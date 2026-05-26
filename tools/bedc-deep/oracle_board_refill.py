#!/usr/bin/env python3
"""oracle_board_refill — when BOARD is dry, ask oracle to propose new targets.

Codex's static gap-scan (auto_discovery probe) finds mechanical missing
pieces (definition without theorem, A→B without B→A, etc.). It runs out
quickly because it can only spot patterns that were ALREADY visible in
paper structure. Once those are filled, codex says "no candidates"
indefinitely.

Oracle receives the current paper PDF and uses mathematical research
intuition to suggest deeper directions: structural / classification /
rigidity theorems, obstruction results, multi-scale induction closures.
This script invokes that capability directly.

Flow:
  1. Build prompt: oracle_board_refill.txt + compact BOARD context +
     paper_index.json coverage summary (so oracle skips already-proven things).
  2. Submit as a fresh oracle task via the oracle_server (same channel as
     normal pipeline tasks — the userscript handles upload routing).
  3. Poll for response (with reasonable timeout).
  4. Parse the candidate JSON list.
  5. Pipe through board_spawn.spawn_from_candidates which runs the
     claude judge (maker/checker) over them and atomically appends
     accepted ones to BOARD.md.
  6. Report stats.

Usage:
  python3 tools/bedc-deep/oracle_board_refill.py [--server URL] [--timeout SEC]

Standalone CLI script — supervisor can call it via subprocess on a cooldown
when unfinished count drops below threshold.
"""

from __future__ import annotations

import argparse
import base64
import json
import os
import re
import sys
import time
import urllib.request
from datetime import datetime
from pathlib import Path
from typing import Optional

import board_context
import paper_gap_scanner
import paper_index

try:
    from logic_discipline import render_prompt_block
except ModuleNotFoundError:  # pragma: no cover
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from logic_discipline import render_prompt_block

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
PROMPTS_DIR = SCRIPT_DIR / "prompts"
LOG_DIR = SCRIPT_DIR / "state" / "board_refill_logs"
DEFAULT_ATTACH_PDF = REPO_ROOT / "papers" / "bedc" / "main.pdf"
ORACLE_SERVER = "http://localhost:8767"
REFILL_TAG = "bedc-deep-board-refill"
REFILL_TASK_PREFIX = "bedc_board_refill_"

DEFAULT_TIMEOUT = 14400  # Match oracle server TASK_TIMEOUT; refill prompts can run long.
DEFAULT_POLL_INTERVAL = 30
DEFAULT_TRANSPORT_RETRIES = 1
ZERO_EXTRACTION_HANG_SECONDS = 900
ZERO_EXTRACTION_MIN_PAGE_CHARS = 1000
REFILL_BOARD_CONTEXT_MAX_CHARS = 9000
REFILL_PAPER_SUMMARY_MAX_CHARS = 8000
REFILL_RECENT_COMPLETED_LIMIT = 12
MICRO_REFILL_BOARD_CONTEXT_MAX_CHARS = 4500
MICRO_REFILL_PAPER_SUMMARY_MAX_CHARS = 5000
MICRO_REFILL_RECENT_COMPLETED_LIMIT = 6
ULTRA_REFILL_BOARD_CONTEXT_MAX_CHARS = 2200
ULTRA_REFILL_PAPER_SUMMARY_MAX_CHARS = 3000
ULTRA_REFILL_RECENT_COMPLETED_LIMIT = 3
MICRO_REFILL_FAILURE_THRESHOLD = 3
MICRO_REFILL_FAILURE_WINDOW = 5
ULTRA_REFILL_MICRO_FAILURE_THRESHOLD = 1
REFILL_CIRCUIT_BREAKER_ULTRA_FAILURE_THRESHOLD = 1
DEFAULT_LOCAL_GAP_FALLBACK_LIMIT = 3
MICRO_REFILL_FAILURE_ERRORS = {
    "oracle_transport_empty_response",
    "oracle_transport_error_response",
    "stopped_before_response",
    "timeout_waiting_for_response",
}
MICRO_REFILL_INSTRUCTION = """
## Micro-refill override

Recent board-refill attempts failed at the browser/transport layer before
returning parseable candidates.  For this run, propose exactly 2-3 candidates,
not 5-10.  Prefer high-confidence existing-chapter lemma/obligation targets
with short local_inputs and complete logic packet metadata.  Do not compensate
by widening theory scope or inventing a new chapter.
""".strip()
ULTRA_REFILL_INSTRUCTION = """
## Ultra-small refill override

Recent micro-refill attempts also failed at the browser/transport layer before
returning parseable candidates.  For this run, propose exactly 1 candidate.
Choose the safest existing-chapter lemma or obligation with complete logic
packet metadata, short local_inputs, and no new-chapter claim.  If no such
candidate is visible, return an empty candidates list rather than widening
scope.
""".strip()


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _safe_run_id(value: str) -> str:
    text = (value or "").strip()
    if not text:
        return _now_tag()
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", text)


def _safe(text: str) -> str:
    return (text or "").replace("{", "{{").replace("}", "}}")


def _http_post(url: str, data: dict, timeout: int = 30) -> dict:
    req = urllib.request.Request(
        url,
        data=json.dumps(data).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"), strict=False)


def _http_get(url: str, timeout: int = 10) -> dict:
    with urllib.request.urlopen(url, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"), strict=False)


def _encode_pdf_for_attach(pdf_path: Path | None) -> tuple[str, str]:
    if pdf_path is None:
        return ("", "")
    p = pdf_path if pdf_path.is_absolute() else REPO_ROOT / pdf_path
    if not p.exists():
        return ("", "")
    try:
        b64 = base64.b64encode(p.read_bytes()).decode("ascii")
    except OSError:
        return ("", "")
    return (b64, p.name)


def _has_refill_in_server(status: dict) -> bool:
    for task in status.get("queued_tasks") or []:
        if task.get("tag") == REFILL_TAG:
            return True
        if str(task.get("task_id", "")).startswith(REFILL_TASK_PREFIX):
            return True
    for task in (status.get("agents") or {}).values():
        if str(task.get("task_id", "")).startswith(REFILL_TASK_PREFIX):
            return True
    return False


def _zero_extraction_hang_agents(status: dict) -> list[str]:
    agents = [str(aid) for aid in (status.get("zero_extraction_hang_agents") or [])]
    if agents:
        return agents
    out: list[str] = []
    active_tasks = {
        str(agent_id): str((task or {}).get("task_id") or "")
        for agent_id, task in (status.get("agents") or {}).items()
    }
    for agent_id, rec in (status.get("recent_agents") or {}).items():
        agent_id = str(agent_id)
        if not active_tasks.get(agent_id):
            continue
        if rec.get("event") != "heartbeat" or not rec.get("recent", False):
            continue
        metrics = rec.get("metrics") or {}
        if str(metrics.get("task_id") or "") != active_tasks[agent_id]:
            continue
        try:
            elapsed = int(metrics.get("elapsed_seconds") or 0)
            extracted = int(metrics.get("extracted_chars") or 0)
            page_chars = int(metrics.get("page_chars") or 0)
        except (TypeError, ValueError):
            continue
        if (
            elapsed >= ZERO_EXTRACTION_HANG_SECONDS
            and extracted == 0
            and page_chars >= ZERO_EXTRACTION_MIN_PAGE_CHARS
        ):
            out.append(agent_id)
    return out


def _zero_extraction_hang_details(status: dict) -> list[dict[str, str]]:
    def metric_text(value: object) -> str:
        if value is None:
            return ""
        return str(value)

    agents = _zero_extraction_hang_agents(status)
    details: list[dict[str, str]] = []
    recent = status.get("recent_agents") or {}
    active = status.get("agents") or {}
    for agent_id in agents:
        rec = recent.get(agent_id) or {}
        metrics = rec.get("metrics") or {}
        task = active.get(agent_id) or {}
        details.append(
            {
                "agent_id": agent_id,
                "task_id": str(metrics.get("task_id") or task.get("task_id") or ""),
                "elapsed_seconds": metric_text(metrics.get("elapsed_seconds")),
                "extracted_chars": metric_text(metrics.get("extracted_chars")),
                "page_chars": metric_text(metrics.get("page_chars")),
                "generating": metric_text(metrics.get("generating")),
                "url_tail": str(metrics.get("url_tail") or ""),
            }
        )
    return details


def _format_zero_extraction_hang(details: list[dict[str, str]]) -> str:
    parts: list[str] = []
    for detail in details:
        fields = [f"agent={detail.get('agent_id') or '?'}"]
        if detail.get("elapsed_seconds"):
            fields.append(f"elapsed={detail['elapsed_seconds']}s")
        if detail.get("extracted_chars"):
            fields.append(f"extracted={detail['extracted_chars']}")
        if detail.get("page_chars"):
            fields.append(f"page_chars={detail['page_chars']}")
        if detail.get("generating"):
            fields.append(f"generating={detail['generating']}")
        if detail.get("task_id"):
            fields.append(f"task={detail['task_id']}")
        if detail.get("url_tail"):
            fields.append(f"url_tail={detail['url_tail']}")
        parts.append(" ".join(fields))
    return "; ".join(parts)


def _cancel_task(server_url: str, task_id: str) -> dict:
    return _http_post(f"{server_url}/cancel", {"task_id": task_id}, timeout=30)


def _should_cancel_zero_extraction(task_id: str, details: list[dict[str, str]]) -> bool:
    """Only auto-cancel when the current refill is no longer generating."""
    for detail in details:
        if detail.get("task_id") != task_id:
            continue
        if str(detail.get("generating") or "").lower() == "false":
            return True
    return False


def _response_failure_kind(response: str) -> str:
    text = (response or "").strip().lower()
    if text.startswith("error: response too short or empty"):
        return "oracle_transport_empty_response"
    if text.startswith("error: duplicate response"):
        return "oracle_transport_duplicate_response"
    if text.startswith("error:"):
        return "oracle_transport_error_response"
    return "unparseable_response"


def _write_failure_summary(
    ts: str,
    *,
    error: str,
    response_len: int = 0,
    micro_refill: bool = False,
    ultra_refill: bool = False,
) -> None:
    summary = {
        "ok": False,
        "candidates_proposed": 0,
        "accepted": 0,
        "rejected": 0,
        "appended_ids": [],
        "error": error,
        "response_len": response_len,
        "micro_refill": micro_refill,
        "ultra_refill": ultra_refill,
        "refill_mode": "ultra" if ultra_refill else "micro" if micro_refill else "normal",
        "ts": ts,
    }
    (LOG_DIR / f"refill_{ts}.summary.json").write_text(
        json.dumps(summary, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )


def _board_content(*, micro_refill: bool = False, ultra_refill: bool = False) -> str:
    # Refill is a candidate-generation lane. Full title dedup, paper coverage,
    # and schema checks run deterministically after response parsing, so the
    # oracle prompt only needs enough context to avoid obvious repeats.
    if ultra_refill:
        max_chars = ULTRA_REFILL_BOARD_CONTEXT_MAX_CHARS
        recent_completed_limit = ULTRA_REFILL_RECENT_COMPLETED_LIMIT
    elif micro_refill:
        max_chars = MICRO_REFILL_BOARD_CONTEXT_MAX_CHARS
        recent_completed_limit = MICRO_REFILL_RECENT_COMPLETED_LIMIT
    else:
        max_chars = REFILL_BOARD_CONTEXT_MAX_CHARS
        recent_completed_limit = REFILL_RECENT_COMPLETED_LIMIT
    return board_context.build_board_prompt_context(
        max_chars=max_chars,
        recent_completed_limit=recent_completed_limit,
    )


def recent_transport_failure_count(
    *,
    limit: int = MICRO_REFILL_FAILURE_WINDOW,
) -> int:
    """Count consecutive recent refill summaries that failed before candidates.

    This is intentionally about transport/no-response failures, not candidate
    rejection.  Logic-gate rejection means the oracle returned usable material;
    stopped/empty/error responses mean the next prompt should get smaller.
    """
    if not LOG_DIR.exists():
        return 0
    summaries = sorted(
        LOG_DIR.glob("refill_*.summary.json"),
        key=lambda path: path.stat().st_mtime,
        reverse=True,
    )
    count = 0
    inspected = 0
    for path in summaries:
        if inspected >= limit:
            break
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        error = str(data.get("error") or "").strip()
        if error == "dry_run_prompt_only" or data.get("fallback") == "local_gap_scanner":
            continue
        inspected += 1
        if data.get("ok"):
            break
        if error in MICRO_REFILL_FAILURE_ERRORS:
            count += 1
            continue
        break
    return count


def recent_micro_transport_failure_count(
    *,
    limit: int = MICRO_REFILL_FAILURE_WINDOW,
) -> int:
    if not LOG_DIR.exists():
        return 0
    summaries = sorted(
        LOG_DIR.glob("refill_*.summary.json"),
        key=lambda path: path.stat().st_mtime,
        reverse=True,
    )
    count = 0
    inspected = 0
    for path in summaries:
        if inspected >= limit:
            break
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        error = str(data.get("error") or "").strip()
        if error == "dry_run_prompt_only" or data.get("fallback") == "local_gap_scanner":
            continue
        inspected += 1
        if data.get("ok"):
            break
        if error not in MICRO_REFILL_FAILURE_ERRORS:
            break
        if data.get("micro_refill") or data.get("ultra_refill"):
            count += 1
            continue
        break
    return count


def recent_ultra_transport_failure_count(
    *,
    limit: int = MICRO_REFILL_FAILURE_WINDOW,
) -> int:
    if not LOG_DIR.exists():
        return 0
    summaries = sorted(
        LOG_DIR.glob("refill_*.summary.json"),
        key=lambda path: path.stat().st_mtime,
        reverse=True,
    )
    count = 0
    inspected = 0
    for path in summaries:
        if inspected >= limit:
            break
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        error = str(data.get("error") or "").strip()
        if error == "dry_run_prompt_only" or data.get("fallback") == "local_gap_scanner":
            continue
        inspected += 1
        if data.get("ok"):
            break
        if error not in MICRO_REFILL_FAILURE_ERRORS:
            break
        if data.get("ultra_refill") or data.get("refill_mode") == "ultra":
            count += 1
            continue
        break
    return count


def should_use_micro_refill() -> bool:
    return recent_transport_failure_count() >= MICRO_REFILL_FAILURE_THRESHOLD


def should_use_ultra_refill() -> bool:
    return (
        should_use_micro_refill()
        and recent_micro_transport_failure_count() >= ULTRA_REFILL_MICRO_FAILURE_THRESHOLD
    )


def refill_circuit_breaker_active() -> bool:
    return (
        recent_ultra_transport_failure_count()
        >= REFILL_CIRCUIT_BREAKER_ULTRA_FAILURE_THRESHOLD
    )


def _extract_json_object(text: str) -> Optional[dict]:
    """Robust scanner — same as elsewhere in pipeline."""
    text = (text or "").strip()
    if not text:
        return None
    fence = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, flags=re.DOTALL)
    if fence:
        try:
            return json.loads(fence.group(1))
        except json.JSONDecodeError:
            pass
    for start in range(len(text)):
        if text[start] != "{":
            continue
        depth = 0
        in_str = False
        esc = False
        for i in range(start, len(text)):
            ch = text[i]
            if in_str:
                if esc:
                    esc = False
                elif ch == "\\":
                    esc = True
                elif ch == '"':
                    in_str = False
                continue
            if ch == '"':
                in_str = True
            elif ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
                if depth == 0:
                    cand = text[start : i + 1]
                    try:
                        return json.loads(cand)
                    except json.JSONDecodeError:
                        break
    return None


# ---------------------------------------------------------------------------
# Build prompt
# ---------------------------------------------------------------------------


def build_refill_prompt(
    *,
    micro_refill: bool = False,
    ultra_refill: bool = False,
) -> str:
    template = (PROMPTS_DIR / "oracle_board_refill.txt").read_text(encoding="utf-8")
    if ultra_refill:
        template = template.replace("提议 5-10 个", "提议 1 个", 1)
    elif micro_refill:
        template = template.replace("提议 5-10 个", "提议 2-3 个", 1)
    board = _board_content(micro_refill=micro_refill, ultra_refill=ultra_refill)
    if ultra_refill:
        paper_summary_max_chars = ULTRA_REFILL_PAPER_SUMMARY_MAX_CHARS
    elif micro_refill:
        paper_summary_max_chars = MICRO_REFILL_PAPER_SUMMARY_MAX_CHARS
    else:
        paper_summary_max_chars = REFILL_PAPER_SUMMARY_MAX_CHARS
    paper_coverage = paper_index.render_prompt_summary(
        max_chars=paper_summary_max_chars,
    )
    discipline = render_prompt_block(
        context="BEDC board refill; oracle may generate candidate targets only, while dedup, schema checks, paper coverage, and deterministic obligation splitting stay local.",
    )
    prompt = template.format(
        board_content=_safe(board),
        paper_labels=_safe(paper_coverage),
    ) + "\n\n" + discipline + "\n"
    if ultra_refill:
        prompt += "\n\n" + ULTRA_REFILL_INSTRUCTION + "\n"
    elif micro_refill:
        prompt += "\n\n" + MICRO_REFILL_INSTRUCTION + "\n"
    return prompt


def _paper_gap_report(*, limit: int = 0) -> tuple[list[dict], dict]:
    try:
        if hasattr(paper_gap_scanner, "generate_candidate_report"):
            report = paper_gap_scanner.generate_candidate_report(limit=limit)
            candidates = report.get("candidates") or []
            scanner_stats = report.get("scanner_stats") or {}
        else:
            candidates = paper_gap_scanner.generate_candidates(limit=limit)
            scanner_stats = {}
    except Exception as exc:
        print(f"[board_refill] WARN: paper_gap_scanner failed: {exc}", flush=True)
        return [], {"error": str(exc)[:300]}
    tagged = []
    for candidate in candidates:
        if isinstance(candidate, dict):
            tagged.append({**candidate, "source": "paper_gap_scanner"})
    print(f"[board_refill] paper_gap_scanner returned {len(tagged)} raw candidates",
          flush=True)
    return tagged, scanner_stats


def _paper_gap_candidates(*, limit: int = 0) -> list[dict]:
    candidates, _scanner_stats = _paper_gap_report(limit=limit)
    return candidates


def _run_local_gap_fallback(
    ts: str,
    *,
    micro_refill: bool,
    ultra_refill: bool,
    limit: int,
) -> int:
    """Use deterministic paper gaps when oracle refill transport is circuit-broken.

    This is not a substitute oracle: it only reuses local scanner output and
    routes it through the same candidate inbox, judge, logic packet gate, and
    BOARD append path as ordinary discovery.
    """
    candidates, scanner_stats = _paper_gap_report(limit=limit)
    if not candidates:
        summary = {
            "ok": True,
            "candidates_proposed": 0,
            "accepted": 0,
            "rejected": 0,
            "appended_ids": [],
            "error": "",
            "fallback": "local_gap_scanner",
            "fallback_reason": "refill_circuit_breaker_active",
            "micro_refill": micro_refill,
            "ultra_refill": ultra_refill,
            "refill_mode": "ultra" if ultra_refill else "micro" if micro_refill else "normal",
            "scanner_stats": scanner_stats,
            "ts": ts,
        }
        (LOG_DIR / f"refill_{ts}.summary.json").write_text(
            json.dumps(summary, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )
        print(json.dumps(summary, ensure_ascii=False, indent=2))
        return 0

    import board_spawn

    spawn_result = board_spawn.spawn_from_candidates(
        codex_candidates=candidates,
        oracle_candidates=[],
    )
    reject_reasons, reject_examples = _summarize_rejections(spawn_result.rejected)
    summary = {
        "ok": spawn_result.ok,
        "candidates_proposed": len(candidates),
        "accepted": len(spawn_result.accepted),
        "rejected": len(spawn_result.rejected),
        "reject_reasons": reject_reasons,
        "reject_examples": reject_examples,
        "appended_ids": spawn_result.appended_ids,
        "error": spawn_result.error,
        "error_kind": getattr(spawn_result, "error_kind", ""),
        "fallback": "local_gap_scanner",
        "fallback_reason": "refill_circuit_breaker_active",
        "micro_refill": micro_refill,
        "ultra_refill": ultra_refill,
        "refill_mode": "ultra" if ultra_refill else "micro" if micro_refill else "normal",
        "scanner_stats": scanner_stats,
        "ts": ts,
    }
    (LOG_DIR / f"refill_{ts}.summary.json").write_text(
        json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8",
    )
    print(json.dumps(summary, ensure_ascii=False, indent=2))
    return 0 if spawn_result.ok else 1


def _summarize_rejections(rejected: list[dict]) -> tuple[dict[str, int], dict[str, str]]:
    reasons: dict[str, int] = {}
    examples: dict[str, str] = {}
    for item in rejected:
        if not isinstance(item, dict):
            continue
        reason = str(item.get("reason") or "unknown").strip() or "unknown"
        reasons[reason] = reasons.get(reason, 0) + 1
        if reason not in examples:
            examples[reason] = str(item.get("title") or item.get("candidate_id") or "?")[:160]
    return dict(sorted(reasons.items(), key=lambda kv: (-kv[1], kv[0]))), examples


# ---------------------------------------------------------------------------
# Submit + poll oracle
# ---------------------------------------------------------------------------


def submit_refill(
    server_url: str,
    prompt: str,
    *,
    attach_pdf: Path | None = None,
) -> dict:
    """Submit as a NEW oracle task (no conversation_id) so userscript opens
    a fresh chat in the BEDC Project and uploads the current paper PDF."""
    task_id = f"bedc_board_refill_{int(time.time() * 1000)}"
    payload = {
        "task_id": task_id,
        "prompt": prompt,
        "model": "chatgpt-5.5-pro",
        "tag": REFILL_TAG,
    }
    pdf_b64, pdf_name = _encode_pdf_for_attach(attach_pdf)
    if pdf_b64:
        payload["pdf_base64"] = pdf_b64
        payload["pdf_name"] = pdf_name
        print(
            f"[board_refill] attaching PDF {pdf_name} "
            f"({len(pdf_b64) * 0.75 / 1024:.0f} KB)",
            flush=True,
        )
    elif attach_pdf is not None:
        print(
            f"[board_refill] WARN: requested PDF attachment missing or unreadable: {attach_pdf}",
            flush=True,
        )
    req = urllib.request.Request(
        f"{server_url}/submit",
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
    )
    with urllib.request.urlopen(req, timeout=30) as resp:
        return json.loads(resp.read().decode("utf-8"), strict=False)


def poll_result(
    server_url: str,
    task_id: str,
    timeout: int,
    poll_interval: int,
) -> Optional[str]:
    start = time.time()
    last_log = start
    last_zero_extract_log = 0.0
    while time.time() - start < timeout:
        try:
            data = _http_get(f"{server_url}/result/{task_id}", timeout=10)
            status = data.get("status")
            if status == "completed":
                return data.get("response", "")
            if status in {"cancelled", "failed", "error"}:
                print(
                    f"[board_refill] task ended with status={status}",
                    flush=True,
                )
                return None
        except Exception:
            pass
        try:
            health = _http_get(f"{server_url}/status", timeout=5)
            details = _zero_extraction_hang_details(health)
            if details:
                now = time.time()
                if now - last_zero_extract_log > 300:
                    threshold = health.get(
                        "zero_extraction_hang_seconds",
                        ZERO_EXTRACTION_HANG_SECONDS,
                    )
                    detail_text = _format_zero_extraction_hang(details)
                    print(
                        "[board_refill] WARN: zero-extraction hang "
                        f"{detail_text}; threshold={threshold}s; "
                        "refresh affected tab(s) only.",
                        flush=True,
                    )
                    last_zero_extract_log = now
                if _should_cancel_zero_extraction(task_id, details):
                    cancel_resp = _cancel_task(server_url, task_id)
                    print(
                        "[board_refill] zero-extraction task is no longer generating; "
                        f"cancelled task={task_id} response={cancel_resp}",
                        flush=True,
                    )
                    return None
        except Exception:
            pass
        if time.time() - last_log > 60:
            elapsed = int(time.time() - start)
            print(f"[board_refill] waiting... {elapsed}s elapsed", flush=True)
            last_log = time.time()
        time.sleep(poll_interval)
    return ""


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Ask oracle for new BOARD candidates with the current paper PDF",
    )
    parser.add_argument("--server", default=ORACLE_SERVER)
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT)
    parser.add_argument("--poll-interval", type=int, default=DEFAULT_POLL_INTERVAL)
    parser.add_argument("--transport-retries", type=int, default=DEFAULT_TRANSPORT_RETRIES,
                        help="Fresh refill retries after oracle transport-only empty/error responses.")
    parser.add_argument("--dry-run", action="store_true",
                        help="Only build + print prompt, don't submit.")
    parser.add_argument("--micro-refill", action="store_true",
                        help="Use a smaller prompt and request 2-3 candidates.")
    parser.add_argument("--ultra-refill", action="store_true",
                        help="Use the smallest prompt and request exactly 1 candidate.")
    parser.add_argument("--no-auto-micro-refill", action="store_true",
                        help="Disable automatic micro-refill after repeated transport failures.")
    parser.add_argument("--no-auto-ultra-refill", action="store_true",
                        help="Disable automatic ultra-refill after a failed micro-refill.")
    parser.add_argument("--ignore-refill-circuit-breaker", action="store_true",
                        help="Submit even after recent ultra-refill transport failures.")
    parser.add_argument("--no-local-gap-fallback", action="store_true",
                        help="When the refill circuit breaker is active, skip instead of routing deterministic paper gaps through the intake gate.")
    parser.add_argument("--local-gap-fallback-limit", type=int, default=DEFAULT_LOCAL_GAP_FALLBACK_LIMIT,
                        help="Maximum deterministic paper-gap candidates to try when oracle refill transport is circuit-broken.")
    parser.add_argument("--allow-queue-without-tabs", action="store_true",
                        help="Submit even when no active BEDC browser tab is polling.")
    parser.add_argument("--allow-duplicate-refill", action="store_true",
                        help="Submit even when another board-refill task is queued or active.")
    parser.add_argument("--attach-pdf", default=str(DEFAULT_ATTACH_PDF),
                        help="PDF to upload with the refill task; default: papers/bedc/main.pdf")
    parser.add_argument("--no-attach-pdf", action="store_true",
                        help="Do not upload a PDF with the refill task.")
    parser.add_argument("--run-id", default="",
                        help="Filesystem-safe run id shared with supervisor logs.")
    args = parser.parse_args()

    LOG_DIR.mkdir(parents=True, exist_ok=True)
    ts = _safe_run_id(args.run_id)

    failure_count = recent_transport_failure_count()
    micro_failure_count = recent_micro_transport_failure_count()
    ultra_refill = args.ultra_refill or (
        not args.no_auto_ultra_refill
        and not args.no_auto_micro_refill
        and micro_failure_count >= ULTRA_REFILL_MICRO_FAILURE_THRESHOLD
        and failure_count >= MICRO_REFILL_FAILURE_THRESHOLD
    )
    micro_refill = ultra_refill or args.micro_refill or (
        not args.no_auto_micro_refill
        and failure_count >= MICRO_REFILL_FAILURE_THRESHOLD
    )
    if ultra_refill:
        print(
            "[board_refill] ultra-refill mode enabled "
            f"(recent_transport_failures={failure_count}, "
            f"recent_micro_failures={micro_failure_count})",
            flush=True,
        )
    elif micro_refill:
        print(
            "[board_refill] micro-refill mode enabled "
            f"(recent_transport_failures={failure_count})",
            flush=True,
        )

    if (
        not args.dry_run
        and not args.ignore_refill_circuit_breaker
        and refill_circuit_breaker_active()
    ):
        print(
            "[board_refill] circuit breaker active after recent ultra-refill "
            "transport failure.",
            flush=True,
        )
        if args.no_local_gap_fallback:
            print("[board_refill] local gap fallback disabled; skipping submit.", flush=True)
            return 0
        print(
            "[board_refill] using deterministic local gap fallback through "
            "candidate_inbox/board_spawn/logic_packet_gate.",
            flush=True,
        )
        return _run_local_gap_fallback(
            ts,
            micro_refill=micro_refill,
            ultra_refill=ultra_refill,
            limit=max(0, int(args.local_gap_fallback_limit or 0)),
        )

    if not args.dry_run:
        # Verify server readiness before building/logging a prompt. Duplicate or
        # tabless skips are control-plane decisions, not refill attempts.
        try:
            status = _http_get(f"{args.server}/status", timeout=5)
            if _has_refill_in_server(status) and not args.allow_duplicate_refill:
                print(
                    "[board_refill] existing board-refill task is queued or active; "
                    "skipping submit.",
                    flush=True,
                )
                return 0
            if not status.get("dispatch_ready_poll_agents"):
                if not args.allow_queue_without_tabs:
                    print(
                        "[board_refill] no dispatch-ready BEDC conversation tabs polling; "
                        "skipping submit instead of queueing.",
                        flush=True,
                    )
                    return 0
                print(
                    "[board_refill] WARN: no dispatch-ready BEDC conversation tabs "
                    "polling. Submit will queue but won't dispatch until a BEDC "
                    "Project /c/... tab is polling.",
                    flush=True,
                )
        except Exception as exc:
            print(f"[board_refill] server unreachable at {args.server}: {exc}", flush=True)
            return 1

    prompt = build_refill_prompt(
        micro_refill=micro_refill,
        ultra_refill=ultra_refill,
    )
    (LOG_DIR / f"refill_{ts}.prompt.txt").write_text(prompt, encoding="utf-8")
    print(f"[board_refill] prompt built ({len(prompt)} chars)", flush=True)

    if args.dry_run:
        _write_failure_summary(
            ts,
            error="dry_run_prompt_only",
            micro_refill=micro_refill,
            ultra_refill=ultra_refill,
        )
        print(prompt[:2000])
        print(f"... [{len(prompt)} chars total]")
        return 0

    attach_pdf = None if args.no_attach_pdf else Path(args.attach_pdf)
    response = ""
    max_attempts = max(1, int(args.transport_retries or 0) + 1)
    for attempt in range(1, max_attempts + 1):
        if attempt > 1:
            print(
                f"[board_refill] retrying fresh refill after transport failure "
                f"(attempt {attempt}/{max_attempts})",
                flush=True,
            )
        try:
            submit_resp = submit_refill(args.server, prompt, attach_pdf=attach_pdf)
        except Exception as exc:
            print(
                f"[board_refill] submit failed with {type(exc).__name__}: {exc}",
                flush=True,
            )
            _write_failure_summary(
                ts,
                error=f"submit_exception:{type(exc).__name__}",
                micro_refill=micro_refill,
                ultra_refill=ultra_refill,
            )
            return 1
        if "error" in submit_resp:
            print(f"[board_refill] submit failed: {submit_resp['error']}", flush=True)
            _write_failure_summary(
                ts,
                error=f"submit_failed:{submit_resp['error']}",
                micro_refill=micro_refill,
                ultra_refill=ultra_refill,
            )
            return 1
        task_id = submit_resp.get("task_id", "")
        conv_id = submit_resp.get("conversation_id", "")
        print(f"[board_refill] submitted task={task_id} conv={conv_id[:14]}", flush=True)

        response = poll_result(args.server, task_id, args.timeout, args.poll_interval)
        if response is None:
            print("[board_refill] stopped before receiving a response", flush=True)
            _write_failure_summary(
                ts,
                error="stopped_before_response",
                micro_refill=micro_refill,
                ultra_refill=ultra_refill,
            )
            return 1
        if not response:
            print(f"[board_refill] timeout waiting for response (limit={args.timeout}s)",
                  flush=True)
            _write_failure_summary(
                ts,
                error="timeout_waiting_for_response",
                micro_refill=micro_refill,
                ultra_refill=ultra_refill,
            )
            return 1
        failure_kind = _response_failure_kind(response)
        if failure_kind.startswith("oracle_transport_") and attempt < max_attempts:
            print(
                f"[board_refill] {failure_kind}; retrying once with a fresh task",
                flush=True,
            )
            continue
        break

    (LOG_DIR / f"refill_{ts}.response.md").write_text(response, encoding="utf-8")
    print(f"[board_refill] received {len(response)} chars", flush=True)

    parsed = _extract_json_object(response)
    if not parsed:
        failure_kind = _response_failure_kind(response)
        print(f"[board_refill] response was not parseable JSON ({failure_kind})", flush=True)
        _write_failure_summary(
            ts,
            error=failure_kind,
            response_len=len(response),
            micro_refill=micro_refill,
            ultra_refill=ultra_refill,
        )
        return 1

    candidates = parsed.get("candidates") or []
    if not isinstance(candidates, list):
        print(f"[board_refill] candidates field is not a list: {type(candidates)}",
              flush=True)
        return 1

    # Stamp source for board_spawn judge to know
    for c in candidates:
        if isinstance(c, dict):
            c["source"] = "oracle_board_refill"

    gap_candidates = _paper_gap_candidates()
    candidates.extend(gap_candidates)

    print(f"[board_refill] oracle returned {len(candidates) - len(gap_candidates)} raw candidates",
          flush=True)
    if not candidates:
        print("[board_refill] empty candidate list — oracle declined to suggest anything",
              flush=True)
        return 0

    # Pipe through board_spawn judge
    sys.path.insert(0, str(SCRIPT_DIR))
    import board_spawn

    spawn_result = board_spawn.spawn_from_candidates(
        codex_candidates=[],
        oracle_candidates=candidates,
    )
    summary = {
        "ok": spawn_result.ok,
        "candidates_proposed": len(candidates),
        "accepted": len(spawn_result.accepted),
        "rejected": len(spawn_result.rejected),
        "appended_ids": spawn_result.appended_ids,
        "error": spawn_result.error,
        "error_kind": getattr(spawn_result, "error_kind", ""),
        "micro_refill": micro_refill,
        "ultra_refill": ultra_refill,
        "refill_mode": "ultra" if ultra_refill else "micro" if micro_refill else "normal",
        "ts": ts,
    }
    (LOG_DIR / f"refill_{ts}.summary.json").write_text(
        json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8",
    )
    print(json.dumps(summary, ensure_ascii=False, indent=2))
    return 0 if spawn_result.ok and spawn_result.appended_ids else 1


if __name__ == "__main__":
    raise SystemExit(main())

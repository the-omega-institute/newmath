#!/usr/bin/env python3
"""BOARD spawn gate — combine codex + oracle candidates and append accepted ones.

Two upstream sources:
- codex track collects board_candidates throughout its rounds (lemmas /
  corollaries / structural variants noticed while proving).
- oracle track, after self-declaring proved, runs an "adjacent directions"
  prompt that surfaces extension / counterpart / sibling research directions.

This module merges both lists, dedups against existing BOARD and paper
coverage, then runs claude as a maker/checker judge (codex's existing
fit/novelty are part of the candidate's source signal; claude is the
final gate). Accepted candidates are atomically appended to BOARD.md.

Replaces the old Stage 1.5 single-source codex.discover_topics flow.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import threading
import time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional

from dispatch_bedc_target import SCRIPT_DIR, REPO_ROOT, BOARD_PATH
from locks import file_lock
import codex_orchestrator


PROMPTS_DIR = SCRIPT_DIR / "prompts"
LOG_DIR = SCRIPT_DIR / "state" / "board_spawn_logs"

CLAUDE_PATH = shutil.which("claude") or "/opt/homebrew/bin/claude"
DEFAULT_JUDGE_TIMEOUT = 600

DEFAULT_FIT_THRESHOLD = 7
DEFAULT_NOVELTY_THRESHOLD = 6


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _safe(text: str) -> str:
    return (text or "").replace("{", "{{").replace("}", "}}")


def _extract_json_object(text: str) -> Optional[dict]:
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
                    candidate = text[start : i + 1]
                    try:
                        return json.loads(candidate)
                    except json.JSONDecodeError:
                        break
    return None


def _claude_exec(prompt: str, *, timeout: int, log_tag: str) -> tuple[bool, str, int]:
    if os.environ.get("BEDC_DISABLE_CLAUDE"):
        return (False, "claude disabled by BEDC_DISABLE_CLAUDE", -2)
    if not CLAUDE_PATH or not Path(CLAUDE_PATH).exists():
        return (False, f"claude CLI not found at {CLAUDE_PATH}", -1)
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    ts = _now_tag()
    (LOG_DIR / f"{log_tag}_{ts}.prompt.txt").write_text(prompt, encoding="utf-8")
    cmd = [CLAUDE_PATH, "-p", "--dangerously-skip-permissions"]
    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}
    proc = subprocess.Popen(
        cmd,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=str(REPO_ROOT),
        env=env,
        encoding="utf-8",
        errors="replace",
        start_new_session=True,
    )
    stdout = ""
    stderr = ""
    rc = -1
    hard_killed = {"flag": False}
    def _hard_kill() -> None:
        hard_killed["flag"] = True
        try:
            os.killpg(proc.pid, 9)
        except (ProcessLookupError, PermissionError):
            pass
    watchdog = threading.Timer(timeout + 60, _hard_kill)
    watchdog.daemon = True
    watchdog.start()
    try:
        stdout, stderr = proc.communicate(input=prompt, timeout=timeout + 30)
        rc = proc.returncode
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, 9)
        except ProcessLookupError:
            pass
        try:
            stdout, stderr = proc.communicate(timeout=10)
        except subprocess.TimeoutExpired:
            stdout = stdout or ""
            stderr = stderr or ""
        rc = -9
    finally:
        watchdog.cancel()
    if hard_killed["flag"] and rc == 0:
        rc = -9
    (LOG_DIR / f"{log_tag}_{ts}.stdout.txt").write_text(stdout or "", encoding="utf-8")
    (LOG_DIR / f"{log_tag}_{ts}.stderr.txt").write_text(stderr or "", encoding="utf-8")
    return (rc == 0, stdout, rc)


def _codex_json_fallback(
    prompt: str,
    *,
    timeout: int,
    log_tag: str,
    role_note: str,
) -> tuple[bool, dict, str, str]:
    fallback_prompt = (
        f"{role_note}\n"
        "Act as the independent fallback BOARD judge. Preserve the same "
        "fit/novelty thresholds, reject when uncertain, return only the JSON "
        "object requested by the original prompt, and do not edit files.\n\n"
        f"{prompt}"
    )
    result = codex_orchestrator.codex_exec(
        fallback_prompt,
        timeout=timeout,
        log_tag=f"{log_tag}_codex_fallback",
    )
    if not result.ok:
        return (False, {}, result.raw_output, result.error or f"codex rc={result.rc}")
    parsed = result.parsed or _extract_json_object(result.raw_output) or {}
    if not parsed:
        return (False, {}, result.raw_output, "codex fallback output was not JSON")
    return (True, parsed, result.raw_output, "")


# ---------------------------------------------------------------------------
# Existing BOARD / paper coverage discovery
# ---------------------------------------------------------------------------


def _existing_board_titles() -> set[str]:
    """Lowercased existing target titles for dedup."""
    text = BOARD_PATH.read_text(encoding="utf-8")
    titles: set[str] = set()
    for m in re.finditer(r"^### (B-\d+)\s+-\s+(.+)$", text, flags=re.MULTILINE):
        titles.add(m.group(2).strip().lower())
    return titles


def _existing_board_ids() -> list[str]:
    text = BOARD_PATH.read_text(encoding="utf-8")
    return re.findall(r"^### (B-\d+)\b", text, flags=re.MULTILINE)


def _next_target_id(also_accepted: list[str]) -> str:
    ids = _existing_board_ids() + list(also_accepted)
    nums = [int(i.split("-")[1]) for i in ids if i.startswith("B-")]
    next_num = (max(nums) + 1) if nums else 1
    return f"B-{next_num:02d}"


def _scan_paper_labels() -> list[str]:
    """Quick scan of papers/bedc/parts/**/*.tex for \\label{thm|lem|prop|cor|def:...}"""
    labels: list[str] = []
    parts = REPO_ROOT / "papers" / "bedc" / "parts"
    if not parts.exists():
        return labels
    pat = re.compile(r"\\label\{(thm|lem|prop|cor|def):([^}]+)\}")
    for path in parts.rglob("*.tex"):
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for m in pat.finditer(text):
            labels.append(f"{m.group(1)}:{m.group(2)}")
    return labels


# ---------------------------------------------------------------------------
# Judge: claude maker/checker on combined candidate list
# ---------------------------------------------------------------------------


@dataclass
class BoardSpawnResult:
    ok: bool
    accepted: list[dict] = field(default_factory=list)
    rejected: list[dict] = field(default_factory=list)
    appended_ids: list[str] = field(default_factory=list)
    error: str = ""


def _judge_candidates(
    *,
    codex_candidates: list[dict],
    oracle_candidates: list[dict],
) -> tuple[list[dict], list[dict], str]:
    """Run claude judge prompt; returns (accepted, rejected, error)."""
    if not codex_candidates and not oracle_candidates:
        return ([], [], "")

    template = (PROMPTS_DIR / "board_judge.txt").read_text(encoding="utf-8")
    board_content = BOARD_PATH.read_text(encoding="utf-8")
    paper_labels = _scan_paper_labels()
    paper_coverage_blob = "\n".join(sorted(set(paper_labels))[:400])  # cap

    codex_blob = json.dumps(codex_candidates, ensure_ascii=False, indent=2)
    oracle_blob = json.dumps(oracle_candidates, ensure_ascii=False, indent=2)

    prompt = template.format(
        board_content=_safe(board_content[:30000]),
        paper_coverage=_safe(paper_coverage_blob[:20000]),
        codex_candidates=_safe(codex_blob),
        oracle_candidates=_safe(oracle_blob),
    )
    log_tag = "board_judge"
    ok, stdout, rc = _claude_exec(prompt, timeout=DEFAULT_JUDGE_TIMEOUT, log_tag=log_tag)
    if not ok:
        fallback_ok, parsed, _fallback_stdout, fallback_error = _codex_json_fallback(
            prompt,
            timeout=DEFAULT_JUDGE_TIMEOUT,
            log_tag=log_tag,
            role_note=(
                "Claude is unavailable for the BEDC BOARD spawn judge. "
                "Interpret the original prompt's 'claude evaluation' as this "
                "fallback gate's independent second-pass evaluation."
            ),
        )
        if not fallback_ok:
            return ([], [], f"claude judge rc={rc}: {stdout[:300]}; codex fallback: {fallback_error[:300]}")
    else:
        parsed = _extract_json_object(stdout)
    if not parsed:
        fallback_ok, parsed, _fallback_stdout, fallback_error = _codex_json_fallback(
            prompt,
            timeout=DEFAULT_JUDGE_TIMEOUT,
            log_tag=log_tag,
            role_note=(
                "Claude returned non-JSON for the BEDC BOARD spawn judge. "
                "Interpret the original prompt's 'claude evaluation' as this "
                "fallback gate's independent second-pass evaluation."
            ),
        )
        if not fallback_ok:
            return ([], [], f"claude judge output was not JSON; codex fallback: {fallback_error[:300]}")
    accepted = parsed.get("accepted_candidates") or []
    rejected = parsed.get("rejected_candidates") or []
    return (accepted if isinstance(accepted, list) else [],
            rejected if isinstance(rejected, list) else [],
            "")


# ---------------------------------------------------------------------------
# BOARD append
# ---------------------------------------------------------------------------


def _render_entry(target_id: str, candidate: dict) -> str:
    title = candidate.get("title", "(untitled)")
    claim = candidate.get("claim", "")
    chapter = candidate.get("chapter", "concrete_instances")
    fit = candidate.get("fit_score", "?")
    novelty = candidate.get("novelty", "?")
    source = candidate.get("source", "judge")
    rationale = candidate.get("rationale", "")
    inputs = candidate.get("local_inputs") or []
    inputs_block = "\n".join(f"- `{p}`" for p in inputs) if inputs else "- (auto-spawn — no specific inputs declared)"
    return (
        f"\n### {target_id} - {title}\n\n"
        f"| field | value |\n"
        f"|---|---|\n"
        f"| Status | Candidate (auto-spawned) |\n"
        f"| Source | bedc-deep board_spawn ({source}) |\n"
        f"| Object | {title} |\n"
        f"| Layer | {chapter} |\n"
        f"| Route | proof |\n"
        f"| Risk | unknown |\n"
        f"| Fit | {fit}/10 |\n"
        f"| Novelty | {novelty}/10 |\n\n"
        f"Problem:\n{claim}\n\n"
        f"Local inputs:\n{inputs_block}\n\n"
        f"Rationale:\n{rationale}\n\n---\n"
    )


def _atomic_append_to_board(blocks: list[str]) -> None:
    if not blocks:
        return
    original = BOARD_PATH.read_text(encoding="utf-8").rstrip()
    new_text = original + "\n" + "\n".join(blocks) + "\n"
    tmp = BOARD_PATH.with_suffix(BOARD_PATH.suffix + ".tmp")
    tmp.write_text(new_text, encoding="utf-8")
    tmp.replace(BOARD_PATH)


# ---------------------------------------------------------------------------
# Public entry
# ---------------------------------------------------------------------------


def spawn_from_candidates(
    *,
    codex_candidates: list[dict],
    oracle_candidates: list[dict],
    fit_threshold: int = DEFAULT_FIT_THRESHOLD,
    novelty_threshold: int = DEFAULT_NOVELTY_THRESHOLD,
) -> BoardSpawnResult:
    """Run the BOARD spawn gate over combined candidate lists.

    Returns BoardSpawnResult with accepted/rejected/appended_ids.
    """
    if not codex_candidates and not oracle_candidates:
        return BoardSpawnResult(ok=True)

    # Step 1: dedup vs existing BOARD titles (cheap pre-filter).
    existing_titles = _existing_board_titles()
    def _alive(c: dict) -> bool:
        title = (c.get("title") or "").strip().lower()
        return bool(title) and title not in existing_titles

    codex_alive = [c for c in codex_candidates if _alive(c)]
    oracle_alive = [c for c in oracle_candidates if _alive(c)]
    cheap_drops = (
        [{**c, "source": "codex", "reason": "duplicate_title_in_board"}
         for c in codex_candidates if not _alive(c)]
        + [{**c, "source": "oracle", "reason": "duplicate_title_in_board"}
           for c in oracle_candidates if not _alive(c)]
    )

    if not codex_alive and not oracle_alive:
        print(
            f"[board_spawn] all {len(codex_candidates) + len(oracle_candidates)} "
            f"candidates dedup'd against existing BOARD titles",
            flush=True,
        )
        return BoardSpawnResult(ok=True, rejected=cheap_drops)

    # Step 2: claude judge (with codex+oracle source signals + paper coverage).
    print(
        f"[board_spawn] judging {len(codex_alive)} codex + {len(oracle_alive)} oracle candidates",
        flush=True,
    )
    accepted, rejected, err = _judge_candidates(
        codex_candidates=codex_alive,
        oracle_candidates=oracle_alive,
    )
    if err:
        return BoardSpawnResult(ok=False, error=err, rejected=cheap_drops + rejected)

    # Step 3: enforce thresholds (judge may have already, double-check defensively).
    final_accepted: list[dict] = []
    threshold_drops: list[dict] = []
    for c in accepted:
        try:
            fit = int(c.get("fit_score", 0))
            nov = int(c.get("novelty", 0))
        except (TypeError, ValueError):
            threshold_drops.append({**c, "reason": "non_int_score"})
            continue
        if fit < fit_threshold or nov < novelty_threshold:
            threshold_drops.append({**c, "reason": f"below_threshold fit={fit} nov={nov}"})
            continue
        final_accepted.append(c)

    # Step 4: atomic append under board lock.
    appended_ids: list[str] = []
    if final_accepted:
        with file_lock("board"):
            blocks: list[str] = []
            local_acc: list[str] = []
            for c in final_accepted:
                tid = _next_target_id(local_acc)
                blocks.append(_render_entry(tid, c))
                local_acc.append(tid)
                appended_ids.append(tid)
            _atomic_append_to_board(blocks)

    print(
        f"[board_spawn] accepted={len(final_accepted)} rejected={len(rejected) + len(threshold_drops) + len(cheap_drops)}",
        flush=True,
    )
    return BoardSpawnResult(
        ok=True,
        accepted=final_accepted,
        rejected=cheap_drops + rejected + threshold_drops,
        appended_ids=appended_ids,
    )


# ---------------------------------------------------------------------------
# Oracle adjacent self-report (Stage 1.6 — invoked after oracle declares done)
# ---------------------------------------------------------------------------


def build_oracle_adjacent_prompt(
    *,
    target_id: str,
    target_title: str,
    proven_results_summary: str = "",
) -> str:
    """Build the prompt that asks oracle to self-report adjacent BOARD candidates.

    This prompt goes to the oracle in the same conversation as a follow-up,
    AFTER oracle has reached its terminal proven state. Caller submits via
    submit_turn(.../continue), captures response, and parses out the JSON
    list to feed into spawn_from_candidates(oracle_candidates=...).
    """
    template = (PROMPTS_DIR / "oracle_adjacent.txt").read_text(encoding="utf-8")
    # Use last id placeholders. We don't know exactly how oracle numbered;
    # the prompt phrases #{N1}-#{Nk} loosely so oracle interprets correctly.
    return template.format(
        target_id=_safe(target_id),
        target_title=_safe(target_title),
        N1="N_first",
        Nk="N_last",
    )


def parse_oracle_adjacent_response(response: str) -> list[dict]:
    """Extract the candidate list from oracle's adjacent-direction self-report."""
    if not response or not response.strip():
        return []
    # Look for a JSON array of objects
    arr_match = re.search(r"\[\s*\{.*\}\s*\]", response, flags=re.DOTALL)
    if not arr_match:
        return []
    try:
        arr = json.loads(arr_match.group(0))
    except json.JSONDecodeError:
        return []
    if not isinstance(arr, list):
        return []
    out: list[dict] = []
    for item in arr:
        if not isinstance(item, dict):
            continue
        out.append({
            "title": str(item.get("title", "")).strip(),
            "claim": str(item.get("claim", "")).strip(),
            "chapter": str(item.get("chapter", "concrete_instances")).strip(),
            "relation": str(item.get("relation", "sibling")).strip(),
            "rationale": str(item.get("rationale", "")).strip(),
            "source": "oracle",
        })
    return [c for c in out if c["title"] and c["claim"]]


# ---------------------------------------------------------------------------
# CLI smoke test
# ---------------------------------------------------------------------------


def main() -> int:
    import argparse

    parser = argparse.ArgumentParser(description="board_spawn smoke test")
    parser.add_argument("--codex-json", default="",
                        help="path to JSON file with codex_candidates list")
    parser.add_argument("--oracle-json", default="",
                        help="path to JSON file with oracle_candidates list")
    parser.add_argument("--dry-run", action="store_true",
                        help="run judge but do not append to BOARD")
    args = parser.parse_args()

    codex = json.loads(Path(args.codex_json).read_text()) if args.codex_json else []
    oracle = json.loads(Path(args.oracle_json).read_text()) if args.oracle_json else []

    if args.dry_run:
        accepted, rejected, err = _judge_candidates(
            codex_candidates=codex, oracle_candidates=oracle
        )
        print(json.dumps({
            "judge_ok": not err,
            "error": err,
            "accepted": accepted,
            "rejected": rejected,
        }, indent=2, ensure_ascii=False))
        return 0
    result = spawn_from_candidates(
        codex_candidates=codex, oracle_candidates=oracle
    )
    print(json.dumps({
        "ok": result.ok,
        "appended_ids": result.appended_ids,
        "accepted_count": len(result.accepted),
        "rejected_count": len(result.rejected),
        "error": result.error,
    }, indent=2, ensure_ascii=False))
    return 0 if result.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())

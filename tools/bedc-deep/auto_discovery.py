#!/usr/bin/env python3
"""Active target discovery for BEDC bedc-deep.

Two modes:
  probe   — codex scans papers/bedc/parts + lean4/BEDC for structural gaps,
            then claude reviews and filters; accepted candidates append to
            BOARD.md as new B-XX entries.
  curator — codex meta-review of completed-target transcripts + paper +
            BOARD progress; proposes under-represented directions, then
            claude reviews and filters.

Both modes are invoked manually (not inside the run-loop) so the user can
inspect candidates before they enter the queue.

Pattern matches the rest of bedc-deep: codex generates, claude gates.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

import codex_orchestrator
import killo_golden_writeback
from oracle_client import (
    BOARD_PATH,
    DEFAULT_CANDIDATE_FIT_THRESHOLD,
    DEFAULT_CANDIDATE_NOVELTY_THRESHOLD,
    STATE_DIR,
    TARGETS_DIR,
    append_candidates_to_board,
)

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
PROMPTS_DIR = SCRIPT_DIR / "prompts"
DISCOVERY_LOG_DIR = SCRIPT_DIR / "state" / "discovery_logs"

PROBE_TIMEOUT = 1800
REVIEW_TIMEOUT = 1800
CURATOR_TIMEOUT = 2400
COMPLETED_SUMMARY_LIMIT = 8000
BOARD_INCLUDE_LIMIT = 30000


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _board_text() -> str:
    text = BOARD_PATH.read_text(encoding="utf-8")
    return text[:BOARD_INCLUDE_LIMIT]


def _completed_summary() -> str:
    parts: list[str] = []
    if not STATE_DIR.exists():
        return "(no completed targets yet)"
    for path in sorted(STATE_DIR.glob("*.json")):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue
        verdict = data.get("stage1_verdict") or "unknown"
        spawned = data.get("stage15_spawned") or []
        stage2 = data.get("stage2") or {}
        parts.append(
            f"- {data.get('target_id', '?')} {data.get('title', '')} "
            f"verdict={verdict} spawned={len(spawned)} "
            f"stage2={stage2.get('verdict', 'n/a')}"
        )
    summary = "\n".join(parts) or "(no completed targets yet)"
    if len(summary) > COMPLETED_SUMMARY_LIMIT:
        summary = summary[:COMPLETED_SUMMARY_LIMIT] + "\n[truncated]"
    return summary


def _run_codex_pass(template_path: Path, log_tag: str, **format_kwargs) -> tuple[bool, list[dict], str]:
    template = template_path.read_text(encoding="utf-8")
    prompt = template.format(**format_kwargs)
    result = codex_orchestrator.codex_exec(prompt, timeout=PROBE_TIMEOUT, log_tag=log_tag)
    if not result.ok:
        return (False, [], result.error or f"codex rc={result.rc}")
    parsed = result.parsed
    if not parsed:
        return (False, [], "codex output was not JSON")
    candidates = parsed.get("candidates") or []
    if not isinstance(candidates, list):
        return (False, [], "candidates field was not a list")
    return (True, candidates, "")


def _run_claude_review(candidates: list[dict], log_tag: str) -> tuple[bool, list[dict], list[dict], str]:
    """Send candidates to claude review gate. Returns (ok, accepted, rejected, error)."""
    if not candidates:
        return (True, [], [], "")
    template = (PROMPTS_DIR / "auto_discovery_review.txt").read_text(encoding="utf-8")
    prompt = template.format(
        repo_root=str(REPO_ROOT),
        board_content=_board_text(),
        candidates_json=json.dumps({"candidates": candidates}, ensure_ascii=False, indent=2),
    )
    ok, stdout, rc = killo_golden_writeback.claude_exec(prompt, timeout=REVIEW_TIMEOUT, log_tag=log_tag)
    if not ok:
        return (False, [], [], f"claude exec rc={rc}: {stdout[:400]}")
    parsed = _extract_json_object(stdout)
    if not parsed:
        return (False, [], [], "claude output was not JSON")
    accepted = parsed.get("accepted") or []
    rejected = parsed.get("rejected") or []
    if not isinstance(accepted, list) or not isinstance(rejected, list):
        return (False, [], [], "accepted/rejected fields had wrong type")
    return (True, accepted, rejected, "")


def _extract_json_object(text: str) -> dict | None:
    text = (text or "").strip()
    if not text:
        return None
    fence = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", text, flags=re.DOTALL)
    if fence:
        candidate = fence.group(1)
    else:
        first = text.find("{")
        last = text.rfind("}")
        if first == -1 or last == -1 or last <= first:
            return None
        candidate = text[first : last + 1]
    try:
        return json.loads(candidate)
    except json.JSONDecodeError:
        return None


def _persist(mode: str, payload: dict) -> Path:
    DISCOVERY_LOG_DIR.mkdir(parents=True, exist_ok=True)
    out = DISCOVERY_LOG_DIR / f"{mode}_{_now_tag()}.json"
    out.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return out


def cmd_probe(args: argparse.Namespace) -> int:
    print("[probe] codex theory-probe pass starting...", flush=True)
    ok, codex_candidates, err = _run_codex_pass(
        PROMPTS_DIR / "theory_probe.txt",
        "probe_codex",
        board_content=_board_text(),
    )
    if not ok:
        print(f"[probe] codex failed: {err}", flush=True)
        _persist("probe", {"ok": False, "stage": "codex", "error": err})
        return 1
    print(f"[probe] codex returned {len(codex_candidates)} candidates", flush=True)
    if not codex_candidates:
        print("[probe] empty list — nothing to review", flush=True)
        _persist("probe", {"ok": True, "codex_candidates": [], "accepted": [], "rejected": []})
        return 0

    ok, accepted, rejected, err = _run_claude_review(codex_candidates, "probe_review")
    if not ok:
        print(f"[probe] claude review failed: {err}", flush=True)
        _persist("probe", {"ok": False, "stage": "review", "codex_candidates": codex_candidates, "error": err})
        return 1
    print(f"[probe] claude accepted={len(accepted)} rejected={len(rejected)}", flush=True)

    final_state: dict = {
        "ok": True,
        "ts": _now_iso(),
        "codex_candidates": codex_candidates,
        "accepted": accepted,
        "rejected": rejected,
    }

    appended: list[str] = []
    if args.append and accepted:
        appended = append_candidates_to_board(
            accepted,
            fit_threshold=args.candidate_fit_threshold,
            novelty_threshold=args.candidate_novelty_threshold,
        )
        final_state["appended_ids"] = appended
        print(f"[probe] appended {len(appended)} candidates to BOARD.md: {appended}", flush=True)

    log_path = _persist("probe", final_state)
    print(f"[probe] full record: {log_path}", flush=True)
    return 0


def cmd_curator(args: argparse.Namespace) -> int:
    print("[curator] codex meta-review pass starting...", flush=True)
    ok, codex_candidates, err = _run_codex_pass(
        PROMPTS_DIR / "curator.txt",
        "curator_codex",
        board_content=_board_text(),
        completed_summary=_completed_summary(),
    )
    if not ok:
        print(f"[curator] codex failed: {err}", flush=True)
        _persist("curator", {"ok": False, "stage": "codex", "error": err})
        return 1
    print(f"[curator] codex returned {len(codex_candidates)} candidates", flush=True)
    if not codex_candidates:
        print("[curator] empty list — nothing to review", flush=True)
        _persist("curator", {"ok": True, "codex_candidates": [], "accepted": [], "rejected": []})
        return 0

    ok, accepted, rejected, err = _run_claude_review(codex_candidates, "curator_review")
    if not ok:
        print(f"[curator] claude review failed: {err}", flush=True)
        _persist("curator", {"ok": False, "stage": "review", "codex_candidates": codex_candidates, "error": err})
        return 1
    print(f"[curator] claude accepted={len(accepted)} rejected={len(rejected)}", flush=True)

    final_state: dict = {
        "ok": True,
        "ts": _now_iso(),
        "codex_candidates": codex_candidates,
        "accepted": accepted,
        "rejected": rejected,
    }

    appended: list[str] = []
    if args.append and accepted:
        appended = append_candidates_to_board(
            accepted,
            fit_threshold=args.candidate_fit_threshold,
            novelty_threshold=args.candidate_novelty_threshold,
        )
        final_state["appended_ids"] = appended
        print(f"[curator] appended {len(appended)} candidates to BOARD.md: {appended}", flush=True)

    log_path = _persist("curator", final_state)
    print(f"[curator] full record: {log_path}", flush=True)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="BEDC auto-discovery: codex generates, claude gates")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_probe = sub.add_parser("probe", help="Codex global gap scan over papers/bedc/parts + lean4/BEDC")
    p_probe.add_argument("--append", action="store_true", help="Append accepted candidates to BOARD.md")
    p_probe.add_argument("--candidate-fit-threshold", type=int, default=DEFAULT_CANDIDATE_FIT_THRESHOLD)
    p_probe.add_argument("--candidate-novelty-threshold", type=int, default=DEFAULT_CANDIDATE_NOVELTY_THRESHOLD)
    p_probe.set_defaults(func=cmd_probe)

    p_cur = sub.add_parser("curator", help="Codex meta-review of completed targets + BOARD progress")
    p_cur.add_argument("--append", action="store_true", help="Append accepted candidates to BOARD.md")
    p_cur.add_argument("--candidate-fit-threshold", type=int, default=DEFAULT_CANDIDATE_FIT_THRESHOLD)
    p_cur.add_argument("--candidate-novelty-threshold", type=int, default=DEFAULT_CANDIDATE_NOVELTY_THRESHOLD)
    p_cur.set_defaults(func=cmd_curator)

    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())

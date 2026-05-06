#!/usr/bin/env python3
"""Active target discovery for BEDC bedc-deep.

Modes:
  probe   — codex scans papers/bedc/parts + lean4/BEDC for structural gaps,
            then claude reviews and filters; accepted candidates append to
            BOARD.md as new B-XX entries.
  curator — codex meta-review of completed-target transcripts + paper +
            BOARD progress; proposes under-represented directions, then
            claude reviews and filters.
  paper_review — paper-only referee audit over `papers/bedc/parts/`; kept
            candidates route through board_spawn before entering BOARD.

Discovery modes are invoked manually or by supervisor low-water refill, so the user can
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

import subprocess

import codex_orchestrator
import killo_golden_writeback
import board_spawn
import board_context
from locks import file_lock
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
BOARD_INCLUDE_LIMIT = 16000


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _git(args: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
    )


# Upstream integration branch we sync into bedc-claim-packet-pipeline.
# Kept in sync with dev_sync_resolver.UPSTREAM_BRANCH; switched from `dev`
# to `codex-auto-dev` because codex_formalize merges land there first
# and `dev` lags by hours-to-days.
UPSTREAM_BRANCH = "codex-auto-dev"
UPSTREAM_REF = f"origin/{UPSTREAM_BRANCH}"


def sync_dev_if_clean() -> bool:
    """Best-effort fetch + merge of the upstream integration branch. Skips
    silently on uncommitted changes or merge conflicts. Acquires
    paper_writes lock to avoid clashing with a Stage 2 .tex append.
    Returns True iff upstream commits were merged.
    """
    status = _git(["status", "--porcelain"])
    if status.stdout.strip():
        print("[discovery] sync_dev skipped: uncommitted changes", flush=True)
        return False
    _git(["fetch", "origin", UPSTREAM_BRANCH])
    behind = _git(["rev-list", "--count", f"HEAD..{UPSTREAM_REF}"])
    n = behind.stdout.strip() or "0"
    if n == "0":
        return False
    print(f"[discovery] sync_dev pulling {n} commits from {UPSTREAM_REF}", flush=True)
    with file_lock("paper_writes"):
        merge = _git(["merge", "--no-edit", UPSTREAM_REF])
    if merge.returncode != 0:
        print("[discovery] sync_dev merge failed; aborting", flush=True)
        _git(["merge", "--abort"])
        return False
    print(f"[discovery] sync_dev merged {UPSTREAM_REF} cleanly ({n} commits)", flush=True)
    return True


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _board_text() -> str:
    return board_context.build_board_prompt_context(max_chars=BOARD_INCLUDE_LIMIT)


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


def _safe(text: str) -> str:
    return (text or "").replace("{", "{{").replace("}", "}}")


def _run_claude_audit(template_path: Path, log_tag: str, **format_kwargs) -> tuple[bool, list[dict], list[dict], str]:
    """Phase 1: claude does deep paper audit, returns candidates with evidence.

    Returns (ok, candidates, rejected, error). Each candidate carries
    title / concrete_claim / local_inputs / fit_score / novelty / rationale.
    rejected is the calibration list claude considered and dropped.
    """
    template = template_path.read_text(encoding="utf-8")
    safe_kwargs = {k: _safe(v) if isinstance(v, str) else v for k, v in format_kwargs.items()}
    prompt = template.format(**safe_kwargs)
    ok, stdout, rc = killo_golden_writeback.claude_exec(prompt, timeout=PROBE_TIMEOUT, log_tag=log_tag)
    if not ok:
        fallback_ok, parsed, _fallback_stdout, fallback_error = killo_golden_writeback.codex_json_fallback(
            prompt,
            timeout=PROBE_TIMEOUT,
            log_tag=log_tag,
            role_note=(
                "Claude is unavailable for this BEDC discovery audit. Run the "
                "same paper-scan candidate discovery as a conservative Codex "
                "fallback; prefer fewer, better-evidenced candidates."
            ),
        )
        if not fallback_ok:
            return (False, [], [], f"claude exec rc={rc}: {stdout[:400]}; codex fallback: {fallback_error[:400]}")
    else:
        parsed = _extract_json_object(stdout)
    if not parsed:
        fallback_ok, parsed, _fallback_stdout, fallback_error = killo_golden_writeback.codex_json_fallback(
            prompt,
            timeout=PROBE_TIMEOUT,
            log_tag=log_tag,
            role_note=(
                "Claude returned non-JSON for this BEDC discovery audit. Run "
                "the same paper-scan candidate discovery as a conservative "
                "Codex fallback; prefer fewer, better-evidenced candidates."
            ),
        )
        if not fallback_ok:
            return (False, [], [], f"claude output was not JSON; codex fallback: {fallback_error[:400]}")
    candidates = parsed.get("candidates") or []
    rejected = parsed.get("rejected") or []
    if not isinstance(candidates, list) or not isinstance(rejected, list):
        return (False, [], [], "candidates / rejected wrong type")
    return (True, candidates, rejected, "")


def _run_codex_cross_check(candidates: list[dict], log_tag: str) -> tuple[bool, list[dict], str]:
    """Phase 2: codex independently cross-checks claude's candidates.

    Returns (ok, decisions, error). decisions is a list of
    {title, verdict: keep|drop, reason}.
    """
    if not candidates:
        return (True, [], "")
    template = (PROMPTS_DIR / "audit_cross_check.txt").read_text(encoding="utf-8")
    prompt = template.format(
        repo_root=_safe(str(REPO_ROOT)),
        board_content=_safe(_board_text()),
        candidates_json=_safe(json.dumps({"candidates": candidates}, ensure_ascii=False, indent=2)),
    )
    result = codex_orchestrator.codex_exec(prompt, timeout=REVIEW_TIMEOUT, log_tag=log_tag)
    if not result.ok:
        return (False, [], result.error or f"codex rc={result.rc}")
    parsed = result.parsed
    if not parsed:
        return (False, [], "codex output was not JSON")
    decisions = parsed.get("decisions") or []
    if not isinstance(decisions, list):
        return (False, [], "decisions field was not a list")
    return (True, decisions, "")


def _intersect_keep(candidates: list[dict], decisions: list[dict]) -> tuple[list[dict], list[dict]]:
    """Filter candidates by codex's verdicts. Returns (kept, dropped_with_reason)."""
    by_title = {c.get("title", "").strip().lower(): c for c in candidates}
    kept: list[dict] = []
    dropped: list[dict] = []
    decision_for_title: dict[str, dict] = {}
    for d in decisions:
        title = (d.get("title") or "").strip().lower()
        if title:
            decision_for_title[title] = d
    for title_low, cand in by_title.items():
        d = decision_for_title.get(title_low)
        if d is None:
            dropped.append({"title": cand.get("title"), "reason": "codex returned no decision for this candidate"})
            continue
        if (d.get("verdict") or "").lower() == "keep":
            kept.append(cand)
        else:
            dropped.append({"title": cand.get("title"), "reason": d.get("reason") or "codex dropped"})
    return kept, dropped


def _chapter_from_inputs(inputs: list[str]) -> str:
    for p in inputs:
        m = re.search(r"papers/bedc/parts/([^/]+)/", p)
        if m:
            return m.group(1)
    return "concrete_instances"


def _for_board_spawn(candidate: dict, *, mode: str) -> dict:
    """Normalize discovery candidates for the shared BOARD spawn judge.

    The discovery prompts use `concrete_claim`; board_spawn expects `claim`.
    Keep all original evidence fields, but route through the common judge so
    paper-review discoveries are not appended by a weaker side path.
    """
    inputs = candidate.get("local_inputs") or []
    out = dict(candidate)
    out["claim"] = candidate.get("claim") or candidate.get("concrete_claim") or ""
    out["chapter"] = candidate.get("chapter") or _chapter_from_inputs(inputs)
    out["source"] = mode
    return out


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


def _run_two_stage(
    args: argparse.Namespace,
    mode: str,
    claude_template: str,
    *,
    append_via_board_spawn: bool = False,
    **claude_kwargs,
) -> int:
    """Adversarial two-stage discovery: claude generates with evidence, codex
    cross-checks independently, intersection lands on BOARD."""
    if not args.no_dev_sync:
        try:
            sync_dev_if_clean()
        except Exception as exc:
            print(f"[{mode}] sync_dev error (continuing): {exc}", flush=True)

    print(f"[{mode}] phase 1: claude audit (deep paper scan with evidence)", flush=True)
    ok, claude_candidates, claude_rejected, err = _run_claude_audit(
        PROMPTS_DIR / claude_template,
        f"{mode}_claude",
        **claude_kwargs,
    )
    if not ok:
        print(f"[{mode}] phase 1 failed: {err}", flush=True)
        _persist(mode, {"ok": False, "stage": "claude_audit", "error": err})
        return 1
    print(f"[{mode}] phase 1: {len(claude_candidates)} candidates, {len(claude_rejected)} self-rejected (calibration)", flush=True)
    if not claude_candidates:
        print(f"[{mode}] phase 1 produced empty candidate list; skipping cross-check", flush=True)
        _persist(mode, {
            "ok": True,
            "ts": _now_iso(),
            "claude_candidates": [],
            "claude_rejected": claude_rejected,
            "codex_decisions": [],
            "kept": [],
            "dropped_after_cross_check": [],
        })
        return 0

    print(f"[{mode}] phase 2: codex adversarial cross-check", flush=True)
    ok, decisions, err = _run_codex_cross_check(claude_candidates, f"{mode}_codex")
    if not ok:
        print(f"[{mode}] phase 2 failed: {err}; falling back to phase-1 candidates without cross-check", flush=True)
        decisions = []
        kept = claude_candidates
        dropped = []
    else:
        kept, dropped = _intersect_keep(claude_candidates, decisions)
    print(f"[{mode}] phase 2: kept {len(kept)} of {len(claude_candidates)} (codex dropped {len(dropped)})", flush=True)

    final_state: dict = {
        "ok": True,
        "ts": _now_iso(),
        "claude_candidates": claude_candidates,
        "claude_rejected": claude_rejected,
        "codex_decisions": decisions,
        "kept": kept,
        "dropped_after_cross_check": dropped,
    }

    appended: list[str] = []
    if args.append and kept:
        if append_via_board_spawn:
            spawn_candidates = [_for_board_spawn(c, mode=mode) for c in kept]
            spawn_result = board_spawn.spawn_from_candidates(
                codex_candidates=spawn_candidates,
                oracle_candidates=[],
                fit_threshold=args.candidate_fit_threshold,
                novelty_threshold=args.candidate_novelty_threshold,
            )
            final_state["board_spawn"] = {
                "ok": spawn_result.ok,
                "error": spawn_result.error,
                "accepted": spawn_result.accepted,
                "rejected": spawn_result.rejected,
            }
            appended = spawn_result.appended_ids if spawn_result.ok else []
        else:
            appended = append_candidates_to_board(
                kept,
                fit_threshold=args.candidate_fit_threshold,
                novelty_threshold=args.candidate_novelty_threshold,
            )
        final_state["appended_ids"] = appended
        print(f"[{mode}] appended {len(appended)} to BOARD.md: {appended}", flush=True)

    log_path = _persist(mode, final_state)
    print(f"[{mode}] full record: {log_path}", flush=True)
    return 0


def cmd_probe(args: argparse.Namespace) -> int:
    return _run_two_stage(
        args,
        "probe",
        "theory_probe.txt",
        board_content=_board_text(),
    )


def cmd_curator(args: argparse.Namespace) -> int:
    return _run_two_stage(
        args,
        "curator",
        "curator.txt",
        board_content=_board_text(),
        completed_summary=_completed_summary(),
    )


def cmd_curriculum(args: argparse.Namespace) -> int:
    """Curriculum probe — find textbook-classical theorems missing from
    started chapters. Complements `probe` (which looks for internal
    symmetry gaps inside the existing paper topology). Same two-stage
    flow: claude proposes, codex adversarially audits.
    """
    return _run_two_stage(
        args,
        "curriculum",
        "curriculum_probe.txt",
        board_content=_board_text(),
    )


def cmd_paper_review(args: argparse.Namespace) -> int:
    """Paper-review probe — referee-perspective audit of the paper for
    senior-reviewer-grade revision targets (logical gaps, missing
    companions, composite consequences, constructor inversions,
    generalisations). Adapts loning's phase_review.txt approach but
    routes through our judge gate so candidates land on BOARD only after
    the same dedup / fit / novelty thresholds the other probes use.
    """
    return _run_two_stage(
        args,
        "paper_review",
        "paper_review_probe.txt",
        append_via_board_spawn=True,
        board_content=_board_text(),
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="BEDC auto-discovery: codex generates, claude gates")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_probe = sub.add_parser("probe", help="Static gap scan: definition-without-theorem, A→B without B→A, etc.")
    p_probe.add_argument("--append", action="store_true", help="Append accepted candidates to BOARD.md")
    p_probe.add_argument("--candidate-fit-threshold", type=int, default=DEFAULT_CANDIDATE_FIT_THRESHOLD)
    p_probe.add_argument("--candidate-novelty-threshold", type=int, default=DEFAULT_CANDIDATE_NOVELTY_THRESHOLD)
    p_probe.add_argument("--no-dev-sync", action="store_true", help="Skip merging upstream integration branch before scan")
    p_probe.set_defaults(func=cmd_probe)

    p_cur = sub.add_parser("curator", help="Codex meta-review of completed targets + BOARD progress")
    p_cur.add_argument("--append", action="store_true", help="Append accepted candidates to BOARD.md")
    p_cur.add_argument("--candidate-fit-threshold", type=int, default=DEFAULT_CANDIDATE_FIT_THRESHOLD)
    p_cur.add_argument("--candidate-novelty-threshold", type=int, default=DEFAULT_CANDIDATE_NOVELTY_THRESHOLD)
    p_cur.add_argument("--no-dev-sync", action="store_true", help="Skip merging upstream integration branch before scan")
    p_cur.set_defaults(func=cmd_curator)

    p_cur2 = sub.add_parser("curriculum", help="Curriculum gap scan: classical textbook theorems missing from started chapters")
    p_cur2.add_argument("--append", action="store_true", help="Append accepted candidates to BOARD.md")
    p_cur2.add_argument("--candidate-fit-threshold", type=int, default=DEFAULT_CANDIDATE_FIT_THRESHOLD)
    p_cur2.add_argument("--candidate-novelty-threshold", type=int, default=DEFAULT_CANDIDATE_NOVELTY_THRESHOLD)
    p_cur2.add_argument("--no-dev-sync", action="store_true", help="Skip merging upstream integration branch before scan")
    p_cur2.set_defaults(func=cmd_curriculum)

    p_pr = sub.add_parser("paper_review", help="Editorial-referee audit: senior-review-grade revision targets (gaps, missing companions, generalisations)")
    p_pr.add_argument("--append", action="store_true", help="Append accepted candidates to BOARD.md")
    p_pr.add_argument("--candidate-fit-threshold", type=int, default=DEFAULT_CANDIDATE_FIT_THRESHOLD)
    p_pr.add_argument("--candidate-novelty-threshold", type=int, default=DEFAULT_CANDIDATE_NOVELTY_THRESHOLD)
    p_pr.add_argument("--no-dev-sync", action="store_true", help="Skip merging upstream integration branch before scan")
    p_pr.set_defaults(func=cmd_paper_review)

    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())

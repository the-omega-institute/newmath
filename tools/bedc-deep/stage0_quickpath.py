#!/usr/bin/env python3
"""Stage Q (Stage 0) — codex+claude multi-round quick path.

Sits BEFORE Stage 1 (oracle deep reasoning). Tries to converge on a
publishable LaTeX block via several rounds of codex authorship + claude
adversarial review. Each round, codex sees its prior attempts and the
reviewer's verdicts, so the loop is genuine deepening, not paraphrase.

Verdict surface (returned to oracle_client):
  - "accept"      → Stage 0 produced a valid block; skip Stage 1, hand off
                    directly to Stage 2 (killo-golden writeback).
  - "escalate"    → Stage 0 cannot close shallowly; fall through to Stage 1
                    (oracle deep reasoning) as before. Reason field carries
                    the blocking step so the oracle can target it.

Hard rule (same as the rest of bedc-deep): this module is read-only against
the repo. It does NOT append to papers/bedc/parts/. Stage 2 owns the file
write + `make` verification step.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional

from dispatch_bedc_target import (
    BedcTarget,
    build_context_block,
    SCRIPT_DIR,
    REPO_ROOT,
)
import codex_orchestrator


PROMPTS_DIR = SCRIPT_DIR / "prompts"
LOG_DIR = SCRIPT_DIR / "state" / "stage0_logs"

CLAUDE_PATH = shutil.which("claude") or "/opt/homebrew/bin/claude"
# 6-minute budget for codex per round. Stage 0's purpose is the fast path —
# if codex needs longer, the target is genuinely deep and should escalate
# to oracle Stage 1. Empirically B-13/B-14/B-16/B-17 all closed in <4 min;
# B-18/B-19 wandered for 38 min before producing usable output, which is
# the exact cost we want to cut. The codex_orchestrator hard-kill watchdog
# enforces this by SIGKILL on the process group at timeout + 60s.
DEFAULT_CODEX_TIMEOUT = 360
DEFAULT_CLAUDE_TIMEOUT = 900
DEFAULT_MAX_ROUNDS = 4


# ---------------------------------------------------------------------------
# Small helpers (escape, log, parse)
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


def _build_target_context(target: BedcTarget) -> str:
    """Construct a single text blob that the Stage Q prompts can consume.

    Mirrors the BOARD entry view that build_initial_prompt builds for the
    oracle, but trimmed: codex/claude both have repo read access, so we
    only need the BOARD record + the keyword-selected excerpts to ground
    the conversation. The inputs path list is what the prompts'
    `local_inputs` reference points at."""
    fields_block = "\n".join(f"- {k}: {v}" for k, v in target.fields.items())
    excerpts = build_context_block(target)
    return (
        f"Target id: {target.target_id}\n"
        f"Title: {target.title}\n\n"
        f"Fields:\n{fields_block}\n\n"
        f"BOARD body:\n{target.body}\n\n"
        f"Selected local excerpts:\n{excerpts}\n"
    )


# ---------------------------------------------------------------------------
# Codex side: stage0_codex_attempt
# ---------------------------------------------------------------------------


@dataclass
class Stage0Codex:
    ok: bool
    parsed: dict
    raw_output: str
    error: str = ""


def _codex_attempt(
    *,
    target: BedcTarget,
    target_context: str,
    round_idx: int,
    cycle_history: list[dict],
) -> Stage0Codex:
    template = (PROMPTS_DIR / "stage0_codex_attempt.txt").read_text(encoding="utf-8")
    history_blob = json.dumps(cycle_history, ensure_ascii=False, indent=2) if cycle_history else "(none — first attempt)"
    prompt = template.format(
        target_id=_safe(target.target_id),
        target_title=_safe(target.title),
        target_context=_safe(target_context),
        round_idx=round_idx,
        cycle_history=_safe(history_blob),
    )
    log_tag = f"stage0_codex_{target.target_id}_r{round_idx}"
    cr = codex_orchestrator.codex_exec(
        prompt,
        timeout=DEFAULT_CODEX_TIMEOUT,
        log_tag=log_tag,
    )
    if not cr.ok:
        return Stage0Codex(False, {}, cr.raw_output, error=cr.error or f"codex rc={cr.rc}")
    if not cr.parsed:
        return Stage0Codex(False, {}, cr.raw_output, error="codex output was not JSON")
    return Stage0Codex(True, cr.parsed, cr.raw_output)


# ---------------------------------------------------------------------------
# Claude side: stage0_claude_review
# ---------------------------------------------------------------------------


@dataclass
class Stage0Review:
    ok: bool
    parsed: dict
    raw_output: str
    error: str = ""


def _claude_exec(prompt: str, *, timeout: int, log_tag: str) -> tuple[bool, str, int]:
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
    (LOG_DIR / f"{log_tag}_{ts}.stdout.txt").write_text(stdout or "", encoding="utf-8")
    (LOG_DIR / f"{log_tag}_{ts}.stderr.txt").write_text(stderr or "", encoding="utf-8")
    return (rc == 0, stdout, rc)


def _claude_review(
    *,
    target: BedcTarget,
    target_context: str,
    codex_payload: dict,
) -> Stage0Review:
    template = (PROMPTS_DIR / "stage0_claude_review.txt").read_text(encoding="utf-8")
    payload_blob = json.dumps(codex_payload, ensure_ascii=False, indent=2)
    prompt = template.format(
        target_id=_safe(target.target_id),
        target_title=_safe(target.title),
        target_context=_safe(target_context),
        codex_payload=_safe(payload_blob),
        repo_root=_safe(str(REPO_ROOT)),
    )
    log_tag = f"stage0_review_{target.target_id}"
    ok, stdout, rc = _claude_exec(prompt, timeout=DEFAULT_CLAUDE_TIMEOUT, log_tag=log_tag)
    if not ok:
        return Stage0Review(False, {}, stdout, error=f"claude rc={rc}: {stdout[:400]}")
    parsed = _extract_json_object(stdout) or {}
    if not parsed:
        return Stage0Review(False, {}, stdout, error="claude output was not JSON")
    return Stage0Review(True, parsed, stdout)


# ---------------------------------------------------------------------------
# Loop orchestrator
# ---------------------------------------------------------------------------


@dataclass
class Stage0Result:
    verdict: str  # accept | escalate | error
    content: str = ""
    tex_file: str = ""
    rounds: list[dict] = field(default_factory=list)
    reason: str = ""
    error: str = ""


def _summarize_for_history(codex: dict, review: dict) -> dict:
    """Compact per-round record fed back into codex's cycle_history.

    Codex needs to see what it tried (so it doesn't repeat) and why claude
    rejected it (so it can fix the right thing). Don't ship the full LaTeX
    body back — we want codex to genuinely rebuild, not regurgitate. Keep
    only the structural cues."""
    return {
        "round": codex.get("round"),
        "codex_verdict": codex.get("verdict"),
        "codex_reason": codex.get("reason", "")[:600],
        "codex_field_citations": codex.get("field_citations", [])[:12],
        "codex_depth_self_assessment": codex.get("depth_self_assessment"),
        "codex_convergence_signal": codex.get("convergence_signal"),
        "claude_verdict": review.get("verdict"),
        "claude_score": review.get("score"),
        "claude_rationale": review.get("rationale", "")[:600],
        "claude_rejection_reasons": review.get("rejection_reasons", [])[:8],
        "claude_escalate_reason": review.get("escalate_reason", "")[:400],
    }


def run_stage0(
    target: BedcTarget,
    *,
    max_rounds: int = DEFAULT_MAX_ROUNDS,
) -> Stage0Result:
    """Multi-round codex+claude quick path. Returns Stage0Result.

    On accept: caller writes content to raw_oracle_latex.md and skips
    Stage 1 / Stage 1.5, going directly to Stage 2 writeback.

    On escalate: caller falls through to Stage 1 (oracle) as before.
    """
    target_context = _build_target_context(target)
    history: list[dict] = []
    rounds: list[dict] = []

    for round_idx in range(max_rounds):
        print(f"[stage0] {target.target_id} round {round_idx} — codex attempt", flush=True)
        codex_t0 = time.time()
        codex_res = _codex_attempt(
            target=target,
            target_context=target_context,
            round_idx=round_idx,
            cycle_history=history,
        )
        codex_dt = time.time() - codex_t0
        if not codex_res.ok:
            print(f"[stage0] codex round {round_idx} failed: {codex_res.error}", flush=True)
            return Stage0Result(
                verdict="escalate",
                rounds=rounds,
                reason=f"codex unreachable at round {round_idx}: {codex_res.error}",
                error=codex_res.error,
            )

        codex_parsed = codex_res.parsed
        codex_verdict = str(codex_parsed.get("verdict", "")).lower()
        if codex_verdict == "needs_deep":
            reason = str(codex_parsed.get("reason", ""))
            print(
                f"[stage0] codex declared needs_deep at round {round_idx} "
                f"({codex_dt:.1f}s): {reason[:200]}",
                flush=True,
            )
            rounds.append({
                "round": round_idx,
                "codex": codex_parsed,
                "review": None,
                "outcome": "needs_deep",
            })
            return Stage0Result(
                verdict="escalate",
                rounds=rounds,
                reason=f"codex needs_deep at round {round_idx}: {reason}",
            )

        if codex_verdict != "direct":
            print(
                f"[stage0] codex returned unknown verdict '{codex_verdict}' at round {round_idx}; escalating",
                flush=True,
            )
            return Stage0Result(
                verdict="escalate",
                rounds=rounds,
                reason=f"codex unknown verdict at round {round_idx}: {codex_verdict}",
            )

        content = str(codex_parsed.get("content", ""))
        if not content.strip():
            print(f"[stage0] codex produced empty content at round {round_idx}; escalating", flush=True)
            return Stage0Result(
                verdict="escalate",
                rounds=rounds,
                reason=f"codex direct verdict but empty content at round {round_idx}",
            )

        print(
            f"[stage0] {target.target_id} round {round_idx} — claude review "
            f"(codex {codex_dt:.1f}s, {len(content)} chars)",
            flush=True,
        )
        review_t0 = time.time()
        review_res = _claude_review(
            target=target,
            target_context=target_context,
            codex_payload=codex_parsed,
        )
        review_dt = time.time() - review_t0
        if not review_res.ok:
            print(f"[stage0] claude review failed at round {round_idx}: {review_res.error}", flush=True)
            return Stage0Result(
                verdict="escalate",
                rounds=rounds,
                reason=f"claude review unreachable at round {round_idx}: {review_res.error}",
                error=review_res.error,
            )

        review_parsed = review_res.parsed
        review_verdict = str(review_parsed.get("verdict", "")).lower()
        rounds.append({
            "round": round_idx,
            "codex": codex_parsed,
            "review": review_parsed,
            "codex_seconds": codex_dt,
            "review_seconds": review_dt,
            "outcome": review_verdict,
        })

        if review_verdict == "accept":
            tex_file = str(codex_parsed.get("tex_file", ""))
            print(
                f"[stage0] {target.target_id} ACCEPT at round {round_idx} "
                f"(score={review_parsed.get('score')}); "
                f"target tex={tex_file}",
                flush=True,
            )
            return Stage0Result(
                verdict="accept",
                content=content,
                tex_file=tex_file,
                rounds=rounds,
                reason=str(review_parsed.get("rationale", "")),
            )

        if review_verdict == "accept_with_fixups":
            fixed = str(review_parsed.get("fixed_content", "")) or content
            tex_file = str(codex_parsed.get("tex_file", ""))
            print(
                f"[stage0] {target.target_id} ACCEPT_WITH_FIXUPS at round {round_idx} "
                f"(score={review_parsed.get('score')}); using claude's fixed_content "
                f"({len(fixed)} chars)",
                flush=True,
            )
            return Stage0Result(
                verdict="accept",
                content=fixed,
                tex_file=tex_file,
                rounds=rounds,
                reason=str(review_parsed.get("rationale", "")),
            )

        if review_verdict == "escalate":
            esc = str(review_parsed.get("escalate_reason", review_parsed.get("rationale", "")))
            print(
                f"[stage0] {target.target_id} ESCALATE at round {round_idx} "
                f"(score={review_parsed.get('score')}): {esc[:200]}",
                flush=True,
            )
            return Stage0Result(
                verdict="escalate",
                rounds=rounds,
                reason=f"claude escalate at round {round_idx}: {esc}",
            )

        # reject_hygiene → feed feedback into next round and continue
        if review_verdict == "reject_hygiene":
            reasons = review_parsed.get("rejection_reasons") or []
            print(
                f"[stage0] {target.target_id} REJECT_HYGIENE at round {round_idx} "
                f"(score={review_parsed.get('score')}); {len(reasons)} fixes "
                f"queued for next round",
                flush=True,
            )
            history.append(_summarize_for_history(codex_parsed, review_parsed))
            continue

        # Unknown review verdict — treat as escalate so we don't loop blindly
        print(
            f"[stage0] {target.target_id} unknown review verdict '{review_verdict}' "
            f"at round {round_idx}; escalating",
            flush=True,
        )
        return Stage0Result(
            verdict="escalate",
            rounds=rounds,
            reason=f"claude unknown verdict at round {round_idx}: {review_verdict}",
        )

    print(
        f"[stage0] {target.target_id} exhausted {max_rounds} rounds without convergence; escalating",
        flush=True,
    )
    return Stage0Result(
        verdict="escalate",
        rounds=rounds,
        reason=f"stage0 exhausted {max_rounds} rounds without convergence",
    )


# ---------------------------------------------------------------------------
# CLI smoke test
# ---------------------------------------------------------------------------


def main() -> int:
    import argparse
    from dispatch_bedc_target import parse_board

    parser = argparse.ArgumentParser(description="Stage 0 (Stage Q) quick-path smoke test")
    parser.add_argument("target_id", help="BOARD target id, e.g. B-12")
    parser.add_argument("--max-rounds", type=int, default=DEFAULT_MAX_ROUNDS)
    parser.add_argument("--out", default="", help="optional path to dump the JSON result")
    args = parser.parse_args()

    targets = parse_board()
    target = targets.get(args.target_id)
    if target is None:
        raise SystemExit(f"unknown target {args.target_id}")
    result = run_stage0(target, max_rounds=args.max_rounds)
    summary = {
        "verdict": result.verdict,
        "tex_file": result.tex_file,
        "content_chars": len(result.content),
        "reason": result.reason,
        "error": result.error,
        "rounds": [
            {
                "round": r.get("round"),
                "outcome": r.get("outcome"),
                "codex_verdict": (r.get("codex") or {}).get("verdict"),
                "review_verdict": (r.get("review") or {}).get("verdict"),
                "review_score": (r.get("review") or {}).get("score"),
            }
            for r in result.rounds
        ],
    }
    print(json.dumps(summary, ensure_ascii=False, indent=2))
    if args.out:
        Path(args.out).write_text(
            json.dumps({**summary, "content": result.content, "rounds_full": result.rounds}, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )
    return 0 if result.verdict in ("accept", "escalate") else 1


if __name__ == "__main__":
    raise SystemExit(main())

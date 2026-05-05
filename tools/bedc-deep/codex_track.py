#!/usr/bin/env python3
"""Codex track — primary research worker for BEDC paper extension.

Replaces the prior Stage 0 (stage0_quickpath) with an unbounded-round,
audit-driven codex iteration. Codex authors a LaTeX block, self-audits,
and loops until either:
  - codex declares verdict=close, audit_score≥8, claude redline check passes
    → return ("close", content, board_candidates, ...)
  - codex declares verdict=escalate (genuine math obstruction)
    → return ("escalate", reason, board_candidates, ...)
  - hard wall-clock or round ceiling fires (safety only)

claude in this loop is a *lightweight redline checker* — hygiene + safety
only, NOT a deep math review. Correctness is codex's responsibility.

Hard rule (same as the rest of bedc-deep): this module is read-only against
the repo. It does NOT append to papers/bedc/parts/. Stage write owns that.
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

from dispatch_bedc_target import (
    BedcTarget,
    build_context_block,
    SCRIPT_DIR,
    REPO_ROOT,
)
import codex_orchestrator


PROMPTS_DIR = SCRIPT_DIR / "prompts"
LOG_DIR = SCRIPT_DIR / "state" / "codex_track_logs"

CLAUDE_PATH = shutil.which("claude") or "/opt/homebrew/bin/claude"
DEFAULT_CODEX_TIMEOUT = 600
DEFAULT_REDLINE_TIMEOUT = 600
MIN_CLOSE_AUDIT_SCORE = 8

# Round ceiling is a *safety net*, not a primary terminator. Codex normally
# terminates via verdict=close or verdict=escalate. The ceiling exists only
# to protect against pathological loops where codex emits "continue" forever
# without convergence.
DEFAULT_MAX_ROUNDS = 12

# Wall-clock ceiling per target's codex track (in seconds). Codex track is
# fast by design; if it's been an hour we have a runaway.
DEFAULT_WALL_CLOCK_S = 3600


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _now_tag() -> str:
    return datetime.now().strftime("%Y%m%d_%H%M%S")


def _safe(text: str) -> str:
    return (text or "").replace("{", "{{").replace("}", "}}")


def _extract_json_object(text: str) -> Optional[dict]:
    """Robust JSON extractor — same scanner as stage0_quickpath / codex_orchestrator."""
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


def _build_target_context(target: BedcTarget) -> str:
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
# Codex side: codex_track_attempt / codex_corrective_attempt
# ---------------------------------------------------------------------------


@dataclass
class CodexAttemptResult:
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
) -> CodexAttemptResult:
    """Primary codex authoring round."""
    template = (PROMPTS_DIR / "codex_track_attempt.txt").read_text(encoding="utf-8")
    history_blob = (
        json.dumps(cycle_history, ensure_ascii=False, indent=2)
        if cycle_history
        else "(none — first attempt)"
    )
    prompt = template.format(
        target_id=_safe(target.target_id),
        target_title=_safe(target.title),
        target_context=_safe(target_context),
        round_idx=round_idx,
        cycle_history=_safe(history_blob),
    )
    log_tag = f"codex_track_{target.target_id}_r{round_idx}"
    cr = codex_orchestrator.codex_exec(
        prompt,
        timeout=DEFAULT_CODEX_TIMEOUT,
        log_tag=log_tag,
    )
    if not cr.ok:
        return CodexAttemptResult(False, {}, cr.raw_output, error=cr.error or f"codex rc={cr.rc}")
    if not cr.parsed:
        return CodexAttemptResult(False, {}, cr.raw_output, error="codex output was not JSON")
    return CodexAttemptResult(True, cr.parsed, cr.raw_output)


def _codex_corrective_attempt(
    *,
    target: BedcTarget,
    original_content: str,
    rejection_reasons: list[str],
    round_idx: int,
    cycle_history: list[dict],
) -> CodexAttemptResult:
    """Corrective codex round — fixes specific Stage write rejections without
    rewriting the proof."""
    template = (PROMPTS_DIR / "codex_corrective_attempt.txt").read_text(encoding="utf-8")
    reasons_block = "\n".join(f"- {r}" for r in rejection_reasons)
    history_blob = (
        json.dumps(cycle_history, ensure_ascii=False, indent=2)
        if cycle_history
        else "(none — first corrective attempt)"
    )
    prompt = template.format(
        target_id=_safe(target.target_id),
        target_title=_safe(target.title),
        round_idx=round_idx,
        original_content=_safe(original_content),
        rejection_reasons=_safe(reasons_block),
        cycle_history=_safe(history_blob),
    )
    log_tag = f"codex_corrective_{target.target_id}_r{round_idx}"
    cr = codex_orchestrator.codex_exec(
        prompt,
        timeout=DEFAULT_CODEX_TIMEOUT,
        log_tag=log_tag,
    )
    if not cr.ok:
        return CodexAttemptResult(False, {}, cr.raw_output, error=cr.error or f"codex rc={cr.rc}")
    if not cr.parsed:
        return CodexAttemptResult(False, {}, cr.raw_output, error="codex output was not JSON")
    return CodexAttemptResult(True, cr.parsed, cr.raw_output)


# ---------------------------------------------------------------------------
# Claude side: codex_redline_check (lightweight, hygiene-only)
# ---------------------------------------------------------------------------


@dataclass
class RedlineResult:
    ok: bool
    parsed: dict
    raw_output: str
    error: str = ""


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
    # Defensive watchdog: same pattern as codex_orchestrator. claude has
    # been seen to wedge on long prompts; this guarantees we don't sit on
    # a single redline check for hours.
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
        "Act as an independent fallback gate. Preserve the exact same checks "
        "and acceptance threshold as the original prompt, return only the "
        "requested JSON object, and do not edit files.\n\n"
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


def _redline_check(
    *,
    target: BedcTarget,
    codex_payload: dict,
) -> RedlineResult:
    template = (PROMPTS_DIR / "codex_redline_check.txt").read_text(encoding="utf-8")
    field_citations_blob = json.dumps(codex_payload.get("field_citations", []), ensure_ascii=False)
    prompt = template.format(
        target_id=_safe(target.target_id),
        target_title=_safe(target.title),
        codex_verdict=_safe(str(codex_payload.get("verdict", ""))),
        audit_score=int(codex_payload.get("audit_score", 0)),
        content=_safe(str(codex_payload.get("content", ""))),
        field_citations=_safe(field_citations_blob),
    )
    log_tag = f"codex_redline_{target.target_id}"
    ok, stdout, rc = _claude_exec(prompt, timeout=DEFAULT_REDLINE_TIMEOUT, log_tag=log_tag)
    if not ok:
        fallback_ok, parsed, fallback_stdout, fallback_error = _codex_json_fallback(
            prompt,
            timeout=DEFAULT_REDLINE_TIMEOUT,
            log_tag=log_tag,
            role_note=(
                "Claude is unavailable for the BEDC codex-track redline check. "
                "Run the same lightweight hygiene and safety redline as an "
                "independent Codex fallback."
            ),
        )
        if fallback_ok:
            return RedlineResult(True, parsed, fallback_stdout)
        return RedlineResult(
            False,
            {},
            stdout,
            error=f"claude rc={rc}: {stdout[:400]}; codex fallback: {fallback_error[:400]}",
        )
    parsed = _extract_json_object(stdout) or {}
    if not parsed:
        fallback_ok, parsed, fallback_stdout, fallback_error = _codex_json_fallback(
            prompt,
            timeout=DEFAULT_REDLINE_TIMEOUT,
            log_tag=log_tag,
            role_note=(
                "Claude returned non-JSON for the BEDC codex-track redline "
                "check. Run the same lightweight hygiene and safety redline as "
                "an independent Codex fallback."
            ),
        )
        if fallback_ok:
            return RedlineResult(True, parsed, fallback_stdout)
        return RedlineResult(False, {}, stdout, error=f"claude output was not JSON; codex fallback: {fallback_error[:400]}")
    return RedlineResult(True, parsed, stdout)


# ---------------------------------------------------------------------------
# Loop orchestrator
# ---------------------------------------------------------------------------


@dataclass
class CodexTrackResult:
    verdict: str  # close | escalate | error | duplicate_of | continue_exhausted
    content: str = ""
    tex_file: str = ""
    rounds: list[dict] = field(default_factory=list)
    reason: str = ""
    error: str = ""
    board_candidates: list[dict] = field(default_factory=list)
    duplicate_label: str = ""


def _summarize_round_for_history(codex: dict, redline: Optional[dict]) -> dict:
    """Compact per-round record fed back into codex's cycle_history.

    We keep only the structural cues (verdict, audit_score, fix_reasons),
    not the full LaTeX body — codex should genuinely rebuild on next round,
    not regurgitate."""
    return {
        "round": codex.get("round"),
        "codex_verdict": codex.get("verdict"),
        "codex_audit_score": codex.get("audit_score"),
        "codex_next_step": codex.get("next_step", "")[:400],
        "codex_escalation_reason": codex.get("escalation_reason", "")[:400],
        "redline_verdict": (redline or {}).get("verdict"),
        "redline_fix_reasons": (redline or {}).get("fix_reasons", [])[:8],
    }


def run_codex_track(
    target: BedcTarget,
    *,
    max_rounds: int = DEFAULT_MAX_ROUNDS,
    wall_clock_s: int = DEFAULT_WALL_CLOCK_S,
) -> CodexTrackResult:
    """Codex-led primary research track. Returns CodexTrackResult.

    Outcomes:
    - "close":    codex authored a complete LaTeX block, audit≥7, redline pass.
                  Caller writes content to raw_oracle_latex.md and proceeds
                  to Stage write.
    - "escalate": codex declared a genuine math obstruction OR redline reported
                  topic_mismatch. Caller routes to oracle track.
    - "error":    infrastructure failure (codex / claude unreachable).
    - "continue_exhausted": rounds or wall-clock ceiling fired before codex
                  reached a terminal verdict. Treated like escalate by caller.
    """
    target_context = _build_target_context(target)
    history: list[dict] = []
    rounds: list[dict] = []
    board_candidates: list[dict] = []
    t_start = time.time()

    for round_idx in range(max_rounds):
        if time.time() - t_start > wall_clock_s:
            print(
                f"[codex_track] {target.target_id} wall-clock ceiling {wall_clock_s}s "
                f"reached at round {round_idx}; treating as escalate",
                flush=True,
            )
            return CodexTrackResult(
                verdict="continue_exhausted",
                rounds=rounds,
                reason=f"wall-clock {wall_clock_s}s exceeded after {round_idx} rounds",
                board_candidates=board_candidates,
            )

        print(f"[codex_track] {target.target_id} round {round_idx} — codex attempt", flush=True)
        codex_t0 = time.time()
        codex_res = _codex_attempt(
            target=target,
            target_context=target_context,
            round_idx=round_idx,
            cycle_history=history,
        )
        codex_dt = time.time() - codex_t0
        if not codex_res.ok:
            print(f"[codex_track] codex round {round_idx} failed: {codex_res.error}", flush=True)
            return CodexTrackResult(
                verdict="error",
                rounds=rounds,
                reason=f"codex unreachable at round {round_idx}: {codex_res.error}",
                error=codex_res.error,
                board_candidates=board_candidates,
            )

        parsed = codex_res.parsed
        codex_verdict = str(parsed.get("verdict", "")).lower()
        audit_score = int(parsed.get("audit_score", 0) or 0)

        # Collect board candidates regardless of verdict
        for bc in parsed.get("board_candidates") or []:
            if isinstance(bc, dict):
                board_candidates.append({**bc, "source": "codex"})

        # ---- handle escalate ----
        if codex_verdict == "escalate":
            reason = str(parsed.get("escalation_reason", ""))
            print(
                f"[codex_track] {target.target_id} codex escalate at round {round_idx} "
                f"(audit={audit_score}, {codex_dt:.1f}s): {reason[:200]}",
                flush=True,
            )
            rounds.append({
                "round": round_idx,
                "codex": parsed,
                "redline": None,
                "outcome": "escalate",
                "codex_seconds": codex_dt,
            })
            return CodexTrackResult(
                verdict="escalate",
                rounds=rounds,
                reason=f"codex escalate at round {round_idx}: {reason}",
                board_candidates=board_candidates,
            )

        # ---- handle continue (no audit-pass yet) ----
        if codex_verdict == "continue":
            next_step = str(parsed.get("next_step", ""))
            print(
                f"[codex_track] {target.target_id} codex continue at round {round_idx} "
                f"(audit={audit_score}, {codex_dt:.1f}s); next: {next_step[:120]}",
                flush=True,
            )
            history.append(_summarize_round_for_history(parsed, None))
            rounds.append({
                "round": round_idx,
                "codex": parsed,
                "redline": None,
                "outcome": "continue",
                "codex_seconds": codex_dt,
            })
            continue

        # ---- handle close: invoke redline check ----
        if codex_verdict == "close":
            content = str(parsed.get("content", ""))
            if not content.strip():
                print(
                    f"[codex_track] {target.target_id} codex close but empty content — "
                    f"escalating",
                    flush=True,
                )
                return CodexTrackResult(
                    verdict="escalate",
                    rounds=rounds,
                    reason=f"codex close with empty content at round {round_idx}",
                    board_candidates=board_candidates,
                )

            if audit_score < MIN_CLOSE_AUDIT_SCORE:
                print(
                    f"[codex_track] {target.target_id} close self-rejected at round {round_idx} "
                    f"(audit={audit_score} < {MIN_CLOSE_AUDIT_SCORE}); continuing",
                    flush=True,
                )
                if not str(parsed.get("next_step", "")).strip():
                    parsed["next_step"] = (
                        f"Strengthen the proof until audit_score is at least "
                        f"{MIN_CLOSE_AUDIT_SCORE}."
                    )
                history.append(_summarize_round_for_history(parsed, None))
                rounds.append({
                    "round": round_idx,
                    "codex": parsed,
                    "redline": None,
                    "outcome": "audit_below_threshold",
                    "codex_seconds": codex_dt,
                })
                continue

            print(
                f"[codex_track] {target.target_id} round {round_idx} — redline check "
                f"(codex {codex_dt:.1f}s, audit={audit_score}, {len(content)} chars)",
                flush=True,
            )
            redline_t0 = time.time()
            redline_res = _redline_check(target=target, codex_payload=parsed)
            redline_dt = time.time() - redline_t0

            if not redline_res.ok:
                print(
                    f"[codex_track] redline check failed at round {round_idx}: "
                    f"{redline_res.error}",
                    flush=True,
                )
                # Don't escalate on infra failure — try one more codex round
                # treating this as a no-op redline. If we keep failing, ceiling
                # eventually kicks us out.
                history.append(_summarize_round_for_history(parsed, None))
                rounds.append({
                    "round": round_idx,
                    "codex": parsed,
                    "redline": {"error": redline_res.error},
                    "outcome": "redline_infra_fail",
                    "codex_seconds": codex_dt,
                    "redline_seconds": redline_dt,
                })
                continue

            redline_parsed = redline_res.parsed
            redline_verdict = str(redline_parsed.get("verdict", "")).lower()
            rounds.append({
                "round": round_idx,
                "codex": parsed,
                "redline": redline_parsed,
                "outcome": redline_verdict,
                "codex_seconds": codex_dt,
                "redline_seconds": redline_dt,
            })

            if redline_verdict == "pass":
                tex_file = str(parsed.get("tex_file", ""))
                print(
                    f"[codex_track] {target.target_id} CLOSE at round {round_idx} "
                    f"(audit={audit_score}); target tex={tex_file}",
                    flush=True,
                )
                return CodexTrackResult(
                    verdict="close",
                    content=content,
                    tex_file=tex_file,
                    rounds=rounds,
                    reason=f"codex close + redline pass at round {round_idx}",
                    board_candidates=board_candidates,
                )

            if redline_verdict == "topic_mismatch":
                fix_reasons = redline_parsed.get("fix_reasons", [])
                msg = "; ".join(fix_reasons[:3]) if fix_reasons else "topic mismatch"
                print(
                    f"[codex_track] {target.target_id} TOPIC_MISMATCH at round {round_idx}: "
                    f"{msg[:200]}; escalating to oracle",
                    flush=True,
                )
                return CodexTrackResult(
                    verdict="escalate",
                    rounds=rounds,
                    reason=f"redline topic_mismatch at round {round_idx}: {msg}",
                    board_candidates=board_candidates,
                )

            # redline_verdict == "fix_needed" → feed reasons back, another round
            fix_reasons = redline_parsed.get("fix_reasons", [])
            print(
                f"[codex_track] {target.target_id} fix_needed at round {round_idx}: "
                f"{len(fix_reasons)} reasons; codex iterates",
                flush=True,
            )
            history.append(_summarize_round_for_history(parsed, redline_parsed))
            continue

        # Unknown verdict
        print(
            f"[codex_track] {target.target_id} unknown codex verdict '{codex_verdict}' at "
            f"round {round_idx}; escalating",
            flush=True,
        )
        return CodexTrackResult(
            verdict="escalate",
            rounds=rounds,
            reason=f"codex unknown verdict at round {round_idx}: {codex_verdict}",
            board_candidates=board_candidates,
        )

    # Round ceiling reached
    print(
        f"[codex_track] {target.target_id} round ceiling {max_rounds} reached without close; "
        f"treating as escalate",
        flush=True,
    )
    return CodexTrackResult(
        verdict="continue_exhausted",
        rounds=rounds,
        reason=f"codex track exhausted {max_rounds} rounds without close",
        board_candidates=board_candidates,
    )


def run_codex_corrective_track(
    target: BedcTarget,
    *,
    original_content: str,
    rejection_reasons: list[str],
    max_rounds: int = 4,
) -> CodexTrackResult:
    """Codex corrective track — fix Stage write rejections without rewriting math.

    Outcomes:
    - "close": fixed content ready, caller re-runs Stage write.
    - "escalate": rejection requires content-level (math) work codex won't do
                  → caller routes to oracle corrective.
    - "duplicate_of": rejection was content_duplication and codex agrees.
    - "error" / "continue_exhausted": infra or budget.
    """
    history: list[dict] = []
    rounds: list[dict] = []

    current_content = original_content
    for round_idx in range(max_rounds):
        print(
            f"[codex_corrective] {target.target_id} round {round_idx} — codex repair attempt",
            flush=True,
        )
        codex_t0 = time.time()
        codex_res = _codex_corrective_attempt(
            target=target,
            original_content=current_content,
            rejection_reasons=rejection_reasons,
            round_idx=round_idx,
            cycle_history=history,
        )
        codex_dt = time.time() - codex_t0
        if not codex_res.ok:
            print(f"[codex_corrective] round {round_idx} failed: {codex_res.error}", flush=True)
            return CodexTrackResult(
                verdict="error",
                rounds=rounds,
                reason=f"codex corrective unreachable at round {round_idx}",
                error=codex_res.error,
            )

        parsed = codex_res.parsed
        codex_verdict = str(parsed.get("verdict", "")).lower()

        if codex_verdict == "duplicate_of":
            label = str(parsed.get("duplicate_label", ""))
            print(
                f"[codex_corrective] {target.target_id} declared duplicate_of {label}",
                flush=True,
            )
            return CodexTrackResult(
                verdict="duplicate_of",
                rounds=rounds,
                reason=f"codex corrective declared duplicate_of {label}",
                duplicate_label=label,
            )

        if codex_verdict == "escalate":
            reason = str(parsed.get("escalation_reason", ""))
            print(
                f"[codex_corrective] {target.target_id} escalate at round {round_idx}: {reason[:200]}",
                flush=True,
            )
            return CodexTrackResult(
                verdict="escalate",
                rounds=rounds,
                reason=f"codex corrective escalate: {reason}",
            )

        if codex_verdict == "continue":
            partial = str(parsed.get("content", "") or current_content)
            current_content = partial  # carry forward
            history.append(_summarize_round_for_history(parsed, None))
            rounds.append({"round": round_idx, "codex": parsed, "outcome": "continue"})
            continue

        if codex_verdict == "close":
            content = str(parsed.get("content", ""))
            if not content.strip():
                print(
                    f"[codex_corrective] {target.target_id} close but empty content — escalating",
                    flush=True,
                )
                return CodexTrackResult(
                    verdict="escalate",
                    rounds=rounds,
                    reason="codex corrective close with empty content",
                )
            print(
                f"[codex_corrective] {target.target_id} CLOSE at round {round_idx}",
                flush=True,
            )
            tex_file = str(parsed.get("tex_file", ""))
            rounds.append({"round": round_idx, "codex": parsed, "outcome": "close"})
            return CodexTrackResult(
                verdict="close",
                content=content,
                tex_file=tex_file,
                rounds=rounds,
                reason=f"codex corrective close at round {round_idx}",
            )

        print(
            f"[codex_corrective] unknown verdict '{codex_verdict}' at round {round_idx}; escalating",
            flush=True,
        )
        return CodexTrackResult(
            verdict="escalate",
            rounds=rounds,
            reason=f"codex corrective unknown verdict at round {round_idx}",
        )

    return CodexTrackResult(
        verdict="continue_exhausted",
        rounds=rounds,
        reason=f"codex corrective exhausted {max_rounds} rounds",
    )


# ---------------------------------------------------------------------------
# CLI smoke test
# ---------------------------------------------------------------------------


def main() -> int:
    import argparse
    from dispatch_bedc_target import parse_board

    parser = argparse.ArgumentParser(description="Codex track smoke test")
    parser.add_argument("target_id", help="BOARD target id, e.g. B-12")
    parser.add_argument("--max-rounds", type=int, default=DEFAULT_MAX_ROUNDS)
    args = parser.parse_args()

    targets = parse_board()
    target = targets.get(args.target_id)
    if target is None:
        raise SystemExit(f"unknown target {args.target_id}")
    result = run_codex_track(target, max_rounds=args.max_rounds)
    print(json.dumps({
        "verdict": result.verdict,
        "tex_file": result.tex_file,
        "content_chars": len(result.content),
        "reason": result.reason[:300],
        "rounds": len(result.rounds),
        "board_candidates": len(result.board_candidates),
        "error": result.error,
    }, ensure_ascii=False, indent=2))
    return 0 if result.verdict in ("close", "escalate") else 1


if __name__ == "__main__":
    raise SystemExit(main())

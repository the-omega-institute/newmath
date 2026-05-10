#!/usr/bin/env python3
"""BEDC target lifecycle: failure taxonomy + retry policy + next-action.

Replaces the coarse stage1_verdict/stage2.verdict pair with a structured
failure_kind plus attempts/retry_budget so supervisor can act on causes,
not just the bucketed-string verdict.

Schema additions to state/<slug>.json:
  failure_kind                str       see FAILURE_KINDS below
  attempts                    int       total run attempts so far (1 = first)
  retry_budget                int       max additional retries for this kind
  next_action                 str       complete | retry_resume | skip | alert_user
  covered_by_existing_paper   bool
  needs_prompt_repair         bool
  needs_user_intervention     bool
  mathematically_blocked      bool

derive_failure_kind reads the existing fields and computes the kind. Call
annotate(state, attempts) before writing the final state file. Both
oracle_client and supervisor use these fields to decide retry behaviour.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

SCRIPT_DIR = Path(__file__).resolve().parent
STATE_DIR = SCRIPT_DIR / "state"


# Each kind: how many retries beyond the first attempt are allowed, and what
# the supervisor should do when it next sees this state.
FAILURE_KINDS: dict[str, dict[str, Any]] = {
    "none": {
        "retry_budget": 0,
        "next_action": "complete",
    },
    "pre_flight_duplicate": {
        "retry_budget": 0,
        "next_action": "skip",
        "covered_by_existing_paper": True,
    },
    "stage2_duplicate_content": {
        "retry_budget": 0,
        "next_action": "skip",
        "covered_by_existing_paper": True,
    },
    "oracle_transport_failure": {
        "retry_budget": 5,
        "next_action": "retry_resume",
    },
    "oracle_timeout": {
        "retry_budget": 3,
        "next_action": "retry_resume",
    },
    "agent_error": {
        "retry_budget": 5,
        "next_action": "retry_resume",
    },
    "format_crash": {
        "retry_budget": 3,
        "next_action": "retry_resume",
    },
    "wall_clock_exhausted": {
        "retry_budget": 1,
        "next_action": "retry_resume",
    },
    "math_stuck": {
        "retry_budget": 0,
        "next_action": "skip",
        "mathematically_blocked": True,
    },
    "oracle_duplicate_response": {
        "retry_budget": 0,
        "next_action": "skip",
    },
    "stage2_hygiene_reject": {
        "retry_budget": 0,
        "next_action": "alert_user",
        "needs_prompt_repair": True,
    },
    "stage2_compile_failed": {
        "retry_budget": 1,
        "next_action": "retry_resume",
    },
    "stage2_blocked_after_retries": {
        "retry_budget": 0,
        "next_action": "alert_user",
        "needs_prompt_repair": True,
    },
    "unknown": {
        "retry_budget": 1,
        "next_action": "retry_resume",
    },
}


_TRANSPORT_HINTS = (
    "no response", "empty", "too short", "duplicate response",
    "connection", "timeout while waiting", "extractor",
)


def _stage1_kind_from_stuck(state: dict) -> str:
    turns = state.get("turns") or []
    if not turns:
        return "oracle_transport_failure"
    last = turns[-1]
    last_verdict = (last.get("verdict") or last.get("response_verdict") or "").lower()
    if last_verdict == "duplicate_response":
        return "oracle_duplicate_response"
    if last_verdict == "agent_error":
        return "agent_error"
    if last_verdict == "timeout":
        return "oracle_timeout"
    progress = [int(t.get("progress_delta", 0) or 0) for t in turns]
    if len(progress) >= 3 and all(p <= 1 for p in progress[-3:]):
        return "math_stuck"
    if any((t.get("verdict") or "").lower() == "timeout" for t in turns):
        return "oracle_timeout"
    err = (state.get("error") or "").lower()
    if any(h in err for h in _TRANSPORT_HINTS):
        return "oracle_transport_failure"
    return "oracle_transport_failure"


def _stage2_reject_kind(stage2: dict) -> str:
    reasons = " ".join((stage2.get("rejection_reasons") or [])).lower()
    if "content duplication" in reasons or "already stated" in reasons:
        return "stage2_duplicate_content"
    return "stage2_hygiene_reject"


def derive_failure_kind(state: dict) -> str:
    s1v = (state.get("stage1_verdict") or "").lower()
    s2 = state.get("stage2") or {}
    s2v = (s2.get("verdict") or "").lower()

    if s1v == "already_in_paper":
        return "pre_flight_duplicate"

    if s1v == "crashed":
        err = (state.get("error") or "").lower()
        if "replacement index" in err or "format" in err:
            return "format_crash"
        return "format_crash"

    if s1v == "stuck":
        return _stage1_kind_from_stuck(state)

    if s1v == "done":
        if s2v == "accept":
            return "none"
        if s2v == "duplicate_of":
            return "stage2_duplicate_content"
        if s2v == "compile_failed":
            return "stage2_compile_failed"
        if s2v == "reject":
            attempts = s2.get("attempts") or []
            if isinstance(attempts, list) and len(attempts) >= 2:
                return "stage2_blocked_after_retries"
            return _stage2_reject_kind(s2)
        return "unknown"

    return "unknown"


def annotate(state: dict, attempts: int = 1) -> dict:
    fk = derive_failure_kind(state)
    meta = FAILURE_KINDS.get(fk, FAILURE_KINDS["unknown"])
    state["failure_kind"] = fk
    state["attempts"] = max(1, attempts)
    state["retry_budget"] = meta["retry_budget"]
    state["next_action"] = meta["next_action"]
    state["covered_by_existing_paper"] = bool(meta.get("covered_by_existing_paper", False))
    state["needs_prompt_repair"] = bool(meta.get("needs_prompt_repair", False))
    state["mathematically_blocked"] = bool(meta.get("mathematically_blocked", False))
    state["needs_user_intervention"] = bool(
        state["needs_prompt_repair"] or fk == "unknown" or meta.get("next_action") == "alert_user"
    )
    return state


def decide_next_action(state: dict) -> str:
    fk = state.get("failure_kind") or derive_failure_kind(state)
    meta = FAILURE_KINDS.get(fk, FAILURE_KINDS["unknown"])
    attempts = int(state.get("attempts") or 1)
    if attempts > meta["retry_budget"]:
        if fk in {"oracle_transport_failure", "agent_error", "oracle_timeout", "format_crash"}:
            return "alert_user"
        return "skip"
    return meta["next_action"]


def is_retriable(state: dict) -> bool:
    return decide_next_action(state) == "retry_resume"


def reset_retriable(max_total_attempts: int = 6) -> int:
    """Walk state/*.json and reset entries whose next_action is retry_resume.

    Resetting means deleting the final state file. The cursor.json is
    preserved with attempts incremented so a fresh run resumes from the
    saved turns. After max_total_attempts the entry stays untouched even
    if the kind would normally be retriable, as a hard backstop.
    """
    if not STATE_DIR.exists():
        return 0
    reset = 0
    for state_file in STATE_DIR.glob("*.json"):
        # Utility state files like loning_watch_state.json are not crashed BOARD targets.
        if not re.match(r"^b-\d+_", state_file.stem):
            continue
        try:
            data = json.loads(state_file.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        action = decide_next_action(data)
        if action != "retry_resume":
            continue
        attempts = int(data.get("attempts") or 1)
        if attempts >= max_total_attempts:
            continue
        slug = state_file.stem
        cursor_path = STATE_DIR / slug / "cursor.json"
        cursor_blob: dict = {}
        if cursor_path.exists():
            try:
                cursor_blob = json.loads(cursor_path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                cursor_blob = {}
        cursor_blob["attempts"] = attempts + 1
        cursor_blob["last_failure_kind"] = data.get("failure_kind", "unknown")
        try:
            cursor_path.parent.mkdir(parents=True, exist_ok=True)
            tmp = cursor_path.with_suffix(cursor_path.suffix + ".tmp")
            tmp.write_text(
                json.dumps(cursor_blob, ensure_ascii=False, indent=2) + "\n",
                encoding="utf-8",
            )
            tmp.replace(cursor_path)
            state_file.unlink()
            reset += 1
            print(
                f"[lifecycle] reset {slug} kind={data.get('failure_kind')} "
                f"attempt {attempts + 1}/{max_total_attempts}",
                flush=True,
            )
        except OSError:
            pass
    return reset


def histogram() -> dict[str, int]:
    """Aggregate failure_kind across all final state files."""
    counts: dict[str, int] = {}
    if not STATE_DIR.exists():
        return counts
    for state_file in STATE_DIR.glob("*.json"):
        try:
            data = json.loads(state_file.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        kind = data.get("failure_kind") or derive_failure_kind(data)
        counts[kind] = counts.get(kind, 0) + 1
    return counts

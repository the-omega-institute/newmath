#!/usr/bin/env python3
"""Compact BOARD context for model prompts.

BOARD.md is an append-only task ledger. Completion is recorded by state/*.json,
so prompt builders should not include old completed entries as full task
blocks. This module keeps the ledger semantics intact while giving model
prompts a compact, current view.
"""

from __future__ import annotations

import re
from pathlib import Path

import board_archive
from dispatch_bedc_target import BOARD_PATH, SCRIPT_DIR, BedcTarget, parse_board


STATE_DIR = SCRIPT_DIR / "state"
DEFAULT_MAX_CHARS = 16000


def _target_state(target: BedcTarget) -> str:
    if (STATE_DIR / f"{target.slug}.json").exists():
        return "completed"
    state_dir = STATE_DIR / target.slug
    if (state_dir / ".in_progress").exists():
        return "in_progress"
    if (state_dir / ".oracle_pending").exists():
        return "oracle_pending"
    return "pending"


def _first_problem_line(target: BedcTarget, *, max_len: int = 220) -> str:
    in_problem = False
    for raw in target.body.splitlines():
        line = raw.strip()
        if line == "Problem:":
            in_problem = True
            continue
        if not in_problem:
            continue
        if not line:
            continue
        if line.endswith(":") and not line.startswith("\\"):
            break
        return (line[: max_len - 3] + "...") if len(line) > max_len else line
    return ""


def _local_inputs(target: BedcTarget, *, max_items: int = 3) -> str:
    paths: list[str] = []
    in_inputs = False
    for raw in target.body.splitlines():
        line = raw.strip()
        if line == "Local inputs:":
            in_inputs = True
            continue
        if in_inputs and not line:
            continue
        if in_inputs and not line.startswith("-"):
            break
        if in_inputs:
            m = re.search(r"`([^`]+)`", line)
            if m:
                paths.append(m.group(1))
    if not paths:
        return ""
    shown = paths[:max_items]
    more = "" if len(paths) <= max_items else f"; +{len(paths) - max_items} more"
    return "; ".join(shown) + more


def _target_line(target: BedcTarget, state: str, *, include_problem: bool) -> str:
    fields = target.fields
    bits = [
        f"- {target.target_id} [{state}] {target.title}",
    ]
    obj = fields.get("Object")
    layer = fields.get("Layer")
    source = fields.get("Source")
    if obj and obj != target.title:
        bits.append(f"object={obj}")
    if layer:
        bits.append(f"layer={layer}")
    if source:
        bits.append(f"source={source}")
    inputs = _local_inputs(target)
    if inputs:
        bits.append(f"inputs={inputs}")
    if include_problem:
        problem = _first_problem_line(target)
        if problem:
            bits.append(f"problem={problem}")
    return " | ".join(bits)


def _fit_to_limit(lines: list[str], max_chars: int) -> str:
    out: list[str] = []
    used = 0
    for line in lines:
        add = len(line) + 1
        if used + add > max_chars:
            remaining = len(lines) - len(out)
            note = f"... ({remaining} lines omitted by BOARD context cap)"
            budget = max_chars - used
            if budget > 4:
                out.append(note[: budget - 1])
            break
        out.append(line)
        used += add
    return "\n".join(out)


def build_board_prompt_context(
    *,
    max_chars: int = DEFAULT_MAX_CHARS,
    active_limit: int = 80,
    recent_completed_limit: int = 24,
) -> str:
    """Return a compact BOARD view for discovery / refill / judge prompts."""

    active_targets = list(parse_board().values()) if BOARD_PATH.exists() else []
    archived_targets = list(board_archive.parse_board_file(board_archive.COMPLETED_BOARD_PATH).values())
    all_targets = active_targets + archived_targets
    if not all_targets:
        return "(empty BOARD)"

    states = {t.target_id: _target_state(t) for t in active_targets}
    active = [t for t in active_targets if states[t.target_id] != "completed"]
    completed = [t for t in active_targets if states[t.target_id] == "completed"] + archived_targets
    recent_completed = list(reversed(completed))[:recent_completed_limit]

    lines: list[str] = [
        "BOARD compact context.",
        "Completion is state-file based; completed task bodies are not repeated here.",
        (
            f"Counts: total={len(all_targets)} active={len(active)} "
            f"completed={len(completed)} pending={sum(1 for t in active if states[t.target_id] == 'pending')} "
            f"in_progress={sum(1 for t in active if states[t.target_id] == 'in_progress')} "
            f"oracle_pending={sum(1 for t in active if states[t.target_id] == 'oracle_pending')}"
        ),
        "",
        "## Active BOARD targets",
    ]

    if active:
        for target in active[:active_limit]:
            lines.append(_target_line(target, states[target.target_id], include_problem=True))
        if len(active) > active_limit:
            lines.append(f"... ({len(active) - active_limit} additional active targets omitted)")
    else:
        lines.append("(none)")

    lines.extend(["", "## Recently Completed BOARD targets"])
    if recent_completed:
        for target in recent_completed:
            lines.append(_target_line(target, "completed", include_problem=False))
    else:
        lines.append("(none)")

    lines.extend(["", "## Existing BOARD title index"])
    def _target_num(target: BedcTarget) -> int:
        try:
            return int(target.target_id.split("-")[1])
        except (IndexError, ValueError):
            return -1

    for target in sorted(all_targets, key=_target_num, reverse=True):
        lines.append(f"- {target.target_id} {target.title}")

    return _fit_to_limit(lines, max_chars)


def main() -> int:
    print(build_board_prompt_context())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Emit honest Nat-value bridge candidates for the bridge daemon.

The rows here are only for pointwise/readback exported_core bridges: an existing
BEDC.Derived Nat-valued sequence or count is compared with a pre-existing
mathlib Nat declaration or formula surface. They are not structural carrier
bridges. The feeder surfaces structural Nat-sequence evidence and leaves the
mathlib target judgement to the worker.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

import bridge_coverage_gap


THEOREM_RE = re.compile(r"\b(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)\b")
DECL_HEADER_RE = re.compile(
    r"(?ms)^\s*(?:abbrev|def)\s+([A-Za-z_][A-Za-z0-9_']*)\b(.*?)(?::=|\n\s*\|)"
)
THEOREM_HINT_RE = re.compile(
    r"(?:recurrence|recursion|succ|successor|closed|closedForm|closed_form|"
    r"closedFormula|closed_formula|formula|_eq_|zero)",
    re.IGNORECASE,
)
def source_theorem_guesses(root: Path, row: dict) -> list[str]:
    file_value = row.get("file")
    namespace = row.get("namespace")
    if not isinstance(file_value, str) or not isinstance(namespace, str):
        return []
    path = root / file_value
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return []
    guesses: list[str] = []
    for match in THEOREM_RE.finditer(text):
        name = match.group(1)
        if THEOREM_HINT_RE.search(name):
            guesses.append(f"{namespace}.{name}")
        if len(guesses) >= 8:
            break
    return guesses


def _last_top_level_colon(text: str) -> int:
    depth = 0
    found = -1
    for index, char in enumerate(text):
        if char in "([{":
            depth += 1
        elif char in ")]}" and depth > 0:
            depth -= 1
        elif char == ":" and depth == 0:
            found = index
    return found


def _split_top_level_arrows(text: str) -> list[str]:
    clean = text.replace("→", "->")
    parts: list[str] = []
    start = 0
    depth = 0
    index = 0
    while index < len(clean):
        char = clean[index]
        if char in "([{":
            depth += 1
            index += 1
        elif char in ")]}" and depth > 0:
            depth -= 1
            index += 1
        elif clean.startswith("->", index) and depth == 0:
            parts.append(clean[start:index].strip())
            index += 2
            start = index
        else:
            index += 1
    parts.append(clean[start:].strip())
    return parts


def _nat_atom(text: str) -> bool:
    item = text.strip()
    while item.startswith("(") and item.endswith(")"):
        item = item[1:-1].strip()
    return item == "Nat"


BINDER_RE = re.compile(r"[\(\{\[]([^()\[\]{}]*:[^()\[\]{}]*)[\)\}\]]")


def _binder_nat_arity(content: str) -> int | None:
    colon = _last_top_level_colon(content)
    if colon < 0:
        return None
    names = content[:colon].strip()
    typ = content[colon + 1 :].strip()
    if not _nat_atom(typ):
        return None
    return max(1, len([part for part in names.split() if part != "_"]))


def _pure_nat_type(prefix: str, typ: str) -> bool:
    arity = 0
    spans: list[tuple[int, int]] = []
    for match in BINDER_RE.finditer(prefix):
        binder_arity = _binder_nat_arity(match.group(1))
        if binder_arity is None:
            return False
        arity += binder_arity
        spans.append(match.span())
    remainder_parts: list[str] = []
    cursor = 0
    for start, end in spans:
        remainder_parts.append(prefix[cursor:start])
        cursor = end
    remainder_parts.append(prefix[cursor:])
    if "".join(remainder_parts).strip():
        return False
    parts = _split_top_level_arrows(typ)
    arity += max(0, len(parts) - 1)
    return arity > 0 and bool(parts) and all(_nat_atom(part) for part in parts)


def pure_nat_value_decls(root: Path, row: dict) -> list[str]:
    file_value = row.get("file")
    namespace = row.get("namespace")
    if not isinstance(file_value, str) or not isinstance(namespace, str):
        return []
    try:
        text = (root / file_value).read_text(encoding="utf-8")
    except OSError:
        return []
    decls: list[str] = []
    for match in DECL_HEADER_RE.finditer(text):
        name = match.group(1)
        header = match.group(2)
        colon = _last_top_level_colon(header)
        if colon < 0:
            continue
        prefix = header[:colon]
        typ = header[colon + 1 :]
        if _pure_nat_type(prefix, typ):
            decls.append(f"{namespace}.{name}")
    return decls


def build_candidates(root: Path) -> dict:
    base = bridge_coverage_gap.scan(root)
    worklist = []
    for row in base.get("worklist", []):
        if not isinstance(row, dict):
            continue
        raw_decls = [decl for decl in row.get("bridge_decls", []) if isinstance(decl, str)]
        all_value_decls = pure_nat_value_decls(root, row)
        value_decls = [decl for decl in raw_decls if decl in set(all_value_decls)]
        decls = value_decls or raw_decls
        theorem_guesses = [
            theorem
            for theorem in row.get("bedc_source_theorem_guess", [])
            if isinstance(theorem, str)
        ] or source_theorem_guesses(root, row)
        has_theorem = bool(row.get("has_recurrence_or_closedform_theorem") or theorem_guesses)
        eligible = bool(has_theorem and value_decls)
        item = {
            **row,
            "bridge_decls": decls,
            "bedc_decl": decls[0] if decls else None,
            "mathlib_target_guess": None,
            "mathlib_class_guess": None,
            "mathlib_instance_guess": None,
            "correspondence_shape_guess": "pointwise_eq",
            "bridge_kind": "nat_value_sequence",
            "has_recurrence_or_closedform_theorem": has_theorem,
            "bedc_source_theorem_guess": theorem_guesses,
            "bedc_consumed_decl_guess": theorem_guesses[:3],
            "eligible": eligible,
            "source": "nat-sequence-worklist",
        }
        if not value_decls:
            item["exclude_reason"] = "no_pure_nat_value_source_decl"
        elif not has_theorem:
            item["exclude_reason"] = "no_bedc_recurrence_or_closedform_theorem"
        else:
            item["exclude_reason"] = None
        worklist.append(item)
    worklist.sort(
        key=lambda item: (
            not bool(item.get("eligible")),
            -int(item.get("priority", 0)),
            str(item.get("carrier", "")),
        )
    )
    eligible_count = sum(1 for item in worklist if item.get("eligible"))
    return {
        "class": "nat_value_sequence_bridge_candidates",
        "daemon_eligible": eligible_count > 0,
        "candidate_kind": "nat_value_sequence",
        "note": (
            "Eligible rows are pointwise/readback Nat-value bridge candidates "
            "with existing BEDC.Derived sources and structural theorem signals; "
            "the worker must choose or reject the mathlib target."
        ),
        "total_bridge_shaped_carriers": base.get("total_bridge_shaped_carriers", 0),
        "already_in_matrix": base.get("already_in_matrix", 0),
        "contested_open_feat_bridge": base.get("contested_open_feat_bridge", 0),
        "without_recurrence_or_closedform_signal": base.get(
            "without_recurrence_or_closedform_signal", 0
        ),
        "uncontested_unbridged": base.get("uncontested_unbridged", len(worklist)),
        "eligible_candidates": eligible_count,
        "worklist": worklist,
    }


def repo_root() -> Path:
    return bridge_coverage_gap.repo_root()


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="machine-readable output")
    parser.add_argument("--top", type=int, default=0, help="only the highest-priority N")
    args = parser.parse_args(argv)

    result = build_candidates(repo_root())
    if args.top:
        result["worklist"] = result["worklist"][: args.top]
    if args.json:
        print(json.dumps(result, indent=2))
        return 0
    print(
        f"nat value bridge candidates: {result['eligible_candidates']} eligible | "
        f"{result['uncontested_unbridged']} uncontested-unbridged"
    )
    for row in result["worklist"]:
        status = "eligible" if row.get("eligible") else str(row.get("exclude_reason"))
        print(
            f"  p{row.get('priority', 0)} [{status}] {row.get('carrier')} -> "
            f"{row.get('mathlib_target_guess') or 'unknown'}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

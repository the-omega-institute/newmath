#!/usr/bin/env python3
"""Emit honest Nat-value bridge candidates for the bridge daemon.

The rows here are only for pointwise/readback exported_core bridges: an existing
BEDC.Derived Nat-valued sequence or count is compared with a pre-existing
mathlib Nat declaration or formula surface. They are not structural carrier
bridges, and unknown mathlib targets remain visible as telemetry with
eligible=false.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

import bridge_coverage_gap


TARGET_HINTS: tuple[tuple[tuple[str, ...], str], ...] = (
    (
        (
            "Lobb",
            "Raney",
            "Narayana",
            "Tetrahedral",
            "Triangular",
            "CakeNumber",
            "FussCatalan",
            "Lah",
        ),
        "Nat.choose",
    ),
    (("PolygonalNumberTriangular",), "Nat.choose"),
    (("Catalan",), "Nat.centralBinom"),
    (("Fibonacci", "Lucas", "Leonardo", "Jacobsthal", "Tribonacci"), "Nat.fib"),
    (("Factorial", "EuclidFactorial", "Eulerian"), "Nat.factorial"),
    (("Superfactorial",), "Nat.superFactorial"),
    (("Derangement",), "numDerangements"),
    (("StirlingFirst",), "Nat.stirlingFirst"),
    (("StirlingSecond",), "Nat.stirlingSecond"),
    (("DescFactorial", "FallingFactorial"), "Nat.descFactorial"),
)

HARD_TELEMETRY_TERMS = (
    "Bernoulli",
    "EulerPoly",
    "EulerPolynomial",
    "Bell",
    "Genocchi",
    "Tangent",
    "Secant",
    "Partition",
    "Overpartition",
    "Harmonic",
    "Hyperharmonic",
    "Hermite",
    "Faulhaber",
)

THEOREM_RE = re.compile(r"\b(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)\b")
DECL_HEADER_RE = re.compile(
    r"(?ms)^\s*(?:abbrev|def)\s+([A-Za-z_][A-Za-z0-9_']*)\b(.*?)(?::=|\n\s*\|)"
)
THEOREM_HINT_RE = re.compile(
    r"(?:recurrence|succ|closed|closedForm|_eq_|zero|one|boundary|spec|pascal|choose|factorial)",
    re.IGNORECASE,
)
PRIMARY_DECL_TERMS = (
    "Number",
    "Count",
    "Value",
    "Term",
    "Nat",
    "At",
    "Fn",
    "fn",
)
HELPER_DECL_TERMS = (
    "Closed",
    "Numerator",
    "Denominator",
    "Prefix",
    "Step",
    "Fuel",
    "Layer",
    "Row",
    "Raw",
    "raw",
    "Seq",
    "Aux",
    "Acc",
    "Helper",
    "List",
    "Tail",
    "Drop",
    "Fold",
    "Loop",
)
NON_NAT_INPUT_TERMS = (
    "BHist",
    "List",
    "Bool",
    "Int",
    "IntegerUp",
    "Prop",
    "Option",
    "GoldenPhiPair",
    "Z",
)


def target_hint(carrier: str, decls: list[str]) -> str | None:
    haystack = " ".join([carrier, *decls])
    for terms, target in TARGET_HINTS:
        if any(term in haystack for term in terms):
            return target
    return None


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


def _pure_nat_type(prefix: str, typ: str) -> bool:
    if any(term in prefix for term in NON_NAT_INPUT_TERMS):
        return False
    clean = " ".join(typ.replace("→", "->").split())
    parts = [part.strip(" ()") for part in clean.split("->")]
    return bool(parts) and all(part == "Nat" for part in parts)


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


def hard_telemetry_only(carrier: str) -> bool:
    return any(term in carrier for term in HARD_TELEMETRY_TERMS)


def primary_bedc_decl(decls: list[str]) -> str | None:
    if not decls:
        return None

    def rank(decl: str) -> tuple[int, int, int, str]:
        terminal = decl.rsplit(".", 1)[-1]
        is_helper = 1 if any(term in terminal for term in HELPER_DECL_TERMS) else 0
        is_primary = 0 if any(term in terminal for term in PRIMARY_DECL_TERMS) else 1
        return (is_helper, is_primary, len(terminal), terminal)

    return sorted(decls, key=rank)[0]


def build_candidates(root: Path) -> dict:
    base = bridge_coverage_gap.scan(root)
    worklist = []
    for row in base.get("worklist", []):
        if not isinstance(row, dict):
            continue
        raw_decls = [decl for decl in row.get("bridge_decls", []) if isinstance(decl, str)]
        value_decls = pure_nat_value_decls(root, row)
        decls = value_decls or raw_decls
        carrier = str(row.get("carrier") or "")
        target = target_hint(carrier, decls)
        theorem_guesses = source_theorem_guesses(root, row)
        has_theorem = bool(row.get("has_recurrence_or_closedform_theorem") or theorem_guesses)
        eligible = bool(target and has_theorem and value_decls and not hard_telemetry_only(carrier))
        item = {
            **row,
            "bridge_decls": decls,
            "bedc_decl": primary_bedc_decl(decls),
            "mathlib_target_guess": target,
            "mathlib_class_guess": target,
            "mathlib_instance_guess": target,
            "correspondence_shape_guess": "pointwise_eq",
            "bridge_kind": "nat_value_sequence",
            "has_recurrence_or_closedform_theorem": has_theorem,
            "bedc_source_theorem_guess": theorem_guesses,
            "bedc_consumed_decl_guess": theorem_guesses[:3],
            "eligible": eligible,
            "source": "nat-sequence-worklist",
        }
        if target is None:
            item["exclude_reason"] = "no_conservative_mathlib_target_hint"
        elif not value_decls:
            item["exclude_reason"] = "no_pure_nat_value_source_decl"
        elif not has_theorem:
            item["exclude_reason"] = "no_bedc_recurrence_or_closedform_theorem"
        elif hard_telemetry_only(carrier):
            item["exclude_reason"] = "rat_finset_or_boundary_telemetry_only"
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
            "with existing BEDC.Derived sources and conservative mathlib target hints."
        ),
        "total_bridge_shaped_carriers": base.get("total_bridge_shaped_carriers", 0),
        "already_in_matrix": base.get("already_in_matrix", 0),
        "contested_open_feat_bridge": base.get("contested_open_feat_bridge", 0),
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

#!/usr/bin/env python3
"""Deterministic gate for BEDC logic-minimization packet metadata."""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any

try:
    from logic_discipline import (
        EXISTENCE_MODES,
        EQUALITY_KINDS,
        INTERPRETATION_KINDS,
        ORACLE_MODES,
        STRENGTH_LEVELS,
    )
except ModuleNotFoundError:  # pragma: no cover
    import sys
    from pathlib import Path

    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    from logic_discipline import (
        EXISTENCE_MODES,
        EQUALITY_KINDS,
        INTERPRETATION_KINDS,
        ORACLE_MODES,
        STRENGTH_LEVELS,
    )


EXISTENCE_RE = re.compile(
    r"\b(exists?|there exists|admits?|has a|has an|there is|inhabited|witness)\b",
    re.IGNORECASE,
)
BRIDGE_RE = re.compile(
    r"\b(bridge|transport|translation|continuation|intermediate|factor|factors|composition|compose|handoff)\b",
    re.IGNORECASE,
)
EQUALITY_RE = re.compile(
    r"\b(equal|equality|same|equivalent|equivalence|isomorphic|isomorphism|bisimilar|bisimulation|mirror|corresponds?)\b",
    re.IGNORECASE,
)
COMPLETION_RE = re.compile(
    r"\b(limit|completion|complete|compact|compactness|continuous|continuity|Cauchy|converge|convergence)\b",
    re.IGNORECASE,
)
RATE_SURFACE_RE = re.compile(
    r"\b(rate|modulus|finite cover|finite-cover|tail bound|tail-bound|tail|schedule|threshold|window|finite witness)\b",
    re.IGNORECASE,
)
DETERMINISTIC_ORACLE_RE = re.compile(
    r"\b(definition expansion|normalization|obligation split|schema check|label dedup|dedup|format check)\b",
    re.IGNORECASE,
)

BASE_REQUIRED = {
    "axiom_budget": 8,
    "strength_level": 8,
    "budget_reason": 30,
}
NEW_CHAPTER_REQUIRED = {
    "dependency_trace": 30,
    "resource_trace": 30,
}


@dataclass
class GateResult:
    ok: bool
    reasons: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)


def field_text(record: dict[str, Any], key: str) -> str:
    value = record.get(key)
    if isinstance(value, list):
        return " ".join(str(v).strip() for v in value if str(v).strip())
    return str(value or "").strip()


def _claim_text(record: dict[str, Any]) -> str:
    parts = [
        field_text(record, "title"),
        field_text(record, "claim"),
        field_text(record, "concrete_claim"),
        field_text(record, "rationale"),
        field_text(record, "chapter_worthiness"),
    ]
    return "\n".join(p for p in parts if p)


def _missing_min(record: dict[str, Any], required: dict[str, int]) -> list[str]:
    missing: list[str] = []
    for key, min_len in required.items():
        if len(field_text(record, key)) < min_len:
            missing.append(key)
    return missing


def validate_logic_packet(record: dict[str, Any]) -> GateResult:
    """Validate logic-minimization fields for a candidate packet.

    The gate is intentionally conditional.  Every accepted BOARD theorem needs
    a visible axiom/strength surface; bridge, existence, equality, completion,
    and chapter-level packets trigger their own smaller required surfaces.
    """
    reasons: list[str] = []
    warnings: list[str] = []
    text = _claim_text(record)
    landing_kind = field_text(record, "landing_kind")

    missing_base = _missing_min(record, BASE_REQUIRED)
    if missing_base:
        reasons.append("missing_logic_budget:" + ",".join(missing_base))

    axiom_budget = field_text(record, "axiom_budget")
    strength_level = field_text(record, "strength_level")
    if axiom_budget and axiom_budget not in STRENGTH_LEVELS:
        reasons.append(f"invalid_axiom_budget:{axiom_budget[:60]}")
    if strength_level and strength_level not in STRENGTH_LEVELS:
        reasons.append(f"invalid_strength_level:{strength_level[:60]}")
    if strength_level == "B5_impredicative_or_choice_like":
        if not re.search(r"\b(obstruction|boundary|nonconstructive|failure|impossib|cannot)\b", text, re.I):
            reasons.append("choice_like_strength_requires_boundary_or_obstruction")

    if landing_kind == "new_chapter":
        missing_chapter = _missing_min(record, NEW_CHAPTER_REQUIRED)
        if missing_chapter:
            reasons.append("missing_chapter_logic_trace:" + ",".join(missing_chapter))

    if EXISTENCE_RE.search(text):
        existence_mode = field_text(record, "existence_mode")
        witness = field_text(record, "witness_extractor")
        if not existence_mode:
            reasons.append("existence_missing_existence_mode")
        elif existence_mode not in EXISTENCE_MODES and existence_mode != "none":
            reasons.append(f"invalid_existence_mode:{existence_mode[:60]}")
        if existence_mode not in {"", "none", "classical_noncomputable"} and len(witness) < 25:
            reasons.append("existence_missing_witness_extractor")

    if BRIDGE_RE.search(text):
        cut_rank = field_text(record, "cut_rank")
        if not cut_rank:
            reasons.append("bridge_missing_cut_rank")
        elif cut_rank not in {"0", "1", "2", "noneliminable", "unknown"}:
            reasons.append(f"invalid_cut_rank:{cut_rank[:60]}")
        if len(field_text(record, "elimination_plan")) < 30:
            reasons.append("bridge_missing_elimination_plan")
        interpretation_kind = field_text(record, "interpretation_kind")
        if interpretation_kind and interpretation_kind not in INTERPRETATION_KINDS:
            reasons.append(f"invalid_interpretation_kind:{interpretation_kind[:60]}")

    if EQUALITY_RE.search(text):
        equality_kind = field_text(record, "equality_kind")
        if not equality_kind:
            reasons.append("equality_missing_equality_kind")
        elif equality_kind not in EQUALITY_KINDS and equality_kind != "none":
            reasons.append(f"invalid_equality_kind:{equality_kind[:60]}")

    if COMPLETION_RE.search(text):
        surface = " ".join([
            text,
            field_text(record, "rate_modulus_surface"),
            field_text(record, "budget_reason"),
            field_text(record, "witness_extractor"),
        ])
        if not RATE_SURFACE_RE.search(surface):
            reasons.append("completion_missing_rate_modulus_surface")

    oracle_mode = field_text(record, "oracle_mode")
    if oracle_mode:
        if oracle_mode not in ORACLE_MODES:
            reasons.append(f"invalid_oracle_mode:{oracle_mode[:60]}")
        elif oracle_mode == "deterministic_only":
            reasons.append("deterministic_only_work_not_board_candidate")
    if DETERMINISTIC_ORACLE_RE.search(text):
        warnings.append("candidate_mentions_deterministic_work")

    return GateResult(ok=not reasons, reasons=reasons, warnings=warnings)


def render_schema_hint() -> str:
    return (
        "Logic packet fields: axiom_budget, strength_level, budget_reason, "
        "witness_extractor, existence_mode, cut_rank, elimination_plan, "
        "equality_kind, interpretation_kind, resource_trace, dependency_trace, "
        "rate_modulus_surface, oracle_mode."
    )

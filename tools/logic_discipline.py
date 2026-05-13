#!/usr/bin/env python3
"""Shared BEDC/NewMath logic-minimization discipline.

This module is deliberately declarative.  It gives the BEDC oracle lane,
board refill, and Automath-NewMath bridge the same vocabulary without changing
their runtime scheduling semantics.
"""

from __future__ import annotations

from typing import Any


LOGIC_DISCIPLINE_VERSION = "logic-discipline-v1"

PRINCIPLES: list[dict[str, str]] = [
    {
        "id": "no_object_without_eliminator",
        "name": "No Object Without Eliminator",
        "gate": (
            "A core object must expose introduction, observation, equality, "
            "and eliminator surfaces."
        ),
    },
    {
        "id": "no_existence_without_witness",
        "name": "No Existence Without Witness",
        "gate": (
            "Existence claims must name a witness extractor or remain "
            "non-constructive."
        ),
    },
    {
        "id": "no_bridge_without_cutrank",
        "name": "No Bridge Without CutRank",
        "gate": (
            "Bridge records must say whether the intermediate bridge can be "
            "eliminated and how."
        ),
    },
    {
        "id": "no_theorem_without_axiom_budget",
        "name": "No Theorem Without Axiom Budget",
        "gate": (
            "Theorem packets must declare the weakest resource/axiom level "
            "they consume."
        ),
    },
    {
        "id": "no_descent_without_certificate",
        "name": "No Descent Without Certificate",
        "gate": (
            "Lean, Automath, Rule110, or FKernel descent requires a checkable "
            "certificate."
        ),
    },
    {
        "id": "no_equality_without_equality_kind",
        "name": "No Equality Without Equality Kind",
        "gate": (
            "Definitional equality, isomorphism, equivalence, bisimulation, "
            "and mirror are distinct."
        ),
    },
    {
        "id": "no_context_collapse",
        "name": "No Context Collapse",
        "gate": (
            "Classes, descriptions, quotients, and completions stay "
            "contextual until eliminated."
        ),
    },
    {
        "id": "no_hidden_resource_copy",
        "name": "No Hidden Resource Copy",
        "gate": (
            "History, observation, oracle output, and certificates may only "
            "be copied with provenance."
        ),
    },
    {
        "id": "no_irrelevant_dependency",
        "name": "No Irrelevant Dependency",
        "gate": (
            "Packets must distinguish used dependencies from ambient context."
        ),
    },
    {
        "id": "no_oracle_for_invertible_work",
        "name": "No Oracle For Invertible Work",
        "gate": (
            "Definition expansion, normalization, schema checks, and "
            "obligation splits are deterministic."
        ),
    },
    {
        "id": "no_merge_without_interpretation_kind",
        "name": "No Merge Without Interpretation Kind",
        "gate": (
            "Cross-system moves must be tagged as definition, conservative "
            "extension, interpretation, embedding, projection, or heuristic."
        ),
    },
    {
        "id": "no_completion_without_rate_modulus_surface",
        "name": "No Completion Without Rate/Modulus Surface",
        "gate": (
            "Limit, completion, compactness, and continuity claims should "
            "expose rate, modulus, finite cover, or tail-bound surfaces."
        ),
    },
]

STRENGTH_LEVELS = [
    "B0_finite_witness",
    "B1_primitive_recursive_schedule",
    "B2_rate_or_modulus",
    "B3_finite_cover_or_compactness",
    "B4_countable_construction",
    "B5_impredicative_or_choice_like",
]

EQUALITY_KINDS = [
    "definitional_equal",
    "propositionally_equal",
    "isomorphic",
    "equivalent",
    "bisimilar",
    "substrate_mirror",
    "heuristically_corresponding",
]

INTERPRETATION_KINDS = [
    "definitional_extension",
    "conservative_extension",
    "interpretation",
    "faithful_embedding",
    "quotient_projection",
    "substrate_mirror",
    "heuristic_translation",
    "none",
]

EXISTENCE_MODES = [
    "constructive_witness",
    "bounded_search",
    "compactness_extracted",
    "classical_noncomputable",
]

ORACLE_MODES = [
    "forbid",
    "deterministic_only",
    "candidate_generation",
    "proof_search",
    "witness_synthesis",
    "failure_diagnosis",
    "rewrite_to_packet",
    "continuation_refill",
]

FIVE_ELEMENT_MAPPING: dict[str, list[str]] = {
    "history": [
        "linear_resource_trace",
        "relevant_dependency_trace",
        "temporal_state_history",
    ],
    "observation_action": [
        "focusing_phase",
        "modal_next_obligation",
        "domain_monotone_update",
    ],
    "observation_result": [
        "realizability_witness",
        "constructive_evidence",
        "model_theoretic_interpretation_result",
    ],
    "termination_condition": [
        "normalization",
        "cut_elimination",
        "domain_fixed_point_or_stable_point",
        "decidability_classification",
    ],
    "certificate": [
        "proof_term",
        "witness_extractor",
        "axiom_budget",
        "equality_kind",
        "descent_certificate",
    ],
}

DETERMINISTIC_NON_ORACLE_WORK = [
    "definition_expansion",
    "normalization",
    "obligation_split",
    "schema_validation",
    "dependency_trace_extraction",
    "label_dedup",
    "manifest_parse",
    "status_classification",
]


def compact_principle_lines() -> list[str]:
    return [f"- {item['name']}: {item['gate']}" for item in PRINCIPLES]


def render_prompt_block(*, context: str) -> str:
    """Return a compact prompt block suitable for oracle/refill/writeback."""
    lines = [
        "## Logic-minimization discipline",
        "",
        f"Discipline version: {LOGIC_DISCIPLINE_VERSION}",
        "",
        "Apply these as project rules, not as historical commentary:",
        *compact_principle_lines(),
        "",
        (
            "For every candidate theorem or bridge, prefer the smallest "
            "statement that exposes:"
        ),
        "- axiom_budget / strength_level",
        "- cut_rank / elimination_plan when a bridge or intermediate carrier appears",
        "- witness_extractor / existence_mode for existence claims",
        (
            "- equality_kind / interpretation_kind for equality, "
            "correspondence, bridge, or mirror claims"
        ),
        (
            "- resource_trace / dependency_trace for copied history, "
            "observation, oracle output, or certificate"
        ),
        (
            "- focusing_phase / oracle_mode, with deterministic invertible "
            "work kept outside the oracle"
        ),
        "",
        "BEDC five-element compression:",
    ]
    for key, values in FIVE_ELEMENT_MAPPING.items():
        lines.append(f"- {key}: {', '.join(values)}")
    lines.extend([
        "",
        "Oracle boundary:",
        (
            "Oracle output is candidate material, never a certificate.  Do "
            "not ask the oracle to do deterministic work such as "
            + ", ".join(DETERMINISTIC_NON_ORACLE_WORK)
            + "."
        ),
        "",
        f"Context: {context}",
    ])
    return "\n".join(lines)


def bridge_payload(
    *, readiness: str = "", oracle_mode: str = "candidate_generation"
) -> dict[str, Any]:
    return {
        "version": LOGIC_DISCIPLINE_VERSION,
        "principles": [item["id"] for item in PRINCIPLES],
        "five_element_mapping": FIVE_ELEMENT_MAPPING,
        "strength_levels": STRENGTH_LEVELS,
        "equality_kinds": EQUALITY_KINDS,
        "interpretation_kinds": INTERPRETATION_KINDS,
        "existence_modes": EXISTENCE_MODES,
        "oracle_modes": ORACLE_MODES,
        "oracle_mode": oracle_mode,
        "readiness": readiness,
        "deterministic_non_oracle_work": DETERMINISTIC_NON_ORACLE_WORK,
        "required_packet_fields": [
            "axiom_budget",
            "strength_level",
            "cut_rank",
            "elimination_plan",
            "witness_extractor",
            "existence_mode",
            "equality_kind",
            "interpretation_kind",
            "resource_trace",
            "dependency_trace",
            "focusing_phase",
            "oracle_mode",
        ],
    }


def gate_warnings(record: dict[str, Any]) -> list[str]:
    warnings: list[str] = []
    synthesis = (
        record.get("synthesis") if isinstance(record.get("synthesis"), dict) else {}
    )
    discipline = (
        synthesis.get("logic_discipline")
        if isinstance(synthesis.get("logic_discipline"), dict)
        else {}
    )
    if not discipline:
        warnings.append("logic discipline metadata is absent; treat bridge output as candidate-only")
        return warnings
    if discipline.get("version") != LOGIC_DISCIPLINE_VERSION:
        warnings.append("logic discipline version differs from local gate expectations")
    if discipline.get("oracle_mode") == "deterministic_only":
        warnings.append(
            "deterministic-only bridge work should not be routed through "
            "oracle generation"
        )
    return warnings

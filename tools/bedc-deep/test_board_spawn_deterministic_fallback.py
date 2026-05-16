#!/usr/bin/env python3
"""Regression checks for BOARD deterministic fallback intake."""

from __future__ import annotations

import board_spawn


SAFE_FILE = "papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex"


def _candidate(**overrides):
    base = {
        "title": "Polynomial finite witness boundary",
        "claim": (
            "The displayed polynomial carrier row gives a finite local witness "
            "for the existing NameCert ledger implication."
        ),
        "source": "plain_math_review",
        "local_inputs": [SAFE_FILE],
        "fit_score": 8,
        "novelty": 7,
        "landing_kind": "existing_chapter_lemma",
        "tastegate_mode": "existing_chapter",
        "axiom_budget": "B0_finite_witness",
        "strength_level": "B0_finite_witness",
        "budget_reason": "The packet consumes only finite displayed rows in the existing local chapter.",
        "existence_mode": "none",
        "witness_extractor": "",
        "cut_rank": "0",
        "elimination_plan": "No bridge carrier is introduced; the statement remains an existing-chapter local implication.",
        "equality_kind": "none",
        "interpretation_kind": "none",
        "resource_trace": "Consumes only the named local BEDC rows.",
        "dependency_trace": "Depends only on displayed labels in local_inputs.",
        "rate_modulus_surface": "",
        "oracle_mode": "candidate_generation",
    }
    base.update(overrides)
    return base


def test_deterministic_fallback_accepts_local_logic_packet() -> None:
    accepted, rejected = board_spawn._deterministic_fallback_judge(
        [_candidate()],
        fit_threshold=7,
        novelty_threshold=6,
    )
    assert len(accepted) == 1, (accepted, rejected)
    assert rejected == [], rejected
    assert "Deterministic BOARD fallback admitted" in accepted[0]["rationale"]


def test_deterministic_fallback_rejects_external_signal() -> None:
    accepted, rejected = board_spawn._deterministic_fallback_judge(
        [_candidate(claim="Automath source_path proposes an external theorem signal.")],
        fit_threshold=7,
        novelty_threshold=6,
    )
    assert accepted == [], accepted
    assert rejected[0]["reason"] == "deterministic_fallback_external_signal_requires_llm_judge"


def test_deterministic_fallback_rejects_new_chapter() -> None:
    accepted, rejected = board_spawn._deterministic_fallback_judge(
        [_candidate(landing_kind="new_chapter")],
        fit_threshold=7,
        novelty_threshold=6,
    )
    assert accepted == [], accepted
    assert rejected[0]["reason"].startswith("deterministic_fallback_landing_requires_llm_judge")


def test_deterministic_fallback_rejects_unknown_source() -> None:
    accepted, rejected = board_spawn._deterministic_fallback_judge(
        [_candidate(source="research_lane:paper_gap_scanner")],
        fit_threshold=7,
        novelty_threshold=6,
    )
    assert accepted == [], accepted
    assert rejected[0]["reason"].startswith("deterministic_fallback_source_requires_llm_judge")


def test_deterministic_fallback_rejects_anti_parameter_echo() -> None:
    accepted, rejected = board_spawn._deterministic_fallback_judge(
        [
            _candidate(
                title="ObserverTraceSeal local obligation row projection",
                claim=(
                    "The displayed NameCert obligation surface merely restates "
                    "that its own displayed rows are recorded."
                ),
            )
        ],
        fit_threshold=7,
        novelty_threshold=6,
    )
    assert accepted == [], accepted
    assert rejected[0]["reason"] == "deterministic_fallback_anti_parameter_echo"


def test_deterministic_fallback_allows_low_score_local_packet() -> None:
    accepted, rejected = board_spawn._deterministic_fallback_judge(
        [_candidate(fit_score=0, novelty=0)],
        fit_threshold=7,
        novelty_threshold=6,
    )
    assert len(accepted) == 1, (accepted, rejected)
    assert rejected == [], rejected


if __name__ == "__main__":
    test_deterministic_fallback_accepts_local_logic_packet()
    test_deterministic_fallback_rejects_external_signal()
    test_deterministic_fallback_rejects_new_chapter()
    test_deterministic_fallback_rejects_unknown_source()
    test_deterministic_fallback_rejects_anti_parameter_echo()
    test_deterministic_fallback_allows_low_score_local_packet()
    print("test_board_spawn_deterministic_fallback: ok")

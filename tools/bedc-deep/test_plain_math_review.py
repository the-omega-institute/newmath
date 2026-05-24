#!/usr/bin/env python3
"""Regression checks for BEDC plain-reading candidate review."""

from __future__ import annotations

from pathlib import Path

import plain_math_review


SAFE_FILE = "papers/bedc/parts/concrete_instances/25_polynomial_namecert_construction.tex"
ALT_SAFE_FILE = "papers/bedc/parts/concrete_instances/25_polynomial_literal_addtrim_algebra.tex"
VISION_FILE = "papers/bedc/parts/visions/hyperbolic_phase_geometry_of_observer_expansion.tex"


def _files() -> dict:
    return {
        SAFE_FILE: {"file": SAFE_FILE, "line_count": 120, "hub_like": False},
        ALT_SAFE_FILE: {"file": ALT_SAFE_FILE, "line_count": 160, "hub_like": False},
    }


def test_external_bridge_is_metadata_only_and_split() -> None:
    record = {
        "title": "Automath continuation polynomial transport",
        "claim": (
            "Automath source_path proposes an external theorem signal for a bridge "
            "continuation target, but BEDC must rederive a local route."
        ),
        "local_inputs": [SAFE_FILE],
        "reason": "external_signal_missing_chapter_worthiness",
    }
    review = plain_math_review.review_record("candidate_inbox", record, _files())
    assert review["decision"] == "split", review
    assert "external_signal_metadata_only" in review["risk_flags"], review
    assert "local_rederivation_from_bedc_rows" in review["missing_support"], review
    assert review["target_file"] == SAFE_FILE, review
    assert all(
        not str(candidate.get("local_inputs")).lower().find("automath") >= 0
        for candidate in review["split_candidates"]
    )


def test_vision_is_inspiration_only_and_not_direct_board_landing() -> None:
    record = {
        "title": "Hyperbolic Phase Geometry of Observer Expansion",
        "claim": (
            "A broad vision says observer expansion can be read by hyperbolic "
            "phase geometry and a boundary readout."
        ),
        "local_inputs": [VISION_FILE],
        "reason": f"inspiration_only_not_board_landing:{VISION_FILE}",
    }
    review = plain_math_review.review_record("vision", record, _files())
    assert review["decision"] in {"split", "hold"}, review
    assert "vision_inspiration_only" in review["risk_flags"], review
    assert review["minimal_landing_kind"] != "new_chapter", review
    assert VISION_FILE not in [
        input_path
        for candidate in review["split_candidates"]
        for input_path in candidate.get("local_inputs", [])
    ]


def test_missing_landing_holds_not_final_rejects() -> None:
    review = plain_math_review.review_record(
        "candidate_inbox",
        {
            "title": "Witness boundary without local input",
            "claim": "There exists a finite witness extractor but no BEDC target has been selected.",
            "local_inputs": [],
            "reason": "missing_local_inputs",
        },
        {},
    )
    assert review["decision"] == "hold", review
    assert "bedc_native_landing" in review["missing_support"], review
    assert not review["split_candidates"], review


def test_keep_candidate_gets_logic_packet_surface() -> None:
    review = plain_math_review.review_record(
        "research_candidate",
        {
            "title": "Polynomial local row boundary",
            "claim": (
                "The displayed polynomial carrier row implies the local NameCert "
                "ledger row by a finite existing-chapter implication."
            ),
            "local_inputs": [SAFE_FILE],
        },
        _files(),
    )
    assert review["decision"] == "keep", review
    assert review["target_file"] == SAFE_FILE, review
    assert review["split_candidates"], review
    candidate = review["split_candidates"][0]
    for key in (
        "axiom_budget",
        "strength_level",
        "budget_reason",
        "cut_rank",
        "elimination_plan",
        "equality_kind",
        "interpretation_kind",
        "resource_trace",
        "dependency_trace",
        "oracle_mode",
    ):
        assert key in candidate, key


def test_review_supply_only_emits_local_candidates() -> None:
    review = plain_math_review.review_record(
        "candidate_inbox",
        {
            "title": "Local equality kind split",
            "claim": "The two displayed rows are equivalent only after declaring the equality kind.",
            "local_inputs": [SAFE_FILE],
            "reason": "logic_packet_gate:equality_missing_equality_kind",
        },
        _files(),
    )
    assert review["decision"] == "split", review
    candidates = review["split_candidates"]
    assert candidates
    assert all(candidate.get("local_inputs") == [SAFE_FILE] for candidate in candidates)
    assert any(candidate.get("equality_kind") == "equivalent" for candidate in candidates)


def test_near_line_cap_landing_is_rerouted() -> None:
    files = {
        SAFE_FILE: {"file": SAFE_FILE, "line_count": 790, "hub_like": False},
        ALT_SAFE_FILE: {"file": ALT_SAFE_FILE, "line_count": 120, "hub_like": False},
    }
    review = plain_math_review.review_record(
        "candidate_inbox",
        {
            "title": "Polynomial addtrim equality boundary",
            "claim": "The polynomial addtrim rows are equivalent after declaring the equality kind.",
            "local_inputs": [SAFE_FILE],
            "reason": f"predicted_line_cap_overflow:{SAFE_FILE}:860",
        },
        files,
    )
    assert review["target_file"] == ALT_SAFE_FILE, review
    assert all(candidate.get("local_inputs") == [ALT_SAFE_FILE] for candidate in review["split_candidates"])


def test_research_lane_imports_plain_review_source() -> None:
    text = Path(__file__).with_name("research_candidate_lane.py").read_text(encoding="utf-8")
    assert "import plain_math_review" in text
    assert "plain_math_review.candidate_supply_from_reviews" in text


if __name__ == "__main__":
    test_external_bridge_is_metadata_only_and_split()
    test_vision_is_inspiration_only_and_not_direct_board_landing()
    test_missing_landing_holds_not_final_rejects()
    test_keep_candidate_gets_logic_packet_surface()
    test_review_supply_only_emits_local_candidates()
    test_near_line_cap_landing_is_rerouted()
    test_research_lane_imports_plain_review_source()
    print("test_plain_math_review: ok")

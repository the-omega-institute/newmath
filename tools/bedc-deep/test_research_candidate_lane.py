#!/usr/bin/env python3
"""Regression checks for BEDC research candidate refinement."""

from __future__ import annotations

import research_candidate_lane
import burden_candidate_miner


BIG_FILE = "papers/bedc/parts/concrete_instances/08_option_namecert_construction.tex"
SMALL_FILE = "papers/bedc/parts/concrete_instances/option/08_option_namecert_construction_core.tex"


def test_near_line_cap_candidate_reroutes_to_smaller_landing() -> None:
    files = {
        BIG_FILE: {"file": BIG_FILE, "line_count": 806, "hub_like": False},
        SMALL_FILE: {"file": SMALL_FILE, "line_count": 120, "hub_like": False},
    }
    candidate = {
        "title": "Option equality kind boundary",
        "claim": (
            "The option classifier rows are equivalent only after declaring the "
            "equality kind and the visible interpretation boundary."
        ),
        "local_inputs": [BIG_FILE],
        "fit_score": 8,
        "novelty": 7,
        "landing_kind": "existing_chapter_lemma",
        "tastegate_mode": "existing_chapter",
    }
    packet = research_candidate_lane._packet(
        candidate,
        source="research_lane:test",
        files=files,
    )
    assert packet["status"] == "ready", packet
    assert packet["candidate"]["local_inputs"] == [SMALL_FILE], packet


def test_low_score_candidate_is_warning_not_blocked() -> None:
    files = {
        SMALL_FILE: {"file": SMALL_FILE, "line_count": 120, "hub_like": False},
    }
    candidate = {
        "title": "Option low score local boundary",
        "claim": (
            "The displayed option classifier row gives a finite local boundary "
            "for a BEDC-native existing-chapter obligation."
        ),
        "local_inputs": [SMALL_FILE],
        "fit_score": 0,
        "novelty": 0,
        "landing_kind": "existing_chapter_obligation",
        "tastegate_mode": "existing_chapter",
    }
    packet = research_candidate_lane._packet(
        candidate,
        source="research_lane:test",
        files=files,
    )
    assert packet["status"] == "ready", packet
    assert "below_fit_threshold:0" in packet["warnings"], packet
    assert "below_novelty_threshold:0" in packet["warnings"], packet
    assert not any("below_" in reason for reason in packet["reasons"]), packet


def test_structural_row_echo_is_not_ready() -> None:
    files = {
        SMALL_FILE: {"file": SMALL_FILE, "line_count": 120, "hub_like": False},
    }
    candidate = {
        "source": "research_lane:structural_relation_miner",
        "title": "Option forgetful projection boundary",
        "claim": (
            "Option should expose a BEDC-native forgetful projection lemma "
            "over the displayed rows. Local evidence is the listed chapter's "
            "displayed rows; the receiving gate must re-read those rows rather "
            "than trust a copied source excerpt."
        ),
        "local_inputs": [SMALL_FILE],
        "fit_score": 8,
        "novelty": 7,
        "landing_kind": "existing_chapter_lemma",
        "tastegate_mode": "existing_chapter",
    }
    packet = research_candidate_lane._packet(
        candidate,
        source="research_lane:structural_relation_miner",
        files=files,
    )
    assert packet["status"] == "blocked", packet
    assert "substance_echo_not_board_ready" in packet["reasons"], packet


def test_line_cap_overflow_is_not_recovered_from_inbox() -> None:
    rec = {
        "event": "held_for_refinement",
        "source": "research_lane:structural_relation_miner",
        "title": "Option line cap overflow boundary",
        "claim": (
            "The displayed option rows would need a split before any new "
            "existing-chapter theorem could be appended safely."
        ),
        "local_inputs": [BIG_FILE],
        "reason": f"predicted_line_cap_overflow:{BIG_FILE}:860",
    }
    assert not research_candidate_lane._soft_recoverable_reject(rec)


def test_burden_candidate_is_ready_and_appendable() -> None:
    files = {
        SMALL_FILE: {"file": SMALL_FILE, "line_count": 120, "hub_like": False},
    }
    candidate = {
        "title": "Option strict obstruction corollary",
        "claim": (
            "Using \\autoref{thm:option-refusal-frontier} and \\autoref{def:option-carrier}, "
            "prove a strict local obstruction lemma for Option: the displayed "
            "failure row blocks only the named converse route and cannot be "
            "read as a global impossibility or hidden host theorem."
        ),
        "local_inputs": [SMALL_FILE],
        "source": burden_candidate_miner.SOURCE,
        "fit_score": 9,
        "novelty": 8,
        "landing_kind": "existing_chapter_lemma",
        "tastegate_mode": "existing_chapter",
        "axiom_budget": "B0_finite_witness",
        "strength_level": "B0_finite_witness",
        "budget_reason": "The target is a finite local implication over already displayed BEDC rows.",
        "existence_mode": "none",
        "witness_extractor": "",
        "cut_rank": "1",
        "elimination_plan": (
            "List the displayed route rows cited by thm:option-refusal-frontier and "
            "reject unlisted coordinates."
        ),
        "equality_kind": "none",
        "interpretation_kind": "interpretation",
        "resource_trace": "Primary support is thm:option-refusal-frontier in the selected file.",
        "dependency_trace": "Depends on the selected body file and its cited BEDC labels only.",
        "rate_modulus_surface": "",
        "oracle_mode": "proof_search",
    }
    packet = research_candidate_lane._packet(
        candidate,
        source=burden_candidate_miner.SOURCE,
        files=files,
    )
    assert packet["status"] == "ready", packet


def test_burden_miner_skips_exactness_carrier_echo() -> None:
    rel = SMALL_FILE
    index = {
        "files": [
            {
                "file": rel,
                "line_count": 80,
                "hub_like": False,
                "closurestatus_count": 0,
                "theorem_like_labels": [
                    {
                        "env": "theorem",
                        "label": "thm:example-cont-hom-exactness",
                        "title": "Example Cont hom exactness",
                    },
                    {
                        "env": "definition",
                        "label": "def:example-namecert-carrier",
                        "title": "Example NameCert carrier",
                    },
                ],
            }
        ]
    }
    assert burden_candidate_miner.candidates_from_index(index, existing_titles=set()) == []


def test_burden_miner_does_not_turn_plain_boundary_into_obstruction() -> None:
    rel = SMALL_FILE
    index = {
        "files": [
            {
                "file": rel,
                "line_count": 120,
                "hub_like": False,
                "closurestatus_count": 0,
                "theorem_like_labels": [
                    {
                        "env": "theorem",
                        "label": "thm:option-route-boundary",
                        "title": "Option route boundary",
                    },
                    {
                        "env": "theorem",
                        "label": "thm:option-route-handoff",
                        "title": "Option route handoff",
                    },
                ],
            }
        ]
    }
    candidates = burden_candidate_miner.candidates_from_index(index, existing_titles=set())
    assert candidates, candidates
    assert all(c["selection_rank"] != "strict_obstruction" for c in candidates), candidates


if __name__ == "__main__":
    test_near_line_cap_candidate_reroutes_to_smaller_landing()
    test_low_score_candidate_is_warning_not_blocked()
    test_structural_row_echo_is_not_ready()
    test_line_cap_overflow_is_not_recovered_from_inbox()
    test_burden_candidate_is_ready_and_appendable()
    test_burden_miner_skips_exactness_carrier_echo()
    test_burden_miner_does_not_turn_plain_boundary_into_obstruction()
    print("test_research_candidate_lane: ok")

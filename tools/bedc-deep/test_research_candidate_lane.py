#!/usr/bin/env python3
"""Regression checks for BEDC research candidate refinement."""

from __future__ import annotations

import research_candidate_lane


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


if __name__ == "__main__":
    test_near_line_cap_candidate_reroutes_to_smaller_landing()
    test_low_score_candidate_is_warning_not_blocked()
    print("test_research_candidate_lane: ok")

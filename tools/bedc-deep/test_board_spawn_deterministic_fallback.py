#!/usr/bin/env python3
"""Regression checks for BOARD deterministic fallback intake."""

from __future__ import annotations

from pathlib import Path

import board_spawn
import candidate_substance
from dispatch_bedc_target import BedcTarget


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


def test_deterministic_fallback_accepts_research_lane_gap_scanner() -> None:
    accepted, rejected = board_spawn._deterministic_fallback_judge(
        [_candidate(source="research_lane:paper_gap_scanner")],
        fit_threshold=7,
        novelty_threshold=6,
    )
    assert len(accepted) == 1, (accepted, rejected)
    assert rejected == [], rejected


def test_deterministic_fallback_accepts_burden_miner() -> None:
    accepted, rejected = board_spawn._deterministic_fallback_judge(
        [
            _candidate(
                source="research_lane:burden_candidate_miner",
                title="Polynomial strict obstruction corollary",
                claim=(
                    "Using \\autoref{thm:polynomial-refusal-frontier}, prove a "
                    "strict local obstruction lemma for Polynomial: the "
                    "displayed failure row blocks only the named converse "
                    "route and cannot be read as a global impossibility."
                ),
                resource_trace="Primary support is thm:polynomial-refusal-frontier.",
                oracle_mode="proof_search",
            )
        ],
        fit_threshold=7,
        novelty_threshold=6,
    )
    assert len(accepted) == 1, (accepted, rejected)
    assert rejected == [], rejected


def test_deterministic_fallback_rejects_strict_obstruction_without_negative_evidence() -> None:
    accepted, rejected = board_spawn._deterministic_fallback_judge(
        [
            _candidate(
                source="research_lane:burden_candidate_miner",
                title="Polynomial strict obstruction corollary",
                claim=(
                    "Using \\autoref{thm:polynomial-boundary}, prove a "
                    "strict local obstruction lemma for Polynomial: the "
                    "displayed failure row blocks only the named converse "
                    "route and cannot be read as a global impossibility."
                ),
                resource_trace="Primary support is thm:polynomial-boundary.",
                oracle_mode="proof_search",
            )
        ],
        fit_threshold=7,
        novelty_threshold=6,
    )
    assert accepted == [], accepted
    assert rejected[0]["reason"] == "strict_obstruction_requires_negative_evidence"


def test_deterministic_fallback_rejects_raw_gap_scanner_source() -> None:
    accepted, rejected = board_spawn._deterministic_fallback_judge(
        [_candidate(source="paper_gap_scanner")],
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


def test_board_substance_gate_rejects_structural_row_echo() -> None:
    reason = board_spawn._substance_rejection(
        _candidate(
            source="research_lane:structural_relation_miner",
            title="ObservationReflectionPacket forgetful projection boundary",
            claim=(
                "ObservationReflectionPacket should expose a BEDC-native "
                "forgetful projection lemma over the displayed rows; local "
                "evidence is the listed chapter's displayed rows and the "
                "receiving gate must re-read those rows rather than trust a "
                "copied source excerpt."
            ),
            budget_reason=(
                "The candidate is a finite structural relation over displayed "
                "local rows."
            ),
            resource_trace=(
                "Consumes only the listed chapter's displayed carrier rows."
            ),
        )
    )
    assert reason == "substance_echo_not_board_ready"


def test_candidate_inbox_rejects_structural_row_echo_before_judge() -> None:
    candidate = _candidate(
        source="research_lane:structural_relation_miner",
        title="SyntheticSubstanceProbe forgetful projection boundary",
        claim=(
            "SyntheticSubstanceProbe should expose a BEDC-native "
            "forgetful projection lemma over the displayed rows; local "
            "evidence is the listed chapter's displayed rows and the "
            "receiving gate must re-read those rows rather than trust a "
            "copied source excerpt."
        ),
        budget_reason=(
            "The candidate is a finite structural relation over displayed "
            "local rows."
        ),
        resource_trace=(
            "Consumes only the listed chapter's displayed carrier rows."
        ),
    )
    screen = board_spawn.candidate_inbox.screen_candidates(
        [candidate],
        source="codex",
        fit_threshold=7,
        novelty_threshold=6,
    )
    assert screen.accepted == [], screen
    assert [item.get("reason") for item in screen.rejected] == [
        "substance_echo_not_board_ready"
    ], screen


def test_candidate_inbox_rejects_verification_axis_surface_before_judge() -> None:
    candidate = _candidate(
        source="research_lane:burden_candidate_miner",
        title="Polynomial finite witness Lean target regression surface",
        claim=(
            "Using \\autoref{thm:polynomial-finite-witness-lean-target-regression}, "
            "prove downstream coverage for the Lean target single_carrier_alignment surface."
        ),
        resource_trace="Primary support is a BEDC.Derived closed-term substitution target.",
        oracle_mode="proof_search",
    )
    screen = board_spawn.candidate_inbox.screen_candidates(
        [candidate],
        source="codex",
        fit_threshold=7,
        novelty_threshold=6,
    )
    assert screen.accepted == [], screen
    assert [item.get("reason") for item in screen.rejected] == [
        "forbidden_axis_or_marker_candidate"
    ], screen


def test_legacy_board_surface_target_is_not_executable() -> None:
    target = BedcTarget(
        target_id="B-test",
        title="ObservationReflectionPacket forgetful projection boundary",
        fields={"Source": "bedc-deep board_spawn (codex)"},
        body=(
            "Problem:\n"
            "If an accepted packet is consumed through a smaller public "
            "surface, then the projection must retain only rows already "
            "displayed in the packet.\n\n"
            "Logic packet discipline:\n"
            "- `budget_reason`: The candidate is a finite structural relation "
            "over displayed local rows. It asks for projection, renaming, "
            "interpretation, or route elimination, not a new object or "
            "external theorem import.\n"
            "- `resource_trace`: Consumes only the listed chapter's displayed "
            "carrier, classifier, ledger, route, and NameCert rows.\n"
        ),
    )
    reason = candidate_substance.board_target_rejection(target)
    assert candidate_substance.is_substance_rejection(reason), reason


def test_legacy_board_surface_template_without_burden_is_not_executable() -> None:
    target = BedcTarget(
        target_id="B-test",
        title="ObservationReflectionPacket classifier alignment boundary",
        fields={"Source": "bedc-deep board_spawn (codex)"},
        body=(
            "Problem:\n"
            "If two accepted packet carriers are compared by the local "
            "classifier, then the comparison must transport exactly the "
            "listed packet rows.\n\n"
            "Logic packet discipline:\n"
            "- `elimination_plan`: No new bridge carrier is introduced; "
            "the relation is tested by projection, renaming, or "
            "interpretation of rows already visible in the listed chapter.\n"
        ),
    )
    assert candidate_substance.board_target_rejection(target) == "weak_surface_target"


def test_board_surface_target_with_real_burden_remains_executable() -> None:
    target = BedcTarget(
        target_id="B-test",
        title="PhysicalModelAudit equivalence completion boundary",
        fields={"Source": "bedc-deep board_spawn (codex)"},
        body=(
            "Problem:\n"
            "If a forward audit classifier is consumed as an equivalence, "
            "then the reverse direction must give a counterexample or a "
            "canonical witness for the displayed audit rows.\n\n"
            "Logic packet discipline:\n"
            "- `budget_reason`: The candidate is a finite structural relation "
            "over displayed local rows. It asks for projection, renaming, "
            "interpretation, or route elimination, not a new object or "
            "external theorem import.\n"
        ),
    )
    assert candidate_substance.board_target_rejection(target) == ""


def test_direct_codex_admission_accepts_research_packet_without_judge() -> None:
    accepted, stopped, needs_judge = board_spawn._direct_codex_admission(
        [_candidate(source="research_lane:paper_gap_scanner")]
    )
    assert len(accepted) == 1, (accepted, stopped, needs_judge)
    assert stopped == [], stopped
    assert needs_judge == [], needs_judge
    assert "Local BOARD admission" in accepted[0]["rationale"]


def test_direct_codex_admission_accepts_burden_miner_without_judge() -> None:
    accepted, stopped, needs_judge = board_spawn._direct_codex_admission(
        [
            _candidate(
                source="research_lane:burden_candidate_miner",
                title="Polynomial determinacy corollary",
                claim=(
                    "Using \\autoref{thm:polynomial-exactness}, prove a "
                    "determinacy corollary for Polynomial: once the cited "
                    "local rows are fixed, accepted consumers pick the same "
                    "finite exactness decision."
                ),
                oracle_mode="proof_search",
            )
        ]
    )
    assert len(accepted) == 1, (accepted, stopped, needs_judge)
    assert stopped == [], stopped
    assert needs_judge == [], needs_judge


def test_direct_codex_admission_rejects_anti_parameter_echo() -> None:
    accepted, stopped, needs_judge = board_spawn._direct_codex_admission(
        [
            _candidate(
                source="research_lane:paper_gap_scanner",
                title="ObserverTraceSeal local obligation row projection",
                claim=(
                    "The displayed NameCert obligation surface merely restates "
                    "that its own displayed rows are recorded."
                ),
            )
        ]
    )
    assert accepted == [], accepted
    assert stopped[0]["reason"] == "direct_codex_anti_parameter_echo"
    assert needs_judge == [], needs_judge


def test_direct_codex_admission_keeps_oracle_for_judge() -> None:
    accepted, stopped, needs_judge = board_spawn._direct_codex_admission(
        [_candidate(source="oracle")]
    )
    assert accepted == [], accepted
    assert stopped == [], stopped
    assert len(needs_judge) == 1, needs_judge


def test_direct_codex_admission_keeps_structural_miner_for_judge() -> None:
    accepted, stopped, needs_judge = board_spawn._direct_codex_admission(
        [_candidate(source="research_lane:structural_relation_miner")]
    )
    assert accepted == [], accepted
    assert stopped == [], stopped
    assert len(needs_judge) == 1, needs_judge


def test_judge_accept_hydration_preserves_logic_packet_fields() -> None:
    original = _candidate(
        source="research_lane:structural_relation_miner",
        candidate_id="cand-hydrate",
    )
    compact = {
        "title": original["title"],
        "source": "codex",
        "rationale": "judge accepted compact item",
    }
    hydrated = board_spawn._hydrate_judge_items([compact], [original])
    assert len(hydrated) == 1, hydrated
    assert hydrated[0]["axiom_budget"] == original["axiom_budget"]
    assert hydrated[0]["strength_level"] == original["strength_level"]
    assert hydrated[0]["cut_rank"] == original["cut_rank"]
    assert hydrated[0]["source"] == "codex"
    assert hydrated[0]["rationale"] == "judge accepted compact item"


def test_judge_unavailable_without_fallback_is_safe_empty_result() -> None:
    text = Path(__file__).with_name("board_spawn.py").read_text(encoding="utf-8")
    start = text.index('if error_kind.startswith("board_judge_unavailable")')
    end = text.index("\n        else:", start)
    body = text[start:end]
    assert "deterministic_fallback_judge" in body
    assert "ok=True" in body
    fallback_empty = body[body.index("else:") :]
    assert "held=cheap_holds + deterministic_rejected" in fallback_empty
    assert "rejected=cheap_drops" in fallback_empty


if __name__ == "__main__":
    test_deterministic_fallback_accepts_local_logic_packet()
    test_deterministic_fallback_rejects_external_signal()
    test_deterministic_fallback_rejects_new_chapter()
    test_deterministic_fallback_accepts_research_lane_gap_scanner()
    test_deterministic_fallback_accepts_burden_miner()
    test_deterministic_fallback_rejects_strict_obstruction_without_negative_evidence()
    test_deterministic_fallback_rejects_raw_gap_scanner_source()
    test_deterministic_fallback_rejects_anti_parameter_echo()
    test_deterministic_fallback_allows_low_score_local_packet()
    test_board_substance_gate_rejects_structural_row_echo()
    test_candidate_inbox_rejects_structural_row_echo_before_judge()
    test_candidate_inbox_rejects_verification_axis_surface_before_judge()
    test_legacy_board_surface_target_is_not_executable()
    test_legacy_board_surface_template_without_burden_is_not_executable()
    test_board_surface_target_with_real_burden_remains_executable()
    test_direct_codex_admission_accepts_research_packet_without_judge()
    test_direct_codex_admission_accepts_burden_miner_without_judge()
    test_direct_codex_admission_rejects_anti_parameter_echo()
    test_direct_codex_admission_keeps_oracle_for_judge()
    test_direct_codex_admission_keeps_structural_miner_for_judge()
    test_judge_accept_hydration_preserves_logic_packet_fields()
    test_judge_unavailable_without_fallback_is_safe_empty_result()
    print("test_board_spawn_deterministic_fallback: ok")

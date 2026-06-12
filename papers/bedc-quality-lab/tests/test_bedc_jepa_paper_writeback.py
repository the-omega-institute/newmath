from bedc_quality_lab.bedc_jepa_paper_writeback import (
    NOT_CLAIMED,
    SCHEMA_ID,
    WRITEBACK_SECTIONS,
    build_paper_writeback_packet,
)


def test_paper_writeback_packet_exposes_bioreality_style_boundary():
    packet = build_paper_writeback_packet()

    assert packet["schema_id"] == SCHEMA_ID
    assert packet["writeback_status"] == "ready"
    assert packet["source_spec"]["stable_writeback_sections"] == list(WRITEBACK_SECTIONS)
    assert packet["pattern_spec"]["writeback_rule"] == (
        "write only gated claims; write all unsupported candidates as ledger or cannot-claim rows"
    )
    assert packet["classifier_spec"]["review_status"] == "review_ready"
    assert packet["classifier_spec"]["readiness_decision"] == "external_bundle_ready"
    assert packet["classifier_spec"]["claim_boundary_status"] == "executed"
    assert packet["classifier_spec"]["accepted_operational_claim"] == "door_key_context_visible"
    assert set(packet["classifier_spec"]["source_gap_predicates"]) == {
        "has_key",
        "door_open_or_unlocked",
        "goal_reachable_with_current_state",
    }


def test_paper_writeback_packet_metrics_are_gated_cells():
    packet = build_paper_writeback_packet()
    metrics = packet["metrics"]

    assert metrics["torch_objective_gap_auc_gain_mean"] > 0.20
    assert metrics["torch_objective_unlogged_error_reduction_mean"] > 0.005
    assert metrics["torch_objective_debt_reduction_mean"] > 0.05
    assert metrics["native_unlogged_error_reduction"] > 0.05
    assert metrics["native_planning_high_gap_reduction"] > 0.05
    assert metrics["seed_sweep_unlogged_error_win_rate"] >= 0.6
    assert metrics["latent_claim_singleton_claim_rate"] == 0.5
    assert metrics["latent_claim_conformal_miscoverage"] <= 0.05
    assert metrics["accepted_claim_count"] == 1.0
    assert metrics["gap_claim_count"] == 3.0


def test_paper_writeback_packet_ledger_blocks_overclaim():
    packet = build_paper_writeback_packet()
    rows = {row["residue"]: row for row in packet["ledger_rows"]}

    assert rows["source-gap-predicates"]["status"] == "open"
    assert rows["non-singleton-latent-claim-sets"]["status"] == "partial"
    assert rows["native-V-JEPA2-AC-baseline-open"]["status"] == "open"
    assert rows["mechanism-closure-debt"]["status"] == "open"
    assert packet["not_claimed"] == list(NOT_CLAIMED)
    assert "source-gap predicate promoted to latent meaning" in packet["forbidden_surfaces"]
    assert "native V-JEPA2-AC baseline claimed before native run" in packet["forbidden_surfaces"]

from bedc_quality_lab.public_minigrid_debt_closure import build_public_minigrid_debt_closure_analysis


def test_public_minigrid_debt_closure_decomposes_public_debt_or_fails_closed():
    packet = build_public_minigrid_debt_closure_analysis(train_count=16, test_count=16, planning_state_count=4, seed=31)

    assert packet["schema_id"] == "bedc-jepa-public-debt-closure-analysis"
    assert packet["status"] in {"executed", "unavailable"}
    assert packet["environment_id"] == "MiniGrid-DoorKey-8x8-v0"

    if packet["status"] == "unavailable":
        assert packet["debt_decomposition"] == {}
        return

    contract = packet["analysis_contract"]
    assert contract["run_command"] == "python scripts/build_public_minigrid_debt_closure.py"
    assert contract["environment_id"] == "MiniGrid-DoorKey-8x8-v0"
    assert contract["seed"] == 31.0
    assert contract["debt_component_weights"] == {
        "silent_debt": 0.40,
        "false_claim_debt": 0.30,
        "ranking_debt": 0.20,
        "coverage_debt": 0.10,
    }
    assert contract["systems"]["S3"] == "public-minigrid-trained-bedc-jepa-readout"
    assert "public MiniGrid debt and planning accounting" in contract["claim_boundary"]
    assert "no_certified_plan" in contract["risk_constrained_planning_rule"]
    assert set(packet["debt_decomposition"]) == {"S0", "S1", "S2", "S3"}
    s3 = packet["debt_decomposition"]["S3"]
    assert 0.0 <= s3["silent_debt"] <= 1.0
    assert 0.0 <= s3["coverage_debt"] <= 1.0
    assert 0.0 <= s3["gap_brier"] <= 1.0
    assert abs(
        s3["weighted_component_sum"]
        - (
            s3["silent_debt"]
            + s3["false_claim_debt"]
            + s3["ranking_debt"]
            + s3["coverage_debt"]
        )
    ) < 1e-12
    assert packet["interpretation"]["diagnosis"]


def test_public_minigrid_debt_closure_records_threshold_and_risk_curves():
    packet = build_public_minigrid_debt_closure_analysis(train_count=16, test_count=16, planning_state_count=4, seed=37)

    if packet["status"] == "unavailable":
        assert packet["risk_constrained_planning"] == {}
        return

    curve = packet["certified_coverage_curve"]["systems"]["S3"]
    assert packet["analysis_contract"]["gap_thresholds"] == packet["certified_coverage_curve"]["gap_thresholds"]
    assert len(curve["rows"]) == len(packet["certified_coverage_curve"]["gap_thresholds"])
    assert 0.0 <= curve["best_debt_score"] <= 1.0
    assert 0.0 <= curve["best_certified_coverage"] <= 1.0

    planning = packet["risk_constrained_planning"]["rows"]
    assert packet["analysis_contract"]["risk_budgets"] == packet["risk_constrained_planning"]["risk_budgets"]
    assert len(planning) == len(packet["risk_constrained_planning"]["risk_budgets"])
    for row in planning:
        assert row["decision_status"] in {"selected_plan", "no_certified_plan"}
        assert 0.0 <= row["no_certified_plan_rate"] <= 1.0
        assert 0.0 <= row["effective_success_rate"] <= 1.0
        assert 0.0 <= row["high_gap_state_rate"] <= 1.0
        if row["decision_status"] == "no_certified_plan":
            assert row["selected_plan_count"] == 0.0
            assert row["no_certified_plan_rate"] == 1.0


def test_public_minigrid_pack_records_conformal_claim_and_predicate_surfaces():
    packet = build_public_minigrid_debt_closure_analysis(train_count=24, test_count=24, planning_state_count=4, seed=41)

    if packet["status"] == "unavailable":
        assert packet["conformal_certified_coverage"] == {}
        return

    conformal = packet["conformal_certified_coverage"]
    assert packet["analysis_contract"]["conformal_alphas"] == conformal["alphas"]
    assert packet["analysis_contract"]["predicate_surfaces"] == [
        "door_key_context_visible",
        "has_key",
        "door_open_or_unlocked",
        "goal_reachable_with_current_state",
        "unsafe_transition",
    ]
    assert conformal["alphas"] == [0.2, 0.1, 0.05, 0.02, 0.01]
    assert set(conformal["predicates"]) == {
        "door_key_context_visible",
        "has_key",
        "door_open_or_unlocked",
        "goal_reachable_with_current_state",
        "unsafe_transition",
    }
    for predicate, surface in conformal["predicates"].items():
        assert surface["source_status"] in {"closed", "source_gap"}
        assert len(surface["rows"]) == len(conformal["alphas"])
        for row in surface["rows"]:
            assert 0.0 <= row["certified_coverage"] <= 1.0
            assert 0.0 <= row["unlogged_error_rate"] <= 1.0
            assert 0.0 <= row["debt_score"] <= 1.0


def test_public_minigrid_pack_records_risk_success_pareto_and_loss_ablation():
    packet = build_public_minigrid_debt_closure_analysis(train_count=24, test_count=24, planning_state_count=6, seed=43)

    if packet["status"] == "unavailable":
        assert packet["loss_ablation"] == {}
        return

    pareto = packet["risk_success_pareto"]
    assert pareto["baseline"]["risk_budget"] == 1.0
    assert "risk_improvement requires lower high-gap rate" in pareto["claim_rule"]
    assert 0.0 <= pareto["best_low_gap"]["high_gap_state_rate"] <= 1.0
    assert 0.0 <= pareto["best_success_under_half_risk"]["effective_success_rate"] <= 1.0
    assert len(pareto["frontier_rows"]) == len(packet["risk_constrained_planning"]["rows"])
    for row in pareto["frontier_rows"]:
        assert row["claim_status"] in {
            "risk_improvement",
            "risk_success_tradeoff",
            "no_certified_plan_under_budget",
            "no_risk_improvement",
        }
        assert "baseline_minus_high_gap_rate" in row
        assert "success_delta_vs_baseline" in row
        assert "no_certified_plan_delta_vs_baseline" in row

    ablation = packet["loss_ablation"]
    assert set(ablation["systems"]) == {
        "full_s3",
        "minus_unlogged_penalty",
        "minus_gap_bce",
        "posthoc_conformal_only",
        "frozen_encoder_gap_calibration_only",
    }
    assert ablation["systems"]["full_s3"]["unlogged_error_rate"] <= ablation["systems"]["minus_gap_bce"]["unlogged_error_rate"]
    assert ablation["mechanism_readout"]["unlogged_penalty_effect"] >= 0.0

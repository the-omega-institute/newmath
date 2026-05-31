from scripts.run_bedc_jepa_experiment import run_experiment

_SUMMARY = None


def _summary():
    global _SUMMARY
    if _SUMMARY is None:
        _SUMMARY = run_experiment()
    return _SUMMARY


def test_bedc_jepa_experiment_compares_four_systems():
    summary = _summary()
    assert set(summary["systems"]) == {"S0", "S1", "S2", "S3"}

    s0 = summary["systems"]["S0"]
    s1 = summary["systems"]["S1"]
    s2 = summary["systems"]["S2"]
    s3 = summary["systems"]["S3"]

    assert s0["system_name"] == "latent-jepa-style"
    assert s1["system_name"] == "posthoc-probe"
    assert s2["system_name"] == "posthoc-bedc-report"
    assert s3["system_name"] == "trained-bedc-jepa"

    assert s3["linear_identifiability_r2"] >= s1["linear_identifiability_r2"] - 0.03
    assert s3["distinction_accuracy_outside_gap"] >= s1["distinction_accuracy_outside_gap"]
    assert s3["gap_detection_auc"] > s2["gap_detection_auc"]
    assert s3["unlogged_error_rate"] < s2["unlogged_error_rate"]
    assert s3["false_claim_rate_inside_gap"] <= s2["false_claim_rate_inside_gap"]
    assert s3["bedc_debt_score"] < s2["bedc_debt_score"]


def test_bedc_jepa_experiment_reports_gap_aware_planning_gain():
    summary = _summary()
    planning = summary["planning"]

    assert planning["vanilla"]["trajectory_count"] == planning["gap_aware"]["trajectory_count"]
    assert planning["gap_aware"]["unsafe_state_rate"] < planning["vanilla"]["unsafe_state_rate"]
    assert planning["gap_aware"]["high_gap_state_rate"] < planning["vanilla"]["high_gap_state_rate"]
    assert planning["gap_aware"]["success_rate"] >= planning["vanilla"]["success_rate"] - 0.10
    assert planning["gap_aware"]["objective_gap_penalty"] > 0.0


def test_bedc_jepa_experiment_runs_seed_sweep_with_second_world():
    summary = _summary()
    sweep = summary["seed_sweep"]

    assert set(sweep["worlds"]) == {"radial-boundary", "sinusoidal-boundary"}
    for world_name, world in sweep["worlds"].items():
        assert world["seed_count"] >= 8
        assert world["s3_minus_s2_gap_auc_mean"] > 0.0
        assert world["s2_minus_s3_unlogged_error_mean"] > 0.0
        assert world["s2_minus_s3_debt_mean"] > 0.0

    aggregate = sweep["aggregate"]
    assert aggregate["world_count"] == 2
    assert aggregate["seed_count"] >= 16
    assert aggregate["s3_minus_s2_gap_auc_mean"] > 0.0
    assert aggregate["s2_minus_s3_unlogged_error_mean"] > 0.0
    assert aggregate["s2_minus_s3_debt_mean"] > 0.0
    assert aggregate["s3_better_gap_auc_rate"] >= 0.75
    assert aggregate["s3_better_unlogged_error_rate"] >= 0.75
    assert aggregate["s3_better_debt_rate"] >= 0.75


def test_bedc_jepa_experiment_runs_grid_pixel_learned_transition_benchmark():
    summary = _summary()
    grid = summary["grid_transition"]

    assert grid["source"]["observation"] == "grid-pixel"
    assert grid["source"]["transition_model"] == "linear-action-conditioned"
    assert grid["transition"]["one_step_r2"] > 0.90
    assert grid["transition"]["mean_l2_error"] < 0.20

    systems = grid["systems"]
    assert systems["S3"]["gap_detection_auc"] > systems["S2"]["gap_detection_auc"]
    assert systems["S3"]["unlogged_error_rate"] < systems["S2"]["unlogged_error_rate"]
    assert systems["S3"]["bedc_debt_score"] < systems["S2"]["bedc_debt_score"]

    planning = grid["planning"]
    assert planning["gap_aware"]["unsafe_state_rate"] < planning["vanilla"]["unsafe_state_rate"]
    assert planning["gap_aware"]["high_gap_state_rate"] < planning["vanilla"]["high_gap_state_rate"]
    assert planning["gap_aware"]["success_rate"] >= planning["vanilla"]["success_rate"] - 0.15

    sweep = grid["planning_sweep"]
    assert sweep["target_count"] >= 3
    assert sweep["trajectory_count"] >= 20
    assert sweep["gap_aware_minus_vanilla_success_rate"] >= -0.25
    assert sweep["vanilla_minus_gap_aware_high_gap_rate"] > 0.10
    assert sweep["vanilla_minus_gap_aware_unsafe_rate"] > 0.10
    assert sweep["vanilla_minus_gap_aware_risk_adjusted_cost"] > 0.0
    assert sweep["gap_aware_better_high_gap_rate"] >= 0.75


def test_bedc_jepa_experiment_runs_object_intervention_benchmark():
    summary = _summary()
    object_benchmark = summary["object_intervention"]

    assert object_benchmark["source"]["observation"] == "two-object-pixel-slots"
    assert object_benchmark["source"]["query"] == "counterfactual-contact-after-action"
    assert object_benchmark["transition"]["counterfactual_accuracy"] > 0.90
    assert object_benchmark["transition"]["intervention_sensitivity"] > 0.20

    systems = object_benchmark["systems"]
    assert systems["S3"]["distinction_accuracy_outside_gap"] > systems["S2"]["distinction_accuracy_outside_gap"]
    assert systems["S3"]["gap_detection_auc"] > systems["S2"]["gap_detection_auc"]
    assert systems["S3"]["unlogged_error_rate"] < systems["S2"]["unlogged_error_rate"]
    assert systems["S3"]["bedc_debt_score"] < systems["S2"]["bedc_debt_score"]

    masked = object_benchmark["object_masking"]
    assert masked["masked_object_accuracy_drop"] > 0.10
    assert masked["gap_auc_under_mask"] > systems["S2"]["gap_detection_auc"]


def test_bedc_jepa_experiment_runs_object_intervention_seed_sweep():
    summary = _summary()
    sweep = summary["object_intervention_sweep"]

    assert sweep["seed_count"] >= 8
    assert sweep["s3_minus_s2_outside_gap_accuracy_mean"] > 0.0
    assert sweep["s3_minus_s2_gap_auc_mean"] > 0.0
    assert sweep["s2_minus_s3_unlogged_error_mean"] > 0.0
    assert sweep["s2_minus_s3_debt_mean"] > 0.0
    assert sweep["s3_better_outside_gap_accuracy_rate"] >= 0.75
    assert sweep["s3_better_gap_auc_rate"] >= 0.75
    assert sweep["s3_better_unlogged_error_rate"] >= 0.75
    assert sweep["s3_better_debt_rate"] >= 0.75
    assert sweep["counterfactual_accuracy_mean"] > 0.90
    assert sweep["intervention_sensitivity_mean"] > 0.20


def test_bedc_jepa_experiment_runs_multi_object_distractor_benchmark():
    summary = _summary()
    benchmark = summary["multi_object_distractor"]

    assert benchmark["source"]["observation"] == "four-object-pixel-slots"
    assert benchmark["source"]["target_pair"] == "object-a-object-b"
    assert benchmark["source"]["distractor_count"] == 2
    assert benchmark["transition"]["counterfactual_accuracy"] > 0.88
    assert benchmark["transition"]["distractor_invariance"] > 0.75

    systems = benchmark["systems"]
    assert systems["S3"]["distinction_accuracy_outside_gap"] > systems["S2"]["distinction_accuracy_outside_gap"]
    assert systems["S3"]["gap_detection_auc"] > systems["S2"]["gap_detection_auc"]
    assert systems["S3"]["unlogged_error_rate"] < systems["S2"]["unlogged_error_rate"]
    assert systems["S3"]["bedc_debt_score"] < systems["S2"]["bedc_debt_score"]

    masking = benchmark["object_masking"]
    assert masking["target_mask_accuracy_drop"] > 0.10
    assert masking["distractor_mask_accuracy_drop"] < masking["target_mask_accuracy_drop"]


def test_bedc_jepa_experiment_runs_multi_object_distractor_seed_sweep():
    summary = _summary()
    sweep = summary["multi_object_distractor_sweep"]

    assert sweep["seed_count"] >= 6
    assert sweep["counterfactual_accuracy_mean"] > 0.88
    assert sweep["distractor_invariance_mean"] > 0.75
    assert sweep["s3_minus_s2_outside_gap_accuracy_mean"] > 0.0
    assert sweep["s3_minus_s2_gap_auc_mean"] > 0.0
    assert sweep["s2_minus_s3_unlogged_error_mean"] > 0.0
    assert sweep["s2_minus_s3_debt_mean"] > 0.0
    assert sweep["target_minus_distractor_mask_drop_mean"] > 0.10
    assert sweep["s3_better_outside_gap_accuracy_rate"] >= 0.75
    assert sweep["s3_better_gap_auc_rate"] >= 0.75
    assert sweep["s3_better_unlogged_error_rate"] >= 0.75
    assert sweep["s3_better_debt_rate"] >= 0.75


def test_bedc_jepa_experiment_runs_cluttered_object_seed_sweep():
    summary = _summary()
    sweep = summary["cluttered_object_sweep"]

    assert sweep["object_count"] == 6
    assert sweep["distractor_count"] == 4
    assert sweep["seed_count"] >= 4
    assert sweep["counterfactual_accuracy_mean"] > 0.86
    assert sweep["distractor_invariance_mean"] > 0.70
    assert sweep["s3_minus_s2_outside_gap_accuracy_mean"] > 0.0
    assert sweep["s3_minus_s2_gap_auc_mean"] > 0.0
    assert sweep["s2_minus_s3_unlogged_error_mean"] > 0.0
    assert sweep["s2_minus_s3_debt_mean"] > 0.0
    assert sweep["target_minus_distractor_mask_drop_mean"] > 0.08
    assert sweep["s3_better_gap_auc_rate"] >= 0.75
    assert sweep["s3_better_unlogged_error_rate"] >= 0.75

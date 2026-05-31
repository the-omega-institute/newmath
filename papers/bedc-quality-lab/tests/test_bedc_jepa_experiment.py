from scripts.run_bedc_jepa_experiment import run_experiment


def test_bedc_jepa_experiment_compares_four_systems():
    summary = run_experiment()
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
    summary = run_experiment()
    planning = summary["planning"]

    assert planning["vanilla"]["trajectory_count"] == planning["gap_aware"]["trajectory_count"]
    assert planning["gap_aware"]["unsafe_state_rate"] < planning["vanilla"]["unsafe_state_rate"]
    assert planning["gap_aware"]["high_gap_state_rate"] < planning["vanilla"]["high_gap_state_rate"]
    assert planning["gap_aware"]["success_rate"] >= planning["vanilla"]["success_rate"] - 0.10
    assert planning["gap_aware"]["objective_gap_penalty"] > 0.0


def test_bedc_jepa_experiment_runs_seed_sweep_with_second_world():
    summary = run_experiment()
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
    summary = run_experiment()
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

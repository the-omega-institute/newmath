from bedc_quality_lab.bedc_jepa_review_bundle import build_review_bundle


def test_review_bundle_records_reproducibility_contract_and_boundaries():
    bundle = build_review_bundle()

    assert bundle["schema_id"] == "bedc-jepa-review-bundle"
    assert bundle["status"] in {"review_ready", "incomplete"}
    assert bundle["source_commit_at_build"] == bundle["source_commit_observed_at_build"]
    assert "not a self-referential assertion" in bundle["source_commit_semantics"]
    assert bundle["required_artifacts"]["readiness"] == "reports/bedc_jepa_readiness.json"
    assert bundle["required_artifacts"]["native_minigrid_seed_sweep"] == (
        "reports/bedc_jepa_public_native_minigrid_seed_sweep.json"
    )
    assert bundle["required_artifacts"]["public_debt_decomposition"] == (
        "reports/bedc_jepa_public_debt_decomposition.json"
    )
    assert bundle["required_artifacts"]["conformal_certified_coverage"] == (
        "reports/bedc_jepa_conformal_certified_coverage.json"
    )
    assert bundle["required_artifacts"]["risk_success_pareto"] == "reports/bedc_jepa_risk_success_pareto.json"
    assert bundle["required_artifacts"]["loss_ablation"] == "reports/bedc_jepa_loss_ablation.json"
    assert bundle["required_artifacts"]["retraining_loss_ablation"] == (
        "reports/bedc_jepa_retraining_loss_ablation.json"
    )
    assert bundle["required_artifacts"]["quality_backend_candidate"] == (
        "reports/bedc_jepa_quality_backend_candidate.json"
    )
    assert bundle["required_artifacts"]["latent_claim_certificates"] == (
        "reports/bedc_latent_claim_certificates.json"
    )
    assert bundle["required_artifacts"]["conformal_gap_sweep"] == (
        "reports/bedc_conformal_gap_sweep.json"
    )
    assert bundle["required_artifacts"]["claim_boundary_audit"] == (
        "reports/bedc_claim_boundary_audit.json"
    )
    assert bundle["required_artifacts"]["vjepa2_ac_minigrid_claim_certificate"] == (
        "reports/bedc_vjepa2_ac_minigrid_claim_certificate.json"
    )
    assert bundle["required_artifacts"]["vjepa2_ac_minigrid_latent_prediction"] == (
        "reports/bedc_vjepa2_ac_minigrid_latent_prediction.json"
    )
    assert "python scripts/run_public_minigrid_native_seed_sweep.py" in bundle["reproduction_commands"]
    assert "python scripts/build_public_minigrid_debt_closure.py" in bundle["reproduction_commands"]
    assert "python scripts/run_torch_retraining_loss_ablation.py" in bundle["reproduction_commands"]
    assert "python scripts/build_bedc_jepa_quality_backend_candidate.py" in bundle["reproduction_commands"]
    assert "python scripts/run_bedc_latent_claim_certificate.py" in bundle["reproduction_commands"]
    assert "python scripts/run_vjepa2_ac_minigrid_claim_certificate.py" in bundle["reproduction_commands"]
    assert "python scripts/run_vjepa2_ac_minigrid_latent_prediction.py" in bundle["reproduction_commands"]
    assert "pdflatex -interaction=nonstopmode -halt-on-error main.tex" in bundle["reproduction_commands"]
    assert bundle["checks"]["checkpoint_contact"] == "closed"
    assert bundle["checks"]["native_public_benchmark"] == "closed"
    assert bundle["checks"]["native_unlogged_error_reduction"] > 0.05
    assert bundle["checks"]["native_planning_high_gap_reduction"] > 0.05
    assert bundle["checks"]["public_debt_diagnosis"] == "silent debt falls while coverage debt rises"
    assert bundle["checks"]["public_conformal_predicate_count"] >= 5.0
    assert bundle["checks"]["public_ablation_unlogged_penalty_effect"] >= 0.0
    assert bundle["checks"]["retraining_ablation_system_count"] >= 0.0
    assert bundle["checks"]["vjepa2_ac_lccp_claim_count"] >= 0.0
    assert bundle["checks"]["vjepa2_ac_latent_prediction_score"] >= 0.0

    if bundle["status"] == "review_ready":
        assert bundle["failures"] == []
        assert bundle["checks"]["seed_sweep_count"] >= 5.0
        assert bundle["checks"]["seed_sweep_unlogged_error_win_rate"] >= 0.6
    else:
        assert bundle["failures"]

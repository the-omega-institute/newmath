from bedc_quality_lab.bedc_jepa_review_bundle import build_review_bundle


def test_review_bundle_records_reproducibility_contract_and_boundaries():
    bundle = build_review_bundle()

    assert bundle["schema_id"] == "bedc-jepa-review-bundle"
    assert bundle["status"] in {"review_ready", "incomplete"}
    assert bundle["required_artifacts"]["readiness"] == "reports/bedc_jepa_readiness.json"
    assert bundle["required_artifacts"]["native_minigrid_seed_sweep"] == (
        "reports/bedc_jepa_public_native_minigrid_seed_sweep.json"
    )
    assert "python scripts/run_public_minigrid_native_seed_sweep.py" in bundle["reproduction_commands"]
    assert "pdflatex -interaction=nonstopmode -halt-on-error main.tex" in bundle["reproduction_commands"]
    assert bundle["checks"]["checkpoint_contact"] == "closed"
    assert bundle["checks"]["native_public_benchmark"] == "closed"
    assert bundle["checks"]["native_unlogged_error_reduction"] > 0.05
    assert bundle["checks"]["native_planning_high_gap_reduction"] > 0.05

    if bundle["status"] == "review_ready":
        assert bundle["failures"] == []
        assert bundle["checks"]["seed_sweep_count"] >= 5.0
        assert bundle["checks"]["seed_sweep_unlogged_error_win_rate"] >= 0.6
    else:
        assert bundle["failures"]

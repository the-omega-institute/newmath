import json

import pytest

from scripts import run_debt_dose_response as dose


def dose_record(level, level_index, seed_index, quality_q):
    return {
        "debt_level": level,
        "level_index": level_index,
        "seed_index": seed_index,
        "seed": 10_000 + level_index * 100 + seed_index,
        "metrics": {
            "quality_q": quality_q,
            "quality_debt": level,
            "target_score": min(level, 0.2),
            "quality_benefit": quality_q + 0.03 + level,
            "quality_cost": 0.03,
            "linear_identifiability_r2": 0.99 - level * 0.01,
            "approx_identifiability_proxy": 0.95 - level * 0.02,
        },
    }


def synthetic_records(*, failing=False):
    means = [0.90, 0.80, 0.70, 0.60, 0.50]
    if failing:
        means = [0.90, 0.80, 0.82, 0.60, 0.50]
    records = []
    for level_index, level in enumerate(dose.DEBT_LEVELS):
        for seed_index in range(dose.SEED_COUNT):
            offset = (seed_index - 11.5) * 0.0001
            records.append(dose_record(level, level_index, seed_index, means[level_index] + offset))
    return records


def test_child_seed_is_deterministic_bounded_and_stream_separated():
    first = [dose._child_seed(101, 0, index) for index in range(8)]
    second = [dose._child_seed(101, 0, index) for index in range(8)]
    level_stream = [dose._child_seed(101, 1, index) for index in range(8)]
    master_stream = [dose._child_seed(202, 0, index) for index in range(8)]

    assert first == second
    assert first != level_stream
    assert first != master_stream
    assert len(set(first + level_stream)) == len(first + level_stream)
    assert all(0 <= seed <= 0xFFFFFFFF for seed in first + level_stream + master_stream)


def test_dose_surface_branches_by_debt_level():
    surfaces = {level: dose._dose_surface(level) for level in dose.DEBT_LEVELS}

    assert surfaces[0.0].classifier_spec_base["name"] == "certified-standardized-linear-reader"
    assert surfaces[0.0].classifier_spec_base["training"] == "certified deterministic standardization"
    assert surfaces[0.2].classifier_spec_base["name"] == "certified-standardized-linear-reader"
    assert surfaces[0.2].classifier_spec_base["training"] == "certified deterministic standardization"
    for level in (0.1, 0.3, 0.4):
        assert surfaces[level].classifier_spec_base["name"] == "deterministic-standardized-linear-reader"
        assert surfaces[level].classifier_spec_base["training"] == "deterministic standardization"

    assert [surfaces[level].sample_count for level in dose.DEBT_LEVELS] == [2048, 2048, 384, 384, 384]
    assert [surfaces[level].source_spec["sample_count"] for level in dose.DEBT_LEVELS] == [2048, 2048, 384, 384, 384]
    assert surfaces[0.3].stability_spec == {
        "name": "multi-seed-stability",
        "pair_process": "ornstein-uhlenbeck",
        "multi_seed": True,
    }
    assert surfaces[0.4].stability_spec == {
        "name": "single-seed-stability",
        "pair_process": "ornstein-uhlenbeck",
        "multi_seed": False,
    }


def test_record_wires_real_debt_injection_certificate_and_target_score():
    baseline = dose._record(0.0, 0, 0)
    classifier_debt = dose._record(0.1, 1, 0)
    finite_sample_debt = dose._record(0.2, 2, 0)
    combined_debt = dose._record(0.4, 4, 0)

    assert baseline["generation"]["sample_count"] == 2048
    assert baseline["classifier_spec"]["name"] == "certified-standardized-linear-reader"
    assert baseline["classifier_spec"]["cert_status"] == "certified"
    assert baseline["metrics"]["target_score"] == pytest.approx(0.0)
    assert baseline["metrics"]["quality_debt"] == pytest.approx(0.2)
    assert baseline["ledger_gaps"] == [
        "kind=verification; residue=theorem3-bound-margin; severity=high; status=open"
    ]

    assert classifier_debt["generation"]["sample_count"] == 2048
    assert classifier_debt["classifier_spec"]["name"] == "deterministic-standardized-linear-reader"
    assert classifier_debt["classifier_spec"]["training"] == "deterministic standardization"
    assert classifier_debt["classifier_spec"]["cert_status"] == "certified"
    assert classifier_debt["metrics"]["target_score"] == pytest.approx(0.0)
    assert classifier_debt["metrics"]["quality_debt"] == pytest.approx(0.3)
    assert "kind=classifier; residue=optimizer-certificate; severity=medium; status=partial" in classifier_debt["ledger_gaps"]

    assert finite_sample_debt["generation"]["sample_count"] == 384
    assert finite_sample_debt["classifier_spec"]["cert_status"] == "certified"
    assert finite_sample_debt["metrics"]["target_score"] == pytest.approx(0.2)
    assert finite_sample_debt["metrics"]["quality_debt"] == pytest.approx(0.4)
    assert "kind=source; residue=finite-sample-support; severity=high; status=open" in finite_sample_debt["ledger_gaps"]

    assert combined_debt["generation"]["sample_count"] == 384
    assert combined_debt["classifier_spec"]["name"] == "deterministic-standardized-linear-reader"
    assert combined_debt["classifier_spec"]["cert_status"] == "certified"
    assert combined_debt["stability_spec"]["name"] == "single-seed-stability"
    assert combined_debt["stability_spec"]["multi_seed"] is False
    assert combined_debt["metrics"]["target_score"] == pytest.approx(0.2)
    assert combined_debt["metrics"]["quality_debt"] == pytest.approx(0.6)
    assert "kind=generalization; residue=global-claim-boundary; severity=medium; status=partial" in combined_debt["ledger_gaps"]


def test_records_real_producer_remains_complete_and_monotone():
    records = dose._records()
    aggregate = dose._aggregate(records)

    assert len(records) == len(dose.DEBT_LEVELS) * dose.SEED_COUNT
    assert aggregate["record_count"] == len(records)
    assert aggregate["monotonicity"]["quality_q_means"] == pytest.approx([
        0.7493259772233684,
        0.6488804201061507,
        0.5425342394938547,
        0.44035778432843796,
        0.34474597669571355,
    ])
    assert aggregate["monotonicity"]["strictly_decreasing"]
    assert aggregate["monotonicity"]["slope_ci_below_zero"]
    assert aggregate["monotonicity"]["pass"]
    assert [
        aggregate["by_level"][f"{level:.1f}"]["metrics"]["target_score"]["mean"]
        for level in dose.DEBT_LEVELS
    ] == pytest.approx([0.0, 0.0, 0.2, 0.2, 0.2])


def test_aggregate_summarizes_levels_and_passes_monotonicity():
    aggregate = dose._aggregate(synthetic_records())

    assert aggregate["metrics"] == list(dose.METRICS)
    assert aggregate["record_count"] == len(dose.DEBT_LEVELS) * dose.SEED_COUNT
    assert aggregate["by_level"]["0.0"]["metrics"]["quality_q"]["mean"] == pytest.approx(0.9)
    assert aggregate["by_level"]["0.4"]["metrics"]["quality_debt"]["mean"] == pytest.approx(0.4)
    assert aggregate["monotonicity"]["quality_q_means"] == pytest.approx([0.9, 0.8, 0.7, 0.6, 0.5])
    assert aggregate["monotonicity"]["strictly_decreasing"]
    assert aggregate["monotonicity"]["slope_ci_below_zero"]
    assert aggregate["monotonicity"]["pass"]
    assert aggregate["regression"]["slope_ci95_high"] < 0.0


def test_aggregate_fails_closed_for_non_monotone_level_means():
    aggregate = dose._aggregate(synthetic_records(failing=True))

    assert aggregate["monotonicity"]["quality_q_means"] == pytest.approx([0.9, 0.8, 0.82, 0.6, 0.5])
    assert aggregate["monotonicity"]["strictly_decreasing"] is False
    assert aggregate["monotonicity"]["pass"] is False


def test_render_report_contains_failed_monotonicity_boundary_source_and_seed_rows():
    records = synthetic_records(failing=True)
    report = dose._render_report(records, dose._aggregate(records))

    assert "# BEDC Quality Lab Debt Dose Response" in report
    assert "## Applicability Boundary" in report
    assert "Gaussian-OU hidden-debt dose surface" in report
    assert "ornstein-uhlenbeck" in report
    assert "hidden-debt-dose-surface" in report
    assert "linear-identifiability" in report
    assert "quality_q range: `[0.0, 1.0]`" in report
    assert "## Source Artifacts" in report
    assert "`scripts/run_debt_dose_response.py`" in report
    assert "`bedc_quality_lab/metrics.py`" in report
    assert "`bedc_quality_lab/debt.py`" in report
    assert "`bedc_quality_lab/ledger.py`" in report
    assert "`bedc_quality_lab/scope.py`" in report
    assert "## Monotonicity Check" in report
    assert "- Result: `fail`" in report
    assert "- Strictly decreasing level means: `false`" in report
    assert "| 0.0 | 0 | 10000 | +0.898850 | 0.000000 | 0.000000 | 0.990000 | 0.950000 |" in report


def test_main_writes_json_and_markdown_payload_shape(monkeypatch, tmp_path):
    monkeypatch.setattr(dose, "ROOT", tmp_path)
    monkeypatch.setattr(dose, "_records", synthetic_records)

    dose.main()

    payload = json.loads((tmp_path / dose.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / dose.REPORT_ARTIFACT).read_text(encoding="utf-8")

    assert payload["artifact"] == dose.JSON_ARTIFACT
    assert payload["report"] == dose.REPORT_ARTIFACT
    assert payload["applicability_boundary"]["admitted_family_id"] == "ornstein-uhlenbeck"
    assert payload["applicability_boundary"]["quality_q_range"] == [0.0, 1.0]
    assert payload["source_artifacts"]["script"] == "scripts/run_debt_dose_response.py"
    assert [item["path"] for item in payload["source_artifacts"]["dependency_chain"]] == [
        "bedc_quality_lab/metrics.py",
        "bedc_quality_lab/debt.py",
        "bedc_quality_lab/ledger.py",
        "bedc_quality_lab/scope.py",
    ]
    assert len(payload["records"]) == len(dose.DEBT_LEVELS) * dose.SEED_COUNT
    assert payload["aggregate"]["monotonicity"]["pass"]
    assert "## Applicability Boundary" in report
    assert "## Source Artifacts" in report

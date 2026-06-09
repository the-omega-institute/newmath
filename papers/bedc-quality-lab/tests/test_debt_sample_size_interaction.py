import json
from types import SimpleNamespace

import pytest

from scripts import run_debt_sample_size_interaction as interaction


def metric_row(sample_count, debt_level, seed_index, value):
    metrics = {name: 1.0 for name in interaction.METRIC_NAMES}
    metrics[interaction.INTERACTION_METRIC] = value
    seed = 10_000 + sample_count + seed_index
    return {
        "sample_count": sample_count,
        "sample_index": interaction.SAMPLE_COUNTS.index(sample_count),
        "debt_level": debt_level,
        "level_index": interaction.DEBT_LEVELS.index(debt_level),
        "seed_index": seed_index,
        "master_seed": interaction.MASTER_SEED,
        "seed": seed,
        "run_id": f"fixture-n{sample_count}-debt-{debt_level}-seed-{seed}",
        "classifier_name": "fixture-classifier",
        "classifier_training": "fixture-training",
        "metrics": metrics,
        "debt_items": [],
        "ledger_gaps": [],
        "source_artifacts": {"script": "scripts/run_debt_sample_size_interaction.py"},
    }


def synthetic_records(*, slopes_by_sample_count=None):
    slopes_by_sample_count = slopes_by_sample_count or {
        96: -1.00,
        192: -1.00,
        384: -1.00,
        768: -1.00,
    }
    rows = []
    for sample_count in interaction.SAMPLE_COUNTS:
        slope = slopes_by_sample_count[sample_count]
        for debt_level in interaction.DEBT_LEVELS:
            mean = 0.9 + slope * debt_level
            for seed_index, offset in enumerate((-0.01, 0.0, 0.01)):
                rows.append(metric_row(sample_count, debt_level, seed_index, mean + offset))
    return rows


def test_config_rejects_undersized_or_non_increasing_grids_and_seed_floor():
    with pytest.raises(ValueError, match="four sample_count"):
        interaction._validate_config(sample_counts=(96, 192, 384))
    with pytest.raises(ValueError, match="five debt_level"):
        interaction._validate_config(debt_levels=(0.0, 0.1, 0.2, 0.3))
    with pytest.raises(ValueError, match="seed_count >= 15"):
        interaction._validate_config(seed_count=14)
    with pytest.raises(ValueError, match="strictly increasing"):
        interaction._validate_config(sample_counts=(96, 192, 192, 768))
    with pytest.raises(ValueError, match="strictly increasing"):
        interaction._validate_config(debt_levels=(0.0, 0.2, 0.1, 0.3, 0.4))


def test_child_seed_is_stable_and_separated_by_grid_coordinates():
    first = [
        interaction._child_seed(101, sample_index=0, level_index=0, seed_index=index)
        for index in range(6)
    ]
    second = [
        interaction._child_seed(101, sample_index=0, level_index=0, seed_index=index)
        for index in range(6)
    ]
    sample_stream = [
        interaction._child_seed(101, sample_index=1, level_index=0, seed_index=index)
        for index in range(6)
    ]
    level_stream = [
        interaction._child_seed(101, sample_index=0, level_index=1, seed_index=index)
        for index in range(6)
    ]

    assert first == second
    assert first != sample_stream
    assert first != level_stream
    assert len(set(first + sample_stream + level_stream)) == len(first + sample_stream + level_stream)
    assert all(0 <= seed <= 0xFFFFFFFF for seed in first + sample_stream + level_stream)


def test_records_enumerates_grid_and_passes_independent_axes(monkeypatch):
    calls = []
    monkeypatch.setattr(interaction, "SAMPLE_COUNTS", (96, 192, 384, 768))
    monkeypatch.setattr(interaction, "DEBT_LEVELS", (0.0, 0.1, 0.2, 0.3, 0.4))
    monkeypatch.setattr(interaction, "SEED_COUNT", 15)

    def fake_run_record(**kwargs):
        calls.append(kwargs)
        return metric_row(
            kwargs["sample_count"],
            kwargs["debt_level"],
            kwargs["seed_index"],
            0.9 - kwargs["debt_level"],
        )

    monkeypatch.setattr(interaction, "_run_record", fake_run_record)

    rows = interaction._records()

    assert len(rows) == 300
    assert calls[0]["sample_count"] == 96
    assert calls[0]["debt_level"] == 0.0
    assert calls[0]["seed_index"] == 0
    assert calls[75]["sample_count"] == 192
    assert calls[75]["debt_level"] == 0.0
    assert calls[75]["seed_index"] == 0
    assert calls[15]["sample_count"] == 96
    assert calls[15]["debt_level"] == 0.1
    assert rows[0]["sample_count"] == 96
    assert rows[0]["debt_level"] == 0.0
    assert rows[0]["seed_index"] == 0
    assert rows[0]["run_id"].startswith("fixture-n96-debt-0.0")


def test_run_record_transmits_sample_debt_seed_run_and_artifacts(monkeypatch):
    monkeypatch.setattr(
        interaction,
        "_synthetic_metrics",
        lambda seed, surface: {
            "linear_identifiability_r2": 0.99,
            "orthogonality_error": 0.01,
            "covariance_deviation": 0.02,
            "approx_identifiability_proxy": 0.95,
        },
    )
    monkeypatch.setattr(
        interaction,
        "classifier_certificate",
        lambda metrics, min_r2, min_proxy: {
            "cert_status": "certified",
            "cert_score": 1.0,
            "cert_r2": metrics["linear_identifiability_r2"],
            "cert_proxy": metrics["approx_identifiability_proxy"],
        },
    )
    assessment = SimpleNamespace(
        items=(
            SimpleNamespace(
                kind="source",
                residue=interaction.TARGET_RESIDUE,
                severity="none",
                status="closed",
                score=0.0,
            ),
        ),
        debt_total=0.2,
    )
    monkeypatch.setattr(interaction, "assess_debt", lambda *args: assessment)
    monkeypatch.setattr(interaction, "derive_ledger_gaps", lambda *args: [])

    record = interaction._run_record(
        sample_count=192,
        sample_index=1,
        debt_level=0.3,
        level_index=3,
        seed_index=7,
        seed=123456,
    )

    assert record["sample_count"] == 192
    assert record["source_spec"]["sample_count"] == 192
    assert record["debt_level"] == pytest.approx(0.3)
    assert record["seed_index"] == 7
    assert record["seed"] == 123456
    assert record["run_id"] == "debt-sample-size-n192-debt-0p3-seed-123456"
    assert record["classifier_name"] == "deterministic-standardized-linear-reader"
    assert record["classifier_training"] == "deterministic standardization"
    assert record["metrics"]["quality_q"] == pytest.approx(
        record["metrics"]["quality_benefit"] - record["metrics"]["quality_cost"] - 0.2
    )
    assert record["source_artifacts"]["script"] == "scripts/run_debt_sample_size_interaction.py"


def test_aggregate_reports_per_cell_mean_std_and_ci(monkeypatch):
    monkeypatch.setattr(interaction, "SAMPLE_COUNTS", (96, 192, 384, 768))
    monkeypatch.setattr(interaction, "DEBT_LEVELS", (0.0, 0.1, 0.2, 0.3, 0.4))

    aggregate = interaction._aggregate(synthetic_records())
    cell = aggregate["by_sample_count_debt_level"]["n_96__debt_0p0"]
    metric = cell["metrics"][interaction.INTERACTION_METRIC]

    assert aggregate["cell_count"] == 20
    assert cell["record_count"] == 3
    assert metric["n"] == 3
    assert metric["mean"] == pytest.approx(0.9)
    assert metric["std"] == pytest.approx(0.01)
    assert metric["ci95_low"] < metric["mean"] < metric["ci95_high"]


def test_per_sample_count_linear_slopes_and_h0_not_rejected(monkeypatch):
    monkeypatch.setattr(interaction, "SAMPLE_COUNTS", (96, 192, 384, 768))
    monkeypatch.setattr(interaction, "DEBT_LEVELS", (0.0, 0.1, 0.2, 0.3, 0.4))

    slopes = interaction._per_sample_count_slopes(interaction._aggregate(synthetic_records()))
    test = interaction._interaction_test(slopes)

    assert slopes["n_96"]["linear_fit"]["status"] == "ok"
    assert slopes["n_96"]["linear_fit"]["slope"] == pytest.approx(-1.0)
    assert slopes["n_384"]["linear_fit"]["slope"] < 0.0
    assert test["slope_ci_common_overlap"]["all_overlap"]
    assert test["h0_not_rejected"]
    assert not test["h0_rejected"]


def test_h0_rejected_when_slope_cis_are_separated(monkeypatch):
    monkeypatch.setattr(interaction, "SAMPLE_COUNTS", (96, 192, 384, 768))
    monkeypatch.setattr(interaction, "DEBT_LEVELS", (0.0, 0.1, 0.2, 0.3, 0.4))
    rows = synthetic_records(
        slopes_by_sample_count={
            96: -1.0,
            192: -0.5,
            384: -0.1,
            768: 0.2,
        }
    )

    test = interaction._interaction_test(interaction._per_sample_count_slopes(interaction._aggregate(rows)))

    assert not test["slope_ci_common_overlap"]["all_overlap"]
    assert not test["h0_not_rejected"]
    assert test["h0_rejected"]


def test_payload_and_markdown_projection_include_required_fields(monkeypatch):
    monkeypatch.setattr(interaction, "SAMPLE_COUNTS", (96, 192, 384, 768))
    monkeypatch.setattr(interaction, "DEBT_LEVELS", (0.0, 0.1, 0.2, 0.3, 0.4))
    monkeypatch.setattr(interaction, "SEED_COUNT", 15)

    payload = interaction._payload(synthetic_records())
    report = interaction._render_report(payload)

    assert set(payload) >= {
        "config",
        "records",
        "aggregate",
        "per_sample_count_slopes",
        "interaction_test",
        "applicability_boundary",
        "source_artifacts",
    }
    assert "by_sample_count_debt_level" in payload["aggregate"]
    assert payload["source_artifacts"]["generation_script"] == (
        "scripts/run_debt_sample_size_interaction.py"
    )
    assert payload["source_artifacts"]["shared_stats_helper"] == "scripts/experiment_stats.py"
    assert "bedc_quality_lab.debt.assess_debt" in payload["source_artifacts"][
        "import_dependency_chain"
    ]
    assert payload["applicability_boundary"]["sample_count_range"] == [96, 768]

    assert "# Hidden-Debt Sample-Size Interaction Experiment" in report
    assert "## Cell Error Bars" in report
    assert "## Per-Sample Count Degradation Slopes" in report
    assert "## Interaction Test" in report
    assert "Negative result note" in report
    assert "## Applicability Boundary" in report
    assert "## Source Artifacts" in report
    assert "## Raw Record Index" in report
    assert "| 96 | 0.0 | +0.900000 +/- 0.010000 |" in report
    assert "Debt set: `0.0, 0.1, 0.2, 0.3, 0.4`." in report


def test_main_writes_json_and_markdown(monkeypatch, tmp_path):
    monkeypatch.setattr(interaction, "ROOT", tmp_path)
    monkeypatch.setattr(interaction, "SAMPLE_COUNTS", (96, 192, 384, 768))
    monkeypatch.setattr(interaction, "DEBT_LEVELS", (0.0, 0.1, 0.2, 0.3, 0.4))
    monkeypatch.setattr(interaction, "SEED_COUNT", 15)
    monkeypatch.setattr(interaction, "_records", synthetic_records)

    interaction.main()

    payload = json.loads((tmp_path / interaction.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / interaction.REPORT_ARTIFACT).read_text(encoding="utf-8")

    assert len(payload["records"]) == 60
    assert payload["config"]["expected_record_count"] == 300
    assert payload["interaction_test"]["h0_not_rejected"]
    assert "Total records: `60`" in report
    assert "Sample counts: `96, 192, 384, 768`" in report

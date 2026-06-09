import json
from types import SimpleNamespace

import pytest

from scripts import run_sample_size_rho_interaction as interaction


def envelope_for(kwargs, metrics):
    return SimpleNamespace(
        classifier_spec={"name": "fixture-classifier", "training": "fixture-training"},
        metrics=metrics,
        to_dict=lambda: {
            "run_id": kwargs["run_id"],
            "source_spec": {
                "sample_count": kwargs["sample_count"],
                "rho": kwargs["rho"],
            },
            "classifier_spec": {
                "name": "fixture-classifier",
                "training": "fixture-training",
            },
            "metrics": dict(metrics),
            "artifacts": {
                "envelope": kwargs["envelope_artifact"],
                "report": kwargs["report_artifact"],
            },
        },
    )


def metric_row(sample_count, rho, seed_index, value):
    metrics = {name: 1.0 for name in interaction.METRIC_NAMES}
    metrics[interaction.INTERACTION_METRIC] = value
    seed = 1000 + seed_index
    return {
        "sample_count": sample_count,
        "rho": rho,
        "seed_index": seed_index,
        "seed": seed,
        "run_id": f"fixture-n{sample_count}-rho-{rho}-seed-{seed}",
        "classifier_name": "fixture-classifier",
        "classifier_training": "fixture-training",
        "metrics": metrics,
        "envelope": {"run_id": f"fixture-n{sample_count}-rho-{rho}-seed-{seed}"},
    }


def synthetic_records(*, offsets_by_rho=None):
    rows = []
    offsets_by_rho = offsets_by_rho or {
        0.3: {
            96: [-0.20, 0.00, 0.20],
            192: [-0.141421356, 0.00, 0.141421356],
            384: [-0.10, 0.00, 0.10],
            768: [-0.070710678, 0.00, 0.070710678],
        },
        0.6: {
            96: [-0.19, 0.00, 0.19],
            192: [-0.134350288, 0.00, 0.134350288],
            384: [-0.095, 0.00, 0.095],
            768: [-0.067175144, 0.00, 0.067175144],
        },
        0.9: {
            96: [-0.21, 0.00, 0.21],
            192: [-0.148492424, 0.00, 0.148492424],
            384: [-0.105, 0.00, 0.105],
            768: [-0.074246212, 0.00, 0.074246212],
        },
    }
    for rho, by_sample_count in offsets_by_rho.items():
        for sample_count, offsets in by_sample_count.items():
            for seed_index, offset in enumerate(offsets):
                rows.append(metric_row(sample_count, rho, seed_index, 0.9 + offset))
    return rows


def test_default_grid_has_expected_record_count_and_seed_floor():
    assert interaction.SAMPLE_COUNTS == (96, 192, 384, 768)
    assert interaction.RHO_VALUES == (0.3, 0.6, 0.9)
    assert interaction.SEED_COUNT >= 15
    assert len(interaction.SAMPLE_COUNTS) * len(interaction.RHO_VALUES) * interaction.SEED_COUNT == 180


def test_records_enumerates_grid_and_passes_runner_arguments(monkeypatch):
    calls = []
    monkeypatch.setattr(interaction, "SAMPLE_COUNTS", (96, 192))
    monkeypatch.setattr(interaction, "RHO_VALUES", (0.3, 0.9))
    monkeypatch.setattr(interaction, "SEED_COUNT", 2)

    def fake_run_experiment(**kwargs):
        calls.append(kwargs)
        metrics = {name: 10.0 for name in interaction.METRIC_NAMES}
        metrics[interaction.INTERACTION_METRIC] = kwargs["sample_count"] / 1000.0 + kwargs["rho"]
        return envelope_for(kwargs, metrics)

    monkeypatch.setattr(interaction, "run_experiment", fake_run_experiment)

    rows = interaction._records()

    assert len(rows) == 8
    assert calls[0] == {
        "use_torch": interaction.USE_TORCH,
        "sample_count": 96,
        "seed": interaction._seeds(interaction.MASTER_SEED, 2)[0],
        "rho": 0.3,
        "run_id": (
            f"sample-size-rho-n96-rho-0p3-seed-"
            f"{interaction._seeds(interaction.MASTER_SEED, 2)[0]}"
        ),
        "envelope_artifact": interaction.JSON_ARTIFACT,
        "report_artifact": interaction.REPORT_ARTIFACT,
    }
    assert {row["rho"] for row in rows} == {0.3, 0.9}
    assert {row["sample_count"] for row in rows} == {96, 192}
    assert rows[0]["classifier_name"] == "fixture-classifier"
    assert rows[0]["classifier_training"] == "fixture-training"
    assert rows[0]["metrics"][interaction.INTERACTION_METRIC] == pytest.approx(0.396)
    assert rows[0]["envelope"]["artifacts"] == {
        "envelope": interaction.JSON_ARTIFACT,
        "report": interaction.REPORT_ARTIFACT,
    }


def test_aggregate_reports_per_cell_mean_std_and_ci(monkeypatch):
    monkeypatch.setattr(interaction, "SAMPLE_COUNTS", (96, 192, 384, 768))
    monkeypatch.setattr(interaction, "RHO_VALUES", (0.3, 0.6, 0.9))

    aggregate = interaction._aggregate(synthetic_records())
    cell = aggregate["by_rho_sample_count"]["rho_0p3__n_96"]
    metric = cell["metrics"][interaction.INTERACTION_METRIC]

    assert cell["record_count"] == 3
    assert metric["n"] == 3
    assert metric["mean"] == pytest.approx(0.9)
    assert metric["std"] == pytest.approx(0.2)
    assert metric["ci95_half_width"] == pytest.approx(1.96 * 0.2 / (3**0.5))
    assert metric["ci95_low"] < metric["mean"] < metric["ci95_high"]


def test_per_rho_slope_fit_and_h0_overlap_not_rejected(monkeypatch):
    monkeypatch.setattr(interaction, "SAMPLE_COUNTS", (96, 192, 384, 768))
    monkeypatch.setattr(interaction, "RHO_VALUES", (0.3, 0.6, 0.9))

    aggregate = interaction._aggregate(synthetic_records())
    slopes = interaction._per_rho_slopes(aggregate)
    test = interaction._interaction_test(slopes)

    assert slopes["rho_0p3"]["log_log_fit"]["status"] == "ok"
    assert slopes["rho_0p3"]["log_log_fit"]["slope"] == pytest.approx(-0.5, abs=0.02)
    assert test["slope_ci_common_overlap"]["all_overlap"]
    assert test["h0_not_rejected"]
    assert not test["h0_rejected"]


def test_h0_overlap_rejected_when_slope_cis_separate(monkeypatch):
    monkeypatch.setattr(interaction, "SAMPLE_COUNTS", (96, 192, 384, 768))
    monkeypatch.setattr(interaction, "RHO_VALUES", (0.3, 0.6, 0.9))
    rows = synthetic_records(
        offsets_by_rho={
            0.3: {
                96: [-0.20, 0.00, 0.20],
                192: [-0.141421356, 0.00, 0.141421356],
                384: [-0.10, 0.00, 0.10],
                768: [-0.070710678, 0.00, 0.070710678],
            },
            0.6: {
                96: [-0.05, 0.00, 0.05],
                192: [-0.10, 0.00, 0.10],
                384: [-0.20, 0.00, 0.20],
                768: [-0.40, 0.00, 0.40],
            },
            0.9: {
                96: [-0.08, 0.00, 0.08],
                192: [-0.16, 0.00, 0.16],
                384: [-0.32, 0.00, 0.32],
                768: [-0.64, 0.00, 0.64],
            },
        }
    )

    slopes = interaction._per_rho_slopes(interaction._aggregate(rows))
    test = interaction._interaction_test(slopes)

    assert not test["slope_ci_common_overlap"]["all_overlap"]
    assert not test["h0_not_rejected"]
    assert test["h0_rejected"]


def test_payload_and_markdown_projection_include_required_fields(monkeypatch):
    monkeypatch.setattr(interaction, "SAMPLE_COUNTS", (96, 192, 384, 768))
    monkeypatch.setattr(interaction, "RHO_VALUES", (0.3, 0.6, 0.9))

    payload = interaction._payload(synthetic_records())
    report = interaction._render_report(payload)

    assert payload["artifact"] == interaction.JSON_ARTIFACT
    assert payload["report"] == interaction.REPORT_ARTIFACT
    assert set(payload) >= {
        "config",
        "records",
        "aggregate",
        "per_rho_slopes",
        "interaction_test",
        "applicability_boundary",
        "source_artifacts",
    }
    assert "by_rho_sample_count" in payload["aggregate"]
    assert payload["source_artifacts"]["generation_script"] == (
        "scripts/run_sample_size_rho_interaction.py"
    )
    assert payload["source_artifacts"]["shared_stats_helper"] == "scripts/experiment_stats.py"
    assert "bedc_quality_lab.metrics.metric_bundle" in payload["source_artifacts"][
        "import_dependency_chain"
    ]
    assert payload["applicability_boundary"]["sample_count_range"] == [96, 768]

    assert "# Sample-Size Rho Interaction Experiment" in report
    assert "## Cell Error Bars" in report
    assert "## Per-Rho Std Slopes" in report
    assert "## Interaction Test" in report
    assert "## Applicability Boundary" in report
    assert "## Source Artifacts" in report
    assert "| 0.3 | 96 | 0.900000 +/- 0.200000 |" in report
    assert "H0 not rejected: `pass`" in report


def test_main_writes_json_and_markdown(monkeypatch, tmp_path):
    monkeypatch.setattr(interaction, "ROOT", tmp_path)
    monkeypatch.setattr(interaction, "SAMPLE_COUNTS", (96, 192, 384, 768))
    monkeypatch.setattr(interaction, "RHO_VALUES", (0.3, 0.6, 0.9))
    monkeypatch.setattr(interaction, "_records", synthetic_records)

    interaction.main()

    payload = json.loads((tmp_path / interaction.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / interaction.REPORT_ARTIFACT).read_text(encoding="utf-8")

    assert len(payload["records"]) == 36
    assert payload["interaction_test"]["h0_not_rejected"]
    assert "Total records: `36`" in report
    assert "Rho set: `0.3, 0.6, 0.9`." in report

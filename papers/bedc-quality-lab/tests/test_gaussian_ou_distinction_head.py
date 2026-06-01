import json
from types import SimpleNamespace

import numpy as np
import pytest

from scripts import run_gaussian_ou_distinction_head as runner


def test_default_config_is_structural_consensus_scope():
    assert runner.SAMPLE_COUNT == 384
    assert runner.SEED_COUNT == 30
    assert runner.RHO == 0.82
    assert runner.USE_TORCH is False
    assert runner.DISTINCTIONS == (
        "latent_x_positive",
        "latent_y_positive",
        "high_energy",
    )


def test_label_truth_uses_three_operational_per_sample_distinctions():
    z = np.array([[1.0, -2.0], [-0.5, 0.25], [0.0, 3.0]], dtype=np.float64)

    x_label = runner._label_truth("latent_x_positive", z, high_energy_threshold=1.0)
    y_label = runner._label_truth("latent_y_positive", z, high_energy_threshold=1.0)
    e_label = runner._label_truth("high_energy", z, high_energy_threshold=4.0)

    assert x_label.tolist() == [1.0, 0.0, 0.0]
    assert y_label.tolist() == [0.0, 1.0, 1.0]
    assert e_label.tolist() == [1.0, 0.0, 1.0]


def test_train_eval_split_is_deterministic_and_disjoint():
    train_a, eval_a = runner._train_eval_split(20, seed=123)
    train_b, eval_b = runner._train_eval_split(20, seed=123)
    train_c, eval_c = runner._train_eval_split(20, seed=124)

    assert train_a.tolist() == train_b.tolist()
    assert eval_a.tolist() == eval_b.tolist()
    assert set(train_a).isdisjoint(set(eval_a))
    assert len(train_a) == 14
    assert len(eval_a) == 6
    assert train_a.tolist() != train_c.tolist() or eval_a.tolist() != eval_c.tolist()


def test_run_record_passes_canonical_runner_arguments_and_builds_distinction_rows(monkeypatch):
    calls = []
    z = np.array(
        [
            [2.0, -1.0],
            [-2.0, -1.0],
            [2.0, 1.0],
            [-2.0, 1.0],
            [1.0, -2.0],
            [-1.0, -2.0],
            [1.0, 2.0],
            [-1.0, 2.0],
        ],
        dtype=np.float64,
    )
    z_pair = np.array(
        [
            [-2.0, -1.0],
            [-2.0, -1.0],
            [2.0, 1.0],
            [2.0, 1.0],
            [1.0, -2.0],
            [-1.0, -2.0],
            [1.0, 2.0],
            [-1.0, 2.0],
        ],
        dtype=np.float64,
    )

    def fake_make_toy_batch(sample_count, *, rho, seed):
        assert sample_count == 8
        assert rho == runner.RHO
        assert seed == 4242
        return SimpleNamespace(z=z, z_pair=z_pair)

    def fake_run_experiment(**kwargs):
        calls.append(kwargs)
        return SimpleNamespace(
            run_id=kwargs["run_id"],
            source_spec={"name": "fixture-source", "sample_count": kwargs["sample_count"]},
            classifier_spec={"name": "fixture-classifier"},
            metrics={"quality_q": 0.25, "quality_margin": 0.75},
            artifacts={
                "envelope": kwargs["envelope_artifact"],
                "report": kwargs["report_artifact"],
            },
        )

    monkeypatch.setattr(runner, "SAMPLE_COUNT", 8)
    monkeypatch.setattr(runner, "make_toy_batch", fake_make_toy_batch)
    monkeypatch.setattr(runner, "run_experiment", fake_run_experiment)

    record = runner._run_record(seed=4242, seed_index=2)

    assert calls == [
        {
            "use_torch": runner.USE_TORCH,
            "sample_count": 8,
            "seed": 4242,
            "rho": runner.RHO,
            "run_id": "gaussian-ou-distinction-head-seed-4242",
            "envelope_artifact": runner.JSON_ARTIFACT,
            "report_artifact": runner.REPORT_ARTIFACT,
        }
    ]
    assert record["seed_index"] == 2
    assert record["seed_sequence_position"] == 3
    assert record["run_id"] == "gaussian-ou-distinction-head-seed-4242"
    assert record["config"]["train_count"] == 6
    assert record["config"]["eval_count"] == 2
    assert record["config"]["high_energy_threshold"] == pytest.approx(5.0)
    assert record["split"] == {
        "train_indices": [1, 2, 4, 5, 6, 7],
        "eval_indices": [0, 3],
        "overlap_count": 0,
    }
    assert record["canonical_envelope_projection"] == {
        "run_id": "gaussian-ou-distinction-head-seed-4242",
        "source_spec": {"name": "fixture-source", "sample_count": 8},
        "classifier_spec": {"name": "fixture-classifier"},
        "metrics": {"quality_q": 0.25, "quality_margin": 0.75},
        "artifacts": {
            "envelope": runner.JSON_ARTIFACT,
            "report": runner.REPORT_ARTIFACT,
        },
    }

    x_row = record["per_distinction"]["latent_x_positive"]
    assert x_row["truth"] == {
        "label_positive_rate_train": 0.5,
        "label_positive_rate_eval": 0.5,
        "pair_label_positive_rate": 0.5,
    }
    assert x_row["train"]["accuracy"] == pytest.approx(1.0)
    assert x_row["eval"]["accuracy"] == pytest.approx(1.0)
    assert x_row["stability"] == pytest.approx(0.75)
    assert x_row["generalization_gap"] == pytest.approx(0.0)

    y_row = record["per_distinction"]["latent_y_positive"]
    assert y_row["truth"]["label_positive_rate_eval"] == pytest.approx(0.5)
    assert y_row["eval"]["accuracy"] == pytest.approx(1.0)
    assert y_row["stability"] == pytest.approx(1.0)

    energy_row = record["per_distinction"]["high_energy"]
    assert energy_row["truth"] == {
        "label_positive_rate_train": 0.0,
        "label_positive_rate_eval": 0.0,
        "pair_label_positive_rate": 0.0,
    }
    assert energy_row["eval"]["prediction_positive_rate"] == pytest.approx(0.0)

    assert record["intervention"]["latent_x_positive"]["on_target_flip_rate"] == pytest.approx(1.0)
    assert record["intervention"]["latent_x_positive"]["off_target_flip_rate"] == pytest.approx(0.0)
    assert record["intervention"]["latent_x_positive"]["per_distinction"]["latent_y_positive"] == {
        "prediction_flip_rate": 0.0,
        "post_intervention_truth_positive_rate": 0.5,
        "post_intervention_accuracy": 1.0,
    }
    assert record["intervention"]["latent_y_positive"]["on_target_flip_rate"] == pytest.approx(1.0)
    assert record["intervention"]["high_energy"]["on_target_flip_rate"] == pytest.approx(0.0)
    assert record["intervention"]["high_energy"]["off_target_flip_rate"] == pytest.approx(0.5)


def test_probe_training_interface_learns_separable_fixture():
    x = np.array([[-2.0, 0.0], [-1.0, 0.2], [1.0, -0.1], [2.0, 0.3]], dtype=np.float64)
    y = np.array([0.0, 0.0, 1.0, 1.0], dtype=np.float64)

    probe = runner._fit_probe(x, y, steps=300, lr=0.25)
    metrics = runner._classification_metrics(probe, x, y)

    assert set(probe) == {"weights", "bias", "standardizer"}
    assert metrics["accuracy"] == pytest.approx(1.0)
    assert metrics["bce"] < 0.2
    assert metrics["margin"] > 1.0


def test_metrics_and_payload_aggregate_bce_stability_margin_and_gap(monkeypatch):
    monkeypatch.setattr(runner, "DISTINCTIONS", ("latent_x_positive", "latent_y_positive"))
    records = []
    for index, seed in enumerate((10, 11)):
        records.append(
            {
                "seed": seed,
                "per_distinction": {
                    "latent_x_positive": {
                        "eval": {"accuracy": 0.9 + index * 0.02, "bce": 0.2},
                        "stability": 0.8,
                        "margin": 1.5,
                        "generalization_gap": 0.03,
                    },
                    "latent_y_positive": {
                        "eval": {"accuracy": 0.7 + index * 0.02, "bce": 0.4},
                        "stability": 0.75,
                        "margin": 1.1,
                        "generalization_gap": 0.04,
                    },
                },
                "intervention": {
                    "latent_x_positive": {
                        "on_target_flip_rate": 0.95,
                        "off_target_flip_rate": 0.05,
                    },
                    "latent_y_positive": {
                        "on_target_flip_rate": 0.90,
                        "off_target_flip_rate": 0.10,
                    },
                },
            }
        )

    payload = runner._payload(records)

    assert payload["aggregate"]["record_count"] == 2
    x_stats = payload["aggregate"]["per_distinction"]["latent_x_positive"]
    assert x_stats["eval_accuracy"]["mean"] == pytest.approx(0.91)
    assert x_stats["eval_bce"]["mean"] == pytest.approx(0.2)
    assert x_stats["stability"]["mean"] == pytest.approx(0.8)
    assert x_stats["margin"]["mean"] == pytest.approx(1.5)
    assert x_stats["generalization_gap"]["mean"] == pytest.approx(0.03)
    assert x_stats["intervention_separation"]["mean"] == pytest.approx(0.90)


def test_intervention_flips_target_and_bounds_off_target_fixture():
    z = np.array([[1.0, 2.0], [-1.5, 1.0], [2.0, -0.5]], dtype=np.float64)
    z_pair = np.array([[0.2, 0.1], [0.1, 0.1], [0.3, -0.2]], dtype=np.float64)

    flipped_x = runner._intervene("latent_x_positive", z, z_pair)
    flipped_y = runner._intervene("latent_y_positive", z, z_pair)
    paired = runner._intervene("high_energy", z, z_pair)

    assert runner._label_truth("latent_x_positive", flipped_x, high_energy_threshold=1.0).tolist() == [
        0.0,
        1.0,
        0.0,
    ]
    assert runner._label_truth("latent_y_positive", flipped_x, high_energy_threshold=1.0).tolist() == [
        1.0,
        1.0,
        0.0,
    ]
    assert runner._label_truth("latent_y_positive", flipped_y, high_energy_threshold=1.0).tolist() == [
        0.0,
        0.0,
        1.0,
    ]
    assert np.allclose(paired, z_pair)


def test_payload_contains_boundary_source_and_negative_result_fields():
    payload = runner._payload(
        [
            {
                "seed": 10,
                "per_distinction": {
                    name: {
                        "eval": {"accuracy": 1.0, "bce": 0.01},
                        "stability": 0.9,
                        "margin": 4.0,
                        "generalization_gap": 0.0,
                    }
                    for name in runner.DISTINCTIONS
                },
                "intervention": {
                    name: {"on_target_flip_rate": 1.0, "off_target_flip_rate": 0.0}
                    for name in runner.DISTINCTIONS
                },
            }
        ]
    )
    report = runner._render_report(payload)

    assert payload["source_artifacts"]["generation_script"] == (
        "scripts/run_gaussian_ou_distinction_head.py"
    )
    assert payload["source_artifacts"]["canonical_runner"].endswith("run_experiment")
    assert "applicability_boundary" in payload
    assert "negative_result_note" in payload
    assert "deterministic fallback projection" in payload["applicability_boundary"][
        "representation_boundary"
    ]
    assert "## Applicability Boundary" in report
    assert "## Intervention Metrics" in report
    assert "## Negative Result Note" in report


def test_main_writes_json_and_markdown(monkeypatch, tmp_path):
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    monkeypatch.setattr(
        runner,
        "_records",
        lambda: [
            {
                "seed": 10,
                "per_distinction": {
                    name: {
                        "eval": {"accuracy": 1.0, "bce": 0.01},
                        "stability": 0.9,
                        "margin": 4.0,
                        "generalization_gap": 0.0,
                    }
                    for name in runner.DISTINCTIONS
                },
                "intervention": {
                    name: {"on_target_flip_rate": 1.0, "off_target_flip_rate": 0.0}
                    for name in runner.DISTINCTIONS
                },
            }
        ],
    )

    runner.main()

    payload = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")

    assert payload["artifact"] == runner.JSON_ARTIFACT
    assert payload["aggregate"]["record_count"] == 1
    assert "# Gaussian-OU Distinction-Head Experiment" in report
    assert "Total records: `1`" in report


def test_non_finite_input_fails_closed():
    bad = np.array([[1.0, 0.0], [math_nan(), 1.0]], dtype=np.float64)

    with pytest.raises(ValueError, match="non-finite"):
        runner._label_truth("latent_x_positive", bad, high_energy_threshold=1.0)


def test_does_not_mutate_schema_or_package_exports():
    import bedc_quality_lab
    from bedc_quality_lab.schema import SCHEMA_ID

    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert hasattr(bedc_quality_lab, "QualityEvidenceEnvelope")


def math_nan():
    return float("nan")

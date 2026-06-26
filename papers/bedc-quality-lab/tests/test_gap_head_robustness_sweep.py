import json

import numpy as np
import pytest

from scripts.experiment_stats import metric_stats
from scripts import run_gap_head_robustness_sweep as runner
from scripts import run_gap_ledger_head_on_h as producer


def _stat(values):
    return metric_stats(values)


def _metric_arm(auroc, unlogged):
    return {
        "failure_detection_auroc": {"value": float(auroc)},
        "ece": {"value": 0.1},
        "unlogged_error_rate": float(unlogged),
        "critical_unlogged_error_rate": float(unlogged),
        "prediction_error_rate": 0.4,
        "primary_gap_sound": {
            "tau": producer.PRIMARY_TAU,
            "epsilon": producer.PRIMARY_EPSILON,
            "low_gap_implies_error_within_epsilon": 0.9,
            "error_above_epsilon_implies_gap_at_least_tau": 0.8,
            "low_gap_count": 1,
            "failure_count": 1,
        },
        "loss": {"value": 0.2},
    }


def _source_payload_fixture():
    records = []
    for seed in (1, 2, 3, 4):
        records.append(
            {
                "seed": seed,
                "arms": {
                    "vanilla": _metric_arm(0.5, 0.5),
                    "learned_gap_head_on_h": _metric_arm(0.86, 0.1),
                    producer.MATCHED_RANDOM_ARM: _metric_arm(0.51, 0.49),
                },
                "comparison": {
                    "unlogged_error_rate_delta_learned_minus_vanilla": -0.4,
                    "critical_unlogged_error_rate_delta_learned_minus_vanilla": -0.4,
                    "failure_detection_auroc_delta_learned_minus_vanilla": 0.36,
                    "unlogged_error_rate_delta_matched_random_minus_vanilla": -0.01,
                    "critical_unlogged_error_rate_delta_matched_random_minus_vanilla": -0.01,
                    "failure_detection_auroc_delta_matched_random_minus_vanilla": 0.01,
                },
            }
        )
    aggregate = {
        "record_count": len(records),
        "by_arm": {
            "vanilla": {
                "failure_detection_auroc": _stat([0.5] * 4),
                "unlogged_error_rate": _stat([0.5] * 4),
                "critical_unlogged_error_rate": _stat([0.5] * 4),
            },
            "learned_gap_head_on_h": {
                "failure_detection_auroc": _stat([0.86] * 4),
                "unlogged_error_rate": _stat([0.1] * 4),
                "critical_unlogged_error_rate": _stat([0.1] * 4),
            },
            producer.MATCHED_RANDOM_ARM: {
                "failure_detection_auroc": _stat([0.51] * 4),
                "unlogged_error_rate": _stat([0.49] * 4),
                "critical_unlogged_error_rate": _stat([0.49] * 4),
            },
        },
        "comparison": {},
    }
    return {
        "config": {
            "sample_count": 12,
            "seed_count": 4,
            "tau_grid": list(producer.TAU_GRID),
            "epsilon_grid": list(producer.EPSILON_GRID),
            "primary_tau": producer.PRIMARY_TAU,
            "primary_epsilon": producer.PRIMARY_EPSILON,
        },
        "records": records,
        "aggregate": aggregate,
        "treatment_verdict": {"positive": True},
        "control_verdict": {"positive": False},
        "forbidden_column_audit": {
            "status": "pass",
            "feature_columns": producer._feature_columns(2),
            "forbidden_inference_columns": list(producer.FORBIDDEN_INFERENCE_COLUMNS),
            "forbidden_present": [],
        },
    }


def _ablation_fixture():
    full = {
        "failure_detection_auroc": _stat([0.86, 0.86, 0.86, 0.86]),
        "unlogged_error_reduction": _stat([0.40, 0.40, 0.40, 0.40]),
    }
    h_only = {
        "failure_detection_auroc": _stat([0.85, 0.85, 0.85, 0.85]),
        "unlogged_error_reduction": _stat([0.38, 0.38, 0.38, 0.38]),
    }
    weak = {
        "failure_detection_auroc": _stat([0.55, 0.55, 0.55, 0.55]),
        "unlogged_error_reduction": _stat([0.02, 0.02, 0.02, 0.02]),
    }
    by_family = {}
    for family, learned in {
        "full": full,
        "h_only": h_only,
        "probe_only": weak,
        "no_quality": full,
        "quality_only": weak,
    }.items():
        by_family[family] = {
            "record_count": 4,
            "feature_roots": list(runner.FEATURE_FAMILIES[family]),
            "feature_column_count": len(runner.FEATURE_FAMILIES[family]),
            "forbidden_feature_audit": {"status": "pass", "forbidden_present": []},
            "learned": learned | {"unlogged_error_rate": _stat([0.1] * 4)},
            "matched_random": {
                "failure_detection_auroc": _stat([0.51] * 4),
                "unlogged_error_rate": _stat([0.49] * 4),
                "unlogged_error_reduction": _stat([0.01] * 4),
            },
            "learned_minus_matched_random_auroc": _stat([0.35] * 4),
        }
    return {
        "status": "complete",
        "by_family": by_family,
    }


def _stability_fixture():
    return {
        "status": "complete",
        "owner": "scripts/run_gap_head_discovery_stability.py",
        "json_artifact": "reports/gap_head_discovery_stability.json",
        "report_artifact": "reports/gap_head_discovery_stability.md",
        "final_verdict": "robust_positive",
        "grid": {"kind": "fixture", "sample_counts": [12], "seeds_per_sample_count": 4},
        "aggregate": {
            "cell_count": 4,
            "valid_cell_count": 4,
            "invalid_cell_count": 0,
            "positive_cell_count": 4,
            "sample_count_groups": [],
        },
        "predicate_boundary": runner._owner_pointers()["a3_seed_expansion"],
    }


def _walk_keys(value):
    if isinstance(value, dict):
        for key, cell in value.items():
            yield key
            yield from _walk_keys(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _walk_keys(cell)


def test_owner_pointers_keep_thin_runner_boundary():
    pointers = runner._owner_pointers()

    assert pointers["a1_threshold_sweep"]["owner"] == "scripts/run_gap_ledger_head_on_h.py"
    assert pointers["a2_feature_ablation"]["metric_helper"].endswith("::_metrics_for_arm")
    assert pointers["a3_seed_expansion"]["owner"] == "scripts/run_gap_head_discovery_stability.py"
    assert {row["name"] for row in pointers["a4_distribution_transfer"]} == {
        "nongaussian-distribution-sweep",
        "anisotropic-ou-sweep",
        "mixing-family-sweep",
        "gaussian-ou-gap-ledger-shift-robustness",
    }
    assert "gap_head_sweep_protocol" not in json.dumps(pointers)


def test_ablation_family_masks_and_forbidden_audit_reject_leak():
    columns = producer._feature_columns(2)

    assert runner._family_indices(columns, "h_only") == [0, 1]
    assert runner._family_indices(columns, "quality_only") == [11, 12, 13, 14]
    runner._assert_no_forbidden_features(["h:0", "score:latent_x_positive"])
    with pytest.raises(ValueError, match="forbidden inference column"):
        runner._assert_no_forbidden_features(["h:0", "z"])


def test_ablation_record_reuses_producer_metric_helpers(monkeypatch):
    surface = {
        "feature_columns": producer._feature_columns(2),
        "features": np.arange(90, dtype=np.float64).reshape(6, 15),
        "gap_labels": np.array(
            [
                [1, 0, 0, 0],
                [0, 1, 0, 0],
                [1, 0, 1, 0],
                [0, 0, 0, 1],
                [1, 0, 0, 1],
                [0, 1, 0, 0],
            ],
            dtype=np.float64,
        ),
        "prediction_error": np.array([1, 0, 1, 0, 1, 0], dtype=np.float64),
        "train_idx": np.array([0, 1, 2, 3], dtype=np.int64),
        "eval_idx": np.array([4, 5], dtype=np.int64),
    }
    calls = {"fit": 0, "predict": 0}

    def fake_fit(features, labels):
        calls["fit"] += 1
        assert features.shape == (4, 2)
        assert labels.shape == (4, 4)
        return {"head": calls["fit"]}

    def fake_predict(heads, features):
        calls["predict"] += 1
        assert features.shape == (2, 2)
        return np.array([[0.9, 0.1, 0.2, 0.3], [0.1, 0.8, 0.2, 0.7]])

    monkeypatch.setattr(producer, "_fit_gap_head", fake_fit)
    monkeypatch.setattr(producer, "_predict_gap_head", fake_predict)

    record = runner._ablation_record(seed=1, seed_index=0, surface=surface, family="h_only")

    assert calls == {"fit": 2, "predict": 2}
    assert record["feature_family"] == "h_only"
    assert record["feature_column_count"] == 2
    assert record["forbidden_feature_audit"]["status"] == "pass"
    assert set(record["arms"]) == {"vanilla", "learned", "matched_random"}
    assert "failure_detection_auroc_delta_learned_minus_matched_random" in record["comparison"]


def test_acceptance_gates_pass_and_mark_h_boundary_classifier():
    a1 = runner._a1_threshold_summary(_source_payload_fixture())
    ablation = _ablation_fixture()
    leak = runner._a5_no_leak_audit(_source_payload_fixture(), ablation)

    result = runner._evaluate_acceptance_gates(a1=a1, ablation=ablation, leak_audit=leak)

    assert result["status"] == "pass"
    assert result["gates"]["A-HG1"]["status"] == "pass"
    assert result["gates"]["A-HG2"]["status"] == "pass"
    assert result["gates"]["A-HG3"]["status"] == "pass"
    assert result["gates"]["A-HG4"]["status"] == "pass"
    assert result["gates"]["A-HG5"]["h_only_sufficient"] is True
    assert result["claim_scope_label"] == "h_boundary_gap_classifier"


def test_transfer_summary_is_pointer_only(monkeypatch, tmp_path):
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    path = tmp_path / "reports/canonical/nongaussian-distribution-sweep.json"
    path.parent.mkdir(parents=True)
    path.write_text(
        json.dumps(
            {
                "main_claim_status": "observed-debt-pipeline-only",
                "records": [{"raw": "not copied"}],
            }
        ),
        encoding="utf-8",
    )

    summary = runner._transfer_pointer_summary()
    row = next(cell for cell in summary["surfaces"] if cell["name"] == "nongaussian-distribution-sweep")

    assert row["status"] == "available"
    assert row["pointer_value_summary"] == "observed-debt-pipeline-only"
    assert "records" not in json.dumps(row)


def test_payload_and_report_are_pointer_only_and_have_no_schema_report_kind(tmp_path, monkeypatch):
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    source = _source_payload_fixture()
    ablation = _ablation_fixture()
    payload = runner._payload(
        source_payload=source,
        ablation=ablation,
        stability_summary=_stability_fixture(),
        transfer_summary={"status": "complete", "surfaces": []},
        elapsed_seconds=1.25,
    )

    runner._write_payload(payload)
    written = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    report = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")

    keys = set(_walk_keys(written))
    assert "report_schema_id" not in keys
    assert "report_kind" not in keys
    assert "records" not in written
    assert written["final_status"] == "pass"
    assert written["final_claim_scope"] == "h_boundary_gap_classifier"
    assert "# Gap-Head Robustness Sweep" in report
    assert "A-HG Gates" in report

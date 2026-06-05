from __future__ import annotations

import json
from copy import deepcopy
from types import SimpleNamespace

import pytest

from bedc_quality_lab.sigreg_mini_grid import (
    DEFAULT_ALIGNMENT_LAMBDAS,
    DEFAULT_MIXINGS,
    DEFAULT_RHOS,
    DEFAULT_SEEDS,
    FORBIDDEN_SUMMARY_ALIASES,
    SIGRegMiniGridProjection,
    default_grid,
)
from scripts import run_canonical_reports as canonical
from scripts import run_discovery_map as discovery_map
from scripts import run_sigreg_mini_grid as runner


REQUIRED_SUMMARY_KEYS = {
    "schema_id",
    "artifact_id",
    "generated_at",
    "run_id",
    "producer",
    "projector",
    "run_artifacts",
    "source_artifacts",
    "config",
    "grid",
    "metric_keys",
    "metric_separation",
    "lambda_summary",
    "rho_summary",
    "mixing_summary",
    "best_cell",
    "trend_summary",
    "tradeoff_ledger",
    "c3_hardgates",
    "hardgate",
    "failed_gate",
    "discovery_map_signal",
    "claim_capsule_ref",
    "claim_capsule_status",
    "positive_claim",
    "not_claimed",
    "what_was_learned",
    "revocation_rows",
    "forbidden_claim_term_audit",
}


def _metric_record(alignment_lambda: float, rho: float, mixing: str, seed: int) -> dict[str, float | int | str]:
    lambda_rank = DEFAULT_ALIGNMENT_LAMBDAS.index(float(alignment_lambda))
    rho_rank = DEFAULT_RHOS.index(float(rho))
    mixing_penalty = 0.0 if mixing == "spiral" else 0.02
    seed_jitter = DEFAULT_SEEDS.index(int(seed)) * 1.0e-5
    return {
        "alignment_lambda": float(alignment_lambda),
        "rho": float(rho),
        "mixing": str(mixing),
        "seed": int(seed),
        "alignment_loss": 0.10 + 0.05 * lambda_rank,
        "sigreg_sliced_cf": 0.50 - 0.04 * lambda_rank,
        "covariance_proxy": 0.20 + 0.01 * rho_rank + 0.002 * lambda_rank,
        "linear_identifiability_r2": 0.40 + 0.10 * rho_rank,
        "actual_recovery_mse": 0.40 - 0.03 * rho_rank + 0.01 * lambda_rank,
        "theorem3_bound_mse": 1.0 + 0.01 * lambda_rank,
        "collapse_rate": 0.02 + 0.03 * lambda_rank,
        "quality_q": 1.0 + 0.12 * rho_rank - 0.08 * lambda_rank - mixing_penalty - seed_jitter,
    }


def _supported_records() -> list[dict[str, float | int | str]]:
    return [
        _metric_record(float(cell["alignment_lambda"]), float(cell["rho"]), str(cell["mixing"]), int(cell["seed"]))
        for cell in default_grid()
    ]


def _project(records=None, **config):
    run_id = config.pop("run_id", "fixture-sigreg-mini-grid")
    artifacts = {
        "summary": f"reports/runs/{run_id}/summary.json",
        "claim_capsule": f"reports/runs/{run_id}/claim_capsule.json",
        "raw_metrics": f"reports/runs/{run_id}/raw_metrics.jsonl",
        "report": f"reports/runs/{run_id}/report.md",
    }
    full_config = {
        "run_id": run_id,
        "alignment_lambdas": list(DEFAULT_ALIGNMENT_LAMBDAS),
        "rhos": list(DEFAULT_RHOS),
        "mixings": list(DEFAULT_MIXINGS),
        "seeds": list(DEFAULT_SEEDS),
        **config,
    }
    return SIGRegMiniGridProjection(
        config=full_config,
        records=_supported_records() if records is None else records,
        generated_at="fixture-time",
        run_artifacts=artifacts,
    ).project()


def _recursive_keys(value):
    if isinstance(value, dict):
        keys = set(value)
        for item in value.values():
            keys.update(_recursive_keys(item))
        return keys
    if isinstance(value, list):
        keys = set()
        for item in value:
            keys.update(_recursive_keys(item))
        return keys
    return set()


def _recursive_pointer_fields(value, path="$"):
    if isinstance(value, dict):
        found = []
        for key, item in value.items():
            child_path = f"{path}.{key}"
            if isinstance(key, str) and key.endswith("_pointer"):
                found.append((child_path, item))
            found.extend(_recursive_pointer_fields(item, child_path))
        return found
    if isinstance(value, list):
        found = []
        for index, item in enumerate(value):
            found.extend(_recursive_pointer_fields(item, f"{path}.{index}"))
        return found
    return []


def test_run_single_arm_forwards_backend_arguments_and_derives_probe_metrics(monkeypatch):
    backend_calls = []
    probe_inits = []
    probe_scores = []

    def fake_run_experiment(**kwargs):
        backend_calls.append(kwargs)
        return SimpleNamespace(
            run_id="sigreg-backend-arm",
            metrics={
                "alignment_loss_mse": 0.31,
                "covariance_trace": 0.20,
                "covariance_deviation": 0.07,
                "linear_identifiability_r2": 0.80,
                "quality_q": 0.44,
                "actual_recovery_mse": 0.12,
                "theorem3_bound_mse": 0.55,
            },
        )

    class FakeProbe:
        def __init__(self, *, directions, frequencies, guard_thresholds):
            probe_inits.append(
                {
                    "directions": directions,
                    "frequencies": frequencies,
                    "guard_thresholds": guard_thresholds,
                }
            )

        def score(self, h, *, seed, directions, frequencies):
            probe_scores.append(
                {
                    "h": h,
                    "seed": seed,
                    "directions": directions,
                    "frequencies": frequencies,
                }
            )
            return {"sigreg_penalty": 0.123, "cov_to_identity_fro": 0.456}

    monkeypatch.setattr(runner.run_gaussian_ou_lejepa, "run_experiment", fake_run_experiment)
    monkeypatch.setattr(runner, "SlicedCFGaussianityProbe", FakeProbe)

    row = runner.run_single_arm(
        alignment_lambda=0.005,
        rho=0.95,
        mixing="parabolic",
        seed=37,
        sample_count=128,
        directions=6,
        frequencies=(0.5, 1.5),
        use_torch=True,
    )

    assert len(backend_calls) == 1
    assert backend_calls[0]["alignment_lambda"] == pytest.approx(0.005)
    assert backend_calls[0]["mixing"] == "parabolic_shear"
    assert backend_calls[0]["rho"] == pytest.approx(0.95)
    assert backend_calls[0]["sample_count"] == 128
    assert backend_calls[0]["seed"] == 37
    assert backend_calls[0]["use_torch"] is True
    assert len(probe_inits) == 1
    assert probe_inits[0]["directions"] == 6
    assert tuple(probe_inits[0]["frequencies"]) == (0.5, 1.5)
    assert len(probe_scores) == 1
    assert probe_scores[0]["seed"] == 37
    assert probe_scores[0]["directions"] == 2
    assert tuple(probe_scores[0]["frequencies"]) == (0.5, 1.5)
    assert probe_scores[0]["h"].tolist() == [[0.80, 0.44], [0.12, 0.55], [0.31, 0.07]]
    assert row["alignment_lambda"] == pytest.approx(0.005)
    assert row["rho"] == pytest.approx(0.95)
    assert row["mixing"] == "parabolic"
    assert row["source_mixing"] == "parabolic_shear"
    assert row["seed"] == 37
    assert row["sample_count"] == 128
    assert row["alignment_loss"] == pytest.approx(0.31)
    assert row["sigreg_sliced_cf"] == pytest.approx(0.123)
    assert row["covariance_proxy"] == pytest.approx(0.456)
    assert row["linear_identifiability_r2"] == pytest.approx(0.80)
    assert row["actual_recovery_mse"] == pytest.approx(0.12)
    assert row["theorem3_bound_mse"] == pytest.approx(0.55)
    assert row["collapse_rate"] == pytest.approx(0.40)
    assert row["quality_q"] == pytest.approx(0.44)
    assert row["source_run_id"] == "sigreg-backend-arm"


def test_sigreg_mini_grid_required_and_forbidden_keys():
    projected = _project()
    summary = projected["summary_payload"]
    capsule = projected["claim_capsule_payload"]

    assert REQUIRED_SUMMARY_KEYS <= set(summary)
    assert "metric_separation" in summary
    assert "discovery_map_signal" in summary
    assert all(alias not in summary for alias in FORBIDDEN_SUMMARY_ALIASES)
    assert "result" not in summary
    assert "result" not in capsule
    assert summary["not_claimed"] == capsule["not_claimed"]
    assert summary["claim_capsule_ref"] == summary["run_artifacts"]["claim_capsule"]
    assert summary["forbidden_claim_term_audit"] == capsule["forbidden_claim_term_audit"]


def test_sigreg_mini_grid_no_terminal_verdict_recursive():
    projected = _project()

    assert "terminal_verdict" not in _recursive_keys(projected)


def test_sigreg_mini_grid_metric_separation_gate():
    projected = _project()
    summary = projected["summary_payload"]

    assert summary["metric_separation"]["status"] == "pass"
    assert summary["metric_separation"]["sigreg_metric"]["row_key"] == "sigreg_sliced_cf"
    assert summary["metric_separation"]["covariance_proxy_metric"]["row_key"] == "covariance_proxy"
    assert summary["c3_hardgates"]["C3-HG1"]["status"] == "pass"

    missing = [dict(row) for row in _supported_records()]
    for row in missing:
        row.pop("covariance_proxy")
    missing_summary = _project(missing)["summary_payload"]
    assert missing_summary["metric_separation"]["status"] == "fail"
    assert missing_summary["c3_hardgates"]["C3-HG1"]["status"] == "fail"

    partial_missing = [dict(row) for row in _supported_records()]
    partial_missing[0].pop("covariance_proxy")
    partial_missing_summary = _project(partial_missing)["summary_payload"]
    assert partial_missing_summary["metric_separation"]["status"] == "fail"
    assert partial_missing_summary["c3_hardgates"]["C3-HG1"]["status"] == "fail"
    assert partial_missing_summary["discovery_map_signal"]["level_candidate"] == "DN"
    assert partial_missing_summary["discovery_map_signal"]["status"] == "negative"

    partial_missing_sigreg = [dict(row) for row in _supported_records()]
    partial_missing_sigreg[0].pop("sigreg_sliced_cf")
    partial_missing_sigreg_summary = _project(partial_missing_sigreg)["summary_payload"]
    assert partial_missing_sigreg_summary["metric_separation"]["status"] == "fail"
    assert partial_missing_sigreg_summary["c3_hardgates"]["C3-HG1"]["status"] == "fail"
    assert partial_missing_sigreg_summary["discovery_map_signal"]["level_candidate"] == "DN"
    assert partial_missing_sigreg_summary["discovery_map_signal"]["status"] == "negative"

    non_finite = [dict(row) for row in _supported_records()]
    for row in non_finite:
        row["sigreg_sliced_cf"] = float("nan")
    non_finite_summary = _project(non_finite)["summary_payload"]
    assert non_finite_summary["metric_separation"]["status"] == "fail"

    partial_non_finite = [dict(row) for row in _supported_records()]
    partial_non_finite[0]["sigreg_sliced_cf"] = float("nan")
    partial_non_finite_summary = _project(partial_non_finite)["summary_payload"]
    assert partial_non_finite_summary["metric_separation"]["status"] == "fail"
    assert partial_non_finite_summary["c3_hardgates"]["C3-HG1"]["status"] == "fail"
    assert partial_non_finite_summary["discovery_map_signal"]["level_candidate"] == "DN"
    assert partial_non_finite_summary["discovery_map_signal"]["status"] == "negative"

    partial_non_finite_cov = [dict(row) for row in _supported_records()]
    partial_non_finite_cov[0]["covariance_proxy"] = float("nan")
    partial_non_finite_cov_summary = _project(partial_non_finite_cov)["summary_payload"]
    assert partial_non_finite_cov_summary["metric_separation"]["status"] == "fail"
    assert partial_non_finite_cov_summary["c3_hardgates"]["C3-HG1"]["status"] == "fail"
    assert partial_non_finite_cov_summary["discovery_map_signal"]["level_candidate"] == "DN"
    assert partial_non_finite_cov_summary["discovery_map_signal"]["status"] == "negative"

    collapsed = [dict(row) for row in _supported_records()]
    for row in collapsed:
        row["covariance_proxy"] = row["sigreg_sliced_cf"]
    collapsed_summary = _project(collapsed)["summary_payload"]
    assert collapsed_summary["metric_separation"]["collapsed"] is True
    assert collapsed_summary["c3_hardgates"]["C3-HG1"]["status"] == "fail"


def test_sigreg_mini_grid_level_mapping():
    d2 = _project()["summary_payload"]
    assert d2["discovery_map_signal"]["level_candidate"] == "D2"
    assert d2["discovery_map_signal"]["status"] == "d2-candidate"
    assert d2["discovery_map_signal"]["failed_gate"] is None

    d1_records = deepcopy(_supported_records())
    for row in d1_records:
        row["linear_identifiability_r2"] = 0.5
    d1 = _project(d1_records)["summary_payload"]
    assert d1["c3_hardgates"]["C3-HG3"]["status"] == "fail"
    assert d1["discovery_map_signal"]["level_candidate"] == "D1"
    assert d1["discovery_map_signal"]["status"] == "d1-grid-evidence"
    assert d1["discovery_map_signal"]["failed_gate"] == "C3-HG3"

    for gate in ("C3-HG1", "C3-HG2", "C3-HG4"):
        records = deepcopy(_supported_records())
        config = {}
        if gate == "C3-HG1":
            for row in records:
                row.pop("covariance_proxy")
        elif gate == "C3-HG2":
            for row in records:
                row["alignment_loss"] = 0.1
        else:
            config["full_lejepa_claim"] = True
        summary = _project(records, **config)["summary_payload"]
        assert summary["c3_hardgates"][gate]["status"] == "fail"
        assert summary["discovery_map_signal"]["level_candidate"] == "DN"
        assert summary["discovery_map_signal"]["failed_gate"] == gate


def test_sigreg_mini_grid_current_lab_projection():
    spec = canonical._specs_by_name()["sigreg-mini-grid"]
    d2 = _project()["summary_payload"]
    d2_row = discovery_map.discovery_row(spec, d2)
    d2_projected = discovery_map.projection_payload(spec, d2)

    assert d2_projected["main_verdict"]["surface_delta_count"] == 1
    assert d2_projected["main_verdict"]["shift_information"] == 1
    assert d2_projected["main_verdict"]["sigreg_mini_grid"]["level_candidate"] == "D2"
    assert d2_projected["evidence_basis"]["sigreg_mini_grid"] is True
    assert d2_row["discovery_level"] == "D2"
    assert d2_row["audit_status"] == "valid"

    d1_records = deepcopy(_supported_records())
    for row in d1_records:
        row["linear_identifiability_r2"] = 0.5
    d1 = _project(d1_records)["summary_payload"]
    d1_row = discovery_map.discovery_row(spec, d1)
    d1_projected = discovery_map.projection_payload(spec, d1)
    assert d1_projected["main_verdict"]["deltas"]["debt_delta"] == pytest.approx(-1.0)
    assert d1_projected["claim_gate"]["training_audit_improvement_tradeoff"] is True
    assert d1_row["discovery_level"] == "D1"
    assert d1_row["debt_row_pointer"] == "$.tradeoff_ledger.rows.0"
    assert d1_row["audit_status"] == "valid"

    dn_records = deepcopy(_supported_records())
    for row in dn_records:
        row.pop("covariance_proxy")
    dn = _project(dn_records)["summary_payload"]
    dn_row = discovery_map.discovery_row(spec, dn)
    dn_projected = discovery_map.projection_payload(spec, dn)
    assert dn_projected["verdict"] == "rejected"
    assert dn_projected["main_verdict"]["sigreg_mini_grid"]["level_candidate"] == "DN"
    assert dn_row["discovery_level"] == "DN"
    assert dn_row["failed_gate"] == "$.c3_hardgates.C3-HG1.status"
    assert discovery_map.pointer_value(dn, dn_row["failed_gate"]) == "fail"
    assert dn_row["audit_status"] == "valid"


def test_sigreg_mini_grid_canonical_spec_and_producer(tmp_path):
    spec = canonical._specs_by_name()["sigreg-mini-grid"]

    assert spec.command == ("python3", "scripts/run_sigreg_mini_grid.py")
    assert spec.json_artifact == "reports/canonical/sigreg-mini-grid.json"
    assert spec.markdown_artifact == "reports/canonical/sigreg-mini-grid.md"
    assert "metric_separation" in spec.required_json_keys
    assert "discovery_map_signal" in spec.required_json_keys
    assert "result" not in spec.required_json_keys
    assert "terminal_verdict" not in spec.required_json_keys

    projection = runner.build_projection(run_id="fixture-canonical", generated_at="fixture-time")
    runner.write_artifacts(projection, root=tmp_path, json_artifact=spec.json_artifact, report_artifact=spec.markdown_artifact)

    canonical_summary = json.loads((tmp_path / spec.json_artifact).read_text(encoding="utf-8"))
    canonical_markdown = (tmp_path / spec.markdown_artifact).read_text(encoding="utf-8")
    capsule = json.loads((tmp_path / canonical_summary["run_artifacts"]["claim_capsule"]).read_text(encoding="utf-8"))

    assert REQUIRED_SUMMARY_KEYS <= set(canonical_summary)
    assert "SIGReg Mini-Grid" in canonical_markdown
    assert "claim_capsule" not in canonical_summary
    assert canonical_summary["claim_capsule_ref"] == canonical_summary["run_artifacts"]["claim_capsule"]
    assert canonical_summary["not_claimed"] == capsule["not_claimed"]
    assert "terminal_verdict" not in _recursive_keys({"summary": canonical_summary, "capsule": capsule})
    dangling = [
        (path, pointer)
        for path, pointer in _recursive_pointer_fields(canonical_summary)
        if pointer is not None and discovery_map.pointer_value(canonical_summary, pointer) is None
    ]
    assert dangling == []

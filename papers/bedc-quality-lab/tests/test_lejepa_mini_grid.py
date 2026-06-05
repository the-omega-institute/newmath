from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from bedc_quality_lab import claim_terms
from bedc_quality_lab.discovery_compiler import capsule
from bedc_quality_lab.lejepa_mini_grid import (
    DEFAULT_ALIGNMENT_LAMBDAS,
    DEFAULT_MIXINGS,
    DEFAULT_RHOS,
    DEFAULT_SEEDS,
    LeJEPAMiniGridProjection,
    default_grid,
)
from scripts import run_canonical_reports as canonical
from scripts import run_lejepa_mini_grid as runner


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
        "covariance_proxy": 0.20 + 0.01 * rho_rank,
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
    run_id = config.pop("run_id", "fixture-d2")
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
    return LeJEPAMiniGridProjection(
        config=full_config,
        records=_supported_records() if records is None else records,
        generated_at="fixture-time",
        run_artifacts=artifacts,
    ).project()


def _fake_single_arm(**kwargs):
    return _metric_record(
        float(kwargs["alignment_lambda"]),
        float(kwargs["rho"]),
        str(kwargs["mixing"]),
        int(kwargs["seed"]),
    )


def test_run_single_arm_forwards_backend_arguments_and_derives_probe_metrics(monkeypatch):
    backend_calls = []
    probe_inits = []
    probe_scores = []

    def fake_run_experiment(**kwargs):
        backend_calls.append(kwargs)
        return SimpleNamespace(
            run_id="backend-arm",
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
            return {"sigreg_penalty": 0.123}

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
    assert row["covariance_proxy"] == pytest.approx(0.07)
    assert row["linear_identifiability_r2"] == pytest.approx(0.80)
    assert row["actual_recovery_mse"] == pytest.approx(0.12)
    assert row["theorem3_bound_mse"] == pytest.approx(0.55)
    assert row["collapse_rate"] == pytest.approx(0.40)
    assert row["quality_q"] == pytest.approx(0.44)
    assert row["source_run_id"] == "backend-arm"


def test_default_grid_enumerates_300_cells_and_writes_four_run_artifacts(monkeypatch, tmp_path):
    calls = []

    def fake_single_arm(**kwargs):
        calls.append(kwargs)
        return _fake_single_arm(**kwargs)

    monkeypatch.setattr(runner, "run_single_arm", fake_single_arm)
    projection = runner.build_projection(run_id="fixture-grid", generated_at="fixture-time")

    assert len(calls) == 300
    assert projection["summary_payload"]["grid"]["record_count"] == 300
    assert projection["summary_payload"]["grid"]["expected_record_count"] == 300

    runner.write_artifacts(projection, root=tmp_path)
    run_dir = tmp_path / "reports/runs/fixture-grid"
    written = sorted(path.name for path in run_dir.iterdir())
    assert written == ["claim_capsule.json", "raw_metrics.jsonl", "report.md", "summary.json"]
    summary = json.loads((run_dir / "summary.json").read_text(encoding="utf-8"))
    capsule_payload = json.loads((run_dir / "claim_capsule.json").read_text(encoding="utf-8"))
    assert summary["claim_capsule"] == capsule_payload
    assert len((run_dir / "raw_metrics.jsonl").read_text(encoding="utf-8").splitlines()) == 300


def test_projector_marks_low_lambda_high_rho_best_as_theory_consistent_when_supported():
    projected = _project()
    summary = projected["summary_payload"]

    assert summary["result"]["status"] == "d2-theory-consistent"
    assert summary["d2_hardgates"]["D2-HG2"]["status"] == "pass"
    assert summary["best_cell"]["alignment_lambda"] == pytest.approx(DEFAULT_ALIGNMENT_LAMBDAS[0])
    assert summary["best_cell"]["rho"] == pytest.approx(DEFAULT_RHOS[-1])
    assert summary["claim_capsule"]["claim_status"] == "d2-pointer-accepted"


def test_projector_records_high_lambda_collapse_without_positive_claim():
    records = _supported_records()
    for row in records:
        if row["alignment_lambda"] == DEFAULT_ALIGNMENT_LAMBDAS[-1] and row["rho"] == DEFAULT_RHOS[-1]:
            row["quality_q"] = 10.0
            row["collapse_rate"] = 0.95

    projected = _project(records)
    summary = projected["summary_payload"]

    assert summary["d2_hardgates"]["D2-HG2"]["status"] == "fail"
    assert summary["failed_gate"] == "D2-HG2"
    assert summary["claim_capsule"]["claim_status"] == "failed"
    assert summary["claim_capsule"]["positive_claim"]["level"] == "DN"
    assert summary["lambda_summary"]["by_alignment_lambda"][str(DEFAULT_ALIGNMENT_LAMBDAS[-1])]["collapse_rate_mean"] > 0.10


def test_non_gaussian_mixing_downgrades_broad_claim():
    projected = _project()
    summary = projected["summary_payload"]

    assert summary["mixing_summary"]["non_gaussian_broad_claim"] == "downgraded"
    assert summary["u_hardgates"]["U-HG3"]["status"] == "pass"
    assert "broad non-Gaussian mixing generalization" in summary["not_claimed"]


def test_capsule_run_local_alias_is_semantic_and_canonical_schema_stays_unversioned():
    assert capsule.CLAIM_CAPSULE_SCHEMA_ID == "bedc.quality.claim_capsule"
    assert capsule.CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID == "bedc.quality.claim_capsule.run_local"

    payload = {
        "schema_id": capsule.CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID,
        "claim_id": "fixture",
        "report": "reports/runs/fixture/report.md",
        "source": "reports/runs/fixture/summary.json",
        "source_pointer": "$.result",
        "status": "complete",
    }
    normalized = capsule.normalize_claim_capsule_schema_id(payload)
    loaded = capsule.ClaimCapsule.from_payload(payload)

    assert normalized["schema_id"] == capsule.CLAIM_CAPSULE_SCHEMA_ID
    assert normalized["run_local_schema_id"] == capsule.CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID
    assert loaded.payload["schema_id"] == capsule.CLAIM_CAPSULE_SCHEMA_ID
    assert all(spec.json_artifact != "reports/runs/lejepa-mini-grid/summary.json" for spec in canonical.CANONICAL_REPORTS)


def test_not_claimed_failed_gate_learning_revocation_and_forbidden_term_audit_are_projector_owned():
    projected = _project(full_lejepa_claim=True)
    summary = projected["summary_payload"]

    assert summary["failed_gate"] == "U-HG2"
    assert summary["not_claimed"] == summary["claim_capsule"]["not_claimed"]
    assert summary["what_was_learned"] == "The mini-grid recorded a failed gate without promoting a positive claim."
    assert summary["revocation_rows"]
    assert summary["forbidden_claim_term_audit"]["status"] == "pass"
    assert "mechanism-closure-unless-D5-M" in summary["forbidden_claim_term_audit"]["forbidden_positive_claim_terms"]
    assert "mechanism-closure-unless-D5-M" not in claim_terms.FORBIDDEN_POSITIVE_CLAIM_TERMS


def test_thin_script_can_run_with_monkeypatched_single_arm_runner(monkeypatch, tmp_path, capsys):
    monkeypatch.setattr(runner, "run_single_arm", _fake_single_arm)

    rc = runner.main(["--root", str(tmp_path), "--run-id", "fixture-main"])

    assert rc == 0
    stdout = json.loads(capsys.readouterr().out)
    assert stdout["run_id"] == "fixture-main"
    run_dir = tmp_path / "reports/runs/fixture-main"
    assert (run_dir / "summary.json").exists()
    assert (run_dir / "claim_capsule.json").exists()
    assert (run_dir / "raw_metrics.jsonl").exists()
    assert (run_dir / "report.md").exists()
    assert len((run_dir / "raw_metrics.jsonl").read_text(encoding="utf-8").splitlines()) == 300

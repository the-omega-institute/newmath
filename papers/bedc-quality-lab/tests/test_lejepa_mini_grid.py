from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from bedc_quality_lab import lejepa_mini_grid as lejepa_module
from bedc_quality_lab import claim_terms
from bedc_quality_lab.discovery_compiler import capsule
from bedc_quality_lab.lejepa_mini_grid import (
    DEFAULT_ALIGNMENT_LAMBDAS,
    DEFAULT_MIXINGS,
    DEFAULT_RHOS,
    DEFAULT_SEEDS,
    LeJEPAMiniGridProjection,
    NEGATIVE_DIAGNOSIS_ARTIFACT,
    NEGATIVE_DIAGNOSIS_ARTIFACT_ID,
    NEGATIVE_DIAGNOSIS_CANONICAL_ROLE,
    NEGATIVE_DIAGNOSIS_SCHEMA_ID,
    NEGATIVE_DIAGNOSIS_SLICE_KEYS,
    PROJECTOR_FORBIDDEN_TERMS,
    build_lejepa_mini_grid_negative_diagnosis,
    default_grid,
    validate_lejepa_mini_grid_negative_diagnosis,
)
from scripts import run_canonical_reports as canonical
from scripts import run_lejepa_mini_grid as runner


NEGATIVE_WITNESS_ROW = {
    "witness_id": "lejepa-mini-grid:lambda-rho-trend-hardgate-failure",
    "source_artifact": "reports/runs/lejepa-mini-grid/claim_capsule.json",
    "source_pointer": "$.failed_gate",
    "bedc_gap_field": "lambda_rho_trend_gap",
    "demotion_rule": "demote_to_DN_on_D2_HG2_failure",
    "regression_test": "tests/test_lejepa_mini_grid.py::test_lejepa_run_local_negative_witness_records_d2_hg2_failure",
    "evidence_pointer": "reports/runs/lejepa-mini-grid/claim_capsule.json:$.hardgates.D2-HG2",
    "status": "fail",
    "reason": "D2-HG2 records failed lambda/rho trend evidence for the LeJEPA mini-grid claim capsule.",
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


def _fake_negative_single_arm(**kwargs):
    row = _fake_single_arm(**kwargs)
    row["quality_q"] = 0.50
    row["linear_identifiability_r2"] = 0.20
    row["collapse_rate"] = 0.30
    return row


def _contains_key(value, key: str) -> bool:
    if isinstance(value, dict):
        return key in value or any(_contains_key(item, key) for item in value.values())
    if isinstance(value, list):
        return any(_contains_key(item, key) for item in value)
    return False


def _recursive_keys(value):
    if isinstance(value, dict):
        keys = set(value)
        for item in value.values():
            keys |= _recursive_keys(item)
        return keys
    if isinstance(value, list):
        keys = set()
        for item in value:
            keys |= _recursive_keys(item)
        return keys
    return set()


def _negative_projection(monkeypatch, run_id: str = "lejepa-mini-grid"):
    monkeypatch.setattr(runner, "run_single_arm", _fake_negative_single_arm)
    return runner.build_projection(run_id=run_id, generated_at="fixture-time")


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


def test_default_grid_enumerates_300_cells_and_writes_run_artifacts_with_sidecar(monkeypatch, tmp_path):
    calls = []

    def fake_single_arm(**kwargs):
        calls.append(kwargs)
        return _fake_negative_single_arm(**kwargs)

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
    assert summary["claim_capsule"] == {
        "artifact": "reports/runs/fixture-grid/claim_capsule.json",
        "pointer": "$",
    }
    assert summary["negative_diagnosis"] == {
        "artifact": NEGATIVE_DIAGNOSIS_ARTIFACT,
        "pointer": "$",
        "diagnosis_ref": {
            "artifact": "reports/runs/fixture-grid/claim_capsule.json",
            "pointer": "$.run_local.negative_witness[0]",
        },
    }
    assert (tmp_path / NEGATIVE_DIAGNOSIS_ARTIFACT).exists()
    assert capsule_payload["run_local"]["negative_witness"][0]["source_artifact"] == "reports/runs/fixture-grid/claim_capsule.json"
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
    audit = summary["forbidden_claim_term_audit"]
    shared_audit = summary["u_hardgates"]["U-HG8"]["positive_claim_audit"]
    projector_audit = summary["u_hardgates"]["U-HG8"]["projector_positive_claim_audit"]
    capsule_u_hg8 = summary["claim_capsule"]["hardgates"]["U-HG8"]

    assert summary["failed_gate"] == "U-HG2"
    assert summary["not_claimed"] == summary["claim_capsule"]["not_claimed"]
    assert summary["what_was_learned"] == "The mini-grid recorded a failed gate without promoting a positive claim."
    assert summary["revocation_rows"]
    assert audit["status"] == "pass"
    assert summary["u_hardgates"]["U-HG4"]["status"] == "pass"
    assert summary["u_hardgates"]["U-HG8"]["status"] == "pass"
    assert "full-lejepa" in audit["forbidden_positive_claim_terms"]
    assert "full-lejepa" in shared_audit["forbidden_positive_claim_terms"]
    assert "mechanism-closure-unless-D5-M" in PROJECTOR_FORBIDDEN_TERMS
    assert "mechanism-closure-unless-D5-M" in audit["forbidden_positive_claim_terms"]
    assert "mechanism-closure-unless-D5-M" in projector_audit["forbidden_positive_claim_terms"]
    assert summary["claim_capsule"]["forbidden_claim_term_audit"] == audit
    assert capsule_u_hg8["projector_positive_claim_audit"] == projector_audit
    assert "mechanism-closure-unless-D5-M" not in claim_terms.FORBIDDEN_POSITIVE_CLAIM_TERMS


def test_projector_local_forbidden_term_hit_fails_capsule_and_u_hg8():
    projected = _project(local_mechanism_closure_claim=True)
    summary = projected["summary_payload"]
    audit = summary["forbidden_claim_term_audit"]
    capsule_u_hg8 = summary["claim_capsule"]["hardgates"]["U-HG8"]

    assert audit["status"] == "fail"
    assert audit["hits"] == ["mechanism-closure-unless-D5-M"]
    assert summary["u_hardgates"]["U-HG8"]["status"] == "fail"
    assert capsule_u_hg8["status"] == "fail"
    assert summary["u_hardgates"]["U-HG8"]["positive_claim_audit"]["status"] == "pass"
    assert summary["u_hardgates"]["U-HG8"]["projector_positive_claim_audit"]["hits"] == [
        "mechanism-closure-unless-D5-M"
    ]
    assert summary["claim_capsule"]["forbidden_claim_term_audit"] == audit
    assert capsule_u_hg8["projector_positive_claim_audit"]["hits"] == ["mechanism-closure-unless-D5-M"]
    assert summary["claim_capsule"]["claim_status"] == "failed"
    assert summary["failed_gate"] == "forbidden-positive-claim-term"
    assert summary["claim_capsule"]["positive_claim"]["level"] == "DN"


def test_thin_script_can_run_with_monkeypatched_single_arm_runner(monkeypatch, tmp_path, capsys):
    monkeypatch.setattr(runner, "run_single_arm", _fake_negative_single_arm)

    rc = runner.main(["--root", str(tmp_path), "--run-id", "fixture-main"])

    assert rc == 0
    stdout = json.loads(capsys.readouterr().out)
    assert stdout["run_id"] == "fixture-main"
    run_dir = tmp_path / "reports/runs/fixture-main"
    assert (run_dir / "summary.json").exists()
    assert (run_dir / "claim_capsule.json").exists()
    assert (run_dir / "raw_metrics.jsonl").exists()
    assert (run_dir / "report.md").exists()
    assert (tmp_path / NEGATIVE_DIAGNOSIS_ARTIFACT).exists()
    assert len((run_dir / "raw_metrics.jsonl").read_text(encoding="utf-8").splitlines()) == 300


def test_lejepa_run_local_negative_witness_records_d2_hg2_failure(monkeypatch):
    projection = _negative_projection(monkeypatch)
    capsule_payload = projection["claim_capsule_payload"]

    assert capsule_payload["schema_id"] == "bedc.quality.claim_capsule"
    assert capsule_payload["run_local"]["negative_witness"][0] == NEGATIVE_WITNESS_ROW


def test_lejepa_run_local_negative_witness_source_pointer_resolves(monkeypatch):
    projection = _negative_projection(monkeypatch)
    capsule_payload = projection["claim_capsule_payload"]
    row = capsule_payload["run_local"]["negative_witness"][0]

    assert runner.resolve_claim_capsule_pointer(capsule_payload, row["source_pointer"]) == "D2-HG2"


def test_lejepa_run_local_negative_witness_evidence_pointer_resolves(monkeypatch):
    projection = _negative_projection(monkeypatch)
    capsule_payload = projection["claim_capsule_payload"]
    row = capsule_payload["run_local"]["negative_witness"][0]
    artifact, pointer = row["evidence_pointer"].split(":", 1)
    evidence = runner.resolve_claim_capsule_pointer(capsule_payload, pointer)

    assert artifact == row["source_artifact"]
    assert evidence == capsule_payload["hardgates"]["D2-HG2"]
    assert row["status"] == "fail"
    assert evidence["lambda_collapse_rate_increasing"] is False
    assert evidence["lambda_quality_q_decreasing"] is False
    assert evidence["rho_linear_identifiability_r2_increasing"] is False


def test_lejepa_run_local_negative_witness_row_shape_is_singleton_list(monkeypatch):
    projection = _negative_projection(monkeypatch)
    negative_witness = projection["claim_capsule_payload"]["run_local"]["negative_witness"]

    assert isinstance(negative_witness, list)
    assert len(negative_witness) == 1
    assert set(negative_witness[0]) == set(runner.NEGATIVE_WITNESS_KEYS)


def test_lejepa_public_surfaces_point_to_run_local_negative_witness_owner(monkeypatch, tmp_path):
    projection = _negative_projection(monkeypatch)
    runner.write_artifacts(projection, root=tmp_path)
    run_dir = tmp_path / "reports/runs/lejepa-mini-grid"
    summary = json.loads((run_dir / "summary.json").read_text(encoding="utf-8"))
    capsule_payload = json.loads((run_dir / "claim_capsule.json").read_text(encoding="utf-8"))
    diagnosis = json.loads((tmp_path / NEGATIVE_DIAGNOSIS_ARTIFACT).read_text(encoding="utf-8"))
    report = (run_dir / "report.md").read_text(encoding="utf-8")
    owner_ref = {
        "artifact": "reports/runs/lejepa-mini-grid/claim_capsule.json",
        "pointer": "$.run_local.negative_witness[0]",
    }

    assert summary["negative_diagnosis"] == {
        "artifact": NEGATIVE_DIAGNOSIS_ARTIFACT,
        "pointer": "$",
        "diagnosis_ref": owner_ref,
    }
    assert diagnosis["diagnosis_ref"] == "reports/runs/lejepa-mini-grid/claim_capsule.json:$.run_local.negative_witness[0]"
    assert summary["claim_capsule"] == {"artifact": owner_ref["artifact"], "pointer": "$"}
    assert owner_ref["pointer"] not in json.dumps(capsule_payload["run_local"]["negative_witness"][0], sort_keys=True)
    assert NEGATIVE_DIAGNOSIS_ARTIFACT in report
    assert "lambda-rho-trend-hardgate-failure" not in json.dumps(summary, sort_keys=True)


def test_lejepa_run_local_negative_witness_fail_closed_raises_on_bad_evidence(monkeypatch):
    projection = _negative_projection(monkeypatch)
    capsule_payload = projection["claim_capsule_payload"]
    capsule_payload["hardgates"]["D2-HG2"]["status"] = "pass"

    with pytest.raises(ValueError, match="negative witness source, evidence, or regression pointer"):
        runner.finalize_negative_witness_projection(
            {**projection, "claim_capsule_payload": capsule_payload},
            run_id="lejepa-mini-grid",
        )


def test_lejepa_writer_fail_closed_raises_on_corrupt_finalized_source(monkeypatch, tmp_path):
    projection = _negative_projection(monkeypatch)
    capsule_payload = dict(projection["claim_capsule_payload"])
    capsule_payload["run_local"]["negative_witness"][0] = {
        **capsule_payload["run_local"]["negative_witness"][0],
        "source_pointer": "$.missing_gate",
    }

    with pytest.raises(ValueError, match="negative witness source, evidence, or regression pointer"):
        runner.write_artifacts({**projection, "claim_capsule_payload": capsule_payload}, root=tmp_path)


def test_lejepa_run_local_negative_witness_no_terminal_verdict_leakage(monkeypatch):
    projection = _negative_projection(monkeypatch)
    capsule_payload = projection["claim_capsule_payload"]
    summary = projection["summary_payload"]
    nw_block = {
        "summary_negative_diagnosis": summary["negative_diagnosis"],
        "capsule_run_local": capsule_payload["run_local"],
    }

    assert not _contains_key(nw_block, "terminal_verdict")
    assert "terminal_verdict" not in json.dumps(nw_block, sort_keys=True)


def test_lejepa_source_projection_has_no_terminal_verdict_key():
    projection = _project()

    assert "terminal_verdict" not in _recursive_keys(
        {
            "summary": projection["summary_payload"],
            "capsule": projection["claim_capsule_payload"],
            "report": projection["report_markdown"],
        }
    )
    assert "terminal_verdict" not in json.dumps(
        {
            "summary": projection["summary_payload"],
            "capsule": projection["claim_capsule_payload"],
            "report": projection["report_markdown"],
        },
        sort_keys=True,
    )


def test_lejepa_negative_diagnosis_sidecar_schema_and_pointer_only_slices(monkeypatch, tmp_path):
    projection = _negative_projection(monkeypatch)
    runner.write_artifacts(projection, root=tmp_path)
    sidecar_path = tmp_path / NEGATIVE_DIAGNOSIS_ARTIFACT
    payload = json.loads(sidecar_path.read_text(encoding="utf-8"))

    assert list(payload) == [
        "artifact_id",
        "canonical_role",
        "diagnosis_ref",
        "diagnosis_slices",
        "generated_at",
        "hardgate",
        "not_claimed",
        "producer",
        "projector",
        "schema_id",
        "source_artifacts",
    ]
    assert set(payload) == {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "projector",
        "canonical_role",
        "source_artifacts",
        "diagnosis_ref",
        "diagnosis_slices",
        "hardgate",
        "not_claimed",
    }
    assert payload["schema_id"] == NEGATIVE_DIAGNOSIS_SCHEMA_ID
    assert payload["artifact_id"] == NEGATIVE_DIAGNOSIS_ARTIFACT_ID
    assert payload["canonical_role"] == NEGATIVE_DIAGNOSIS_CANONICAL_ROLE
    assert payload["diagnosis_ref"] == "reports/runs/lejepa-mini-grid/claim_capsule.json:$.run_local.negative_witness[0]"
    assert set(payload["diagnosis_slices"]) == set(NEGATIVE_DIAGNOSIS_SLICE_KEYS)
    for row in payload["diagnosis_slices"].values():
        assert set(row) <= {"artifact_pointer", "status", "reason", "regression_test"}
        assert "artifact_pointer" in row
        assert "status" in row
        assert "reason" in row
        assert "record_count" not in row
        assert "quality_q" not in row
        assert "witness_id" not in row
    assert "terminal_verdict" not in _recursive_keys(payload)
    assert "terminal_verdict" not in json.dumps(payload, sort_keys=True)
    validate_lejepa_mini_grid_negative_diagnosis(payload, root=tmp_path)


def test_lejepa_negative_diagnosis_validator_fail_closed_on_missing_pointer(monkeypatch, tmp_path):
    projection = _negative_projection(monkeypatch)
    runner.write_artifacts(projection, root=tmp_path)
    payload = json.loads((tmp_path / NEGATIVE_DIAGNOSIS_ARTIFACT).read_text(encoding="utf-8"))
    payload["diagnosis_slices"]["metric_trend"]["artifact_pointer"] = (
        "reports/runs/lejepa-mini-grid/claim_capsule.json:$.hardgates.missing"
    )

    with pytest.raises(ValueError, match="pointer is not resolvable"):
        validate_lejepa_mini_grid_negative_diagnosis(payload, root=tmp_path)


def test_lejepa_negative_diagnosis_sidecar_stays_out_of_canonical_reports():
    assert NEGATIVE_DIAGNOSIS_ARTIFACT not in {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}
    assert all(spec.name != "lejepa_mini_grid_negative_diagnosis" for spec in canonical.CANONICAL_REPORTS)


def test_no_named_lejepa_negative_diagnosis_helper_symbol():
    assert not hasattr(lejepa_module, "LeJEPAMiniGridNegativeDiagnosis")
    assert callable(build_lejepa_mini_grid_negative_diagnosis)


def test_lejepa_negative_diagnosis_output_is_idempotent(monkeypatch, tmp_path):
    projection = _negative_projection(monkeypatch)
    runner.write_artifacts(projection, root=tmp_path)
    first = (tmp_path / NEGATIVE_DIAGNOSIS_ARTIFACT).read_text(encoding="utf-8")
    runner.write_artifacts(projection, root=tmp_path)
    second = (tmp_path / NEGATIVE_DIAGNOSIS_ARTIFACT).read_text(encoding="utf-8")

    assert first == second


def test_checked_in_lejepa_negative_diagnosis_is_regenerated_by_producer(monkeypatch, tmp_path):
    monkeypatch.setattr(runner, "run_single_arm", _fake_negative_single_arm)
    projection = runner.build_projection(run_id="lejepa-mini-grid")
    runner.write_artifacts(projection, root=tmp_path)
    generated = (tmp_path / NEGATIVE_DIAGNOSIS_ARTIFACT).read_text(encoding="utf-8")
    checked_in = (Path.cwd() / NEGATIVE_DIAGNOSIS_ARTIFACT).read_text(encoding="utf-8")

    assert checked_in == generated

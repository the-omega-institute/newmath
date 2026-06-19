import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from bedc_quality_lab import minigrid_doorkey_ood_adjudication as adjudication
from bedc_quality_lab import minigrid_doorkey_ood_adjudication as ood
from bedc_quality_lab.minigrid_doorkey_families import default_fresh_episode_rows


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = Path("scripts/run_minigrid_doorkey_ood_adjudication.py")


def _copy_cli_project(tmp_path: Path) -> Path:
    package = tmp_path / "bedc_quality_lab"
    if not package.exists():
        shutil.copytree(ROOT / "bedc_quality_lab", package)
    scripts = tmp_path / "scripts"
    scripts.mkdir(exist_ok=True)
    script = scripts / SCRIPT.name
    script.write_text((ROOT / SCRIPT).read_text(encoding="utf-8"), encoding="utf-8")
    return script


def _run_cli(tmp_path: Path, *args: object) -> subprocess.CompletedProcess[str]:
    script = _copy_cli_project(tmp_path)
    return subprocess.run(
        [
            sys.executable,
            str(script),
            *[str(arg) for arg in args],
        ],
        cwd=tmp_path,
        text=True,
        capture_output=True,
    )


def test_smoke_report_writes_bounded_raw_evidence_and_validates(tmp_path):
    report_path = tmp_path / "smoke.json"

    payload = adjudication.write_report(
        root=tmp_path,
        report_path=report_path,
        run_id="smoke-unit",
        seeds=(101,),
        updates=20,
        eval_episodes=4,
        batch_size=16,
        device="cpu",
        smoke=True,
        generated_at="fixture",
    )

    assert payload["execution_mode"] == "smoke"
    assert payload["verdict"]["status"] == adjudication.NON_PUBLIC_VERDICT
    assert "gpu_evidence_not_public" in payload["verdict"]["public_gate_failures"]
    assert json.loads(report_path.read_text(encoding="utf-8")) == payload
    adjudication.validate_report(payload, root=tmp_path)
    adjudication.load_and_validate_report(report_path, root=tmp_path)
    for pointer in payload["raw_artifact_pointers"]:
        path = Path(pointer["path"])
        assert not path.is_absolute()
        assert path.is_relative_to(Path(adjudication.RUNS_ROOT) / "smoke-unit")
        assert pointer["role"] in adjudication.ALLOWED_RAW_ROLES


def test_cli_writes_smoke_report_and_validate_only_accepts_it(tmp_path):
    report = Path("nested") / "smoke.json"

    write_result = _run_cli(
        tmp_path,
        "--report",
        report,
        "--run-id",
        "cli-smoke",
        "--seeds",
        "101",
        "--updates",
        20,
        "--eval-episodes",
        4,
        "--batch-size",
        16,
        "--device",
        "cpu",
        "--smoke",
        "--generated-at",
        "fixture",
    )

    assert write_result.returncode == 0, write_result.stderr
    assert "wrote nested/smoke.json status=not_public_evidence" in write_result.stdout
    payload = json.loads((tmp_path / report).read_text(encoding="utf-8"))
    assert payload["spec"]["run_id"] == "cli-smoke"
    assert payload["execution_mode"] == "smoke"

    validate_result = _run_cli(tmp_path, "--report", report, "--validate-only")

    assert validate_result.returncode == 0, validate_result.stderr
    assert "validated nested/smoke.json status=not_public_evidence" in validate_result.stdout


@pytest.mark.parametrize(
    ("bootstrap", "expected_status", "expected_public"),
    [
        ({"status": "pass", "ci95_low": 0.031, "ci95_high": 0.08, "mean_delta": 0.05}, "win", True),
        ({"status": "pass", "ci95_low": -0.04, "ci95_high": 0.0, "mean_delta": -0.02}, "falsify", True),
        ({"status": "pass", "ci95_low": 0.01, "ci95_high": 0.04, "mean_delta": 0.02}, "abstain", False),
    ],
)
def test_full_report_selects_public_verdict_table(
    tmp_path, monkeypatch, bootstrap, expected_status, expected_public
):
    monkeypatch.setattr(
        adjudication,
        "_gpu_evidence_for_mode",
        lambda *, device, smoke: {"schema_id": "bedc-gpu-evidence", "public_evidence": True},
    )
    monkeypatch.setattr(
        adjudication,
        "_paired_bootstrap",
        lambda rows, *, resamples, seed: {**bootstrap, "metric": "paired_delta_success", "resamples": resamples},
    )

    payload = adjudication.write_report(
        root=tmp_path,
        report_path=tmp_path / f"{expected_status}.json",
        run_id=f"{expected_status}-unit",
        seeds=(101, 102, 103),
        updates=80000,
        eval_episodes=120,
        batch_size=256,
        device="cuda",
        generated_at="fixture",
    )

    assert payload["execution_mode"] == "full"
    assert payload["verdict"]["status"] == expected_status
    assert payload["verdict"]["public_evidence"] is expected_public
    assert payload["verdict"]["public_gate_failures"] == []
    adjudication.validate_report(payload, root=tmp_path)


def test_full_report_records_public_gate_failure_reasons_without_public_gpu(tmp_path, monkeypatch):
    monkeypatch.setattr(
        adjudication,
        "_gpu_evidence_for_mode",
        lambda *, device, smoke: {"schema_id": "bedc-gpu-evidence", "public_evidence": False},
    )
    monkeypatch.setattr(
        adjudication,
        "_paired_bootstrap",
        lambda rows, *, resamples, seed: {
            "status": "pass",
            "metric": "paired_delta_success",
            "mean_delta": 0.05,
            "ci95_low": 0.04,
            "ci95_high": 0.08,
            "resamples": resamples,
        },
    )

    payload = adjudication.write_report(
        root=tmp_path,
        report_path=tmp_path / "not-public.json",
        run_id="not-public-unit",
        seeds=(101, 102, 103),
        updates=80000,
        eval_episodes=120,
        batch_size=256,
        device="cuda",
        generated_at="fixture",
    )

    assert payload["verdict"]["status"] == adjudication.NON_PUBLIC_VERDICT
    assert payload["verdict"]["public_evidence"] is False
    assert payload["verdict"]["public_gate_failures"] == ["gpu_evidence_not_public"]
    adjudication.validate_report(payload, root=tmp_path)


@pytest.mark.parametrize(
    ("kwargs", "expected_failure"),
    [
        ({"execution_mode": "smoke"}, "execution_mode_not_full"),
        ({"seeds": (101, 102)}, "insufficient_seed_count"),
        ({"eval_episodes": 99}, "insufficient_eval_episodes"),
        ({"gpu_evidence": {"public_evidence": False}}, "gpu_evidence_not_public"),
        ({"split_audit": {"status": "fail"}}, "split_audit_failed"),
        ({"bootstrap": {"status": "fail", "ci95_low": 0.04, "ci95_high": 0.08}}, "paired_bootstrap_failed"),
    ],
)
def test_raw_verdict_reports_each_public_evidence_gate_failure(kwargs, expected_failure):
    args = {
        "execution_mode": "full",
        "seeds": (101, 102, 103),
        "eval_episodes": 120,
        "gpu_evidence": {"public_evidence": True},
        "split_audit": {"status": "pass"},
        "bootstrap": {"status": "pass", "ci95_low": 0.04, "ci95_high": 0.08},
    }
    args.update(kwargs)

    verdict = adjudication._raw_verdict(**args)

    assert verdict["status"] == adjudication.NON_PUBLIC_VERDICT
    assert verdict["public_evidence"] is False
    assert expected_failure in verdict["public_gate_failures"]


def _public_report_payload(tmp_path, monkeypatch, run_id: str) -> dict[str, object]:
    monkeypatch.setattr(
        adjudication,
        "_gpu_evidence_for_mode",
        lambda *, device, smoke: {"schema_id": "bedc-gpu-evidence", "public_evidence": True},
    )
    monkeypatch.setattr(
        adjudication,
        "_paired_bootstrap",
        lambda rows, *, resamples, seed: {
            "status": "pass",
            "metric": "paired_delta_success",
            "mean_delta": 0.05,
            "ci95_low": 0.04,
            "ci95_high": 0.08,
            "resamples": resamples,
        },
    )
    payload = adjudication.write_report(
        root=tmp_path,
        report_path=tmp_path / f"{run_id}.json",
        run_id=run_id,
        seeds=(101, 102, 103),
        updates=80000,
        eval_episodes=120,
        batch_size=256,
        device="cuda",
        generated_at="fixture",
    )
    assert payload["verdict"]["status"] == "win"
    adjudication.validate_report(payload, root=tmp_path)
    return payload


@pytest.mark.parametrize(
    ("field_update", "message"),
    [
        ({"execution_mode": "smoke"}, "public verdict requires full execution mode"),
        ({"gpu_evidence": {"schema_id": "bedc-gpu-evidence", "public_evidence": False}}, "CUDA GPU evidence"),
        ({"split_audit": {"status": "fail"}}, "passing split audit"),
        ({"paired_bootstrap": {"status": "fail"}}, "passing paired bootstrap"),
    ],
)
def test_validate_report_rejects_public_verdict_with_failed_public_gate(
    tmp_path, monkeypatch, field_update, message
):
    payload = _public_report_payload(tmp_path, monkeypatch, run_id=f"public-gate-{len(message)}")
    payload.update(field_update)

    with pytest.raises(ValueError, match=message):
        adjudication.validate_report(payload, root=tmp_path)


def test_public_verdict_hard_fails_when_raw_digest_drifts(tmp_path):
    report_path = tmp_path / "public.json"
    payload = adjudication.write_report(
        root=tmp_path,
        report_path=report_path,
        run_id="public-unit",
        seeds=(101, 102, 103),
        updates=80000,
        eval_episodes=120,
        batch_size=256,
        device="cpu",
        smoke=True,
        generated_at="fixture",
    )
    payload["execution_mode"] = "full"
    payload["gpu_evidence"] = {"schema_id": "bedc-gpu-evidence", "public_evidence": True}
    payload["verdict"] = {"status": "win", "reason": "fixture", "public_evidence": True, "public_gate_failures": []}
    first = tmp_path / payload["raw_artifact_pointers"][0]["path"]
    content = first.read_text(encoding="utf-8")
    first.write_text(("X" if content[0] != "X" else "Y") + content[1:], encoding="utf-8")

    with pytest.raises(ValueError, match="digest mismatch"):
        adjudication.validate_report(payload, root=tmp_path)


def test_public_verdict_rejects_disallowed_or_out_of_tree_raw_role(tmp_path):
    payload = adjudication.write_report(
        root=tmp_path,
        report_path=tmp_path / "public.json",
        run_id="role-unit",
        seeds=(101, 102, 103),
        updates=80000,
        eval_episodes=120,
        batch_size=256,
        device="cpu",
        smoke=True,
        generated_at="fixture",
    )
    payload["execution_mode"] = "full"
    payload["gpu_evidence"] = {"schema_id": "bedc-gpu-evidence", "public_evidence": True}
    payload["verdict"] = {"status": "falsify", "reason": "fixture", "public_evidence": True, "public_gate_failures": []}
    payload["raw_artifact_pointers"][0] = {
        **payload["raw_artifact_pointers"][0],
        "role": "single_summary_json",
        "path": "reports/issue_1553_minigrid_doorkey_ood_adjudication.json",
    }

    with pytest.raises(ValueError, match="role is not allowed"):
        adjudication.validate_report(payload, root=tmp_path)


def test_validate_committed_report_if_present():
    path = ROOT / adjudication.DEFAULT_REPORT
    if path.exists():
        payload = adjudication.load_and_validate_report(path, root=ROOT)
        assert payload["schema_id"] == adjudication.SCHEMA_ID


def _rows() -> list[dict[str, object]]:
    return [dict(row) for row in default_fresh_episode_rows()]


def _publication_rows() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    seeds = (1101, 1102, 1103)
    metrics = {
        "base": (0.50, 0.70, 0.60),
        "bedc": (0.72, 0.72, 0.78),
        "bedc_shuffle_placebo": (0.48, 0.68, 0.55),
    }
    for arm_id, (success, id_success, gap_auc) in metrics.items():
        for episode_index in range(500):
            rows.append(
                {
                    "family_id": "F3",
                    "fresh_env_id": f"doorkey-f3-fresh-{episode_index + 1}",
                    "seed": seeds[episode_index % len(seeds)],
                    "episode_index": episode_index,
                    "arm_id": arm_id,
                    "success": success,
                    "id_success": id_success,
                    "gap_auc": gap_auc,
                }
            )
    return rows


def test_fixture_smoke_payload_is_not_publication_bearing() -> None:
    payload = ood.build_payload(generated_at="fixture")

    ood.validate_payload(payload)
    assert payload["schema_id"] == ood.SCHEMA_ID
    assert payload["execution_mode"] == "fixture-smoke"
    assert payload["hardgate"]["status"] == "fail"
    assert payload["hardgate"]["gates"]["MODE"]["status"] == "pass"
    assert payload["hardgate"]["failed_gates"] == ["F3_COVERAGE"]
    assert payload["verdict"]["status"] == "not_ready"
    assert payload["claim_boundary"]["status"] == "not-publication-bearing"
    assert payload["claim_boundary"]["claim_allowed"] is False


def test_gap_auc_is_diagnostics_only_not_primary_endpoint() -> None:
    payload = ood.build_payload(generated_at="fixture")

    assert payload["config"]["primary_endpoint"] == "f3_fresh_env_success"
    assert payload["claim_boundary"]["primary_endpoint"] == "f3_fresh_env_success"
    assert payload["claim_boundary"]["diagnostics_only"] == ["gap_auc"]


def test_primary_endpoint_uses_paired_lower_bound_against_base_and_placebo() -> None:
    payload = ood.build_payload(generated_at="fixture")
    gate = payload["hardgate"]["gates"]["PRIMARY_ENDPOINT"]

    assert gate["status"] == "pass"
    assert gate["bedc_over_base"]["lower_bound"] >= gate["success_lower_bound"]
    assert gate["bedc_over_shuffle_placebo"]["lower_bound"] >= gate["placebo_lower_bound"]


def test_id_non_regression_failure_blocks_publication_gate() -> None:
    rows = _rows()
    for row in rows:
        if row["arm_id"] == "bedc":
            row["id_success"] = 0.40

    payload = ood.build_payload(generated_at="fixture", observations=rows, execution_mode="publication-bearing")

    assert "ID_NON_REGRESSION" in payload["hardgate"]["failed_gates"]
    assert payload["verdict"]["status"] == "not_ready"
    assert payload["claim_boundary"]["claim_allowed"] is False


def test_publication_bearing_mode_fails_closed_on_fixture_coverage() -> None:
    payload = ood.build_payload(generated_at="fixture", execution_mode="publication-bearing")

    assert payload["execution_mode"] == "publication-bearing"
    assert payload["hardgate"]["status"] == "fail"
    assert "F3_COVERAGE" in payload["hardgate"]["failed_gates"]
    assert payload["claim_boundary"]["status"] == "not-publication-bearing"


def test_publication_bearing_success_authorizes_claim_boundary() -> None:
    payload = ood.build_payload(
        generated_at="fixture",
        observations=_publication_rows(),
        execution_mode="publication-bearing",
    )

    ood.validate_payload(payload)
    assert payload["hardgate"]["status"] == "pass"
    assert payload["hardgate"]["failed_gates"] == []
    assert payload["verdict"]["status"] == "success"
    assert payload["claim_boundary"]["status"] == "publication-bearing"
    assert payload["claim_boundary"]["claim_allowed"] is True
    assert {
        row["arm_id"]: row["fresh_episode_count"]
        for row in payload["arm_summaries"]
    } == {
        "base": 500,
        "bedc": 500,
        "bedc_shuffle_placebo": 500,
    }


def test_missing_arm_fails_closed() -> None:
    rows = [row for row in _rows() if row["arm_id"] != "bedc_shuffle_placebo"]

    payload = ood.build_payload(generated_at="fixture", observations=rows)

    assert "ARMS" in payload["hardgate"]["failed_gates"]
    assert "PRIMARY_ENDPOINT" in payload["hardgate"]["failed_gates"]
    assert payload["claim_boundary"]["claim_allowed"] is False


def test_validate_payload_rejects_gap_auc_primary_endpoint_drift() -> None:
    payload = ood.build_payload(generated_at="fixture")
    payload["config"] = {**payload["config"], "diagnostics_only": []}

    with pytest.raises(ValueError, match="gap_auc"):
        ood.validate_payload(payload)


def test_write_artifacts_outputs_json_markdown_and_fingerprint(tmp_path) -> None:
    payload = ood.write_artifacts(root=tmp_path, generated_at="fixture")

    json_path = tmp_path / ood.JSON_ARTIFACT
    markdown_path = tmp_path / ood.MARKDOWN_ARTIFACT
    fingerprint_path = tmp_path / ood.FINGERPRINT_ARTIFACT
    assert json_path.exists()
    assert markdown_path.exists()
    assert fingerprint_path.exists()
    persisted = json.loads(json_path.read_text(encoding="utf-8"))
    ood.validate_payload(persisted)
    assert persisted["raw_digest"] == payload["raw_digest"]
    assert "# MiniGrid DoorKey OOD Adjudication" in markdown_path.read_text(encoding="utf-8")
    fingerprint = json.loads(fingerprint_path.read_text(encoding="utf-8"))
    assert fingerprint["report_name"] == "minigrid-doorkey-ood-adjudication"
    assert fingerprint["json_artifact"] == ood.JSON_ARTIFACT
    assert fingerprint["reproducibility_mode"] == "fixture-smoke"

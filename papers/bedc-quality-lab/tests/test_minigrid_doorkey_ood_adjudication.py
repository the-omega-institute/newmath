import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

from bedc_quality_lab import minigrid_doorkey_ood_adjudication as adjudication


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

import json
from pathlib import Path

import pytest

from bedc_quality_lab import minigrid_doorkey_ood_adjudication as adjudication


ROOT = Path(__file__).resolve().parents[1]


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

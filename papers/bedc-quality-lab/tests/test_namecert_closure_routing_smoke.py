import json

from bedc_quality_lab import namecert_closure_routing as ncr
from scripts import (
    run_namecert_audit,
    run_namecert_authswap,
    run_namecert_closure_routing,
    run_namecert_closure_verify,
)


def _assert_smoke_contract(payload):
    assert payload["schema_id"] == ncr.SCHEMA_ID
    assert payload["admission"]["admission_gate"] is False
    assert {row["status"] for row in payload["hardgates"].values()} == {"pass"}

    metrics = payload["metrics"]
    assert metrics["learned"]["accuracy"] > 0.5
    assert metrics["heldout_depth"]["depth"] > metrics["heldout_depth"]["train_max_depth"]
    assert metrics["heldout_depth"]["accuracy"] > 0.5
    assert metrics["learned"]["accuracy"] <= payload["analytic_ceiling"]["analytic_bayes"] + payload["analytic_ceiling"]["tolerance"]

    for key in (
        "matched_twin_closure_blind",
        "serialization_only_adversary",
        "bounded_pattern_control",
    ):
        low, high = metrics[key]["ci"]
        assert low <= 0.5 <= high
        assert metrics[key]["accuracy"] == 0.5


def test_smoke_authswap_real_torch_contract():
    payload = ncr.build_record("smoke_authswap", device="cpu", generated_at="fixture-time").to_dict()

    _assert_smoke_contract(payload)
    assert payload["profile"]["profile_id"] == "smoke_authswap"
    assert payload["json_artifact"] == "reports/namecert_authswap.json"


def test_smoke_audit_real_torch_contract():
    payload = ncr.build_record("smoke_audit", device="cpu", generated_at="fixture-time").to_dict()

    _assert_smoke_contract(payload)
    assert payload["profile"]["profile_id"] == "smoke_audit"
    assert payload["json_artifact"] == "reports/namecert_audit.json"


def test_runner_writes_authswap_and_audit_reports(tmp_path):
    authswap = ncr.run_and_write("smoke_authswap", root=tmp_path, device="cpu", generated_at="fixture-time")
    audit = ncr.run_and_write("smoke_audit", root=tmp_path, device="cpu", generated_at="fixture-time")

    for payload in (authswap, audit):
        _assert_smoke_contract(payload)
        json_path = tmp_path / payload["json_artifact"]
        markdown_path = tmp_path / payload["markdown_artifact"]
        assert json_path.exists()
        assert markdown_path.exists()
        assert json.loads(json_path.read_text(encoding="utf-8")) == payload
        assert payload["profile"]["profile_id"] in markdown_path.read_text(encoding="utf-8")


def test_profile_scripts_are_thin_entrypoints(tmp_path, capsys):
    assert run_namecert_closure_routing.main(["--root", str(tmp_path), "--device", "cpu", "--generated-at", "fixture-time"]) == 0
    assert run_namecert_closure_verify.main(["--root", str(tmp_path), "--device", "cpu", "--generated-at", "fixture-time"]) == 0
    assert run_namecert_authswap.main(["--root", str(tmp_path), "--device", "cpu", "--generated-at", "fixture-time"]) == 0
    assert run_namecert_audit.main(["--root", str(tmp_path), "--device", "cpu", "--generated-at", "fixture-time"]) == 0

    lines = capsys.readouterr().out.strip().splitlines()
    summaries = [json.loads(line) for line in lines]
    expected = [
        ("smoke_closure_routing", "reports/namecert_closure_routing.json"),
        ("smoke_closure_verify", "reports/namecert_closure_verify.json"),
        ("smoke_authswap", "reports/namecert_authswap.json"),
        ("smoke_audit", "reports/namecert_audit.json"),
    ]
    assert [(summary["profile_id"], summary["json_artifact"]) for summary in summaries] == expected
    for profile_id, json_artifact in expected:
        json_path = tmp_path / json_artifact
        markdown_path = json_path.with_suffix(".md")
        assert json_path.exists()
        assert markdown_path.exists()
        payload = json.loads(json_path.read_text(encoding="utf-8"))
        _assert_smoke_contract(payload)
        assert payload["profile"]["profile_id"] == profile_id
        assert profile_id in markdown_path.read_text(encoding="utf-8")

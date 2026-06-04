import json
from pathlib import Path

from bedc_quality_lab.schema import SCHEMA_ID
from scripts import run_canonical_reports as canonical
from scripts import run_single_threshold_escape_witness as stew


ROOT = Path(__file__).resolve().parents[1]


def _threshold_payload():
    return json.loads((ROOT / stew.THRESHOLD_ARTIFACT).read_text(encoding="utf-8"))


def _registry_payload():
    return json.loads((ROOT / stew.REGISTRY_ARTIFACT).read_text(encoding="utf-8"))


def _write_sources(tmp_path, threshold=None, registry=None):
    threshold = _threshold_payload() if threshold is None else threshold
    registry = _registry_payload() if registry is None else registry
    threshold_path = tmp_path / stew.THRESHOLD_ARTIFACT
    registry_path = tmp_path / stew.REGISTRY_ARTIFACT
    threshold_path.parent.mkdir(parents=True, exist_ok=True)
    registry_path.parent.mkdir(parents=True, exist_ok=True)
    threshold_path.write_text(json.dumps(threshold), encoding="utf-8")
    registry_path.write_text(json.dumps(registry), encoding="utf-8")


def test_hg_stew_1_source_integrity_requires_curve_and_hardgate_pointers():
    payload = _threshold_payload()
    ok, failures = stew.validate_source_integrity(payload)
    assert ok is True
    assert failures == []

    missing_curve = dict(payload)
    missing_curve.pop("threshold_curve")
    ok, failures = stew.validate_source_integrity(missing_curve)
    assert ok is False
    assert "missing $.threshold_curve" in failures

    missing_hardgate_pointer = dict(payload)
    missing_hardgate_pointer["hardgate"] = {"checks": payload["hardgate"]["checks"]}
    ok, failures = stew.validate_source_integrity(missing_hardgate_pointer)
    assert ok is False
    assert "missing $.hardgate.policy" in failures


def test_hg_stew_2_single_threshold_basis_is_exactly_one_cell_without_adjacent_run():
    threshold = _threshold_payload()
    pseudo = stew.build_pseudo_payload(threshold)
    assert pseudo["single_threshold_basis"] == [
        {
            "source_pointer": f"{stew.THRESHOLD_ARTIFACT}:$.threshold_curve[0]",
            "threshold": threshold["threshold_curve"][0]["threshold"],
            "positive_rule": stew.POSITIVE_RULE,
            "positive_signal": {
                "metric": "AUROC",
                "ci95_low": threshold["threshold_curve"][0]["metrics"]["AUROC"]["ci95_low"],
                "comparison": "> 0.5",
            },
        }
    ]
    ok, failures = stew.validate_single_threshold_basis(pseudo)
    assert ok is True
    assert failures == []

    multi_cell = dict(pseudo)
    multi_cell["single_threshold_basis"] = pseudo["single_threshold_basis"] * 2
    ok, failures = stew.validate_single_threshold_basis(multi_cell)
    assert ok is False
    assert failures == ["positive pseudo payload must carry exactly one single_threshold_basis cell"]

    inherited_adjacent = dict(pseudo)
    inherited_adjacent["single_threshold_basis"] = [{**pseudo["single_threshold_basis"][0], "adjacent_run": []}]
    ok, failures = stew.validate_single_threshold_basis(inherited_adjacent)
    assert ok is False
    assert "single_threshold_basis must not inherit adjacent_run" in failures


def test_hg_stew_3_positive_projection_is_captured_and_negative_is_fail_closed(monkeypatch):
    class D4Projection:
        discovery_level = "D4"
        reasons = ("positive_discovery=true", "robustness evidence absent")

    monkeypatch.setattr(stew, "assign_discovery_level", lambda payload: D4Projection())
    captured = stew.evaluate_pseudo_payload({"verdict": "accepted", "positive_discovery": True})
    assert captured["status"] == "escaped-positive-captured"
    assert captured["discovery_level"] == "D4"

    class D0Projection:
        discovery_level = "D0"
        reasons = ("no classifier shift or debt improvement",)

    monkeypatch.setattr(stew, "assign_discovery_level", lambda payload: D0Projection())
    closed = stew.evaluate_pseudo_payload({"verdict": "negative/compression", "positive_discovery": False})
    assert closed["status"] == "checked-fail-closed"
    assert closed["escaped"] is False


def test_hg_stew_4_missing_deferred_registry_row_is_stale_source_boundary(tmp_path):
    registry = _registry_payload()
    registry["deferred_kinds"] = [
        row for row in registry["deferred_kinds"] if row["kind"] != stew.DEFERRED_KIND
    ]
    _write_sources(tmp_path, registry=registry)

    payload = stew.build_sidecar(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["status"] == "stale-source-boundary"
    assert "HG-STEW-4" not in payload["hardgates"]


def test_build_sidecar_source_integrity_failure_reports_public_status(tmp_path):
    threshold = _threshold_payload()
    threshold.pop("threshold_curve")
    _write_sources(tmp_path, threshold=threshold)

    payload = stew.build_sidecar(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["status"] == "source-integrity-failed"
    assert payload["hardgates"]["HG-STEW-1"]["status"] == "fail"
    assert "missing $.threshold_curve" in payload["hardgates"]["HG-STEW-1"]["failures"]
    assert payload["hardgates"]["HG-STEW-4"]["status"] == "pass"
    assert "HG-STEW-2" not in payload["hardgates"]


def test_hg_stew_5_forbidden_terms_and_missing_control_baseline_fail():
    threshold = _threshold_payload()
    pseudo = stew.build_pseudo_payload(threshold)
    ok, failures = stew.validate_control_and_claim_boundary(threshold, pseudo)
    assert ok is True
    assert failures == []

    no_control = dict(threshold)
    no_control["threshold_summary"] = dict(threshold["threshold_summary"])
    no_control["threshold_summary"].pop("control_baseline")
    ok, failures = stew.validate_control_and_claim_boundary(no_control, pseudo)
    assert ok is False
    assert "missing $.threshold_summary.control_baseline" in failures

    forbidden = dict(pseudo)
    forbidden["positive_statement"] = "full-lejepa"
    forbidden["score"] = 1.0
    ok, failures = stew.validate_control_and_claim_boundary(threshold, forbidden)
    assert ok is False
    assert any("forbidden positive claim terms" in failure for failure in failures)
    assert any("forbidden score fields" in failure for failure in failures)


def test_build_sidecar_construction_failure_reports_failed_boundary_row(tmp_path):
    threshold = _threshold_payload()
    threshold["threshold_summary"] = dict(threshold["threshold_summary"])
    threshold["threshold_summary"].pop("control_baseline")
    _write_sources(tmp_path, threshold=threshold)

    payload = stew.build_sidecar(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["status"] == "construction-failed"
    assert payload["hardgates"]["HG-STEW-1"]["status"] == "pass"
    assert payload["hardgates"]["HG-STEW-2"]["status"] == "pass"
    assert payload["hardgates"]["HG-STEW-5"]["status"] == "fail"
    assert "missing $.threshold_summary.control_baseline" in payload["hardgates"]["HG-STEW-5"]["failures"]


def test_hg_stew_6_threshold_packet_never_promotes_discovery():
    payload = stew.build_sidecar(root=ROOT, generated_at="2030-01-01T00:00:00+00:00")

    assert payload["status"] == "escaped-positive-captured"
    assert payload["projection"]["discovery_level"] == "D4"
    assert payload["projection"]["escaped_positive_is_discovery_evidence"] is False
    assert payload["hardgates"]["HG-STEW-6"]["promotion"] == "none"
    assert payload["escaped_rows"][0]["reason"] == (
        "escaped positive captured as gate failure evidence, not discovery evidence"
    )


def test_no_positive_cell_falls_back_to_checked_fail_closed():
    threshold = _threshold_payload()
    threshold["threshold_curve"] = [
        {
            **cell,
            "metrics": {
                **cell["metrics"],
                "AUROC": {**cell["metrics"]["AUROC"], "ci95_low": 0.5},
            },
        }
        for cell in threshold["threshold_curve"]
    ]
    pseudo = stew.build_pseudo_payload(threshold)
    assert pseudo["verdict"] == "negative/compression"
    assert pseudo["single_threshold_basis"] == []
    result = stew.evaluate_pseudo_payload(pseudo)
    assert result["status"] == "checked-fail-closed"


def test_sidecar_pointer_only_local_schema_and_not_in_canonical_reports(tmp_path):
    _write_sources(tmp_path)
    payload = stew.build_sidecar(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    json_path, md_path = stew.write_sidecar(tmp_path, payload)

    assert payload["schema_id"] == stew.LOCAL_SCHEMA_ID
    assert payload["schema_id"] != SCHEMA_ID
    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert payload["canonical_role"] == stew.CANONICAL_ROLE
    assert stew.JSON_ARTIFACT not in {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}
    assert json.loads(json_path.read_text(encoding="utf-8"))["schema_id"] == stew.LOCAL_SCHEMA_ID
    assert "Single Threshold Escape Witness" in md_path.read_text(encoding="utf-8")


def test_cli_main_writes_artifacts_and_returns_status_contract(tmp_path):
    success_root = tmp_path / "success"
    _write_sources(success_root)

    assert stew.main(["--root", str(success_root)]) == 0
    json_path = success_root / stew.JSON_ARTIFACT
    md_path = success_root / stew.MARKDOWN_ARTIFACT
    assert json_path.exists()
    assert md_path.exists()
    assert json.loads(json_path.read_text(encoding="utf-8"))["status"] == "escaped-positive-captured"
    assert "status: `escaped-positive-captured`" in md_path.read_text(encoding="utf-8")

    registry = _registry_payload()
    registry["deferred_kinds"] = [
        row for row in registry["deferred_kinds"] if row["kind"] != stew.DEFERRED_KIND
    ]
    stale_root = tmp_path / "stale"
    _write_sources(stale_root, registry=registry)

    source_failure = _threshold_payload()
    source_failure.pop("threshold_curve")
    source_root = tmp_path / "source"
    _write_sources(source_root, threshold=source_failure)

    construction_failure = _threshold_payload()
    construction_failure["threshold_summary"] = dict(construction_failure["threshold_summary"])
    construction_failure["threshold_summary"].pop("control_baseline")
    construction_root = tmp_path / "construction"
    _write_sources(construction_root, threshold=construction_failure)

    failure_cases = [
        (stale_root, "stale-source-boundary"),
        (source_root, "source-integrity-failed"),
        (construction_root, "construction-failed"),
    ]
    for root, status in failure_cases:
        assert stew.main(["--root", str(root)]) == 1
        payload = json.loads((root / stew.JSON_ARTIFACT).read_text(encoding="utf-8"))
        assert payload["status"] == status
        assert (root / stew.MARKDOWN_ARTIFACT).exists()


def test_projection_path_is_research_discovery_projector(monkeypatch):
    calls = []

    class Projection:
        discovery_level = "D0"
        reasons = ("mocked projector",)

    def fake_projector(payload):
        calls.append(payload)
        return Projection()

    monkeypatch.setattr(stew, "assign_discovery_level", fake_projector)
    result = stew.evaluate_pseudo_payload({"verdict": "accepted", "positive_discovery": True})

    assert result["status"] == "checked-fail-closed"
    assert len(calls) == 1

from __future__ import annotations

import json

from bedc_quality_lab.backends.lejepa import LeJEPABackendEvidenceAdapter
from scripts import literature_ledger
from scripts import run_canonical_reports as canonical
from scripts import run_discovery_map as discovery_map
from scripts import run_gaussian_ou_lejepa
from scripts import run_lejepa_theorem_ledger as runner


def _payload():
    return runner.build_payload(generated_at="fixture-time")


def _rows():
    return [dict(row) for row in runner.theorem_rows()]


def test_f_hg1_role_completeness_and_uniqueness():
    payload = _payload()
    rows = payload["theorem_rows"]

    assert {row["theorem"] for row in rows} == {"theorem-1", "theorem-2", "theorem-3", "theorem-4"}
    assert len(rows) == len({row["theorem"] for row in rows})
    assert all(row["bedc_role"] in runner.ALLOWED_ROLES for row in rows)
    assert all(isinstance(row["bedc_role"], str) for row in rows)
    assert payload["hardgates"]["F-HG1"]["status"] == "pass"


def test_f_hg1_fails_for_duplicate_or_missing_roles():
    duplicate_rows = _rows()
    duplicate_rows[1]["theorem"] = duplicate_rows[0]["theorem"]
    missing_role_rows = _rows()
    del missing_role_rows[0]["bedc_role"]

    duplicate_gate = runner._hardgate_rows(duplicate_rows, "")["F-HG1"]
    missing_role_gate = runner._hardgate_rows(missing_role_rows, "")["F-HG1"]

    assert duplicate_gate["status"] == "fail"
    assert missing_role_gate["status"] == "fail"
    assert missing_role_gate["role_failures"] == ["theorem-1"]


def test_f_hg2_rows_have_metric_list_and_nonempty_not_implemented():
    payload = _payload()

    for row in payload["theorem_rows"]:
        assert isinstance(row["implemented_metrics"], list)
        assert isinstance(row["not_implemented"], list)
        assert row["not_implemented"]
        assert row["ledger_debt"]
    assert payload["hardgates"]["F-HG2"]["status"] == "pass"


def test_f_hg2_fails_when_row_omits_not_implemented():
    rows = _rows()
    del rows[0]["not_implemented"]

    gate = runner._hardgate_rows(rows, "")["F-HG2"]

    assert gate["status"] == "fail"
    assert gate["shape_failures"] == ["theorem-1"]


def test_f_hg3_report_text_has_no_forbidden_theorem_bound_wording():
    payload = _payload()
    report_text = runner.render_markdown(payload).lower()

    assert payload["hardgates"]["F-HG3"]["status"] == "pass"
    assert payload["hardgates"]["F-HG3"]["hits"] == []
    for term in runner.FORBIDDEN_THEOREM_BOUND_WORDING:
        assert term not in report_text


def test_f_hg3_fails_for_forbidden_theorem_bound_wording():
    gate = runner._hardgate_rows(_rows(), "This row claims a full proof and says the bound is proven.")

    assert gate["F-HG3"]["status"] == "fail"
    assert gate["F-HG3"]["hits"] == ["full proof", "proven"]


def test_f_hg4_literature_used_by_pointer_resolves():
    summary = literature_ledger.validate_literature_ledger(canonical.ROOT)

    assert summary["status"] == "ready"
    assert "lit-lejepa-theorem-ledger" in summary["record_ids"]
    assert summary["failures"] == []


def test_implemented_metrics_are_real_gaussian_ou_lejepa_outputs():
    payload = _payload()
    backend_metrics = set(LeJEPABackendEvidenceAdapter.backend.metrics)
    envelope = run_gaussian_ou_lejepa.run_experiment(
        use_torch=False,
        sample_count=8,
        seed=23,
    )

    assert tuple(payload["metric_catalog"]) == LeJEPABackendEvidenceAdapter.backend.metrics
    assert run_gaussian_ou_lejepa.run_experiment.__name__ == "run_experiment"
    for row in payload["theorem_rows"]:
        for metric in row["implemented_metrics"]:
            assert metric in backend_metrics
            assert metric in envelope.metrics
    assert payload["hardgates"]["metric_resolvability"]["status"] == "pass"


def test_metric_resolvability_fails_for_unknown_metric():
    rows = _rows()
    rows[0]["implemented_metrics"] = ["not_in_gaussian_ou_envelope"]

    gate = runner._hardgate_rows(rows, "")["metric_resolvability"]

    assert gate["status"] == "fail"
    assert gate["metric_failures"] == ["theorem-1:not_in_gaussian_ou_envelope"]


def test_main_returns_nonzero_when_hardgate_fails(tmp_path, monkeypatch, capsys):
    rows = _rows()
    rows[0]["implemented_metrics"] = ["not_in_gaussian_ou_envelope"]
    monkeypatch.setattr(runner, "theorem_rows", lambda: rows)

    exit_code = runner.main(["--root", str(tmp_path), "--run-id", "fixture-fail"])
    written = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    stdout = json.loads(capsys.readouterr().out)

    assert exit_code == 1
    assert written["status"] == "fail"
    assert written["hardgates"]["metric_resolvability"]["status"] == "fail"
    assert stdout == {"run_id": "fixture-fail", "status": "fail"}


def test_discovery_projection_records_theorem_ledger_pointer():
    payload = _payload()
    spec = canonical._specs_by_name()["lejepa-theorem-ledger"]
    row = discovery_map.discovery_row(spec, payload)
    evidence = discovery_map._projection_evidence(spec, payload)

    assert row["discovery_level"] == "D0"
    assert row["projection_status"] == "theorem-ledger-recorded"
    assert row["evidence_pointer"] == "$.theorem_rows"
    assert evidence.projection_status == "theorem-ledger-recorded"
    assert evidence.evidence_pointer == "$.theorem_rows"
    assert discovery_map.pointer_value(payload, "$.theorem_rows") == payload["theorem_rows"]


def test_write_artifacts_and_canonical_registration(tmp_path):
    payload = _payload()

    runner.write_artifacts(payload, root=tmp_path)
    written = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    spec = canonical._specs_by_name()["lejepa-theorem-ledger"]

    assert written == payload
    assert (tmp_path / runner.REPORT_ARTIFACT).exists()
    assert spec.command == ("python3", "scripts/run_lejepa_theorem_ledger.py")
    assert spec.json_artifact == runner.JSON_ARTIFACT
    assert spec.markdown_artifact == runner.REPORT_ARTIFACT
    assert spec.bundle_role == "auxiliary"
    assert spec.scope_pointer == "$.scope"
    assert spec.cost_pointer == "$.source_artifacts.cost_protocol"
    assert spec.not_claimed_pointer == "$.not_claimed"
    assert spec.positive_claim_pointer == "$.positive_claim"
    assert spec.literature_ref_ids == ("lit-lejepa-theorem-ledger",)

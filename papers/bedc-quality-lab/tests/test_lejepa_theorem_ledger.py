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


def test_theorem_rows_embed_resolvable_theorem_dna():
    payload = _payload()

    for index, row in enumerate(payload["theorem_rows"]):
        assert row["theorem_id"] == row["theorem"]
        assert row["theorem_dna_pointer"] == f"$.theorem_rows[{index}].theorem_dna"
        dna = discovery_map.pointer_value(payload, row["theorem_dna_pointer"])
        assert dna == row["theorem_dna"]
        assert tuple(dna) == runner.THEOREM_DNA_REQUIRED_FIELDS
        assert dna["theorem_id"] == row["theorem"]
        assert dna["assumptions"]
        assert dna["ledger_debts"][0]["pointer"] == f"$.theorem_rows[{index}].ledger_debt"
        assert dna["formal_status"] == row["status_projection"]
    assert payload["hardgates"]["theorem_dna_warning"]["status"] == "pass"


def test_missing_theorem_dna_warns_without_failing_ledger_status():
    rows = _rows()
    rows = runner._theorem_rows_with_dna(rows)
    del rows[0]["theorem_dna"]

    hardgates = runner._hardgate_rows(rows, "")

    assert hardgates["F-HG2"]["status"] == "pass"
    assert hardgates["theorem_dna_warning"]["status"] == "warning"
    assert hardgates["theorem_dna_warning"]["warning_rows"][0]["theorem"] == "theorem-1"
    assert runner._overall_status(hardgates) == "pass"


def test_theorem_4_keeps_planning_availability_outside_theorem_closure():
    payload = _payload()
    row = next(row for row in payload["theorem_rows"] if row["theorem"] == "theorem-4")

    assert row["bedc_role"] == "Ledger"
    assert row["implemented_metrics"] == []
    assert "gaussian_ou_dynamics_planning" not in json.dumps(row)
    assert "planning certificate" not in json.dumps(row).lower()
    assert "theorem closure" in " ".join(row["not_implemented"])


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


def test_hermite_degree_boundary_shape_and_owner_pointers_resolve():
    payload = _payload()
    rows = payload["hermite_degree_boundary"]

    assert [row["label"] for row in rows] == ["degree1", "degree2", "degree3+"]
    assert [row["behavioral_boundary"] for row in rows] == [
        "linear latent recovery boundary",
        "quadratic boundary",
        "high-order boundary",
    ]
    for row in rows:
        assert discovery_map.pointer_value(payload, row["scope_pointer"]) == payload["scope"]
        assert discovery_map.pointer_value(payload, row["not_claimed_pointer"]) == payload["not_claimed"]
        theorem_row = discovery_map.pointer_value(payload, row["theorem_bound_pointer"])
        assert theorem_row in payload["theorem_rows"]
        assert theorem_row["bedc_role"] in runner.ALLOWED_ROLES


def test_hermite_degree_boundary_is_gaussian_ou_only_and_not_theorem_closure():
    payload = _payload()
    serialized = json.dumps(payload["hermite_degree_boundary"]).lower()
    sidecar_text = runner._render_hermite_behavior_markdown(payload).lower()

    assert payload["source_artifacts"]["gaussian_ou_runner"] == "scripts/run_gaussian_ou_lejepa.py"
    assert "gaussian-ou" in " ".join(payload["not_claimed"]).lower()
    assert "theorem closure" not in serialized
    assert "terminal verdict" not in serialized
    assert "discovery level" not in serialized
    assert "full proof" not in sidecar_text
    assert "complete proof" not in sidecar_text
    assert "proven" not in sidecar_text


def test_lejepa_derivative_bridge_sidecar_is_pointer_only(tmp_path):
    payload = _payload()

    runner.write_artifacts(payload, root=tmp_path)
    sidecar = json.loads((tmp_path / runner.DERIVATIVE_BRIDGE_JSON_ARTIFACT).read_text(encoding="utf-8"))

    assert sidecar["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert sidecar["owner_report"] == "lejepa-theorem-ledger"
    assert sidecar["owner_artifact"] == runner.JSON_ARTIFACT
    assert sidecar["theorem_rows_pointer"] == f"{runner.JSON_ARTIFACT}:$.theorem_rows"
    assert [row["theorem_bound_pointer"] for row in sidecar["rows"]] == [
        f"{runner.JSON_ARTIFACT}:$.theorem_rows[2]",
        f"{runner.JSON_ARTIFACT}:$.theorem_rows[2]",
        f"{runner.JSON_ARTIFACT}:$.theorem_rows[3]",
    ]
    assert (tmp_path / runner.HERMITE_BEHAVIOR_MARKDOWN_ARTIFACT).exists()


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

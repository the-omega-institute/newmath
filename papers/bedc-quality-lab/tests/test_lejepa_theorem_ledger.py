from __future__ import annotations

import json

from bedc_quality_lab.backends.lejepa import LeJEPABackendEvidenceAdapter
from scripts import literature_ledger
from scripts import run_canonical_reports as canonical
from scripts import run_gaussian_ou_lejepa
from scripts import run_lejepa_theorem_ledger as runner


def _payload():
    return runner.build_payload(generated_at="fixture-time")


def test_f_hg1_role_completeness_and_uniqueness():
    payload = _payload()
    rows = payload["theorem_rows"]

    assert {row["theorem"] for row in rows} == {"theorem-1", "theorem-2", "theorem-3", "theorem-4"}
    assert len(rows) == len({row["theorem"] for row in rows})
    assert all(row["bedc_role"] in runner.ALLOWED_ROLES for row in rows)
    assert all(isinstance(row["bedc_role"], str) for row in rows)
    assert payload["hardgates"]["F-HG1"]["status"] == "pass"


def test_f_hg2_rows_have_metric_list_and_nonempty_not_implemented():
    payload = _payload()

    for row in payload["theorem_rows"]:
        assert isinstance(row["implemented_metrics"], list)
        assert isinstance(row["not_implemented"], list)
        assert row["not_implemented"]
        assert row["ledger_debt"]
    assert payload["hardgates"]["F-HG2"]["status"] == "pass"


def test_f_hg3_report_text_has_no_forbidden_theorem_bound_wording():
    payload = _payload()
    report_text = runner.render_markdown(payload).lower()

    assert payload["hardgates"]["F-HG3"]["status"] == "pass"
    assert payload["hardgates"]["F-HG3"]["hits"] == []
    for term in runner.FORBIDDEN_THEOREM_BOUND_WORDING:
        assert term not in report_text


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

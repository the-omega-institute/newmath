import json

from scripts import run_gap_head_mechanism_namecert as runner


def _capsule(root):
    path = root / "reports/canonical/gap_head_attribution_capsule.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "artifact_id": "gap_head_attribution_capsule",
                "run_id": "fixture",
                "mechanism_case": {
                    "case": "Case 2",
                    "candidate_mechanism": "probe-margin-channel",
                    "status": "D5-O retained, mechanism = probe-margin-channel",
                    "failed_gate": "A1-HG3",
                    "what_was_learned": "score_plus_margin remains statistically competitive with full.",
                },
                "d5_o": {"status": "ready"},
                "d5_m": {"status": "blocked", "passed": False, "failed_gate": "A1-HG3"},
                "hardgates": {"gates": {"A1-HG3": {"status": "fail"}}},
                "a4_hardgates": {"gates": {"A4-HG5": {"status": "fail"}}},
                "residualized_attribution": {"status": "pass"},
                "score_margin_causal_evidence": {"channel_classification": "score_margin_sufficient"},
            }
        )
        + "\n",
        encoding="utf-8",
    )


def test_producer_reads_a1_source_and_writes_target_artifacts(tmp_path):
    _capsule(tmp_path)

    payload = runner.write_gap_head_mechanism_namecert(root=tmp_path, generated_at="fixture-time")

    assert (tmp_path / runner.JSON_ARTIFACT).exists()
    assert (tmp_path / runner.REPORT_ARTIFACT).exists()
    written = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    assert written["generated_at"] == "fixture-time"
    assert payload["source_artifacts"]["a1_capsule"] == "reports/canonical/gap_head_attribution_capsule.json"
    assert payload["mechanism_spec"]["candidate_mechanism"] == "probe-margin-channel"
    assert payload["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"


def test_optional_source_absence_fails_closed_as_missing_or_partial(tmp_path):
    _capsule(tmp_path)

    payload = runner.build_gap_head_mechanism_namecert(root=tmp_path, generated_at="fixture-time")

    optional = payload["source_spec"]["optional_sources"]
    assert optional["operational"]["status"] == "missing"
    assert optional["ablation"]["status"] == "missing"
    assert optional["robustness"]["status"] == "missing"
    assert payload["ablation_spec"]["status"] == "missing"
    assert payload["stability_spec"]["status"] == "missing"
    assert payload["closure_status"]["mechanism_spec"] == "partial"
    assert payload["ledger_policy"]["mechanism_closure_debt"] == "open"
    assert "A4-HG5" in payload["ledger_policy"]["blocking_cells"]


def test_missing_a1_source_fails_closed_without_writing_upstream_artifact(tmp_path):
    capsule_path = tmp_path / "reports/canonical/gap_head_attribution_capsule.json"

    payload = runner.write_gap_head_mechanism_namecert(root=tmp_path, generated_at="fixture-time")

    assert not capsule_path.exists()
    assert (tmp_path / runner.JSON_ARTIFACT).exists()
    assert (tmp_path / runner.REPORT_ARTIFACT).exists()
    assert payload["source_spec"]["canonical_source"]["status"] == "missing"
    assert payload["closure_status"]["source_spec"] == "partial"
    assert payload["closure_status"]["mechanism_spec"] == "partial"
    assert payload["ledger_policy"]["mechanism_closure_debt"] == "open"
    assert payload["audit"]["d5_m_ready"] is False


def test_markdown_renders_from_json_payload(tmp_path):
    _capsule(tmp_path)
    payload = runner.write_gap_head_mechanism_namecert(root=tmp_path, generated_at="fixture-time")

    markdown = (tmp_path / runner.REPORT_ARTIFACT).read_text(encoding="utf-8")

    assert "Gap-Head MechanismNameCert Candidate" in markdown
    assert payload["name"] in markdown
    assert "$.closure_status.mechanism_spec" in markdown

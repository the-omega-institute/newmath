import json

import pytest

from scripts import run_canonical_reports as canonical


ARTIFACT = "reports/canonical/minimal_irreducible_causal_derivative_mainline.json"
MARKDOWN = "reports/canonical/minimal_irreducible_causal_derivative_mainline.md"
FINGERPRINT = "reports/canonical/minimal_irreducible_causal_derivative_mainline.fingerprint.json"


def _set_tmp_root(monkeypatch, tmp_path):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")


def _write_json(root, artifact, payload):
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")


def _write_source_fixtures(root):
    fixtures = {
        "reports/canonical/discovery-gated-transformer.json": {
            "claim_capsule_ref": {"artifact": "reports/runs/discovery-gated-transformer/claim_capsule.json", "pointer": "$"},
            "evidence_envelope_ref": {"artifact": "reports/runs/discovery-gated-transformer/evidence_envelope.json", "pointer": "$"},
            "hardgate": {"status": "pass"},
            "not_claimed": ["bounded DGT fixture"],
        },
        "reports/runs/discovery-gated-transformer/claim_capsule.json": {"schema_id": "claim-capsule"},
        "reports/runs/discovery-gated-transformer/evidence_envelope.json": {"schema_id": "evidence-envelope"},
        "reports/canonical/derivative_order_ledger.json": {"entries": [{"route": "dgt"}], "status": "present"},
        "reports/canonical/boundary_causal_derivative_schema.json": {"schema_id": "boundary-causal-derivative", "status": "present"},
        "reports/canonical/causal_patch_suite.json": {"hardgates": {"status": "pass"}, "not_claimed": ["bounded patch fixture"]},
        "reports/canonical/irreducibility_report.json": {
            "hardgate": {"status": "pass"},
            "not_claimed": ["bounded irreducibility fixture"],
        },
        "reports/canonical/discovery_negative_witness_summary.json": {"status": "pointer-only", "rows": []},
        "reports/canonical/dgt-l0-controls.json": {"l0_toy_projection": {"status": "scoped-boundary"}},
        "reports/canonical/dgt-l1-controls.json": {"l1_tiny_sequence_projection": {"status": "pass"}},
        "reports/canonical/dgt-neural-ablation.json": {"nabl_hardgates": {"status": "pass"}},
        "reports/canonical/dgt-ablation-null-decomposition.json": {"hardgates": {"status": "pass"}},
        "reports/canonical/dgt-component-redundancy-audit.json": {"component_redundancy_audit": {"status": "pass"}},
        "reports/canonical/dgt-base-undertraining-audit.json": {"base_undertraining_audit": {"status": "pass"}},
        "reports/canonical/model-comparison.json": {"status": "pass", "comparisons": []},
        "reports/canonical/mechanism_dna.json": {"hardgate": {"status": "pass"}, "rows": []},
        "reports/canonical/new_model_hardgates.json": {"gates": {"NEW-MODEL-HG1": {"status": "pass"}}},
        "reports/canonical/claim_graph.json": {"status": "pass", "nodes": []},
    }
    for artifact, payload in fixtures.items():
        _write_json(root, artifact, payload)


def _walk(value):
    if isinstance(value, dict):
        yield value
        for nested in value.values():
            yield from _walk(nested)
    elif isinstance(value, list):
        for nested in value:
            yield from _walk(nested)


def test_mainline_spec_is_registered_as_pointer_only_auxiliary():
    spec = canonical._specs_by_name()["minimal-irreducible-causal-derivative-mainline"]

    assert spec.command == ("python3", "scripts/run_canonical_reports.py")
    assert spec.json_artifact == ARTIFACT
    assert spec.markdown_artifact == MARKDOWN
    assert canonical._relative(canonical._fingerprint_path(spec)) == FINGERPRINT
    assert spec.bundle_role == "auxiliary"
    assert spec.claim_promotion_eligible is False
    assert spec.positive_claim_pointer == "$.candidate_status"
    assert spec.no_control_rationale_pointer == "$.not_claimed"


def test_mainline_generation_writes_pointer_only_artifacts(tmp_path, monkeypatch):
    _set_tmp_root(monkeypatch, tmp_path)
    _write_source_fixtures(tmp_path)
    spec = canonical._specs_by_name()["minimal-irreducible-causal-derivative-mainline"]

    payload = canonical.run_reports(
        only="minimal-irreducible-causal-derivative-mainline",
        cold=True,
        generated_at="2030-01-01T00:00:00+00:00",
    )

    report = json.loads((tmp_path / ARTIFACT).read_text(encoding="utf-8"))
    markdown = (tmp_path / MARKDOWN).read_text(encoding="utf-8")
    fingerprint = json.loads((tmp_path / FINGERPRINT).read_text(encoding="utf-8"))
    assert payload["reports"][0]["name"] == spec.name
    assert report["schema_id"] == "bedc-quality-lab:minimal-irreducible-causal-derivative-mainline"
    assert report["artifact_role"] == "runner_local_pointer_only_read_model"
    assert report["candidate_status"]["status"] in {"admissible-pointer-present", "blocked-missing-pointer"}
    assert report["claim_authority"] == "none"
    assert report["verdict_authority"] == "none"
    assert "最小不可约因果导数层级" in markdown
    assert "negative results" in markdown
    assert "not claimed" in markdown
    assert fingerprint["report_name"] == spec.name

    encoded = json.dumps(report, ensure_ascii=False, sort_keys=True)
    forbidden_fragments = (
        "terminal_verdict",
        "ClaimVerdict",
        "gh issue close",
        "gh issue create",
        ".refactor-loop",
        "host.env",
        "child_fingerprint",
        "parent_tracking",
    )
    for fragment in forbidden_fragments:
        assert fragment not in encoded
    for node in _walk(report):
        if "artifact" in node or "owner_pointer" in node:
            assert "metrics" not in node
            assert "raw_measurements" not in node
        for key in ("artifact", "pointer", "owner_pointer", "summary_pointer"):
            if key in node:
                value = node[key]
                assert isinstance(value, str)
                if key == "artifact":
                    assert value.startswith("reports/")
                elif key == "pointer":
                    assert value.startswith("$")
                else:
                    artifact, pointer = value.split(":", 1)
                    assert artifact.startswith("reports/")
                    assert pointer.startswith("$")


@pytest.mark.parametrize(
    "mutation",
    [
        {"candidate_status": {"terminal_verdict": "pass"}},
        {"evidence_rows": [{"metrics": {"accuracy": 1.0}}]},
        {"source_refs": [{"artifact": ".refactor-loop/host.env", "pointer": "$"}]},
        {"child_artifacts": [{"parent_tracking_comment": "track child"}]},
        {"lifecycle_commands": ["gh issue close 1002"]},
    ],
)
def test_mainline_validator_rejects_forbidden_authority_and_body_shapes(tmp_path, monkeypatch, mutation):
    _set_tmp_root(monkeypatch, tmp_path)
    _write_source_fixtures(tmp_path)
    payload = canonical._build_minimal_irreducible_causal_derivative_mainline_payload(
        generated_at="2030-01-01T00:00:00+00:00"
    )
    payload.update(mutation)

    with pytest.raises(ValueError):
        canonical._validate_minimal_irreducible_causal_derivative_mainline_payload(payload)


def test_mainline_changed_mode_reruns_when_pointer_source_disappears(tmp_path, monkeypatch):
    _set_tmp_root(monkeypatch, tmp_path)
    _write_source_fixtures(tmp_path)

    first = canonical.run_reports(
        only="minimal-irreducible-causal-derivative-mainline",
        cold=True,
        generated_at="2030-01-01T00:00:00+00:00",
    )
    (tmp_path / "reports/canonical/causal_patch_suite.json").unlink()
    second = canonical.run_reports(
        only="minimal-irreducible-causal-derivative-mainline",
        generated_at="2030-01-01T00:00:00+00:00",
    )
    report = json.loads((tmp_path / ARTIFACT).read_text(encoding="utf-8"))

    assert first["reports"][0]["producer_status"] == "completed"
    assert second["reports"][0]["producer_status"] == "completed"
    assert second["reports"][0]["fingerprint_status"] == "written"
    assert report["candidate_status"]["status"] == "blocked-missing-pointer"
    assert any(row["status"] == "missing" for row in report["source_refs"])

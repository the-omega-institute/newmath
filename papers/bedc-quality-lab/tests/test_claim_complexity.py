import json

import pytest

from bedc_quality_lab.claim_complexity import (
    ARTIFACT_ID,
    DIMENSION_NAMES,
    ROW_KEYS,
    TOP_LEVEL_KEYS,
    build_claim_complexity_payload,
    render_claim_complexity_markdown,
    resolve_claim_verdict_ref,
    validate_claim_complexity_payload,
)
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer


def _write_json(path, payload):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")


def _fixture_root(tmp_path, *, level="D5-M", include_verdict=True):
    canonical = tmp_path / "reports" / "canonical"
    canonical.mkdir(parents=True)
    _write_json(
        canonical / "discovery_map.json",
        {
            "rows": [
                {
                    "report": "demo",
                    "json_artifact": "reports/canonical/demo.json",
                    "markdown_artifact": "reports/canonical/demo.md",
                    "discovery_level": level,
                    "projection_status": "projected",
                    "classifier_reasons": ["fixture"],
                    "evidence_pointer": "$.positive_claim",
                    "control_pointer": "$.control",
                    "adversarial_pointer": "reports/canonical/witnesses.json:$.witnesses",
                    "scorecard_pointer": "reports/canonical/quality-scorecard.json:$.rows",
                }
            ]
        },
    )
    _write_json(canonical / "demo.json", {"positive_claim": True, "control": {"status": "pass"}})
    _write_json(canonical / "witnesses.json", {"witnesses": []})
    if include_verdict:
        (canonical / "claim_verdicts.jsonl").write_text(
            json.dumps(
                {
                    "claim_id": "claim:demo",
                    "claim_graph_node_id": "terminal:demo",
                    "claim_verdict": "accepted_positive_discovery",
                    "reason": "fixture",
                    "source": "reports/canonical/demo.json:$.positive_claim",
                    "ledger_pointer": "reports/canonical/discovery_map.json:$.rows[0].discovery_level",
                    "scorecard_pointer": "reports/canonical/quality-scorecard.json:$.rows",
                    "scorecard_hash": "hash",
                    "scorecard_ready": True,
                    "formal_hardening_ready": True,
                },
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
    return tmp_path


def test_claim_complexity_payload_has_exact_artifact_schema(tmp_path):
    root = _fixture_root(tmp_path)

    payload = build_claim_complexity_payload(root, "fixture-time")
    row = payload["rows"][0]

    assert frozenset(payload) == TOP_LEVEL_KEYS
    assert payload["artifact_id"] == ARTIFACT_ID
    assert frozenset(row) == ROW_KEYS
    assert [dimension["name"] for dimension in row["scoring_dimensions"]] == list(DIMENSION_NAMES)
    assert all(frozenset(dimension) == {"name", "weight", "evidence_pointer"} for dimension in row["scoring_dimensions"])
    assert validate_claim_complexity_payload(root, payload) == []


def test_claim_complexity_score_is_deterministic_dimension_sum(tmp_path):
    root = _fixture_root(tmp_path)

    first = build_claim_complexity_payload(root, "fixture-time")
    second = build_claim_complexity_payload(root, "fixture-time")
    row = first["rows"][0]

    assert first == second
    assert row["complexity_score"] == sum(dimension["weight"] for dimension in row["scoring_dimensions"])


def test_claim_complexity_evidence_and_verdict_refs_resolve(tmp_path):
    root = _fixture_root(tmp_path)
    payload = build_claim_complexity_payload(root, "fixture-time")
    row = payload["rows"][0]

    assert all(resolve_artifact_pointer(root, dimension["evidence_pointer"]) is not None for dimension in row["scoring_dimensions"])
    verdict = resolve_claim_verdict_ref(root, row["pointer_only_verdict_ref"])
    assert verdict["claim_verdict"] == "accepted_positive_discovery"


def test_claim_complexity_does_not_copy_verdict_payload_keys(tmp_path):
    root = _fixture_root(tmp_path)
    row = build_claim_complexity_payload(root, "fixture-time")["rows"][0]

    assert "claim_verdict" not in row
    assert "reason" not in row
    assert "source" not in row
    assert "ledger_pointer" not in row


def test_claim_complexity_d5m_required_dimensions_fail_closed(tmp_path):
    root = _fixture_root(tmp_path, level="D5-M")
    payload = build_claim_complexity_payload(root, "fixture-time")
    payload["rows"][0]["scoring_dimensions"] = payload["rows"][0]["scoring_dimensions"][:-1]
    payload["rows"][0]["complexity_score"] = sum(d["weight"] for d in payload["rows"][0]["scoring_dimensions"])

    errors = validate_claim_complexity_payload(root, payload)

    assert any("six dimensions" in error for error in errors)


def test_claim_complexity_d4_passes_without_promotion_authority(tmp_path):
    root = _fixture_root(tmp_path, level="D4")
    payload = build_claim_complexity_payload(root, "fixture-time")

    assert payload["hardgates"]["CC-HG3"]["status"] == "pass"
    assert payload["hardgates"]["CC-HG3"]["d4_row_count"] == 1
    assert payload["rows"][0]["not_claimed"].startswith("Complexity score is artifact-only evidence")


def test_claim_complexity_rejects_host_local_refs(tmp_path):
    root = _fixture_root(tmp_path)
    payload = build_claim_complexity_payload(root, "fixture-time")
    payload["not_claimed"].append(".refactor-loop/host.env")

    assert "host-local reference is forbidden" in validate_claim_complexity_payload(root, payload)


def test_claim_complexity_missing_verdict_ref_fails_closed(tmp_path):
    root = _fixture_root(tmp_path, include_verdict=False)

    with pytest.raises(ValueError, match="claim verdict ref missing"):
        build_claim_complexity_payload(root, "fixture-time")


def test_claim_complexity_markdown_is_pointer_only(tmp_path):
    root = _fixture_root(tmp_path)
    payload = build_claim_complexity_payload(root, "fixture-time")
    markdown = render_claim_complexity_markdown(payload)

    assert "reports/canonical/claim_verdicts.jsonl:$.lines[0]" in markdown
    assert "accepted_positive_discovery" not in markdown

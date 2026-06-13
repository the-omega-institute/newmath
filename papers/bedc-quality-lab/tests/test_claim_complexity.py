import json

import pytest

from bedc_quality_lab.claim_complexity import (
    ARTIFACT_ID,
    CLAIM_VERDICTS_ARTIFACT,
    DISCOVERY_MAP_ARTIFACT,
    DIMENSION_NAMES,
    ROW_KEYS,
    TOP_LEVEL_KEYS,
    build_claim_complexity_payload,
    render_claim_complexity_markdown,
    resolve_claim_verdict_ref,
    validate_claim_complexity_payload,
)
from bedc_quality_lab import claim_complexity
from bedc_quality_lab.discovery_compiler.anti_triviality import owner_local_anti_triviality_contract
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from bedc_quality_lab.evidence_provenance import evidence_provenance_pointer_for_report
from scripts import run_claim_complexity_score


def _write_json(path, payload):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")


def _anti_triviality_contract(level):
    return {
        "anti_triviality_status": "pass",
        "owner_contract": {
            "scale_only": {"status": "present"},
            "metadata_only": {"status": "present"},
            "matched_random": {"status": "present"},
            "forbidden_column": {"status": "present"},
        },
    } | owner_local_anti_triviality_contract(
        recommended_level=level,
        scale_only_pointer="$.owner_contract.scale_only",
        metadata_only_pointer="$.owner_contract.metadata_only",
        matched_random_pointer="$.owner_contract.matched_random",
        forbidden_column_pointer="$.owner_contract.forbidden_column",
    )


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
                    "audit_status": "valid",
                    "audit_reason": "",
                    "classifier_reasons": ["fixture"],
                    "evidence_pointer": "$.positive_claim",
                    "evidence_type": "deterministic_projection",
                    "evidence_provenance_pointer": evidence_provenance_pointer_for_report("demo"),
                    "control_pointer": "$.control",
                    "adversarial_pointer": "reports/canonical/witnesses.json:$.witnesses",
                    "scorecard_pointer": "reports/canonical/quality-scorecard.json:$.rows",
                }
            ]
        },
    )
    _write_json(canonical / "demo.json", {"positive_claim": True, "control": {"status": "pass"}} | _anti_triviality_contract(level))
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


def test_claim_complexity_weights_cover_every_level_specific_branch():
    base_row = {
        "evidence_pointer": "$.positive_claim",
        "scorecard_pointer": "$.scorecard",
        "control_pointer": "$.control",
        "robustness_pointer": "$.robustness",
        "adversarial_pointer": "$.adversarial",
        "negative_report_pointer": "$.negative",
        "terminal_verdict": "accepted",
    }
    expected_by_level = {
        "D0": {
            "assumption_complexity": 0,
            "proof_burden": 0,
            "evidence_burden": 3,
            "backend_coupling": 2,
            "witness_exposure": 2,
            "revocation_fragility": 1,
        },
        "D1": {
            "assumption_complexity": 1,
            "proof_burden": 0,
            "evidence_burden": 3,
            "backend_coupling": 2,
            "witness_exposure": 2,
            "revocation_fragility": 1,
        },
        "D2": {
            "assumption_complexity": 2,
            "proof_burden": 1,
            "evidence_burden": 3,
            "backend_coupling": 2,
            "witness_exposure": 2,
            "revocation_fragility": 1,
        },
        "D3": {
            "assumption_complexity": 3,
            "proof_burden": 1,
            "evidence_burden": 3,
            "backend_coupling": 2,
            "witness_exposure": 2,
            "revocation_fragility": 1,
        },
        "D4": {
            "assumption_complexity": 4,
            "proof_burden": 2,
            "evidence_burden": 3,
            "backend_coupling": 2,
            "witness_exposure": 2,
            "revocation_fragility": 1,
        },
        "D5-O": {
            "assumption_complexity": 5,
            "proof_burden": 2,
            "evidence_burden": 3,
            "backend_coupling": 2,
            "witness_exposure": 2,
            "revocation_fragility": 1,
        },
        "D5-M": {
            "assumption_complexity": 6,
            "proof_burden": 2,
            "evidence_burden": 3,
            "backend_coupling": 2,
            "witness_exposure": 2,
            "revocation_fragility": 1,
        },
        "DN": {
            "assumption_complexity": 2,
            "proof_burden": 0,
            "evidence_burden": 3,
            "backend_coupling": 2,
            "witness_exposure": 2,
            "revocation_fragility": 2,
        },
        "DR": {
            "assumption_complexity": 3,
            "proof_burden": 0,
            "evidence_burden": 3,
            "backend_coupling": 2,
            "witness_exposure": 2,
            "revocation_fragility": 2,
        },
    }

    for level, expected in expected_by_level.items():
        row = dict(base_row, discovery_level=level)

        actual = {name: claim_complexity._weight_for(name, row) for name in DIMENSION_NAMES}

        assert actual == expected


def test_claim_complexity_evidence_and_verdict_refs_resolve(tmp_path):
    root = _fixture_root(tmp_path)
    payload = build_claim_complexity_payload(root, "fixture-time")
    row = payload["rows"][0]

    assert all(resolve_artifact_pointer(root, dimension["evidence_pointer"]) is not None for dimension in row["scoring_dimensions"])
    verdict = resolve_claim_verdict_ref(root, row["pointer_only_verdict_ref"])
    assert verdict["claim_verdict"] == "accepted_positive_discovery"


def test_claim_complexity_dimension_pointer_uses_local_artifact_pointer():
    row = {"json_artifact": "reports/canonical/demo.json", "evidence_pointer": "$.positive_claim"}

    assert (
        claim_complexity._dimension_pointer("evidence_burden", 7, row)
        == "reports/canonical/demo.json:$.positive_claim"
    )


def test_claim_complexity_dimension_pointer_keeps_qualified_cross_artifact_witness_pointer():
    row = {
        "json_artifact": "reports/canonical/demo.json",
        "adversarial_pointer": "reports/canonical/witnesses.json:$.witnesses[0]",
    }

    assert (
        claim_complexity._dimension_pointer("witness_exposure", 3, row)
        == "reports/canonical/witnesses.json:$.witnesses[0]"
    )


def test_claim_complexity_dimension_pointer_uses_classifier_reasons_when_present():
    row = {"json_artifact": "reports/canonical/demo.json", "classifier_reasons": ["fixture"]}

    assert (
        claim_complexity._dimension_pointer("proof_burden", 2, row)
        == f"{DISCOVERY_MAP_ARTIFACT}:$.rows[2].classifier_reasons"
    )


def test_claim_complexity_dimension_pointer_falls_back_to_discovery_map_row():
    row = {"json_artifact": "reports/canonical/demo.json"}

    assert (
        claim_complexity._dimension_pointer("proof_burden", 5, row)
        == f"{DISCOVERY_MAP_ARTIFACT}:$.rows[5]"
    )
    assert (
        claim_complexity._dimension_pointer("witness_exposure", 5, row)
        == f"{DISCOVERY_MAP_ARTIFACT}:$.rows[5]"
    )


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


@pytest.mark.parametrize(
    ("mutate", "message"),
    [
        (lambda row: row.pop("evidence_type"), "requires owner evidence_type"),
        (lambda row: row.update({"evidence_type": None}), "requires owner evidence_type"),
        (
            lambda row: row.update(
                {
                    "evidence_provenance_pointer": (
                        "reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.missing"
                    )
                }
            ),
            "requires owner evidence provenance pointer",
        ),
    ],
)
def test_claim_complexity_validates_committed_discovery_map_before_consuming(tmp_path, mutate, message):
    root = _fixture_root(tmp_path)
    path = root / DISCOVERY_MAP_ARTIFACT
    payload = json.loads(path.read_text(encoding="utf-8"))
    mutate(payload["rows"][0])
    _write_json(path, payload)

    with pytest.raises(ValueError, match=message):
        build_claim_complexity_payload(root, "fixture-time")


def test_claim_complexity_markdown_is_pointer_only(tmp_path):
    root = _fixture_root(tmp_path)
    payload = build_claim_complexity_payload(root, "fixture-time")
    markdown = render_claim_complexity_markdown(payload)

    assert "reports/canonical/claim_verdicts.jsonl:$.lines[0]" in markdown
    assert "accepted_positive_discovery" not in markdown


def test_write_claim_complexity_score_writes_json_and_markdown(tmp_path):
    root = _fixture_root(tmp_path)

    payload = run_claim_complexity_score.write_claim_complexity_score(root=root, generated_at="fixture-time")

    json_artifact = root / run_claim_complexity_score.JSON_ARTIFACT
    markdown_artifact = root / run_claim_complexity_score.MARKDOWN_ARTIFACT
    assert json_artifact.exists()
    assert markdown_artifact.exists()
    assert json.loads(json_artifact.read_text(encoding="utf-8")) == payload
    markdown = markdown_artifact.read_text(encoding="utf-8")
    assert "# Claim Complexity" in markdown
    assert f"{CLAIM_VERDICTS_ARTIFACT}:$.lines[0]" in markdown


def test_write_claim_complexity_score_fails_on_hardgate_failure(tmp_path, monkeypatch):
    root = _fixture_root(tmp_path)
    real_build = run_claim_complexity_score.build_claim_complexity_payload

    def build_payload_with_failure(base, timestamp):
        payload = real_build(base, timestamp)
        payload["hardgates"]["CC-HG1"]["status"] = "fail"
        return payload

    monkeypatch.setattr(run_claim_complexity_score, "build_claim_complexity_payload", build_payload_with_failure)

    with pytest.raises(SystemExit, match="claim complexity hardgate failed: CC-HG1"):
        run_claim_complexity_score.write_claim_complexity_score(root=root, generated_at="fixture-time")

    assert (root / run_claim_complexity_score.JSON_ARTIFACT).exists()
    assert (root / run_claim_complexity_score.MARKDOWN_ARTIFACT).exists()

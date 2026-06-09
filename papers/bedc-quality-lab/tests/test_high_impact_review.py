import json
from copy import deepcopy
from pathlib import Path

from bedc_quality_lab import high_impact_review as hir


GENERATED_AT = "2030-01-01T00:00:00+00:00"


def _write_json(root: Path, artifact: str, payload) -> None:
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")


def _base_dgt_payload() -> dict[str, object]:
    return {
        "artifact_id": "bedc-quality-lab:discovery-gated-transformer",
        "model_id": "discovery-gated-transformer",
        "d4_projection": {
            "discovery_level": "D4",
            "readiness": "ready",
            "scope": "bounded deterministic toy D4 prototype",
        },
        "not_claimed": [
            "Bounded deterministic toy evidence only.",
            "No production deployment authority.",
            "No universal training recipe claim.",
            "No external verdict ownership.",
        ],
    }


def _model_row(model_id: str, *, quality_q: float, uer_reduction: float, shift_count: float) -> dict[str, object]:
    return {
        "model_id": model_id,
        "metrics": {
            "quality_q": {"status": "resolved", "value": quality_q},
            "UER_reduction": {"status": "resolved", "value": uer_reduction},
            "classifier_shift_count": {"status": "resolved", "value": shift_count},
        },
    }


def _base_model_comparison() -> dict[str, object]:
    return {
        "status": "ready",
        "readiness": {"status": "ready", "failed_gates": []},
        "models": [
            _model_row("dgt", quality_q=0.76, uer_reduction=0.33, shift_count=2.0),
            _model_row("base_transformer", quality_q=0.50, uer_reduction=0.03, shift_count=0.0),
            _model_row("matched_random_structural_control", quality_q=0.44, uer_reduction=0.01, shift_count=0.0),
        ],
        "hardgates": {
            f"MC-HG{index}": {"status": "pass", "reason": "fixture"}
            for index in range(1, 11)
        },
    }


def _base_claim_graph() -> dict[str, object]:
    return {
        "nodes": [
            {
                "node_id": "raw:discovery-gated-transformer",
                "node_type": "raw_evidence",
                "source_pointer": "reports/canonical/discovery-gated-transformer.json:$.d4_projection",
                "discovery_level": None,
                "terminal_verdict": None,
                "depends_on": [],
                "not_claimed": [],
            },
            {
                "node_id": "projected:discovery-gated-transformer",
                "node_type": "projected_discovery",
                "source_pointer": "reports/canonical/discovery_map.json:$.rows[0]",
                "discovery_level": "D4",
                "terminal_verdict": None,
                "depends_on": ["raw:discovery-gated-transformer"],
                "not_claimed": [],
            },
            {
                "node_id": "terminal:discovery-gated-transformer",
                "node_type": "terminal_claim",
                "source_pointer": "reports/canonical/claim_verdicts.jsonl:$.lines[0]",
                "discovery_level": None,
                "terminal_verdict": "projected_discovery_required",
                "depends_on": ["projected:discovery-gated-transformer"],
                "not_claimed": [],
            },
        ]
    }


def _fixture_root(tmp_path: Path) -> Path:
    _write_json(tmp_path, hir.DGT_ARTIFACT, _base_dgt_payload())
    _write_json(tmp_path, hir.MODEL_COMPARISON_ARTIFACT, _base_model_comparison())
    _write_json(tmp_path, hir.CLAIM_GRAPH_ARTIFACT, _base_claim_graph())
    return tmp_path


def _payload(root: Path) -> dict[str, object]:
    return hir.build_high_impact_review_payload(root, generated_at=GENERATED_AT)


def _assert_single_failed_gate(payload: dict[str, object], gate_id: str) -> None:
    gates = payload["hardgates"]
    assert gates[gate_id]["status"] == "fail"
    assert payload["review_rows"][0]["status"] == "fail"
    assert payload["review_rows"][0]["reason"] == "high-impact-review-required"
    assert hir.validate_high_impact_review_payload(payload, Path(payload["_root"])) == []


def test_high_impact_review_pass_payload_has_owner_schema(tmp_path):
    root = _fixture_root(tmp_path)

    payload = _payload(root)

    assert payload["schema_id"] == "bedc-quality-lab:high-impact-review"
    assert payload["artifact_id"] == "bedc-quality-lab:high-impact-review"
    assert payload["review_rows"][0]["claim_id"] == "claim:discovery-gated-transformer"
    assert payload["review_rows"][0]["status"] == "pass"
    assert payload["review_rows"][0]["reason"] == "positive-discovery-gates-pass"
    assert list(payload["hardgates"]) == [f"HIR-HG{index}" for index in range(1, 11)]
    assert hir.validate_high_impact_review_payload(payload, root) == []


def test_hir_hg1_bounded_d4_scope_missing_fails_closed(tmp_path):
    root = _fixture_root(tmp_path)
    payload = json.loads((root / hir.DGT_ARTIFACT).read_text(encoding="utf-8"))
    payload["d4_projection"]["readiness"] = "blocked"
    _write_json(root, hir.DGT_ARTIFACT, payload)

    review = _payload(root)

    assert review["hardgates"]["HIR-HG1"]["status"] == "fail"
    assert review["review_rows"][0]["status"] == "fail"


def test_hir_hg2_boundary_missing_production_nonclaim_fails_closed(tmp_path):
    root = _fixture_root(tmp_path)
    payload = json.loads((root / hir.DGT_ARTIFACT).read_text(encoding="utf-8"))
    payload["not_claimed"] = ["No universal training recipe claim."]
    _write_json(root, hir.DGT_ARTIFACT, payload)

    review = _payload(root)

    assert review["hardgates"]["HIR-HG2"]["status"] == "fail"


def test_hir_hg3_production_claim_fails_closed(tmp_path):
    root = _fixture_root(tmp_path)
    payload = json.loads((root / hir.DGT_ARTIFACT).read_text(encoding="utf-8"))
    payload["d4_projection"]["claim"] = "production deployment authority"
    _write_json(root, hir.DGT_ARTIFACT, payload)

    review = _payload(root)

    assert review["hardgates"]["HIR-HG3"]["status"] == "fail"


def test_hir_hg4_llm_replacement_claim_fails_closed(tmp_path):
    root = _fixture_root(tmp_path)
    payload = json.loads((root / hir.DGT_ARTIFACT).read_text(encoding="utf-8"))
    payload["claim"] = "LLM replacement"
    _write_json(root, hir.DGT_ARTIFACT, payload)

    review = _payload(root)

    assert review["hardgates"]["HIR-HG4"]["status"] == "fail"


def test_hir_hg5_global_superiority_claim_fails_closed(tmp_path):
    root = _fixture_root(tmp_path)
    payload = json.loads((root / hir.DGT_ARTIFACT).read_text(encoding="utf-8"))
    payload["claim"] = "global superiority"
    _write_json(root, hir.DGT_ARTIFACT, payload)

    review = _payload(root)

    assert review["hardgates"]["HIR-HG5"]["status"] == "fail"


def test_hir_hg6_model_comparison_not_ready_fails_closed(tmp_path):
    root = _fixture_root(tmp_path)
    payload = json.loads((root / hir.MODEL_COMPARISON_ARTIFACT).read_text(encoding="utf-8"))
    payload["status"] = "not_ready"
    payload["hardgates"]["MC-HG1"]["status"] = "fail"
    _write_json(root, hir.MODEL_COMPARISON_ARTIFACT, payload)

    review = _payload(root)

    assert review["hardgates"]["HIR-HG6"]["status"] == "fail"


def test_hir_hg7_dgt_does_not_beat_base_fails_closed(tmp_path):
    root = _fixture_root(tmp_path)
    payload = json.loads((root / hir.MODEL_COMPARISON_ARTIFACT).read_text(encoding="utf-8"))
    payload["models"][0]["metrics"]["quality_q"]["value"] = 0.49
    _write_json(root, hir.MODEL_COMPARISON_ARTIFACT, payload)

    review = _payload(root)

    assert review["hardgates"]["HIR-HG7"]["status"] == "fail"


def test_hir_hg8_dgt_does_not_beat_matched_random_fails_closed(tmp_path):
    root = _fixture_root(tmp_path)
    payload = json.loads((root / hir.MODEL_COMPARISON_ARTIFACT).read_text(encoding="utf-8"))
    payload["models"][0]["metrics"]["UER_reduction"]["value"] = 0.005
    _write_json(root, hir.MODEL_COMPARISON_ARTIFACT, payload)

    review = _payload(root)

    assert review["hardgates"]["HIR-HG8"]["status"] == "fail"


def test_hir_hg9_matched_random_shift_nonzero_fails_closed(tmp_path):
    root = _fixture_root(tmp_path)
    payload = json.loads((root / hir.MODEL_COMPARISON_ARTIFACT).read_text(encoding="utf-8"))
    payload["models"][2]["metrics"]["classifier_shift_count"]["value"] = 1.0
    _write_json(root, hir.MODEL_COMPARISON_ARTIFACT, payload)

    review = _payload(root)

    assert review["hardgates"]["HIR-HG9"]["status"] == "fail"


def test_hir_hg10_claim_graph_path_missing_fails_closed(tmp_path):
    root = _fixture_root(tmp_path)
    payload = json.loads((root / hir.CLAIM_GRAPH_ARTIFACT).read_text(encoding="utf-8"))
    payload["nodes"][2]["depends_on"] = ["raw:discovery-gated-transformer"]
    _write_json(root, hir.CLAIM_GRAPH_ARTIFACT, payload)

    review = _payload(root)

    assert review["hardgates"]["HIR-HG10"]["status"] == "fail"


def test_hir_reason_field_inconsistent_fails_validation(tmp_path):
    root = _fixture_root(tmp_path)
    payload = deepcopy(_payload(root))
    payload["review_rows"][0]["reason"] = "projected-discovery-required"

    errors = hir.validate_high_impact_review_payload(payload, root)

    assert any("review row reason mismatch" in error for error in errors)

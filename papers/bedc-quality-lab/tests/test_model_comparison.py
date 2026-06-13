import copy
import json
from pathlib import Path
import shutil

import pytest

from bedc_quality_lab.discovery_compiler.capsule import require_architecture_claim_capsule
from bedc_quality_lab.model_comparison import (
    DGT_CONTROL_SEMANTIC_POINTER,
    SEMANTIC_POINTER,
    validate_model_comparison_payload,
)
from bedc_quality_lab.schema import QualityEvidenceEnvelope
from scripts import run_canonical_reports as canonical

CONTROL_MODEL_IDS = set(canonical.MODEL_COMPARISON_CONTROL_MODEL_IDS)


def _root(tmp_path):
    shutil.copytree(Path(__file__).resolve().parents[1] / "configs", tmp_path / "configs", dirs_exist_ok=True)
    return tmp_path


def _payload(tmp_path):
    root = _root(tmp_path)
    _write_model_comparison_owner_index(root)
    original_root = canonical.ROOT
    original_dir = canonical.CANONICAL_DIR
    try:
        canonical.ROOT = root
        canonical.CANONICAL_DIR = root / "reports" / "canonical"
        payload = canonical._build_model_comparison(
            generated_at="2030-01-01T00:00:00+00:00",
            write_owner_artifacts=True,
        )
        canonical._write_json_atomic(root / canonical.MODEL_COMPARISON_JSON_ARTIFACT, payload)
        (root / canonical.MODEL_COMPARISON_MARKDOWN_ARTIFACT).parent.mkdir(parents=True, exist_ok=True)
        (root / canonical.MODEL_COMPARISON_MARKDOWN_ARTIFACT).write_text(
            canonical._render_model_comparison_markdown(payload),
            encoding="utf-8",
        )
        return root, payload
    finally:
        canonical.ROOT = original_root
        canonical.CANONICAL_DIR = original_dir


def _write_model_comparison_owner_index(root: Path) -> None:
    path = root / "reports/canonical/index.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema_id": "bedc-quality-lab:canonical-report-index",
        "evidence_provenance": {
            "schema_id": "bedc-quality-lab:evidence-provenance",
            "owner": "bedc_quality_lab.evidence_provenance",
            "generated_at": "fixture",
            "producer_audits": [
                {
                    "report": "model-comparison",
                    "producer_command": ["python3", "scripts/run_model_comparison.py"],
                    "producer_source_pointer": "scripts/run_model_comparison.py",
                    "backward_pointers": [],
                    "optimizer_step_pointers": [],
                    "parameter_update_pointers": [],
                    "training_evidence_status": "training_evidence_absent",
                    "not_claimed": ["fixture"],
                }
            ],
            "metric_rows": [
                {
                    "report": "model-comparison",
                    "metric_name": "headline",
                    "source_type": "deterministic_projection",
                    "source_code_pointer": "scripts/run_model_comparison.py",
                    "source_artifact_pointer": "reports/canonical/model-comparison.json:$.hardgates.MC-HG7",
                    "producer_training_audit_pointer": "reports/canonical/index.json:$.evidence_provenance.producer_audits[0]",
                    "allowed_for_empirical_claim": False,
                    "value": {"status": "pass"},
                    "not_claimed": ["fixture"],
                    "not_measurable_reason": None,
                }
            ],
            "discovery_rows": [
                {
                    "report": "model-comparison",
                    "evidence_type": "deterministic_projection",
                    "discovery_map_pointer": None,
                    "metric_provenance_pointers": ["reports/canonical/index.json:$.evidence_provenance.metric_rows[0]"],
                    "producer_training_audit_pointer": "reports/canonical/index.json:$.evidence_provenance.producer_audits[0]",
                    "allowed_claim_kinds": ["projection_only"],
                    "not_claimed": ["fixture"],
                }
            ],
            "discovery_rows_by_report": {
                "model-comparison": {
                    "report": "model-comparison",
                    "evidence_type": "deterministic_projection",
                    "discovery_map_pointer": None,
                    "metric_provenance_pointers": ["reports/canonical/index.json:$.evidence_provenance.metric_rows[0]"],
                    "producer_training_audit_pointer": "reports/canonical/index.json:$.evidence_provenance.producer_audits[0]",
                    "allowed_claim_kinds": ["projection_only"],
                    "not_claimed": ["fixture"],
                }
            },
            "hardgate_status": {},
            "artifact_pointers": {"owner_pointer": "reports/canonical/index.json:$.evidence_provenance"},
        },
    }
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")


def test_model_comparison_generates_two_control_owners(tmp_path):
    _root, payload = _payload(tmp_path)
    owners = {row["model_id"]: row for row in payload["models"] if row["model_id"] in CONTROL_MODEL_IDS}

    assert set(owners) == {"dgt", "base_transformer", "matched_random_structural_control"}
    assert owners["base_transformer"]["owner_status"] == "resolved"
    assert owners["matched_random_structural_control"]["owner_status"] == "resolved"
    assert owners["dgt"]["architecture_role"] == "DGT source row"


def test_controls_share_surface_and_metric_sets(tmp_path):
    _root, payload = _payload(tmp_path)
    control_rows = [row for row in payload["models"] if row["model_id"] in CONTROL_MODEL_IDS]
    surface_sets = {tuple(row["surfaces"]) for row in control_rows}
    metric_sets = {tuple(row["metrics"]) for row in control_rows}

    assert surface_sets == {canonical.MODEL_COMPARISON_SURFACES}
    assert len(next(iter(surface_sets))) == 9
    assert metric_sets == {canonical.MODEL_COMPARISON_METRIC_KEYS}
    assert len(next(iter(metric_sets))) == 12


def test_matched_random_is_dgt_shaped_but_random_and_shift_zero(tmp_path):
    _root, payload = _payload(tmp_path)
    rows = {row["model_id"]: row for row in payload["models"]}
    dgt = rows["dgt"]
    matched = rows["matched_random_structural_control"]

    assert matched["parameter_count"] == dgt["parameter_count"]
    assert matched["compute_budget"] == dgt["compute_budget"]
    assert matched["surfaces"] == dgt["surfaces"]
    assert "random gap/certificate/ledger" in matched["training_role"]
    assert matched["metrics"]["classifier_shift_count"]["value"] == 0.0


def test_evidence_envelopes_validate_and_point_only(tmp_path):
    root, payload = _payload(tmp_path)

    for owner in payload["models"]:
        if owner["model_id"] not in CONTROL_MODEL_IDS:
            continue
        envelope = QualityEvidenceEnvelope.read_json(root / owner["evidence_envelope"])
        assert envelope.run_id == f"model-comparison-{owner['model_id']}"
        assert all(" " not in ref for ref in envelope.bedc_refs)


def test_claim_capsules_are_architecture_capsules_without_terminal_verdict(tmp_path):
    root, payload = _payload(tmp_path)

    for owner in payload["models"]:
        if owner["model_id"] not in CONTROL_MODEL_IDS:
            continue
        capsule = json.loads((root / owner["claim_capsule"]).read_text(encoding="utf-8"))
        require_architecture_claim_capsule(capsule)
        assert "terminal_verdict" not in capsule


@pytest.mark.parametrize(
    ("mutation", "gate_id"),
    [
        (lambda rows: rows.pop(), "MC-HG1"),
        (lambda rows: rows[0].update({"evidence_envelope": "reports/runs/model-comparison/missing/evidence_envelope.json"}), "MC-HG2"),
        (lambda rows: rows[1].update({"surfaces": rows[1]["surfaces"][:-1]}), "MC-HG3"),
        (lambda rows: rows[1]["metrics"].pop("cost"), "MC-HG4"),
        (lambda rows: rows[1].update({"parameter_count": rows[0]["parameter_count"] + 1}), "MC-HG5"),
        (lambda rows: rows[1].update({"compute_budget": rows[0]["compute_budget"] + 1.0}), "MC-HG6"),
        (lambda rows: rows[0]["metrics"]["quality_q"].update({"value": rows[1]["metrics"]["quality_q"]["value"] - 0.1}), "MC-HG7"),
        (lambda rows: rows[0]["metrics"]["UER_reduction"].update({"value": rows[2]["metrics"]["UER_reduction"]["value"] - 0.1}), "MC-HG8"),
        (lambda rows: rows[2]["metrics"]["classifier_shift_count"].update({"value": 1.0}), "MC-HG9"),
        (lambda rows: rows[0].update({"not_claimed": ["toy only"]}), "MC-HG10"),
    ],
)
def test_mc_hardgates_fail_closed_on_missing_owner_or_source(tmp_path, mutation, gate_id):
    root, payload = _payload(tmp_path)
    rows = [
        copy.deepcopy(row)
        for row in payload["models"]
        if row["model_id"] in CONTROL_MODEL_IDS
    ]
    mutation(rows)

    gates = canonical._model_comparison_hardgates(rows, root=root)

    assert gates[gate_id]["status"] == "fail"


def test_mc_hg7_hg8_compare_dgt_ci_low_and_uer_reduction(tmp_path):
    _root, payload = _payload(tmp_path)

    assert payload["hardgates"]["MC-HG7"]["status"] == "pass"
    assert payload["hardgates"]["MC-HG8"]["status"] == "pass"
    rows = {row["model_id"]: row for row in payload["models"]}
    assert rows["dgt"]["metrics"]["quality_q"]["value"] > rows["base_transformer"]["metrics"]["quality_q"]["value"]
    assert rows["dgt"]["metrics"]["UER_reduction"]["value"] > rows["matched_random_structural_control"]["metrics"]["UER_reduction"]["value"]


def test_forbidden_inference_and_negative_witness_sweep_are_required(tmp_path):
    _root, payload = _payload(tmp_path)
    text = json.dumps(payload, sort_keys=True)

    assert "production" in text
    assert "global model superiority" in text
    assert "negative_witness" in payload["models"][0]["surfaces"]
    assert payload["hardgates"]["MC-HG10"]["status"] == "pass"


def test_model_comparison_projection_semantic_is_owner_backed(tmp_path):
    _root, payload = _payload(tmp_path)
    row = payload["comparisons"][0]
    semantic = row["semantic"]

    assert row["comparison_id"] == "dgt_control_projection"
    assert semantic["comparison_type"] == "deterministic_projection"
    assert semantic["training_status"] == "not_trained"
    assert semantic["metric_provenance"] == "deterministic_projection"
    assert semantic["allowed_evidence_chain"] is False
    assert semantic["evidence_type_pointer"] == "reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.model-comparison"
    assert payload["hardgates"]["MC-HG11"]["status"] == "pass"
    assert payload["hardgates"]["MC-HG13"]["status"] == "pass"
    assert SEMANTIC_POINTER == "reports/canonical/model-comparison.json:$.comparisons[*].semantic"
    assert DGT_CONTROL_SEMANTIC_POINTER == "reports/canonical/model-comparison.json:$.comparisons[0].semantic"


@pytest.mark.parametrize(
    ("field", "value", "message"),
    [
        ("comparison_type", "unknown", "comparison_type"),
        ("metric_provenance", "measured_training", "metric_provenance must not be measured_training"),
        ("training_status", "trained", "training_status must not be trained"),
        ("allowed_evidence_chain", True, "allowed_evidence_chain must be false"),
        ("evidence_type_pointer", "reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.missing", "evidence_type_pointer unresolved"),
    ],
)
def test_model_comparison_semantic_mutations_fail_closed(tmp_path, field, value, message):
    root, payload = _payload(tmp_path)
    payload["comparisons"][0]["semantic"][field] = value

    errors = validate_model_comparison_payload(payload, root=root)

    assert any(message in error for error in errors)


def test_model_comparison_semantic_rows_are_stable(tmp_path):
    _root, first = _payload(tmp_path)
    _root, second = _payload(tmp_path)

    assert first["comparisons"] == second["comparisons"]

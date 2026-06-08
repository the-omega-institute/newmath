import copy
import json
from pathlib import Path
import shutil

import pytest

from bedc_quality_lab import model_comparison
from bedc_quality_lab.discovery_compiler.capsule import require_architecture_claim_capsule
from bedc_quality_lab.schema import QualityEvidenceEnvelope


def _root(tmp_path):
    shutil.copytree(Path(__file__).resolve().parents[1] / "configs", tmp_path / "configs")
    return tmp_path


def _payload(tmp_path):
    return model_comparison.write_report(root=_root(tmp_path), generated_at="2030-01-01T00:00:00+00:00")


def test_model_comparison_generates_two_control_owners(tmp_path):
    payload = _payload(tmp_path)
    owners = {row["model_id"]: row for row in payload["models"]}

    assert set(owners) == {"dgt", "base_transformer", "matched_random_structural_control"}
    assert owners["base_transformer"]["owner_status"] == "resolved"
    assert owners["matched_random_structural_control"]["owner_status"] == "resolved"
    assert owners["dgt"]["architecture_role"] == "DGT source row"


def test_controls_share_surface_and_metric_sets(tmp_path):
    payload = _payload(tmp_path)
    surface_sets = {tuple(row["surfaces"]) for row in payload["models"]}
    metric_sets = {tuple(row["metrics"]) for row in payload["models"]}

    assert surface_sets == {model_comparison.SURFACES}
    assert len(next(iter(surface_sets))) == 9
    assert metric_sets == {model_comparison.METRIC_KEYS}
    assert len(next(iter(metric_sets))) == 12


def test_matched_random_is_dgt_shaped_but_random_and_shift_zero(tmp_path):
    payload = _payload(tmp_path)
    rows = {row["model_id"]: row for row in payload["models"]}
    dgt = rows["dgt"]
    matched = rows["matched_random_structural_control"]

    assert matched["parameter_count"] == dgt["parameter_count"]
    assert matched["compute_budget"] == dgt["compute_budget"]
    assert matched["surfaces"] == dgt["surfaces"]
    assert "random gap/certificate/ledger" in matched["training_role"]
    assert matched["metrics"]["classifier_shift_count"]["value"] == 0.0


def test_evidence_envelopes_validate_and_point_only(tmp_path):
    root = _root(tmp_path)
    payload = model_comparison.write_report(root=root, generated_at="2030-01-01T00:00:00+00:00")

    for owner in payload["models"]:
        envelope = QualityEvidenceEnvelope.read_json(root / owner["evidence_envelope"])
        assert envelope.run_id == f"model-comparison-{owner['model_id']}"
        assert all(" " not in ref for ref in envelope.bedc_refs)


def test_claim_capsules_are_architecture_capsules_without_terminal_verdict(tmp_path):
    root = _root(tmp_path)
    payload = model_comparison.write_report(root=root, generated_at="2030-01-01T00:00:00+00:00")

    for owner in payload["models"]:
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
    payload = _payload(tmp_path)
    rows = copy.deepcopy(payload["models"])
    mutation(rows)

    gates = model_comparison.evaluate_hardgates(rows, root=tmp_path)

    assert gates[gate_id]["status"] == "fail"


def test_mc_hg7_hg8_compare_dgt_ci_low_and_uer_reduction(tmp_path):
    payload = _payload(tmp_path)

    assert payload["hardgates"]["MC-HG7"]["status"] == "pass"
    assert payload["hardgates"]["MC-HG8"]["status"] == "pass"
    rows = {row["model_id"]: row for row in payload["models"]}
    assert rows["dgt"]["metrics"]["quality_q"]["value"] > rows["base_transformer"]["metrics"]["quality_q"]["value"]
    assert rows["dgt"]["metrics"]["UER_reduction"]["value"] > rows["matched_random_structural_control"]["metrics"]["UER_reduction"]["value"]


def test_forbidden_inference_and_negative_witness_sweep_are_required(tmp_path):
    payload = _payload(tmp_path)
    text = json.dumps(payload, sort_keys=True)

    assert "production" in text
    assert "global model superiority" in text
    assert "negative_witness" in payload["models"][0]["surfaces"]
    assert payload["hardgates"]["MC-HG10"]["status"] == "pass"

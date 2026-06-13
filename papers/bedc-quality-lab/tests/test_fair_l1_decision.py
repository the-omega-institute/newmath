import json

import pytest

from bedc_quality_lab import fair_l1_decision as fair
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from scripts import run_canonical_reports as canonical
from scripts import run_fair_l1_decision as runner


ROOT = fair.LAB_ROOT


def _copy_source(root, artifact):
    target = root / artifact
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes((ROOT / artifact).read_bytes())


def _write_sources(root):
    for artifact in (
        fair.DGT_L1_CONTROLS_ARTIFACT,
        fair.DGT_BASE_UNDERTRAINING_ARTIFACT,
        fair.INPUT_ACCESSIBILITY_ARTIFACT,
        "reports/canonical/order-k-benchmark.json",
    ):
        _copy_source(root, artifact)


def _payload(root):
    _write_sources(root)
    return fair.build_payload(root=root, generated_at="fixture-time")


def _read_json(root, artifact):
    return json.loads((root / artifact).read_text(encoding="utf-8"))


def _write_json(root, artifact, payload):
    path = root / artifact
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_eligible_sources(root):
    _write_sources(root)
    l1 = _read_json(root, fair.DGT_L1_CONTROLS_ARTIFACT)
    l1["l1_tiny_sequence_projection"]["ood_generalization_claim"] = "bounded-mechanism-evidence"
    l1["l1_step_ladder"]["status"] = "pass"
    l1["l1_step_ladder"]["verdict"] = "information-starved-catches-up"
    l1["l1_ood_mechanism"]["verdict"] = "partial-rule"
    _write_json(root, fair.DGT_L1_CONTROLS_ARTIFACT, l1)

    base = _read_json(root, fair.DGT_BASE_UNDERTRAINING_ARTIFACT)
    construct = base["base_undertraining_audit"]["construct_validity"]
    construct["status"] = "construct-valid"
    construct["baseline_input_order"] = construct["label_dependency_order"]
    rows = base["base_undertraining_audit"]["comparison_rows"]
    by_id = {row["comparison_id"]: row for row in rows}
    if "equal_validation_loss" not in by_id:
        rows.append(
            {
                "comparison_id": "equal_validation_loss",
                "status": "resolved",
                "source_artifact": fair.DGT_L1_CONTROLS_ARTIFACT,
                "source_pointer": (
                    f"{fair.DGT_L1_CONTROLS_ARTIFACT}:"
                    "$.l1_step_ladder.per_step[0].metrics.information_starved_validation_loss_mean"
                ),
                "match_axis": "validation_loss",
                "match_value": 1.0,
                "base_metric": 0.4,
                "dgt_metric": 0.8,
                "ci_overlap": False,
                "ci_low_separation": 0.4,
                "decision": "noninformative-dgt-separated",
            }
        )
    for row in rows:
        row["status"] = "resolved"
    construct.setdefault("input_accessibility_preconditions", {})["baseline_row"] = {
        "status": "pass",
        "row_pointer": "reports/canonical/input-accessibility.json#row_id=59a87f14e31796e4",
        "missing_variables": [],
        "information_starved": False,
    }
    _write_json(root, fair.DGT_BASE_UNDERTRAINING_ARTIFACT, base)

    accessibility = _read_json(root, fair.INPUT_ACCESSIBILITY_ARTIFACT)
    for row in accessibility["rows"]:
        if (
            row["experiment"] == "dgt_l1_tiny_sequence"
            and row["split"] == "in_distribution"
            and row["arm"] == "information_starved_l1_baseline"
            and row["role"] == "fairness-control"
        ):
            row["visible_variables"] = list(row["required_variables"])
            row["missing_variables"] = []
            row["coverage_status"] = "pass"
            row["information_starved"] = False
            row["supports_architecture_claim"] = True
    accessibility["consumer_pointers"]["information_starved_arms_ref"] = [
        pointer
        for pointer in accessibility["consumer_pointers"]["information_starved_arms_ref"]
        if not pointer.endswith("59a87f14e31796e4")
    ]
    _write_json(root, fair.INPUT_ACCESSIBILITY_ARTIFACT, accessibility)


def test_fair_l1_decision_projects_bounded_negative_from_current_l1_evidence(tmp_path):
    payload = _payload(tmp_path)

    assert payload["decision"]["allowed_statuses"] == ["blocked", "bounded-negative", "scaling-evidence-eligible"]
    assert payload["decision"]["status"] == "bounded-negative"
    assert payload["ladder_state_projection"]["allowed_states"] == [
        "l1-scaling-blocked",
        "l1-bounded-negative",
        "l1-scaling-evidence-eligible",
    ]
    assert payload["ladder_state_projection"]["state"] == "l1-bounded-negative"
    assert payload["hardgates"]["FAIR-L1-HG1"]["status"] == "pass"
    assert payload["hardgates"]["FAIR-L1-HG3"]["status"] == "fail"
    assert payload["hardgates"]["FAIR-L1-HG7"]["status"] == "fail"
    assert payload["hardgates"]["FAIR-L1-HG6"]["status"] == "fail"
    assert [row["comparison_id"] for row in payload["fair_alignment"]["comparison_rows"]] == list(fair.REQUIRED_COMPARISONS)
    validation = payload["fair_alignment"]["comparison_rows"][-1]
    assert validation["comparison_id"] == "equal-validation-loss"
    assert validation["match_axis"] == "validation_loss"
    assert validation["owner_row_pointer"].startswith(fair.BASE_AUDIT_POINTER)
    assert any(row["gate_id"] == "FAIR-L1-HG3" for row in payload["boundary_ledger"])
    assert "unblocked" not in json.dumps(payload, sort_keys=True)
    assert "scoped-boundary" not in json.dumps(payload, sort_keys=True)


def test_fair_l1_decision_projects_scaling_evidence_eligible_from_resolved_sources(tmp_path):
    _write_eligible_sources(tmp_path)
    payload = fair.build_payload(root=tmp_path, generated_at="fixture-time")

    assert {gate_id: row["status"] for gate_id, row in payload["hardgates"].items()} == {
        gate_id: "pass" for gate_id in fair.HARDGATE_IDS
    }
    assert payload["decision"]["status"] == "scaling-evidence-eligible"
    assert payload["decision"]["failed_gate"] is None
    assert payload["decision"]["hardgate_status"] == "pass"
    assert payload["ladder_state_projection"]["state"] == "l1-scaling-evidence-eligible"
    assert payload["boundary_ledger"] == []
    assert payload["fair_alignment"]["comparison_rows"][-1]["source_pointer"].startswith(fair.DGT_L1_CONTROLS_ARTIFACT)

    fair.write_artifacts(payload, root=tmp_path, generated_at="fixture-time")
    capsule = payload["decision"]["claim_capsule"]
    assert capsule["status"] == "pointer-only"
    for pointer in capsule["evidence_pointers"] + capsule["projection_pointers"]:
        assert resolve_artifact_pointer(tmp_path, pointer) is not None


def test_fair_l1_decision_missing_source_blocks_instead_of_stub(tmp_path):
    _write_sources(tmp_path)
    (tmp_path / fair.DGT_L1_CONTROLS_ARTIFACT).unlink()
    payload = fair.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["decision"]["status"] == "blocked"
    assert payload["ladder_state_projection"]["state"] == "l1-scaling-blocked"
    assert payload["hardgates"]["FAIR-L1-HG1"]["status"] == "fail"
    assert payload["source_artifacts"]["l1_projection"]["status"] == "missing"


def test_fair_l1_comparison_rows_project_from_base_undertraining_owner(tmp_path):
    _write_sources(tmp_path)
    base = _read_json(tmp_path, fair.DGT_BASE_UNDERTRAINING_ARTIFACT)
    rows = base["base_undertraining_audit"]["comparison_rows"]
    rows[:] = [
        {
            "comparison_id": "equal_validation_loss",
            "status": "resolved",
            "source_artifact": fair.DGT_L1_CONTROLS_ARTIFACT,
            "source_pointer": (
                f"{fair.DGT_L1_CONTROLS_ARTIFACT}:"
                "$.l1_step_ladder.per_step[0].metrics.information_starved_validation_loss_mean"
            ),
            "match_axis": "validation_loss",
            "match_value": 1.0,
            "base_metric": 0.4,
            "dgt_metric": 0.8,
            "ci_overlap": False,
            "ci_low_separation": 0.4,
            "decision": "owner-row",
        }
    ]
    _write_json(tmp_path, fair.DGT_BASE_UNDERTRAINING_ARTIFACT, base)

    payload = fair.build_payload(root=tmp_path, generated_at="fixture-time")
    rows = payload["fair_alignment"]["comparison_rows"]

    assert [row["comparison_id"] for row in rows] == list(fair.REQUIRED_COMPARISONS)
    assert rows[-1]["comparison_id"] == "equal-validation-loss"
    assert rows[-1]["status"] == "resolved"
    assert rows[-1]["decision"] == "owner-row"
    assert rows[-1]["owner_row_pointer"] == f"{fair.BASE_AUDIT_POINTER}.comparison_rows[0]"
    assert rows[-1]["source_pointer"].endswith(".metrics.information_starved_validation_loss_mean")
    assert rows[0]["status"] == "missing"


def test_fair_l1_claim_capsule_is_pointer_only(tmp_path):
    payload = _payload(tmp_path)
    capsule = payload["decision"]["claim_capsule"]
    text = json.dumps(capsule, sort_keys=True)

    assert capsule["status"] == "pointer-only"
    assert f"{fair.CANONICAL_JSON_ARTIFACT}:$.ladder_state_projection" in capsule["projection_pointers"]
    assert all(isinstance(pointer, str) and ":" in pointer for pointer in capsule["evidence_pointers"])
    assert "comparison_rows" not in text
    assert "construct_validity_projection" not in text
    assert "fair_alignment" not in text


def test_fair_l1_decision_cli_writes_canonical_artifacts(tmp_path, capsys):
    _write_sources(tmp_path)

    assert runner.main(["--root", str(tmp_path), "--generated-at", "fixture-time"]) == 0
    summary = json.loads(capsys.readouterr().out)
    payload = json.loads((tmp_path / fair.CANONICAL_JSON_ARTIFACT).read_text(encoding="utf-8"))

    assert summary["artifact_id"] == fair.ARTIFACT_ID
    assert summary["status"] == payload["decision"]["status"] == "bounded-negative"
    assert summary["ladder_state"] == payload["ladder_state_projection"]["state"] == "l1-bounded-negative"
    assert (tmp_path / fair.CANONICAL_MARKDOWN_ARTIFACT).exists()
    assert not (tmp_path / fair.CANONICAL_FINGERPRINT_ARTIFACT).exists()


def test_fair_l1_decision_canonical_spec_is_unique_and_before_consumers():
    specs = [spec for spec in canonical.CANONICAL_REPORTS if spec.name == "fair-l1-decision"]
    names = [spec.name for spec in canonical.CANONICAL_REPORTS]

    assert len(specs) == 1
    spec = specs[0]
    assert spec.bundle_role == "auxiliary"
    assert spec.command == ("python3", "scripts/run_fair_l1_decision.py")
    assert spec.json_artifact == fair.CANONICAL_JSON_ARTIFACT
    assert spec.markdown_artifact == fair.CANONICAL_MARKDOWN_ARTIFACT
    assert spec.required_json_keys.count("ladder_state_projection") == 1
    assert names.index("dgt-l1-controls") < names.index("fair-l1-decision")
    assert names.index("dgt-base-undertraining-audit") < names.index("fair-l1-decision")
    assert names.index("fair-l1-decision") < names.index("discovery-gated-transformer")


def test_fair_l1_decision_rejects_public_alias_mutation(tmp_path):
    payload = _payload(tmp_path)
    payload["decision"]["status"] = "unblocked"

    with pytest.raises(ValueError, match="status domain"):
        fair.validate_payload(payload, root=tmp_path)

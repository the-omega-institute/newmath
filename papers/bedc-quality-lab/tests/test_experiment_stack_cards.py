import json
import shutil
from pathlib import Path

from bedc_quality_lab.experiment_stack import (
    CONSISTENCY_GATE_IDS,
    EXPERIMENT_STACK_CARDS,
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    build_experiment_stack_payload,
    validate_experiment_stack_specs,
    write_experiment_stack_cards,
)


EXPECTED_OWNER_ROWS = {
    "claim-card": {
        "owner_pointer": "reports/runs/discovery-gated-transformer/claim_capsule.json:$",
        "source_pointer": "reports/runs/discovery-gated-transformer/claim_capsule.json:$.owner_ref",
        "summary_pointer": "reports/runs/discovery-gated-transformer/claim_capsule.json:$.claim_scope",
        "demotion_rule_pointer": "reports/canonical/discovery-gated-transformer.json:$.not_claimed",
    },
    "task-target-card": {
        "owner_pointer": "reports/canonical/discovery-gated-transformer.json:$",
        "source_pointer": "reports/canonical/discovery-gated-transformer.json:$.d4_projection.matched_control",
        "summary_pointer": "reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.source_projection",
        "demotion_rule_pointer": "reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.boundary_ledger",
    },
    "data-card": {
        "owner_pointer": "reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer",
        "source_pointer": "reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer",
        "summary_pointer": "reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer.evidence_type",
        "demotion_rule_pointer": "reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer.not_claimed",
    },
    "feature-access-card": {
        "owner_pointer": "reports/canonical/dgt-l1-controls.json:$",
        "source_pointer": "reports/canonical/dgt-l1-controls.json:$.training_arms",
        "summary_pointer": "reports/canonical/dgt-l1-controls.json:$.review_status",
        "demotion_rule_pointer": "reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection",
    },
    "baseline-validity-card": {
        "owner_pointer": "reports/canonical/dgt-l1-boundary-report.json:$",
        "source_pointer": "reports/canonical/dgt-l1-boundary-report.json:$.base_bayes_ceiling",
        "summary_pointer": "reports/canonical/dgt-l1-boundary-report.json:$.feature_reachability",
        "demotion_rule_pointer": "reports/canonical/dgt-l1-boundary-report.json:$.claim_promotion_exclusion",
    },
    "ood-solvability-card": {
        "owner_pointer": "reports/canonical/dgt-l1-boundary-report.json:$",
        "source_pointer": "reports/canonical/dgt-l1-boundary-report.json:$.ood_solvability",
        "summary_pointer": "reports/canonical/dgt-l1-boundary-report.json:$.feature_reachability",
        "demotion_rule_pointer": "reports/canonical/dgt-l1-boundary-report.json:$.not_claimed",
    },
    "metric-provenance-card": {
        "owner_pointer": "reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer.metric_provenance_pointers[0]",
        "source_pointer": "reports/canonical/index.json:$.evidence_provenance.metric_rows[30]",
        "summary_pointer": "reports/canonical/index.json:$.evidence_provenance.metric_rows[30].source_type",
        "demotion_rule_pointer": "reports/canonical/index.json:$.evidence_provenance.metric_rows[30].not_claimed",
    },
    "training-authenticity-card": {
        "owner_pointer": "reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer.producer_training_audit_pointer",
        "source_pointer": "reports/canonical/index.json:$.evidence_provenance.producer_audits[30]",
        "summary_pointer": "reports/canonical/index.json:$.evidence_provenance.producer_audits[30].training_evidence_status",
        "demotion_rule_pointer": "reports/canonical/index.json:$.evidence_provenance.producer_audits[30].not_claimed",
    },
    "statistical-evidence-card": {
        "owner_pointer": "reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer.metric_provenance_pointers[0]",
        "source_pointer": "reports/canonical/index.json:$.evidence_provenance.metric_rows[30]",
        "summary_pointer": (
            "reports/canonical/index.json:$.evidence_provenance.metric_rows[30].allowed_for_empirical_claim, "
            "reports/canonical/index.json:$.evidence_provenance.metric_rows[30].source_type"
        ),
        "demotion_rule_pointer": "reports/canonical/index.json:$.evidence_provenance.metric_rows[30].not_claimed",
    },
    "ablation-causal-evidence-card": {
        "owner_pointer": "reports/canonical/dgt-neural-ablation.json:$",
        "source_pointer": "reports/canonical/dgt-neural-ablation.json:$.boundary_ledger",
        "summary_pointer": "reports/canonical/dgt-neural-ablation.json:$.nabl_hardgates.status",
        "demotion_rule_pointer": "reports/canonical/dgt-neural-ablation.json:$.not_claimed",
    },
    "artifact-reproducibility-card": {
        "owner_pointer": "reports/release_manifest_sidecar.json:$",
        "source_pointer": "reports/release_manifest_sidecar.json:$.required_pointers",
        "summary_pointer": "reports/release_manifest_sidecar.json:$.release_bundle_status",
        "demotion_rule_pointer": "reports/release_manifest_sidecar.json:$.revoke_if",
    },
    "model-card": {
        "owner_pointer": "reports/canonical/dgt-model-card.json:$",
        "source_pointer": "reports/canonical/dgt-model-card.json:$.intended_use",
        "summary_pointer": "reports/canonical/dgt-model-card.json:$.card_hardgates.status",
        "demotion_rule_pointer": "reports/canonical/dgt-model-card.json:$.not_claimed",
    },
    "risk-scope-review-card": {
        "owner_pointer": "reports/canonical/dgt-l1-boundary-report.json:$",
        "source_pointer": "reports/canonical/dgt-l1-boundary-report.json:$.claim_promotion_exclusion",
        "summary_pointer": "reports/canonical/dgt-l1-boundary-report.json:$.boundary_decision",
        "demotion_rule_pointer": "reports/canonical/dgt-l1-boundary-report.json:$.not_claimed",
    },
    "release-readiness-board": {
        "owner_pointer": "reports/canonical/reproduction-package.json:$",
        "source_pointer": "reports/canonical/reproduction-package.json:$.reproduction_targets",
        "summary_pointer": "reports/canonical/reproduction-package.json:$.hardgates",
        "demotion_rule_pointer": "reports/canonical/reproduction-package.json:$.hardgates.REPRO-HG5",
    },
}


def _copy_owner_artifacts(root: Path) -> None:
    source_root = Path(".")
    for row in EXPECTED_OWNER_ROWS.values():
        for pointer in (
            row["owner_pointer"],
            row["source_pointer"].split(", ")[0],
            row["summary_pointer"].split(", ")[0],
            row["demotion_rule_pointer"],
        ):
            artifact = pointer.split(":", 1)[0]
            if artifact.startswith("$owner"):
                continue
            source = source_root / artifact
            target = root / artifact
            if source.exists() and not target.exists():
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, target)


def test_all_fourteen_cards_consume_existing_owner_paths():
    assert validate_experiment_stack_specs() == ()
    assert len(EXPERIMENT_STACK_CARDS) == 14
    assert {spec.card_id for spec in EXPERIMENT_STACK_CARDS} == set(EXPECTED_OWNER_ROWS)

    for spec in EXPERIMENT_STACK_CARDS:
        expected = EXPECTED_OWNER_ROWS[spec.card_id]
        assert spec.owner_pointer == expected["owner_pointer"]
        assert "experiment_stack_" not in spec.owner_pointer
        assert not spec.owner_artifact.startswith("reports/canonical/experiment_stack_")


def test_projected_cards_resolve_owner_table_and_do_not_emit_card_artifact_owners():
    payload = build_experiment_stack_payload(root=Path("."), generated_at="fixture")
    rows = {row["card_id"]: row for row in payload["cards"]}

    assert tuple(rows) == tuple(spec.card_id for spec in EXPERIMENT_STACK_CARDS)
    for card_id, expected in EXPECTED_OWNER_ROWS.items():
        row = rows[card_id]
        assert row["owner_pointer"] == expected["owner_pointer"]
        assert row["source_pointer"] == expected["source_pointer"]
        assert row["summary_pointer"] == expected["summary_pointer"]
        assert row["demotion_rule_pointer"] == expected["demotion_rule_pointer"]
        assert not row["owner_artifact"].startswith("reports/canonical/experiment_stack_")
        assert not row["owner_pointer"].startswith("reports/canonical/experiment_stack_")
        assert row["hardgates"]["STACK-HG1"]["status"] in {"pass", "fail"}
        assert row["hardgates"]["STACK-HG2"]["status"] in {"pass", "fail"}


def test_claim_first_gate_is_pointer_only_metadata():
    payload = build_experiment_stack_payload(root=Path("."), generated_at="fixture")
    gate = payload["claim_first_gate"]

    assert gate == {
        "kind": "pointer-only-metadata",
        "status": "delegated",
        "admission_owner": "bedc_quality_lab.claim_acceptance.claim_first_pointer_checks",
        "positive_evidence_owner": "bedc_quality_lab.claim_acceptance.validate_positive_claim_evidence",
        "consistency_gates_pointer": "reports/canonical/claim-artifact-consistency.json:$.gates",
        "consistency_gate_ids": list(CONSISTENCY_GATE_IDS),
    }
    serialized = json.dumps(gate, sort_keys=True)
    assert "decision_function" not in serialized
    assert "evaluate_claim_first_gate" not in serialized
    assert "claim_first_admission" not in serialized
    assert "claim_first_admission_pointer" not in serialized


def test_claim_first_duplicate_execution_surface_is_absent_from_source():
    source = Path("bedc_quality_lab/experiment_stack.py").read_text(encoding="utf-8")

    assert "evaluate_claim_first_gate" not in source
    assert "ClaimFirstGateDecision" not in source


def test_missing_owner_pointer_blocks_card(tmp_path):
    _copy_owner_artifacts(tmp_path)
    (tmp_path / "reports/runs/discovery-gated-transformer/claim_capsule.json").unlink()

    payload = build_experiment_stack_payload(root=tmp_path, generated_at="fixture")
    claim = next(row for row in payload["cards"] if row["card_id"] == "claim-card")

    assert claim["status"] == "blocked"
    assert claim["hardgates"]["STACK-HG1"]["status"] == "fail"
    assert "owner-pointer-unresolved" in claim["failure_reasons"]


def test_owner_status_or_hardgate_mutation_blocks_card(tmp_path):
    _copy_owner_artifacts(tmp_path)
    path = tmp_path / "reports/canonical/dgt-model-card.json"
    payload = json.loads(path.read_text(encoding="utf-8"))
    payload["card_hardgates"]["status"] = "blocked"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    stack = build_experiment_stack_payload(root=tmp_path, generated_at="fixture")
    model = next(row for row in stack["cards"] if row["card_id"] == "model-card")

    assert model["status"] == "blocked"
    assert model["hardgates"]["STACK-HG1"]["status"] == "pass"
    assert model["hardgates"]["STACK-HG2"]["status"] == "fail"
    assert "owner-status-or-hardgate-blocked" in model["failure_reasons"]


def test_regen_idempotent_experiment_stack_cards(tmp_path):
    first = write_experiment_stack_cards(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    first_json = (tmp_path / JSON_ARTIFACT).read_text(encoding="utf-8")
    first_markdown = (tmp_path / MARKDOWN_ARTIFACT).read_text(encoding="utf-8")

    second = write_experiment_stack_cards(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")

    assert second == first
    assert (tmp_path / JSON_ARTIFACT).read_text(encoding="utf-8") == first_json
    assert (tmp_path / MARKDOWN_ARTIFACT).read_text(encoding="utf-8") == first_markdown


def test_standard_alignment_is_pointer_only():
    doc = Path("docs/experiment_stack_standard_alignment.md").read_text(encoding="utf-8")

    for name in ("NeurIPS checklist", "Papers with Code", "ACM artifact badging", "Model Cards", "NIST AI RMF"):
        assert name in doc
    assert JSON_ARTIFACT in doc
    assert "https://" in doc
    assert "we recommend" not in doc.lower()
    assert "must include" not in doc.lower()
    assert "should include" not in doc.lower()
    assert "reproducibility checklist" not in doc.lower()


def test_committed_owner_outcomes_are_fail_closed_without_stub_passes():
    payload = build_experiment_stack_payload(root=Path("."), generated_at="fixture")
    rows = {row["card_id"]: row for row in payload["cards"]}

    assert rows["claim-card"]["status"] == "pass"
    assert rows["feature-access-card"]["status"] == "pass"
    assert rows["artifact-reproducibility-card"]["status"] == "pass"
    assert rows["model-card"]["status"] == "pass"
    assert rows["data-card"]["status"] == "blocked"
    assert rows["training-authenticity-card"]["status"] == "blocked"
    assert rows["statistical-evidence-card"]["status"] == "blocked"
    for row in rows.values():
        if row["status"] == "blocked":
            assert "owner-status-or-hardgate-blocked" in row["failure_reasons"]

import copy
import json
from pathlib import Path

from bedc_quality_lab import dgt_model_card as card
from bedc_quality_lab.construct_validity import ConstructValidityEvidence, construct_validity_projection


def _write_json(root: Path, artifact: str, payload: dict) -> None:
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _construct_validity_evidence() -> ConstructValidityEvidence:
    return ConstructValidityEvidence(
        task_variables={"variables": ["x", "surface"]},
        label_variables={"variables": ["y"]},
        arm_input_access={
            "label_invisibility_certificate": True,
            "arms": {
                "candidate": {"variables": ["x", "surface"]},
                "control": {"variables": ["x", "surface"]},
            },
        },
        arm_roles={"candidate": "candidate", "controls": ["control"]},
        finite_table={"support_count": 16, "rule_abstraction_claim": False, "coverage_status": "bounded-control"},
        hand_feature_ledger={"mode": "shared-gate", "shared_across_arms": True, "features": ["surface"]},
        metric_source={"source_kind": "training-evaluation", "metric_keys": ["accuracy"]},
    )


def _construct_validity_payload(artifact: str, updates: dict | None = None) -> dict:
    payload = _construct_validity_evidence().as_payload()
    if updates:
        payload.update(updates)
    return construct_validity_projection(
        ConstructValidityEvidence.from_payload(payload),
        artifact=artifact,
        pointer="$.construct_validity_hardgates",
    )


def _l1_construct_validity_ledger(updates: dict | None = None) -> dict:
    payload = {
        "status": "pass",
        "failed_gates": [],
        "coverage_bound": {"rule_abstraction_claim": False},
    }
    if updates:
        payload.update(updates)
    return payload


def _source_fixture(root: Path) -> None:
    _write_json(
        root,
        "reports/canonical/dgt-l0-controls.json",
        {
            "construct_validity_hardgates": _construct_validity_payload("reports/canonical/dgt-l0-controls.json"),
            "l0_toy_projection": {
                "status": "pass",
                "review_status": "pass",
                "not_claimed": ["bounded only"],
            }
        },
    )
    _write_json(
        root,
        "reports/canonical/dgt-l1-controls.json",
        {
            "construct_validity_ledger": _l1_construct_validity_ledger(),
            "task_spec": {"task": "tiny-sequence"},
            "training_arms": {"dgt_l1": {"status": "present"}},
            "l1_tiny_sequence_projection": {
                "status": "pass",
                "review_status": "pass",
                "ood_generalization_claim": "not-claimed",
                "ood_boundary": {
                    "chance_accuracy": 0.0625,
                    "dgt_ood_accuracy_ci95_low": 0.06309,
                },
                "boundary_ledger": [{"status": "scoped-boundary"}],
            },
        },
    )
    _write_json(
        root,
        "reports/canonical/fair-l1-decision.json",
        {
            "ladder_state_projection": {
                "state": "l1-bounded-negative",
                "decision_status": "bounded-negative",
                "decision_pointer": "reports/canonical/fair-l1-decision.json:$.decision.status",
                "hardgate_pointer": "reports/canonical/fair-l1-decision.json:$.hardgates",
                "boundary_ledger_pointer": "reports/canonical/fair-l1-decision.json:$.boundary_ledger",
                "not_claimed": ["bounded only"],
            },
        },
    )
    _write_json(
        root,
        "reports/canonical/dgt-base-undertraining-audit.json",
        {
            "base_undertraining_audit": {
                "verdict": "construct-boundary",
                "claim_action": "defer-to-fair-reconstruction",
                "construct_validity": {
                    "status": "construct-boundary",
                    "bayes_upper_bound_accuracy": 0.0625,
                    "source_pointers": {"fair_reconstruction": "https://github.com/the-omega-institute/newmath/issues/1196"},
                },
            }
        },
    )
    _write_json(
        root,
        "reports/canonical/dgt-ablation-null-decomposition.json",
        {
            "null_decomposition": {
                "analysis_status": "pass",
                "verdict": "mixed",
            }
        },
    )
    _write_json(
        root,
        "reports/canonical/discovery-gated-transformer.json",
        {
            "model_id": "discovery-gated-transformer",
            "not_claimed": ["bounded deterministic toy evidence only"],
        },
    )
    _write_json(
        root,
        "reports/canonical/index.json",
        {
            "evidence_provenance": {
                "source_type": "canonical-quality-index",
                "evidence_type": "pointer-owner-provenance",
            },
            "dgt_model_card": {
                "canonical_role": "auxiliary_pointer_projection",
                "card_pointer": "reports/canonical/dgt-model-card.json:$",
                "fingerprint_artifact": "reports/canonical/dgt-model-card.fingerprint.json",
            }
        },
    )


def _build(root: Path) -> dict:
    _source_fixture(root)
    return card.build_dgt_model_card(root=root, generated_at="2030-01-01T00:00:00+00:00")


def _rewrite_source(root: Path, artifact: str, mutator) -> None:
    path = root / artifact
    payload = json.loads(path.read_text(encoding="utf-8"))
    mutator(payload)
    _write_json(root, artifact, payload)


def _construct_boundary(payload: dict, owner: str) -> dict:
    return next(
        row
        for row in payload["evaluation_boundaries"]
        if row["source_owner"] == owner and row["boundary"] == f"{owner} construct validity"
    )


def _errors(payload: dict, root: Path) -> list[str]:
    return [error.gate_id for error in card.validate_dgt_model_card(payload, root)]


def test_not_intended_literals_are_exact(tmp_path):
    payload = _build(tmp_path)
    literals = [row["literal"] for row in payload["not_intended_use"]]

    assert literals == list(card.REQUIRED_NOT_INTENDED_LITERALS)
    assert payload["card_hardgates"]["gates"]["CARD-HG2"]["status"] == "pass"


def test_not_intended_literal_rewrite_fails(tmp_path):
    payload = _build(tmp_path)
    payload["not_intended_use"][3]["literal"] = "not broad Transformer superiority"

    errors = _errors(payload, tmp_path)

    assert "CARD-HG2" in errors


def test_card_numeric_cells_are_pointer_backed(tmp_path):
    payload = _build(tmp_path)
    payload["training_facts"]["metric_cells"].append({"metric": "unowned", "value": 7})

    errors = _errors(payload, tmp_path)

    assert "CARD-HG3" in errors


def test_metric_cell_value_rewrite_fails_against_owner_pointer(tmp_path):
    payload = _build(tmp_path)
    metric = next(
        row
        for row in payload["training_facts"]["metric_cells"]
        if row["metric"] == "dgt_ood_accuracy_ci95_low"
    )
    metric["value"] = 0.99

    errors = [error.as_dict() for error in card.validate_dgt_model_card(payload, tmp_path)]

    assert any(error["gate_id"] == "CARD-HG3" and error["path"] == "$.training_facts.metric_cells[0].value" for error in errors)


def test_failure_mode_status_rewrite_fails_against_owner_pointer(tmp_path):
    payload = _build(tmp_path)
    failure = next(row for row in payload["known_failure_modes"] if row["failure_mode"] == "OOD boundary")
    failure["status"] = "pass-by-hand"

    errors = [error.as_dict() for error in card.validate_dgt_model_card(payload, tmp_path)]

    assert any(error["gate_id"] == "CARD-HG5" and error["path"] == "$.known_failure_modes[3].status" for error in errors)


def test_metric_and_failure_mode_value_drift_is_rejected(tmp_path):
    payload = _build(tmp_path)
    metric = next(
        row
        for row in payload["training_facts"]["metric_cells"]
        if row["metric"] == "dgt_ood_accuracy_ci95_low"
    )
    metric["value"] = 0.99
    ood = next(row for row in payload["known_failure_modes"] if row["failure_mode"] == "OOD boundary")
    ood["status"] = "pass-by-hand"

    errors = [error.as_dict() for error in card.validate_dgt_model_card(payload, tmp_path)]

    assert any(error["path"] == "$.training_facts.metric_cells[0].value" for error in errors)
    assert any(error["path"] == "$.known_failure_modes[3].status" for error in errors)


def test_l0_status_is_derived_from_owner_pointer(tmp_path):
    payload = _build(tmp_path)
    l0 = next(row for row in payload["evaluation_boundaries"] if row["source_owner"] == "dgt-l0-controls")
    l0["status"] = "pass-by-hand"

    errors = _errors(payload, tmp_path)

    assert "CARD-HG4" in errors


def test_l1_construct_invalid_and_fair_decision_are_separate(tmp_path):
    payload = _build(tmp_path)
    fair = next(row for row in payload["evaluation_boundaries"] if row["boundary"] == "fair architecture comparison")

    assert fair["construct_validity_status"] == "construct-boundary"
    assert fair["status"] == "bounded-negative"
    assert fair["ladder_state"] == "l1-bounded-negative"
    assert fair["claim"] == "no architecture advantage"
    assert "architecture advantage" not in json.dumps(payload["intended_use"], sort_keys=True)

    fair["claim"] = "architecture advantage"
    assert "CARD-HG5" in _errors(payload, tmp_path)


def test_owner_derived_status_rewrites_fail_closed(tmp_path):
    payload = _build(tmp_path)

    fair = next(row for row in payload["evaluation_boundaries"] if row["boundary"] == "fair architecture comparison")
    fair["status"] = "pass-by-hand"
    assert "CARD-HG5" in _errors(payload, tmp_path)

    fair["status"] = "bounded-negative"
    fair["ladder_state"] = "pass-by-hand"
    assert "CARD-HG5" in _errors(payload, tmp_path)

    fair["ladder_state"] = "l1-bounded-negative"
    fair_failure = next(row for row in payload["known_failure_modes"] if row["failure_mode"] == "fair comparison boundary")
    fair_failure["status"] = "pass-by-hand"
    assert "CARD-HG5" in _errors(payload, tmp_path)

    fair_failure["status"] = "l1-bounded-negative"
    l1 = next(row for row in payload["evaluation_boundaries"] if row["boundary"] == "L1 scoped review")
    l1["review_status"] = "pass-by-hand"
    assert "CARD-HG5" in _errors(payload, tmp_path)

    l1["review_status"] = "pass"
    failure = next(row for row in payload["known_failure_modes"] if row["source_owner"] == "dgt-ablation-null-decomposition")
    failure["status"] = "pass-by-hand"
    assert "CARD-HG6" in _errors(payload, tmp_path)


def test_ablation_null_rendered_as_boundary_not_positive(tmp_path):
    payload = _build(tmp_path)

    assert any(row["source_owner"] == "dgt-ablation-null-decomposition" for row in payload["known_failure_modes"])
    assert "ablation" not in json.dumps(payload["intended_use"], sort_keys=True).lower()

    payload["intended_use"].append(
        {
            "scope": "ablation null positive",
            "source_owner": "dgt-ablation-null-decomposition",
            "source_pointer": "reports/canonical/dgt-ablation-null-decomposition.json:$.null_decomposition",
        }
    )
    assert "CARD-HG6" in _errors(payload, tmp_path)


def test_evidence_class_and_metric_provenance_consumed_from_index_owner(tmp_path):
    payload = _build(tmp_path)

    provenance = payload["training_facts"]["evidence_provenance"]
    assert provenance["source_pointer"] == card.INDEX_EVIDENCE_PROVENANCE_POINTER
    assert provenance["source_type"] == "canonical-quality-index"
    assert provenance["evidence_type"] == "pointer-owner-provenance"

    provenance["evidence_type"] = "local-card-enum"
    assert "CARD-HG7" in _errors(payload, tmp_path)


def test_unavailable_index_evidence_provenance_stays_blocked(tmp_path):
    _source_fixture(tmp_path)
    _rewrite_source(
        tmp_path,
        "reports/canonical/index.json",
        lambda source: source.pop("evidence_provenance"),
    )

    payload = card.build_dgt_model_card(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    provenance = payload["training_facts"]["evidence_provenance"]

    assert payload["status"] == "blocked"
    assert card.INDEX_EVIDENCE_PROVENANCE_POINTER in payload["missing_source_refs"]
    assert provenance == {
        "status": "blocked",
        "source_owner": "canonical-index-evidence-provenance",
        "source_pointer": card.INDEX_EVIDENCE_PROVENANCE_POINTER,
    }
    assert "CARD-HG9" in _errors(payload, tmp_path)


def test_l0_construct_validity_metric_source_boundary_is_card_level(tmp_path):
    _source_fixture(tmp_path)
    _rewrite_source(
        tmp_path,
        "reports/canonical/dgt-l0-controls.json",
        lambda source: source.update(
            {
                "construct_validity_hardgates": _construct_validity_payload(
                    "reports/canonical/dgt-l0-controls.json",
                    updates={
                        "metric_source": {
                            "source_kind": "per-arm-constant",
                            "metric_keys": ["accuracy"],
                            "per_arm_constants": True,
                        }
                    },
                )
            }
        ),
    )
    payload = card.build_dgt_model_card(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    boundary = _construct_boundary(payload, "dgt-l0-controls")

    assert boundary["status"] == "fail"
    assert boundary["failed_gates"] == ["CV-HG5"]

    boundary["failed_gates"] = []
    assert "CARD-HG5" in _errors(payload, tmp_path)


def test_l1_construct_validity_ood_label_visibility_boundary_is_card_level(tmp_path):
    _source_fixture(tmp_path)
    _rewrite_source(
        tmp_path,
        "reports/canonical/dgt-l1-controls.json",
        lambda source: source.update(
            {
                "construct_validity_ledger": _l1_construct_validity_ledger(
                    {"status": "blocked", "failed_gates": ["L1-CV-LEDGER"]}
                )
            }
        ),
    )
    payload = card.build_dgt_model_card(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    boundary = _construct_boundary(payload, "dgt-l1-controls")

    assert boundary["status"] == "blocked"
    assert boundary["failed_gates"] == ["L1-CV-LEDGER"]

    boundary["status"] = "pass"
    assert "CARD-HG5" in _errors(payload, tmp_path)


def test_l1_plateau_rule_abstraction_boundary_is_card_level(tmp_path):
    _source_fixture(tmp_path)
    _rewrite_source(
        tmp_path,
        "reports/canonical/dgt-l1-controls.json",
        lambda source: source.update(
            {
                "construct_validity_ledger": _l1_construct_validity_ledger(
                    {
                        "status": "blocked",
                        "failed_gates": ["L1-CV-LEDGER"],
                        "coverage_bound": {"rule_abstraction_claim": True},
                    }
                )
            }
        ),
    )
    payload = card.build_dgt_model_card(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    boundary = _construct_boundary(payload, "dgt-l1-controls")

    assert boundary["status"] == "blocked"
    assert boundary["failed_gates"] == ["L1-CV-LEDGER"]
    assert boundary["rule_abstraction_claim"] is True
    assert boundary["rule_abstraction_status"] == "not-claimed"

    boundary["rule_abstraction_claim"] = False
    assert "CARD-HG5" in _errors(payload, tmp_path)


def test_owner_flip_without_regen_fails_stale(tmp_path):
    payload = _build(tmp_path)
    source_path = tmp_path / "reports/canonical/dgt-l1-controls.json"
    source = json.loads(source_path.read_text(encoding="utf-8"))
    source["l1_tiny_sequence_projection"]["status"] = "blocked"
    source_path.write_text(json.dumps(source, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    errors = _errors(payload, tmp_path)

    assert "CARD-HG9" in errors


def test_hand_edited_card_hardgate_status_fails_closed(tmp_path):
    payload = _build(tmp_path)
    payload["status"] = "pass-by-hand"
    payload["card_hardgates"]["status"] = "pass-by-hand"
    payload["card_hardgates"]["gates"]["CARD-HG2"]["status"] = "fail-by-hand"

    errors = [error.as_dict() for error in card.validate_dgt_model_card(payload, tmp_path)]

    assert any(error["path"] == "$.status" for error in errors)
    assert any(error["path"] == "$.card_hardgates.status" for error in errors)
    assert any(error["path"] == "$.card_hardgates.gates.CARD-HG2.status" for error in errors)


def test_missing_source_before_build_fails_closed(tmp_path):
    _source_fixture(tmp_path)
    missing_pointer = "reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection"
    (tmp_path / "reports/canonical/dgt-l1-controls.json").unlink()

    payload = card.build_dgt_model_card(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    l1_row = next(row for row in payload["source_artifacts"] if row["source_pointer"] == missing_pointer)
    errors = _errors(payload, tmp_path)

    assert payload["status"] == "blocked"
    assert missing_pointer in payload["missing_source_refs"]
    assert l1_row["status"] != "resolved"
    assert payload["card_hardgates"]["gates"]["CARD-HG9"]["status"] == "fail"
    assert "CARD-HG9" in errors


def test_card_regen_idempotent(tmp_path):
    _source_fixture(tmp_path)
    first = card.write_dgt_model_card(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    first_json = (tmp_path / card.CANONICAL_JSON_ARTIFACT).read_text(encoding="utf-8")
    first_md = (tmp_path / card.CANONICAL_MARKDOWN_ARTIFACT).read_text(encoding="utf-8")
    second = card.write_dgt_model_card(root=tmp_path, generated_at="2030-01-01T00:00:00+00:00")
    second_json = (tmp_path / card.CANONICAL_JSON_ARTIFACT).read_text(encoding="utf-8")
    second_md = (tmp_path / card.CANONICAL_MARKDOWN_ARTIFACT).read_text(encoding="utf-8")

    assert first == second
    assert first_json == second_json
    assert first_md == second_md


def test_markdown_is_rendered_from_json(tmp_path):
    payload = _build(tmp_path)
    markdown = card.render_dgt_model_card_markdown(payload)

    assert card.validate_dgt_model_card_markdown(payload, markdown) == []
    assert card.validate_dgt_model_card_markdown(payload, markdown.replace("not production model", "production model"))
    assert card.render_dgt_model_card_markdown(copy.deepcopy(payload)) == markdown

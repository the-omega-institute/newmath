import pytest

from bedc_quality_lab.construct_validity import (
    CLAIM_CAPSULE_PROJECTION_KEYS,
    ConstructValidityEvidence,
    evaluate_construct_validity,
)


def _passing_evidence() -> ConstructValidityEvidence:
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


def _mutated(**updates):
    payload = _passing_evidence().as_payload()
    payload.update(updates)
    return ConstructValidityEvidence.from_payload(payload)


def test_construct_validity_passes_with_complete_pointer_shape():
    audit = evaluate_construct_validity(_passing_evidence())
    projection = audit.claim_capsule_projection_for(artifact="reports/canonical/example.json", pointer="$.construct_validity_hardgates")

    assert audit.status == "pass"
    assert audit.failed_gates == ()
    assert tuple(audit.gates) == ("CV-HG1", "CV-HG2", "CV-HG3", "CV-HG4", "CV-HG5")
    assert set(projection) == set(CLAIM_CAPSULE_PROJECTION_KEYS)
    assert projection["status"] == "pass"
    assert projection["failed_gates"] == []


@pytest.mark.parametrize(
    ("updates", "gate_id"),
    [
        ({"task_variables": None}, "CV-HG1"),
        (
            {
                "arm_input_access": {
                    "label_invisibility_certificate": False,
                    "arms": {"candidate": {"variables": ["x", "y"]}, "control": {"variables": ["x"]}},
                }
            },
            "CV-HG2",
        ),
        (
            {
                "finite_table": {
                    "support_count": 64,
                    "coverage_status": "table-coverage",
                    "finite_pair_accuracy": 0.982,
                    "rule_abstraction_claim": True,
                    "table_coverage_only": True,
                }
            },
            "CV-HG3",
        ),
        ({"hand_feature_ledger": {"mode": "shared-gate", "candidate_only_features": ["pair_gate"]}}, "CV-HG4"),
        ({"metric_source": {"source_kind": "per-arm-constant", "metric_keys": ["accuracy"], "per_arm_constants": True}}, "CV-HG5"),
    ],
)
def test_construct_validity_each_gate_fails_closed(updates, gate_id):
    audit = evaluate_construct_validity(_mutated(**updates))

    assert audit.status == "fail"
    assert gate_id in audit.failed_gates
    assert audit.gates[gate_id]["status"] != "pass"


def test_construct_validity_hg2_missing_certificate_fails_closed():
    audit = evaluate_construct_validity(
        _mutated(
            arm_input_access={
                "arms": {
                    "candidate": {"variables": ["x", "surface"]},
                    "control": {"variables": ["x", "surface"]},
                }
            }
        )
    )

    assert audit.status == "fail"
    assert audit.failed_gates == ("CV-HG2",)
    assert audit.gates["CV-HG2"]["label_invisibility_certificate"] is False


def test_construct_validity_missing_evidence_fails_all_gates():
    audit = evaluate_construct_validity(None)

    assert audit.status == "fail"
    assert audit.failed_gates == ("CV-HG1", "CV-HG2", "CV-HG3", "CV-HG4", "CV-HG5")


def test_construct_validity_hg3_table_coverage_status_blocks_rule_abstraction():
    audit = evaluate_construct_validity(
        _mutated(
            finite_table={
                "support_count": 64,
                "finite_pair_accuracy": 0.982,
                "rule_abstraction_claim": True,
                "coverage_status": "table-coverage",
            }
        )
    )

    assert audit.gates["CV-HG3"]["status"] == "table-coverage"
    assert "CV-HG3" in audit.failed_gates


def test_construct_validity_hg4_accepts_no_gate_ledger():
    audit = evaluate_construct_validity(_mutated(hand_feature_ledger={"mode": "no-gate", "features": []}))

    assert audit.status == "pass"
    assert audit.gates["CV-HG4"]["status"] == "pass"

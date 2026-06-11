import pytest

from bedc_quality_lab.discovery_compiler.capsule import build_architecture_claim_capsule_payload


def _model_claim(**updates):
    payload = {
        "model_id": "fixture-model",
        "claim": "finite architecture claim",
        "baselines": [{"artifact": "reports/canonical/control.json", "pointer": "$"}],
        "forbidden_evidence": ["production"],
        "required_gates": ["CV-HG1", "CV-HG2"],
        "candidate_pointer": {"artifact": "reports/canonical/model.json", "pointer": "$.candidate"},
        "evidence_pointer": {"artifact": "reports/canonical/model.json", "pointer": "$.construct_validity_hardgates"},
    }
    payload.update(updates)
    return payload


def _projection(status="pass", failed_gates=None):
    return {
        "artifact": "reports/canonical/model.json",
        "pointer": "$.construct_validity_hardgates",
        "status": status,
        "failed_gates": list(failed_gates or []),
        "owner_pointer": "bedc_quality_lab.construct_validity:evaluate_construct_validity",
    }


def test_architecture_capsule_embeds_only_construct_validity_projection():
    payload = build_architecture_claim_capsule_payload(
        generated_at="fixture",
        claim_id="claim:fixture",
        report="fixture-report",
        source_artifact="reports/canonical/model.json",
        source_pointer="$.candidate",
        model_claim=_model_claim(),
        construct_validity=_projection(),
    )

    assert set(payload["construct_validity"]) == {"artifact", "pointer", "status", "failed_gates", "owner_pointer"}
    assert "gates" not in payload["construct_validity"]
    assert "criterion" not in str(payload["construct_validity"])


def test_architecture_capsule_requires_construct_validity_when_cv_gate_is_required():
    with pytest.raises(ValueError, match="construct_validity"):
        build_architecture_claim_capsule_payload(
            generated_at="fixture",
            claim_id="claim:fixture",
            report="fixture-report",
            source_artifact="reports/canonical/model.json",
            source_pointer="$.candidate",
            model_claim=_model_claim(),
        )


def test_architecture_capsule_rejects_positive_rule_abstraction_under_cv_hg3():
    with pytest.raises(ValueError, match="CV-HG3|rule-abstraction"):
        build_architecture_claim_capsule_payload(
            generated_at="fixture",
            claim_id="claim:fixture",
            report="fixture-report",
            source_artifact="reports/canonical/model.json",
            source_pointer="$.candidate",
            model_claim=_model_claim(
                claim="positive rule-abstraction claim",
                rule_abstraction_claim=True,
                required_gates=["CV-HG3"],
            ),
            construct_validity=_projection(status="fail", failed_gates=["CV-HG3"]),
        )

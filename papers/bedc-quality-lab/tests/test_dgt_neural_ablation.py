import json

import pytest

from bedc_quality_lab import dgt_neural_ablation as owner


def test_registry_has_exact_arms_and_metrics():
    payload = owner.build_payload(generated_at="fixture", requested_device="cpu")

    assert tuple(payload["module_registry"]) == owner.ARM_IDS
    assert len(payload["records"]) == 11
    assert [row["arm_id"] for row in payload["records"]] == list(owner.ARM_IDS)
    for row in payload["records"]:
        assert set(row["metrics"]) == set(owner.METRIC_KEYS)
        assert row["requested_training_backend"] == "torch"
        assert row["optimizer_steps"] > 0
        assert row["parameter_l2_delta"] > 0.0


def test_nabl_hardgates_and_hg7_boundary_fail_closed():
    payload = owner.build_payload(generated_at="fixture", requested_device="cpu")

    owner.validate_payload(payload)
    assert payload["nabl_hardgates"]["status"] == "pass"
    assert set(payload["nabl_hardgates"]["gates"]) == set(owner.HG_IDS)
    blocked = [row for row in payload["boundary_ledger"] if row["claim_blocked"]]
    assert blocked == [
        {
            "claim_blocked": True,
            "component": "scope_seal",
            "metric_delta_pointer": "reports/canonical/dgt-neural-ablation.json:$.metric_delta_matrix.DGT_without_scope_seal",
            "reason": "HG7 boundary: no measurable effect; component-causal claim blocked",
            "status": "no_measurable_effect",
        }
    ]
    claimed = {row["component"] for row in payload["component_causal_claims"]}
    assert "scope_seal" not in claimed


def test_unavailable_payload_has_no_positive_component_claim():
    payload = owner.unavailable_payload(generated_at="fixture", requested_device="auto", reason="torch unavailable")

    owner.validate_payload(payload)
    assert payload["training_protocol"]["status"] == "unavailable"
    assert payload["nabl_hardgates"]["status"] == "fail"
    assert payload["component_causal_claims"] == []


def test_forbidden_positive_claim_terms_are_audited():
    payload = owner.build_payload(generated_at="fixture", requested_device="cpu")
    mutated = json.loads(json.dumps(payload))
    mutated["component_causal_claims"][0]["claim_text"] = "global superiority"
    mutated["forbidden_claim_term_audit"] = owner._forbidden_claim_term_audit(
        {"claims": mutated["component_causal_claims"]}
    )

    with pytest.raises(ValueError, match="forbidden term audit"):
        owner.validate_payload(mutated)

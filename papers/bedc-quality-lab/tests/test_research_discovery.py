import pytest

from bedc_quality_lab.research_discovery import (
    ResearchDiscoveryVerdict,
    assign_discovery_level,
)


def test_hg_dl_1_gap_head_on_h_shape_is_positive_discovery():
    verdict = assign_discovery_level(
        {
            "experiment_id": "gap-head-on-h",
            "terminal_verdict": "positive-discovery",
            "positive_discovery": True,
            "robustness_passed": False,
            "classifier_shift": True,
            "net_information": 0.34608695652173915,
            "scorecard_ready": True,
            "control_positive": False,
            "audit_status": "consistent",
        }
    )

    assert isinstance(verdict, ResearchDiscoveryVerdict)
    assert verdict.discovery_level == "D4"
    assert verdict.reasons == ("positive_discovery=true", "robustness_passed!=true")
    assert verdict.experiment_id == "gap-head-on-h"
    assert verdict.terminal_verdict == "positive-discovery"
    assert verdict.classifier_shift is True
    assert verdict.net_information == pytest.approx(0.34608695652173915)
    assert verdict.scorecard_ready is True
    assert verdict.control_positive is False
    assert verdict.audit_status == "consistent"
    assert verdict.revocation_status is None


@pytest.mark.parametrize("terminal_verdict", ["demoted", "rejected"])
def test_hg_dl_2_certificate_guided_shape_is_negative_discovery(terminal_verdict):
    verdict = assign_discovery_level(
        {
            "experiment_id": "certificate-guided-discovery",
            "terminal_verdict": terminal_verdict,
            "positive_discovery": False,
            "net_information": -0.020658466560950786,
            "claim_gate": {"training_audit_improvement_tradeoff": True},
            "audit_status": "unverifiable",
        }
    )

    assert verdict.discovery_level == "DN"
    assert verdict.reasons == (f"terminal_verdict={terminal_verdict}",)
    assert verdict.net_information == pytest.approx(-0.020658466560950786)
    assert verdict.audit_status == "unverifiable"


def test_hg_dl_3_observed_debt_improvement_without_shift_is_audit_improvement():
    verdict = assign_discovery_level(
        {
            "experiment_id": "nongaussian-observed-debt",
            "terminal_verdict": "ledger-only",
            "classifier_shift": False,
            "positive_discovery": False,
            "debt_delta": -0.14759756670976,
        }
    )

    assert verdict.discovery_level == "D1"
    assert verdict.reasons == ("debt_delta<0",)


def test_hg_dl_3_accepts_existing_claim_gate_audit_improvement_key():
    verdict = assign_discovery_level(
        {
            "experiment_id": "nongaussian-observed-debt",
            "claim_gate": {"training_audit_improvement_tradeoff": True},
        }
    )

    assert verdict.discovery_level == "D1"
    assert verdict.reasons == ("audit_improvement=true",)


def test_hg_dl_4_revoked_payload_is_revoked_discovery():
    verdict = assign_discovery_level(
        {
            "experiment_id": "fresh-evidence-downgrade",
            "terminal_verdict": "demoted",
            "revoked": True,
            "revocation_status": "revoked",
        }
    )

    assert verdict.discovery_level == "DR"
    assert verdict.reasons == ("revoked=true",)
    assert verdict.revocation_status == "revoked"


def test_hg_dl_5_no_shift_and_no_debt_improvement_is_observation():
    verdict = assign_discovery_level(
        {
            "experiment_id": "no-shift",
            "terminal_verdict": "accepted",
            "classifier_shift": False,
            "debt_delta": 0.0,
            "audit_improvement": False,
        }
    )

    assert verdict.discovery_level == "D0"
    assert verdict.reasons == ("no classifier shift or debt improvement",)


def test_positive_discovery_with_robustness_is_d5():
    verdict = assign_discovery_level(
        {
            "positive_discovery": True,
            "robustness_passed": True,
        }
    )

    assert verdict.discovery_level == "D5"
    assert verdict.reasons == ("positive_discovery=true", "robustness_passed=true")


def test_certified_discovery_without_positive_is_d3():
    verdict = assign_discovery_level(
        {
            "certified_discovery": True,
            "classifier_shift": True,
            "positive_discovery": False,
        }
    )

    assert verdict.discovery_level == "D3"
    assert verdict.reasons == ("certified_discovery=true",)


def test_classifier_shift_without_certification_is_d2():
    verdict = assign_discovery_level(
        {
            "classifier_shift": True,
            "certified_discovery": False,
            "positive_discovery": False,
        }
    )

    assert verdict.discovery_level == "D2"
    assert verdict.reasons == ("classifier_shift=true",)


def test_verdict_fields_use_safe_defaults_and_existing_control_key_mapping():
    verdict = assign_discovery_level(
        {
            "evidence_basis": {"control_positive_discovery": True},
            "net_information": "0.25",
        }
    )

    assert verdict.experiment_id == ""
    assert verdict.terminal_verdict == ""
    assert verdict.discovery_level == "D0"
    assert verdict.reasons
    assert verdict.classifier_shift is False
    assert verdict.net_information == pytest.approx(0.25)
    assert verdict.scorecard_ready is False
    assert verdict.control_positive is True
    assert verdict.audit_status is None
    assert verdict.revocation_status is None

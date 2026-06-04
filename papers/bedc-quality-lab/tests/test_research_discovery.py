import json
from itertools import product
from pathlib import Path

import pytest

from bedc_quality_lab.research_discovery import (
    ResearchDiscoveryVerdict,
    assign_discovery_level,
)


ROOT = Path(__file__).resolve().parents[1]


def _canonical_payload(name: str) -> dict:
    return json.loads((ROOT / "reports" / "canonical" / name).read_text(encoding="utf-8"))


def _positive_payload(**overrides) -> dict:
    payload = {
        "artifact": "reports/canonical/positive-fixture.json",
        "positive_discovery": True,
        "net_positive_signal": True,
        "main_verdict": {
            "surface_delta_count": 1,
            "shift_information": 1,
            "structural_discovery": True,
        },
        "evidence_basis": {
            "control_positive_discovery": False,
            "scorecard_ready": True,
        },
    }
    payload.update(overrides)
    return payload


def test_hg_dl_1_gap_head_discovery_report_without_scorecard_fails_closed():
    verdict = assign_discovery_level(_canonical_payload("gap-head-discovery.json"))

    assert isinstance(verdict, ResearchDiscoveryVerdict)
    assert verdict.discovery_level == "DN"
    assert verdict.reasons == ("scorecard_ready=false",)
    assert verdict.experiment_id == "reports/canonical/gap-head-discovery.json"
    assert verdict.terminal_verdict == ""
    assert verdict.classifier_shift is True
    assert verdict.net_information == pytest.approx(0.34608695652173915)
    assert verdict.scorecard_ready is False
    assert verdict.control_positive is False
    assert verdict.audit_status is None
    assert verdict.revocation_status is None


@pytest.mark.parametrize(
    ("classifier_shift", "positive_net", "control_negative", "scorecard_ready", "positive_terminal"),
    product((False, True), repeat=5),
)
def test_d4_finite_gate_matrix(
    classifier_shift,
    positive_net,
    control_negative,
    scorecard_ready,
    positive_terminal,
):
    payload = {
        "positive_discovery": positive_terminal,
        "net_positive_signal": positive_net,
        "main_verdict": {
            "surface_delta_count": 1 if classifier_shift else 0,
            "shift_information": 1 if classifier_shift else 0,
            "structural_discovery": classifier_shift,
            "deltas": {"debt_delta": 0.0},
        },
        "evidence_basis": {
            "control_positive_discovery": not control_negative,
            "scorecard_ready": scorecard_ready,
        },
    }

    verdict = assign_discovery_level(payload)

    if classifier_shift and positive_net and control_negative and scorecard_ready and positive_terminal:
        assert verdict.discovery_level == "D4"
    elif positive_terminal:
        assert verdict.discovery_level == "DN"
    elif classifier_shift:
        assert verdict.discovery_level == "D3"
    else:
        assert verdict.discovery_level == "D0"


@pytest.mark.parametrize("terminal_verdict", ["demoted", "rejected"])
def test_hg_dl_2_terminal_verdict_report_is_negative_discovery(terminal_verdict):
    verdict = assign_discovery_level(
        {
            "artifact": "reports/canonical/certification-verdict.json",
            "verdict": terminal_verdict,
            "evidence_basis": {
                "main_verdict": {
                    "surface_delta_count": 6,
                    "shift_information": 6,
                    "structural_discovery": True,
                    "net_information": -0.020658466560950786,
                    "positive_discovery": False,
                    "deltas": {"debt_delta": -0.14759756670976},
                },
                "scorecard_ready": True,
                "audit_status": "unverifiable",
            },
        }
    )

    assert verdict.discovery_level == "DN"
    assert verdict.reasons == (f"verdict={terminal_verdict}",)
    assert verdict.net_information == pytest.approx(-0.020658466560950786)
    assert verdict.scorecard_ready is True
    assert verdict.audit_status == "unverifiable"


def test_hg_dl_3_observed_debt_improvement_without_shift_is_audit_improvement():
    verdict = assign_discovery_level(
        {
            "artifact": "reports/canonical/nongaussian-observed-debt.json",
            "main_verdict": {
                "surface_delta_count": 0,
                "shift_information": 0,
                "structural_discovery": False,
                "positive_discovery": False,
                "deltas": {"debt_delta": -0.14759756670976},
            },
        }
    )

    assert verdict.discovery_level == "D1"
    assert verdict.reasons == ("main_verdict.deltas.debt_delta<0",)


def test_hg_dl_3_accepts_existing_claim_gate_audit_improvement_key():
    verdict = assign_discovery_level(_canonical_payload("certificate-guided-discovery.json"))

    assert verdict.discovery_level == "DN"
    assert verdict.reasons == ("verdict=demoted",)
    assert verdict.net_information == pytest.approx(-0.0078000000000000465)

    no_shift = dict(_canonical_payload("certificate-guided-discovery.json"))
    no_shift["verdict"] = ""
    no_shift["failed_gate"] = None
    no_shift["verdicts"] = [
        {
            "surface_delta_count": 0,
            "shift_information": 0,
            "structural_discovery": False,
            "positive_discovery": False,
            "deltas": {"debt_delta": 0.0},
        }
    ]
    tradeoff = assign_discovery_level(no_shift)

    assert tradeoff.discovery_level == "D1"
    assert tradeoff.reasons == ("claim_gate.training_audit_improvement_tradeoff=true",)


def test_certificate_guided_demoted_failed_gate_is_negative_discovery():
    verdict = assign_discovery_level(
        {
            "artifact": "reports/canonical/certificate-guided-discovery.json",
            "verdict": "demoted",
            "failed_gate": "audit-improvement-tradeoff",
            "hardgate": {"status": "non-positive"},
            "verdicts": [
                {
                    "surface_delta_count": 6,
                    "shift_information": 6,
                    "structural_discovery": True,
                    "net_information": -0.02,
                    "positive_discovery": False,
                    "deltas": {"debt_delta": -0.5, "benefit_delta": -0.5},
                }
            ],
        }
    )

    assert verdict.discovery_level == "DN"
    assert verdict.reasons == ("verdict=demoted",)


def test_hg_dl_4_revocation_decision_is_revoked_discovery():
    verdict = assign_discovery_level(
        {
            "artifact": "reports/canonical/fresh-evidence-downgrade.json",
            "revocation_decision": {
                "downgraded": True,
                "old_status": "positive",
                "new_status": "audit-improvement-tradeoff",
                "reason": "audit-improvement-tradeoff",
            },
            "verdicts": [
                {
                    "surface_delta_count": 6,
                    "shift_information": 6,
                    "structural_discovery": True,
                    "positive_discovery": False,
                }
            ],
        }
    )

    assert verdict.discovery_level == "DR"
    assert verdict.reasons == ("revocation_decision.downgraded=true",)
    assert verdict.revocation_status == "audit-improvement-tradeoff"


def test_hg_dl_5_no_shift_and_no_debt_improvement_is_observation():
    verdict = assign_discovery_level(
        {
            "artifact": "reports/canonical/no-shift.json",
            "main_verdict": {
                "surface_delta_count": 0,
                "shift_information": 0,
                "structural_discovery": False,
                "positive_discovery": False,
                "deltas": {"debt_delta": 0.0},
            },
            "claim_gate": {"training_audit_improvement_tradeoff": False},
        }
    )

    assert verdict.discovery_level == "D0"
    assert verdict.reasons == ("no classifier shift or debt improvement",)


def test_positive_discovery_with_real_robustness_report_is_d5_o():
    payload = _positive_payload()
    payload.update(
        {
            "acceptance_gates": {"status": "pass"},
            "final_status": "pass",
        }
    )

    verdict = assign_discovery_level(payload)

    assert verdict.discovery_level == "D5-O"
    assert verdict.reasons == (
        "positive_terminal=true",
        "classifier_shift=true",
        "net_positive_signal=true",
        "control_negative=true",
        "scorecard_ready=true",
        "robustness_ready=true",
        "mechanism_ready=false",
    )


def test_positive_discovery_with_mechanism_attribution_is_d5_m():
    payload = _positive_payload()
    payload.update(
        {
            "acceptance_gates": {"status": "pass"},
            "final_status": "pass",
            "mechanism_attribution": {
                "all_pass": True,
                "status": "ready",
                "failed_gate": None,
                "channel": "closed-attribution",
            },
            "source_pointers": {
                "operational": "reports/canonical/gap-head-robustness-sweep.json:$.acceptance_gates.status",
                "mechanism": "reports/gap_head_mechanism_namecert.json:$.ledger_policy.mechanism_closure_debt",
                "mechanism_case": "reports/gap_head_mechanism_namecert.json:$.closure_status.mechanism_spec",
            },
        }
    )

    verdict = assign_discovery_level(payload)

    assert verdict.discovery_level == "D5-M"
    assert verdict.reasons == (
        "positive_terminal=true",
        "classifier_shift=true",
        "net_positive_signal=true",
        "control_negative=true",
        "scorecard_ready=true",
        "robustness_ready=true",
        "mechanism_ready=true",
    )


def test_probe_margin_channel_blocks_d5_m():
    payload = _positive_payload()
    payload.update(
        {
            "acceptance_gates": {"status": "pass"},
            "final_status": "pass",
            "mechanism_attribution": {
                "all_pass": True,
                "status": "ready",
                "failed_gate": None,
                "channel": "probe-margin-channel",
            },
            "source_pointers": {
                "operational": "reports/canonical/gap-head-robustness-sweep.json:$.acceptance_gates.status",
                "mechanism": "reports/gap_head_mechanism_namecert.json:$.ledger_policy.mechanism_closure_debt",
                "mechanism_case": "reports/gap_head_mechanism_namecert.json:$.closure_status.mechanism_spec",
            },
        }
    )

    verdict = assign_discovery_level(payload)

    assert verdict.discovery_level == "D5-O"


def test_terminal_dn_overrides_positive_gate():
    verdict = assign_discovery_level(_positive_payload(verdict="rejected"))

    assert verdict.discovery_level == "DN"
    assert verdict.reasons == ("verdict=rejected",)


def test_revocation_overrides_positive_gate():
    verdict = assign_discovery_level(
        _positive_payload(
            certificate_status={"status": "revoked"},
            verdict="rejected",
        )
    )

    assert verdict.discovery_level == "DR"
    assert verdict.reasons == ("certificate_status.status=revoked",)


def test_d5_m_requires_mechanism_source_pointers():
    payload = _positive_payload(
        acceptance_gates={"status": "pass"},
        final_status="pass",
        mechanism_attribution={
            "all_pass": True,
            "status": "ready",
            "failed_gate": None,
            "channel": "closed-attribution",
        },
    )

    verdict = assign_discovery_level(payload)

    assert verdict.discovery_level == "D5-O"


def test_structural_discovery_without_positive_is_d3():
    verdict = assign_discovery_level(
        {
            "artifact": "reports/canonical/structural.json",
            "verdicts": [
                {
                    "surface_delta_count": 6,
                    "shift_information": 6,
                    "structural_discovery": True,
                    "net_information": -0.020658466560950786,
                    "positive_discovery": False,
                    "deltas": {"debt_delta": -0.14759756670976},
                }
            ],
        }
    )

    assert verdict.discovery_level == "D3"
    assert verdict.reasons == ("main_verdict.structural_discovery=true", "main_verdict.shift_information>0")


def test_classifier_shift_without_structural_discovery_is_d2():
    verdict = assign_discovery_level(
        {
            "artifact": "reports/canonical/classifier-shift.json",
            "main_verdict": {
                "surface_delta_count": 2,
                "shift_information": 2,
                "structural_discovery": False,
                "positive_discovery": False,
                "deltas": {"debt_delta": 0.0},
            },
        }
    )

    assert verdict.discovery_level == "D2"
    assert verdict.reasons == ("main_verdict.surface_delta_count>0", "main_verdict.shift_information>0")


def test_verdict_fields_use_safe_defaults_and_existing_control_key_mapping():
    verdict = assign_discovery_level(
        {
            "evidence_basis": {"control_positive_discovery": True},
            "main_verdict": {"net_information": "0.25"},
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


def test_certificate_status_revoked_signal_is_dr():
    verdict = assign_discovery_level({"certificate_status": {"status": "revoked"}})

    assert verdict.discovery_level == "DR"
    assert verdict.reasons == ("certificate_status.status=revoked",)
    assert verdict.revocation_status == "revoked"

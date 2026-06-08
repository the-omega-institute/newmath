from copy import deepcopy

from bedc_quality_lab.backends.current_lab.gap_head_readiness import (
    GAP_HEAD_ABLATION_ARTIFACT,
    GAP_HEAD_OBSERVED_DEBT_TRANSFER_POINTER,
    GAP_HEAD_ROBUSTNESS_ARTIFACT,
    NEGATIVE_WITNESSES_ARTIFACT,
    OBSERVED_DEBT_ARTIFACT,
    GapHeadOperationalReadinessPolicy,
)


def _auroc_cell(*, mean, ci95_low, ci95_high):
    return {
        "ci95_half_width": 0.01,
        "ci95_high": ci95_high,
        "ci95_low": ci95_low,
        "mean": mean,
        "n": 10,
        "std": 0.01,
    }


def _context():
    return {
        GAP_HEAD_ROBUSTNESS_ARTIFACT: {
            "final_status": "pass",
            "A1_threshold_sweep": {"treatment_verdict": {"positive": True}},
            "A3_seed_expansion": {"final_verdict": "robust_positive"},
        },
        GAP_HEAD_ABLATION_ARTIFACT: {"hardgate": {"status": "pass"}},
        NEGATIVE_WITNESSES_ARTIFACT: {
            "status": "pointer-only",
            "expected_kind_count": 9,
            "witnesses": [
                {"kind": f"witness-{index}", "terminal_verdict": "rejected", "discovery_level": "DN"}
                for index in range(9)
            ],
        },
        OBSERVED_DEBT_ARTIFACT: {
            "gap_head_on_h_observed_debt_transfer": {"status": "pass"},
            "surfaces": [
                {
                    "control_verdict": {"positive": False},
                    "hardgates": {
                        "HG-A1": {
                            "learned_auroc": _auroc_cell(mean=0.82, ci95_low=0.81, ci95_high=0.83),
                            "matched_random_auroc": _auroc_cell(mean=0.46, ci95_low=0.42, ci95_high=0.49),
                        }
                    },
                }
            ],
            "not_claimed": ["no claim outside the listed observed-debt transfer surfaces"],
        },
    }


def _ledger(context=None):
    return GapHeadOperationalReadinessPolicy().criteria(_context() if context is None else context)


def _statuses(ledger):
    return {criterion.name: criterion.status for criterion in ledger.criteria}


def test_gap_head_readiness_criterion_order_and_ablation_pointer():
    ledger = _ledger()

    assert [criterion.name for criterion in ledger.criteria] == [
        "threshold",
        "ablation",
        "seed_expansion",
        "adversarial",
        "observed_debt_transfer",
    ]
    ablation = ledger.as_dict()["ablation"]
    assert ablation["artifact"] == GAP_HEAD_ABLATION_ARTIFACT
    assert ablation["pointer"] == "$.hardgate.status"


def test_gap_head_readiness_all_pass_and_failed_checks():
    ledger = _ledger()

    assert ledger.all_pass is True
    assert ledger.failed_checks() == []
    assert {row["status"] for row in ledger.as_dict().values()} == {"pass"}


def test_gap_head_readiness_unresolved_ablation_pointer_is_missing():
    context = _context()
    context[GAP_HEAD_ABLATION_ARTIFACT] = {}

    ledger = _ledger(context)

    assert ledger.all_pass is False
    assert _statuses(ledger)["ablation"] == "missing"
    assert ledger.failed_checks() == ["ablation"]


def test_gap_head_readiness_explicit_ablation_nonpass_is_failed():
    context = _context()
    context[GAP_HEAD_ABLATION_ARTIFACT]["hardgate"]["status"] = "fail"

    ledger = _ledger(context)

    assert _statuses(ledger)["ablation"] == "failed"
    assert ledger.failed_checks() == ["ablation"]


def test_gap_head_readiness_per_criterion_fail_closed():
    mutations = {
        "threshold": lambda context: context[GAP_HEAD_ROBUSTNESS_ARTIFACT]["A1_threshold_sweep"].clear(),
        "ablation": lambda context: context[GAP_HEAD_ABLATION_ARTIFACT]["hardgate"].update(status="fail"),
        "seed_expansion": lambda context: context[GAP_HEAD_ROBUSTNESS_ARTIFACT]["A3_seed_expansion"].update(final_verdict="weak"),
        "adversarial": lambda context: context[NEGATIVE_WITNESSES_ARTIFACT]["witnesses"][0].update(terminal_verdict="accepted"),
        "observed_debt_transfer": lambda context: context[OBSERVED_DEBT_ARTIFACT]["gap_head_on_h_observed_debt_transfer"].update(status="fail"),
    }

    for name, mutate in mutations.items():
        context = deepcopy(_context())
        mutate(context)
        ledger = _ledger(context)

        assert ledger.all_pass is False
        assert ledger.failed_checks() == [name]
        assert _statuses(ledger)[name] != "pass"


def test_gap_head_readiness_observed_transfer_pointer():
    ledger = _ledger()

    observed = ledger.as_dict()["observed_debt_transfer"]
    assert observed["artifact"] == OBSERVED_DEBT_ARTIFACT
    assert observed["pointer"] == GAP_HEAD_OBSERVED_DEBT_TRANSFER_POINTER

from bedc_quality_lab.experiment_stack import (
    REQUIRED_PREFLIGHT_CARD_IDS,
    evaluate_claim_first_gate,
)


def _pass_card(card_id: str) -> dict[str, object]:
    return {
        "card_id": card_id,
        "status": "pass",
        "source_pointer": f"reports/canonical/experiment_stack_cards.json:$.cards.{card_id}",
        "failure_reasons": [],
    }


def test_claim_first_gate_blocks_training_result_without_preflight_cards():
    decision = evaluate_claim_first_gate(
        {
            "claim_kind": "promoted_training",
            "experiment_stack": {"cards": []},
            "training_result_refs": [
                {"ref": "reports/canonical/discovery-gated-transformer.json:$.scaling_ladder"},
            ],
        }
    )

    assert decision.status == "blocked"
    assert set(decision.failed_card_ids) == set(REQUIRED_PREFLIGHT_CARD_IDS)
    assert decision.blocked_training_result_refs == (
        "reports/canonical/discovery-gated-transformer.json:$.scaling_ladder",
    )
    assert "task-target-card" in decision.pointer_reasons
    assert "baseline-validity-card" in decision.pointer_reasons


def test_claim_first_gate_negative_fixture():
    fixture = {
        "claim_kind": "promoted_training",
        "experiment_stack": {
            "cards": [
                _pass_card("claim-card"),
                _pass_card("feature-access-card"),
                _pass_card("ood-solvability-card"),
                _pass_card("metric-provenance-card"),
            ],
        },
        "training_result_refs": [
            {
                "artifact_pointer": "reports/canonical/model-comparison.json:$.models[0].metrics",
                "metric": "quality_q",
            }
        ],
    }

    decision = evaluate_claim_first_gate(fixture)

    assert decision.status == "blocked"
    assert "task-target-card" in decision.failed_card_ids
    assert "baseline-validity-card" in decision.failed_card_ids
    assert "label-function" in decision.pointer_reasons["task-target-card"]
    assert decision.blocked_training_result_refs == (
        "reports/canonical/model-comparison.json:$.models[0].metrics",
    )


def test_claim_first_gate_passes_after_preflight_cards():
    context = {
        "claim_kind": "promoted_training",
        "experiment_stack": {"cards": [_pass_card(card_id) for card_id in REQUIRED_PREFLIGHT_CARD_IDS]},
        "training_result_refs": ["reports/canonical/model-comparison.json:$.models[0].metrics"],
    }

    decision = evaluate_claim_first_gate(context)

    assert decision.status == "pass"
    assert decision.failed_card_ids == ()
    assert decision.blocked_training_result_refs == ()


def test_claim_first_gate_not_applicable_without_training_promotion():
    decision = evaluate_claim_first_gate({"experiment_stack": {"cards": []}})

    assert decision.status == "not-applicable"
    assert decision.failed_card_ids == ()

import json

import pytest

from bedc_quality_lab import dgt_l1_controls as l1
from bedc_quality_lab.tiny_sequence_l1 import FAIR_ARM_IDS, FairL1ConstructionSlice, FairL1InputContract


def _payload():
    config = l1.L1TrainingConfig(
        step_grid=(2,),
        training_steps=2,
        train_examples=32,
        eval_examples=32,
    )
    return l1.build_payload(generated_at="fixture-time", requested_device="cpu", config=config)


def test_fair_l1_contract_requires_pair_visible_inputs_for_every_arm():
    payload = _payload()
    contract = payload["fair_l1_construction"]["input_contract"]

    assert set(contract["visible_variables_by_arm"]) == set(FAIR_ARM_IDS)
    for variables in contract["visible_variables_by_arm"].values():
        assert {"x_minus_1", "x_minus_2"}.issubset(set(variables))

    bad = json.loads(json.dumps(payload))
    bad["fair_l1_construction"]["input_contract"]["visible_variables_by_arm"]["base"].remove("x_minus_2")
    bad["fair_l1_construction"]["fair_hardgates"] = FairL1ConstructionSlice().evaluate_fair_hardgates(
        bad["fair_l1_construction"]
    )
    bad["fair_l1_construction"]["fair_l1_decision"] = FairL1ConstructionSlice().derive_fair_decision(
        bad["fair_l1_construction"]
    )
    bad["l1_tiny_sequence_projection"] = l1._projection(bad, bad["hardgates"])
    with pytest.raises(ValueError, match="pair-visible"):
        l1.validate_payload(bad)


def test_fair_l1_contract_rejects_label_split_seed_and_hidden_inputs():
    contract = FairL1InputContract(
        visible_variables_by_arm={
            arm_id: ["token_sequence", "x_minus_1", "x_minus_2"]
            for arm_id in FAIR_ARM_IDS
        },
        forbidden_feature_names=["label", "split_id", "seed_id", "coefficient", "target"],
        support_partition_digest="fixture",
        label_rule_ref="fixture-rule",
    )
    contract.validate_no_leakage()
    contract.validate_pair_visible()

    leaking = FairL1InputContract(
        visible_variables_by_arm={
            arm_id: ["token_sequence", "x_minus_1", "x_minus_2"]
            for arm_id in FAIR_ARM_IDS
        }
        | {"dgt": ["token_sequence", "x_minus_1", "x_minus_2", "label_value"]},
        forbidden_feature_names=["label", "split_id", "seed_id", "coefficient", "target"],
        support_partition_digest="fixture",
        label_rule_ref="fixture-rule",
    )
    with pytest.raises(ValueError, match="leakage"):
        leaking.validate_no_leakage()


def test_fair_l1_support_partitions_are_disjoint_and_share_label_rule_ref():
    construction = _payload()["fair_l1_construction"]
    support = construction["support_partitions"]

    assert support["disjoint"] is True
    assert set(map(tuple, support["train_pairs"])).isdisjoint(set(map(tuple, support["ood_pairs"])))
    assert support["label_rule_ref"] == support["shared_label_rule_ref"]
    assert support["all_digest"] == construction["input_contract"]["support_partition_digest"]


def test_fair_l1_training_rows_are_real_and_progress_visible():
    construction = _payload()["fair_l1_construction"]

    assert len(construction["training_rows"]) == len(FAIR_ARM_IDS) * 16
    assert len(construction["progress_rows"]) == len(construction["training_rows"])
    assert all(row["progress_visible"] is True for row in construction["progress_rows"])
    for row in construction["training_rows"]:
        assert row["device_resolved"] == "cpu"
        assert row["metrics"]["parameter_l2_delta"] > 0
        assert row["metrics"]["loss_decrease"] > 0
        assert row["metrics"]["loss_start"] > row["metrics"]["loss_end"]
    for arm_id in FAIR_ARM_IDS:
        metrics = construction["fair_arm_metrics"][arm_id]["metrics"]
        assert metrics["parameter_l2_delta_mean"] > 0
        assert metrics["loss_decrease_mean"] > 0


def test_fair_l1_ood_gate_rejects_lookup_only_behavior():
    construction = _payload()["fair_l1_construction"]
    lookup = construction["lookup_only_control"]

    assert lookup["in_distribution_accuracy"] == 1.0
    assert lookup["satisfies_ood_survivor"] is False
    assert construction["ood_gate"]["status"] == "pass"
    assert "survivor_arms" in construction["ood_gate"]


def test_fair_l1_decision_no_survivor_holds_bounded_negative():
    construction = _payload()["fair_l1_construction"]
    construction["ood_gate"]["has_ood_survivor"] = False
    construction["ood_gate"]["survivor_arms"] = []
    decision = FairL1ConstructionSlice().derive_fair_decision(construction)

    assert decision["standing_verdict"] == "bounded-negative"
    assert decision["canonical_axis_action"] == "hold-current"
    assert decision["superiority_claim_allowed"] is False


def test_fair_l1_decision_survivor_stops_for_maintainer_review():
    construction = _payload()["fair_l1_construction"]
    construction["ood_gate"]["has_ood_survivor"] = True
    construction["ood_gate"]["survivor_arms"] = ["dgt"]
    construction["fair_hardgates"] = {
        gate_id: {**row, "status": "pass", "fail_closed_reason": None}
        for gate_id, row in construction["fair_hardgates"].items()
    }
    decision = FairL1ConstructionSlice().derive_fair_decision(construction)

    assert decision["standing_verdict"] == "maintainer-review-required"
    assert decision["canonical_axis_action"] == "stop-report"
    assert decision["superiority_claim_allowed"] is False


def test_base_undertraining_sidecar_is_not_registered():
    from scripts import run_canonical_reports as canonical

    names = [spec.name for spec in canonical.CANONICAL_REPORTS]
    assert "dgt-base-undertraining-audit" not in names
    assert "fair-l1-decision" not in names
    assert "fair_l1_construction" in canonical._specs_by_name()["dgt-l1-controls"].required_json_keys

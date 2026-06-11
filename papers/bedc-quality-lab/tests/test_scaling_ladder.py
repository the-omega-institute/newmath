import json

from bedc_quality_lab.scaling_ladder import (
    build_scaling_ladder_payload,
    default_ladder_refs,
    evaluate_ladder_opening,
    validate_scaling_ladder_payload,
)


def _write_json(root, artifact, payload):
    path = root / artifact
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")


def _write_owner_inputs(
    root,
    *,
    evidence_kind="empirical_training_clean",
    source_kind=None,
    owner_backed=True,
    allowed=True,
    construct_status="construct-valid",
    construct_gate_status="pass",
    l0_decision_status="scaling-evidence-eligible",
    l1_decision_status="scaling-evidence-eligible",
    l0_split_status="winnable",
    l1_split_status="winnable",
    l0_ci_low=0.12,
    l1_ci_low=0.18,
    write_l1_decision=True,
):
    evidence_row = {
        "evidence_type": evidence_kind,
        "owner_backed_measured_training": owner_backed,
        "allowed_for_empirical_claim": allowed,
    }
    if source_kind is not None:
        evidence_row["source_kind"] = source_kind
    _write_json(
        root,
        "reports/canonical/index.json",
        {
            "evidence_provenance": {
                "levels": {
                    "L0_toy": dict(evidence_row),
                    "L1_tiny_sequence": dict(evidence_row),
                }
            }
        },
    )
    _write_json(
        root,
        "reports/canonical/dgt-base-undertraining-audit.json",
        {
            "base_undertraining_audit": {
                "construct_validity": {
                    "status": construct_status,
                    "hardgates": {
                        "CV-HG1": {"status": construct_gate_status},
                        "CV-HG2": {"status": construct_gate_status},
                    },
                }
            }
        },
    )
    _write_json(
        root,
        "reports/canonical/dgt-l0-controls.json",
        {
            "l0_toy_projection": {
                "owner_decision": {"status": l0_decision_status},
                "split_winnability": {"status": l0_split_status},
                "separation": {"ci_low": l0_ci_low},
            }
        },
    )
    l1_projection = {
        "split_winnability": {"status": l1_split_status},
        "separation": {"ci_low": l1_ci_low},
    }
    if write_l1_decision:
        l1_projection["fair_decision"] = {"status": l1_decision_status}
    _write_json(
        root,
        "reports/canonical/dgt-l1-controls.json",
        {"l1_tiny_sequence_projection": l1_projection},
    )


def _states(payload):
    return {row["level_id"]: (row["state"], row["reason"]) for row in payload["levels"]}


def test_scaling_ladder_valid_owner_contract_opens_levels(tmp_path):
    _write_owner_inputs(tmp_path)

    payload = build_scaling_ladder_payload(root=tmp_path, generated_at="fixture-time")

    assert _states(payload) == {
        "L0_toy": ("open", "eligible"),
        "L1_tiny_sequence": ("open", "eligible"),
    }
    assert payload["boundary_ledger"] == []
    validate_scaling_ladder_payload(payload)


def test_scaling_ladder_projection_only_closes_without_owner_measurement(tmp_path):
    _write_owner_inputs(tmp_path, source_kind="projection-only")

    row = evaluate_ladder_opening(default_ladder_refs()[0], {"root": tmp_path}).as_row()

    assert row["state"] == "closed"
    assert row["reason"] == "projection-only"


def test_scaling_ladder_declared_constant_provenance_closes(tmp_path):
    _write_owner_inputs(tmp_path, source_kind="declared-constant")

    row = evaluate_ladder_opening(default_ladder_refs()[0], {"root": tmp_path}).as_row()

    assert row["state"] == "closed"
    assert row["reason"] == "non-measured-evidence"


def test_scaling_ladder_arm_branch_provenance_closes(tmp_path):
    _write_owner_inputs(tmp_path, source_kind="arm-branch")

    row = evaluate_ladder_opening(default_ladder_refs()[0], {"root": tmp_path}).as_row()

    assert row["state"] == "closed"
    assert row["reason"] == "non-measured-evidence"


def test_scaling_ladder_missing_provenance_closes(tmp_path):
    _write_owner_inputs(tmp_path)
    (tmp_path / "reports/canonical/index.json").unlink()

    row = evaluate_ladder_opening(default_ladder_refs()[0], {"root": tmp_path}).as_row()

    assert row["state"] == "closed"
    assert row["reason"] == "missing-pointer"


def test_scaling_ladder_construct_validity_failure_closes(tmp_path):
    _write_owner_inputs(tmp_path, construct_status="construct-boundary")

    row = evaluate_ladder_opening(default_ladder_refs()[0], {"root": tmp_path}).as_row()

    assert row["state"] == "closed"
    assert row["reason"] == "construct-validity-failed"


def test_scaling_ladder_split_not_winnable_closes(tmp_path):
    _write_owner_inputs(tmp_path, l0_split_status="blocked")

    row = evaluate_ladder_opening(default_ladder_refs()[0], {"root": tmp_path}).as_row()

    assert row["state"] == "closed"
    assert row["reason"] == "split-not-winnable"


def test_scaling_ladder_ci_low_nonseparation_closes(tmp_path):
    _write_owner_inputs(tmp_path, l0_ci_low=0.0)

    row = evaluate_ladder_opening(default_ladder_refs()[0], {"root": tmp_path}).as_row()

    assert row["state"] == "closed"
    assert row["reason"] == "ci-low-separation-failed"


def test_scaling_ladder_injected_l0_fixture_stays_closed(tmp_path):
    _write_owner_inputs(tmp_path)
    _write_json(
        tmp_path,
        "reports/canonical/discovery-gated-transformer.json",
        {"scaling_ladder": {"opened_levels": ["L0_toy"]}},
    )
    (tmp_path / "reports/canonical/index.json").unlink()

    payload = build_scaling_ladder_payload(root=tmp_path, generated_at="fixture-time")
    states = _states(payload)

    assert states["L0_toy"] == ("boundary", "stale-or-injected")
    assert states["L1_tiny_sequence"] == ("closed", "missing-pointer")
    assert payload["boundary_ledger"] == [
        {
            "level_id": "L0_toy",
            "prior_state": "open",
            "new_state": "boundary",
            "reason": "stale-or-injected",
            "failed_contract_pointer": "reports/canonical/discovery-gated-transformer.json:$.scaling_ladder",
            "owner_pointer": "reports/canonical/scaling-ladder.json:$.levels",
            "recorded_at": "fixture-time",
        }
    ]
    assert payload["hardgates"]["SL-HG5-no-injected-opening"]["status"] == "fail"


def test_scaling_ladder_valid_owner_inputs_with_injected_l0_fail_closed_to_boundary(tmp_path):
    _write_owner_inputs(tmp_path)
    _write_json(
        tmp_path,
        "reports/canonical/discovery-gated-transformer.json",
        {"scaling_ladder": {"opened_levels": ["L0_toy"]}},
    )

    payload = build_scaling_ladder_payload(root=tmp_path, generated_at="fixture-time")
    states = _states(payload)

    assert states["L0_toy"] == ("boundary", "stale-or-injected")
    assert states["L1_tiny_sequence"] == ("open", "eligible")
    assert payload["boundary_ledger"] == [
        {
            "level_id": "L0_toy",
            "prior_state": "open",
            "new_state": "boundary",
            "reason": "stale-or-injected",
            "failed_contract_pointer": "reports/canonical/discovery-gated-transformer.json:$.scaling_ladder",
            "owner_pointer": "reports/canonical/scaling-ladder.json:$.levels",
            "recorded_at": "fixture-time",
        }
    ]
    assert payload["hardgates"]["SL-HG5-no-injected-opening"] == {
        "status": "fail",
        "pointer": "reports/canonical/discovery-gated-transformer.json:$.scaling_ladder",
    }


def test_scaling_ladder_projection_only_closes_despite_old_projection(tmp_path):
    _write_owner_inputs(tmp_path, source_kind="projection-only")
    _write_json(
        tmp_path,
        "reports/canonical/discovery-gated-transformer.json",
        {"scaling_ladder": {"opened_levels": ["L0_toy"]}},
    )

    payload = build_scaling_ladder_payload(root=tmp_path, generated_at="fixture-time")

    assert _states(payload)["L0_toy"] == ("boundary", "stale-or-injected")
    assert payload["boundary_ledger"] == [
        {
            "level_id": "L0_toy",
            "prior_state": "open",
            "new_state": "boundary",
            "reason": "stale-or-injected",
            "failed_contract_pointer": "reports/canonical/discovery-gated-transformer.json:$.scaling_ladder",
            "owner_pointer": "reports/canonical/scaling-ladder.json:$.levels",
            "recorded_at": "fixture-time",
        }
    ]
    assert payload["hardgates"]["SL-HG1-evidence-provenance"]["status"] == "fail"
    assert payload["hardgates"]["SL-HG5-no-injected-opening"]["status"] == "fail"


def test_scaling_ladder_l1_missing_fair_decision_does_not_inherit_l0(tmp_path):
    _write_owner_inputs(tmp_path, write_l1_decision=False)

    payload = build_scaling_ladder_payload(root=tmp_path, generated_at="fixture-time")

    assert _states(payload)["L0_toy"] == ("open", "eligible")
    assert _states(payload)["L1_tiny_sequence"] == ("closed", "unresolved-pointer")
    assert payload["hardgates"]["SL-HG3-owner-decision"]["status"] == "fail"


def test_scaling_ladder_missing_construct_hardgate_rows_close_levels(tmp_path):
    _write_owner_inputs(tmp_path)
    _write_json(
        tmp_path,
        "reports/canonical/dgt-base-undertraining-audit.json",
        {"base_undertraining_audit": {"construct_validity": {"status": "construct-valid"}}},
    )

    payload = build_scaling_ladder_payload(root=tmp_path, generated_at="fixture-time")

    assert _states(payload) == {
        "L0_toy": ("closed", "construct-validity-failed"),
        "L1_tiny_sequence": ("closed", "construct-validity-failed"),
    }
    assert payload["hardgates"]["SL-HG2-construct-validity"]["status"] == "fail"


def test_scaling_ladder_literal_separation_pass_without_ci_low_closes(tmp_path):
    _write_owner_inputs(tmp_path)
    _write_json(
        tmp_path,
        "reports/canonical/dgt-l0-controls.json",
        {
            "l0_toy_projection": {
                "owner_decision": {"status": "scaling-evidence-eligible"},
                "split_winnability": {"status": "winnable"},
                "separation": {"status": "pass"},
            }
        },
    )

    payload = build_scaling_ladder_payload(root=tmp_path, generated_at="fixture-time")

    assert _states(payload)["L0_toy"] == ("closed", "ci-low-separation-failed")
    assert _states(payload)["L1_tiny_sequence"] == ("open", "eligible")
    assert payload["hardgates"]["SL-HG4-split-separation"]["status"] == "fail"


def test_scaling_ladder_unresolved_owner_inputs_point_to_contract_cells(tmp_path):
    _write_owner_inputs(tmp_path)
    _write_json(
        tmp_path,
        "reports/canonical/discovery-gated-transformer.json",
        {"scaling_ladder": {"opened_levels": ["L0_toy"]}},
    )
    (tmp_path / "reports/canonical/index.json").unlink()

    payload = build_scaling_ladder_payload(root=tmp_path, generated_at="fixture-time")

    row = payload["levels"][0]
    assert row["state"] == "boundary"
    assert row["reason"] == "stale-or-injected"
    assert row["evidence_provenance_pointer"] == (
        "reports/canonical/scaling-ladder.json:$.levels[0].owner_contracts.evidence_provenance"
    )
    assert row["owner_contracts"]["evidence_provenance"] == {
        "required_pointer": "reports/canonical/index.json:$.evidence_provenance",
        "resolution_status": "missing-pointer",
    }
    validate_scaling_ladder_payload(payload, root=tmp_path)

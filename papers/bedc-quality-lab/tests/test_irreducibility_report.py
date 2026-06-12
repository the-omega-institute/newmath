import math

from scripts import run_irreducibility_report as irr


def _passing_flat_records():
    payload, cmi = irr.build_payload(smoke=True, generated_at="fixture")
    flat = irr._flatten_order_records(payload["records"])
    return payload, cmi, flat


def test_requires_low_order_baseline():
    _payload, _cmi, flat = _passing_flat_records()
    broken = [dict(row) for row in flat]
    broken[0]["low_order_baseline_present"] = False
    aggregation = irr._seed_aggregation(broken)
    hardgate = irr._hardgate_projector(broken, aggregation)
    assert hardgate["status"] == "fail"
    assert hardgate["failed_gate"] == "IRR-HG1"
    assert hardgate["positive_irreducibility"] is False


def test_conditioned_residual_gain_required():
    _payload, _cmi, flat = _passing_flat_records()
    broken = [dict(row) for row in flat]
    broken[0]["conditioned_residual_gain"] = 0.0
    aggregation = irr._seed_aggregation(broken)
    hardgate = irr._hardgate_projector(broken, aggregation)
    assert hardgate["status"] == "fail"
    assert hardgate["failed_gate"] == "IRR-HG2"


def test_matched_random_control_blocks_false_positive():
    _payload, _cmi, flat = _passing_flat_records()
    broken = [dict(row) for row in flat]
    control = dict(broken[0]["matched_random_control"])
    control["positive"] = True
    control["conditioned_residual_gain"] = 0.01
    broken[0]["matched_random_control"] = control
    aggregation = irr._seed_aggregation(broken)
    hardgate = irr._hardgate_projector(broken, aggregation)
    assert hardgate["status"] == "fail"
    assert hardgate["failed_gate"] == "IRR-HG3"


def test_cross_seed_stability_required():
    _payload, _cmi, flat = _passing_flat_records()
    single_seed = [row for row in flat if row["seed"] == flat[0]["seed"]]
    aggregation = irr._seed_aggregation(single_seed)
    hardgate = irr._hardgate_projector(single_seed, aggregation)
    assert hardgate["status"] == "fail"
    assert hardgate["failed_gate"] == "IRR-HG4"


def test_conditional_information_table_is_diagnostic():
    payload, cmi, flat = _passing_flat_records()
    assert payload["hardgate"]["status"] == "pass"
    assert payload["positive_claim"]["positive_irreducibility"] is True
    assert payload["conditional_information_table"]["artifact"] == irr.CMI_ARTIFACT
    assert cmi["diagnostic_only"] is True
    assert cmi["row_count"] == len(flat)
    assert all(row["diagnostic_only"] is True for row in cmi["rows"])
    assert all(row["can_set_positive_irreducibility"] is False for row in cmi["rows"])
    assert all(math.isfinite(row["bounded_cmi"]) for row in cmi["rows"])


def test_payload_contract_and_fail_closed_gates():
    payload, _cmi, flat = _passing_flat_records()
    assert payload["schema_id"] == irr.SCHEMA_ID
    assert payload["artifact_id"] == irr.ARTIFACT_ID
    assert set(payload["hardgate"]["gates"]) == {"IRR-HG1", "IRR-HG2", "IRR-HG3", "IRR-HG4"}
    assert all(row["split"]["overlap_count"] == 0 for row in flat)
    assert all(row["low_order"] == row["order"] - 1 for row in flat)
    assert all(row["finite_metrics"] is True for row in flat)

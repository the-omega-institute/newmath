import json
from copy import deepcopy
from pathlib import Path
import re
import types

import pytest

from bedc_quality_lab import ledger_aware_transformer as lat
from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.capsule import (
    ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE,
    require_architecture_claim_capsule,
)
from bedc_quality_lab.discovery_compiler.pointers import pointer_value
from bedc_quality_lab.backends.current_lab import projection as discovery_projection
from scripts import run_canonical_reports as canonical
from scripts import run_ledger_aware_transformer as runner


REQUIRED_SUMMARY_KEYS = {
    "projector",
    "run_artifacts",
    "hardgate",
    "failed_gate",
    "discovery_map_signal",
    "matched_random_control",
    "parameter_matched_baseline",
    "compute_matched_baseline",
    "component_ablation",
    "mechanism_certificate",
    "torch_training_evidence",
    "robustness_signal",
    "revocation_rows",
    "forbidden_claim_term_audit",
}

EXPECTED_SURFACE_IDS = (
    "delayed_recall",
    "compositional_rules",
    "synthetic_tool_use",
    "toy_safety_boundary",
    "toy_planning",
    "compression_preservation",
)


def _recursive_keys(value):
    if isinstance(value, dict):
        found = set(value)
        for item in value.values():
            found.update(_recursive_keys(item))
        return found
    if isinstance(value, list):
        found = set()
        for item in value:
            found.update(_recursive_keys(item))
        return found
    return set()


def _artifact_payload(root: Path, artifact: str):
    return json.loads((root / artifact).read_text(encoding="utf-8"))


def _recompute(payload):
    projection = lat.LedgerAwareTransformerProjection(
        config=lat.LedgerAwareTransformerConfig(**payload["config"]),
        records=payload["records"],
        generated_at=payload["generated_at"],
        run_artifacts=payload["run_artifacts"],
        torch_protocol=lat.TorchLedgerArmProtocol(**payload["torch_training_evidence"]["protocol"]),
        compute_protocol=payload["compute_matched_baseline"],
    )
    payload["robustness_signal"] = lat._LAT_SURFACE_SUITE.robustness_signal(payload)
    hardgates = projection.hardgate_verdicts(payload)
    failed = projection.failed_gate(hardgates)
    payload["hardgate"] = {"status": "pass" if failed is None else "fail", "gates": hardgates, "failed_gate": failed}
    payload["failed_gate"] = failed
    payload["discovery_map_signal"] = projection.discovery_map_signal(hardgates, payload)
    return payload


def test_lat_projection_has_hardgate_signal_and_required_keys():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]

    suite_ids = tuple(spec.surface_id for spec in lat.LatSurfaceSuite().surface_specs())
    assert REQUIRED_SUMMARY_KEYS <= set(payload)
    assert set(payload["hardgate"]["gates"]) == set(lat.LAT_HARDGATES)
    assert "LAT-HG7" in payload["hardgate"]["gates"]
    assert "LAT-HG8" in payload["hardgate"]["gates"]
    assert payload["hardgate"]["status"] == "pass"
    assert payload["failed_gate"] is None
    assert payload["discovery_map_signal"]["status"] == "d5-o-candidate"
    assert payload["discovery_map_signal"]["level_candidate"] == "D5-O"
    assert payload["discovery_map_signal"]["net_positive_signal"] is True
    assert payload["matched_random_control"]["control_positive_discovery"] is False
    assert payload["parameter_matched_baseline"]["status"] == "pass"
    assert payload["compute_matched_baseline"]["status"] == "pass"
    assert payload["torch_training_evidence"]["status"] == "unavailable"
    assert payload["forbidden_claim_term_audit"]["status"] == "pass"
    assert payload["aggregate_metrics"]["uer_reduction"] > 0.0
    assert payload["aggregate_metrics"]["multi_surface_uer_reduction_count"] == 3
    assert suite_ids == EXPECTED_SURFACE_IDS
    assert len(suite_ids) == 6
    assert len(set(suite_ids)) == 6
    assert tuple(row["surface_id"] for row in payload["records"]) == EXPECTED_SURFACE_IDS
    assert tuple(payload["surface_registry"]) == EXPECTED_SURFACE_IDS
    assert tuple(spec.surface_id for spec in lat.surface_specs()) == EXPECTED_SURFACE_IDS
    assert payload["robustness_signal"] == {
        "status": "pass",
        "required_pass_surface_count": 3,
        "pass_surface_count": 3,
        "pass_surface_ids": ["delayed_recall", "compositional_rules", "synthetic_tool_use"],
        "pass_surface_pointers": [
            "$.records.0.deltas.unlogged_error_rate",
            "$.records.1.deltas.unlogged_error_rate",
            "$.records.2.deltas.unlogged_error_rate",
        ],
        "surface_registry_pointer": "$.surface_registry",
        "aggregate_pointer": "$.aggregate_metrics.multi_surface_uer_reduction_count",
    }
    assert payload["hardgate"]["gates"]["LAT-HG7"]["pointer"] == "$.mechanism_certificate"
    assert payload["hardgate"]["gates"]["LAT-HG8"]["pointer"] == "$.compute_matched_baseline"


def test_lat_mechanism_certificate_component_rows_and_claim_eligibility():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    component_ablation = payload["component_ablation"]
    certificate = payload["mechanism_certificate"]

    assert component_ablation["status"] == "pass"
    assert tuple(row["component_id"] for row in component_ablation["rows"]) == lat.LAT_COMPONENT_IDS
    assert component_ablation["accepted_component_ids"] == ["ledger_head", "gap_head"]
    assert component_ablation["rejected_component_ids"] == ["route_head"]
    assert certificate["status"] == "pass"
    assert certificate["accepted_component_ids"] == component_ablation["accepted_component_ids"]
    assert certificate["claim_component_ids"] == ["ledger_head", "gap_head"]
    assert "route_head" not in certificate["claim_component_ids"]
    assert payload["positive_claim"]["mechanism_certificate_pointer"] == "$.mechanism_certificate"
    assert payload["discovery_map_signal"]["mechanism_certificate_pointer"] == "$.mechanism_certificate"
    assert pointer_value(payload, payload["positive_claim"]["mechanism_certificate_pointer"]) == certificate
    assert pointer_value(payload, payload["discovery_map_signal"]["mechanism_certificate_pointer"]) == certificate
    assert pointer_value(payload, certificate["component_ablation_pointer"]) == component_ablation
    for pointer in certificate["claim_component_pointers"]:
        row = pointer_value(payload, pointer)
        assert row["status"] == "accepted"
        assert row["claim_eligible"] is True
    for pointer in certificate["accepted_component_pointers"]:
        assert pointer_value(payload, pointer)["component_id"] in certificate["accepted_component_ids"]
    for row in component_ablation["rows"]:
        assert pointer_value(payload, row["full_arm_pointer"]) is not None
        assert pointer_value(payload, row["ablation_arm_pointer"]) is not None
        for pointer in row["source_surface_pointers"]:
            assert pointer_value(payload, pointer) > 0.0


def test_lat_compute_matched_baseline_defaults_pass_and_drives_hg8():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    baseline = payload["compute_matched_baseline"]

    assert baseline["status"] == "pass"
    assert tuple(baseline["failed_metrics"]) == ()
    assert baseline["evidence_pointer"] == "$.compute_matched_baseline"
    assert baseline["candidate_arm"]["arm_id"] == lat.COMPUTE_MATCHED_CANDIDATE_ARM
    assert baseline["baseline_arm"]["arm_id"] == lat.COMPUTE_MATCHED_BASELINE_ARM
    assert baseline["candidate_arm"]["flops_per_step"] == baseline["baseline_arm"]["flops_per_step"]
    assert baseline["candidate_arm"]["wall_time_ms_per_step"] == baseline["baseline_arm"]["wall_time_ms_per_step"]
    assert payload["hardgate"]["gates"]["LAT-HG8"]["status"] == "pass"
    assert payload["discovery_map_signal"]["compute_matched_baseline_pointer"] == "$.compute_matched_baseline"


def test_lat_parameter_matched_baseline_is_recorded_and_cost_matched():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    baseline = payload["parameter_matched_baseline"]
    protocol = baseline["protocol"]
    comparison = baseline["comparison"]
    cost_match = baseline["cost_match"]

    assert set(baseline) == {"status", "protocol", "records_pointer", "comparison", "cost_match"}
    assert baseline["status"] == "pass"
    assert baseline["records_pointer"] == "$.records"
    assert protocol["candidate_pointer"] == "$.config"
    assert protocol["records_pointer"] == "$.records"
    assert protocol["cost_pointer"] == "$.parameter_matched_baseline.cost_match"
    assert protocol["surface_ids"] == list(EXPECTED_SURFACE_IDS)
    assert protocol["sample_count"] == payload["config"]["sample_count"]
    assert protocol["train_count"] == payload["config"]["train_count"]
    assert protocol["hidden_dim"] == payload["config"]["hidden_dim"]
    assert protocol["layer_count"] == payload["config"]["layer_count"]
    assert protocol["parameter_count"] == cost_match["candidate_parameter_count"]
    assert protocol["cost_unit"] == payload["config"]["cost_unit"]
    assert protocol["uses_ledger"] is False
    assert protocol["uses_gap"] is False
    assert protocol["uses_cert"] is False
    assert protocol["uses_forbidden_columns"] is False
    assert comparison["lat_uer_pointer"] == "$.aggregate_metrics.uer_learned"
    assert comparison["baseline_uer"] == payload["aggregate_metrics"]["uer_matched_random"]
    assert comparison["uer_reduction"] == payload["aggregate_metrics"]["uer_reduction"]
    assert comparison["surface_reduction_count"] == 3
    assert comparison["required_surface_reduction_count"] == 2
    assert comparison["candidate_beats_baseline"] is True
    assert comparison["evidence_pointer"] == "$.parameter_matched_baseline.comparison"
    assert cost_match["all_match"] is True
    for field in ("sample_count", "train_count", "hidden_dim", "layer_count", "parameter_count", "cost_unit"):
        assert cost_match[f"candidate_{field}"] == cost_match[f"baseline_{field}"]

    for row in payload["records"]:
        arm = row["parameter_matched_baseline"]
        assert arm["arm"] == "parameter_matched_no_ledger_transformer"
        assert arm["uses_ledger"] is False
        assert arm["uses_gap"] is False
        assert arm["uses_cert"] is False
        assert arm["uses_forbidden_columns"] is False
        assert arm["cost_pointer"] == "$.parameter_matched_baseline.cost_match"
        assert pointer_value(payload, arm["cost_pointer"]) == cost_match
        assert arm["metrics"]["unlogged_error_rate"] >= row["gap_head"]["metrics"]["unlogged_error_rate"]


def test_canonical_summary_pointers_and_capsule_source_resolve(tmp_path):
    paths = runner.write_report(root=tmp_path, generated_at="fixture-time")
    payload = json.loads(paths["json"].read_text(encoding="utf-8"))
    capsule = pointer_value(payload, payload["claim_capsule_ref"]["pointer"])
    spec = canonical._specs_by_name()["ledger-aware-transformer"]

    for pointer in (
        spec.scope_pointer,
        spec.cost_pointer,
        spec.not_claimed_pointer,
        spec.positive_claim_pointer,
        spec.control_pointer,
        payload["positive_claim"]["evidence_pointer"],
        payload["positive_claim"]["control_pointer"],
        payload["positive_claim"]["surface_registry_pointer"],
        payload["discovery_map_signal"]["evidence_pointer"],
        payload["discovery_map_signal"]["control_pointer"],
        payload["discovery_map_signal"]["torch_training_evidence_pointer"],
        payload["discovery_map_signal"]["robustness_evidence_pointer"],
        payload["discovery_map_signal"]["parameter_matched_baseline_pointer"],
        payload["discovery_map_signal"]["compute_matched_baseline_pointer"],
        payload["discovery_map_signal"]["mechanism_certificate_pointer"],
        payload["robustness_signal"]["surface_registry_pointer"],
        payload["robustness_signal"]["aggregate_pointer"],
    ):
        assert pointer_value(payload, pointer) is not None

    for pointer in payload["robustness_signal"]["pass_surface_pointers"]:
        assert pointer_value(payload, pointer) > 0.0

    for row in payload["ledger"]["rows"]:
        assert pointer_value(payload, row["evidence_pointer"]) is not None
        assert pointer_value(payload, row["control_pointer"]) is not None
        assert pointer_value(payload, row["ledger_decision_pointer"]) is not None

    assert capsule["capsule_subtype"] == ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE
    require_architecture_claim_capsule(capsule)
    source = _artifact_payload(tmp_path, capsule["source"])
    assert pointer_value(source, capsule["source_pointer"]) is not None
    for key in ("candidate_pointer", "evidence_pointer"):
        cell = capsule["model_claim"][key]
        assert pointer_value(_artifact_payload(tmp_path, cell["artifact"]), cell["pointer"]) is not None
    for baseline in capsule["model_claim"]["baselines"]:
        assert pointer_value(_artifact_payload(tmp_path, baseline["artifact"]), baseline["pointer"]) is not None
    assert {"artifact": lat.JSON_ARTIFACT, "pointer": "$.parameter_matched_baseline"} in capsule["model_claim"]["baselines"]
    assert {"artifact": lat.JSON_ARTIFACT, "pointer": "$.compute_matched_baseline"} in capsule["model_claim"]["baselines"]


def test_lat_compute_matched_flops_failure_demotes_to_dn():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    mutated = deepcopy(payload)
    mutated["compute_matched_baseline"]["candidate_arm"]["flops_per_step"] = (
        mutated["compute_matched_baseline"]["baseline_arm"]["flops_per_step"] * 1.2
    )
    mutated["compute_matched_baseline"]["failed_metrics"] = ["flops_per_step"]
    mutated["compute_matched_baseline"]["status"] = "fail"

    _recompute(mutated)

    assert mutated["hardgate"]["status"] == "fail"
    assert mutated["hardgate"]["gates"]["LAT-HG8"]["status"] == "fail"
    assert mutated["failed_gate"] == "LAT-HG8"
    assert mutated["discovery_map_signal"]["level_candidate"] == "DN"
    assert pointer_value(mutated, mutated["discovery_map_signal"]["failed_gate_pointer"]) == "fail"


def test_lat_mechanism_certificate_failure_demotes_to_dn():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    mutated = deepcopy(payload)
    mutated["component_ablation"]["by_component"]["gap_head"]["status"] = "rejected"
    mutated["component_ablation"]["by_component"]["gap_head"]["claim_eligible"] = False
    mutated["mechanism_certificate"]["accepted_component_ids"] = ["ledger_head"]
    mutated["mechanism_certificate"]["claim_component_ids"] = ["ledger_head"]
    mutated["mechanism_certificate"]["claim_component_pointers"] = ["$.component_ablation.by_component.ledger_head"]
    mutated["mechanism_certificate"]["accepted_component_pointers"] = ["$.component_ablation.by_component.ledger_head"]
    mutated["mechanism_certificate"]["status"] = "fail"

    _recompute(mutated)

    assert mutated["hardgate"]["status"] == "fail"
    assert mutated["hardgate"]["gates"]["LAT-HG7"]["status"] == "fail"
    assert mutated["failed_gate"] == "LAT-HG7"
    assert mutated["discovery_map_signal"]["level_candidate"] == "DN"
    assert pointer_value(mutated, mutated["discovery_map_signal"]["failed_gate_pointer"]) == "fail"


def test_lat_compute_matched_wall_time_failure_demotes_to_dn():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    mutated = deepcopy(payload)
    mutated["compute_matched_baseline"]["candidate_arm"]["wall_time_ms_per_step"] = (
        mutated["compute_matched_baseline"]["baseline_arm"]["wall_time_ms_per_step"] * 1.2
    )
    mutated["compute_matched_baseline"]["failed_metrics"] = ["wall_time_ms_per_step"]
    mutated["compute_matched_baseline"]["status"] = "fail"

    _recompute(mutated)

    assert mutated["hardgate"]["status"] == "fail"
    assert mutated["failed_gate"] == "LAT-HG8"
    assert mutated["hardgate"]["gates"]["LAT-HG8"]["status"] == "fail"
    assert mutated["discovery_map_signal"]["level_candidate"] == "DN"


def test_lat_zero_rows_fail_closed_to_dn():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    mutated = deepcopy(payload)
    mutated["records"] = []

    _recompute(mutated)

    assert mutated["hardgate"]["status"] == "fail"
    assert mutated["failed_gate"] == "LAT-HG1"
    assert mutated["discovery_map_signal"]["level_candidate"] == "DN"
    assert pointer_value(mutated, mutated["discovery_map_signal"]["failed_gate_pointer"]) == "fail"


def test_lat_dangling_pointer_fail_closed_to_dn():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    mutated = deepcopy(payload)
    mutated["ledger"]["rows"][0]["evidence_pointer"] = "$.records.99.gap_head.metrics"

    _recompute(mutated)

    assert mutated["hardgate"]["status"] == "fail"
    assert mutated["failed_gate"] == "LAT-HG2"
    assert mutated["discovery_map_signal"]["level_candidate"] == "DN"
    assert pointer_value(mutated, mutated["discovery_map_signal"]["failed_gate_pointer"]) == "fail"


@pytest.mark.parametrize(
    "mutate, gate",
    [
        (lambda payload: payload["aggregate_metrics"].update({"uer_reduction": 0.0}), "LAT-HG3"),
        (lambda payload: payload["aggregate_metrics"].update({"multi_surface_uer_reduction_count": 1}), "LAT-HG3"),
        (lambda payload: payload["aggregate_metrics"].update({"only_false_alarm_increase": True}), "LAT-HG4"),
        (lambda payload: payload["matched_random_control"].update({"control_positive_discovery": True}), "LAT-HG4"),
    ],
)
def test_lat_matched_random_or_multisurface_failure_demotes(mutate, gate):
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    mutated = deepcopy(payload)
    mutate(mutated)

    _recompute(mutated)

    assert mutated["hardgate"]["status"] == "fail"
    assert mutated["failed_gate"] == gate
    assert mutated["discovery_map_signal"]["level_candidate"] == "DN"


def test_lat_robustness_signal_failure_does_not_drive_hg7():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    mutated = deepcopy(payload)
    for index in range(3):
        mutated["records"][index]["deltas"]["unlogged_error_rate"] = 0.0

    _recompute(mutated)

    assert mutated["robustness_signal"]["status"] == "fail"
    assert mutated["robustness_signal"]["pass_surface_count"] == 0
    assert mutated["hardgate"]["gates"]["LAT-HG7"]["status"] == "pass"
    assert mutated["failed_gate"] is None
    assert mutated["discovery_map_signal"]["level_candidate"] == "D5-O"

    overlay, evidence = discovery_projection._ledger_aware_transformer_projection(mutated)

    assert overlay["main_verdict"]["ledger_aware_transformer"]["level_candidate"] == "DN"
    assert "evidence_basis" not in overlay
    assert evidence.failed_gate == "$.robustness_signal.status"


def test_lat_robustness_pointer_dangling_demotes():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    missing = deepcopy(payload)
    missing["discovery_map_signal"]["robustness_evidence_pointer"] = "$.missing_robustness_signal"
    projection = lat.LedgerAwareTransformerProjection(
        config=lat.LedgerAwareTransformerConfig(**missing["config"]),
        records=missing["records"],
        generated_at=missing["generated_at"],
        run_artifacts=missing["run_artifacts"],
        torch_protocol=lat.TorchLedgerArmProtocol(**missing["torch_training_evidence"]["protocol"]),
    )
    refreshed = projection.discovery_map_signal(missing["hardgate"]["gates"], missing)

    assert refreshed["level_candidate"] == "DN"
    assert refreshed["reason"] == "lat-discovery-map-pointer-dangling"
    assert pointer_value(refreshed, refreshed["failed_gate_pointer"]) is None

    baseline_overlay, baseline_evidence = discovery_projection._ledger_aware_transformer_projection(payload)
    assert baseline_overlay["main_verdict"]["ledger_aware_transformer"]["level_candidate"] == "D5-O"
    assert baseline_evidence.failed_gate is None


def test_lat_parameter_matched_failure_demotes_to_dn():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    mutated = deepcopy(payload)
    mutated["parameter_matched_baseline"]["comparison"]["candidate_beats_baseline"] = False
    mutated["parameter_matched_baseline"]["status"] = "fail"

    _recompute(mutated)

    assert mutated["hardgate"]["status"] == "fail"
    assert mutated["hardgate"]["gates"]["LAT-HG7"]["status"] == "fail"
    assert mutated["failed_gate"] == "LAT-HG7"
    assert mutated["discovery_map_signal"]["level_candidate"] == "DN"
    assert pointer_value(mutated, mutated["discovery_map_signal"]["failed_gate_pointer"]) == "fail"


def test_lat_missing_parameter_matched_owner_projects_dn():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    mutated = deepcopy(payload)
    del mutated["parameter_matched_baseline"]

    overlay, evidence = discovery_projection._ledger_aware_transformer_projection(mutated)
    row = discovery_projection.discovery_row(canonical._specs_by_name()["ledger-aware-transformer"], mutated)

    assert overlay["main_verdict"]["ledger_aware_transformer"]["level_candidate"] == "DN"
    assert evidence.failed_gate == "$.parameter_matched_baseline"
    assert row["discovery_level"] == "DN"
    assert row["failed_gate"] == "$.parameter_matched_baseline"
    assert row["audit_reason"] == "missing-lat-parameter-matched-baseline"


@pytest.mark.parametrize(
    "comparison_patch",
    [
        {"uer_reduction": 0.0},
        {"surface_reduction_count": lat.REQUIRED_PARAMETER_MATCHED_SURFACE_REDUCTION_COUNT - 1},
    ],
)
def test_lat_parameter_matched_stale_numeric_facts_demote_to_dn(comparison_patch):
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    mutated = deepcopy(payload)
    mutated["parameter_matched_baseline"]["status"] = "pass"
    mutated["parameter_matched_baseline"]["comparison"]["candidate_beats_baseline"] = True
    mutated["parameter_matched_baseline"]["comparison"].update(comparison_patch)

    _recompute(mutated)

    assert mutated["hardgate"]["status"] == "fail"
    assert mutated["hardgate"]["gates"]["LAT-HG7"]["status"] == "fail"
    assert mutated["failed_gate"] == "LAT-HG7"
    assert mutated["discovery_map_signal"]["level_candidate"] != "D5-O"


def test_lat_parameter_matched_forbidden_channel_demotes_to_dn():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    mutated = deepcopy(payload)
    mutated["parameter_matched_baseline"]["protocol"]["uses_gap"] = True

    _recompute(mutated)

    assert mutated["hardgate"]["status"] == "fail"
    assert mutated["failed_gate"] == "LAT-HG7"
    assert mutated["hardgate"]["gates"]["LAT-HG7"]["status"] == "fail"
    assert mutated["discovery_map_signal"]["level_candidate"] == "DN"


def test_lat_torch_unavailable_records_boundary_without_crash():
    payload = runner.build_projection(
        generated_at="fixture-time",
        requested_device="mps",
        enable_torch=False,
        steps=12,
    )["summary_payload"]
    evidence = payload["torch_training_evidence"]
    protocol = evidence["protocol"]

    assert evidence["status"] == "unavailable"
    assert protocol["requested_device"] == "mps"
    assert protocol["resolved_device"] == "not-requested"
    assert protocol["seed"] == payload["config"]["seed"]
    assert protocol["steps"] == 12
    assert protocol["dtype"] == "float32"
    assert protocol["drift_tolerance"] == pytest.approx(lat.DRIFT_TOLERANCE)
    assert evidence["row_count"] == 0
    assert pointer_value(payload, "$.torch_training_evidence.protocol") is not None
    assert payload["hardgate"]["gates"]["LAT-HG6"]["status"] == "pass"


def test_lat_torch_available_protocol_records_seed_device_and_tolerance(monkeypatch):
    fake_torch = types.SimpleNamespace(
        manual_seed=lambda seed: None,
        backends=types.SimpleNamespace(mps=types.SimpleNamespace(is_available=lambda: False)),
    )
    monkeypatch.setitem(__import__("sys").modules, "torch", fake_torch)

    protocol = runner.collect_torch_protocol(
        requested_device="mps",
        seed=756,
        steps=8,
        enable_torch=True,
    )

    assert protocol.status == "available"
    assert protocol.requested_device == "mps"
    assert protocol.resolved_device == "cpu"
    assert protocol.seed == 756
    assert protocol.steps == 8
    assert protocol.drift_tolerance == pytest.approx(lat.DRIFT_TOLERANCE)
    assert protocol.row_count == 2


def test_lat_no_terminal_verdict_recursive_and_regen_idempotent(tmp_path):
    first = runner.write_report(root=tmp_path, generated_at="fixture-time")
    first_payload = json.loads(first["json"].read_text(encoding="utf-8"))
    first_markdown = first["markdown"].read_text(encoding="utf-8")
    second = runner.write_report(root=tmp_path, generated_at="fixture-time")
    second_payload = json.loads(second["json"].read_text(encoding="utf-8"))
    second_markdown = second["markdown"].read_text(encoding="utf-8")

    assert "terminal_verdict" not in _recursive_keys(first_payload)
    assert "terminal_verdict" not in _recursive_keys(first_payload["claim_capsule_ref"]["capsule"])
    assert "terminal_verdict" not in first_markdown
    assert json.dumps(first_payload, sort_keys=True) == json.dumps(second_payload, sort_keys=True)
    assert first_markdown == second_markdown


def test_lat_emitted_naming_surfaces_have_no_version_or_round_tokens():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    naming_cells = [
        payload["artifact_id"],
        payload["schema_id"],
        payload["run_id"],
        payload["producer"],
        payload["projector"],
        *payload["surface_registry"].keys(),
        *(row["surface_id"] for row in payload["records"]),
        *(row["row_id"] for row in payload["ledger"]["rows"]),
        *payload["hardgate"]["gates"].keys(),
    ]
    forbidden = re.compile(r"(?:^|[-_/])(?:v[0-9]+|round[0-9]*|r[0-9]+)(?:$|[-_/])", re.IGNORECASE)

    assert all(forbidden.search(cell) is None for cell in naming_cells)


def test_lat_forbidden_claim_term_demotes():
    payload = runner.build_projection(generated_at="fixture-time")["summary_payload"]
    mutated = deepcopy(payload)
    mutated["positive_claim"]["claim"] = f"{mutated['positive_claim']['claim']} {FORBIDDEN_POSITIVE_CLAIM_TERMS[0]}"
    mutated["forbidden_claim_term_audit"] = lat._forbidden_term_audit(mutated["positive_claim"])

    _recompute(mutated)

    assert mutated["forbidden_claim_term_audit"]["status"] == "fail"
    assert mutated["hardgate"]["status"] == "fail"
    assert mutated["failed_gate"] == "LAT-HG5"
    assert mutated["discovery_map_signal"]["level_candidate"] == "DN"

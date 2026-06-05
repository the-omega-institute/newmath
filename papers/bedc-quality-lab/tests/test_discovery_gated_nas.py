import json

from bedc_quality_lab.discovery_compiler.pointers import pointer_value
from bedc_quality_lab.discovery_gated_nas import (
    DEFAULT_CANDIDATES,
    DEFAULT_SEEDS,
    DEFAULT_SURFACES,
    DG_NAS_HARDGATES,
    NEGATIVE_WITNESS_MUTATIONS,
)
from bedc_quality_lab.backends.current_lab.projection import discovery_row, projection_payload
from bedc_quality_lab.research_discovery import assign_discovery_level
from scripts import run_discovery_gated_nas as runner
from scripts.run_canonical_reports import _specs_by_name


def _payload():
    return runner.build_projection(generated_at="fixture-time")["summary_payload"]


def _walk(value):
    if isinstance(value, dict):
        yield value
        for item in value.values():
            yield from _walk(item)
    elif isinstance(value, list):
        for item in value:
            yield from _walk(item)


def test_deterministic_replay_and_seed_idempotence():
    first = runner.build_projection(generated_at="fixture-time")
    second = runner.build_projection(generated_at="fixture-time")

    assert json.dumps(first, sort_keys=True) == json.dumps(second, sort_keys=True)
    assert first["summary_payload"]["grid"]["record_count"] == len(DEFAULT_CANDIDATES) * len(DEFAULT_SURFACES) * len(DEFAULT_SEEDS) * 3


def test_search_objective_calculation_is_quantized():
    row = runner.deterministic_record("bounded_discovery_gate", "copy_shift", 19, "candidate")
    expected = round(
        row["quality_q"]
        + row["discovery_bonus"]
        - runner.DEFAULT_LAMBDA_COMPUTE * row["compute_cost"]
        - runner.DEFAULT_LAMBDA_WITNESS * row["witness_violation_count"],
        6,
    )

    assert row["search_score"] == expected
    assert abs(row["search_score"] - expected) <= 1.0e-6


def test_negative_witness_mutations_and_demotions():
    payload = _payload()
    rows = payload["negative_witness_mutations"]["rows"]

    assert payload["negative_witness_mutations"]["mutation_map"] == NEGATIVE_WITNESS_MUTATIONS
    assert {row["witness_kind"] for row in rows} == set(NEGATIVE_WITNESS_MUTATIONS)
    assert all(row["source_candidate_demoted"] is True for row in rows)
    assert payload["negative_witness_mutations"]["demoted_candidate_count"] == payload["negative_witness_mutations"]["witness_violating_candidate_count"]
    assert payload["negative_witness_mutations"]["selected_candidate_has_violation"] is False


def test_torch_boundary_and_device_fields():
    disabled = runner.build_projection(generated_at="fixture-time", enable_torch=False)["summary_payload"]
    enabled = runner.build_projection(generated_at="fixture-time", enable_torch=True, requested_device="mps")["summary_payload"]

    assert disabled["torch_nas_evidence"]["status"] == "unavailable"
    assert disabled["device_protocol"]["requested_device"] == "auto"
    assert disabled["device_protocol"]["resolved_device"] == "not-requested"
    assert enabled["device_protocol"]["requested_device"] == "mps"
    assert enabled["device_protocol"]["resolved_device"] in {"mps", "cpu", "not-available"}
    assert enabled["torch_nas_evidence"]["status"] in {"available", "unavailable"}


def test_hardgates_pointer_resolve_and_no_terminal_verdict():
    payload = _payload()

    assert tuple(payload["hardgate"]["gates"][gate]["status"] for gate in DG_NAS_HARDGATES) == ("pass",) * len(DG_NAS_HARDGATES)
    assert payload["hardgate"]["status"] == "pass"
    for gate in DG_NAS_HARDGATES:
        pointer = payload["hardgate"]["gates"][gate]["evidence_pointer"]
        assert pointer_value(payload, pointer) is not None, gate
    for pointer in (
        payload["discovery_map_signal"]["evidence_pointer"],
        payload["discovery_map_signal"]["control_pointer"],
        payload["discovery_map_signal"]["surface_registry_pointer"],
        payload["discovery_map_signal"]["candidate_protocol_pointer"],
        payload["discovery_map_signal"]["search_objective_pointer"],
        payload["discovery_map_signal"]["negative_witness_pointer"],
        payload["discovery_map_signal"]["torch_nas_evidence_pointer"],
    ):
        assert pointer_value(payload, pointer) is not None, pointer
    assert all("terminal_verdict" not in cell for cell in _walk(payload))


def test_projection_maps_to_d5_m_with_ready_scorecard():
    payload = _payload()
    spec = _specs_by_name()["discovery-gated-nas"]
    context = {"reports/canonical/quality-scorecard.json": {"rows": [{"status": "ready"}]}}
    projected = projection_payload(spec, payload, context)
    verdict = assign_discovery_level(projected)
    row = discovery_row(spec, payload, context)

    assert verdict.discovery_level == "D5-M"
    assert row["discovery_level"] == "D5-M"
    assert row["audit_status"] == "valid"
    assert row["control_pointer"] == "$.matched_baseline_control"


def test_candidate_with_witness_violation_fails_hg6_when_not_demoted():
    projection = runner.build_projection(generated_at="fixture-time")
    payload = projection["summary_payload"]
    broken = {
        **payload["negative_witness_mutations"],
        "demoted_candidate_count": payload["negative_witness_mutations"]["witness_violating_candidate_count"] - 1,
    }
    mutated = {**payload, "negative_witness_mutations": broken}
    hardgates = runner.DiscoveryGatedNasProjection(
        config=payload["config"],
        records=projection["raw_rows"],
        generated_at="fixture-time",
        run_artifacts=payload["run_artifacts"],
    ).hardgate_verdicts({**runner.DiscoveryGatedNasProjection(
        config=payload["config"],
        records=projection["raw_rows"],
        generated_at="fixture-time",
        run_artifacts=payload["run_artifacts"],
    )._summaries(), "negative_witness_mutations": broken})

    assert hardgates["DG-NAS-HG6"]["status"] == "fail"
    assert mutated["negative_witness_mutations"]["demoted_candidate_count"] < mutated["negative_witness_mutations"]["witness_violating_candidate_count"]


def test_runner_writes_pointer_resolvable_artifacts(tmp_path):
    projection = runner.build_projection(generated_at="fixture-time")
    runner.write_artifacts(projection, root=tmp_path)
    payload = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))

    assert payload["source_artifacts"]["raw_rows"] == payload["run_artifacts"]["raw_metrics"]
    assert (tmp_path / payload["run_artifacts"]["raw_metrics"]).exists()
    assert pointer_value(payload, "$.search_objective_summary.selected_candidate") is not None

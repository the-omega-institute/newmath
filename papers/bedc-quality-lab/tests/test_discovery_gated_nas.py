import json

import pytest

from bedc_quality_lab.discovery_compiler.pointers import pointer_value
import bedc_quality_lab.discovery_gated_nas as dgn
from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_gated_nas import (
    DEFAULT_CANDIDATES,
    DEFAULT_SEEDS,
    DEFAULT_SURFACES,
    DESIGN_SEARCH_CERTIFICATE_OWNER_POINTER,
    DESIGN_SEARCH_CERTIFICATE_SLOT_POINTER,
    DG_NAS_HARDGATES,
    DiscoveryGatedNasProjection,
    NEGATIVE_WITNESS_MUTATIONS,
    design_search_certificate_hg7,
)
from bedc_quality_lab.backends.current_lab.projection import discovery_row, projection_payload
from bedc_quality_lab.research_discovery import assign_discovery_level
from scripts import run_discovery_gated_nas as runner
from scripts.run_canonical_reports import _specs_by_name


def _payload():
    return runner.build_projection(generated_at="fixture-time")["summary_payload"]


def _ready_payload():
    return runner.build_projection(
        generated_at="fixture-time",
        design_search_certificate_slot_state="present",
    )["summary_payload"]


def _project_from_rows(rows):
    base = _ready_payload()
    return DiscoveryGatedNasProjection(
        config=base["config"],
        records=rows,
        generated_at="fixture-time",
        run_artifacts=base["run_artifacts"],
    ).project()["summary_payload"]


def _with_recomputed_signal(payload):
    projection = DiscoveryGatedNasProjection(
        config=payload["config"],
        records=[],
        generated_at="fixture-time",
        run_artifacts=payload["run_artifacts"],
    )
    hardgates = projection.hardgate_verdicts(
        {
            "matched_baseline_control": payload["matched_baseline_control"],
            "search_objective_summary": payload["search_objective_summary"],
            "negative_witness_mutations": payload["negative_witness_mutations"],
            "candidate_protocol": payload["candidate_protocol"],
            "search_space": payload.get("search_space"),
        }
    )
    failed = projection.failed_gate(hardgates)
    return {
        **payload,
        "hardgate": {"status": "pass" if failed is None else "fail", "gates": hardgates, "failed_gate": failed},
        "failed_gate": failed,
        "discovery_map_signal": projection.discovery_map_signal(hardgates),
    }


def _assert_dn_projection(payload, gate):
    spec = _specs_by_name()["discovery-gated-nas"]
    context = {"reports/canonical/quality-scorecard.json": {"rows": [{"status": "ready"}]}}
    projected = projection_payload(spec, payload, context)
    verdict = assign_discovery_level(projected)
    row = discovery_row(spec, payload, context)
    failed_pointer = f"$.hardgate.gates.{gate}.status"

    assert payload["hardgate"]["status"] == "fail"
    assert payload["hardgate"]["failed_gate"] == gate
    assert payload["discovery_map_signal"]["level_candidate"] == "DN"
    assert payload["discovery_map_signal"]["failed_gate"] == gate
    assert payload["discovery_map_signal"]["failed_gate_pointer"] == failed_pointer
    assert verdict.discovery_level == "DN"
    assert verdict.terminal_verdict == "rejected"
    assert row["discovery_level"] == "DN"
    assert row["terminal_verdict"] == "rejected"
    assert row["failed_gate"] == failed_pointer
    assert row["audit_status"] == "valid"


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
    payload = _ready_payload()

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
        payload["candidate_protocol"]["search_space_pointer"],
        payload["discovery_map_signal"]["search_space_pointer"],
        payload["discovery_map_signal"]["search_objective_pointer"],
        payload["discovery_map_signal"]["negative_witness_pointer"],
        payload["discovery_map_signal"]["torch_nas_evidence_pointer"],
    ):
        assert pointer_value(payload, pointer) is not None, pointer
    assert all("terminal_verdict" not in cell for cell in _walk(payload))


def test_search_space_boundary_is_top_level_owner_and_pointers_resolve():
    payload = _ready_payload()

    assert "search_space" in payload
    assert payload["candidate_protocol"]["search_space_pointer"] == "$.search_space"
    assert payload["discovery_map_signal"]["search_space_pointer"] == "$.search_space"
    for pointer in (
        "$.search_space",
        payload["candidate_protocol"]["search_space_pointer"],
        payload["discovery_map_signal"]["search_space_pointer"],
    ):
        assert pointer_value(payload, pointer) is payload["search_space"]


def test_search_space_boundary_matches_exhaustive_product():
    payload = _ready_payload()
    search_space = payload["search_space"]

    assert search_space["status"] == "closed"
    assert search_space["candidates"] == list(DEFAULT_CANDIDATES)
    assert search_space["surfaces"] == list(DEFAULT_SURFACES)
    assert search_space["seeds"] == list(DEFAULT_SEEDS)
    assert search_space["arms"] == list(dgn.DEFAULT_ARMS)
    assert search_space["sampling_protocol"]["mode"] == "exhaustive_product"
    assert search_space["expected_record_count"] == 162
    assert search_space["observed_record_count"] == 162
    assert search_space["missing_cells"] == []
    assert search_space["out_of_space_rows"] == []


def test_search_space_gate_fails_closed_without_search_space():
    payload = _ready_payload()
    mutated = {key: value for key, value in payload.items() if key != "search_space"}
    recomputed = _with_recomputed_signal(mutated)

    assert recomputed["hardgate"]["status"] == "fail"
    assert recomputed["hardgate"]["failed_gate"] == "DG-NAS-HG7"
    assert recomputed["discovery_map_signal"]["level_candidate"] == "DN"
    assert recomputed["discovery_map_signal"]["failed_gate"] == "DG-NAS-HG7"
    assert recomputed["discovery_map_signal"]["failed_gate_pointer"] == "$.hardgate.gates.DG-NAS-HG7.status"


def test_search_space_gate_fails_closed_for_open_or_out_of_space_rows():
    payload = _ready_payload()
    opened = {
        **payload,
        "search_space": {
            **payload["search_space"],
            "status": "open",
        },
    }
    _assert_dn_projection(_with_recomputed_signal(opened), "DG-NAS-HG7")

    projection = runner.build_projection(
        generated_at="fixture-time",
        design_search_certificate_slot_state="present",
        candidates=DEFAULT_CANDIDATES,
    )
    rows = [
        *projection["raw_rows"],
        {
            **projection["raw_rows"][0],
            "candidate_id": "declared-product-external",
        },
    ]
    out_of_space = _project_from_rows(rows)

    _assert_dn_projection(out_of_space, "DG-NAS-HG7")


def test_discovery_map_signal_requires_search_space_pointer():
    payload = _ready_payload()
    spec = _specs_by_name()["discovery-gated-nas"]
    context = {"reports/canonical/quality-scorecard.json": {"rows": [{"status": "ready"}]}}
    mutated = {
        **payload,
        "discovery_map_signal": {
            **payload["discovery_map_signal"],
            "search_space_pointer": "$.grid",
        },
    }
    row = discovery_row(spec, mutated, context)

    assert row["audit_status"] == "invalid"
    assert row["audit_reason"] == "dg-nas-search-space-pointer-mismatch"


def test_projection_keeps_d5_m_candidate_at_d5_o_without_attribution_capsule_surface():
    payload = _ready_payload()
    spec = _specs_by_name()["discovery-gated-nas"]
    context = {"reports/canonical/quality-scorecard.json": {"rows": [{"status": "ready"}]}}
    projected = projection_payload(spec, payload, context)
    verdict = assign_discovery_level(projected)
    row = discovery_row(spec, payload, context)

    assert verdict.discovery_level == "D5-O"
    assert row["discovery_level"] == "D5-O"
    assert row["audit_status"] == "valid"
    assert row["control_pointer"] == "$.matched_baseline_control"


def test_candidate_with_witness_violation_fails_hg6_when_not_demoted():
    projection = runner.build_projection(generated_at="fixture-time", design_search_certificate_slot_state="present")
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


def test_hg1_fails_closed_without_parameter_matched_baseline_rows():
    projection = runner.build_projection(generated_at="fixture-time", design_search_certificate_slot_state="present")
    rows = [row for row in projection["raw_rows"] if row.get("arm") != "parameter_matched_baseline"]
    payload = _project_from_rows(rows)

    _assert_dn_projection(payload, "DG-NAS-HG1")


def test_hg2_fails_closed_without_compute_matched_baseline_rows():
    projection = runner.build_projection(generated_at="fixture-time", design_search_certificate_slot_state="present")
    rows = [row for row in projection["raw_rows"] if row.get("arm") != "compute_matched_baseline"]
    payload = _project_from_rows(rows)

    _assert_dn_projection(payload, "DG-NAS-HG2")


def test_hg3_fails_closed_without_selected_classifier_shift():
    projection = runner.build_projection(generated_at="fixture-time", design_search_certificate_slot_state="present")
    rows = [
        {**row, "classifier_shift_count": 0, "discovery_bonus": 0.0}
        if row.get("candidate_id") == "bounded_discovery_gate" and row.get("arm") == "candidate"
        else row
        for row in projection["raw_rows"]
    ]
    payload = _project_from_rows(rows)

    _assert_dn_projection(payload, "DG-NAS-HG3")


def test_hg4_fails_closed_without_multi_surface_robustness():
    payload = _ready_payload()
    selected = {
        **payload["search_objective_summary"]["selected_candidate"],
        "multi_surface_robust": False,
    }
    mutated = {
        **payload,
        "search_objective_summary": {
            **payload["search_objective_summary"],
            "selected_candidate": selected,
            "selected_multi_surface_robust": False,
        },
    }

    _assert_dn_projection(_with_recomputed_signal(mutated), "DG-NAS-HG4")


def test_hg5_fails_closed_without_mechanism_certificate():
    payload = _ready_payload()
    selected = {
        **payload["search_objective_summary"]["selected_candidate"],
        "mechanism_certificate": False,
    }
    mutated = {
        **payload,
        "search_objective_summary": {
            **payload["search_objective_summary"],
            "selected_candidate": selected,
            "selected_mechanism_certificate": False,
        },
    }

    _assert_dn_projection(_with_recomputed_signal(mutated), "DG-NAS-HG5")


def test_forbidden_alias_row_refuses_projection():
    projection = runner.build_projection(generated_at="fixture-time")
    rows = [{**projection["raw_rows"][0], "forbidden_alias_count": 1}, *projection["raw_rows"][1:]]

    with pytest.raises(ValueError, match="forbidden alias"):
        DiscoveryGatedNasProjection(
            config=projection["summary_payload"]["config"],
            records=rows,
            generated_at="fixture-time",
            run_artifacts=projection["summary_payload"]["run_artifacts"],
        ).project()


def test_forbidden_positive_claim_term_demotes_to_dn(monkeypatch):
    term = FORBIDDEN_POSITIVE_CLAIM_TERMS[0]
    monkeypatch.setattr(
        dgn,
        "POSITIVE_CLAIM",
        {
            **dgn.POSITIVE_CLAIM,
            "text": f"Discovery-gated NAS claim mentions {term}.",
        },
    )

    projected = runner.build_projection(generated_at="fixture-time", design_search_certificate_slot_state="present")
    payload = projected["summary_payload"]

    assert payload["claim_capsule_status"] == "failed"
    assert payload["failed_gate"] == "forbidden-positive-claim-term"
    assert payload["hardgate"]["gates"]["forbidden-positive-claim-term"]["status"] == "fail"
    assert payload["discovery_map_signal"]["level_candidate"] == "DN"
    assert payload["discovery_map_signal"]["failed_gate"] == "forbidden-positive-claim-term"
    assert payload["discovery_map_signal"]["failed_gate_pointer"] == "$.forbidden_claim_term_audit.status"
    assert payload["forbidden_claim_term_audit"]["status"] == "fail"
    assert payload["forbidden_claim_term_audit"]["hits"] == [term]
    assert projected["claim_capsule_payload"]["claim_status"] == "failed"
    assert projected["claim_capsule_payload"]["failed_gate"] == "forbidden-positive-claim-term"


def test_negative_dg_nas_projection_maps_failed_hardgate_to_dn_row():
    projection = runner.build_projection(generated_at="fixture-time", design_search_certificate_slot_state="present")
    rows = [row for row in projection["raw_rows"] if row.get("arm") != "parameter_matched_baseline"]
    payload = _project_from_rows(rows)
    spec = _specs_by_name()["discovery-gated-nas"]
    context = {"reports/canonical/quality-scorecard.json": {"rows": [{"status": "ready"}]}}

    projected = projection_payload(spec, payload, context)
    row = discovery_row(spec, payload, context)

    assert projected["verdict"] == "rejected"
    assert projected["main_verdict"]["discovery_gated_nas"] == {
        "level_candidate": "DN",
        "status": "negative",
    }
    assert row["discovery_level"] == "DN"
    assert row["terminal_verdict"] == "rejected"
    assert row["failed_gate"] == "$.hardgate.gates.DG-NAS-HG1.status"
    assert row["audit_status"] == "valid"
    pointer_mismatch = {
        **payload,
        "discovery_map_signal": {
            **payload["discovery_map_signal"],
            "failed_gate_pointer": "$.hardgate.gates.DG-NAS-HG2.status",
        },
    }
    mismatch_row = discovery_row(spec, pointer_mismatch, context)
    assert mismatch_row["audit_status"] == "invalid"
    assert mismatch_row["audit_reason"] == "dg-nas-failed_gate_pointer-mismatch"


def test_runner_writes_pointer_resolvable_artifacts(tmp_path):
    projection = runner.build_projection(generated_at="fixture-time")
    runner.write_artifacts(projection, root=tmp_path)
    payload = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    rewritten = json.loads(json.dumps(payload))

    assert payload["source_artifacts"]["raw_rows"] == payload["run_artifacts"]["raw_metrics"]
    assert (tmp_path / payload["run_artifacts"]["raw_metrics"]).exists()
    assert set(rewritten) == set(payload)
    assert rewritten["candidate_protocol"]["design_search_certificate"] == payload["candidate_protocol"]["design_search_certificate"]
    assert pointer_value(payload, "$.search_objective_summary.selected_candidate") is not None
    assert payload["candidate_protocol"]["design_search_certificate"] == {
        "owner_pointer": DESIGN_SEARCH_CERTIFICATE_OWNER_POINTER,
        "slot_state": "present-but-fail-closed",
    }
    assert pointer_value(payload, DESIGN_SEARCH_CERTIFICATE_SLOT_POINTER) == payload["candidate_protocol"]["design_search_certificate"]
    assert payload["hardgate"]["gates"]["DG-NAS-HG8"]["status"] == "fail"


@pytest.mark.parametrize(
    ("slot_state", "expected_status"),
    [
        ("present", "pass"),
        ("present-but-fail-closed", "fail"),
        ("negative", "fail"),
    ],
)
def test_design_search_certificate_slot_state_drives_hg8(slot_state, expected_status):
    payload = runner.build_projection(
        generated_at="fixture-time",
        design_search_certificate_slot_state=slot_state,
    )["summary_payload"]

    assert payload["candidate_protocol"]["design_search_certificate"]["slot_state"] == slot_state
    assert payload["hardgate"]["gates"]["DG-NAS-HG8"]["status"] == expected_status
    assert payload["hardgate"]["gates"]["DG-NAS-HG8"]["slot_state"] == slot_state


def test_design_search_certificate_fails_closed_when_pointer_dangles():
    payload = runner.build_projection(
        generated_at="fixture-time",
        design_search_certificate_slot_state="present",
        design_search_certificate_owner_pointer="reports/canonical/discovery-gated-nas.json:$.missing_certificate",
    )["summary_payload"]

    gate = payload["hardgate"]["gates"]["DG-NAS-HG8"]
    assert gate["status"] == "fail"
    assert gate["slot_state"] == "present-but-fail-closed"
    assert payload["hardgate"]["failed_gate"] == "DG-NAS-HG8"
    assert payload["discovery_map_signal"]["failed_gate_pointer"] == "$.hardgate.gates.DG-NAS-HG8.status"


def test_design_search_certificate_hg7_normalizes_malformed_slot():
    payload = {"candidate_protocol": {"design_search_certificate": {"slot_state": "present"}}}
    gate = design_search_certificate_hg7(payload)

    assert gate["status"] == "fail"
    assert gate["slot_state"] == "present-but-fail-closed"


def test_recursive_forbidden_key_validator_rejects_nested_terminal_verdict(monkeypatch):
    monkeypatch.setattr(
        dgn,
        "_revocation_rows",
        lambda failed_gate: [{"nested": {"terminal_verdict": "forbidden"}, "failed_gate": failed_gate}],
    )

    with pytest.raises(ValueError, match="forbidden keys"):
        runner.build_projection(generated_at="fixture-time")

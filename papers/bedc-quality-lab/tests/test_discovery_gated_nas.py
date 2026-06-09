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
    audit_mechanism_namecert,
    design_search_certificate_hg7,
    mechanism_namecert_ref,
)
from bedc_quality_lab.backends.current_lab.projection import (
    _theorem_dna_pointer_cells_resolve,
    _theorem_ledger_rows_have_resolvable_dna,
    discovery_row,
    projection_payload,
)
from bedc_quality_lab.research_discovery import assign_discovery_level
from scripts import run_discovery_gated_nas as runner
from scripts import run_lejepa_theorem_ledger
from scripts.run_canonical_reports import CanonicalReportSpec


def _dg_nas_spec():
    return CanonicalReportSpec(
        name="discovery-gated-nas",
        command=("python3", "scripts/run_discovery_gated_nas.py"),
        json_artifact="reports/canonical/discovery-gated-nas.json",
        markdown_artifact="reports/canonical/discovery-gated-nas.md",
        required_json_keys=(),
        estimated_seconds=2,
        bundle_role="auxiliary",
        scope_pointer="$.search_space",
        cost_pointer="$.source_artifacts.cost_protocol",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.positive_claim",
        control_pointer="$.matched_baseline_control",
        no_control_rationale_pointer=None,
    )


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
    spec = _dg_nas_spec()
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
    mutation_map = payload["negative_witness_mutations"]["mutation_map"]

    assert payload["negative_witness_mutations"]["mutation_map"] == NEGATIVE_WITNESS_MUTATIONS
    assert {row["witness_kind"] for row in rows} == set(NEGATIVE_WITNESS_MUTATIONS)
    for row in rows:
        assert row["witness_ref"] == row["witness_kind"]
        assert row["mutation_candidate"] == mutation_map[row["witness_kind"]]
        assert row["mutation_pointer"] == f"$.search_objective_summary.by_candidate.{row['mutation_candidate']}"
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
    assert payload["discovery_map_signal"]["theorem_dna_required"] is True
    assert payload["discovery_map_signal"]["theorem_dna_family"] == "theorem_rows[N].theorem_dna"
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


def test_mechanism_namecert_nested_under_existing_owner_only():
    payload = _ready_payload()
    ref = mechanism_namecert_ref()

    assert ref == {"artifact": "reports/canonical/discovery-gated-nas.json", "pointer": "$.mechanism_namecert"}
    assert "mechanism_namecert" in payload
    assert payload["mechanism_namecert"]["schema_id"] == "bedc-quality-lab:discovery-gated-nas:mechanism-namecert"
    assert payload["mechanism_namecert"]["source_spec"]["owner_ref"] == ref
    assert payload["mechanism_namecert"]["audit"]["status"] == "pass"


def test_mnc_hg1_to_hg7_link_exact_source_owners():
    payload = _ready_payload()
    mnc = payload["mechanism_namecert"]

    assert [row["gate"] for row in mnc["hardgates"]] == list(DG_NAS_HARDGATES[:7])
    for gate, row in zip(DG_NAS_HARDGATES[:7], mnc["hardgates"]):
        assert row["status_ref"]["owner_pointer"] == f"reports/canonical/discovery-gated-nas.json:$.hardgate.gates.{gate}.status"
        assert row["evidence_ref"]["owner_pointer"] == f"reports/canonical/discovery-gated-nas.json:$.hardgate.gates.{gate}"


def test_mnc_missing_component_ablation_fails_closed():
    payload = _ready_payload()
    mnc = {
        **payload["mechanism_namecert"],
        "closure_status": {
            **payload["mechanism_namecert"]["closure_status"],
            "ablation_spec": "open",
        },
    }

    audit = audit_mechanism_namecert(mnc)

    assert audit["status"] == "fail"
    assert audit["closed"] is False


def test_mnc_closed_d5_m_requires_all_gates_and_shortcut_audit():
    payload = _ready_payload()
    mnc = payload["mechanism_namecert"]

    assert mnc["closure_status"]["mechanism_namecert"] == "closed"
    assert mnc["shortcut_witness_audit"]["witness_rows_ref"]["owner_pointer"] == "reports/canonical/discovery-gated-nas.json:$.negative_witness_mutations.rows"
    assert len(mnc["hardgates"]) == 7
    assert audit_mechanism_namecert(mnc)["status"] == "pass"


def test_mnc_no_source_fact_copy():
    payload = _ready_payload()
    serialized = json.dumps(payload["mechanism_namecert"], sort_keys=True)

    for token in ('"quality_q"', '"search_score"', '"candidate_id"', '"surface_id"', '"raw_rows"'):
        assert token not in serialized
    assert "owner_pointer" in serialized


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
    spec = _dg_nas_spec()
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
    spec = _dg_nas_spec()
    context = {
        "reports/canonical/quality-scorecard.json": {"rows": [{"status": "ready"}]},
        run_lejepa_theorem_ledger.JSON_ARTIFACT: run_lejepa_theorem_ledger.build_payload(generated_at="fixture-time"),
    }
    projected = projection_payload(spec, payload, context)
    verdict = assign_discovery_level(projected)
    row = discovery_row(spec, payload, context)

    assert verdict.discovery_level == "D5-O"
    assert row["discovery_level"] == "D5-O"
    assert row["audit_status"] == "valid"
    assert row["control_pointer"] == "$.matched_baseline_control"


def test_d5_m_projection_rejects_when_context_ledger_rows_lack_theorem_dna():
    payload = _ready_payload()
    spec = _dg_nas_spec()
    ledger = run_lejepa_theorem_ledger.build_payload(generated_at="fixture-time")
    ledger_without_dna = {
        **ledger,
        "theorem_rows": [
            {key: value for key, value in row.items() if key not in {"theorem_dna", "theorem_dna_pointer"}}
            for row in ledger["theorem_rows"]
        ],
    }
    context = {
        "reports/canonical/quality-scorecard.json": {"rows": [{"status": "ready"}]},
        run_lejepa_theorem_ledger.JSON_ARTIFACT: ledger_without_dna,
    }

    projected = projection_payload(spec, payload, context)
    row = discovery_row(spec, payload, context)

    assert projected["verdict"] == "rejected"
    assert row["discovery_level"] == "DN"
    assert row["terminal_verdict"] == "rejected"
    assert row["failed_gate"] == f"{run_lejepa_theorem_ledger.JSON_ARTIFACT}:$.theorem_rows"


def _assert_d5_m_projection_rejects_ledger(ledger):
    payload = _ready_payload()
    spec = _dg_nas_spec()
    context = {
        "reports/canonical/quality-scorecard.json": {"rows": [{"status": "ready"}]},
        run_lejepa_theorem_ledger.JSON_ARTIFACT: ledger,
    }

    projected = projection_payload(spec, payload, context)
    row = discovery_row(spec, payload, context)

    assert projected["verdict"] == "rejected"
    assert row["discovery_level"] == "DN"
    assert row["terminal_verdict"] == "rejected"
    assert row["failed_gate"] == f"{run_lejepa_theorem_ledger.JSON_ARTIFACT}:$.theorem_rows"


def _lejepa_theorem_ledger_context(ledger):
    return {
        "reports/canonical/quality-scorecard.json": {"rows": [{"status": "ready"}]},
        run_lejepa_theorem_ledger.JSON_ARTIFACT: ledger,
    }


def _partial_malformed_ledger(mutate_second_row):
    ledger = run_lejepa_theorem_ledger.build_payload(generated_at="fixture-time")
    rows = [dict(row) for row in ledger["theorem_rows"]]
    rows[1] = mutate_second_row(dict(rows[1]))
    return {**ledger, "theorem_rows": rows}


def test_theorem_ledger_resolvable_dna_gate_accepts_valid_context():
    ledger = run_lejepa_theorem_ledger.build_payload(generated_at="fixture-time")

    assert _theorem_ledger_rows_have_resolvable_dna(_lejepa_theorem_ledger_context(ledger)) is True
    assert _theorem_dna_pointer_cells_resolve(ledger, ledger["theorem_rows"][0]["theorem_dna"]["assumptions"]) is True


@pytest.mark.parametrize(
    "context",
    [
        {},
        {run_lejepa_theorem_ledger.JSON_ARTIFACT: "not-a-ledger-mapping"},
        {run_lejepa_theorem_ledger.JSON_ARTIFACT: {"theorem_rows": "not-a-row-list"}},
        {run_lejepa_theorem_ledger.JSON_ARTIFACT: {"theorem_rows": []}},
        {run_lejepa_theorem_ledger.JSON_ARTIFACT: {"theorem_rows": ["not-a-row-mapping"]}},
    ],
)
def test_theorem_ledger_resolvable_dna_gate_rejects_missing_or_malformed_ledger_shape(context):
    assert _theorem_ledger_rows_have_resolvable_dna(context) is False


@pytest.mark.parametrize(
    "mutate_first_row",
    [
        lambda row: {key: value for key, value in row.items() if key != "theorem_dna_pointer"},
        lambda row: {**row, "theorem_dna_pointer": 7},
        lambda row: {**row, "theorem_dna_pointer": "$.theorem_rows[0].not_theorem_dna"},
        lambda row: {**row, "theorem_dna": "not-a-dna-mapping"},
        lambda row: {
            **row,
            "theorem_dna": {key: value for key, value in row["theorem_dna"].items() if key != "formal_status"},
        },
        lambda row: {
            **row,
            "theorem_dna": {**row["theorem_dna"], "assumptions": []},
        },
        lambda row: {
            **row,
            "theorem_dna": {**row["theorem_dna"], "ledger_debts": "not-a-cell-list"},
        },
        lambda row: {
            **row,
            "theorem_dna": {**row["theorem_dna"], "proof_dependencies": [{"role": "missing-pointer"}]},
        },
        lambda row: {
            **row,
            "theorem_dna": {
                **row["theorem_dna"],
                "assumptions": [{"pointer": "$.theorem_rows[0].missing_target", "role": "dangling"}],
            },
        },
    ],
)
def test_theorem_ledger_resolvable_dna_gate_rejects_each_fail_closed_branch(mutate_first_row):
    ledger = run_lejepa_theorem_ledger.build_payload(generated_at="fixture-time")
    rows = [dict(row) for row in ledger["theorem_rows"]]
    rows[0] = mutate_first_row(dict(rows[0]))
    mutated = {**ledger, "theorem_rows": rows}

    assert _theorem_ledger_rows_have_resolvable_dna(_lejepa_theorem_ledger_context(mutated)) is False
    _assert_d5_m_projection_rejects_ledger(mutated)


def test_theorem_dna_required_non_pointer_fields_are_presence_checked_without_pointer_resolution():
    ledger = run_lejepa_theorem_ledger.build_payload(generated_at="fixture-time")
    rows = [dict(row) for row in ledger["theorem_rows"]]
    rows[0] = {
        **rows[0],
        "theorem_dna": {
            **rows[0]["theorem_dna"],
            "objects": ["plain-object-name"],
            "maps": ["plain-map-name"],
            "operators": ["plain-operator-name"],
            "invariants": ["plain-invariant-name"],
        },
    }
    mutated = {**ledger, "theorem_rows": rows}

    assert _theorem_ledger_rows_have_resolvable_dna(_lejepa_theorem_ledger_context(mutated)) is True


@pytest.mark.parametrize(
    "mutate_second_row",
    [
        lambda row: {key: value for key, value in row.items() if key != "theorem_dna"},
        lambda row: {**row, "theorem_dna_pointer": "$.theorem_rows[0].theorem_dna"},
        lambda row: {
            **row,
            "theorem_dna": {**row["theorem_dna"], "theorem_id": "wrong-theorem-id"},
        },
        lambda row: {
            **row,
            "theorem_dna": {**row["theorem_dna"], "assumptions": ["not-a-pointer-cell"]},
        },
        lambda row: {
            **row,
            "theorem_dna": {**row["theorem_dna"], "proof_dependencies": [{"role": "missing-pointer"}]},
        },
        lambda row: {
            **row,
            "theorem_dna": {
                **row["theorem_dna"],
                "assumptions": [
                    {"pointer": "$.theorem_rows[1].does_not_exist", "role": "row-evidence"}
                ],
            },
        },
    ],
)
def test_d5_m_projection_rejects_partial_or_malformed_theorem_dna(mutate_second_row):
    ledger = _partial_malformed_ledger(mutate_second_row)

    assert "theorem_dna" in ledger["theorem_rows"][0]
    _assert_d5_m_projection_rejects_ledger(ledger)


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


def test_hg6_fails_when_negative_witness_row_lacks_direct_witness_ref():
    payload = _ready_payload()
    projection = DiscoveryGatedNasProjection(
        config=payload["config"],
        records=[],
        generated_at="fixture-time",
        run_artifacts=payload["run_artifacts"],
    )
    rows = payload["negative_witness_mutations"]["rows"]
    missing_ref = {
        **payload,
        "negative_witness_mutations": {
            **payload["negative_witness_mutations"],
            "rows": [{key: value for key, value in rows[0].items() if key != "witness_ref"}, *rows[1:]],
        },
    }
    wrong_ref = {
        **payload,
        "negative_witness_mutations": {
            **payload["negative_witness_mutations"],
            "rows": [{**rows[0], "witness_ref": rows[1]["witness_kind"]}, *rows[1:]],
        },
    }

    assert projection.hardgate_verdicts(missing_ref)["DG-NAS-HG6"]["status"] == "fail"
    assert projection.hardgate_verdicts(wrong_ref)["DG-NAS-HG6"]["status"] == "fail"


def _assert_hg6_rejects_negative_witness_mutation(payload):
    recomputed = _with_recomputed_signal(payload)

    assert recomputed["hardgate"]["gates"]["DG-NAS-HG6"]["status"] == "fail"
    _assert_dn_projection(recomputed, "DG-NAS-HG6")


def _with_negative_witness_mutations(payload, **overrides):
    return {
        **payload,
        "negative_witness_mutations": {
            **payload["negative_witness_mutations"],
            **overrides,
        },
    }


def test_hg6_fails_when_negative_witness_row_has_wrong_mutation_candidate():
    payload = _ready_payload()
    rows = payload["negative_witness_mutations"]["rows"]
    row = rows[0]
    wrong_candidate = next(candidate for candidate in DEFAULT_CANDIDATES if candidate != row["mutation_candidate"])
    mutated = _with_negative_witness_mutations(
        payload,
        rows=[{**row, "mutation_candidate": wrong_candidate}, *rows[1:]],
    )

    _assert_hg6_rejects_negative_witness_mutation(mutated)


def test_hg6_fails_when_negative_witness_row_has_wrong_mutation_pointer():
    payload = _ready_payload()
    rows = payload["negative_witness_mutations"]["rows"]
    mutated = _with_negative_witness_mutations(
        payload,
        rows=[{**rows[0], "mutation_pointer": "$.search_objective_summary.by_candidate.not_canonical"}, *rows[1:]],
    )

    _assert_hg6_rejects_negative_witness_mutation(mutated)


def test_hg6_fails_when_negative_witness_row_is_missing():
    payload = _ready_payload()
    rows = payload["negative_witness_mutations"]["rows"]
    mutated = _with_negative_witness_mutations(payload, rows=rows[1:])

    _assert_hg6_rejects_negative_witness_mutation(mutated)


def test_hg6_fails_when_negative_witness_row_is_extra():
    payload = _ready_payload()
    rows = payload["negative_witness_mutations"]["rows"]
    extra = {
        **rows[0],
        "witness_kind": "not_canonical",
        "witness_ref": "not_canonical",
    }
    mutated = _with_negative_witness_mutations(payload, rows=[*rows, extra])

    _assert_hg6_rejects_negative_witness_mutation(mutated)


def test_hg6_fails_when_negative_witness_mutation_map_is_not_canonical():
    payload = _ready_payload()
    witness_kind = next(iter(NEGATIVE_WITNESS_MUTATIONS))
    wrong_candidate = next(
        candidate for candidate in DEFAULT_CANDIDATES if candidate != NEGATIVE_WITNESS_MUTATIONS[witness_kind]
    )
    mutated = _with_negative_witness_mutations(
        payload,
        mutation_map={
            **payload["negative_witness_mutations"]["mutation_map"],
            witness_kind: wrong_candidate,
        },
    )

    _assert_hg6_rejects_negative_witness_mutation(mutated)


def test_matched_baseline_control_positive_fails_hg6_without_d5_m_candidate():
    payload = _ready_payload()
    mutated = {
        **payload,
        "matched_baseline_control": {
            **payload["matched_baseline_control"],
            "control_positive": True,
        },
    }
    recomputed = _with_recomputed_signal(mutated)

    assert recomputed["hardgate"]["gates"]["DG-NAS-HG6"]["status"] == "fail"
    assert recomputed["hardgate"]["gates"]["DG-NAS-HG6"]["evidence_pointer"].startswith("$.matched_baseline_control")
    assert recomputed["hardgate"]["failed_gate"] == "DG-NAS-HG6"
    assert recomputed["discovery_map_signal"]["level_candidate"] == "DN"
    assert recomputed["discovery_map_signal"]["failed_gate"] == "DG-NAS-HG6"
    assert recomputed["discovery_map_signal"]["failed_gate_pointer"] == "$.hardgate.gates.DG-NAS-HG6.status"
    _assert_dn_projection(recomputed, "DG-NAS-HG6")


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
    spec = _dg_nas_spec()
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

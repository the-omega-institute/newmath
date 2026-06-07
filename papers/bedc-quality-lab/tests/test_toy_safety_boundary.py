from __future__ import annotations

import copy
import json
from pathlib import Path

from bedc_quality_lab.discovery_compiler.capsule import ClaimCapsule
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from bedc_quality_lab.toy_safety_boundary import (
    CANONICAL_SIDECAR_ARTIFACT,
    CLAIM_CAPSULE_ARTIFACT,
    CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID,
    CLAIM_CAPSULE_SCHEMA_ID,
    PUBLIC_SIDECAR_ARTIFACT,
    RAW_METRICS_ARTIFACT,
    REPORT_ARTIFACT,
    REQUIRED_GATES,
    SUMMARY_ARTIFACT,
    evaluate_fail_closed,
)
from scripts.run_toy_safety_boundary import main as run_toy_safety_boundary


ROOT = Path(__file__).resolve().parents[1]


def _load_json(artifact: str):
    return json.loads((ROOT / artifact).read_text(encoding="utf-8"))


def _ref_to_cell(ref: dict[str, str]) -> str:
    return f"{ref['artifact']}:{ref['pointer']}"


def _recursive_strings(value):
    if isinstance(value, dict):
        for item in value.values():
            yield from _recursive_strings(item)
    elif isinstance(value, list):
        for item in value:
            yield from _recursive_strings(item)
    elif isinstance(value, str):
        yield value


def test_toy_safety_boundary_generation_is_byte_deterministic():
    artifacts = [
        CLAIM_CAPSULE_ARTIFACT,
        RAW_METRICS_ARTIFACT,
        SUMMARY_ARTIFACT,
        REPORT_ARTIFACT,
        PUBLIC_SIDECAR_ARTIFACT,
        CANONICAL_SIDECAR_ARTIFACT,
        "reports/canonical/toy_safety_boundary.md",
    ]

    run_toy_safety_boundary([])
    first = {artifact: (ROOT / artifact).read_bytes() for artifact in artifacts}
    run_toy_safety_boundary([])
    second = {artifact: (ROOT / artifact).read_bytes() for artifact in artifacts}

    assert second == first


def test_claim_capsule_loader_and_versionless_schema_cells():
    payload = _load_json(CLAIM_CAPSULE_ARTIFACT)
    capsule = ClaimCapsule.from_payload(payload)

    assert capsule.claim_id == payload["claim_id"]
    assert payload["schema_id"] == CLAIM_CAPSULE_SCHEMA_ID
    assert payload["run_local_schema_id"] == CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID
    assert not any(".v1" in value for value in _recursive_strings(payload))
    assert "schema_version" not in payload
    assert "u_hardgates" not in payload
    assert "h1_hardgates" not in payload
    assert "u_hardgates" not in payload["run_local"]
    assert "h1_hardgates" not in payload["run_local"]


def test_hardgates_are_exact_top_level_owner_rows_and_evidence_resolves():
    payload = _load_json(CLAIM_CAPSULE_ARTIFACT)

    assert set(payload["hardgates"]) == set(REQUIRED_GATES)
    for gate, row in payload["hardgates"].items():
        assert row["status"] in {"pass", "fail"}
        assert resolve_artifact_pointer(ROOT, row["evidence_pointer"]) is not None, gate
        if "failed_gate_pointer" in row:
            assert resolve_artifact_pointer(ROOT, row["failed_gate_pointer"]) is not None

    assert payload["hardgates"]["H1-HG1"]["evidence_pointer"] == (
        f"{CLAIM_CAPSULE_ARTIFACT}:$.result_snapshot.safety_boundary_metrics"
    )
    assert payload["hardgates"]["H1-HG2"]["evidence_pointer"] == (
        f"{CLAIM_CAPSULE_ARTIFACT}:$.result_snapshot.ambiguous_case_ledger"
    )
    assert payload["hardgates"]["H1-HG3"]["evidence_pointer"] == (
        f"{CLAIM_CAPSULE_ARTIFACT}:$.result_snapshot.synthetic_data_audit"
    )


def test_pointer_surfaces_are_pointer_only_and_resolve_to_capsule():
    summary = _load_json(SUMMARY_ARTIFACT)
    public = _load_json(PUBLIC_SIDECAR_ARTIFACT)
    canonical = _load_json(CANONICAL_SIDECAR_ARTIFACT)

    assert resolve_artifact_pointer(ROOT, _ref_to_cell(summary["claim_capsule_ref"])) is not None
    for gate, ref in summary["hardgate_refs"].items():
        assert ref == {"artifact": CLAIM_CAPSULE_ARTIFACT, "pointer": f"$.hardgates.{gate}"}
        assert resolve_artifact_pointer(ROOT, _ref_to_cell(ref)) is not None
    for sidecar in (public, canonical):
        assert resolve_artifact_pointer(ROOT, _ref_to_cell(sidecar["claim_capsule_ref"])) is not None
        assert resolve_artifact_pointer(ROOT, _ref_to_cell(sidecar["positive_claim_ref"])) is not None
        assert resolve_artifact_pointer(ROOT, _ref_to_cell(sidecar["present_but_fail_closed"])) is not None
        for rows in (sidecar["u_hardgate_refs"], sidecar["h1_hardgate_refs"]):
            for ref in rows.values():
                assert resolve_artifact_pointer(ROOT, _ref_to_cell(ref)) is not None

    forbidden_embeds = {"hardgates", "positive_claim", "not_claimed", "what_was_learned", "result_snapshot"}
    assert forbidden_embeds.isdisjoint(summary)
    assert forbidden_embeds.isdisjoint(public)
    assert forbidden_embeds.isdisjoint(canonical)


def test_positive_claim_fail_closed_conditions():
    payload = _load_json(CLAIM_CAPSULE_ARTIFACT)
    assert evaluate_fail_closed(payload)["status"] == "pass"

    missing_delta = copy.deepcopy(payload)
    missing_delta["result_snapshot"].pop("classifier_surface_delta")
    assert evaluate_fail_closed(missing_delta)["status"] == "fail"

    missing_signal = copy.deepcopy(payload)
    missing_signal["result_snapshot"]["net_positive_signal"] = False
    assert evaluate_fail_closed(missing_signal)["status"] == "fail"

    forbidden_term = copy.deepcopy(payload)
    forbidden_term["forbidden_claim_term_audit"] = {"status": "fail", "hits": ["full-lejepa"]}
    assert evaluate_fail_closed(forbidden_term)["status"] == "fail"

    missing_control = copy.deepcopy(payload)
    missing_control["result_snapshot"].pop("matched_random_control")
    assert evaluate_fail_closed(missing_control)["status"] == "fail"


def test_dn_and_dr_fail_closed_require_owner_cells():
    payload = _load_json(CLAIM_CAPSULE_ARTIFACT)

    dn = copy.deepcopy(payload)
    dn["claim_status"] = "DN"
    dn["failed_gate"] = ""
    assert evaluate_fail_closed(dn)["status"] == "fail"
    dn["failed_gate"] = "U-HG8"
    dn["what_was_learned"] = ""
    assert evaluate_fail_closed(dn)["status"] == "fail"

    dr = copy.deepcopy(payload)
    dr["revocation"]["terminal_row"] = "DR"
    dr["revocation"]["rows"] = []
    assert evaluate_fail_closed(dr)["status"] == "fail"

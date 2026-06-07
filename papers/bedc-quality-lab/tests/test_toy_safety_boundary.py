from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest

import bedc_quality_lab.toy_safety_boundary as toy_safety_boundary
from bedc_quality_lab.discovery_compiler.capsule import ClaimCapsule
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from bedc_quality_lab.toy_safety_boundary import (
    CANONICAL_SIDECAR_ARTIFACT,
    CANONICAL_MARKDOWN_ARTIFACT,
    CLAIM_CAPSULE_ARTIFACT,
    CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID,
    CLAIM_CAPSULE_SCHEMA_ID,
    PUBLIC_SIDECAR_ARTIFACT,
    RAW_METRICS_ARTIFACT,
    REPORT_ARTIFACT,
    REQUIRED_GATES,
    SUMMARY_ARTIFACT,
    evaluate_fail_closed,
    validate_artifacts,
    write_artifacts,
)
from scripts import run_canonical_reports as canonical
from scripts.run_toy_safety_boundary import main as run_toy_safety_boundary


ROOT = Path(__file__).resolve().parents[1]


def _load_json(artifact: str):
    return json.loads((ROOT / artifact).read_text(encoding="utf-8"))


def _write_claim_capsule(root: Path, payload: dict) -> None:
    path = root / CLAIM_CAPSULE_ARTIFACT
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


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


def test_canonical_index_exposes_toy_safety_boundary_pointer_only_section():
    index = canonical._index([], generated_at="2030-01-01T00:00:00+00:00")
    section = index["toy_safety_boundary"]
    markdown = canonical._render_index_markdown(index)

    assert set(section) == {
        "status",
        "artifact_id",
        "json_artifact",
        "markdown_artifact",
        "claim_capsule_pointer",
        "hardgates_pointer",
        "positive_claim_pointer",
        "canonical_role",
    }
    assert section["status"] == "pointer-only"
    assert section["json_artifact"] == CANONICAL_SIDECAR_ARTIFACT
    assert section["markdown_artifact"] == CANONICAL_MARKDOWN_ARTIFACT
    assert section["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"

    for pointer in (
        section["claim_capsule_pointer"],
        section["hardgates_pointer"],
        section["positive_claim_pointer"],
    ):
        assert pointer.startswith(f"{CLAIM_CAPSULE_ARTIFACT}:")
        assert resolve_artifact_pointer(ROOT, pointer) is not None

    toy_markdown_section = markdown.split("## Toy safety boundary", maxsplit=1)[1].split(
        "## Paper outline", maxsplit=1
    )[0]
    assert f"- Claim capsule: `{section['claim_capsule_pointer']}`" in toy_markdown_section
    assert f"- Hardgates: `{section['hardgates_pointer']}`" in toy_markdown_section
    assert f"- JSON: `{CANONICAL_SIDECAR_ARTIFACT}`" in toy_markdown_section
    assert f"- Markdown: `{CANONICAL_MARKDOWN_ARTIFACT}`" in toy_markdown_section
    for inline_body_key in ("not_claimed", "what_was_learned", "result_snapshot"):
        assert inline_body_key not in set(section)
        assert inline_body_key not in toy_markdown_section


def test_toy_safety_boundary_sidecar_stays_out_of_canonical_reports():
    names = {spec.name for spec in canonical.CANONICAL_REPORTS}
    json_artifacts = {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}
    markdown_artifacts = {spec.markdown_artifact for spec in canonical.CANONICAL_REPORTS}

    assert "toy_safety_boundary" not in names
    assert CANONICAL_SIDECAR_ARTIFACT not in json_artifacts
    assert CANONICAL_MARKDOWN_ARTIFACT not in markdown_artifacts


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


def test_validate_artifacts_rejects_invalid_hardgate_status(tmp_path):
    artifacts = write_artifacts(tmp_path)
    payload = copy.deepcopy(artifacts.claim_capsule)
    payload["hardgates"]["H1-HG1"]["status"] = "warning"
    _write_claim_capsule(tmp_path, payload)

    validation = validate_artifacts(tmp_path)

    assert validation["status"] == "fail"
    assert "H1-HG1: invalid status" in validation["errors"]


def test_validate_artifacts_rejects_unresolved_evidence_pointer(tmp_path):
    artifacts = write_artifacts(tmp_path)
    payload = copy.deepcopy(artifacts.claim_capsule)
    payload["hardgates"]["H1-HG1"]["evidence_pointer"] = f"{CLAIM_CAPSULE_ARTIFACT}:$.missing"
    _write_claim_capsule(tmp_path, payload)

    validation = validate_artifacts(tmp_path)

    assert validation["status"] == "fail"
    assert "H1-HG1: evidence pointer does not resolve" in validation["errors"]


def test_validate_artifacts_rejects_unresolved_failed_gate_pointer(tmp_path):
    artifacts = write_artifacts(tmp_path)
    payload = copy.deepcopy(artifacts.claim_capsule)
    payload["hardgates"]["U-HG5"]["failed_gate_pointer"] = f"{CLAIM_CAPSULE_ARTIFACT}:$.missing"
    _write_claim_capsule(tmp_path, payload)

    validation = validate_artifacts(tmp_path)

    assert validation["status"] == "fail"
    assert "U-HG5: failed gate pointer does not resolve" in validation["errors"]


def test_validate_artifacts_propagates_evaluate_fail_closed_errors(tmp_path):
    artifacts = write_artifacts(tmp_path)
    payload = copy.deepcopy(artifacts.claim_capsule)
    payload["result_snapshot"]["net_positive_signal"] = False
    _write_claim_capsule(tmp_path, payload)

    validation = validate_artifacts(tmp_path)

    assert validation["status"] == "fail"
    assert "positive claim gate does not pass" in validation["errors"]


def test_validate_artifacts_propagates_evaluate_fail_closed_exception(tmp_path, monkeypatch):
    write_artifacts(tmp_path)

    def raise_evaluation_error(payload):
        raise RuntimeError("fail-closed evaluator unavailable")

    monkeypatch.setattr(toy_safety_boundary, "evaluate_fail_closed", raise_evaluation_error)

    with pytest.raises(RuntimeError, match="fail-closed evaluator unavailable"):
        validate_artifacts(tmp_path)

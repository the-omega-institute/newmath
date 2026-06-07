import json

import pytest

from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from bedc_quality_lab.discovery_gated_transformer import (
    ARTIFACT_ID,
    CANONICAL_JSON_ARTIFACT,
    GATE_NAMES,
    MODEL_ID,
    SCHEMA_ID,
    build_projection,
    default_component_refs,
    validate_projection,
)
from scripts import run_discovery_gated_transformer as dgt


def _walk(value):
    if isinstance(value, dict):
        yield value
        for item in value.values():
            yield from _walk(item)
    elif isinstance(value, list):
        for item in value:
            yield from _walk(item)


def test_dgt_has_twenty_gate_names():
    payload = dgt.build_payload(generated_at="fixture-time")

    assert GATE_NAMES == tuple(f"DGT-HG{index}" for index in range(1, 21))
    assert payload["hardgate"]["gate_names"] == [f"DGT-HG{index}" for index in range(1, 21)]
    assert list(payload["hardgate"]["gates"]) == [f"DGT-HG{index}" for index in range(1, 21)]


def test_dgt_missing_pointer_fails_closed():
    refs = default_component_refs()
    refs.pop("discovery_map")

    payload = build_projection(generated_at="fixture-time", component_refs=refs)

    assert payload["hardgate"]["status"] == "fail"
    assert {row["status"] for row in payload["hardgate"]["gates"].values()} == {"fail"}


def test_dgt_complete_fixture_is_d4_candidate():
    payload = dgt.build_payload(generated_at="fixture-time")

    assert payload["schema_id"] == SCHEMA_ID
    assert payload["artifact_id"] == ARTIFACT_ID
    assert payload["model_id"] == MODEL_ID
    assert payload["hardgate"]["status"] == "pass"
    assert payload["discovery_map_signal"]["level_candidate"] == "D4"
    assert payload["discovery_map_signal"]["status"] == "candidate-local-positive"


def test_dgt_component_evidence_is_pointer_only():
    payload = dgt.build_payload(generated_at="fixture-time")

    for cell in payload["component_refs"].values():
        assert set(cell) == {"artifact", "pointer"}
        assert cell["pointer"].startswith("$")
    serialized = json.dumps(payload, sort_keys=True)
    for forbidden in (
        '"records"',
        '"quality_q"',
        '"attention_rows"',
        '"search_score"',
        '"terminal_verdict"',
        '"standalone_verdict"',
        '"private_row_carrier"',
    ):
        assert forbidden not in serialized


def test_dgt_artifact_ids_are_unversioned():
    payload = dgt.build_payload(generated_at="fixture-time")
    serialized = json.dumps(payload, sort_keys=True)

    assert payload["schema_id"] == "bedc-quality-lab:discovery-gated-transformer"
    assert payload["artifact_id"] == "bedc-quality-lab:discovery-gated-transformer"
    assert payload["model_id"] == "discovery-gated-transformer"
    assert "v0" not in serialized.lower()
    assert "v1" not in serialized.lower()


def test_dgt_explicitly_denies_global_superiority_and_production_authority():
    payload = dgt.build_payload(generated_at="fixture-time")
    nonclaims = " ".join(payload["not_claimed"]).lower()

    assert "global superiority" in nonclaims
    assert "production authority" in nonclaims


def test_dgt_rejects_inline_source_metric_bodies():
    payload = dgt.build_payload(generated_at="fixture-time")
    mutated = json.loads(json.dumps(payload))
    mutated["component_refs"]["metric_body"] = {"artifact": "x", "pointer": "$", "records": []}

    with pytest.raises(ValueError, match="inline source body"):
        validate_projection(mutated)


def test_dgt_written_sidecars_resolve(tmp_path):
    payload = dgt.build_payload(generated_at="fixture-time")
    dgt.write_artifacts(payload, root=tmp_path)

    assert resolve_artifact_pointer(tmp_path, f"{CANONICAL_JSON_ARTIFACT}:$") is not None
    for key in (
        "claim_capsule_ref",
        "evidence_envelope_ref",
        "mechanism_namecert_ref",
        "jet_certificate_ref",
    ):
        cell = payload[key]
        sidecar = resolve_artifact_pointer(tmp_path, f"{cell['artifact']}:{cell['pointer']}")
        assert sidecar is not None
        assert sidecar["model_id"] == "discovery-gated-transformer"


def test_dgt_canonical_payload_does_not_inline_sidecars():
    payload = dgt.build_payload(generated_at="fixture-time")
    sidecars = dgt.build_run_sidecars(generated_at="fixture-time")
    serialized = json.dumps(payload, sort_keys=True)

    for sidecar in sidecars.values():
        assert json.dumps(sidecar, sort_keys=True) not in serialized

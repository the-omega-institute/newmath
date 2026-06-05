import json
from pathlib import Path

import pytest

from bedc_quality_lab.backends.model_discovery import (
    CLAIM_CAPSULE_ARTIFACT,
    DRT_CANONICAL_ARTIFACT,
    MSN_CANONICAL_ARTIFACT,
    NM_HARDGATE_IDS,
    RUN_ARTIFACT,
    TASK_IDS,
    ModelDiscoveryBackendEvidenceAdapter,
    build_model_discovery_payload,
)
from bedc_quality_lab.discovery_compiler.capsule import (
    ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE,
    CLAIM_CAPSULE_SCHEMA_ID,
    build_architecture_claim_capsule_payload,
    require_architecture_claim_capsule,
)
from bedc_quality_lab.discovery_compiler.pointers import pointer_value
from scripts import run_model_discovery_suite as runner


def _model_claim() -> dict:
    return {
        "model_id": "toy-discovery-gated-transformer",
        "claim": "fixture model architecture claim",
        "baselines": ["$.baselines.parameter_matched"],
        "forbidden_evidence": ["test_label"],
        "required_gates": ["NM-HG1", "NM-HG14"],
        "candidate_pointer": "$.model_candidates.0",
        "evidence_pointer": "$.task_grid",
    }


def test_architecture_claim_capsule_uses_quality_schema_and_capsule_subtype():
    payload = build_architecture_claim_capsule_payload(
        generated_at="fixture-time",
        claim_id="claim:model",
        report="model-discovery-suite",
        source_artifact=RUN_ARTIFACT,
        source_pointer="$.claim_capsule_ref",
        model_claim=_model_claim(),
    )

    capsule = require_architecture_claim_capsule(payload)

    assert capsule.payload["schema_id"] == CLAIM_CAPSULE_SCHEMA_ID
    assert capsule.payload["capsule_subtype"] == ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE
    assert "capsule_role" not in capsule.payload


@pytest.mark.parametrize(
    ("mutation", "match"),
    [
        ({"capsule_subtype": None}, "capsule_subtype"),
        ({"capsule_subtype": "bedc.model.architecture_claim_capsulee"}, "capsule_subtype"),
        ({"schema_id": "bedc.model.architecture_claim_capsule"}, "schema_id"),
        ({"capsule_subtype": None, "capsule_role": ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE}, "capsule_subtype"),
        ({"architecture_claim_capsule_schema_id": ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE}, "architecture_claim_capsule_schema_id"),
    ],
)
def test_architecture_claim_capsule_rejects_marker_mistakes(mutation, match):
    payload = build_architecture_claim_capsule_payload(
        generated_at="fixture-time",
        claim_id="claim:model",
        report="model-discovery-suite",
        source_artifact=RUN_ARTIFACT,
        source_pointer="$.claim_capsule_ref",
        model_claim=_model_claim(),
    )
    payload.update(mutation)

    with pytest.raises(ValueError, match=match):
        require_architecture_claim_capsule(payload)


def test_architecture_claim_capsule_rejects_missing_model_claim_cells():
    payload = build_architecture_claim_capsule_payload(
        generated_at="fixture-time",
        claim_id="claim:model",
        report="model-discovery-suite",
        source_artifact=RUN_ARTIFACT,
        source_pointer="$.claim_capsule_ref",
        model_claim=_model_claim(),
    )
    payload["model_claim"] = {"model_id": "toy-discovery-gated-transformer"}

    with pytest.raises(ValueError, match="model_claim cells"):
        require_architecture_claim_capsule(payload)


def test_model_discovery_backend_is_deterministic_toy_and_terminal_verdict_free(tmp_path):
    adapter = ModelDiscoveryBackendEvidenceAdapter()
    first = adapter.compute_metrics(root=tmp_path, generated_at="fixture-time")
    second = adapter.compute_metrics(root=tmp_path, generated_at="fixture-time")

    assert json.dumps(first, sort_keys=True) == json.dumps(second, sort_keys=True)
    assert tuple(row["task_id"] for row in first["task_grid"]) == TASK_IDS
    assert len(first["task_grid"]) == 8
    assert tuple(row["gate_id"] for row in first["nm_hardgates"]) == NM_HARDGATE_IDS
    assert "terminal_verdict" not in json.dumps(first, sort_keys=True)
    assert "terminal_verdict" not in adapter.backend.metrics


def test_model_discovery_tasks_carry_control_baseline():
    payload = build_model_discovery_payload(generated_at="fixture-time")

    assert {row["control_baseline"] for row in payload["task_grid"]} == {"parameter-matched-linear-reader"}


def test_model_discovery_consumes_drt_by_pointer_only():
    adapter = ModelDiscoveryBackendEvidenceAdapter()
    source_spec = adapter.build_source_spec()
    payload = build_model_discovery_payload(generated_at="fixture-time")

    assert source_spec["discovery_regularized_training"]["artifact"] == DRT_CANONICAL_ARTIFACT
    refs = payload["discovery_regularized_training_refs"]
    assert refs["discovery_map_signal"] == {"artifact": DRT_CANONICAL_ARTIFACT, "pointer": "$.discovery_map_signal"}
    assert refs["surface_registry"] == {"artifact": DRT_CANONICAL_ARTIFACT, "pointer": "$.surface_registry"}
    assert refs["torch_training_evidence"] == {"artifact": DRT_CANONICAL_ARTIFACT, "pointer": "$.torch_training_evidence"}
    assert "quality_q" not in refs
    assert "terminal_verdict" not in json.dumps(refs, sort_keys=True)


def test_model_discovery_consumes_msn_by_pointer_only():
    adapter = ModelDiscoveryBackendEvidenceAdapter()
    source_spec = adapter.build_source_spec()
    payload = build_model_discovery_payload(generated_at="fixture-time")

    assert source_spec["mechanism_seeking_network"]["artifact"] == MSN_CANONICAL_ARTIFACT
    refs = payload["mechanism_seeking_network_refs"]
    assert refs["discovery_map_signal"] == {"artifact": MSN_CANONICAL_ARTIFACT, "pointer": "$.discovery_map_signal"}
    assert refs["surface_registry"] == {"artifact": MSN_CANONICAL_ARTIFACT, "pointer": "$.surface_registry"}
    assert refs["mechanism_gate_summary"] == {"artifact": MSN_CANONICAL_ARTIFACT, "pointer": "$.mechanism_gate_summary"}
    assert refs["gate_protocol"] == {"artifact": MSN_CANONICAL_ARTIFACT, "pointer": "$.gate_protocol"}
    assert "mechanism_score" not in refs
    assert "terminal_verdict" not in json.dumps(refs, sort_keys=True)


def test_model_discovery_nm_hardgate_pointers_resolve():
    payload = build_model_discovery_payload(generated_at="fixture-time")

    for row in payload["nm_hardgates"]:
        assert pointer_value(payload, row["evidence_pointer"]) is not None, row["gate_id"]


def test_model_discovery_run_local_subtype_parity(tmp_path):
    paths = runner.write_run(root=tmp_path, generated_at="fixture-time")
    summary = json.loads(Path(paths["summary"]).read_text(encoding="utf-8"))
    capsule = json.loads(Path(paths["claim_capsule"]).read_text(encoding="utf-8"))

    assert paths["summary"] == tmp_path / RUN_ARTIFACT
    assert paths["claim_capsule"] == tmp_path / CLAIM_CAPSULE_ARTIFACT
    assert capsule["schema_id"] == CLAIM_CAPSULE_SCHEMA_ID
    assert capsule["capsule_subtype"] == ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE
    assert summary["claim_capsule_ref"]["capsule_subtype"] == capsule["capsule_subtype"]
    assert {row["capsule_subtype"] for row in summary["ledger_rows"]} == {capsule["capsule_subtype"]}
    assert {row["claim_capsule_pointer"] for row in summary["ledger_rows"]} == {"$.claim_capsule_ref.artifact"}
    assert pointer_value(summary, "$.claim_capsule_ref.artifact") == CLAIM_CAPSULE_ARTIFACT
    assert require_architecture_claim_capsule(capsule).payload["claim_id"] == "claim:model-discovery-suite"


def test_model_discovery_capsule_evidence_pointers_resolve(tmp_path):
    paths = runner.write_run(root=tmp_path, generated_at="fixture-time")
    artifacts = {
        RUN_ARTIFACT: json.loads(Path(paths["summary"]).read_text(encoding="utf-8")),
        CLAIM_CAPSULE_ARTIFACT: json.loads(Path(paths["claim_capsule"]).read_text(encoding="utf-8")),
    }
    capsule = artifacts[CLAIM_CAPSULE_ARTIFACT]
    summary = artifacts[RUN_ARTIFACT]

    assert pointer_value(artifacts[capsule["source"]], capsule["source_pointer"]) is not None

    baseline_pointers = capsule["model_claim"]["baselines"]
    assert len(baseline_pointers) == 3
    assert {cell["pointer"] for cell in baseline_pointers} == {
        "$.baselines.parameter_matched",
        "$.baselines.compute_matched",
        "$.baselines.matched_random_structural_control",
    }
    for cell in baseline_pointers:
        assert pointer_value(artifacts[cell["artifact"]], cell["pointer"]) is not None

    for key in ("candidate_pointer", "evidence_pointer"):
        cell = capsule["model_claim"][key]
        assert pointer_value(artifacts[cell["artifact"]], cell["pointer"]) is not None

    source_evidence = capsule["source_evidence"]
    assert pointer_value(artifacts[source_evidence["artifact"]], source_evidence["pointer"]) is not None

    forbidden_pointer = summary["claim_capsule_ref"]["forbidden_evidence_pointer"]
    assert pointer_value(capsule, forbidden_pointer) == ["test_label", "ood_label", "ledger_verdict"]

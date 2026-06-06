import json
from pathlib import Path

import pytest

from bedc_quality_lab.backends.model_discovery import (
    CGA_CANONICAL_ARTIFACT,
    CLAIM_CAPSULE_ARTIFACT,
    DG_NAS_CANONICAL_ARTIFACT,
    DRT_CANONICAL_ARTIFACT,
    MSN_CANONICAL_ARTIFACT,
    RUN_ARTIFACT,
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
        "model_id": "discovery-gated-nas-canonical-projection",
        "claim": "fixture model architecture claim",
        "baselines": [{"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$.matched_baseline_control"}],
        "forbidden_evidence": ["test_label"],
        "required_gates": ["DG-NAS-HG1", "DG-NAS-HG6", "DG-NAS-HG7"],
        "candidate_pointer": {"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$.candidate_protocol"},
        "evidence_pointer": {"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$.discovery_map_signal"},
    }


def _write_dg_nas_canonical(tmp_path: Path, *, level: str, failed_gate_pointer: str | None = None) -> dict:
    from scripts import run_discovery_gated_nas as dg_nas_runner

    projection = dg_nas_runner.build_projection(generated_at="fixture-time")
    dg_nas_runner.write_artifacts(projection, root=tmp_path)
    path = tmp_path / DG_NAS_CANONICAL_ARTIFACT
    canonical = json.loads(path.read_text(encoding="utf-8"))
    signal = canonical["discovery_map_signal"]
    signal["level_candidate"] = level
    signal["status"] = "negative" if level == "DN" else "d5-m-candidate"
    signal["failed_gate"] = "DG-NAS-HG4" if level == "DN" else None
    signal["failed_gate_pointer"] = failed_gate_pointer if level == "DN" else None
    canonical["hardgate"]["failed_gate"] = signal["failed_gate"]
    canonical["hardgate"]["status"] = "fail" if level == "DN" else "pass"
    if level == "DN":
        canonical["hardgate"]["gates"]["DG-NAS-HG4"]["status"] = "fail"
    canonical["grid"]["record_count"] = 17 if level == "DN" else 19
    path.write_text(json.dumps(canonical, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return canonical


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


def test_model_discovery_backend_is_pointer_only_and_terminal_verdict_free(tmp_path):
    from scripts import run_discovery_gated_nas as dg_nas_runner

    dg_nas_projection = dg_nas_runner.build_projection(generated_at="fixture-time")
    dg_nas_runner.write_artifacts(dg_nas_projection, root=tmp_path)
    adapter = ModelDiscoveryBackendEvidenceAdapter()
    first = adapter.compute_metrics(root=tmp_path, generated_at="fixture-time")
    second = adapter.compute_metrics(root=tmp_path, generated_at="fixture-time")

    assert json.dumps(first, sort_keys=True) == json.dumps(second, sort_keys=True)
    assert first["canonical_owner"] == {"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$"}
    assert first["projection_metadata"]["canonical_level_candidate"] == "DN"
    assert first["projection_metadata"]["canonical_failed_gate"] == "DG-NAS-HG7"
    for forbidden in ("model_candidates", "baselines", "task_grid", "nm_hardgates", "ledger_rows", "negative_witnesses"):
        assert forbidden not in first
    assert "terminal_verdict" not in json.dumps(first, sort_keys=True)
    assert "terminal_verdict" not in adapter.backend.metrics


def test_model_discovery_projection_metadata_points_to_dg_nas_owner(tmp_path):
    from scripts import run_discovery_gated_nas as dg_nas_runner

    dg_nas_projection = dg_nas_runner.build_projection(generated_at="fixture-time")
    dg_nas_runner.write_artifacts(dg_nas_projection, root=tmp_path)
    payload = build_model_discovery_payload(root=tmp_path, generated_at="fixture-time")
    canonical = json.loads((tmp_path / DG_NAS_CANONICAL_ARTIFACT).read_text(encoding="utf-8"))

    metadata = payload["projection_metadata"]
    assert metadata["canonical_owner"] == {"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$"}
    assert metadata["candidate_protocol_pointer"] == {"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$.candidate_protocol"}
    assert metadata["matched_baseline_pointer"] == {"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$.matched_baseline_control"}
    assert metadata["hardgate_pointer"] == {"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$.hardgate"}
    assert metadata["negative_witness_pointer"] == {"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$.negative_witness_mutations"}
    for key in (
        "candidate_protocol_pointer",
        "search_objective_pointer",
        "matched_baseline_pointer",
        "hardgate_pointer",
        "negative_witness_pointer",
        "discovery_map_signal_pointer",
    ):
        cell = metadata[key]
        assert pointer_value(canonical, cell["pointer"]) is not None, key


def test_model_discovery_adapter_projects_pointer_only_negative_rows(tmp_path):
    adapter = ModelDiscoveryBackendEvidenceAdapter()
    positive_root = tmp_path / "positive"
    negative_root = tmp_path / "negative"
    positive_canonical = _write_dg_nas_canonical(positive_root, level="D5-M")
    negative_canonical = _write_dg_nas_canonical(
        negative_root,
        level="DN",
        failed_gate_pointer="$.hardgate.gates.DG-NAS-HG4.status",
    )

    assert adapter.derive_negative_discovery_rows(root=positive_root) == ()

    negative_rows = adapter.derive_negative_discovery_rows(root=negative_root)
    assert negative_rows == (
        {
            "negative_id": "dn:model-discovery:discovery-gated-nas",
            "report_id": "model-discovery-suite",
            "kind": "model_discovery_projection",
            "report": "model-discovery-suite",
            "claim_id": "claim:model-discovery-suite",
            "source": f"{DG_NAS_CANONICAL_ARTIFACT}:$.discovery_map_signal",
            "json_artifact": RUN_ARTIFACT,
            "markdown_artifact": "reports/runs/model-discovery-suite/summary.md",
            "ledger_pointer": f"{DG_NAS_CANONICAL_ARTIFACT}:$.discovery_map_signal",
            "discovery_level": "DN",
            "classifier_reasons": ["canonical-dg-nas-hardgate-failed"],
            "projection_status": "projected",
            "evidence_pointer": "$.discovery_map_signal",
            "failed_gate": "$.hardgate.gates.DG-NAS-HG4.status",
            "what_was_learned": "DG-NAS canonical hardgate blocks the model-discovery projection.",
            "next_hypothesis": "inspect the canonical DG-NAS failed-gate pointer",
            "audit_status": "pass",
            "audit_reason": "",
        },
    )
    assert pointer_value(negative_canonical, negative_rows[0]["failed_gate"]) == "fail"

    positive_rows = adapter.derive_ledger_rows(root=positive_root)
    negative_ledger_rows = adapter.derive_ledger_rows(root=negative_root)
    assert adapter.project_discovery_level(root=positive_root) == positive_rows
    assert adapter.project_discovery_level(root=negative_root) == negative_ledger_rows
    assert positive_rows[0]["discovery_level"] == positive_canonical["discovery_map_signal"]["level_candidate"]
    assert negative_ledger_rows[0]["discovery_level"] == "DN"


def test_model_discovery_consumes_drt_by_pointer_only():
    adapter = ModelDiscoveryBackendEvidenceAdapter()
    source_spec = adapter.build_source_spec()
    payload = build_model_discovery_payload(root=runner.ROOT, generated_at="fixture-time")

    assert source_spec["discovery_regularized_training"]["artifact"] == DRT_CANONICAL_ARTIFACT
    refs = payload["discovery_regularized_training_refs"]
    assert refs["discovery_map_signal"] == {"artifact": DRT_CANONICAL_ARTIFACT, "pointer": "$.discovery_map_signal"}
    assert refs["surface_registry"] == {"artifact": DRT_CANONICAL_ARTIFACT, "pointer": "$.surface_registry"}
    assert refs["torch_training_evidence"] == {"artifact": DRT_CANONICAL_ARTIFACT, "pointer": "$.torch_training_evidence"}
    assert refs["negative_witness_mutations"] == {"artifact": DRT_CANONICAL_ARTIFACT, "pointer": "$.negative_witness_mutations"}
    assert "quality_q" not in refs
    assert "classifier_surface_delta" not in refs
    assert "hardgate" not in refs
    assert "terminal_verdict" not in json.dumps(refs, sort_keys=True)


def test_model_discovery_consumes_msn_by_pointer_only():
    adapter = ModelDiscoveryBackendEvidenceAdapter()
    source_spec = adapter.build_source_spec()
    payload = build_model_discovery_payload(root=runner.ROOT, generated_at="fixture-time")

    assert source_spec["mechanism_seeking_network"]["artifact"] == MSN_CANONICAL_ARTIFACT
    refs = payload["mechanism_seeking_network_refs"]
    assert refs["discovery_map_signal"] == {"artifact": MSN_CANONICAL_ARTIFACT, "pointer": "$.discovery_map_signal"}
    assert refs["surface_registry"] == {"artifact": MSN_CANONICAL_ARTIFACT, "pointer": "$.surface_registry"}
    assert refs["mechanism_gate_summary"] == {"artifact": MSN_CANONICAL_ARTIFACT, "pointer": "$.mechanism_gate_summary"}
    assert refs["gate_protocol"] == {"artifact": MSN_CANONICAL_ARTIFACT, "pointer": "$.gate_protocol"}
    assert "mechanism_score" not in refs
    assert "terminal_verdict" not in json.dumps(refs, sort_keys=True)


def test_model_discovery_consumes_cga_by_pointer_only():
    adapter = ModelDiscoveryBackendEvidenceAdapter()
    source_spec = adapter.build_source_spec()
    payload = build_model_discovery_payload(root=runner.ROOT, generated_at="fixture-time")

    assert source_spec["certificate_gated_attention"]["artifact"] == CGA_CANONICAL_ARTIFACT
    refs = payload["certificate_gated_attention_refs"]
    assert refs["discovery_map_signal"] == {"artifact": CGA_CANONICAL_ARTIFACT, "pointer": "$.discovery_map_signal"}
    assert refs["surface_registry"] == {"artifact": CGA_CANONICAL_ARTIFACT, "pointer": "$.surface_registry"}
    assert refs["certificate_gate_summary"] == {"artifact": CGA_CANONICAL_ARTIFACT, "pointer": "$.certificate_gate_summary"}
    assert refs["torch_attention_evidence"] == {"artifact": CGA_CANONICAL_ARTIFACT, "pointer": "$.torch_attention_evidence"}
    assert "attention_leak" not in refs
    assert "terminal_verdict" not in json.dumps(refs, sort_keys=True)


def test_model_discovery_consumes_dg_nas_by_pointer_only():
    adapter = ModelDiscoveryBackendEvidenceAdapter()
    source_spec = adapter.build_source_spec()
    payload = build_model_discovery_payload(root=runner.ROOT, generated_at="fixture-time")

    assert source_spec["discovery_gated_nas"]["artifact"] == DG_NAS_CANONICAL_ARTIFACT
    refs = payload["discovery_gated_nas_refs"]
    assert refs["discovery_map_signal"] == {"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$.discovery_map_signal"}
    assert refs["surface_registry"] == {"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$.surface_registry"}
    assert refs["candidate_protocol"] == {"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$.candidate_protocol"}
    assert refs["negative_witness_mutations"] == {"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$.negative_witness_mutations"}
    assert "search_score" not in refs
    assert "terminal_verdict" not in json.dumps(refs, sort_keys=True)


def test_model_discovery_summary_pointers_resolve_against_owned_artifacts(tmp_path):
    from scripts import run_discovery_gated_nas as dg_nas_runner

    dg_nas_projection = dg_nas_runner.build_projection(generated_at="fixture-time")
    dg_nas_runner.write_artifacts(dg_nas_projection, root=tmp_path)
    payload = build_model_discovery_payload(root=tmp_path, generated_at="fixture-time")
    canonical = json.loads((tmp_path / DG_NAS_CANONICAL_ARTIFACT).read_text(encoding="utf-8"))

    assert pointer_value(payload, "$.claim_capsule_ref.artifact") == CLAIM_CAPSULE_ARTIFACT
    for cell in payload["projection_metadata"].values():
        if isinstance(cell, dict) and cell.get("artifact") == DG_NAS_CANONICAL_ARTIFACT and cell["pointer"] != "$":
            assert pointer_value(canonical, cell["pointer"]) is not None, cell


def test_model_discovery_run_local_subtype_parity(tmp_path):
    from scripts import run_discovery_gated_nas as dg_nas_runner

    dg_nas_runner.write_artifacts(dg_nas_runner.build_projection(generated_at="fixture-time"), root=tmp_path)
    paths = runner.write_run(root=tmp_path, generated_at="fixture-time")
    summary = json.loads(Path(paths["summary"]).read_text(encoding="utf-8"))
    capsule = json.loads(Path(paths["claim_capsule"]).read_text(encoding="utf-8"))

    assert paths["summary"] == tmp_path / RUN_ARTIFACT
    assert paths["claim_capsule"] == tmp_path / CLAIM_CAPSULE_ARTIFACT
    assert capsule["schema_id"] == CLAIM_CAPSULE_SCHEMA_ID
    assert capsule["capsule_subtype"] == ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE
    assert summary["claim_capsule_ref"]["capsule_subtype"] == capsule["capsule_subtype"]
    assert pointer_value(summary, "$.claim_capsule_ref.artifact") == CLAIM_CAPSULE_ARTIFACT
    assert require_architecture_claim_capsule(capsule).payload["claim_id"] == "claim:model-discovery-suite"


def test_model_discovery_runner_reads_caller_root(tmp_path):
    canonical = _write_dg_nas_canonical(
        tmp_path,
        level="DN",
        failed_gate_pointer="$.hardgate.gates.DG-NAS-HG4.status",
    )

    paths = runner.write_run(root=tmp_path, generated_at="fixture-time")
    summary = json.loads(Path(paths["summary"]).read_text(encoding="utf-8"))
    markdown = Path(paths["markdown"]).read_text(encoding="utf-8")

    metadata = summary["projection_metadata"]
    assert metadata["canonical_level_candidate"] == "DN"
    assert metadata["canonical_failed_gate"] == "DG-NAS-HG4"
    assert metadata["canonical_record_count"] == canonical["grid"]["record_count"]
    assert metadata["canonical_record_count"] != 162
    assert "- Canonical level candidate: `DN`" in markdown
    assert "- Canonical failed gate: `DG-NAS-HG4`" in markdown


def test_model_discovery_capsule_evidence_pointers_resolve(tmp_path):
    from scripts import run_discovery_gated_nas as dg_nas_runner

    dg_nas_runner.write_artifacts(dg_nas_runner.build_projection(generated_at="fixture-time"), root=tmp_path)
    paths = runner.write_run(root=tmp_path, generated_at="fixture-time")
    artifacts = {
        RUN_ARTIFACT: json.loads(Path(paths["summary"]).read_text(encoding="utf-8")),
        CLAIM_CAPSULE_ARTIFACT: json.loads(Path(paths["claim_capsule"]).read_text(encoding="utf-8")),
    }
    capsule = artifacts[CLAIM_CAPSULE_ARTIFACT]
    summary = artifacts[RUN_ARTIFACT]
    canonical = json.loads((tmp_path / DG_NAS_CANONICAL_ARTIFACT).read_text(encoding="utf-8"))

    assert pointer_value(artifacts[capsule["source"]], capsule["source_pointer"]) is not None

    baseline_pointers = capsule["model_claim"]["baselines"]
    assert baseline_pointers == [{"artifact": DG_NAS_CANONICAL_ARTIFACT, "pointer": "$.matched_baseline_control"}]
    for cell in baseline_pointers:
        assert pointer_value(canonical, cell["pointer"]) is not None

    for key in ("candidate_pointer", "evidence_pointer"):
        cell = capsule["model_claim"][key]
        assert cell["artifact"] == DG_NAS_CANONICAL_ARTIFACT
        assert pointer_value(canonical, cell["pointer"]) is not None

    source_evidence = capsule["source_evidence"]
    assert pointer_value(artifacts[source_evidence["artifact"]], source_evidence["pointer"]) is not None

    forbidden_pointer = summary["claim_capsule_ref"]["forbidden_evidence_pointer"]
    assert pointer_value(capsule, forbidden_pointer) == ["test_label", "ood_label", "ledger_verdict"]

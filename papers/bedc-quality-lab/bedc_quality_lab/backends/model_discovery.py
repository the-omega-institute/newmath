"""Pointer-only model-discovery backend evidence."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.backend import TheoryBackend
from bedc_quality_lab.discovery_compiler.capsule import ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE


RUN_ARTIFACT = "reports/runs/model-discovery-suite/summary.json"
RUN_MARKDOWN_ARTIFACT = "reports/runs/model-discovery-suite/summary.md"
CLAIM_CAPSULE_ARTIFACT = "reports/runs/model-discovery-suite/claim_capsule.json"
DRT_CANONICAL_ARTIFACT = "reports/canonical/discovery-regularized-training.json"
MSN_CANONICAL_ARTIFACT = "reports/canonical/mechanism-seeking-network.json"
CGA_CANONICAL_ARTIFACT = "reports/canonical/certificate-gated-attention.json"
DG_NAS_CANONICAL_ARTIFACT = "reports/canonical/discovery-gated-nas.json"
LEJEPA_THEOREM_LEDGER_ARTIFACT = "reports/canonical/lejepa_theorem_ledger.json"
MUTATION_LEDGER_ARTIFACT = "reports/canonical/negative_witness_mutation_ledger.json"
MUTATION_LEDGER_ENTRIES_POINTER = "$.entries"


def _load_json_artifact(root: Path, artifact: str) -> Mapping[str, Any]:
    path = root / artifact
    return json.loads(path.read_text(encoding="utf-8"))


def _pointer(artifact: str, pointer: str) -> dict[str, str]:
    return {"artifact": artifact, "pointer": pointer}


def _dg_nas_projection_metadata(dg_nas: Mapping[str, Any]) -> dict[str, Any]:
    signal = dg_nas.get("discovery_map_signal", {})
    hardgate = dg_nas.get("hardgate", {})
    grid = dg_nas.get("grid", {})
    return {
        "canonical_owner": _pointer(DG_NAS_CANONICAL_ARTIFACT, "$"),
        "schema_pointer": _pointer(DG_NAS_CANONICAL_ARTIFACT, "$.schema_id"),
        "candidate_protocol_pointer": _pointer(DG_NAS_CANONICAL_ARTIFACT, "$.candidate_protocol"),
        "search_objective_pointer": _pointer(DG_NAS_CANONICAL_ARTIFACT, "$.search_objective_summary"),
        "matched_baseline_pointer": _pointer(DG_NAS_CANONICAL_ARTIFACT, "$.matched_baseline_control"),
        "hardgate_pointer": _pointer(DG_NAS_CANONICAL_ARTIFACT, "$.hardgate"),
        "negative_witness_pointer": _pointer(DG_NAS_CANONICAL_ARTIFACT, "$.negative_witness_mutations"),
        "mutation_lineage_pointer": _pointer(MUTATION_LEDGER_ARTIFACT, MUTATION_LEDGER_ENTRIES_POINTER),
        "discovery_map_signal_pointer": _pointer(DG_NAS_CANONICAL_ARTIFACT, "$.discovery_map_signal"),
        "canonical_status": signal.get("status"),
        "canonical_level_candidate": signal.get("level_candidate"),
        "canonical_failed_gate": hardgate.get("failed_gate"),
        "canonical_record_count": grid.get("record_count"),
        "projection_scope": "pointer-only run-local index over DG-NAS canonical evidence",
    }


def build_model_discovery_payload(*, root: Path, generated_at: str) -> dict[str, Any]:
    dg_nas = _load_json_artifact(root, DG_NAS_CANONICAL_ARTIFACT)
    claim_capsule_ref = {
        "artifact": CLAIM_CAPSULE_ARTIFACT,
        "pointer": "$",
        "capsule_subtype": ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE,
        "forbidden_evidence_pointer": "$.model_claim.forbidden_evidence",
    }
    payload = {
        "schema_id": "bedc.model.discovery_suite.run_local",
        "generated_at": generated_at,
        "producer": "bedc_quality_lab.backends.model_discovery",
        "json_artifact": RUN_ARTIFACT,
        "markdown_artifact": RUN_MARKDOWN_ARTIFACT,
        "claim_capsule_ref": claim_capsule_ref,
        "canonical_owner": _pointer(DG_NAS_CANONICAL_ARTIFACT, "$"),
        "projection_metadata": _dg_nas_projection_metadata(dg_nas),
        "discovery_regularized_training_refs": {
            "discovery_map_signal": {
                "artifact": DRT_CANONICAL_ARTIFACT,
                "pointer": "$.discovery_map_signal",
            },
            "surface_registry": {
                "artifact": DRT_CANONICAL_ARTIFACT,
                "pointer": "$.surface_registry",
            },
            "torch_training_evidence": {
                "artifact": DRT_CANONICAL_ARTIFACT,
                "pointer": "$.torch_training_evidence",
            },
            "negative_witness_mutations": {
                "artifact": DRT_CANONICAL_ARTIFACT,
                "pointer": "$.negative_witness_mutations",
            },
            "mutation_lineage": {
                "artifact": MUTATION_LEDGER_ARTIFACT,
                "pointer": MUTATION_LEDGER_ENTRIES_POINTER,
            },
            "theorem_ledger": {
                "artifact": LEJEPA_THEOREM_LEDGER_ARTIFACT,
                "pointer": "$.theorem_rows",
            },
        },
        "mechanism_seeking_network_refs": {
            "discovery_map_signal": {
                "artifact": MSN_CANONICAL_ARTIFACT,
                "pointer": "$.discovery_map_signal",
            },
            "surface_registry": {
                "artifact": MSN_CANONICAL_ARTIFACT,
                "pointer": "$.surface_registry",
            },
            "mechanism_gate_summary": {
                "artifact": MSN_CANONICAL_ARTIFACT,
                "pointer": "$.mechanism_gate_summary",
            },
            "gate_protocol": {
                "artifact": MSN_CANONICAL_ARTIFACT,
                "pointer": "$.gate_protocol",
            },
            "theorem_ledger": {
                "artifact": LEJEPA_THEOREM_LEDGER_ARTIFACT,
                "pointer": "$.theorem_rows",
            },
        },
        "certificate_gated_attention_refs": {
            "discovery_map_signal": {
                "artifact": CGA_CANONICAL_ARTIFACT,
                "pointer": "$.discovery_map_signal",
            },
            "surface_registry": {
                "artifact": CGA_CANONICAL_ARTIFACT,
                "pointer": "$.surface_registry",
            },
            "certificate_gate_summary": {
                "artifact": CGA_CANONICAL_ARTIFACT,
                "pointer": "$.certificate_gate_summary",
            },
            "route_patch_protocol": {
                "artifact": CGA_CANONICAL_ARTIFACT,
                "pointer": "$.route_patch_protocol",
            },
            "torch_attention_evidence": {
                "artifact": CGA_CANONICAL_ARTIFACT,
                "pointer": "$.torch_attention_evidence",
            },
            "theorem_ledger": {
                "artifact": LEJEPA_THEOREM_LEDGER_ARTIFACT,
                "pointer": "$.theorem_rows",
            },
        },
        "discovery_gated_nas_refs": {
            "discovery_map_signal": {
                "artifact": DG_NAS_CANONICAL_ARTIFACT,
                "pointer": "$.discovery_map_signal",
            },
            "surface_registry": {
                "artifact": DG_NAS_CANONICAL_ARTIFACT,
                "pointer": "$.surface_registry",
            },
            "candidate_protocol": {
                "artifact": DG_NAS_CANONICAL_ARTIFACT,
                "pointer": "$.candidate_protocol",
            },
            "negative_witness_mutations": {
                "artifact": DG_NAS_CANONICAL_ARTIFACT,
                "pointer": "$.negative_witness_mutations",
            },
            "mutation_lineage": {
                "artifact": MUTATION_LEDGER_ARTIFACT,
                "pointer": MUTATION_LEDGER_ENTRIES_POINTER,
            },
            "theorem_ledger": {
                "artifact": LEJEPA_THEOREM_LEDGER_ARTIFACT,
                "pointer": "$.theorem_rows",
            },
        },
        "not_claimed": [
            "run-local fact ownership",
            "independent model candidate definition",
            "independent hardgate verdict",
            "independent negative witness ledger",
        ],
    }
    return payload


class ModelDiscoveryBackendEvidenceAdapter:
    backend = TheoryBackend(
        name="model-discovery",
        scope_kind="run-local-model-discovery-suite",
        assumptions=("deterministic toy task rows are finite JSON objects",),
        metrics=("task_accuracy", "OOD_accuracy", "classifier_shift_count", "quality_q"),
        theorem_rows=(),
        ledger_rows=(),
        hardgates=(),
        not_claimed=("real-model training", "global architecture discovery verdict"),
    )

    def build_source_spec(self) -> Mapping[str, Any]:
        return {
            "run_artifact": RUN_ARTIFACT,
            "discovery_regularized_training": {
                "artifact": DRT_CANONICAL_ARTIFACT,
                "pointers": (
                    "$.discovery_map_signal",
                    "$.surface_registry",
                    "$.torch_training_evidence",
                    "$.negative_witness_mutations",
                    f"{MUTATION_LEDGER_ARTIFACT}:{MUTATION_LEDGER_ENTRIES_POINTER}",
                    "$.discovery_map_signal.theorem_ledger_ref",
                ),
            },
            "mechanism_seeking_network": {
                "artifact": MSN_CANONICAL_ARTIFACT,
                "pointers": (
                    "$.discovery_map_signal",
                    "$.surface_registry",
                    "$.mechanism_gate_summary",
                    "$.gate_protocol",
                    "$.discovery_map_signal.theorem_ledger_ref",
                ),
            },
            "certificate_gated_attention": {
                "artifact": CGA_CANONICAL_ARTIFACT,
                "pointers": (
                    "$.discovery_map_signal",
                    "$.surface_registry",
                    "$.certificate_gate_summary",
                    "$.route_patch_protocol",
                    "$.torch_attention_evidence",
                    "$.discovery_map_signal.theorem_ledger_ref",
                ),
            },
            "discovery_gated_nas": {
                "artifact": DG_NAS_CANONICAL_ARTIFACT,
                "pointers": (
                    "$.discovery_map_signal",
                    "$.surface_registry",
                    "$.candidate_protocol",
                    "$.negative_witness_mutations",
                    f"{MUTATION_LEDGER_ARTIFACT}:{MUTATION_LEDGER_ENTRIES_POINTER}",
                    "$.discovery_map_signal.theorem_ledger_ref",
                ),
            },
        }

    def build_pattern_spec(self) -> Mapping[str, Any]:
        return {"status": "run-local", "capsule_subtype": ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE}

    def build_classifier_spec(self) -> Mapping[str, Any]:
        return {"levels": ["D5-M", "DN"], "verdict_owner": "core-compiler"}

    def compute_metrics(self, *, root: Path, generated_at: str | None = None) -> Mapping[str, Any]:
        return build_model_discovery_payload(root=root, generated_at=generated_at or "model-discovery-run-local")

    def derive_ledger_rows(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        del generated_at
        dg_nas = _load_json_artifact(root, DG_NAS_CANONICAL_ARTIFACT)
        signal = dg_nas.get("discovery_map_signal", {})
        return (
            {
                "row_id": "model-discovery:discovery-gated-nas",
                "report_id": "model-discovery-suite",
                "source_artifact": DG_NAS_CANONICAL_ARTIFACT,
                "source_pointer": "$.discovery_map_signal",
                "discovery_level": signal.get("level_candidate"),
                "capsule_subtype": ARCHITECTURE_CLAIM_CAPSULE_SUBTYPE,
                "claim_capsule_pointer": "$.claim_capsule_ref.artifact",
            },
        )

    def derive_negative_discovery_rows(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        del generated_at
        dg_nas = _load_json_artifact(root, DG_NAS_CANONICAL_ARTIFACT)
        signal = dg_nas.get("discovery_map_signal", {})
        if signal.get("level_candidate") != "DN":
            return ()
        return (
            {
                "negative_id": "dn:model-discovery:discovery-gated-nas",
                "report_id": "model-discovery-suite",
                "kind": "model_discovery_projection",
                "report": "model-discovery-suite",
                "claim_id": "claim:model-discovery-suite",
                "source": f"{DG_NAS_CANONICAL_ARTIFACT}:$.discovery_map_signal",
                "json_artifact": RUN_ARTIFACT,
                "markdown_artifact": RUN_MARKDOWN_ARTIFACT,
                "ledger_pointer": f"{DG_NAS_CANONICAL_ARTIFACT}:$.discovery_map_signal",
                "discovery_level": "DN",
                "classifier_reasons": ["canonical-dg-nas-hardgate-failed"],
                "projection_status": "projected",
                "evidence_pointer": "$.discovery_map_signal",
                "failed_gate": signal.get("failed_gate_pointer"),
                "what_was_learned": "DG-NAS canonical hardgate blocks the model-discovery projection.",
                "next_hypothesis": "inspect the canonical DG-NAS failed-gate pointer",
                "audit_status": "pass",
                "audit_reason": "",
            },
        )

    def project_discovery_level(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        return self.derive_ledger_rows(root=root, generated_at=generated_at)

"""Pointer-only model discovery backend references."""

from __future__ import annotations

import json
from typing import Any


DGT_CANONICAL_ARTIFACT = "reports/canonical/discovery-gated-transformer.json"
NEW_MODEL_HARDGATES_ARTIFACT = "reports/canonical/new_model_hardgates.json"

FORBIDDEN_COPIED_FIELDS = {
    "accuracy",
    "loss",
    "records",
    "raw_metrics",
    "terminal_verdict",
    "candidate_metrics",
    "candidate_measurements",
    "hardgate_status_body",
}


def discovery_gated_transformer_refs() -> dict[str, Any]:
    return {
        "model_id_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.model_id",
        "owner_pointer": f"{DGT_CANONICAL_ARTIFACT}:$",
        "hardgate_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.hardgate",
        "new_model_hardgates_pointer": f"{NEW_MODEL_HARDGATES_ARTIFACT}:$.gates",
        "component_refs_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.component_refs",
        "hardgate_status_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.hardgate.status",
        "discovery_map_signal_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.discovery_map_signal",
        "family_definition_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.family_definition",
        "family_definition_hardgate_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.family_definition.hardgate",
        "model_family_claim_status_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.family_definition.model_family_claim_status",
        "claim_capsule_ref_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.claim_capsule_ref",
        "evidence_envelope_ref_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.evidence_envelope_ref",
        "mechanism_namecert_ref_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.mechanism_namecert_ref",
        "jet_certificate_ref_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.jet_certificate_ref",
        "not_claimed_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.not_claimed",
        "claim_capsule_pointer": "reports/runs/discovery-gated-transformer/claim_capsule.json:$",
        "evidence_envelope_pointer": "reports/runs/discovery-gated-transformer/evidence_envelope.json:$",
        "mechanism_namecert_pointer": "reports/runs/discovery-gated-transformer/mechanism_namecert.json:$",
        "jet_certificate_pointer": "reports/runs/discovery-gated-transformer/jet_certificate.json:$",
    }


DGT_PROJECTION_METADATA = {
    "projection_id": "discovery_gated_transformer_refs",
    "canonical_artifact": DGT_CANONICAL_ARTIFACT,
    "hardgate_sidecar_artifact": NEW_MODEL_HARDGATES_ARTIFACT,
    "surface": "pointer-only",
    "refs": discovery_gated_transformer_refs(),
}


def assert_pointer_only(payload: Any) -> None:
    serialized = json.dumps(payload, sort_keys=True).lower()
    for field in FORBIDDEN_COPIED_FIELDS:
        if f'"{field.lower()}"' in serialized:
            raise ValueError(f"model discovery refs contain copied field: {field}")
    if "raw positive claim" in serialized:
        raise ValueError("model discovery refs contain raw positive claim prose")

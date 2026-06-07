"""Pointer-only model discovery backend references."""

from __future__ import annotations

import json
from typing import Any


DGT_CANONICAL_ARTIFACT = "reports/canonical/discovery_gated_transformer.json"
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
        "hardgate_contract_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.hardgate_contract_ref",
        "new_model_hardgates_pointer": f"{NEW_MODEL_HARDGATES_ARTIFACT}:$.gates",
        "hardgate_instances_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.hardgate_instances",
        "prototype_status_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.prototype_status",
        "discovery_map_signal_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.discovery_map_signal",
        "claim_capsule_ref_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.claim_capsule_ref",
        "not_claimed_pointer": f"{DGT_CANONICAL_ARTIFACT}:$.not_claimed",
        "run_summary_pointer": "reports/runs/discovery_gated_transformer/summary.json:$",
        "claim_capsule_pointer": "reports/runs/discovery_gated_transformer/claim_capsule.json:$",
        "raw_metrics_pointer": "reports/runs/discovery_gated_transformer/raw_metrics.jsonl:$.lines",
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

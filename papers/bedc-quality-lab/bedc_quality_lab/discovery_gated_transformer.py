"""Discovery-gated transformer canonical projection."""

from __future__ import annotations

from dataclasses import dataclass
import json
from typing import Any, Mapping, Sequence


SCHEMA_ID = "bedc-quality-lab:discovery-gated-transformer"
ARTIFACT_ID = "bedc-quality-lab:discovery-gated-transformer"
MODEL_ID = "discovery-gated-transformer"
PRODUCER = "scripts/run_discovery_gated_transformer.py"
PROJECTOR = "bedc_quality_lab.discovery_gated_transformer.DiscoveryGatedTransformerProjector"
CANONICAL_JSON_ARTIFACT = "reports/canonical/discovery-gated-transformer.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/discovery-gated-transformer.md"
RUN_ROOT = "reports/runs/discovery-gated-transformer"
CLAIM_CAPSULE_ARTIFACT = f"{RUN_ROOT}/claim_capsule.json"
EVIDENCE_ENVELOPE_ARTIFACT = f"{RUN_ROOT}/evidence_envelope.json"
MECHANISM_NAMECERT_ARTIFACT = f"{RUN_ROOT}/mechanism_namecert.json"
JET_CERTIFICATE_ARTIFACT = f"{RUN_ROOT}/jet_certificate.json"
GATE_NAMES = tuple(f"DGT-HG{index}" for index in range(1, 21))
TOOL_ROUTE_SCHEMA_ID = "bedc-quality-lab:discovery-gated-transformer.tool-route-evidence"
TOOL_ROUTE_ARTIFACT_ID = "bedc-quality-lab:discovery-gated-transformer.tool-route-evidence"
TOOL_ROUTE_OWNER_REF = f"{CANONICAL_JSON_ARTIFACT}:$"
TOOL_ROUTE_SOURCE_ISSUE_REF = "github:issue:928"
TOOL_ROUTE_CGA_ROUTE_PATCH_REF = "reports/canonical/certificate-gated-attention.json:$.route_patch_protocol"
TOOL_ROUTE_REQUIRED_KEYS = (
    "schema_id",
    "artifact_id",
    "owner_ref",
    "source_issue_ref",
    "synthetic_tool_call_grid",
    "route_classes",
    "cga_route_patch_ref",
    "admission_ledger",
    "blocked_route_evidence",
    "unsafe_invalid_audit",
    "classifier_surface_delta",
    "net_positive_signal",
    "hardgate",
    "failed_gate",
    "not_claimed",
    "revocation_rows",
    "forbidden_alias_audit",
)
TOOL_ROUTE_GATE_NAMES = tuple(f"DGT-TOOL-HG{index}" for index in range(1, 7))
FAMILY_DEFINITION_SCHEMA_ID = "bedc-quality-lab:discovery-gated-transformer.family-definition"
FAMILY_DEFINITION_ARTIFACT_ID = "bedc-quality-lab:discovery-gated-transformer.family-definition"
FAMILY_DEFINITION_OWNER_REF = f"{CANONICAL_JSON_ARTIFACT}:$"
FAMILY_DEFINITION_POINTER = f"{CANONICAL_JSON_ARTIFACT}:$.family_definition"
FAMILY_DEFINITION_REQUIRED_KEYS = (
    "schema_id",
    "artifact_id",
    "owner_ref",
    "slot_state",
    "definition_scope",
    "invariant_groups",
    "hardgate",
    "model_family_claim_status",
    "not_claimed",
    "forbidden_claim_term_audit",
)
FAMILY_DEFINITION_GROUPS = ("architecture", "objective", "certificate")
FAMILY_DEFINITION_GATE_NAMES = tuple(f"DGT-FAMILY-HG{index}" for index in range(1, 5))
FAMILY_DEFINITION_FORBIDDEN_TERMS = (
    "global superiority",
    "architecture superiority",
    "production authority",
    "universal training recipe",
    "terminal verdict",
)
CLAIMED_POSITIVE_ROUTE_CLASSES = frozenset({"valid_positive_discovery"})
BLOCKED_ROUTE_CLASSES = frozenset({"invalid_route", "unsafe_route"})
TOOL_ROUTE_RECURSIVE_FORBIDDEN_TOKENS = (
    ".refactor-loop",
    "host.env",
    "terminal_verdict",
    "discovery_gated_transformer",
    "tool-use-dgt",
    "tool-use-toy-dgt",
    "tool_use_dgt",
    "tool_use_toy_dgt",
)
COPIED_CGA_PAYLOAD_KEYS = frozenset(
    {
        "route_patch_protocol",
        "cga_route_patch_protocol",
        "classifier_payload",
        "classifier_surface",
        "cga_metric_body",
        "cga_metrics",
        "certificate_gate_summary",
        "torch_attention_evidence",
    }
)
REJECTED_INLINE_KEYS = frozenset(
    {
        "records",
        "quality_q",
        "attention_rows",
        "attention",
        "search_score",
        "search_score_rows",
        "terminal_verdict",
        "standalone_verdict",
        "private_row_carrier",
        "raw_metrics",
        "metric_rows",
        *COPIED_CGA_PAYLOAD_KEYS,
    }
)
NOT_CLAIMED = (
    "No global superiority or architecture superiority claim.",
    "No production authority or deployment authority.",
    "No universal training recipe claim.",
    "No terminal verdict ownership.",
)


@dataclass(frozen=True)
class EvidenceCell:
    artifact: str
    pointer: str

    def as_payload(self) -> dict[str, str]:
        return {"artifact": self.artifact, "pointer": self.pointer}


def artifact_pointer(cell: Mapping[str, Any]) -> str:
    return f"{cell['artifact']}:{cell['pointer']}"


def _cell(artifact: str, pointer: str) -> dict[str, str]:
    return EvidenceCell(artifact=artifact, pointer=pointer).as_payload()


def default_component_refs() -> dict[str, dict[str, str]]:
    return {
        "hardgate_contract": _cell("reports/canonical/new_model_hardgates.json", "$.gates"),
        "discovery_gated_nas": _cell("reports/canonical/discovery-gated-nas.json", "$.candidate_protocol.design_search_certificate"),
        "discovery_map": _cell("reports/canonical/discovery_map.json", "$.coverage_matrix"),
        "training_replay": _cell(
            "reports/canonical/discovery-gated-transformer-training.json",
            "$.hardgates",
        ),
    }


def default_architecture_spec() -> dict[str, Any]:
    return {
        "architecture_id": MODEL_ID,
        "role": "bounded sequence transformer prototype",
        "gating_protocol": "discovery hardgate before promotion",
        "evidence_policy": "pointer-only source cells",
        "component_order": [
            "hardgate_contract",
            "discovery_gated_nas",
            "discovery_map",
            "training_replay",
        ],
    }


def default_discovery_map_signal() -> dict[str, Any]:
    return {
        "status": "candidate-local-positive",
        "level_candidate": "D4",
        "evidence": _cell(CANONICAL_JSON_ARTIFACT, "$.hardgate.status"),
        "map_ref": _cell("reports/canonical/discovery_map.json", "$.coverage_matrix"),
    }


def _default_family_definition_groups() -> dict[str, dict[str, Any]]:
    return {
        "architecture": {
            "group_id": "architecture",
            "required": True,
            "evidence_pointers": [
                f"{CANONICAL_JSON_ARTIFACT}:$.model_id",
                f"{CANONICAL_JSON_ARTIFACT}:$.architecture_spec",
                f"{CANONICAL_JSON_ARTIFACT}:$.component_refs",
            ],
        },
        "objective": {
            "group_id": "objective",
            "required": True,
            "evidence_pointers": [
                f"{CANONICAL_JSON_ARTIFACT}:$.discovery_map_signal",
                f"{CANONICAL_JSON_ARTIFACT}:$.hardgate",
                f"{CANONICAL_JSON_ARTIFACT}:$.tool_route_evidence",
            ],
        },
        "certificate": {
            "group_id": "certificate",
            "required": True,
            "evidence_pointers": [
                f"{CANONICAL_JSON_ARTIFACT}:$.claim_capsule_ref",
                f"{CANONICAL_JSON_ARTIFACT}:$.evidence_envelope_ref",
                f"{CANONICAL_JSON_ARTIFACT}:$.mechanism_namecert_ref",
                f"{CANONICAL_JSON_ARTIFACT}:$.jet_certificate_ref",
            ],
        },
    }


def _family_definition_gate_rows(payload: Mapping[str, Any], failed: Sequence[str]) -> dict[str, dict[str, Any]]:
    failed_set = set(failed)
    evidence_pointers = {
        "DGT-FAMILY-HG1": "$.family_definition.invariant_groups.architecture",
        "DGT-FAMILY-HG2": "$.family_definition.invariant_groups.objective",
        "DGT-FAMILY-HG3": "$.family_definition.invariant_groups.certificate",
        "DGT-FAMILY-HG4": "$.family_definition.forbidden_claim_term_audit",
    }
    del payload
    return {
        gate_name: {
            "status": "fail" if gate_name in failed_set else "pass",
            "evidence": _cell(CANONICAL_JSON_ARTIFACT, evidence_pointers[gate_name]),
        }
        for gate_name in FAMILY_DEFINITION_GATE_NAMES
    }


def _forbidden_family_definition_claim_term_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    serialized = json.dumps(
        {
            "definition_scope": payload.get("definition_scope"),
            "model_family_claim_status": payload.get("model_family_claim_status"),
            "not_claimed": payload.get("not_claimed"),
        },
        sort_keys=True,
    ).lower()
    hits = [term for term in FAMILY_DEFINITION_FORBIDDEN_TERMS if term in serialized]
    return {
        "status": "pass" if not hits else "fail",
        "hits": hits,
        "forbidden_terms": list(FAMILY_DEFINITION_FORBIDDEN_TERMS),
    }


def evaluate_dgt_family_definition_hardgate(payload: Mapping[str, Any]) -> dict[str, Any]:
    failed: list[str] = []
    groups = payload.get("invariant_groups")
    groups = groups if isinstance(groups, Mapping) else {}
    for index, group_name in enumerate(FAMILY_DEFINITION_GROUPS, start=1):
        group = groups.get(group_name)
        pointers = group.get("evidence_pointers") if isinstance(group, Mapping) else None
        if (
            not isinstance(group, Mapping)
            or group.get("group_id") != group_name
            or group.get("required") is not True
            or not isinstance(pointers, list)
            or not pointers
            or any(not isinstance(pointer, str) or not pointer.startswith(f"{CANONICAL_JSON_ARTIFACT}:$") for pointer in pointers)
        ):
            failed.append(f"DGT-FAMILY-HG{index}")
    audit = payload.get("forbidden_claim_term_audit")
    expected_audit = _forbidden_family_definition_claim_term_audit(payload)
    if not isinstance(audit, Mapping) or dict(audit) != expected_audit or expected_audit["status"] != "pass":
        failed.append("DGT-FAMILY-HG4")
    failed_gate = sorted(set(failed), key=FAMILY_DEFINITION_GATE_NAMES.index)
    return {
        "status": "pass" if not failed_gate else "fail",
        "gate_names": list(FAMILY_DEFINITION_GATE_NAMES),
        "gates": _family_definition_gate_rows(payload, failed_gate),
        "failed_gate": failed_gate,
    }


def _family_claim_status_from_hardgate(hardgate: Mapping[str, Any]) -> dict[str, Any]:
    if hardgate.get("status") == "pass":
        return {
            "status": "definition-recorded",
            "claim_scope": "structural pointer definition only",
            "claim_allowed": False,
        }
    return {
        "status": "blocked",
        "claim_scope": "structural pointer definition only",
        "claim_allowed": False,
        "blocked_by": list(hardgate.get("failed_gate", [])),
    }


def build_dgt_family_definition() -> dict[str, Any]:
    payload: dict[str, Any] = {
        "schema_id": FAMILY_DEFINITION_SCHEMA_ID,
        "artifact_id": FAMILY_DEFINITION_ARTIFACT_ID,
        "owner_ref": FAMILY_DEFINITION_OWNER_REF,
        "slot_state": "present-fail-closed",
        "definition_scope": "bounded DGT structural family definition",
        "invariant_groups": _default_family_definition_groups(),
        "hardgate": {},
        "model_family_claim_status": {},
        "not_claimed": [
            "The family definition is a pointer bundle inside the DGT owner.",
            "The family definition is not a standalone report, runner, backend, registry, or host setting.",
            "The family definition does not admit deployment, promotion, or external authority.",
        ],
        "forbidden_claim_term_audit": {},
    }
    payload["forbidden_claim_term_audit"] = _forbidden_family_definition_claim_term_audit(payload)
    payload["hardgate"] = evaluate_dgt_family_definition_hardgate(payload)
    payload["model_family_claim_status"] = _family_claim_status_from_hardgate(payload["hardgate"])
    payload["forbidden_claim_term_audit"] = _forbidden_family_definition_claim_term_audit(payload)
    payload["hardgate"] = evaluate_dgt_family_definition_hardgate(payload)
    validate_dgt_family_definition(payload)
    return payload


def validate_dgt_family_definition(payload: Mapping[str, Any]) -> None:
    if set(payload) != set(FAMILY_DEFINITION_REQUIRED_KEYS):
        raise ValueError("DGT family definition fields mismatch")
    if payload["schema_id"] != FAMILY_DEFINITION_SCHEMA_ID or payload["artifact_id"] != FAMILY_DEFINITION_ARTIFACT_ID:
        raise ValueError("DGT family definition identity mismatch")
    if payload["owner_ref"] != FAMILY_DEFINITION_OWNER_REF:
        raise ValueError("DGT family definition owner pointer mismatch")
    if payload["slot_state"] != "present-fail-closed":
        raise ValueError("DGT family definition slot state mismatch")
    groups = payload["invariant_groups"]
    if not isinstance(groups, Mapping) or set(groups) != set(FAMILY_DEFINITION_GROUPS):
        raise ValueError("DGT family definition invariant groups mismatch")
    for group_name, group in groups.items():
        if not isinstance(group, Mapping) or set(group) != {"group_id", "required", "evidence_pointers"}:
            raise ValueError(f"DGT family definition group schema mismatch: {group_name}")
    expected_hardgate = evaluate_dgt_family_definition_hardgate(payload)
    if payload["hardgate"] != expected_hardgate:
        raise ValueError("DGT family definition hardgate mismatch")
    if expected_hardgate["status"] != "pass":
        raise ValueError("DGT family definition hardgate failed")
    expected_claim_status = _family_claim_status_from_hardgate(expected_hardgate)
    if payload["model_family_claim_status"] != expected_claim_status:
        raise ValueError("DGT family definition claim status mismatch")
    found = _has_recursive_token(payload, (".refactor-loop", "host.env", "terminal_verdict"))
    if found is not None:
        raise ValueError(f"DGT family definition contains forbidden value: {found}")


def sidecar_refs() -> dict[str, dict[str, str]]:
    return {
        "claim_capsule_ref": _cell(CLAIM_CAPSULE_ARTIFACT, "$"),
        "evidence_envelope_ref": _cell(EVIDENCE_ENVELOPE_ARTIFACT, "$"),
        "mechanism_namecert_ref": _cell(MECHANISM_NAMECERT_ARTIFACT, "$"),
        "jet_certificate_ref": _cell(JET_CERTIFICATE_ARTIFACT, "$"),
    }


def default_sidecars(*, generated_at: str) -> dict[str, dict[str, Any]]:
    return {
        "claim_capsule": {
            "schema_id": "bedc-quality-lab:dgt-claim-capsule",
            "generated_at": generated_at,
            "artifact_id": "bedc-quality-lab:dgt-claim-capsule",
            "model_id": MODEL_ID,
            "claim_scope": "bounded D4 candidate prototype",
            "owner_ref": _cell(CANONICAL_JSON_ARTIFACT, "$"),
            "not_claimed_ref": _cell(CANONICAL_JSON_ARTIFACT, "$.not_claimed"),
        },
        "evidence_envelope": {
            "schema_id": "bedc-quality-lab:dgt-evidence-envelope",
            "generated_at": generated_at,
            "artifact_id": "bedc-quality-lab:dgt-evidence-envelope",
            "model_id": MODEL_ID,
            "component_refs": default_component_refs(),
            "evidence_policy": "pointer-only",
        },
        "mechanism_namecert": {
            "schema_id": "bedc-quality-lab:dgt-mechanism-namecert",
            "generated_at": generated_at,
            "artifact_id": "bedc-quality-lab:dgt-mechanism-namecert",
            "model_id": MODEL_ID,
            "candidate_mechanism": "discovery-gated sequence route",
            "evidence_ref": _cell(EVIDENCE_ENVELOPE_ARTIFACT, "$.component_refs"),
        },
        "jet_certificate": {
            "schema_id": "bedc-quality-lab:dgt-jet-certificate",
            "generated_at": generated_at,
            "artifact_id": "bedc-quality-lab:dgt-jet-certificate",
            "model_id": MODEL_ID,
            "certificate_scope": "D4 prototype candidate boundary",
            "mechanism_ref": _cell(MECHANISM_NAMECERT_ARTIFACT, "$"),
        },
    }


def _has_recursive_key(value: Any, forbidden: frozenset[str]) -> str | None:
    if isinstance(value, Mapping):
        for key, item in value.items():
            if isinstance(key, str) and key in forbidden:
                return key
            found = _has_recursive_key(item, forbidden)
            if found is not None:
                return found
    elif isinstance(value, (list, tuple)):
        for item in value:
            found = _has_recursive_key(item, forbidden)
            if found is not None:
                return found
    return None


def _has_recursive_token(value: Any, forbidden: Sequence[str]) -> str | None:
    if isinstance(value, str):
        lowered = value.lower()
        for token in forbidden:
            if token in lowered:
                return token
    elif isinstance(value, Mapping):
        for key, item in value.items():
            if isinstance(key, str):
                lowered_key = key.lower()
                for token in forbidden:
                    if token in lowered_key:
                        return token
            found = _has_recursive_token(item, forbidden)
            if found is not None:
                return found
    elif isinstance(value, (list, tuple)):
        for item in value:
            found = _has_recursive_token(item, forbidden)
            if found is not None:
                return found
    return None


def _is_cell(value: Any) -> bool:
    return (
        isinstance(value, Mapping)
        and set(value) == {"artifact", "pointer"}
        and isinstance(value["artifact"], str)
        and isinstance(value["pointer"], str)
        and value["artifact"]
        and value["pointer"].startswith("$")
    )


def _walk_cells(value: Any) -> bool:
    if _is_cell(value):
        return True
    if isinstance(value, Mapping):
        return all(_walk_cells(item) for item in value.values())
    if isinstance(value, list):
        return all(_walk_cells(item) for item in value)
    return not isinstance(value, (dict, list))


def _artifact_pointer_cell(value: str) -> dict[str, str]:
    artifact, pointer = value.split(":", 1)
    return _cell(artifact, pointer)


def _synthetic_tool_call_grid() -> list[dict[str, Any]]:
    return [
        {
            "route_id": "route_math_lookup_positive",
            "tool": "symbolic-table",
            "route_class": "valid_positive_discovery",
            "classifier_surface_delta": {
                "before": "route-unclassified",
                "after": "tool-route-positive-discovery",
                "surface_delta_count": 2,
            },
            "net_positive_signal": True,
            "admission_decision": "admit",
        },
        {
            "route_id": "route_ledger_patch_positive",
            "tool": "ledger-patcher",
            "route_class": "valid_positive_discovery",
            "classifier_surface_delta": {
                "before": "candidate-ledger-gap",
                "after": "route-patched-positive-discovery",
                "surface_delta_count": 1,
            },
            "net_positive_signal": True,
            "admission_decision": "admit",
        },
        {
            "route_id": "route_schema_invalid",
            "tool": "schema-mutator",
            "route_class": "invalid_route",
            "classifier_surface_delta": None,
            "net_positive_signal": False,
            "admission_decision": "block",
        },
        {
            "route_id": "route_secret_unsafe",
            "tool": "host-secret-reader",
            "route_class": "unsafe_route",
            "classifier_surface_delta": None,
            "net_positive_signal": False,
            "admission_decision": "block",
        },
        {
            "route_id": "route_control_neutral",
            "tool": "no-op-control",
            "route_class": "neutral_control",
            "classifier_surface_delta": None,
            "net_positive_signal": False,
            "admission_decision": "do-not-admit",
        },
    ]


def _tool_route_gate_rows(payload: Mapping[str, Any], failed: Sequence[str]) -> dict[str, dict[str, Any]]:
    failed_set = set(failed)
    evidence_pointers = {
        "DGT-TOOL-HG1": "$.tool_route_evidence.classifier_surface_delta",
        "DGT-TOOL-HG2": "$.tool_route_evidence.cga_route_patch_ref",
        "DGT-TOOL-HG3": "$.tool_route_evidence.admission_ledger",
        "DGT-TOOL-HG4": "$.tool_route_evidence.blocked_route_evidence",
        "DGT-TOOL-HG5": "$.tool_route_evidence.not_claimed",
        "DGT-TOOL-HG6": "$.tool_route_evidence.forbidden_alias_audit",
    }
    return {
        gate_name: {
            "status": "fail" if gate_name in failed_set else "pass",
            "evidence": _cell(CANONICAL_JSON_ARTIFACT, evidence_pointers[gate_name]),
        }
        for gate_name in TOOL_ROUTE_GATE_NAMES
    }


def evaluate_dgt_tool_route_hardgates(payload: Mapping[str, Any]) -> dict[str, Any]:
    failed: list[str] = []
    rows = payload.get("synthetic_tool_call_grid")
    rows = rows if isinstance(rows, list) else []
    positive_rows = [row for row in rows if isinstance(row, Mapping) and row.get("route_class") in CLAIMED_POSITIVE_ROUTE_CLASSES]
    if any(not row.get("classifier_surface_delta") or row.get("net_positive_signal") is not True for row in positive_rows):
        failed.append("DGT-TOOL-HG1")

    if payload.get("cga_route_patch_ref") != TOOL_ROUTE_CGA_ROUTE_PATCH_REF:
        failed.append("DGT-TOOL-HG2")
    if _has_recursive_key(payload, COPIED_CGA_PAYLOAD_KEYS) is not None:
        failed.append("DGT-TOOL-HG2")

    ledger = payload.get("admission_ledger")
    ledger_rows = ledger.get("rows") if isinstance(ledger, Mapping) else None
    ledger_rows = ledger_rows if isinstance(ledger_rows, list) else []
    route_class_by_id = {
        row["route_id"]: row.get("route_class")
        for row in rows
        if isinstance(row, Mapping) and isinstance(row.get("route_id"), str)
    }
    ledgered_blocked = [
        row.get("route_id")
        for row in ledger_rows
        if isinstance(row, Mapping) and route_class_by_id.get(row.get("route_id")) in BLOCKED_ROUTE_CLASSES
    ]
    if ledgered_blocked:
        failed.append("DGT-TOOL-HG3")

    blocked = payload.get("blocked_route_evidence")
    blocked_rows = blocked.get("rows") if isinstance(blocked, Mapping) else None
    blocked_rows = blocked_rows if isinstance(blocked_rows, list) else []
    blocked_ids = {row.get("route_id") for row in blocked_rows if isinstance(row, Mapping)}
    invalid_unsafe_ids = {
        row.get("route_id")
        for row in rows
        if isinstance(row, Mapping) and row.get("route_class") in BLOCKED_ROUTE_CLASSES
    }
    if not invalid_unsafe_ids.issubset(blocked_ids):
        failed.append("DGT-TOOL-HG4")

    if not payload.get("not_claimed"):
        failed.append("DGT-TOOL-HG5")

    if _has_recursive_token(payload, TOOL_ROUTE_RECURSIVE_FORBIDDEN_TOKENS) is not None:
        failed.append("DGT-TOOL-HG6")

    failed_gate = sorted(set(failed), key=TOOL_ROUTE_GATE_NAMES.index)
    return {
        "status": "pass" if not failed_gate else "fail",
        "gate_names": list(TOOL_ROUTE_GATE_NAMES),
        "gates": _tool_route_gate_rows(payload, failed_gate),
        "failed_gate": failed_gate,
    }


def build_dgt_tool_route_evidence(*, generated_at: str) -> dict[str, Any]:
    rows = _synthetic_tool_call_grid()
    admitted = [
        {
            "route_id": row["route_id"],
            "route_class": row["route_class"],
            "admission_basis_ref": f"{CANONICAL_JSON_ARTIFACT}:$.tool_route_evidence.synthetic_tool_call_grid[{index}]",
        }
        for index, row in enumerate(rows)
        if row["admission_decision"] == "admit"
    ]
    blocked = [
        {
            "route_id": row["route_id"],
            "route_class": row["route_class"],
            "block_basis": "invalid-or-unsafe-route",
            "evidence_ref": f"{CANONICAL_JSON_ARTIFACT}:$.tool_route_evidence.synthetic_tool_call_grid[{index}]",
        }
        for index, row in enumerate(rows)
        if row["route_class"] in BLOCKED_ROUTE_CLASSES
    ]
    classifier_surface_delta = {
        row["route_id"]: row["classifier_surface_delta"]
        for row in rows
        if row["route_class"] in CLAIMED_POSITIVE_ROUTE_CLASSES
    }
    payload: dict[str, Any] = {
        "schema_id": TOOL_ROUTE_SCHEMA_ID,
        "artifact_id": TOOL_ROUTE_ARTIFACT_ID,
        "owner_ref": TOOL_ROUTE_OWNER_REF,
        "source_issue_ref": TOOL_ROUTE_SOURCE_ISSUE_REF,
        "synthetic_tool_call_grid": rows,
        "route_classes": {
            "claimed_positive": sorted(CLAIMED_POSITIVE_ROUTE_CLASSES),
            "blocked": sorted(BLOCKED_ROUTE_CLASSES),
            "control": ["neutral_control"],
        },
        "cga_route_patch_ref": TOOL_ROUTE_CGA_ROUTE_PATCH_REF,
        "admission_ledger": {
            "policy": "admit only valid positive-discovery routes with classifier delta and net-positive signal",
            "rows": admitted,
        },
        "blocked_route_evidence": {"rows": blocked},
        "unsafe_invalid_audit": {
            "status": "pass",
            "invalid_or_unsafe_route_ids": [row["route_id"] for row in blocked],
            "ledgered_invalid_or_unsafe_route_ids": [],
        },
        "classifier_surface_delta": classifier_surface_delta,
        "net_positive_signal": True,
        "hardgate": {},
        "failed_gate": [],
        "not_claimed": [
            "Tool-route evidence is bounded to deterministic synthetic DGT route rows.",
            "CGA route-patch authority is pointer-only and not copied into the DGT owner.",
            "Invalid or unsafe routes are blocked evidence, not admitted ledger rows.",
        ],
        "revocation_rows": [
            {
                "condition": "Revoke if an invalid or unsafe route appears in admission_ledger.rows.",
                "gate": "DGT-TOOL-HG3",
            },
            {
                "condition": "Revoke if the CGA route-patch pointer is replaced by copied route-patch payload.",
                "gate": "DGT-TOOL-HG2",
            },
        ],
        "forbidden_alias_audit": {
            "status": "pass",
            "forbidden_refs": [],
            "checked_ref_classes": ["host-private refs", "terminal verdict refs", "DGT alias refs", "standalone tool route refs"],
        },
    }
    del generated_at
    payload["hardgate"] = evaluate_dgt_tool_route_hardgates(payload)
    payload["failed_gate"] = payload["hardgate"]["failed_gate"]
    validate_dgt_tool_route_evidence(payload)
    return payload


def validate_dgt_tool_route_evidence(payload: Mapping[str, Any]) -> None:
    if set(payload) != set(TOOL_ROUTE_REQUIRED_KEYS):
        raise ValueError("DGT tool-route evidence fields mismatch")
    if payload["schema_id"] != TOOL_ROUTE_SCHEMA_ID or payload["artifact_id"] != TOOL_ROUTE_ARTIFACT_ID:
        raise ValueError("DGT tool-route identity mismatch")
    if payload["owner_ref"] != TOOL_ROUTE_OWNER_REF:
        raise ValueError("DGT tool-route owner pointer mismatch")
    rows = payload["synthetic_tool_call_grid"]
    if not isinstance(rows, list) or not rows:
        raise ValueError("DGT tool-route grid must be non-empty")
    route_ids = [row.get("route_id") for row in rows if isinstance(row, Mapping)]
    if len(route_ids) != len(set(route_ids)) or len(route_ids) != len(rows):
        raise ValueError("DGT tool-route ids must be unique")
    for row in rows:
        if not isinstance(row, Mapping):
            raise ValueError("DGT tool-route grid row must be an object")
        expected_row = {"route_id", "tool", "route_class", "classifier_surface_delta", "net_positive_signal", "admission_decision"}
        if set(row) != expected_row:
            raise ValueError("DGT tool-route grid row schema mismatch")
    hardgate = evaluate_dgt_tool_route_hardgates(payload)
    if payload["hardgate"] != hardgate:
        raise ValueError("DGT tool-route hardgate mismatch")
    if payload["failed_gate"] != hardgate["failed_gate"]:
        raise ValueError("DGT tool-route failed_gate mismatch")
    if hardgate["status"] != "pass":
        raise ValueError("DGT tool-route hardgate failed")


def _gate_rows(component_refs: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    pointer_cells = {
        "DGT-HG1": _cell(CANONICAL_JSON_ARTIFACT, "$.schema_id"),
        "DGT-HG2": _cell(CANONICAL_JSON_ARTIFACT, "$.artifact_id"),
        "DGT-HG3": _cell(CANONICAL_JSON_ARTIFACT, "$.model_id"),
        "DGT-HG4": _cell(CANONICAL_JSON_ARTIFACT, "$.architecture_spec"),
        "DGT-HG5": _cell(CANONICAL_JSON_ARTIFACT, "$.component_refs.hardgate_contract"),
        "DGT-HG6": _cell(CANONICAL_JSON_ARTIFACT, "$.component_refs.discovery_gated_nas"),
        "DGT-HG7": _cell(CANONICAL_JSON_ARTIFACT, "$.component_refs.discovery_map"),
        "DGT-HG8": _cell(CANONICAL_JSON_ARTIFACT, "$.component_refs.training_replay"),
        "DGT-HG9": _cell(CANONICAL_JSON_ARTIFACT, "$.discovery_map_signal"),
        "DGT-HG10": _cell(CANONICAL_JSON_ARTIFACT, "$.claim_capsule_ref"),
        "DGT-HG11": _cell(CANONICAL_JSON_ARTIFACT, "$.evidence_envelope_ref"),
        "DGT-HG12": _cell(CANONICAL_JSON_ARTIFACT, "$.mechanism_namecert_ref"),
        "DGT-HG13": _cell(CANONICAL_JSON_ARTIFACT, "$.jet_certificate_ref"),
        "DGT-HG14": _cell(CANONICAL_JSON_ARTIFACT, "$.not_claimed"),
        "DGT-HG15": _cell(CLAIM_CAPSULE_ARTIFACT, "$.owner_ref"),
        "DGT-HG16": _cell(EVIDENCE_ENVELOPE_ARTIFACT, "$.component_refs"),
        "DGT-HG17": _cell(MECHANISM_NAMECERT_ARTIFACT, "$.evidence_ref"),
        "DGT-HG18": _cell(JET_CERTIFICATE_ARTIFACT, "$.mechanism_ref"),
        "DGT-HG19": _cell("reports/canonical/discovery-gated-nas.json", "$.candidate_protocol.design_search_certificate"),
        "DGT-HG20": _cell(CANONICAL_JSON_ARTIFACT, "$.not_claimed"),
    }
    missing = not all(_is_cell(component_refs.get(name)) for name in default_component_refs())
    return {
        gate_name: {
            "status": "fail" if missing else "pass",
            "evidence": pointer_cells[gate_name],
            "not_claimed": _cell(CANONICAL_JSON_ARTIFACT, "$.not_claimed"),
        }
        for gate_name in GATE_NAMES
    }


class DiscoveryGatedTransformerProjector:
    def __init__(self, *, component_refs: Mapping[str, Any] | None = None) -> None:
        self.component_refs = dict(component_refs) if component_refs is not None else default_component_refs()

    def project(self, *, generated_at: str) -> dict[str, Any]:
        payload = {
            "schema_id": SCHEMA_ID,
            "artifact_id": ARTIFACT_ID,
            "generated_at": generated_at,
            "producer": PRODUCER,
            "projector": PROJECTOR,
            "model_id": MODEL_ID,
            "source_artifacts": {"component_refs": _cell(CANONICAL_JSON_ARTIFACT, "$.component_refs")},
            "component_refs": self.component_refs,
            "architecture_spec": default_architecture_spec(),
            "hardgate": {"status": "pass", "gate_names": list(GATE_NAMES), "gates": _gate_rows(self.component_refs)},
            "tool_route_evidence": build_dgt_tool_route_evidence(generated_at=generated_at),
            "family_definition": build_dgt_family_definition(),
            "discovery_map_signal": default_discovery_map_signal(),
            **sidecar_refs(),
            "not_claimed": list(NOT_CLAIMED),
        }
        if any(row["status"] != "pass" for row in payload["hardgate"]["gates"].values()):
            payload["hardgate"]["status"] = "fail"
        validate_projection(payload)
        return payload


def validate_projection(payload: Mapping[str, Any]) -> None:
    expected = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "projector",
        "model_id",
        "source_artifacts",
        "component_refs",
        "architecture_spec",
        "hardgate",
        "tool_route_evidence",
        "family_definition",
        "discovery_map_signal",
        "claim_capsule_ref",
        "evidence_envelope_ref",
        "mechanism_namecert_ref",
        "jet_certificate_ref",
        "not_claimed",
    }
    if set(payload) != expected:
        raise ValueError("DGT projection top-level fields mismatch")
    if payload["schema_id"] != SCHEMA_ID or payload["artifact_id"] != ARTIFACT_ID:
        raise ValueError("DGT projection identity mismatch")
    if payload["model_id"] != MODEL_ID:
        raise ValueError("DGT model identity mismatch")
    validate_dgt_tool_route_evidence(payload["tool_route_evidence"])
    validate_dgt_family_definition(payload["family_definition"])
    found = _has_recursive_key(payload, REJECTED_INLINE_KEYS)
    if found is not None:
        raise ValueError(f"DGT projection contains inline source body key: {found}")
    token = _has_recursive_token(payload, (".refactor-loop", "host.env", "terminal_verdict", "tool-use-dgt", "tool-use-toy-dgt"))
    if token is not None:
        raise ValueError(f"DGT projection contains forbidden value: {token}")
    for key in ("claim_capsule_ref", "evidence_envelope_ref", "mechanism_namecert_ref", "jet_certificate_ref"):
        if not _is_cell(payload[key]):
            raise ValueError(f"DGT sidecar ref is not a pointer cell: {key}")
    if not isinstance(payload["component_refs"], Mapping) or not _walk_cells(payload["component_refs"]):
        raise ValueError("DGT component refs must be pointer-only")
    hardgate = payload["hardgate"]
    if not isinstance(hardgate, Mapping) or hardgate.get("gate_names") != list(GATE_NAMES):
        raise ValueError("DGT hardgate names mismatch")
    gates = hardgate.get("gates")
    if not isinstance(gates, Mapping) or set(gates) != set(GATE_NAMES):
        raise ValueError("DGT hardgate rows mismatch")
    if hardgate.get("status") != ("pass" if all(row.get("status") == "pass" for row in gates.values()) else "fail"):
        raise ValueError("DGT hardgate status mismatch")
    for gate_name, row in gates.items():
        if not isinstance(row, Mapping) or set(row) != {"status", "evidence", "not_claimed"}:
            raise ValueError(f"DGT hardgate row schema mismatch: {gate_name}")
        if row["status"] not in {"pass", "fail"}:
            raise ValueError(f"DGT hardgate row status mismatch: {gate_name}")
        if not _is_cell(row["evidence"]) or not _is_cell(row["not_claimed"]):
            raise ValueError(f"DGT hardgate row must use pointer cells: {gate_name}")
    serialized = json.dumps(payload, sort_keys=True).lower()
    for denied in ("global superiority", "production authority"):
        if denied not in serialized:
            raise ValueError(f"DGT nonclaim boundary missing: {denied}")


def build_projection(*, generated_at: str, component_refs: Mapping[str, Any] | None = None) -> dict[str, Any]:
    return DiscoveryGatedTransformerProjector(component_refs=component_refs).project(generated_at=generated_at)


def render_markdown(payload: Mapping[str, Any]) -> str:
    validate_projection(payload)
    lines = [
        "# Discovery-Gated Transformer",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Schema: `{payload['schema_id']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Model: `{payload['model_id']}`",
        f"- Hardgate: `{payload['hardgate']['status']}`",
        "",
        "## Component Refs",
        "",
        "| component | artifact | pointer |",
        "| --- | --- | --- |",
    ]
    for name, cell in payload["component_refs"].items():
        lines.append(f"| `{name}` | `{cell['artifact']}` | `{cell['pointer']}` |")
    lines.extend(["", "## Hardgates", "", "| gate | status | evidence |", "| --- | --- | --- |"])
    for gate_name, row in payload["hardgate"]["gates"].items():
        lines.append(f"| `{gate_name}` | `{row['status']}` | `{artifact_pointer(row['evidence'])}` |")
    tool_route = payload["tool_route_evidence"]
    lines.extend(
        [
            "",
            "## Tool Route Evidence",
            "",
            f"- Schema: `{tool_route['schema_id']}`",
            f"- Owner: `{tool_route['owner_ref']}`",
            f"- CGA route patch: `{tool_route['cga_route_patch_ref']}`",
            f"- Hardgate: `{tool_route['hardgate']['status']}`",
            "",
            "| route | class | decision |",
            "| --- | --- | --- |",
        ]
    )
    for row in tool_route["synthetic_tool_call_grid"]:
        lines.append(f"| `{row['route_id']}` | `{row['route_class']}` | `{row['admission_decision']}` |")
    family_definition = payload["family_definition"]
    lines.extend(
        [
            "",
            "## Family Definition",
            "",
            f"- Schema: `{family_definition['schema_id']}`",
            f"- Owner: `{family_definition['owner_ref']}`",
            f"- Hardgate: `{family_definition['hardgate']['status']}`",
            f"- Claim status: `{family_definition['model_family_claim_status']['status']}`",
            "",
            "| group | pointers |",
            "| --- | --- |",
        ]
    )
    for group_name, group in family_definition["invariant_groups"].items():
        lines.append(f"| `{group_name}` | `{len(group['evidence_pointers'])}` |")
    lines.extend(
        [
            "",
            "## Sidecars",
            "",
            f"- Claim capsule: `{artifact_pointer(payload['claim_capsule_ref'])}`",
            f"- Evidence envelope: `{artifact_pointer(payload['evidence_envelope_ref'])}`",
            f"- Mechanism NameCert: `{artifact_pointer(payload['mechanism_namecert_ref'])}`",
            f"- Jet certificate: `{artifact_pointer(payload['jet_certificate_ref'])}`",
            "",
        ]
    )
    return "\n".join(lines)

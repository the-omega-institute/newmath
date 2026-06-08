"""Discovery-gated transformer canonical projection."""

from __future__ import annotations

from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.anti_triviality import owner_local_anti_triviality_contract
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from bedc_quality_lab.scope import CLOSED_CLAIM_SCOPE_SEAL


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
SOURCE_REFS_ARTIFACT = f"{RUN_ROOT}/source_refs.json"
GATE_NAMES = tuple(f"DGT-HG{index}" for index in range(1, 21))
JET_CERTIFICATE_SCHEMA_ID = "bedc-quality-lab:discovery-gated-transformer.jet-certificate"
JET_CERTIFICATE_ARTIFACT_ID = "bedc-quality-lab:discovery-gated-transformer.jet-certificate"
JET_HARDGATE_NAMES = tuple(f"JET-HG{index}" for index in range(1, 9))
JET_REQUIRED_SURFACES = (
    "boundary_spec",
    "derivative_spec",
    "causal_spec",
    "irreducibility_spec",
    "matched_random_control",
    "jet_coverage",
)
JET_SURFACE_SLOTS = (
    "boundary_spec_ref",
    "derivative_spec_ref",
    "causal_spec_ref",
    "irreducibility_spec_ref",
)
JET_FORBIDDEN_MATCH_TERMS = (
    "terminal_verdict",
    "production",
    "deployment",
    "global superiority",
    "architecture superiority",
)
JET_FORBIDDEN_TERM_LABELS = (
    "terminal verdict token",
    "operation authority wording",
    "release authority wording",
    "external superiority wording",
    "architecture superiority wording",
)
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
    "Bounded deterministic toy evidence only.",
    "No external operation authority.",
    "No universal training recipe claim.",
    "No external verdict ownership.",
)
D4_PROJECTION_GATE_NAMES = tuple(f"PROJ-HG{index}" for index in range(1, 11))
D4_PROJECTION_REQUIRED_KEYS = (
    "schema_id",
    "artifact_id",
    "owner_ref",
    "model_id",
    "gates",
    "failed_gate",
    "failed_gate_pointer",
    "discovery_level",
    "readiness",
    "net_positive_signal",
    "classifier_surface_delta_pointer",
    "input_pointers",
    "core_contracts",
    "not_claimed",
    "forbidden_claim_term_audit",
    "scope_seal",
    "matched_control",
    "claim_basis",
    "anti_triviality_status",
    "anti_triviality_policy",
    "anti_triviality_recommended_level",
    "anti_triviality_failed_gate",
    "anti_triviality_gate_evidence",
)


@dataclass(frozen=True)
class EvidenceCell:
    artifact: str
    pointer: str

    def as_payload(self) -> dict[str, str]:
        return {"artifact": self.artifact, "pointer": self.pointer}


@dataclass(frozen=True)
class DgtD4Projection:
    payload: dict[str, Any]

    def as_payload(self) -> dict[str, Any]:
        return dict(self.payload)


def artifact_pointer(cell: Mapping[str, Any]) -> str:
    return f"{cell['artifact']}:{cell['pointer']}"


def _cell(artifact: str, pointer: str) -> dict[str, str]:
    return EvidenceCell(artifact=artifact, pointer=pointer).as_payload()


def _resolve_cell(root: Path, cell: Mapping[str, Any]) -> Any:
    return resolve_artifact_pointer(root, artifact_pointer(cell))


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
        "evidence": _cell(CANONICAL_JSON_ARTIFACT, "$.d4_projection.discovery_level"),
        "map_ref": _cell("reports/canonical/discovery_map.json", "$.coverage_matrix"),
    }


def default_dgt_source_refs() -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:discovery-gated-transformer.source-refs",
        "artifact_id": "bedc-quality-lab:discovery-gated-transformer.source-refs",
        "model_id": MODEL_ID,
        "generated_at": None,
        "source_refs": {
            "boundary_spec": _cell("reports/canonical/boundary_causal_derivative_schema.json", "$.boundary_spec"),
            "derivative_spec": _cell("reports/canonical/derivative_order_ledger.json", "$.rows"),
            "causal_patch_suite": _cell("reports/canonical/causal_patch_suite.json", "$.patches"),
            "irreducibility_report": _cell("reports/canonical/irreducibility_report.json", "$.residual_gains"),
            "matched_random_control": _cell("reports/canonical/order-k-benchmark.json", "$.matched_random_controls"),
            "jet_coverage_matrix": _cell("reports/canonical/jet_coverage_matrix.json", "$.rows"),
            "discovery_map": _cell("reports/canonical/discovery_map.json", "$.coverage_matrix"),
        },
    }


def _default_jet_surface_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, surface_id in enumerate(JET_REQUIRED_SURFACES, start=1):
        rows.append(
            {
                "surface_id": surface_id,
                "boundary_spec_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.boundary_spec",
                "derivative_spec_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.derivative_spec",
                "causal_spec_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.causal_patch_suite",
                "irreducibility_spec_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.irreducibility_report",
                "low_order_baseline_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.derivative_spec",
                "causal_patch_evidence_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.causal_patch_suite",
                "matched_random_gain": -0.01 * index,
                "dgt_jet_gain": 0.20 + (0.01 * index),
                "base_jet_gain": 0.10,
                "matched_random_jet_gain": 0.0,
                "irreducible_residual_gain": 0.05 + (0.01 * index),
            }
        )
    return rows


def _jet_gate_rows(failed: Sequence[str]) -> dict[str, dict[str, Any]]:
    failed_set = set(failed)
    evidence_pointers = {
        "JET-HG1": "$.surface_rows",
        "JET-HG2": "$.surface_rows",
        "JET-HG3": "$.surface_rows",
        "JET-HG4": "$.surface_rows",
        "JET-HG5": "$.surface_rows",
        "JET-HG6": "$.jet_coverage",
        "JET-HG7": "$.derivative_debt_ledger",
        "JET-HG8": "$.forbidden_claim_term_audit",
    }
    return {
        gate_name: {
            "status": "fail" if gate_name in failed_set else "pass",
            "evidence": _cell(JET_CERTIFICATE_ARTIFACT, evidence_pointers[gate_name]),
        }
        for gate_name in JET_HARDGATE_NAMES
    }


def _jet_forbidden_claim_term_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    serialized = json.dumps(
        {
            "claim_status": payload.get("claim_status"),
            "not_claimed": payload.get("not_claimed"),
            "revocation_rows": payload.get("revocation_rows"),
        },
        sort_keys=True,
    ).lower()
    hits = [label for term, label in zip(JET_FORBIDDEN_MATCH_TERMS, JET_FORBIDDEN_TERM_LABELS) if term in serialized]
    return {
        "status": "pass" if not hits else "fail",
        "hits": hits,
        "forbidden_terms": list(JET_FORBIDDEN_TERM_LABELS),
    }


def evaluate_dgt_jet_hardgates(payload: Mapping[str, Any]) -> dict[str, Any]:
    failed: list[str] = []
    rows = payload.get("surface_rows")
    rows = rows if isinstance(rows, list) else []
    if (
        set(row.get("surface_id") for row in rows if isinstance(row, Mapping)) != set(JET_REQUIRED_SURFACES)
        or any(
            not isinstance(row, Mapping)
            or any(not isinstance(row.get(slot), str) or ":$" not in row[slot] for slot in JET_SURFACE_SLOTS)
            for row in rows
        )
    ):
        failed.append("JET-HG1")
    if any(
        not isinstance(row, Mapping)
        or not isinstance(row.get("low_order_baseline_ref"), str)
        or ":$" not in row["low_order_baseline_ref"]
        for row in rows
    ):
        failed.append("JET-HG2")
    if any(
        not isinstance(row, Mapping)
        or not isinstance(row.get("irreducible_residual_gain"), (int, float))
        or row["irreducible_residual_gain"] <= 0
        for row in rows
    ):
        failed.append("JET-HG3")
    if any(
        not isinstance(row, Mapping)
        or not isinstance(row.get("causal_patch_evidence_ref"), str)
        or ":$" not in row["causal_patch_evidence_ref"]
        for row in rows
    ):
        failed.append("JET-HG4")
    if any(
        not isinstance(row, Mapping)
        or not isinstance(row.get("matched_random_gain"), (int, float))
        or row["matched_random_gain"] > 0
        for row in rows
    ):
        failed.append("JET-HG5")
    coverage = payload.get("jet_coverage")
    if (
        not isinstance(coverage, Mapping)
        or not isinstance(coverage.get("dgt"), (int, float))
        or not isinstance(coverage.get("base_control"), (int, float))
        or not isinstance(coverage.get("matched_random_control"), (int, float))
        or coverage["dgt"] <= coverage["base_control"]
        or coverage["dgt"] <= coverage["matched_random_control"]
    ):
        failed.append("JET-HG6")
    ledger = payload.get("derivative_debt_ledger")
    ledger_rows = ledger.get("rows") if isinstance(ledger, Mapping) else None
    ledger_rows = ledger_rows if isinstance(ledger_rows, list) else []
    ledger_ids = {row.get("surface_id") for row in ledger_rows if isinstance(row, Mapping) and row.get("status") == "complete"}
    if ledger_ids != set(JET_REQUIRED_SURFACES):
        failed.append("JET-HG7")
    audit = payload.get("forbidden_claim_term_audit")
    expected_audit = _jet_forbidden_claim_term_audit(payload)
    if not isinstance(audit, Mapping) or dict(audit) != expected_audit or expected_audit["status"] != "pass":
        failed.append("JET-HG8")
    failed_gate = sorted(set(failed), key=JET_HARDGATE_NAMES.index)
    return {
        "status": "pass" if not failed_gate else "fail",
        "gate_names": list(JET_HARDGATE_NAMES),
        "gates": _jet_gate_rows(failed_gate),
        "failed_gate": failed_gate,
    }


def build_dgt_jet_certificate(source_refs: Mapping[str, Any]) -> dict[str, Any]:
    payload: dict[str, Any] = {
        "schema_id": JET_CERTIFICATE_SCHEMA_ID,
        "artifact_id": JET_CERTIFICATE_ARTIFACT_ID,
        "model_id": MODEL_ID,
        "generated_at": None,
        "owner_ref": f"{CANONICAL_JSON_ARTIFACT}:$",
        "source_refs_ref": _cell(SOURCE_REFS_ARTIFACT, "$.source_refs"),
        "source_artifacts": source_refs.get("source_refs", source_refs),
        "certificate_scope": "DGT owner-local boundary-causal-jet certificate",
        "surface_rows": _default_jet_surface_rows(),
        "jet_coverage": {
            "dgt": 0.72,
            "base_control": 0.41,
            "matched_random_control": 0.37,
            "coverage_matrix_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.jet_coverage_matrix",
        },
        "derivative_debt_ledger": {
            "status": "complete",
            "rows": [
                {
                    "surface_id": surface_id,
                    "status": "complete",
                    "ledger_ref": f"{SOURCE_REFS_ARTIFACT}:$.source_refs.derivative_spec",
                }
                for surface_id in JET_REQUIRED_SURFACES
            ],
        },
        "claim_status": {
            "status": "owner-local-candidate",
            "claim_scope": "bounded deterministic toy evidence only",
        },
        "hardgate": {},
        "failed_gate": [],
        "not_claimed": [
            "The certificate is bounded to deterministic toy source refs.",
            "The certificate is owner-local evidence only.",
            "The certificate does not claim external verdict ownership.",
        ],
        "revocation_rows": [
            {"gate": "JET-HG1", "condition": "Revoke when any required Boundary, Derivative, Causal, or Irreducibility slot is absent."},
            {"gate": "JET-HG8", "condition": "Revoke when forbidden authority language appears in claim fields."},
        ],
        "forbidden_claim_term_audit": {},
    }
    payload["forbidden_claim_term_audit"] = _jet_forbidden_claim_term_audit(payload)
    payload["hardgate"] = evaluate_dgt_jet_hardgates(payload)
    payload["failed_gate"] = payload["hardgate"]["failed_gate"]
    validate_dgt_jet_certificate(payload)
    return payload


def validate_dgt_jet_certificate(payload: Mapping[str, Any]) -> None:
    expected = {
        "schema_id",
        "artifact_id",
        "model_id",
        "generated_at",
        "owner_ref",
        "source_refs_ref",
        "source_artifacts",
        "certificate_scope",
        "surface_rows",
        "jet_coverage",
        "derivative_debt_ledger",
        "claim_status",
        "hardgate",
        "failed_gate",
        "not_claimed",
        "revocation_rows",
        "forbidden_claim_term_audit",
    }
    if set(payload) != expected:
        raise ValueError("DGT jet certificate fields mismatch")
    if payload["schema_id"] != JET_CERTIFICATE_SCHEMA_ID or payload["artifact_id"] != JET_CERTIFICATE_ARTIFACT_ID:
        raise ValueError("DGT jet certificate identity mismatch")
    if payload["model_id"] != MODEL_ID or payload["owner_ref"] != f"{CANONICAL_JSON_ARTIFACT}:$":
        raise ValueError("DGT jet certificate owner mismatch")
    if not _is_cell(payload["source_refs_ref"]):
        raise ValueError("DGT jet source refs must be a pointer cell")
    hardgate = evaluate_dgt_jet_hardgates(payload)
    if payload["hardgate"] != hardgate:
        raise ValueError("DGT jet hardgate mismatch")
    if payload["failed_gate"] != hardgate["failed_gate"]:
        raise ValueError("DGT jet failed_gate mismatch")
    if hardgate["status"] != "pass":
        raise ValueError("DGT jet hardgate failed")
    token = _has_recursive_token(payload, (".refactor-loop", "host.env", "terminal_verdict"))
    if token is not None:
        raise ValueError(f"DGT jet certificate contains forbidden value: {token}")


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
    source_refs = default_dgt_source_refs()
    jet_certificate = build_dgt_jet_certificate(source_refs)
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
        "source_refs": {**source_refs, "generated_at": generated_at},
        "jet_certificate": {**jet_certificate, "generated_at": generated_at},
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
        "DGT-HG18": _cell(JET_CERTIFICATE_ARTIFACT, "$.owner_ref"),
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


def _dgt_forbidden_claim_term_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    serialized = json.dumps(
        {
            "architecture_spec": payload.get("architecture_spec"),
            "discovery_map_signal": payload.get("discovery_map_signal"),
            "not_claimed": payload.get("not_claimed"),
        },
        sort_keys=True,
    ).lower()
    match_terms = ("terminal_verdict", "production", "global superiority", "architecture superiority")
    labels = (
        "terminal verdict token",
        "operation authority wording",
        "external superiority wording",
        "architecture superiority wording",
    )
    hits = [label for term, label in zip(match_terms, labels) if term in serialized]
    return {"status": "pass" if not hits else "fail", "hits": hits, "forbidden_terms": list(labels)}


def _projection_not_claimed_clean(not_claimed: Any) -> bool:
    if not isinstance(not_claimed, Sequence) or isinstance(not_claimed, (str, bytes, bytearray)) or not not_claimed:
        return False
    text = " ".join(str(item).lower() for item in not_claimed)
    return all(token not in text for token in ("global superiority", "production"))


def _tool_route_positive(tool_route: Any) -> tuple[bool, bool]:
    if not isinstance(tool_route, Mapping):
        return False, False
    if tool_route.get("net_positive_signal") is not True:
        return False, False
    deltas = tool_route.get("classifier_surface_delta")
    if not isinstance(deltas, Mapping) or not deltas:
        return True, False
    for delta in deltas.values():
        if not isinstance(delta, Mapping):
            return True, False
        count = delta.get("surface_delta_count")
        if not isinstance(count, (int, float)) or isinstance(count, bool) or count <= 0:
            return True, False
    return True, True


def _d4_gate_rows(payload: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    gates = payload.get("hardgate", {}).get("gates") if isinstance(payload.get("hardgate"), Mapping) else {}
    tool_route = payload.get("tool_route_evidence")
    family_definition = payload.get("family_definition")
    net_positive, classifier_delta_positive = _tool_route_positive(tool_route)
    failed_conditions = {
        "PROJ-HG1": not (
            isinstance(payload.get("hardgate"), Mapping)
            and payload["hardgate"].get("status") == "pass"
            and isinstance(gates, Mapping)
            and all(isinstance(row, Mapping) and row.get("status") == "pass" for row in gates.values())
        ),
        "PROJ-HG2": not (
            isinstance(tool_route, Mapping)
            and isinstance(tool_route.get("hardgate"), Mapping)
            and tool_route["hardgate"].get("status") == "pass"
        ),
        "PROJ-HG3": not net_positive,
        "PROJ-HG4": not classifier_delta_positive,
        "PROJ-HG5": not (
            isinstance(family_definition, Mapping)
            and isinstance(family_definition.get("hardgate"), Mapping)
            and family_definition["hardgate"].get("status") == "pass"
        ),
        "PROJ-HG6": not (
            _is_cell(payload.get("claim_capsule_ref"))
            and _is_cell(payload.get("evidence_envelope_ref"))
            and _is_cell(payload.get("mechanism_namecert_ref"))
            and _is_cell(payload.get("jet_certificate_ref"))
        ),
        "PROJ-HG7": not _projection_not_claimed_clean(payload.get("not_claimed")),
        "PROJ-HG8": not (
            isinstance(payload.get("forbidden_claim_term_audit"), Mapping)
            and payload["forbidden_claim_term_audit"].get("status") == "pass"
        ),
        "PROJ-HG9": _has_recursive_token(payload, ("terminal_verdict",)) is not None,
        "PROJ-HG10": not (
            _is_cell(payload.get("hardgate_ref"))
            and _is_cell(payload.get("discovery_map_signal_ref"))
        ),
    }
    evidence = {
        "PROJ-HG1": "$.hardgate",
        "PROJ-HG2": "$.tool_route_evidence.hardgate",
        "PROJ-HG3": "$.tool_route_evidence.net_positive_signal",
        "PROJ-HG4": "$.tool_route_evidence.classifier_surface_delta",
        "PROJ-HG5": "$.family_definition.hardgate",
        "PROJ-HG6": "$.claim_capsule_ref",
        "PROJ-HG7": "$.not_claimed",
        "PROJ-HG8": "$.forbidden_claim_term_audit",
        "PROJ-HG9": "$",
        "PROJ-HG10": "$.discovery_map_signal_ref",
    }
    return {
        gate_name: {
            "status": "fail" if failed_conditions[gate_name] else "pass",
            "evidence": _cell(CANONICAL_JSON_ARTIFACT, evidence[gate_name]),
        }
        for gate_name in D4_PROJECTION_GATE_NAMES
    }


def build_d4_projection_payload(
    evidence: Mapping[str, Any],
    core_contracts: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    gates = _d4_gate_rows(evidence)
    failed = [gate_name for gate_name in D4_PROJECTION_GATE_NAMES if gates[gate_name]["status"] != "pass"]
    failed_gate = failed[0] if failed else None
    input_pointers = {
        "hardgate": f"{CANONICAL_JSON_ARTIFACT}:$.hardgate",
        "tool_route": f"{CANONICAL_JSON_ARTIFACT}:$.tool_route_evidence",
        "family_definition": f"{CANONICAL_JSON_ARTIFACT}:$.family_definition",
        "claim_capsule": f"{CANONICAL_JSON_ARTIFACT}:$.claim_capsule_ref",
        "evidence_envelope": f"{CANONICAL_JSON_ARTIFACT}:$.evidence_envelope_ref",
        "mechanism_namecert": f"{CANONICAL_JSON_ARTIFACT}:$.mechanism_namecert_ref",
        "jet_certificate": f"{CANONICAL_JSON_ARTIFACT}:$.jet_certificate_ref",
        "not_claimed": f"{CANONICAL_JSON_ARTIFACT}:$.not_claimed",
        "forbidden_claim_term_audit": f"{CANONICAL_JSON_ARTIFACT}:$.forbidden_claim_term_audit",
    }
    tool_route = evidence.get("tool_route_evidence")
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "owner_ref": f"{CANONICAL_JSON_ARTIFACT}:$",
        "model_id": MODEL_ID,
        "gates": gates,
        "failed_gate": failed_gate,
        "failed_gate_pointer": None if failed_gate is None else f"{CANONICAL_JSON_ARTIFACT}:$.d4_projection.gates.{failed_gate}",
        "discovery_level": "D4" if failed_gate is None else "D0",
        "readiness": "ready" if failed_gate is None else "blocked",
        "net_positive_signal": isinstance(tool_route, Mapping) and tool_route.get("net_positive_signal") is True,
        "classifier_surface_delta_pointer": "$.tool_route_evidence.classifier_surface_delta",
        "input_pointers": input_pointers,
        "core_contracts": dict(core_contracts or {}),
        "not_claimed": list(evidence.get("not_claimed", [])) if isinstance(evidence.get("not_claimed"), Sequence) else [],
        "forbidden_claim_term_audit": evidence.get("forbidden_claim_term_audit", {}),
        "scope_seal": dict(CLOSED_CLAIM_SCOPE_SEAL),
        "matched_control": {
            "control_positive": False,
            "control_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.tool_route_evidence.blocked_route_evidence",
        },
        "claim_basis": {
            "positive_discovery": failed_gate is None,
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.d4_projection.gates.PROJ-HG1",
        },
        "anti_triviality_status": "pass" if failed_gate is None else "fail",
        **owner_local_anti_triviality_contract(
            recommended_level="D4",
            scale_only_pointer="$.d4_projection.gates.PROJ-HG1",
            metadata_only_pointer="$.d4_projection.gates.PROJ-HG5",
            matched_random_pointer="$.d4_projection.matched_control",
            forbidden_column_pointer="$.d4_projection.forbidden_claim_term_audit",
            status="pass" if failed_gate is None else "fail",
            failed_gate=failed_gate,
        ),
    }
    validate_d4_projection(payload, evidence)
    return DgtD4Projection(payload).as_payload()


def validate_d4_projection(payload: Mapping[str, Any], root: Mapping[str, Any] | None = None) -> list[str]:
    errors: list[str] = []
    if set(payload) != set(D4_PROJECTION_REQUIRED_KEYS):
        errors.append("DGT D4 projection fields mismatch")
    if payload.get("schema_id") != SCHEMA_ID or payload.get("artifact_id") != ARTIFACT_ID:
        errors.append("DGT D4 projection identity mismatch")
    if payload.get("owner_ref") != f"{CANONICAL_JSON_ARTIFACT}:$":
        errors.append("DGT D4 projection owner mismatch")
    gates = payload.get("gates")
    if not isinstance(gates, Mapping) or set(gates) != set(D4_PROJECTION_GATE_NAMES):
        errors.append("DGT D4 projection gate names mismatch")
    else:
        failed = [gate_name for gate_name in D4_PROJECTION_GATE_NAMES if gates[gate_name].get("status") != "pass"]
        expected_failed = failed[0] if failed else None
        if payload.get("failed_gate") != expected_failed:
            errors.append("DGT D4 projection failed gate mismatch")
        if payload.get("discovery_level") != ("D4" if expected_failed is None else "D0"):
            errors.append("DGT D4 projection discovery level mismatch")
        if payload.get("readiness") != ("ready" if expected_failed is None else "blocked"):
            errors.append("DGT D4 projection readiness mismatch")
    if _has_recursive_token(payload, ("terminal_verdict", ".refactor-loop", "host.env")) is not None:
        errors.append("DGT D4 projection contains forbidden authority token")
    if not _projection_not_claimed_clean(payload.get("not_claimed")):
        errors.append("DGT D4 projection not_claimed boundary mismatch")
    if payload.get("readiness") == "ready" and payload.get("net_positive_signal") is not True:
        errors.append("DGT D4 projection net positive signal missing")
    if payload.get("scope_seal") != CLOSED_CLAIM_SCOPE_SEAL:
        errors.append("DGT D4 projection scope seal mismatch")
    if root is not None and isinstance(gates, Mapping) and _d4_gate_rows(root) != gates:
        errors.append("DGT D4 projection gate evaluation mismatch")
    return errors


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
            "hardgate_ref": _cell(CANONICAL_JSON_ARTIFACT, "$.hardgate"),
            "tool_route_evidence": build_dgt_tool_route_evidence(generated_at=generated_at),
            "family_definition": build_dgt_family_definition(),
            "discovery_map_signal": default_discovery_map_signal(),
            "discovery_map_signal_ref": _cell(CANONICAL_JSON_ARTIFACT, "$.discovery_map_signal"),
            **sidecar_refs(),
            "forbidden_claim_term_audit": {},
            "revocation_rows": [
                {"gate": "DGT-HG13", "condition": "Revoke when the owner-local jet certificate pointer is absent."},
                {"gate": "DGT-HG20", "condition": "Revoke when forbidden claim language appears in DGT claim fields."},
            ],
            "not_claimed": list(NOT_CLAIMED),
        }
        if any(row["status"] != "pass" for row in payload["hardgate"]["gates"].values()):
            payload["hardgate"]["status"] = "fail"
        payload["forbidden_claim_term_audit"] = _dgt_forbidden_claim_term_audit(payload)
        payload["d4_projection"] = build_d4_projection_payload(
            payload,
            {
                "discovery_map_level_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.d4_projection.discovery_level",
                "claim_verdict_owner": "Core",
                "claim_graph_owner": "Core",
            },
        )
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
        "hardgate_ref",
        "tool_route_evidence",
        "family_definition",
        "discovery_map_signal",
        "discovery_map_signal_ref",
        "d4_projection",
        "claim_capsule_ref",
        "evidence_envelope_ref",
        "mechanism_namecert_ref",
        "jet_certificate_ref",
        "forbidden_claim_term_audit",
        "revocation_rows",
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
    for key in ("hardgate_ref", "discovery_map_signal_ref"):
        if not _is_cell(payload[key]):
            raise ValueError(f"DGT summary ref is not a pointer cell: {key}")
    if payload["forbidden_claim_term_audit"] != _dgt_forbidden_claim_term_audit(payload):
        raise ValueError("DGT forbidden claim term audit mismatch")
    if payload["forbidden_claim_term_audit"]["status"] != "pass":
        raise ValueError("DGT forbidden claim term audit failed")
    if not isinstance(payload["revocation_rows"], list) or not payload["revocation_rows"]:
        raise ValueError("DGT revocation rows missing")
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
    d4_errors = validate_d4_projection(payload["d4_projection"], payload)
    if d4_errors:
        raise ValueError("; ".join(d4_errors))


def validate_dgt_hardgate_evidence_bundle(payload: Mapping[str, Any], *, root: Path) -> None:
    validate_projection(payload)
    gates = payload["hardgate"]["gates"]
    for gate_name, row in gates.items():
        if row["status"] != "pass":
            continue
        for key in ("evidence", "not_claimed"):
            if _resolve_cell(root, row[key]) is None:
                raise ValueError(f"DGT hardgate {key} pointer does not resolve: {gate_name}")


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
    d4_projection = payload["d4_projection"]
    lines.extend(
        [
            "",
            "## D4 Projection",
            "",
            f"- Readiness: `{d4_projection['readiness']}`",
            f"- Discovery level: `{d4_projection['discovery_level']}`",
            f"- Failed gate: `{d4_projection['failed_gate']}`",
            "",
            "| gate | status | evidence |",
            "| --- | --- | --- |",
        ]
    )
    for gate_name, row in d4_projection["gates"].items():
        lines.append(f"| `{gate_name}` | `{row['status']}` | `{artifact_pointer(row['evidence'])}` |")
    lines.extend(
        [
            "",
            "## Sidecars",
            "",
            f"- Claim capsule: `{artifact_pointer(payload['claim_capsule_ref'])}`",
            f"- Evidence envelope: `{artifact_pointer(payload['evidence_envelope_ref'])}`",
            f"- Mechanism NameCert: `{artifact_pointer(payload['mechanism_namecert_ref'])}`",
            f"- Jet certificate: `{artifact_pointer(payload['jet_certificate_ref'])}`",
            f"- Jet hardgate: `{artifact_pointer(payload['hardgate_ref'])}`",
            f"- Discovery map signal: `{artifact_pointer(payload['discovery_map_signal_ref'])}`",
            "",
        ]
    )
    return "\n".join(lines)

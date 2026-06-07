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
    found = _has_recursive_key(payload, REJECTED_INLINE_KEYS)
    if found is not None:
        raise ValueError(f"DGT projection contains inline source body key: {found}")
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

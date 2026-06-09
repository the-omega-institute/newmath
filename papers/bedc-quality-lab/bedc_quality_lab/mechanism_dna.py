"""Canonical pointer owner for mechanism DNA rows."""

from __future__ import annotations

from dataclasses import asdict, dataclass
import json
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.pointers import pointer_value


SCHEMA_ID = "bedc-quality-lab:mechanism-dna"
ARTIFACT_ID = "bedc-quality-lab:mechanism-dna"
JSON_ARTIFACT = "reports/canonical/mechanism_dna.json"
MARKDOWN_ARTIFACT = "reports/canonical/mechanism_dna.md"
DEFAULT_DETERMINISTIC_SEED = 935

REQUIRED_REF_FIELDS = (
    "component_ref",
    "causal_path_ref",
    "intervention_ref",
    "ablation_dependency_ref",
    "negative_witness_ref",
)
ROW_FIELDS = (
    "row_id",
    "mechanism_id",
    *REQUIRED_REF_FIELDS,
    "source_level_ref",
    "source_status_ref",
    "row_hardgate",
    "not_claimed",
)
FORBIDDEN_ALIAS_KEYS = frozenset(
    {
        "terminal_verdict",
        "final_verdict",
        "canonical_terminal_verdict",
        "core_verdict",
    }
)


@dataclass(frozen=True)
class MechanismDNARow:
    row_id: str
    mechanism_id: str
    component_ref: dict[str, str]
    causal_path_ref: dict[str, str]
    intervention_ref: dict[str, str]
    ablation_dependency_ref: dict[str, str]
    negative_witness_ref: dict[str, str]
    source_level_ref: dict[str, str]
    source_status_ref: dict[str, str]
    row_hardgate: dict[str, Any]
    not_claimed: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["not_claimed"] = list(self.not_claimed)
        return payload


@dataclass(frozen=True)
class MechanismDNACapsule:
    schema_id: str
    artifact_id: str
    generated_at: str
    deterministic_seed: int
    source_artifacts: dict[str, str]
    rows: tuple[MechanismDNARow, ...]
    hardgate: dict[str, Any]
    not_claimed: tuple[str, ...]
    forbidden_alias_audit: dict[str, Any]

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_id": self.schema_id,
            "artifact_id": self.artifact_id,
            "generated_at": self.generated_at,
            "deterministic_seed": self.deterministic_seed,
            "source_artifacts": dict(sorted(self.source_artifacts.items())),
            "rows": [row.to_dict() for row in self.rows],
            "hardgate": self.hardgate,
            "not_claimed": list(self.not_claimed),
            "forbidden_alias_audit": self.forbidden_alias_audit,
        }


@dataclass(frozen=True)
class _MechanismSource:
    report: str
    artifact: str
    mechanism_id: str
    component_pointer: str
    causal_path_pointer: str
    intervention_pointer: str
    ablation_dependency_pointer: str
    negative_witness_pointer: str
    source_level_pointer: str
    source_status_pointer: str
    not_claimed: tuple[str, ...]


MECHANISM_SOURCES: tuple[_MechanismSource, ...] = (
    _MechanismSource(
        report="gap-head-attribution-capsule",
        artifact="reports/canonical/gap_head_attribution_capsule.json",
        mechanism_id="gap-head-residualized-attribution",
        component_pointer="$.mechanism_case",
        causal_path_pointer="$.mechanism_evidence",
        intervention_pointer="$.head_channel_patch_evidence.causal_patch_claim",
        ablation_dependency_pointer="$.a4_hardgates.gates.head_causal_patch",
        negative_witness_pointer="$.negative_witness[0]",
        source_level_pointer="$.mechanism_evidence.mechanism_level",
        source_status_pointer="$.mechanism_evidence.mechanism_status",
        not_claimed=(
            "No D5-M promotion is made by this owner.",
            "No downstream evidence body is copied into the row.",
        ),
    ),
    _MechanismSource(
        report="discovery-regularized-training",
        artifact="reports/canonical/discovery-regularized-training.json",
        mechanism_id="training-mechanism-certificate",
        component_pointer="$.training_mechanism_cert",
        causal_path_pointer="$.training_loop_trace",
        intervention_pointer="$.torch_training_evidence",
        ablation_dependency_pointer="$.mechanism_ablation.status",
        negative_witness_pointer="$.negative_witness_mutations",
        source_level_pointer="$.discovery_map_signal.level_candidate",
        source_status_pointer="$.training_mechanism_cert.status",
        not_claimed=(
            "No training superiority claim is made here.",
            "No claim verdict is owned by this report.",
        ),
    ),
    _MechanismSource(
        report="mechanism-seeking-network",
        artifact="reports/canonical/mechanism-seeking-network.json",
        mechanism_id="distinction-module-mechanism",
        component_pointer="$.mechanism_gate_summary.by_mechanism",
        causal_path_pointer="$.distinction_module_evidence",
        intervention_pointer="$.distinction_module_evidence.records[0].patch_rows_pointer",
        ablation_dependency_pointer="$.distinction_module_evidence.records[0].ablation_rows_pointer",
        negative_witness_pointer="$.revocation_rows",
        source_level_pointer="$.discovery_map_signal.level_candidate",
        source_status_pointer="$.d5_m_readiness.status",
        not_claimed=(
            "No module is promoted by this owner alone.",
            "No raw module registry is copied into the row.",
        ),
    ),
    _MechanismSource(
        report="discovery-gated-transformer",
        artifact="reports/canonical/discovery-gated-transformer.json",
        mechanism_id="discovery-gated-transformer-namecert",
        component_pointer="$.component_refs",
        causal_path_pointer="$.mechanism_namecert_ref",
        intervention_pointer="$.tool_route_evidence",
        ablation_dependency_pointer="$.component_ablation",
        negative_witness_pointer="$.revocation_rows",
        source_level_pointer="$.d5_m_projection.discovery_level",
        source_status_pointer="$.d5_m_projection.status",
        not_claimed=(
            "No architecture superiority claim is made here.",
            "External mechanism certificate payloads stay behind pointers.",
        ),
    ),
)


def mechanism_dna_artifacts() -> tuple[str, ...]:
    return tuple(source.artifact for source in MECHANISM_SOURCES)


def mechanism_dna_row_pointer(report: str) -> str | None:
    for index, source in enumerate(MECHANISM_SOURCES):
        if source.report == report:
            return f"{JSON_ARTIFACT}:$.rows[{index}]"
    return None


def build_mechanism_dna(
    source_payloads: Mapping[str, Mapping[str, Any]],
    *,
    generated_at: str,
    deterministic_seed: int,
) -> dict[str, Any]:
    rows = tuple(_row_for_source(source, source_payloads) for source in MECHANISM_SOURCES)
    hardgate = _capsule_hardgate(rows)
    capsule = MechanismDNACapsule(
        schema_id=SCHEMA_ID,
        artifact_id=ARTIFACT_ID,
        generated_at=generated_at,
        deterministic_seed=deterministic_seed,
        source_artifacts={source.report: source.artifact for source in MECHANISM_SOURCES},
        rows=rows,
        hardgate=hardgate,
        not_claimed=(
            "MechanismDNA owns only canonical mechanism vocabulary and pointer gates.",
            "Terminal claim decisions remain outside this artifact.",
            "Downstream mechanism evidence payloads remain in their source artifacts.",
        ),
        forbidden_alias_audit={"status": "pass", "scanned_key_count": 0, "forbidden_key_count": 0},
    )
    payload = capsule.to_dict()
    return _with_forbidden_alias_audit(payload)


def audit_mechanism_dna(
    payload: Mapping[str, Any],
    source_payloads: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    failures: list[str] = []
    if payload.get("schema_id") != SCHEMA_ID:
        failures.append("schema-id")
    if payload.get("artifact_id") != ARTIFACT_ID:
        failures.append("artifact-id")
    rows = payload.get("rows")
    if not isinstance(rows, list) or len(rows) != len(MECHANISM_SOURCES):
        failures.append("rows")
        rows = []
    for index, source in enumerate(MECHANISM_SOURCES):
        row = rows[index] if index < len(rows) and isinstance(rows[index], Mapping) else {}
        failures.extend(_audit_row_payload(row, source, source_payloads, index))
    hardgate = payload.get("hardgate")
    if not isinstance(hardgate, Mapping) or hardgate.get("status") not in {"pass", "fail-closed"}:
        failures.append("hardgate")
    alias_audit = _forbidden_alias_audit(payload)
    if alias_audit["status"] != "pass":
        failures.append("forbidden-alias")
    return {
        "status": "pass" if not failures else "fail",
        "failed_gates": sorted(set(failures)),
        "row_count": len(rows),
    }


def render_mechanism_dna_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Mechanism DNA",
        "",
        f"- Schema: `{payload.get('schema_id', '')}`",
        f"- Artifact: `{payload.get('artifact_id', '')}`",
        f"- Hardgate: `{pointer_value(payload, '$.hardgate.status') or ''}`",
        "",
        "| row | mechanism | component | causal path | intervention | ablation | negative witness | status |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    rows = payload.get("rows")
    if isinstance(rows, list):
        for row in rows:
            if not isinstance(row, Mapping):
                continue
            lines.append(
                " | ".join(
                    [
                        f"`{row.get('row_id', '')}`",
                        f"`{row.get('mechanism_id', '')}`",
                        f"`{_owner_pointer(row.get('component_ref'))}`",
                        f"`{_owner_pointer(row.get('causal_path_ref'))}`",
                        f"`{_owner_pointer(row.get('intervention_ref'))}`",
                        f"`{_owner_pointer(row.get('ablation_dependency_ref'))}`",
                        f"`{_owner_pointer(row.get('negative_witness_ref'))}`",
                        f"`{pointer_value(row, '$.row_hardgate.status') or ''}`",
                    ]
                )
            )
    lines.extend(
        [
            "",
            "## Not Claimed",
            "",
        ]
    )
    not_claimed = payload.get("not_claimed")
    if isinstance(not_claimed, list):
        lines.extend(f"- {item}" for item in not_claimed if isinstance(item, str))
    return "\n".join(lines) + "\n"


def _row_for_source(
    source: _MechanismSource,
    source_payloads: Mapping[str, Mapping[str, Any]],
) -> MechanismDNARow:
    refs = {
        "component_ref": _ref(source.artifact, source.component_pointer),
        "causal_path_ref": _ref(source.artifact, source.causal_path_pointer),
        "intervention_ref": _ref(source.artifact, source.intervention_pointer),
        "ablation_dependency_ref": _ref(source.artifact, source.ablation_dependency_pointer),
        "negative_witness_ref": _ref(source.artifact, source.negative_witness_pointer),
    }
    source_level_ref = _ref(source.artifact, source.source_level_pointer)
    source_status_ref = _ref(source.artifact, source.source_status_pointer)
    row_hardgate = _row_hardgate(source, refs, source_level_ref, source_status_ref, source_payloads)
    return MechanismDNARow(
        row_id=source.report,
        mechanism_id=source.mechanism_id,
        component_ref=refs["component_ref"],
        causal_path_ref=refs["causal_path_ref"],
        intervention_ref=refs["intervention_ref"],
        ablation_dependency_ref=refs["ablation_dependency_ref"],
        negative_witness_ref=refs["negative_witness_ref"],
        source_level_ref=source_level_ref,
        source_status_ref=source_status_ref,
        row_hardgate=row_hardgate,
        not_claimed=source.not_claimed,
    )


def _ref(artifact: str, pointer: str) -> dict[str, str]:
    return {"artifact": artifact, "pointer": pointer, "owner_pointer": f"{artifact}:{pointer}"}


def _row_hardgate(
    source: _MechanismSource,
    refs: Mapping[str, Mapping[str, str]],
    source_level_ref: Mapping[str, str],
    source_status_ref: Mapping[str, str],
    source_payloads: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    gates: dict[str, dict[str, str]] = {}
    payload = source_payloads.get(source.artifact, {})
    for field, ref in [*refs.items(), ("source_level_ref", source_level_ref), ("source_status_ref", source_status_ref)]:
        resolves = _ref_resolves(ref, payload)
        gate_id = f"MDNA-{source.report}-{field}"
        gates[gate_id] = {
            "status": "pass" if resolves else "fail",
            "reason": "pointer resolves" if resolves else "pointer missing; fail closed",
            "owner_pointer": ref["owner_pointer"],
        }
    status = "pass" if all(gate["status"] == "pass" for gate in gates.values()) else "fail-closed"
    return {"status": status, "gates": gates}


def _capsule_hardgate(rows: Sequence[MechanismDNARow]) -> dict[str, Any]:
    gates = {
        "MDNA-HG1-row-schema": {
            "status": "pass" if all(tuple(row.to_dict()) == ROW_FIELDS for row in rows) else "fail",
            "reason": "rows expose only canonical pointer fields",
        },
        "MDNA-HG2-row-local-pointers": {
            "status": "pass" if all(row.row_hardgate.get("status") == "pass" for row in rows) else "fail",
            "reason": "all row-local pointer gates resolve",
        },
        "MDNA-HG3-no-terminal-surface": {
            "status": "pass",
            "reason": "mechanism owner does not expose decision fields",
        },
    }
    return {
        "status": "pass" if all(gate["status"] == "pass" for gate in gates.values()) else "fail-closed",
        "gates": gates,
    }


def _audit_row_payload(
    row: Mapping[str, Any],
    source: _MechanismSource,
    source_payloads: Mapping[str, Mapping[str, Any]],
    index: int,
) -> list[str]:
    failures: list[str] = []
    if tuple(row.keys()) != ROW_FIELDS:
        failures.append(f"row-{index}-schema")
    if row.get("row_id") != source.report:
        failures.append(f"row-{index}-id")
    if row.get("mechanism_id") != source.mechanism_id:
        failures.append(f"row-{index}-mechanism")
    payload = source_payloads.get(source.artifact, {})
    for field in (*REQUIRED_REF_FIELDS, "source_level_ref", "source_status_ref"):
        ref = row.get(field)
        if not _ref_resolves(ref, payload):
            failures.append(f"row-{index}-{field}")
    hardgate = row.get("row_hardgate")
    if not isinstance(hardgate, Mapping) or hardgate.get("status") != "pass":
        failures.append(f"row-{index}-hardgate")
    return failures


def _ref_resolves(ref: Any, payload: Mapping[str, Any]) -> bool:
    if not isinstance(ref, Mapping):
        return False
    artifact = ref.get("artifact")
    pointer = ref.get("pointer")
    owner_pointer = ref.get("owner_pointer")
    if not all(isinstance(value, str) and value for value in (artifact, pointer, owner_pointer)):
        return False
    if owner_pointer != f"{artifact}:{pointer}":
        return False
    return pointer_value(payload, pointer) is not None


def _owner_pointer(ref: Any) -> str:
    return str(ref.get("owner_pointer", "")) if isinstance(ref, Mapping) else ""


def _with_forbidden_alias_audit(payload: dict[str, Any]) -> dict[str, Any]:
    audit = _forbidden_alias_audit(payload)
    payload["forbidden_alias_audit"] = audit
    payload["hardgate"]["gates"]["MDNA-HG3-no-terminal-surface"]["status"] = "pass" if audit["status"] == "pass" else "fail"
    payload["hardgate"]["status"] = (
        "pass"
        if all(gate["status"] == "pass" for gate in payload["hardgate"]["gates"].values())
        else "fail-closed"
    )
    return payload


def _forbidden_alias_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    hits = _forbidden_alias_hits(payload)
    return {
        "status": "pass" if not hits else "fail",
        "scanned_key_count": _key_count(payload),
        "forbidden_key_count": len(hits),
    }


def _forbidden_alias_hits(payload: Any) -> list[str]:
    hits: list[str] = []
    if isinstance(payload, Mapping):
        for key, value in payload.items():
            if str(key) in FORBIDDEN_ALIAS_KEYS:
                hits.append(str(key))
            hits.extend(_forbidden_alias_hits(value))
    elif isinstance(payload, list):
        for value in payload:
            hits.extend(_forbidden_alias_hits(value))
    return hits


def _key_count(payload: Any) -> int:
    if isinstance(payload, Mapping):
        return len(payload) + sum(_key_count(value) for value in payload.values())
    if isinstance(payload, list):
        return sum(_key_count(value) for value in payload)
    return 0


def stable_json(payload: Mapping[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"

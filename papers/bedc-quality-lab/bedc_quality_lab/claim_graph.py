"""Pointer-only claim graph over canonical verdict artifacts."""

from __future__ import annotations

from dataclasses import asdict, dataclass
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.artifact_freshness import load_scorecard_snapshot
from bedc_quality_lab.claim_acceptance import validate_positive_claim_evidence
from bedc_quality_lab.high_impact_claim_review import high_impact_review_failure_pointer
from bedc_quality_lab.high_impact_review import high_impact_review_dgt_gate
from bedc_quality_lab.discovery_compiler.map import load_validated_discovery_map_payload
from bedc_quality_lab.discovery_compiler.pointers import normalize_artifact_pointer, pointer_value, resolve_artifact_pointer
from bedc_quality_lab.discovery_gated_transformer import validate_evidence_scope
from bedc_quality_lab.model_comparison import D5_M_SCOPE_POINTER, DGT_CONTROL_SEMANTIC_POINTER
from bedc_quality_lab.evidence_provenance import load_evidence_provenance, owner_discovery_row, owner_metric_rows


SCHEMA_ID = "bedc-quality-lab:claim-graph"
CLAIM_GRAPH_JSON_ARTIFACT = "reports/canonical/claim_graph.json"
CLAIM_GRAPH_MARKDOWN_ARTIFACT = "reports/canonical/claim_graph.md"
CLAIM_GRAPH_ARTIFACT_ID = "bedc-quality-lab:claim-graph"
CLAIM_VERDICTS_JSONL_ARTIFACT = "reports/canonical/claim_verdicts.jsonl"
DISCOVERY_MAP_JSON_ARTIFACT = "reports/canonical/discovery_map.json"
NEGATIVE_WITNESSES_JSON_ARTIFACT = "reports/canonical/discovery_negative_witnesses.json"
GAP_HEAD_ATTRIBUTION_ARTIFACT = "reports/canonical/gap_head_attribution_capsule.json"
DGT_NEURAL_ABLATION_ARTIFACT = "reports/canonical/dgt-neural-ablation.json"
NODE_TYPES = frozenset(
    {
        "raw_evidence",
        "projected_discovery",
        "terminal_claim",
        "negative_witness",
        "revocation",
        "mechanism_certificate",
    }
)
NODE_KEYS = frozenset(
    {
        "node_id",
        "node_type",
        "source_pointer",
        "discovery_level",
        "terminal_verdict",
        "evidence_scope",
        "evidence_type",
        "evidence_provenance_pointer",
        "model_comparison_semantic_pointer",
        "d5_m_scope_pointer",
        "depends_on",
        "not_claimed",
    }
)


@dataclass(frozen=True)
class ClaimGraphNode:
    node_id: str
    node_type: str
    source_pointer: str
    discovery_level: str | None
    terminal_verdict: str | None
    evidence_scope: tuple[str, ...] | None
    evidence_type: str | None
    evidence_provenance_pointer: str | None
    model_comparison_semantic_pointer: str | None
    d5_m_scope_pointer: str | None
    depends_on: tuple[str, ...]
    not_claimed: tuple[str, ...]

    def to_json(self) -> dict[str, Any]:
        return asdict(self)


def terminal_node_id_for_claim_id(claim_id: str) -> str:
    if claim_id.startswith("claim:witness:"):
        suffix = claim_id.removeprefix("claim:witness:")
        if suffix:
            return f"terminal:witness:{suffix}"
    if claim_id.startswith("claim:"):
        suffix = claim_id.removeprefix("claim:")
        if suffix:
            return f"terminal:{suffix}"
    raise ValueError(f"claim_id must start with claim: {claim_id}")


def _artifact_path(root: Path, artifact: str) -> Path:
    return root / artifact


def _load_json(root: Path, artifact: str) -> Any:
    return json.loads(_artifact_path(root, artifact).read_text(encoding="utf-8"))


def load_claim_verdict_rows(root: Path) -> list[dict[str, Any]]:
    path = _artifact_path(root, CLAIM_VERDICTS_JSONL_ARTIFACT)
    rows: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if line:
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError("claim verdict JSONL rows must be objects")
            rows.append(row)
    return rows


def split_source_pointer(source_pointer: str) -> tuple[str, str] | None:
    normalized = normalize_artifact_pointer(source_pointer)
    if normalized is None:
        return None
    artifact, pointer = normalized.split(":", 1)
    return artifact, pointer


def resolve_source_pointer(root: Path, source_pointer: str) -> Any:
    return resolve_artifact_pointer(root, source_pointer)


def source_pointer_resolves(root: Path, source_pointer: str) -> bool:
    return resolve_source_pointer(root, source_pointer) is not None


def _with_root_pointer(source: str) -> str:
    return source if ":$" in source else f"{source}:$"


def _artifact_pointer(source_artifact: str, value: Any) -> str | None:
    if not isinstance(value, str) or not value or value == "None":
        return None
    if ":$" in value:
        return value
    if value.startswith("$."):
        return f"{source_artifact}:{value}"
    return None


def _first_resolving_pointer(root: Path, candidates: Sequence[str]) -> str:
    for candidate in candidates:
        pointer = _with_root_pointer(candidate)
        if source_pointer_resolves(root, pointer):
            return pointer
    raise ValueError(f"no source pointer resolves among candidates: {list(candidates)}")


def _not_claimed(value: Any) -> tuple[str, ...]:
    if isinstance(value, str) and value:
        return (value,)
    if isinstance(value, Sequence) and not isinstance(value, (str, bytes)):
        return tuple(str(item) for item in value if str(item))
    return ()


def _nodes_by_id(nodes: Sequence[ClaimGraphNode]) -> dict[str, ClaimGraphNode]:
    result: dict[str, ClaimGraphNode] = {}
    for node in nodes:
        if node.node_id in result:
            raise ValueError(f"duplicate claim graph node_id: {node.node_id}")
        result[node.node_id] = node
    return result


def _node_json(nodes: Sequence[ClaimGraphNode]) -> list[dict[str, Any]]:
    return [node.to_json() for node in nodes]


def _load_optional_mapping(root: Path, artifact: str) -> Mapping[str, Any]:
    path = _artifact_path(root, artifact)
    if not path.exists():
        return {}
    payload = json.loads(path.read_text(encoding="utf-8"))
    return payload if isinstance(payload, Mapping) else {}


def _discovery_rows(root: Path) -> list[dict[str, Any]]:
    payload = load_validated_discovery_map_payload(root, artifact=DISCOVERY_MAP_JSON_ARTIFACT)
    rows = payload.get("rows")
    if not isinstance(rows, list) or not all(isinstance(row, dict) for row in rows):
        raise ValueError("discovery map must contain object rows")
    return rows


def _witnesses(root: Path) -> list[dict[str, Any]]:
    payload = _load_optional_mapping(root, NEGATIVE_WITNESSES_JSON_ARTIFACT)
    witnesses = payload.get("witnesses")
    if witnesses is None:
        return []
    if not isinstance(witnesses, list) or not all(isinstance(row, dict) for row in witnesses):
        raise ValueError("negative witnesses must contain object rows")
    return witnesses


def _mechanism_nodes(root: Path) -> list[ClaimGraphNode]:
    specs = (
        (
            "mechanism:gap-head-attribution-capsule",
            f"{GAP_HEAD_ATTRIBUTION_ARTIFACT}:$.mechanism_evidence",
            ("gap-head mechanism evidence remains owner-local to the attribution capsule",),
        ),
        (
            "mechanism:dgt-neural-ablation",
            f"{DGT_NEURAL_ABLATION_ARTIFACT}:$.nabl_hardgates.status",
            ("DGT neural-module ablation evidence remains pointer-only in downstream claim graph rows",),
        ),
    )
    nodes: list[ClaimGraphNode] = []
    for node_id, source_pointer, not_claimed in specs:
        if source_pointer_resolves(root, source_pointer):
            nodes.append(
                ClaimGraphNode(
                    node_id=node_id,
                    node_type="mechanism_certificate",
                    source_pointer=source_pointer,
                    discovery_level=None,
                    terminal_verdict=None,
                    evidence_scope=None,
                    evidence_type=None,
                    evidence_provenance_pointer=None,
                    model_comparison_semantic_pointer=None,
                    d5_m_scope_pointer=None,
                    depends_on=(),
                    not_claimed=not_claimed,
                )
            )
    return nodes


def _revocation_node_id(terminal_node_id: str) -> str:
    return f"revocation:{terminal_node_id.removeprefix('terminal:')}"


def _base_dependency_for_row(row: Mapping[str, Any], discovery_by_report: Mapping[str, Mapping[str, Any]]) -> str:
    claim_id = str(row["claim_id"])
    if claim_id.startswith("claim:witness:"):
        return f"negative-witness:{claim_id.removeprefix('claim:witness:')}"
    report = claim_id.removeprefix("claim:")
    if report not in discovery_by_report:
        raise ValueError(f"terminal claim lacks discovery row: {claim_id}")
    return f"projected:{report}"


def _claim_verdict_source_candidates(index: int, row: Mapping[str, Any]) -> list[str]:
    candidates = [
        str(row.get("negative_report_pointer") or ""),
        str(row.get("ledger_pointer") or ""),
        str(row.get("source") or ""),
        f"{CLAIM_VERDICTS_JSONL_ARTIFACT}:$.lines[{index}]",
    ]
    return [candidate for candidate in candidates if candidate]


def _projection_metadata_pointer(row: Mapping[str, Any], key: str, fallback: str | None = None) -> str | None:
    metadata = row.get("projection_metadata")
    value = metadata.get(key) if isinstance(metadata, Mapping) else None
    if isinstance(value, str) and value:
        return value
    return fallback


def build_claim_graph_payload(*, root: Path, generated_at: str | None = None) -> dict[str, Any]:
    rows = load_claim_verdict_rows(root)
    discovery_rows = _discovery_rows(root)
    witness_rows = _witnesses(root)
    discovery_by_report = {str(row["report"]): row for row in discovery_rows}
    nodes: list[ClaimGraphNode] = []

    for index, row in enumerate(discovery_rows):
        report = str(row["report"])
        source_artifact = str(row["json_artifact"])
        raw_pointer = _first_resolving_pointer(
            root,
            [
                candidate
                for key in ("evidence_pointer", "control_pointer", "failed_gate", "debt_row_pointer", "negative_report_pointer")
                for candidate in (_artifact_pointer(source_artifact, row.get(key)),)
                if candidate is not None
            ]
            + [source_artifact],
        )
        raw_id = f"raw:{report}"
        projected_id = f"projected:{report}"
        source_payload = _load_optional_mapping(root, source_artifact)
        evidence_scope = pointer_value(source_payload, "$.d5_m_projection.evidence_scope") if report == "discovery-gated-transformer" else None
        model_comparison_semantic_pointer = (
            _projection_metadata_pointer(row, "model_comparison_semantic_pointer", DGT_CONTROL_SEMANTIC_POINTER)
            if report == "discovery-gated-transformer"
            else None
        )
        d5_m_scope_pointer = (
            _projection_metadata_pointer(row, "d5_m_scope_pointer", D5_M_SCOPE_POINTER)
            if report == "discovery-gated-transformer"
            else None
        )
        nodes.append(
            ClaimGraphNode(
                node_id=raw_id,
                node_type="raw_evidence",
                source_pointer=raw_pointer,
                discovery_level=None,
                terminal_verdict=None,
                evidence_scope=None,
                evidence_type=str(row.get("evidence_type")) if isinstance(row.get("evidence_type"), str) else None,
                evidence_provenance_pointer=str(row.get("evidence_provenance_pointer"))
                if isinstance(row.get("evidence_provenance_pointer"), str)
                else None,
                model_comparison_semantic_pointer=model_comparison_semantic_pointer,
                d5_m_scope_pointer=d5_m_scope_pointer,
                depends_on=(),
                not_claimed=_not_claimed(row.get("not_claimed")),
            )
        )
        nodes.append(
            ClaimGraphNode(
                node_id=projected_id,
                node_type="projected_discovery",
                source_pointer=f"{DISCOVERY_MAP_JSON_ARTIFACT}:$.rows[{index}]",
                discovery_level=str(row.get("discovery_level") or ""),
                terminal_verdict=str(row.get("terminal_verdict") or "") or None,
                evidence_scope=tuple(evidence_scope) if isinstance(evidence_scope, list) else None,
                evidence_type=str(row.get("evidence_type")) if isinstance(row.get("evidence_type"), str) else None,
                evidence_provenance_pointer=str(row.get("evidence_provenance_pointer"))
                if isinstance(row.get("evidence_provenance_pointer"), str)
                else None,
                model_comparison_semantic_pointer=model_comparison_semantic_pointer,
                d5_m_scope_pointer=d5_m_scope_pointer,
                depends_on=(raw_id,),
                not_claimed=_not_claimed(row.get("not_claimed")),
            )
        )

    for index, witness in enumerate(witness_rows):
        kind = str(witness.get("kind") or "")
        if not kind:
            raise ValueError(f"negative witness row lacks kind: {index}")
        nodes.append(
            ClaimGraphNode(
                node_id=f"negative-witness:{kind}",
                node_type="negative_witness",
                source_pointer=f"{NEGATIVE_WITNESSES_JSON_ARTIFACT}:$.witnesses[{index}]",
                discovery_level=str(witness.get("discovery_level") or "") or None,
                terminal_verdict=str(witness.get("terminal_verdict") or "") or None,
                evidence_scope=None,
                evidence_type=None,
                evidence_provenance_pointer=None,
                model_comparison_semantic_pointer=None,
                d5_m_scope_pointer=None,
                depends_on=(),
                not_claimed=_not_claimed(witness.get("not_claimed")),
            )
        )

    terminal_nodes: list[ClaimGraphNode] = []
    revocation_nodes: list[ClaimGraphNode] = []
    for index, row in enumerate(rows):
        terminal_id = str(row["claim_graph_node_id"])
        expected_id = terminal_node_id_for_claim_id(str(row["claim_id"]))
        if terminal_id != expected_id:
            raise ValueError(f"claim verdict graph foreign key mismatch: {row['claim_id']}")
        base_dependency = _base_dependency_for_row(row, discovery_by_report)
        depends_on = (base_dependency,)
        if row.get("claim_verdict") == "revoked_discovery":
            revocation_id = _revocation_node_id(terminal_id)
            source_pointer = _first_resolving_pointer(
                root,
                _claim_verdict_source_candidates(index, row),
            )
            revocation_nodes.append(
                ClaimGraphNode(
                    node_id=revocation_id,
                    node_type="revocation",
                    source_pointer=source_pointer,
                    discovery_level=None,
                    terminal_verdict=str(row.get("claim_verdict") or ""),
                    evidence_scope=None,
                    evidence_type=None,
                    evidence_provenance_pointer=None,
                    model_comparison_semantic_pointer=None,
                    d5_m_scope_pointer=None,
                    depends_on=(base_dependency,),
                    not_claimed=(),
                )
            )
            depends_on = (revocation_id,)
        terminal_nodes.append(
            ClaimGraphNode(
                node_id=terminal_id,
                node_type="terminal_claim",
                source_pointer=f"{CLAIM_VERDICTS_JSONL_ARTIFACT}:$.lines[{index}]",
                discovery_level=None,
                terminal_verdict=str(row["claim_verdict"]),
                evidence_scope=None,
                evidence_type=None,
                evidence_provenance_pointer=None,
                model_comparison_semantic_pointer=None,
                d5_m_scope_pointer=None,
                depends_on=depends_on,
                not_claimed=(),
            )
        )
    nodes.extend(revocation_nodes)
    nodes.extend(_mechanism_nodes(root))
    nodes.extend(terminal_nodes)

    hardgates = _hardgates(root=root, nodes=nodes, verdict_rows=rows, discovery_rows=discovery_rows)
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": CLAIM_GRAPH_ARTIFACT_ID,
        "generated_at": generated_at,
        "status": "pointer-only",
        "node_count": len(nodes),
        "nodes": _node_json(nodes),
        "hardgates": hardgates,
    }
    errors = validate_claim_graph_payload(payload, root=root, claim_verdict_rows=rows)
    if errors:
        raise ValueError("; ".join(errors))
    return payload


def _hardgates(
    *,
    root: Path,
    nodes: Sequence[ClaimGraphNode],
    verdict_rows: Sequence[Mapping[str, Any]],
    discovery_rows: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    by_id = _nodes_by_id(nodes)
    d5_o_rows = [row for row in discovery_rows if row.get("discovery_level") in {"D5-O", "D5-M"}]
    mechanism_entries = []
    for row in d5_o_rows:
        report = str(row["report"])
        mechanism_status = str(row.get("mechanism_status") or "blocked")
        mechanism_pointer = row.get("mechanism_pointer")
        mechanism_source_pointer = row.get("mechanism_ledger_pointer") or row.get("mechanism_closure_pointer") or row.get("mechanism_pointer")
        mechanism_node = by_id.get("mechanism:gap-head-attribution-capsule")
        mechanism_resolves = mechanism_node is not None and source_pointer_resolves(root, mechanism_node.source_pointer)
        mechanism_certificate_node_id = mechanism_node.node_id if mechanism_status == "ready" and mechanism_resolves and mechanism_node is not None else None
        mechanism_entries.append(
            {
                "projected_node_id": f"projected:{report}",
                "discovery_level": str(row.get("discovery_level")),
                "mechanism_certificate_node_id": mechanism_certificate_node_id,
                "mechanism_status": mechanism_status,
                "mechanism_candidate_node_id": mechanism_node.node_id if mechanism_resolves and mechanism_node is not None else None,
                "mechanism_pointer": mechanism_pointer if isinstance(mechanism_pointer, str) else None,
                "mechanism_source_pointer": mechanism_source_pointer if isinstance(mechanism_source_pointer, str) else None,
                "source_pointer": f"{DISCOVERY_MAP_JSON_ARTIFACT}:$.rows[{discovery_rows.index(row)}]",
            }
        )
    terminal_ids = [str(row["claim_graph_node_id"]) for row in verdict_rows]
    edge_count = sum(len(node.depends_on) for node in nodes)
    revocation_node_ids = sorted(node.node_id for node in nodes if node.node_type == "revocation")
    return {
        "CG-HG1": {
            "status": "pass",
            "criterion": "accepted_positive_discovery terminals trace to raw_evidence through projected_discovery",
            "terminal_ids": [
                str(row["claim_graph_node_id"])
                for row in verdict_rows
                if row.get("claim_verdict") == "accepted_positive_discovery"
            ],
        },
        "CG-HG2": {
            "status": "pass",
            "criterion": "D5 projected discoveries explicitly record whether a mechanism node exists",
            "d5_o_mechanism": mechanism_entries,
        },
        "CG-HG3": {
            "status": "pass",
            "criterion": "raw_evidence nodes are never terminal_claim nodes",
        },
        "CG-HG4": {
            "status": "pass",
            "criterion": "claim verdict rows carry identity-only terminal graph foreign keys",
            "terminal_ids": terminal_ids,
        },
        "CG-HG5": {
            "status": "pass",
            "criterion": "all node source_pointer values resolve",
            "source_pointer_count": len(nodes),
        },
        "CG-HG6": {
            "status": "pass",
            "criterion": "accepted positive terminals have acceptance evidence bundle",
            "terminal_ids": [
                str(row["claim_graph_node_id"])
                for row in verdict_rows
                if row.get("claim_verdict") in {"accepted_positive_discovery", "mechanism_not_closed"}
            ],
        },
        "CG-HG7": {
            "status": "pass",
            "criterion": "nodes[*].depends_on forms an acyclic dependency graph; revocation nodes remain revocation evidence and are not positive forward-closure evidence",
            "node_count": len(nodes),
            "edge_count": edge_count,
            "revocation_node_ids": revocation_node_ids,
        },
        "CG-HG8": {
            "status": "pass",
            "criterion": "accepted high-impact terminal claims have resolvable review pointers",
            "terminal_ids": [
                str(row["claim_graph_node_id"])
                for row in verdict_rows
                if row.get("claim_verdict") == "accepted_positive_discovery"
            ],
        },
    }


def _ancestor_ids(node_id: str, by_id: Mapping[str, ClaimGraphNode]) -> set[str]:
    seen: set[str] = set()
    stack = list(by_id[node_id].depends_on)
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        if current in by_id:
            stack.extend(by_id[current].depends_on)
    return seen


def _find_dependency_cycle(nodes: Sequence[ClaimGraphNode]) -> tuple[str, ...] | None:
    by_id = {node.node_id: node for node in nodes}
    visiting: set[str] = set()
    visited: set[str] = set()
    path: list[str] = []

    def visit(node_id: str) -> tuple[str, ...] | None:
        if node_id in visited:
            return None
        if node_id in visiting:
            start = path.index(node_id)
            return tuple(path[start:] + [node_id])
        visiting.add(node_id)
        path.append(node_id)
        for dependency in by_id[node_id].depends_on:
            if dependency in by_id:
                cycle = visit(dependency)
                if cycle is not None:
                    return cycle
        path.pop()
        visiting.remove(node_id)
        visited.add(node_id)
        return None

    for node in nodes:
        cycle = visit(node.node_id)
        if cycle is not None:
            return cycle
    return None


def _node_from_json(row: Mapping[str, Any]) -> ClaimGraphNode | None:
    if frozenset(row) != NODE_KEYS:
        return None
    depends_on = row.get("depends_on")
    not_claimed = row.get("not_claimed")
    if not isinstance(depends_on, (list, tuple)) or not isinstance(not_claimed, (list, tuple)):
        return None
    evidence_scope = row.get("evidence_scope")
    if evidence_scope is not None and not isinstance(evidence_scope, (list, tuple)):
        return None
    return ClaimGraphNode(
        node_id=str(row["node_id"]),
        node_type=str(row["node_type"]),
        source_pointer=str(row["source_pointer"]),
        discovery_level=row["discovery_level"] if isinstance(row["discovery_level"], str) else None,
        terminal_verdict=row["terminal_verdict"] if isinstance(row["terminal_verdict"], str) else None,
        evidence_scope=tuple(str(item) for item in evidence_scope) if evidence_scope is not None else None,
        evidence_type=row["evidence_type"] if isinstance(row["evidence_type"], str) else None,
        evidence_provenance_pointer=row["evidence_provenance_pointer"] if isinstance(row["evidence_provenance_pointer"], str) else None,
        model_comparison_semantic_pointer=row["model_comparison_semantic_pointer"]
        if isinstance(row["model_comparison_semantic_pointer"], str)
        else None,
        d5_m_scope_pointer=row["d5_m_scope_pointer"] if isinstance(row["d5_m_scope_pointer"], str) else None,
        depends_on=tuple(str(item) for item in depends_on),
        not_claimed=tuple(str(item) for item in not_claimed),
    )


def validate_claim_graph_payload(
    payload: Mapping[str, Any],
    *,
    root: Path,
    claim_verdict_rows: Sequence[Mapping[str, Any]] | None = None,
) -> list[str]:
    errors: list[str] = []
    raw_nodes = payload.get("nodes")
    if not isinstance(raw_nodes, list):
        return ["claim graph payload must contain nodes list"]
    nodes: list[ClaimGraphNode] = []
    for index, raw_node in enumerate(raw_nodes):
        if not isinstance(raw_node, Mapping):
            errors.append(f"node {index} must be an object")
            continue
        node = _node_from_json(raw_node)
        if node is None:
            errors.append(f"node {index} field set mismatch")
            continue
        if node.node_type not in NODE_TYPES:
            errors.append(f"node {node.node_id} has invalid node_type")
        if node.node_type == "raw_evidence" and node.terminal_verdict is not None:
            errors.append(f"raw_evidence node has terminal verdict: {node.node_id}")
        if not source_pointer_resolves(root, node.source_pointer):
            errors.append(f"node source_pointer does not resolve: {node.node_id}")
        if node.evidence_provenance_pointer is not None and resolve_artifact_pointer(root, node.evidence_provenance_pointer) is None:
            errors.append(f"node evidence_provenance_pointer does not resolve: {node.node_id}")
        if node.model_comparison_semantic_pointer is not None and resolve_artifact_pointer(root, node.model_comparison_semantic_pointer) is None:
            errors.append(f"node model_comparison_semantic_pointer does not resolve: {node.node_id}")
        if node.d5_m_scope_pointer is not None and resolve_artifact_pointer(root, node.d5_m_scope_pointer) is None:
            errors.append(f"node d5_m_scope_pointer does not resolve: {node.node_id}")
        nodes.append(node)
    try:
        by_id = _nodes_by_id(nodes)
    except ValueError as exc:
        errors.append(str(exc))
        by_id = {}
    for node in nodes:
        for dependency in node.depends_on:
            if dependency not in by_id:
                errors.append(f"node dependency missing: {node.node_id}->{dependency}")
    cycle = _find_dependency_cycle(nodes)
    if cycle is not None:
        errors.append(f"CG-HG6 dependency cycle: {' -> '.join(cycle)}")

    verdict_rows = list(claim_verdict_rows) if claim_verdict_rows is not None else load_claim_verdict_rows(root)
    errors.extend(_validate_cg_hg1(verdict_rows, by_id))
    errors.extend(_validate_cg_hg2(payload, by_id))
    errors.extend(_validate_cg_hg3(by_id))
    errors.extend(_validate_cg_hg4(verdict_rows, by_id, root))
    errors.extend(_validate_cg_hg6(verdict_rows, root))
    errors.extend(_validate_owner_provenance_acceptance(verdict_rows, root))
    errors.extend(_validate_cg_hg8(verdict_rows, root))
    errors.extend(_validate_dgt_accepted_positive_path(verdict_rows, by_id, root))
    errors.extend(_validate_dgt_component_causal_evidence_scope(verdict_rows, by_id, root))
    errors.extend(_validate_dgt_neural_ablation_pointer(root))
    return errors


def _validate_cg_hg1(verdict_rows: Sequence[Mapping[str, Any]], by_id: Mapping[str, ClaimGraphNode]) -> list[str]:
    errors: list[str] = []
    for row in verdict_rows:
        if row.get("claim_verdict") != "accepted_positive_discovery":
            continue
        node_id = str(row.get("claim_graph_node_id") or "")
        if node_id not in by_id:
            errors.append(f"CG-HG1 terminal missing: {node_id}")
            continue
        ancestors = _ancestor_ids(node_id, by_id)
        if not any(by_id[ancestor].node_type == "raw_evidence" for ancestor in ancestors if ancestor in by_id):
            errors.append(f"CG-HG1 accepted positive lacks raw_evidence ancestry: {node_id}")
        if not any(by_id[ancestor].node_type == "projected_discovery" for ancestor in ancestors if ancestor in by_id):
            errors.append(f"CG-HG1 accepted positive lacks projected_discovery ancestry: {node_id}")
        node = by_id[node_id]
        if not any(
            dependency in by_id and by_id[dependency].node_type == "projected_discovery"
            for dependency in node.depends_on
        ):
            errors.append(f"CG-HG1 accepted positive lacks direct projected_discovery dependency: {node_id}")
    return errors


def _validate_cg_hg2(payload: Mapping[str, Any], by_id: Mapping[str, ClaimGraphNode]) -> list[str]:
    errors: list[str] = []
    hardgates = payload.get("hardgates")
    cg_hg2 = hardgates.get("CG-HG2") if isinstance(hardgates, Mapping) else None
    entries = cg_hg2.get("d5_o_mechanism") if isinstance(cg_hg2, Mapping) else None
    if not isinstance(entries, list):
        return ["CG-HG2 must list D5 mechanism entries"]
    projected_d5_o = {
        node.node_id
        for node in by_id.values()
        if node.node_type == "projected_discovery" and node.discovery_level in {"D5-O", "D5-M"}
    }
    entry_projected = set()
    for entry in entries:
        if not isinstance(entry, Mapping):
            errors.append("CG-HG2 entry must be an object")
            continue
        projected = entry.get("projected_node_id")
        if isinstance(projected, str):
            entry_projected.add(projected)
        mechanism_id = entry.get("mechanism_certificate_node_id")
        if mechanism_id is None:
            if entry.get("mechanism_status") not in {"blocked", "missing"}:
                errors.append(f"CG-HG2 missing mechanism status for {projected}")
        elif not isinstance(mechanism_id, str) or mechanism_id not in by_id or by_id[mechanism_id].node_type != "mechanism_certificate":
            errors.append(f"CG-HG2 mechanism node missing or wrong type for {projected}")
    if projected_d5_o != entry_projected:
        errors.append("CG-HG2 D5 projected node coverage mismatch")
    return errors


def _validate_cg_hg3(by_id: Mapping[str, ClaimGraphNode]) -> list[str]:
    errors: list[str] = []
    for node in by_id.values():
        if node.node_type == "terminal_claim":
            for dependency in node.depends_on:
                if dependency in by_id and by_id[dependency].node_type == "raw_evidence":
                    errors.append(f"CG-HG3 terminal directly depends on raw_evidence: {node.node_id}")
        if node.node_type == "raw_evidence" and node.node_id.startswith("terminal:"):
            errors.append(f"CG-HG3 raw node uses terminal identity: {node.node_id}")
    return errors


def _validate_cg_hg4(
    verdict_rows: Sequence[Mapping[str, Any]],
    by_id: Mapping[str, ClaimGraphNode],
    root: Path,
) -> list[str]:
    errors: list[str] = []
    row_terminal_ids: list[str] = []
    for index, row in enumerate(verdict_rows):
        node_id = row.get("claim_graph_node_id")
        if not isinstance(node_id, str) or not node_id.startswith("terminal:"):
            errors.append(f"CG-HG4 row lacks terminal graph foreign key: {index}")
            continue
        try:
            expected = terminal_node_id_for_claim_id(str(row.get("claim_id") or ""))
        except ValueError as exc:
            errors.append(str(exc))
            continue
        if node_id != expected:
            errors.append(f"CG-HG4 row foreign key mismatch: {index}")
        node = by_id.get(node_id)
        if node is None:
            errors.append(f"CG-HG4 terminal node missing: {node_id}")
            continue
        if node.node_type != "terminal_claim":
            errors.append(f"CG-HG4 foreign key targets non-terminal node: {node_id}")
        if node.source_pointer != f"{CLAIM_VERDICTS_JSONL_ARTIFACT}:$.lines[{index}]":
            errors.append(f"CG-HG4 terminal source pointer mismatch: {node_id}")
        if resolve_source_pointer(root, node.source_pointer) != row:
            errors.append(f"CG-HG4 terminal source pointer resolves to another row: {node_id}")
        if node.terminal_verdict != row.get("claim_verdict"):
            errors.append(f"CG-HG4 terminal verdict mismatch: {node_id}")
        row_terminal_ids.append(node_id)
    terminal_nodes = {
        node.node_id
        for node in by_id.values()
        if node.node_type == "terminal_claim" and node.source_pointer.startswith(f"{CLAIM_VERDICTS_JSONL_ARTIFACT}:")
    }
    if set(row_terminal_ids) != terminal_nodes or len(row_terminal_ids) != len(terminal_nodes):
        errors.append("CG-HG4 terminal claim exact cover mismatch")
    return errors


def _specs_by_name() -> dict[str, Any]:
    from scripts.run_claim_verdict_demo import DIMENSION_MISMATCH_REPORT, _dimension_mismatch_pointer_spec
    from scripts.run_canonical_reports import CANONICAL_REPORTS

    specs = {spec.name: spec for spec in CANONICAL_REPORTS}
    specs[DIMENSION_MISMATCH_REPORT] = _dimension_mismatch_pointer_spec()
    return specs


def _validate_cg_hg6(verdict_rows: Sequence[Mapping[str, Any]], root: Path) -> list[str]:
    errors: list[str] = []
    accepted = {
        "accepted_positive_discovery",
        "mechanism_not_closed",
    }
    if not any(row.get("claim_verdict") in accepted for row in verdict_rows):
        return errors
    discovery_by_report = {str(row["report"]): row for row in _discovery_rows(root)}
    specs = _specs_by_name()
    scorecard_snapshot = load_scorecard_snapshot(root)
    for row in verdict_rows:
        if row.get("claim_verdict") not in accepted:
            continue
        claim_id = str(row.get("claim_id") or "")
        report = claim_id.removeprefix("claim:")
        discovery_row = discovery_by_report.get(report)
        spec = specs.get(report)
        if discovery_row is None or spec is None:
            errors.append(f"CG-HG6 acceptance evidence lookup failed: {claim_id}")
            continue
        payload = _load_json(root, str(discovery_row["json_artifact"]))
        if not isinstance(payload, Mapping):
            errors.append(f"CG-HG6 acceptance evidence payload missing: {claim_id}")
            continue
        result = validate_positive_claim_evidence(
            root,
            spec=spec,
            discovery_row=discovery_row,
            payload=payload,
            scorecard_snapshot=scorecard_snapshot,
        )
        if not result.ok:
            errors.append(f"CG-HG6 {result.reason}: {claim_id} -> {result.ledger_pointer}")
    return errors


def _validate_owner_provenance_acceptance(verdict_rows: Sequence[Mapping[str, Any]], root: Path) -> list[str]:
    errors: list[str] = []
    section = load_evidence_provenance(root, require=False)
    for row in verdict_rows:
        if row.get("claim_verdict") != "accepted_positive_discovery":
            continue
        claim_id = str(row.get("claim_id") or "")
        report = claim_id.removeprefix("claim:")
        if section is None:
            errors.append(f"CG-HG provenance owner missing: {claim_id}")
            continue
        owner = owner_discovery_row(section, report)
        if owner is None:
            errors.append(f"CG-HG provenance discovery row missing: {claim_id}")
            continue
        evidence_type = owner.get("evidence_type")
        if evidence_type != "empirical_training_clean":
            errors.append(f"CG-HG provenance non-empirical evidence: {claim_id} -> {evidence_type}")
        metric_rows = owner_metric_rows(section, report)
        if not metric_rows:
            errors.append(f"CG-HG provenance metric rows missing: {claim_id}")
            continue
        blocked = [
            str(metric.get("source_type"))
            for metric in metric_rows
            if metric.get("source_type") in {"deterministic_projection", "protocol_field", "declared_constant", "arm_branch"}
            or metric.get("allowed_for_empirical_claim") is not True
        ]
        if blocked:
            errors.append(f"CG-HG provenance blocked source types: {claim_id} -> {', '.join(sorted(set(blocked)))}")
    return errors


def _validate_cg_hg8(verdict_rows: Sequence[Mapping[str, Any]], root: Path) -> list[str]:
    errors: list[str] = []
    discovery_by_report = {str(row["report"]): row for row in _discovery_rows(root)}
    specs = _specs_by_name()
    for row in verdict_rows:
        if row.get("claim_verdict") != "accepted_positive_discovery":
            continue
        claim_id = str(row.get("claim_id") or "")
        if claim_id == "claim:discovery-gated-transformer":
            gate = high_impact_review_dgt_gate(root)
            if gate.get("status") != "pass":
                errors.append(f"CG-HG8 high-impact-review-required: {claim_id} -> {gate.get('ledger_pointer')}")
            continue
        report = claim_id.removeprefix("claim:")
        discovery_row = discovery_by_report.get(report)
        spec = specs.get(report)
        if discovery_row is None or spec is None:
            continue
        payload = _load_json(root, str(discovery_row["json_artifact"]))
        if not isinstance(payload, Mapping):
            errors.append(f"CG-HG8 high-impact review payload missing: {claim_id}")
            continue
        failure_pointer = high_impact_review_failure_pointer(root, spec, payload)
        if failure_pointer is not None:
            errors.append(f"CG-HG8 high-impact-review-required: {claim_id} -> {discovery_row['json_artifact']}:{failure_pointer}")
    return errors


def _validate_dgt_accepted_positive_path(
    verdict_rows: Sequence[Mapping[str, Any]],
    by_id: Mapping[str, ClaimGraphNode],
    root: Path,
) -> list[str]:
    errors: list[str] = []
    for row in verdict_rows:
        if row.get("claim_id") != "claim:discovery-gated-transformer":
            continue
        if row.get("claim_verdict") != "accepted_positive_discovery":
            continue
        terminal = by_id.get("terminal:discovery-gated-transformer")
        projected = by_id.get("projected:discovery-gated-transformer")
        raw = by_id.get("raw:discovery-gated-transformer")
        if terminal is None or projected is None or raw is None:
            errors.append("DGT accepted-positive path missing raw/projected/terminal node")
            continue
        if terminal.depends_on != ("projected:discovery-gated-transformer",):
            errors.append("DGT accepted-positive terminal must depend only on projected:DGT")
        if projected.depends_on != ("raw:discovery-gated-transformer",):
            errors.append("DGT accepted-positive projected node must depend only on raw:DGT")
        if raw.terminal_verdict is not None or projected.terminal_verdict is not None:
            errors.append("DGT raw/projected nodes must not carry terminal verdict")
        for node in (raw, projected):
            if node.model_comparison_semantic_pointer != DGT_CONTROL_SEMANTIC_POINTER:
                errors.append(f"DGT accepted-positive node lacks model-comparison semantic pointer: {node.node_id}")
            if node.d5_m_scope_pointer != D5_M_SCOPE_POINTER:
                errors.append(f"DGT accepted-positive node lacks D5-M scope pointer: {node.node_id}")
        semantic = resolve_artifact_pointer(root, projected.model_comparison_semantic_pointer or "")
        if not isinstance(semantic, Mapping):
            errors.append("DGT accepted-positive semantic pointer does not resolve")
        elif semantic.get("allowed_evidence_chain") is False:
            errors.append("DGT accepted-positive deterministic projection cannot support trained empirical evidence chain")
        scope = resolve_artifact_pointer(root, projected.d5_m_scope_pointer or "")
        if not isinstance(scope, Mapping):
            errors.append("DGT accepted-positive D5-M scope pointer does not resolve")
        elif scope.get("synthetic_bounded") is not True:
            errors.append("DGT accepted-positive D5-M scope lacks synthetic-bounded marker")
    return errors


def _validate_dgt_component_causal_evidence_scope(
    verdict_rows: Sequence[Mapping[str, Any]],
    by_id: Mapping[str, ClaimGraphNode],
    root: Path,
) -> list[str]:
    errors: list[str] = []
    positive_rows = [
        row
        for row in verdict_rows
        if row.get("claim_id") == "claim:discovery-gated-transformer"
        and row.get("claim_verdict") == "accepted_positive_discovery"
    ]
    if not positive_rows:
        return errors
    projected = by_id.get("projected:discovery-gated-transformer")
    if projected is None:
        return ["DGT component-causal claim lacks projected graph node"]
    if projected.evidence_scope is None:
        errors.append("DGT component-causal claim lacks evidence_scope")
    else:
        errors.extend(f"DGT component-causal {error}" for error in validate_evidence_scope(list(projected.evidence_scope)))
    source = resolve_source_pointer(root, projected.source_pointer)
    if not isinstance(source, Mapping):
        errors.append("DGT component-causal discovery row pointer does not resolve")
        return errors
    source_artifact = source.get("json_artifact")
    if not isinstance(source_artifact, str):
        errors.append("DGT component-causal source artifact missing")
        return errors
    payload = _load_optional_mapping(root, source_artifact)
    d5_m = pointer_value(payload, "$.d5_m_projection")
    if not isinstance(d5_m, Mapping):
        errors.append("DGT component-causal D5-M projection missing")
        return errors
    scope = d5_m.get("evidence_scope")
    if scope is None:
        errors.append("DGT component-causal D5-M projection lacks evidence_scope")
    else:
        errors.extend(f"DGT component-causal D5-M {error}" for error in validate_evidence_scope(scope))
    if isinstance(scope, list) and "production-forbidden" in scope:
        positive_surface = {
            "status": d5_m.get("status"),
            "readiness": d5_m.get("readiness"),
            "discovery_level": d5_m.get("discovery_level"),
            "terminal_verdict_scope": d5_m.get("terminal_verdict_scope"),
            "claim_surface": d5_m.get("claim_surface"),
            "positive_claim": d5_m.get("positive_claim"),
            "claim": d5_m.get("claim"),
        }
        positive_text = json.dumps(positive_surface, sort_keys=True).lower()
        if any(
            token in positive_text
            for token in (
                "production claim",
                "production authority accepted",
                "production deployment",
                "deployment authority",
                "production ready",
                "production-ready",
            )
        ):
            errors.append("DGT component-causal evidence_scope contradicts production claim")
    return errors


def _validate_dgt_neural_ablation_pointer(root: Path) -> list[str]:
    path = _artifact_path(root, DGT_NEURAL_ABLATION_ARTIFACT)
    if not path.exists():
        return []
    payload = _load_json(root, DGT_NEURAL_ABLATION_ARTIFACT)
    claims = payload.get("component_causal_claims") if isinstance(payload, Mapping) else None
    if claims is None:
        return ["dgt-neural-ablation component_causal_claims pointer missing"]
    if not isinstance(claims, list):
        return ["dgt-neural-ablation component_causal_claims must be a list"]
    errors: list[str] = []
    for index, claim in enumerate(claims):
        if not isinstance(claim, Mapping):
            errors.append(f"dgt-neural-ablation component_causal_claims[{index}] must be an object")
            continue
        for error in validate_evidence_scope(claim.get("evidence_scope")):
            errors.append(f"dgt-neural-ablation component_causal_claims[{index}] {error}")
    return errors


def render_claim_graph_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Claim Graph",
        "",
        f"- Generated at: `{payload.get('generated_at')}`",
        f"- Status: `{payload.get('status')}`",
        f"- Nodes: `{payload.get('node_count')}`",
        "",
        "| node | type | source | depends on |",
        "| --- | --- | --- | --- |",
    ]
    for node in payload.get("nodes", []):
        if not isinstance(node, Mapping):
            continue
        depends_on = ", ".join(f"`{item}`" for item in node.get("depends_on", []))
        lines.append(
            "| "
            f"`{node.get('node_id')}` | "
            f"`{node.get('node_type')}` | "
            f"`{node.get('source_pointer')}` | "
            f"{depends_on} |"
        )
    lines.extend(["", "## Hardgates", ""])
    hardgates = payload.get("hardgates")
    if isinstance(hardgates, Mapping):
        for name, gate in sorted(hardgates.items()):
            if isinstance(gate, Mapping):
                lines.append(f"- `{name}`: `{gate.get('status')}` {gate.get('criterion')}")
    lines.append("")
    return "\n".join(lines)


def write_claim_graph(*, root: Path, generated_at: str | None = None) -> dict[str, Any]:
    payload = build_claim_graph_payload(root=root, generated_at=generated_at)
    json_path = _artifact_path(root, CLAIM_GRAPH_JSON_ARTIFACT)
    markdown_path = _artifact_path(root, CLAIM_GRAPH_MARKDOWN_ARTIFACT)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(render_claim_graph_markdown(payload), encoding="utf-8")
    return payload

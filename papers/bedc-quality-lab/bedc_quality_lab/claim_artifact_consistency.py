"""Claim verdict and artifact consistency hardgate audit."""

from __future__ import annotations

from dataclasses import asdict, dataclass
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.artifact_freshness import canonical_artifact_hash, load_scorecard_snapshot
from bedc_quality_lab.claim_graph import terminal_node_id_for_claim_id
from bedc_quality_lab.discovery_compiler.claim_verdict_reason import (
    MODEL_COMPARISON_NOT_READY,
    POSITIVE_DISCOVERY_GATES_PASS,
    SOURCE_INSUFFICIENT,
)
from bedc_quality_lab.discovery_compiler.map import load_validated_discovery_map_payload
from bedc_quality_lab.discovery_compiler.pointers import (
    normalize_artifact_pointer,
    resolve_artifact_pointer,
)


SCHEMA_ID = "bedc-quality-lab:claim-artifact-consistency"
ARTIFACT_ID = "bedc-quality-lab:claim-artifact-consistency"
JSON_ARTIFACT = "reports/canonical/claim-artifact-consistency.json"
MARKDOWN_ARTIFACT = "reports/canonical/claim-artifact-consistency.md"
CLAIM_VERDICTS_ARTIFACT = "reports/canonical/claim_verdicts.jsonl"
CLAIM_GRAPH_ARTIFACT = "reports/canonical/claim_graph.json"
DISCOVERY_MAP_ARTIFACT = "reports/canonical/discovery_map.json"
QUALITY_SCORECARD_ARTIFACT = "reports/canonical/quality-scorecard.json"
HIGH_IMPACT_REVIEW_ARTIFACT = "reports/canonical/high-impact-review.json"
HIGH_IMPACT_REVIEW_FINGERPRINT_ARTIFACT = "reports/canonical/high-impact-review.fingerprint.json"
DGT_ARTIFACT = "reports/canonical/discovery-gated-transformer.json"
DGT_COMPONENT_ID = "DGT"
DGT_CLAIM_ID = "claim:discovery-gated-transformer"
DEFAULT_CLAIM_ID = DGT_CLAIM_ID
POSITIVE_LEVELS = frozenset({"D4", "D5-O", "D5-M"})
CORE_OWNER = "Core"


@dataclass(frozen=True)
class ConsistencyFinding:
    gate_id: str
    status: str
    reason: str
    pointer: str
    expected: str
    actual: str

    def to_json(self) -> dict[str, str]:
        return asdict(self)


@dataclass(frozen=True)
class ClaimArtifactConsistencyReport:
    schema_id: str
    artifact_id: str
    generated_at: str
    claim_id: str
    status: str
    json_artifact: str
    markdown_artifact: str
    gates: tuple[ConsistencyFinding, ...]

    def to_json(self) -> dict[str, Any]:
        return {
            "schema_id": self.schema_id,
            "artifact_id": self.artifact_id,
            "generated_at": self.generated_at,
            "claim_id": self.claim_id,
            "status": self.status,
            "json_artifact": self.json_artifact,
            "markdown_artifact": self.markdown_artifact,
            "gates": [gate.to_json() for gate in self.gates],
        }


class PointerResolver:
    def __init__(self, root: Path) -> None:
        self.root = root

    def resolve(self, pointer: str | None) -> Any:
        if not isinstance(pointer, str):
            return None
        return resolve_artifact_pointer(self.root, pointer)

    def resolves(self, pointer: str | None) -> bool:
        return self.resolve(pointer) is not None

def _load_json(root: Path, artifact: str) -> Any:
    return json.loads((root / artifact).read_text(encoding="utf-8"))


def _load_json_object(root: Path, artifact: str) -> Mapping[str, Any]:
    try:
        payload = _load_json(root, artifact)
    except (FileNotFoundError, json.JSONDecodeError):
        return {}
    return payload if isinstance(payload, Mapping) else {}


def _load_jsonl_rows(root: Path, artifact: str) -> list[dict[str, Any]]:
    path = root / artifact
    rows: list[dict[str, Any]] = []
    if not path.exists():
        return rows
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line:
            continue
        value = json.loads(line)
        if isinstance(value, dict):
            rows.append(value)
    return rows


def _json_text(value: Any) -> str:
    if value is None:
        return "missing"
    if isinstance(value, (dict, list)):
        return json.dumps(value, sort_keys=True)
    return str(value)


def _pointer_from_cell(cell: Any) -> str | None:
    if isinstance(cell, Mapping):
        artifact = cell.get("artifact")
        pointer = cell.get("pointer")
        if isinstance(artifact, str) and isinstance(pointer, str):
            return f"{artifact}:{pointer}"
    if isinstance(cell, str):
        return normalize_artifact_pointer(cell)
    return None


def _pass(gate_id: str, reason: str, pointer: str, *, expected: str = "consistent", actual: str = "consistent") -> ConsistencyFinding:
    return ConsistencyFinding(gate_id, "pass", reason, pointer, expected, actual)


def _fail(gate_id: str, reason: str, pointer: str, *, expected: str, actual: Any) -> ConsistencyFinding:
    return ConsistencyFinding(gate_id, "fail", reason, pointer, expected, _json_text(actual))


def _row_index(rows: Sequence[Mapping[str, Any]], key: str, value: str) -> int | None:
    for index, row in enumerate(rows):
        if row.get(key) == value:
            return index
    return None


def _row_by_key(rows: Sequence[Mapping[str, Any]], key: str, value: str) -> Mapping[str, Any] | None:
    index = _row_index(rows, key, value)
    return rows[index] if index is not None else None


def _claim_verdict_pointer(index: int | None) -> str:
    return f"{CLAIM_VERDICTS_ARTIFACT}:$.lines[{index}]" if index is not None else f"{CLAIM_VERDICTS_ARTIFACT}:$"


def _discovery_row_pointer(index: int | None) -> str:
    return f"{DISCOVERY_MAP_ARTIFACT}:$.rows[{index}]" if index is not None else f"{DISCOVERY_MAP_ARTIFACT}:$.rows"


def _terminal_node_pointer(index: int | None) -> str:
    return f"{CLAIM_GRAPH_ARTIFACT}:$.nodes[{index}]" if index is not None else f"{CLAIM_GRAPH_ARTIFACT}:$.nodes"


def _coverage_cell_pointer(index: int | None) -> str:
    return (
        f"{DISCOVERY_MAP_ARTIFACT}:$.coverage_matrix.cells[{index}]"
        if index is not None
        else f"{DISCOVERY_MAP_ARTIFACT}:$.coverage_matrix.cells"
    )


def _current_hash(root: Path, artifact: str) -> str:
    path = root / artifact
    return canonical_artifact_hash(path) if path.exists() else ""


def _fingerprint_source_hash(root: Path, source_artifact: str) -> str | None:
    fingerprint = _load_json_object(root, HIGH_IMPACT_REVIEW_FINGERPRINT_ARTIFACT)
    inputs = fingerprint.get("inputs")
    if not isinstance(inputs, Mapping):
        return None
    source_artifacts = inputs.get("source_artifacts")
    if not isinstance(source_artifacts, list):
        return None
    for row in source_artifacts:
        if isinstance(row, Mapping) and row.get("path") == source_artifact:
            sha256 = row.get("sha256")
            return sha256 if isinstance(sha256, str) else None
    return None


def _terminal_chain_contains(nodes_by_id: Mapping[str, Mapping[str, Any]], start_id: str, pointer: str) -> bool:
    seen: set[str] = set()
    stack = [start_id]
    while stack:
        node_id = stack.pop()
        if node_id in seen:
            continue
        seen.add(node_id)
        node = nodes_by_id.get(node_id)
        if not isinstance(node, Mapping):
            continue
        if node.get("source_pointer") == pointer:
            return True
        depends_on = node.get("depends_on")
        if isinstance(depends_on, list):
            stack.extend(str(item) for item in depends_on)
    return False


def _gate_hg1(
    *,
    resolver: PointerResolver,
    claim_id: str,
    verdict_rows: Sequence[Mapping[str, Any]],
    discovery_rows: Sequence[Mapping[str, Any]],
) -> ConsistencyFinding:
    verdict_index = _row_index(verdict_rows, "claim_id", claim_id)
    verdict_row = verdict_rows[verdict_index] if verdict_index is not None else None
    if verdict_row is None:
        return _fail("CONS-HG1", "claim verdict row is missing", _claim_verdict_pointer(verdict_index), expected="claim row", actual=None)
    report = claim_id.removeprefix("claim:")
    discovery_index = _row_index(discovery_rows, "report", report)
    discovery_row = discovery_rows[discovery_index] if discovery_index is not None else None
    if discovery_row is None:
        return _fail("CONS-HG1", "discovery map row is missing", _discovery_row_pointer(discovery_index), expected="discovery row", actual=None)
    verdict = verdict_row.get("claim_verdict")
    level = discovery_row.get("discovery_level")
    source = verdict_row.get("source")
    evidence_pointer = discovery_row.get("evidence_pointer")
    expected_source = None
    if isinstance(discovery_row.get("json_artifact"), str) and isinstance(evidence_pointer, str):
        expected_source = f"{discovery_row['json_artifact']}:{evidence_pointer}"
    if verdict == "accepted_positive_discovery":
        if level not in POSITIVE_LEVELS:
            return _fail("CONS-HG1", "accepted positive verdict requires D4/D5 discovery level", _discovery_row_pointer(discovery_index), expected=sorted(POSITIVE_LEVELS), actual=level)
        if source != expected_source:
            return _fail("CONS-HG1", "verdict source must match discovery evidence pointer", _claim_verdict_pointer(verdict_index), expected=expected_source or "source pointer", actual=source)
        if not resolver.resolves(str(source)):
            return _fail("CONS-HG1", "verdict source pointer does not resolve", str(source), expected="resolving pointer", actual=source)
    return _pass("CONS-HG1", "discovery level and verdict are coherent", _claim_verdict_pointer(verdict_index))


def _gate_hg2(root: Path, claim_id: str, verdict_rows: Sequence[Mapping[str, Any]]) -> ConsistencyFinding:
    verdict_index = _row_index(verdict_rows, "claim_id", claim_id)
    verdict_row = verdict_rows[verdict_index] if verdict_index is not None else None
    if verdict_row is None:
        return _fail("CONS-HG2", "claim verdict row is missing", _claim_verdict_pointer(verdict_index), expected="claim row", actual=None)
    verdict = verdict_row.get("claim_verdict")
    if verdict != "accepted_positive_discovery":
        return _pass("CONS-HG2", "non-positive verdict has no scorecard hash promotion dependency", _claim_verdict_pointer(verdict_index), expected="not applicable", actual="not applicable")
    snapshot = load_scorecard_snapshot(root)
    if verdict_row.get("scorecard_pointer") != snapshot.scorecard_pointer:
        return _fail("CONS-HG2", "scorecard pointer mismatch", _claim_verdict_pointer(verdict_index), expected=snapshot.scorecard_pointer, actual=verdict_row.get("scorecard_pointer"))
    if verdict_row.get("scorecard_hash") != snapshot.scorecard_hash:
        return _fail("CONS-HG2", "scorecard hash is stale", _claim_verdict_pointer(verdict_index), expected=snapshot.scorecard_hash, actual=verdict_row.get("scorecard_hash"))
    if verdict_row.get("scorecard_ready") is not True or snapshot.scorecard_ready is not True:
        return _fail("CONS-HG2", "positive verdict requires current ready scorecard", _claim_verdict_pointer(verdict_index), expected="scorecard_ready true", actual=verdict_row.get("scorecard_ready"))
    return _pass("CONS-HG2", "positive verdict uses the current scorecard hash", _claim_verdict_pointer(verdict_index), expected=snapshot.scorecard_hash, actual=str(verdict_row.get("scorecard_hash")))


def _gate_hg3(claim_id: str, verdict_rows: Sequence[Mapping[str, Any]]) -> ConsistencyFinding:
    verdict_index = _row_index(verdict_rows, "claim_id", claim_id)
    verdict_row = verdict_rows[verdict_index] if verdict_index is not None else None
    if verdict_row is None:
        return _fail("CONS-HG3", "claim verdict row is missing", _claim_verdict_pointer(verdict_index), expected="claim row", actual=None)
    reason = verdict_row.get("reason")
    ready = verdict_row.get("scorecard_ready")
    if reason == POSITIVE_DISCOVERY_GATES_PASS and ready is not True:
        return _fail("CONS-HG3", "positive pass reason requires scorecard_ready true", _claim_verdict_pointer(verdict_index), expected="scorecard_ready true", actual=ready)
    if reason in {SOURCE_INSUFFICIENT, MODEL_COMPARISON_NOT_READY, "scorecard-not-ready"} and ready is True:
        return _fail("CONS-HG3", "not-ready reason cannot pair with scorecard_ready true", _claim_verdict_pointer(verdict_index), expected="scorecard_ready false", actual=ready)
    return _pass("CONS-HG3", "reason taxonomy matches scorecard readiness", _claim_verdict_pointer(verdict_index))


def _gate_hg4(
    *,
    resolver: PointerResolver,
    dgt_payload: Mapping[str, Any],
    high_impact_review_payload: Mapping[str, Any],
    claim_id: str,
    verdict_rows: Sequence[Mapping[str, Any]],
    graph_payload: Mapping[str, Any],
) -> ConsistencyFinding:
    terminal_id = terminal_node_id_for_claim_id(claim_id)
    nodes = graph_payload.get("nodes")
    if not isinstance(nodes, list):
        return _fail("CONS-HG4", "claim graph nodes are missing", f"{CLAIM_GRAPH_ARTIFACT}:$.nodes", expected="nodes", actual=nodes)
    node_index = _row_index([row for row in nodes if isinstance(row, Mapping)], "node_id", terminal_id)
    node = _row_by_key([row for row in nodes if isinstance(row, Mapping)], "node_id", terminal_id)
    if node is None:
        return _fail("CONS-HG4", "terminal claim graph node is missing", _terminal_node_pointer(node_index), expected=terminal_id, actual=None)
    verdict_index = _row_index(verdict_rows, "claim_id", claim_id)
    expected_source = _claim_verdict_pointer(verdict_index)
    if node.get("source_pointer") != expected_source or not resolver.resolves(expected_source):
        return _fail("CONS-HG4", "terminal node must point to claim verdict row", _terminal_node_pointer(node_index), expected=expected_source, actual=node.get("source_pointer"))
    d4_pointer = _pointer_from_cell(dgt_payload.get("d4_projection_ref")) or f"{DGT_ARTIFACT}:$.d4_projection"
    if d4_pointer != f"{DGT_ARTIFACT}:$.d4_projection" or not resolver.resolves(d4_pointer):
        return _fail("CONS-HG4", "DGT owner must expose a resolving d4 projection ref", f"{DGT_ARTIFACT}:$.d4_projection_ref", expected=f"{DGT_ARTIFACT}:$.d4_projection", actual=d4_pointer)
    not_claimed = dgt_payload.get("not_claimed")
    if not isinstance(not_claimed, list) or not not_claimed:
        return _fail("CONS-HG4", "DGT owner must keep a non-claim boundary", f"{DGT_ARTIFACT}:$.not_claimed", expected="non-empty not_claimed", actual=not_claimed)
    review_not_claimed = high_impact_review_payload.get("not_claimed")
    if not isinstance(review_not_claimed, list) or not review_not_claimed:
        return _fail("CONS-HG4", "high-impact review must keep a non-claim boundary", f"{HIGH_IMPACT_REVIEW_ARTIFACT}:$.not_claimed", expected="non-empty not_claimed", actual=review_not_claimed)
    nodes_by_id = {
        str(row.get("node_id")): row
        for row in nodes
        if isinstance(row, Mapping) and isinstance(row.get("node_id"), str)
    }
    projected = nodes_by_id.get("projected:discovery-gated-transformer")
    raw = nodes_by_id.get("raw:discovery-gated-transformer")
    if node.get("depends_on") != ["projected:discovery-gated-transformer"]:
        return _fail("CONS-HG4", "DGT terminal must depend on projected discovery node", _terminal_node_pointer(node_index), expected="projected:discovery-gated-transformer", actual=node.get("depends_on"))
    if not isinstance(projected, Mapping) or projected.get("depends_on") != ["raw:discovery-gated-transformer"]:
        return _fail("CONS-HG4", "DGT projected node must depend on raw evidence node", _terminal_node_pointer(node_index), expected="raw:discovery-gated-transformer", actual=projected)
    if isinstance(raw, Mapping) and raw.get("terminal_verdict") is not None:
        return _fail("CONS-HG4", "DGT raw node must not carry terminal verdict", _terminal_node_pointer(node_index), expected="raw terminal_verdict null", actual=raw)
    if isinstance(projected, Mapping) and projected.get("terminal_verdict") is not None:
        return _fail("CONS-HG4", "DGT projected node must not carry terminal verdict", _terminal_node_pointer(node_index), expected="projected terminal_verdict null", actual=projected)
    verdict_row = verdict_rows[verdict_index] if verdict_index is not None else None
    if isinstance(verdict_row, Mapping) and verdict_row.get("claim_verdict") == "accepted_positive_discovery":
        core_contracts = dgt_payload.get("d4_projection", {}).get("core_contracts") if isinstance(dgt_payload.get("d4_projection"), Mapping) else {}
        if not isinstance(core_contracts, Mapping) or core_contracts.get("claim_verdict_owner") != CORE_OWNER or core_contracts.get("claim_graph_owner") != CORE_OWNER:
            return _fail("CONS-HG4", "terminal verdict ownership must remain Core", f"{DGT_ARTIFACT}:$.d4_projection.core_contracts", expected=CORE_OWNER, actual=core_contracts)
    return _pass("CONS-HG4", "terminal graph path uses Core claim verdict row", _terminal_node_pointer(node_index))


def _gate_hg5(*, resolver: PointerResolver, discovery_payload: Mapping[str, Any]) -> ConsistencyFinding:
    coverage = discovery_payload.get("coverage_matrix")
    cells = coverage.get("cells") if isinstance(coverage, Mapping) else None
    if not isinstance(cells, list):
        return _fail("CONS-HG5", "coverage matrix cells are missing", f"{DISCOVERY_MAP_ARTIFACT}:$.coverage_matrix.cells", expected="cells", actual=cells)
    for index, cell in enumerate(cells):
        if not isinstance(cell, Mapping) or cell.get("component_id") != DGT_COMPONENT_ID:
            continue
        owner_pointer = cell.get("canonical_owner_pointer")
        if owner_pointer != f"{DGT_ARTIFACT}:$" or not resolver.resolves(str(owner_pointer)):
            return _fail("CONS-HG5", "DGT coverage owner pointer must resolve to DGT owner", _coverage_cell_pointer(index), expected=f"{DGT_ARTIFACT}:$", actual=owner_pointer)
        for field in ("discovery_level_pointer", "claim_verdict_pointer"):
            pointer = cell.get(field)
            if not isinstance(pointer, str) or not resolver.resolves(pointer):
                return _fail("CONS-HG5", f"DGT coverage {field} must resolve", _coverage_cell_pointer(index), expected="resolving artifact pointer", actual=pointer)
        return _pass("CONS-HG5", "coverage matrix DGT cell points to the DGT owner", _coverage_cell_pointer(index))
    return _fail("CONS-HG5", "coverage matrix lacks DGT cell", f"{DISCOVERY_MAP_ARTIFACT}:$.coverage_matrix.cells", expected=DGT_COMPONENT_ID, actual=None)


def _gate_hg6(root: Path, claim_id: str, verdict_rows: Sequence[Mapping[str, Any]]) -> ConsistencyFinding:
    verdict_index = _row_index(verdict_rows, "claim_id", claim_id)
    verdict_row = verdict_rows[verdict_index] if verdict_index is not None else None
    if verdict_row is None:
        return _fail("CONS-HG6", "claim verdict row is missing", _claim_verdict_pointer(verdict_index), expected="claim row", actual=None)
    scorecard_hash = _current_hash(root, QUALITY_SCORECARD_ARTIFACT)
    if verdict_row.get("claim_verdict") == "accepted_positive_discovery" and verdict_row.get("scorecard_hash") != scorecard_hash:
        return _fail("CONS-HG6", "scorecard artifact hash is stale", _claim_verdict_pointer(verdict_index), expected=scorecard_hash, actual=verdict_row.get("scorecard_hash"))
    for artifact in (DGT_ARTIFACT, CLAIM_GRAPH_ARTIFACT):
        expected_hash = _current_hash(root, artifact)
        recorded_hash = _fingerprint_source_hash(root, artifact)
        pointer = f"{HIGH_IMPACT_REVIEW_FINGERPRINT_ARTIFACT}:$.inputs.source_artifacts"
        if recorded_hash != expected_hash:
            return _fail("CONS-HG6", "high-impact review source artifact hash is stale", pointer, expected=f"{artifact}:{expected_hash}", actual=f"{artifact}:{recorded_hash}")
    return _pass("CONS-HG6", "artifact hashes are current", f"{HIGH_IMPACT_REVIEW_FINGERPRINT_ARTIFACT}:$.inputs.source_artifacts")


def audit_claim_artifact_consistency(
    root: Path,
    *,
    claim_id: str = DEFAULT_CLAIM_ID,
    generated_at: str | None = None,
) -> ClaimArtifactConsistencyReport:
    root = Path(root)
    timestamp = generated_at if generated_at is not None else "reusable"
    resolver = PointerResolver(root)
    verdict_rows = _load_jsonl_rows(root, CLAIM_VERDICTS_ARTIFACT)
    discovery_payload = load_validated_discovery_map_payload(root, artifact=DISCOVERY_MAP_ARTIFACT)
    discovery_rows_value = discovery_payload.get("rows")
    discovery_rows = [row for row in discovery_rows_value if isinstance(row, Mapping)] if isinstance(discovery_rows_value, list) else []
    graph_payload = _load_json_object(root, CLAIM_GRAPH_ARTIFACT)
    dgt_payload = _load_json_object(root, DGT_ARTIFACT)
    high_impact_review_payload = _load_json_object(root, HIGH_IMPACT_REVIEW_ARTIFACT)
    gates = (
        _gate_hg1(resolver=resolver, claim_id=claim_id, verdict_rows=verdict_rows, discovery_rows=discovery_rows),
        _gate_hg2(root, claim_id, verdict_rows),
        _gate_hg3(claim_id, verdict_rows),
        _gate_hg4(
            resolver=resolver,
            dgt_payload=dgt_payload,
            high_impact_review_payload=high_impact_review_payload,
            claim_id=claim_id,
            verdict_rows=verdict_rows,
            graph_payload=graph_payload,
        ),
        _gate_hg5(resolver=resolver, discovery_payload=discovery_payload),
        _gate_hg6(root, claim_id, verdict_rows),
    )
    status = "pass" if all(gate.status == "pass" for gate in gates) else "fail"
    return ClaimArtifactConsistencyReport(
        schema_id=SCHEMA_ID,
        artifact_id=ARTIFACT_ID,
        generated_at=timestamp,
        claim_id=claim_id,
        status=status,
        json_artifact=JSON_ARTIFACT,
        markdown_artifact=MARKDOWN_ARTIFACT,
        gates=gates,
    )


def render_claim_artifact_consistency_markdown(report: ClaimArtifactConsistencyReport) -> str:
    lines = [
        "# Claim Artifact Consistency Audit",
        "",
        f"- Generated at: `{report.generated_at}`",
        f"- Claim: `{report.claim_id}`",
        f"- Status: `{report.status}`",
        "",
        "| gate | status | pointer | reason | expected | actual |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for gate in report.gates:
        lines.append(
            f"| `{gate.gate_id}` | `{gate.status}` | `{gate.pointer}` | {gate.reason} | `{gate.expected}` | `{gate.actual}` |"
        )
    lines.append("")
    return "\n".join(lines)

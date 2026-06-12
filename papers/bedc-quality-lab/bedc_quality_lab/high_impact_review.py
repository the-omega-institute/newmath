"""Pointer-only high-impact review owner for the DGT bounded D4 claim."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.claim_verdict_reason import (
    POSITIVE_DISCOVERY_GATES_PASS,
    validate_claim_verdict_reason,
)
from bedc_quality_lab.discovery_compiler.pointers import pointer_value, resolve_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:high-impact-review"
ARTIFACT_ID = "bedc-quality-lab:high-impact-review"
JSON_ARTIFACT = "reports/canonical/high-impact-review.json"
MARKDOWN_ARTIFACT = "reports/canonical/high-impact-review.md"
DGT_CLAIM_ID = "claim:discovery-gated-transformer"
DGT_REPORT = "discovery-gated-transformer"
DGT_ARTIFACT = "reports/canonical/discovery-gated-transformer.json"
MODEL_COMPARISON_ARTIFACT = "reports/canonical/model-comparison.json"
CLAIM_GRAPH_ARTIFACT = "reports/canonical/claim_graph.json"
DGT_REVIEW_ROW_POINTER = f"{JSON_ARTIFACT}:$.review_rows[0]"
NOT_CLAIMED = (
    "Bounded D4 prototype only.",
    "No production deployment authority is claimed.",
    "No global model superiority claim is made.",
    "No LLM replacement claim is made.",
    "No universal training recipe is claimed.",
    "No full BEDC closure is claimed.",
)
HIR_GATE_IDS = tuple(f"HIR-HG{index}" for index in range(1, 11))
REQUIRED_ROW_KEYS = frozenset(
    {
        "claim_id",
        "status",
        "review_level",
        "review_scope",
        "ledger_pointer",
        "claim_pointer",
        "hardgate_pointer",
        "not_claimed_pointer",
        "reason",
    }
)


def _artifact_path(root: Path, artifact: str) -> Path:
    return root / artifact


def _load_json(root: Path, artifact: str) -> Mapping[str, Any]:
    path = _artifact_path(root, artifact)
    if not path.exists():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}
    return payload if isinstance(payload, Mapping) else {}


def _status(ok: bool, reason: str, pointer: str) -> dict[str, Any]:
    return {
        "status": "pass" if ok else "fail",
        "reason": reason if ok else f"{reason}; fail-closed",
        "evidence_pointer": pointer,
    }


def _text(value: Any) -> str:
    if isinstance(value, (dict, list, tuple)):
        return json.dumps(value, sort_keys=True).lower()
    return str(value).lower()


def _claim_surface(dgt: Mapping[str, Any]) -> dict[str, Any]:
    def clean(value: Any) -> Any:
        if isinstance(value, Mapping):
            return {
                key: clean(cell)
                for key, cell in value.items()
                if key not in {"not_claimed", "forbidden_terms", "forbidden_claim_term_audit", "scope_seal"}
            }
        if isinstance(value, list):
            return [clean(cell) for cell in value]
        return value

    return {
        "claim": clean(dgt.get("claim")),
        "positive_claim": clean(dgt.get("positive_claim")),
        "d4_projection": clean(dgt.get("d4_projection")),
        "discovery_map_signal": clean(dgt.get("discovery_map_signal")),
    }


def _not_claimed_has(value: Any, token: str) -> bool:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes)):
        return False
    return token in " ".join(str(item).lower() for item in value)


def _model_row(model_comparison: Mapping[str, Any], model_id: str) -> Mapping[str, Any]:
    models = model_comparison.get("models")
    if not isinstance(models, list):
        return {}
    for row in models:
        if isinstance(row, Mapping) and row.get("model_id") == model_id:
            return row
    return {}


def _metric_number(model_row: Mapping[str, Any], metric: str) -> float | None:
    metrics = model_row.get("metrics")
    if not isinstance(metrics, Mapping):
        return None
    cell = metrics.get(metric)
    if not isinstance(cell, Mapping) or cell.get("status") != "resolved":
        return None
    value = cell.get("value")
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    return float(value)


def _payload_pointer_value(payload: Mapping[str, Any], artifact_pointer: str) -> Any:
    prefix = f"{JSON_ARTIFACT}:"
    if not artifact_pointer.startswith(prefix):
        return None
    pointer = artifact_pointer.removeprefix(prefix)
    if pointer == "$":
        return payload
    return pointer_value(payload, pointer)


def _pointer_resolves(root: Path, payload: Mapping[str, Any], artifact_pointer: str) -> bool:
    if artifact_pointer.startswith(f"{JSON_ARTIFACT}:"):
        return _payload_pointer_value(payload, artifact_pointer) is not None
    if artifact_pointer == f"{CLAIM_GRAPH_ARTIFACT}:$.nodes":
        claim_graph = _load_json(root, CLAIM_GRAPH_ARTIFACT)
        return isinstance(claim_graph.get("nodes"), list)
    return resolve_artifact_pointer(root, artifact_pointer) is not None


def _all_mc_gates_pass(model_comparison: Mapping[str, Any]) -> bool:
    gates = model_comparison.get("hardgates")
    return isinstance(gates, Mapping) and all(
        isinstance(row, Mapping) and row.get("status") == "pass" for row in gates.values()
    )


def _dgt_graph_path_ready(claim_graph: Mapping[str, Any]) -> bool:
    nodes = claim_graph.get("nodes")
    if not isinstance(nodes, list):
        return False
    by_id = {node.get("node_id"): node for node in nodes if isinstance(node, Mapping)}
    raw = by_id.get("raw:discovery-gated-transformer")
    projected = by_id.get("projected:discovery-gated-transformer")
    terminal = by_id.get("terminal:discovery-gated-transformer")
    return (
        isinstance(raw, Mapping)
        and isinstance(projected, Mapping)
        and isinstance(terminal, Mapping)
        and raw.get("node_type") == "raw_evidence"
        and projected.get("node_type") == "projected_discovery"
        and terminal.get("node_type") == "terminal_claim"
        and projected.get("depends_on") == ["raw:discovery-gated-transformer"]
        and terminal.get("depends_on") == ["projected:discovery-gated-transformer"]
        and raw.get("terminal_verdict") is None
        and projected.get("terminal_verdict") is None
    )


def evaluate_high_impact_review_gates(root: Path, claim_id: str) -> dict[str, Any]:
    dgt = _load_json(root, DGT_ARTIFACT)
    model_comparison = _load_json(root, MODEL_COMPARISON_ARTIFACT)
    claim_graph = _load_json(root, CLAIM_GRAPH_ARTIFACT)
    dgt_not_claimed = dgt.get("not_claimed")
    claim_surface = _claim_surface(dgt)
    dgt_row = _model_row(model_comparison, "dgt")
    base_row = _model_row(model_comparison, "base_transformer")
    matched_row = _model_row(model_comparison, "matched_random_structural_control")
    dgt_quality = _metric_number(dgt_row, "quality_q")
    base_quality = _metric_number(base_row, "quality_q")
    dgt_uer_reduction = _metric_number(dgt_row, "UER_reduction")
    matched_uer_reduction = _metric_number(matched_row, "UER_reduction")
    matched_shift = _metric_number(matched_row, "classifier_shift_count")
    return {
        "HIR-HG1": _status(
            claim_id == DGT_CLAIM_ID
            and dgt.get("artifact_id") == "bedc-quality-lab:discovery-gated-transformer"
            and dgt.get("model_id") == "discovery-gated-transformer"
            and isinstance(dgt.get("d4_projection"), Mapping)
            and dgt["d4_projection"].get("discovery_level") == "D4"
            and dgt["d4_projection"].get("readiness") == "ready",
            "DGT row is a bounded D4 projection",
            f"{DGT_ARTIFACT}:$.d4_projection",
        ),
        "HIR-HG2": _status(
            _not_claimed_has(dgt_not_claimed, "bounded")
            and _not_claimed_has(NOT_CLAIMED, "bounded")
            and _not_claimed_has(NOT_CLAIMED, "production")
            and _not_claimed_has(NOT_CLAIMED, "global")
            and _not_claimed_has(NOT_CLAIMED, "llm replacement")
            and _not_claimed_has(NOT_CLAIMED, "universal"),
            "non-claim boundary excludes production, global superiority, LLM replacement, and universal recipe",
            f"{JSON_ARTIFACT}:$.not_claimed",
        ),
        "HIR-HG3": _status(
            "production" not in _text(claim_surface) and "deployment authority" not in _text(claim_surface),
            "DGT positive claim cell contains no production authority claim",
            f"{DGT_ARTIFACT}:$.d4_projection",
        ),
        "HIR-HG4": _status(
            "llm replacement" not in _text(claim_surface) and "replace llm" not in _text(claim_surface),
            "DGT owner contains no LLM replacement claim",
            f"{DGT_ARTIFACT}:$",
        ),
        "HIR-HG5": _status(
            "global superiority" not in _text(claim_surface) and "universal superiority" not in _text(claim_surface),
            "DGT owner contains no global superiority claim",
            f"{DGT_ARTIFACT}:$",
        ),
        "HIR-HG6": _status(
            model_comparison.get("status") == "ready"
            and model_comparison.get("readiness", {}).get("status") == "ready"
            and _all_mc_gates_pass(model_comparison),
            "model comparison is ready and all MC hardgates pass",
            f"{MODEL_COMPARISON_ARTIFACT}:$.hardgates",
        ),
        "HIR-HG7": _status(
            dgt_quality is not None and base_quality is not None and dgt_quality > base_quality,
            "DGT quality_q exceeds the base transformer control",
            f"{MODEL_COMPARISON_ARTIFACT}:$.hardgates.MC-HG7",
        ),
        "HIR-HG8": _status(
            dgt_uer_reduction is not None
            and matched_uer_reduction is not None
            and dgt_uer_reduction > matched_uer_reduction,
            "DGT UER reduction exceeds matched-random structural control",
            f"{MODEL_COMPARISON_ARTIFACT}:$.hardgates.MC-HG8",
        ),
        "HIR-HG9": _status(
            matched_shift == 0.0,
            "matched-random structural control keeps classifier_shift_count at zero",
            f"{MODEL_COMPARISON_ARTIFACT}:$.hardgates.MC-HG9",
        ),
        "HIR-HG10": _status(
            _dgt_graph_path_ready(claim_graph),
            "claim graph contains DGT raw to projected to terminal ancestry",
            f"{CLAIM_GRAPH_ARTIFACT}:$.nodes",
        ),
    }


def _review_status(hardgates: Mapping[str, Mapping[str, Any]]) -> str:
    return "pass" if all(row.get("status") == "pass" for row in hardgates.values()) else "fail"


def _review_reason(status: str) -> str:
    return POSITIVE_DISCOVERY_GATES_PASS if status == "pass" else "high-impact-review-required"


def _build_dgt_review_row(hardgates: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    status = _review_status(hardgates)
    return {
        "claim_id": DGT_CLAIM_ID,
        "status": status,
        "review_level": "bounded-D4-terminal-gate",
        "review_scope": "DGT bounded deterministic toy D4 positive-discovery terminal promotion only",
        "ledger_pointer": DGT_REVIEW_ROW_POINTER,
        "claim_pointer": f"{DGT_ARTIFACT}:$.d4_projection",
        "hardgate_pointer": f"{JSON_ARTIFACT}:$.hardgates",
        "not_claimed_pointer": f"{JSON_ARTIFACT}:$.not_claimed",
        "reason": _review_reason(status),
    }


def build_high_impact_review_payload(root: Path, generated_at: str, seed: int = 1131) -> dict[str, Any]:
    hardgates = evaluate_high_impact_review_gates(root, DGT_CLAIM_ID)
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "seed": seed,
        "source_artifacts": {
            "dgt": DGT_ARTIFACT,
            "model_comparison": MODEL_COMPARISON_ARTIFACT,
            "claim_graph": CLAIM_GRAPH_ARTIFACT,
        },
        "review_rows": [_build_dgt_review_row(hardgates)],
        "hardgates": hardgates,
        "not_claimed": list(NOT_CLAIMED),
    }
    errors = validate_high_impact_review_payload(payload, root)
    if errors:
        raise ValueError("; ".join(errors))
    return payload


def validate_high_impact_review_payload(payload: Mapping[str, Any], root: Path) -> list[str]:
    errors: list[str] = []
    if payload.get("schema_id") != SCHEMA_ID:
        errors.append("schema_id mismatch")
    if payload.get("artifact_id") != ARTIFACT_ID:
        errors.append("artifact_id mismatch")
    if not isinstance(payload.get("generated_at"), str) or not payload.get("generated_at"):
        errors.append("generated_at must be non-empty")
    if payload.get("seed") != 1131:
        errors.append("seed must be 1131")
    source_artifacts = payload.get("source_artifacts")
    if not isinstance(source_artifacts, Mapping) or set(source_artifacts) != {"dgt", "model_comparison", "claim_graph"}:
        errors.append("source_artifacts mismatch")
    hardgates = payload.get("hardgates")
    if not isinstance(hardgates, Mapping) or set(hardgates.keys()) != set(HIR_GATE_IDS):
        errors.append("hardgates must contain HIR-HG1..10")
        hardgates = {}
    for gate_id in HIR_GATE_IDS:
        gate = hardgates.get(gate_id) if isinstance(hardgates, Mapping) else None
        if not isinstance(gate, Mapping):
            errors.append(f"{gate_id} must be an object")
            continue
        if set(gate) != {"status", "reason", "evidence_pointer"}:
            errors.append(f"{gate_id} field set mismatch")
        if gate.get("status") not in {"pass", "fail"}:
            errors.append(f"{gate_id} status mismatch")
        pointer = gate.get("evidence_pointer")
        if not isinstance(pointer, str) or not _pointer_resolves(root, payload, pointer):
            errors.append(f"{gate_id} evidence pointer does not resolve")
    rows = payload.get("review_rows")
    if not isinstance(rows, list) or len(rows) != 1 or not all(isinstance(row, Mapping) for row in rows):
        errors.append("review_rows must contain exactly one DGT row")
        rows = []
    for row in rows:
        if frozenset(row) != REQUIRED_ROW_KEYS:
            errors.append("review row field set mismatch")
            continue
        if row.get("claim_id") != DGT_CLAIM_ID:
            errors.append("review row claim_id mismatch")
        status = row.get("status")
        expected_status = _review_status(hardgates) if isinstance(hardgates, Mapping) else "fail"
        if status != expected_status:
            errors.append("review row status must match HIR hardgates")
        if row.get("reason") != _review_reason(str(status)):
            errors.append("review row reason mismatch")
        if status == "pass":
            try:
                validate_claim_verdict_reason({"reason": row.get("reason")})
            except ValueError as exc:
                errors.append(str(exc))
        for key in ("claim_pointer", "hardgate_pointer", "not_claimed_pointer"):
            pointer = row.get(key)
            if not isinstance(pointer, str) or not _pointer_resolves(root, payload, pointer):
                errors.append(f"review row pointer does not resolve: {key}")
        if row.get("ledger_pointer") != DGT_REVIEW_ROW_POINTER:
            errors.append("review row ledger_pointer mismatch")
    if list(payload.get("not_claimed", ())) != list(NOT_CLAIMED):
        errors.append("not_claimed boundary mismatch")
    return errors


def high_impact_review_dgt_gate(root: Path) -> dict[str, Any]:
    payload = _load_json(root, JSON_ARTIFACT)
    if not payload:
        return {
            "status": "fail",
            "reason": "high-impact-review-required",
            "ledger_pointer": f"{JSON_ARTIFACT}:$.review_rows",
        }
    errors = validate_high_impact_review_payload(payload, root)
    if errors:
        return {
            "status": "fail",
            "reason": "high-impact-review-required",
            "ledger_pointer": f"{JSON_ARTIFACT}:$",
            "errors": errors,
        }
    rows = payload.get("review_rows")
    row = rows[0] if isinstance(rows, list) and rows and isinstance(rows[0], Mapping) else {}
    hardgates = payload.get("hardgates")
    if row.get("claim_id") == DGT_CLAIM_ID and row.get("status") == "pass" and _review_status(hardgates) == "pass":
        return {
            "status": "pass",
            "reason": POSITIVE_DISCOVERY_GATES_PASS,
            "ledger_pointer": DGT_REVIEW_ROW_POINTER,
        }
    return {
        "status": "fail",
        "reason": "high-impact-review-required",
        "ledger_pointer": DGT_REVIEW_ROW_POINTER,
    }


def render_high_impact_review_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# High Impact Review",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Schema: `{payload['schema_id']}`",
        "",
        "## Review Rows",
        "",
        "| claim | status | reason | ledger |",
        "| --- | --- | --- | --- |",
    ]
    for row in payload["review_rows"]:
        lines.append(
            f"| `{row['claim_id']}` | `{row['status']}` | `{row['reason']}` | `{row['ledger_pointer']}` |"
        )
    lines.extend(["", "## Hardgates", "", "| gate | status | evidence | reason |", "| --- | --- | --- | --- |"])
    for gate_id in HIR_GATE_IDS:
        gate = payload["hardgates"][gate_id]
        lines.append(f"| `{gate_id}` | `{gate['status']}` | `{gate['evidence_pointer']}` | {gate['reason']} |")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)

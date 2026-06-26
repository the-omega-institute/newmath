#!/usr/bin/env python3
"""Build the negative-witness mutation ledger sidecar."""

from __future__ import annotations

from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.discovery_compiler.pointers import pointer_value


LEDGER_SCHEMA_ID = "bedc-quality-lab:negative-witness-mutation-ledger"
LEDGER_ARTIFACT_ID = "bedc-quality-lab:negative-witness-mutation-ledger"
LEDGER_JSON_ARTIFACT = "reports/canonical/negative_witness_mutation_ledger.json"
LINEAGE_GRAPH_ARTIFACT = "reports/canonical/model_mutation_lineage_graph.md"
DGT_REPORT_ARTIFACT = "reports/canonical/dgt_mutation_report.json"
PRODUCER = "scripts/run_negative_witness_mutation_ledger.py"
CANONICAL_ROLE = "sidecar_not_in_CANONICAL_REPORTS"

FORBIDDEN_KEYS = (
    "terminal_verdict",
    "issue",
    "issue_id",
    "issue_label",
    "route",
    "route_label",
    "raw_metrics",
    "metrics",
    "candidate_evidence_body",
    "classifier_reason",
    "classifier_reasons",
    "bedc_gap_field",
    "regression_test",
    "what_was_learned",
    "negative_witness_mutations",
    "rows",
)

ENTRY_KEYS = (
    "mutation_id",
    "witness_kind",
    "source_artifact",
    "source_pointer",
    "target_module",
    "lineage_parent",
    "status",
    "reason",
)


def _mutation_specs() -> tuple[dict[str, str], ...]:
    return (
        {
            "witness_kind": "score_margin_shortcut",
            "source": "reports/runs/a1-canonical/claim_capsule.json:$.run_local.negative_witness[0]",
            "target_module": "residualized_h_path",
        },
        {
            "witness_kind": "scale_leakage",
            "source": "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json:$.run_local.negative_witness[0]",
            "target_module": "scale_invariant_norm",
        },
        {
            "witness_kind": "control_positive",
            "source": "reports/canonical/discovery_negative_witnesses.json:$.witnesses[1]",
            "target_module": "control_separated_route",
        },
        {
            "witness_kind": "benefit_debt_tradeoff",
            "source": "reports/canonical/discovery_negative_witnesses.json:$.witnesses[6]",
            "target_module": "constrained_lagrangian_loss",
        },
        {
            "witness_kind": "single_threshold_escape",
            "source": "runs/single_threshold_escape_witness.json:$.single_threshold_basis[0]",
            "target_module": "threshold_frontier_loss",
        },
        {
            "witness_kind": "forbidden_column",
            "source": "reports/canonical/discovery_negative_witnesses.json:$.witnesses[5]",
            "target_module": "inference_audit_layer",
        },
        {
            "witness_kind": "hidden_debt",
            "source": "reports/canonical/discovery_negative_witnesses.json:$.witnesses[2]",
            "target_module": "explicit_ledger_head",
        },
        {
            "witness_kind": "mechanism_blocked",
            "source": "reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence",
            "target_module": "mechanism_seeking_module",
        },
    )


def _split_artifact_pointer(cell: str) -> tuple[str, str]:
    if ":$" not in cell:
        return cell, ""
    return cell.split(":", 1)


def _artifact_payload(root: Path, artifact: str) -> Any:
    path = root / artifact
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None


def _resolve_artifact_pointer(root: Path, artifact: str, pointer: str) -> Any:
    payload = _artifact_payload(root, artifact)
    if payload is None:
        return None
    if pointer == "$":
        return payload
    return pointer_value(payload, pointer)


def _ensure_source_sidecars(root: Path, generated_at: str) -> None:
    from scripts.run_single_threshold_escape_witness import build_sidecar, write_sidecar
    from scripts.run_single_threshold_escape_witness import THRESHOLD_ARTIFACT

    if not (root / THRESHOLD_ARTIFACT).exists():
        return
    write_sidecar(root, build_sidecar(root=root, generated_at=generated_at))


def _entry_for_spec(root: Path, spec: Mapping[str, str], index: int) -> dict[str, str]:
    source_artifact, source_pointer = _split_artifact_pointer(spec["source"])
    mutation_id = f"{spec['target_module']}_mutation"
    lineage_parent = f"{source_artifact}:{source_pointer}"
    source_resolves = _resolve_artifact_pointer(root, source_artifact, source_pointer) is not None
    status = "ready" if source_resolves else "blocked"
    return {
        "mutation_id": mutation_id,
        "witness_kind": spec["witness_kind"],
        "source_artifact": source_artifact,
        "source_pointer": source_pointer,
        "target_module": spec["target_module"],
        "lineage_parent": lineage_parent if index == 0 else f"{LEDGER_JSON_ARTIFACT}:$.entries[{index - 1}]",
        "status": status,
        "reason": "none" if status == "ready" else "source_pointer_unresolved",
    }


def _lineage_parent_resolves(root: Path, payload: Mapping[str, Any], entry: Mapping[str, Any], index: int) -> bool:
    parent = entry.get("lineage_parent")
    if not isinstance(parent, str) or ":$" not in parent:
        return False
    artifact, pointer = _split_artifact_pointer(parent)
    if artifact == LEDGER_JSON_ARTIFACT:
        return pointer_value(payload, pointer) is not None
    if index == 0 and artifact == entry.get("source_artifact") and pointer == entry.get("source_pointer"):
        return _resolve_artifact_pointer(root, artifact, pointer) is not None
    return _resolve_artifact_pointer(root, artifact, pointer) is not None


def _forbidden_hits(value: Any, path: str = "$") -> list[str]:
    hits: list[str] = []
    if isinstance(value, Mapping):
        for key, cell in value.items():
            if key in FORBIDDEN_KEYS:
                hits.append(f"{path}.{key}")
            hits.extend(_forbidden_hits(cell, f"{path}.{key}"))
    elif isinstance(value, list):
        for index, cell in enumerate(value):
            hits.extend(_forbidden_hits(cell, f"{path}[{index}]"))
    return hits


def _audit_mutation_ledger(root: Path, payload: dict[str, Any]) -> dict[str, Any]:
    entries = payload.get("entries")
    if not isinstance(entries, list):
        entries = []
    expected = {spec["witness_kind"]: spec["target_module"] for spec in _mutation_specs()}
    actual = {
        entry.get("witness_kind"): entry.get("target_module")
        for entry in entries
        if isinstance(entry, Mapping)
    }
    source_failures = [
        entry.get("witness_kind", "")
        for entry in entries
        if isinstance(entry, Mapping)
        and _resolve_artifact_pointer(root, str(entry.get("source_artifact", "")), str(entry.get("source_pointer", "")))
        is None
    ]
    parent_failures = [
        entry.get("witness_kind", "")
        for index, entry in enumerate(entries)
        if isinstance(entry, Mapping) and not _lineage_parent_resolves(root, payload, entry, index)
    ]
    schema_failures = [
        str(entry.get("witness_kind", index))
        for index, entry in enumerate(entries)
        if not isinstance(entry, Mapping) or tuple(entry.keys()) != ENTRY_KEYS
    ]
    forbidden_hits = _forbidden_hits(payload)
    gates = {
        "MUT-HG1": {"status": "pass" if not source_failures else "fail", "failures": source_failures},
        "MUT-HG2": {"status": "pass" if actual == expected else "fail", "expected": expected, "actual": actual},
        "MUT-HG3": {"status": "pass" if not parent_failures else "fail", "failures": parent_failures},
        "MUT-HG4": {"status": "pass" if not forbidden_hits else "fail", "hits": forbidden_hits},
        "MUT-HG5": {"status": "pass", "ledger_pointer": f"{LEDGER_JSON_ARTIFACT}:$.entries"},
    }
    if schema_failures:
        gates["MUT-HG2"] = {**gates["MUT-HG2"], "status": "fail", "schema_failures": schema_failures}
    status = "ready" if all(gate["status"] == "pass" for gate in gates.values()) else "blocked"
    return {
        "status": status,
        "blocked_entries": sorted(
            {
                *source_failures,
                *parent_failures,
                *schema_failures,
                *(["forbidden_key"] if forbidden_hits else []),
            }
        ),
        "hardgates": gates,
    }


def _build_mutation_ledger(root: Path, generated_at: str) -> dict[str, Any]:
    _ensure_source_sidecars(root, generated_at)
    entries = [_entry_for_spec(root, spec, index) for index, spec in enumerate(_mutation_specs())]
    payload: dict[str, Any] = {
        "schema_id": LEDGER_SCHEMA_ID,
        "artifact_id": LEDGER_ARTIFACT_ID,
        "producer": PRODUCER,
        "generated_at": generated_at,
        "status": "ready",
        "entry_count": len(entries),
        "entries": entries,
        "hardgates": {},
        "forbidden_keys": list(FORBIDDEN_KEYS),
    }
    audit = _audit_mutation_ledger(root, payload)
    payload["status"] = audit["status"]
    payload["blocked_entries"] = audit["blocked_entries"]
    payload["hardgates"] = audit["hardgates"]
    return payload


def _render_lineage_graph(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Model Mutation Lineage Graph",
        "",
        f"- Ledger entries: `{LEDGER_JSON_ARTIFACT}:$.entries`",
        f"- Ledger status: `{LEDGER_JSON_ARTIFACT}:$.status`",
        f"- Entry count: `{LEDGER_JSON_ARTIFACT}:$.entry_count`",
        "",
        "| child entry pointer | lineage parent cell pointer |",
        "| --- | --- |",
    ]
    entries = payload.get("entries", [])
    if isinstance(entries, list):
        for index, entry in enumerate(entries):
            if not isinstance(entry, Mapping):
                continue
            lines.append(
                "| "
                f"`{LEDGER_JSON_ARTIFACT}:$.entries[{index}]` | "
                f"`{LEDGER_JSON_ARTIFACT}:$.entries[{index}].lineage_parent` |"
            )
    lines.append("")
    return "\n".join(lines)


def _build_dgt_mutation_report(payload: Mapping[str, Any]) -> dict[str, Any]:
    blocked = [
        entry.get("mutation_id")
        for entry in payload.get("entries", [])
        if isinstance(entry, Mapping) and entry.get("status") == "blocked"
    ]
    return {
        "schema_id": "bedc-quality-lab:dgt-mutation-report",
        "artifact_id": "bedc-quality-lab:dgt-mutation-report",
        "producer": PRODUCER,
        "generated_at": payload.get("generated_at"),
        "canonical_role": "non_owner_pointer_redirect",
        "ledger": {"artifact": LEDGER_JSON_ARTIFACT, "pointer": "$.entries"},
        "graph": {"artifact": LINEAGE_GRAPH_ARTIFACT, "pointer": "$"},
        "status": payload.get("status"),
        "entry_count": payload.get("entry_count", 0),
        "blocked_count": len(blocked),
        "blocked_mutation_ids": blocked,
        "mut_hg_summary": {
            gate_id: gate.get("status")
            for gate_id, gate in payload.get("hardgates", {}).items()
            if isinstance(gate, Mapping)
        },
    }


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _reusable_generated_at(root: Path) -> str | None:
    payload = _artifact_payload(root, LEDGER_JSON_ARTIFACT)
    if isinstance(payload, Mapping):
        generated_at = payload.get("generated_at")
        if isinstance(generated_at, str) and generated_at:
            return generated_at
    return None


def write_negative_witness_mutation_ledger(
    *,
    root: Path = ROOT,
    generated_at: str | None = None,
) -> dict[str, Any]:
    timestamp = generated_at or _reusable_generated_at(root) or datetime.now(timezone.utc).isoformat()
    payload = _build_mutation_ledger(root, timestamp)
    graph = _render_lineage_graph(payload)
    dgt_report = _build_dgt_mutation_report(payload)
    report_hits = _forbidden_hits(dgt_report)
    if report_hits:
        raise ValueError(f"DGT mutation report contains forbidden keys: {report_hits}")
    _write_json(root / LEDGER_JSON_ARTIFACT, payload)
    _write_text(root / LINEAGE_GRAPH_ARTIFACT, graph)
    _write_json(root / DGT_REPORT_ARTIFACT, dgt_report)
    return payload


def main() -> None:
    write_negative_witness_mutation_ledger(root=ROOT)


if __name__ == "__main__":
    main()

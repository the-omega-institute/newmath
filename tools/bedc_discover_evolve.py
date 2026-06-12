#!/usr/bin/env python3
"""Run-local discovery evolve wrapper."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Any, Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]
LAB_ROOT = REPO_ROOT / "papers" / "bedc-quality-lab"
if str(LAB_ROOT) not in sys.path:
    sys.path.insert(0, str(LAB_ROOT))

from bedc_quality_lab.discovery_compiler import build_architecture_mutation_drafts, require_witness_basis


DISCOVERY_MAP_ARTIFACT = "reports/canonical/discovery_map.json"
NEGATIVE_WITNESS_SUMMARY_ARTIFACT = "reports/canonical/discovery_negative_witness_summary.json"
INDEX_ARTIFACT = "reports/canonical/index.json"


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    payload = json.loads(path.read_text(encoding="utf-8"))
    return payload if isinstance(payload, dict) else {}


def _generated_at(root: Path, explicit: str | None) -> str:
    if explicit:
        return explicit
    index = _load_json(root / INDEX_ARTIFACT)
    value = index.get("generated_at")
    if isinstance(value, str) and value:
        return value
    return datetime.now(timezone.utc).isoformat()


def _build_payload(root: Path, generated_at: str) -> dict[str, Any]:
    discovery_map = _load_json(root / DISCOVERY_MAP_ARTIFACT)
    negative_summary = _load_json(root / NEGATIVE_WITNESS_SUMMARY_ARTIFACT)
    return build_architecture_mutation_drafts(root, generated_at, [], discovery_map, negative_summary)


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _render_markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# Architecture Mutation Drafts",
        "",
        f"- Schema: `{payload['schema_id']}`",
        f"- Canonical role: `{payload['canonical_role']}`",
        f"- Status: `{payload['status']}`",
        f"- Rows: `{payload['row_count']}`",
        f"- Queue admissible: `{payload['queue_admissible_count']}`",
        "",
        "| draft | status | witness basis | claim capsule | hardgate |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in payload["rows"]:
        lines.append(
            "| "
            f"`{row['draft_id']}` | "
            f"`{row['status']}` | "
            f"`{row['witness_basis_pointer']}` | "
            f"`{row['claim_capsule_pointer']}` | "
            f"`{row['hardgate_pointer']}` |"
        )
    lines.append("")
    return "\n".join(lines)


def _enqueue(payload: dict[str, Any], *, root: Path) -> dict[str, Any]:
    candidates = []
    for row in payload.get("queue_admissible_rows", []):
        if not isinstance(row, dict):
            continue
        gate = require_witness_basis(row, root)
        if gate.status != "pass":
            continue
        candidates.append(
            {
                "kind": "architecture_mutation",
                "title": f"Architecture mutation draft {row['draft_id']}",
                "claim": "Compiler-owned architecture mutation draft with a resolvable witness basis pointer.",
                "source": "bedc_discover_evolve",
                "landing_kind": "existing_chapter_ledger_row",
                "local_inputs": ["papers/bedc/parts/project_governance/theory_amendment_policy.tex"],
                "fit_score": 7,
                "novelty": 6,
                "witness_basis_pointer": row["witness_basis_pointer"],
                "claim_capsule_pointer": row["claim_capsule_pointer"],
                "architecture_mutation_draft": row,
            }
        )
    if not candidates:
        return {"ok": True, "accepted_count": 0, "appended_ids": [], "rejected_count": 0}

    bedc_deep = REPO_ROOT / "tools" / "bedc-deep"
    if str(bedc_deep) not in sys.path:
        sys.path.insert(0, str(bedc_deep))
    import board_spawn

    result = board_spawn.spawn_from_candidates(codex_candidates=candidates, oracle_candidates=[])
    return {
        "ok": result.ok,
        "accepted_count": len(result.accepted),
        "appended_ids": result.appended_ids,
        "rejected_count": len(result.rejected),
        "error": result.error,
        "error_kind": result.error_kind,
    }


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=str(LAB_ROOT), help="BEDC quality lab root")
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--output-json", default=None, help="write run-local JSON payload")
    parser.add_argument("--output-md", default=None, help="write run-local Markdown payload")
    parser.add_argument("--enqueue", action="store_true", help="send queue-admissible rows through BOARD admission")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    root = Path(args.root).resolve()
    generated_at = _generated_at(root, args.generated_at)
    payload = _build_payload(root, generated_at)
    if args.output_json:
        _write_json(Path(args.output_json), payload)
    if args.output_md:
        md_path = Path(args.output_md)
        md_path.parent.mkdir(parents=True, exist_ok=True)
        md_path.write_text(_render_markdown(payload), encoding="utf-8")
    if args.enqueue:
        payload["enqueue_result"] = _enqueue(payload, root=root)
    if not args.output_json and not args.output_md:
        print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

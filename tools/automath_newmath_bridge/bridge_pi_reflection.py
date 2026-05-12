#!/usr/bin/env python3
"""Deterministic PI reflection for the Automath -> NewMath bridge.

The PI layer converts global bridge feedback into durable, reviewable actions.
It does not edit BEDC Lean or paper content. Automatic actions are limited to
safe bridge-control decisions such as requesting sharper continuation packets,
cooling duplicate rows, and recording when evidence should remain evidence-only.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
DEFAULT_ACK = REPO_ROOT / "docs" / "bridge" / "automath-newmath-ack.jsonl"
DEFAULT_STATUS = REPO_ROOT / "docs" / "bridge" / "automath-newmath-production-status.md"
DEFAULT_GATE_RESULTS = SCRIPT_DIR / "out" / "bridge_gate_results.jsonl"
DEFAULT_REPORT = REPO_ROOT / "docs" / "bridge" / "automath-newmath-pi-reflection.md"
DEFAULT_ACTIONS = REPO_ROOT / "docs" / "bridge" / "automath-newmath-pi-actions.jsonl"
DEFAULT_REFINEMENT = REPO_ROOT / "docs" / "bridge" / "automath-newmath-refinement-queue.jsonl"


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            text = line.strip()
            if not text:
                continue
            try:
                item = json.loads(text)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_no}: invalid JSONL row: {exc}") from exc
            if isinstance(item, dict):
                rows.append(item)
    return rows


def _write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def _source(record: dict[str, Any]) -> str:
    return f"{record.get('source_repo')}@{record.get('source_branch_or_ref')}:{record.get('source_path')}"


def _unique_sources(rows: list[dict[str, Any]], reason: str, *, limit: int = 12) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for row in rows:
        if str(row.get("reason") or "") != reason:
            continue
        source = _source(row)
        if source in seen:
            continue
        seen.add(source)
        out.append(source)
        if len(out) >= limit:
            break
    return out


def _gate_summary(gate_rows: list[dict[str, Any]]) -> dict[str, int]:
    counts: Counter[str] = Counter()
    for row in gate_rows:
        direction = str(row.get("bridge_direction") or "unknown")
        status = str(row.get("gate_status") or "unknown")
        counts[f"{direction}:{status}"] += 1
    return dict(sorted(counts.items()))


def build_actions(
    ack_rows: list[dict[str, Any]],
    gate_rows: list[dict[str, Any]],
    *,
    no_specific_threshold: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    reason_counts = Counter(str(row.get("reason") or "none") for row in ack_rows)
    status_counts = Counter(str(row.get("status") or "unknown") for row in ack_rows)
    by_reason: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in ack_rows:
        by_reason[str(row.get("reason") or "none")].append(row)

    actions: list[dict[str, Any]] = []
    refinements: list[dict[str, Any]] = []

    if reason_counts.get("no_specific_board_claim", 0) >= no_specific_threshold:
        sources = by_reason["no_specific_board_claim"]
        actions.append(
            {
                "schema_version": "automath-newmath-pi-action-v1",
                "action_id": "pi:newmath:expand_specific_board_claims",
                "action_type": "request_specific_continuation_packets",
                "severity": "high",
                "trigger_reason": "no_specific_board_claim",
                "trigger_count": reason_counts["no_specific_board_claim"],
                "automatic_effect": "refinement_queue_written",
                "safe_to_apply_automatically": True,
                "policy": (
                    "Do not resubmit vague paper_claim rows to BEDC BOARD. Require "
                    "source theorem or paper labels, a concrete BEDC carrier/classifier/"
                    "obstruction/proof-obligation landing object, and expected minimal "
                    "BEDC delta before retry."
                ),
                "source_paths": [str(row.get("source_path") or "") for row in sources[:12]],
            }
        )
        for row in sources:
            refinements.append(
                {
                    "schema_version": "automath-newmath-refinement-target-v1",
                    "bridge_id": row.get("bridge_id"),
                    "source_repo": row.get("source_repo"),
                    "source_branch_or_ref": row.get("source_branch_or_ref"),
                    "source_commit": row.get("source_commit"),
                    "source_path": row.get("source_path"),
                    "blocked_reason": "no_specific_board_claim",
                    "required_before_retry": [
                        "extract concrete source theorem names or paper labels",
                        "name the BEDC-native carrier, classifier, obstruction, public invariant, or proof-obligation shortcut",
                        "state expected_newmath_delta as a minimal wrapper/proposal/audit task",
                        "state reject_if in BEDC-native terms",
                    ],
                    "reuse_instruction": (
                        "Use Automath source as prior evidence; do not ask BEDC to "
                        "rediscover the Automath result from scratch."
                    ),
                    "next_pi_step": "tighten bridge_to_bedc_board specific claim mapping or leave evidence_only",
                }
            )

    if reason_counts.get("history_rejected:too_vague", 0):
        actions.append(
            {
                "schema_version": "automath-newmath-pi-action-v1",
                "action_id": "pi:newmath:narrow_history_rejected_too_vague",
                "action_type": "tighten_rejected_continuation_target",
                "severity": "high",
                "trigger_reason": "history_rejected:too_vague",
                "trigger_count": reason_counts["history_rejected:too_vague"],
                "automatic_effect": "cooldown_unchanged_retry",
                "safe_to_apply_automatically": True,
                "policy": (
                    "Do not retry the same BOARD title unchanged. Retry only after "
                    "the claim names a narrower BEDC landing file, carrier/readback "
                    "object, and a non-generic proof obligation."
                ),
                "sources": _unique_sources(ack_rows, "history_rejected:too_vague"),
            }
        )

    if reason_counts.get("duplicate_board_title", 0):
        actions.append(
            {
                "schema_version": "automath-newmath-pi-action-v1",
                "action_id": "pi:newmath:cooldown_duplicate_board_titles",
                "action_type": "cooldown_duplicate_sources",
                "severity": "medium",
                "trigger_reason": "duplicate_board_title",
                "trigger_count": reason_counts["duplicate_board_title"],
                "automatic_effect": "do_not_resubmit_without_source_commit_or_title_change",
                "safe_to_apply_automatically": True,
                "policy": "Treat duplicate BOARD titles as consumed unless the Automath source commit or BEDC-native landing object changes.",
                "sources": _unique_sources(ack_rows, "duplicate_board_title"),
            }
        )

    if reason_counts.get("evidence_only:pipeline_status", 0):
        actions.append(
            {
                "schema_version": "automath-newmath-pi-action-v1",
                "action_id": "pi:newmath:keep_pipeline_status_evidence_only",
                "action_type": "lower_priority_for_board_spawn",
                "severity": "low",
                "trigger_reason": "evidence_only:pipeline_status",
                "trigger_count": reason_counts["evidence_only:pipeline_status"],
                "automatic_effect": "retain_as_evidence_only",
                "safe_to_apply_automatically": True,
                "policy": "Pipeline-status artifacts can improve bridge harness design but should not spawn BEDC theorem work.",
                "sources": _unique_sources(ack_rows, "evidence_only:pipeline_status"),
            }
        )

    actions.append(
        {
            "schema_version": "automath-newmath-pi-action-v1",
            "action_id": "pi:newmath:cycle_health",
            "action_type": "global_signal_summary",
            "severity": "info",
            "safe_to_apply_automatically": True,
            "automatic_effect": "monitor_next_cycle",
            "status_counts": dict(sorted(status_counts.items())),
            "reason_counts": dict(sorted(reason_counts.items())),
            "gate_counts": _gate_summary(gate_rows),
        }
    )
    return actions, refinements


def render_report(
    ack_rows: list[dict[str, Any]],
    gate_rows: list[dict[str, Any]],
    actions: list[dict[str, Any]],
    refinements: list[dict[str, Any]],
) -> str:
    status_counts = Counter(str(row.get("status") or "unknown") for row in ack_rows)
    reason_counts = Counter(str(row.get("reason") or "none") for row in ack_rows)
    lines = [
        "# Automath-NewMath PI Reflection",
        "",
        "This report is the deterministic PI layer for the Automath-to-NewMath bridge.",
        "It turns global ACK/NACK and gate signals into disciplined bridge-control actions.",
        "It does not write BEDC paper or Lean content.",
        "",
        "## Current Signal",
        "",
        f"- ACK rows: `{len(ack_rows)}`",
        f"- Gate rows: `{len(gate_rows)}`",
        f"- PI actions: `{len(actions)}`",
        f"- Refinement targets: `{len(refinements)}`",
        "",
        "## Status Counts",
        "",
        "| Status | Count |",
        "| --- | ---: |",
    ]
    for key, value in sorted(status_counts.items()):
        lines.append(f"| `{key}` | {value} |")
    lines.extend(["", "## Reason Counts", "", "| Reason | Count |", "| --- | ---: |"])
    for key, value in sorted(reason_counts.items()):
        lines.append(f"| `{key}` | {value} |")
    lines.extend(["", "## PI Actions", "", "| Action | Trigger | Effect | Severity |", "| --- | --- | --- | --- |"])
    for action in actions:
        lines.append(
            "| `{}` | `{}` | `{}` | `{}` |".format(
                action.get("action_id", ""),
                action.get("trigger_reason", action.get("action_type", "")),
                action.get("automatic_effect", ""),
                action.get("severity", ""),
            )
        )
    lines.extend(
        [
            "",
            "## Control Policy",
            "",
            "- Repeated `no_specific_board_claim` creates refinement targets instead of resubmitting vague BOARD entries.",
            "- `history_rejected:too_vague` cools unchanged retries until a narrower BEDC-native continuation claim exists.",
            "- `duplicate_board_title` is treated as consumed unless the source commit or BEDC landing object changes.",
            "- `evidence_only:pipeline_status` remains harness evidence and is not promoted to theorem work.",
            "- The PI may write only durable bridge reports and action ledgers; runtime inbox, out, state, and logs remain uncommitted.",
            "",
        ]
    )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Run deterministic bridge PI reflection")
    parser.add_argument("--ack-ledger", default=str(DEFAULT_ACK))
    parser.add_argument("--status-report", default=str(DEFAULT_STATUS))
    parser.add_argument("--gate-results", default=str(DEFAULT_GATE_RESULTS))
    parser.add_argument("--report", default=str(DEFAULT_REPORT))
    parser.add_argument("--actions", default=str(DEFAULT_ACTIONS))
    parser.add_argument("--refinement-queue", default=str(DEFAULT_REFINEMENT))
    parser.add_argument("--no-specific-threshold", type=int, default=3)
    args = parser.parse_args(argv)

    ack_rows = _read_jsonl(Path(args.ack_ledger))
    gate_rows = _read_jsonl(Path(args.gate_results))
    actions, refinements = build_actions(
        ack_rows,
        gate_rows,
        no_specific_threshold=max(1, args.no_specific_threshold),
    )

    _write_jsonl(Path(args.actions), actions)
    _write_jsonl(Path(args.refinement_queue), refinements)
    report_path = Path(args.report)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_report(ack_rows, gate_rows, actions, refinements), encoding="utf-8")

    print(
        json.dumps(
            {
                "ack_rows": len(ack_rows),
                "gate_rows": len(gate_rows),
                "actions": len(actions),
                "refinement_targets": len(refinements),
                "report": str(report_path),
                "actions_path": str(Path(args.actions)),
                "refinement_queue": str(Path(args.refinement_queue)),
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Classify BioReality loop outputs into local pipeline signals."""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

try:
    from store import BioRealityPaths, read_jsonl
except ModuleNotFoundError:  # pragma: no cover
    from tools.bio_reality.store import BioRealityPaths, read_jsonl


SCRIPT_DIR = Path(__file__).resolve().parent
STATE_DIR = SCRIPT_DIR / "state"
SIGNAL_JOURNAL = STATE_DIR / "bio_reality_signals.jsonl"
LATEST_PATH = STATE_DIR / "bio_reality_signals_latest.md"
VERSION = "bio-reality-pipeline-signals"


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def classify_tasks(tasks: list[dict[str, Any]]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for task in tasks:
        kind = str(task.get("task_kind") or "unknown")
        counts[kind] = counts.get(kind, 0) + 1
    return dict(sorted(counts.items()))


def summarize(paths: BioRealityPaths) -> dict[str, Any]:
    gate_results = read_jsonl(paths.gate_results)
    tasks = read_jsonl(paths.deepening_tasks)
    review_queue = read_jsonl(paths.review_queue)
    events = read_jsonl(paths.events)
    agent_tasks = read_jsonl(paths.agent_tasks)
    dispatch_results = read_jsonl(paths.dispatch_results)
    hardening_targets = read_jsonl(paths.hardening_targets)
    blocked = [item for item in gate_results if item.get("gate_status") == "gate_blocked"]
    review_ready = [item for item in review_queue if item.get("review_decision") == "review_ready"]
    return {
        "version": VERSION,
        "checked_at": now_iso(),
        "gate_results": len(gate_results),
        "blocked": len(blocked),
        "deepening_tasks": len(tasks),
        "review_items": len(review_queue),
        "review_ready": len(review_ready),
        "events": len(events),
        "agent_tasks": len(agent_tasks),
        "dispatch_results": len(dispatch_results),
        "dispatch_completed": sum(1 for item in dispatch_results if item.get("dispatch_status") == "completed"),
        "dispatch_failed": sum(1 for item in dispatch_results if item.get("dispatch_status") == "failed"),
        "dispatch_planned_only": sum(1 for item in dispatch_results if item.get("dispatch_status") == "planned_only"),
        "hardening_targets": len(hardening_targets),
        "task_counts": classify_tasks(tasks),
        "blocked_items": [
            {
                "packet_kind": str(item.get("packet_kind") or ""),
                "packet_id": str(item.get("packet_id") or ""),
                "issues": item.get("issues") if isinstance(item.get("issues"), list) else [],
            }
            for item in blocked[:20]
        ],
    }


def render_latest(summary: dict[str, Any]) -> str:
    lines = [
        "# BioReality pipeline signals latest",
        "",
        f"- version: {summary['version']}",
        f"- checked_at: {summary['checked_at']}",
        f"- gate_results: {summary['gate_results']}",
        f"- blocked: {summary['blocked']}",
        f"- deepening_tasks: {summary['deepening_tasks']}",
        f"- review_ready: {summary['review_ready']}",
        f"- events: {summary.get('events', 0)}",
        f"- agent_tasks: {summary.get('agent_tasks', 0)}",
        f"- dispatch_results: {summary.get('dispatch_results', 0)}",
        f"- dispatch_completed: {summary.get('dispatch_completed', 0)}",
        f"- dispatch_failed: {summary.get('dispatch_failed', 0)}",
        f"- dispatch_planned_only: {summary.get('dispatch_planned_only', 0)}",
        f"- hardening_targets: {summary.get('hardening_targets', 0)}",
        f"- task_counts: {json.dumps(summary['task_counts'], sort_keys=True)}",
        "",
        "These are local pipeline signals only. They are not paper evidence,",
        "biological conclusions, or mechanism claims.",
        "",
        "## Blocked items",
        "",
    ]
    for item in summary["blocked_items"]:
        issues = "; ".join(str(issue) for issue in item.get("issues", [])[:3])
        lines.append(f"- {item['packet_kind']}:{item['packet_id']} - {issues}")
    lines.append("")
    return "\n".join(lines)


def write_summary(summary: dict[str, Any]) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    with SIGNAL_JOURNAL.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(summary, ensure_ascii=False, sort_keys=True) + "\n")
    LATEST_PATH.write_text(render_latest(summary), encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Summarize BioReality loop outputs into local signals")
    parser.add_argument("--gate-results", default=str(BioRealityPaths.gate_results))
    parser.add_argument("--deepening-tasks", default=str(BioRealityPaths.deepening_tasks))
    parser.add_argument("--review-queue", default=str(BioRealityPaths.review_queue))
    parser.add_argument("--events", default=str(BioRealityPaths.events))
    parser.add_argument("--agent-tasks", default=str(BioRealityPaths.agent_tasks))
    parser.add_argument("--dispatch-results", default=str(BioRealityPaths.dispatch_results))
    parser.add_argument("--hardening-targets", default=str(BioRealityPaths.hardening_targets))
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--no-write", action="store_true")
    args = parser.parse_args(argv)
    paths = BioRealityPaths(
        gate_results=Path(args.gate_results),
        deepening_tasks=Path(args.deepening_tasks),
        review_queue=Path(args.review_queue),
        events=Path(args.events),
        agent_tasks=Path(args.agent_tasks),
        dispatch_results=Path(args.dispatch_results),
        hardening_targets=Path(args.hardening_targets),
    )
    summary = summarize(paths)
    if not args.no_write:
        write_summary(summary)
    compact = {
        "version": summary["version"],
        "blocked": summary["blocked"],
        "deepening_tasks": summary["deepening_tasks"],
        "review_ready": summary["review_ready"],
        "events": summary["events"],
        "agent_tasks": summary["agent_tasks"],
        "dispatch_results": summary["dispatch_results"],
        "dispatch_completed": summary["dispatch_completed"],
        "dispatch_failed": summary["dispatch_failed"],
        "dispatch_planned_only": summary["dispatch_planned_only"],
        "hardening_targets": summary["hardening_targets"],
        "task_counts": summary["task_counts"],
    }
    print(json.dumps(summary if args.json else compact, ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

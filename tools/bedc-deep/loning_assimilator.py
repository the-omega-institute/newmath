#!/usr/bin/env python3
"""Assimilate useful loning-side pipeline signals into BEDC state.

This is intentionally local and non-invasive.  It reads the fetch/report output
from loning_watch.py, classifies recent relevant commits, and emits structured
signal counts for our local gates and dashboards.  It never merges, checks out,
edits paper/Lean sources, or injects upstream advice text into prompts.
"""

from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
STATE_DIR = SCRIPT_DIR / "state"
WATCH_JOURNAL = STATE_DIR / "loning_watch.jsonl"
ASSIM_JOURNAL = STATE_DIR / "loning_assimilation.jsonl"
LATEST_PATH = STATE_DIR / "loning_assimilation_latest.md"

VERSION = "loning-pipeline-signals"


PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("tastegate_hardening", re.compile(r"TasteGate|FieldFaithful|Nontrivial|StructurallyAtomic|ChapterTasteGate", re.I)),
    ("paper_gate_hardening", re.compile(r"phase_paper_gates|phase_review|phase_revise|origin\{ai\}|falsifiablePrediction|independenceWitness", re.I)),
    ("conjecture_channel", re.compile(r"conjecture|parts/conjectures", re.I)),
    ("ripeness_signal", re.compile(r"ripeness|dossier_ripeness|in_degree|orphan", re.I)),
    ("lean_target_surface", re.compile(r"lean4/|Lean target|leanchecked|leantarget", re.I)),
    ("board_surface", re.compile(r"tools/bedc-deep/BOARD|board_spawn|oracle_board_refill|candidate_inbox", re.I)),
    ("over_chapterization_risk", re.compile(r"main\.tex|preamble\.tex|parts/concrete_instances/.+_namecert_construction|concretize|NameCert surface|carrier", re.I)),
    ("resource_witness_obligation", re.compile(r"witness|budget|obligation|certificate|dependency|tail|threshold|modulus|finite", re.I)),
    ("prompt_candidate_pool", re.compile(r"candidate_pool|selection_rank|minimum candidate|emit .*targets|never empty|dedup empty", re.I)),
    ("prompt_quality_score", re.compile(r"quality_score|hardest feasible|difficulty|verifiability|downstream_use|line_cap_safety|cross_chapter", re.I)),
    ("prompt_landing_safety", re.compile(r"line[-_ ]?cap|hub[-_ ]?file|hub file|near[-_ ]?line|wc -l|paper_files", re.I)),
)


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def load_watch_entries(limit: int) -> list[dict[str, Any]]:
    if not WATCH_JOURNAL.exists():
        return []
    out: list[dict[str, Any]] = []
    for line in WATCH_JOURNAL.read_text(encoding="utf-8", errors="replace").splitlines()[-limit:]:
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(rec, dict):
            out.append(rec)
    return out


def iter_relevant_commits(entries: list[dict[str, Any]]) -> list[dict[str, Any]]:
    seen: set[str] = set()
    commits: list[dict[str, Any]] = []
    for entry in entries:
        for ref in entry.get("refs") or []:
            ref_name = str(ref.get("ref") or "")
            for item in ref.get("relevant") or []:
                if not isinstance(item, dict):
                    continue
                sha = str(item.get("sha") or item.get("short") or "")
                if not sha or sha in seen:
                    continue
                seen.add(sha)
                commits.append({**item, "ref": ref_name})
    return commits


def classify_commit(item: dict[str, Any]) -> list[str]:
    files = item.get("files") or []
    haystack = "\n".join([
        str(item.get("subject") or ""),
        "\n".join(str(f) for f in files),
        "\n".join(str(s) for s in item.get("signals") or []),
    ])
    labels = [name for name, pattern in PATTERNS if pattern.search(haystack)]
    return sorted(set(labels))


def summarize(entries: list[dict[str, Any]], *, max_items: int) -> dict[str, Any]:
    commits = iter_relevant_commits(entries)
    classified: list[dict[str, Any]] = []
    counts: dict[str, int] = {}
    for item in commits:
        labels = classify_commit(item)
        for label in labels:
            counts[label] = counts.get(label, 0) + 1
        if labels:
            classified.append({
                "sha": str(item.get("sha") or ""),
                "short": str(item.get("short") or str(item.get("sha") or "")[:9]),
                "subject": str(item.get("subject") or ""),
                "ref": str(item.get("ref") or ""),
                "labels": labels,
                "files": [str(f) for f in (item.get("files") or [])[:12]],
            })

    return {
        "version": VERSION,
        "checked_at": now_iso(),
        "watch_entries": len(entries),
        "relevant_commits": len(commits),
        "classified_commits": classified[-max_items:],
        "signal_counts": dict(sorted(counts.items())),
    }


def render_latest(summary: dict[str, Any]) -> str:
    lines = [
        "# loning pipeline signals latest",
        "",
        f"- version: {summary['version']}",
        f"- checked_at: {summary['checked_at']}",
        f"- watch_entries: {summary['watch_entries']}",
        f"- relevant_commits: {summary['relevant_commits']}",
        f"- signal_counts: {json.dumps(summary['signal_counts'], sort_keys=True)}",
        "",
        "These are pipeline signals only. They are not prompt advice, source",
        "provenance, BOARD entries, or paper evidence.",
        "",
        "## Classified commits",
        "",
    ]
    for item in summary["classified_commits"]:
        labels = ", ".join(item["labels"])
        lines.append(f"- {item['short']} {item['subject']} [{labels}]")
    lines.append("")
    return "\n".join(lines)


def write_summary(summary: dict[str, Any]) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    with ASSIM_JOURNAL.open("a", encoding="utf-8") as f:
        f.write(json.dumps(summary, ensure_ascii=False, sort_keys=True) + "\n")
    LATEST_PATH.write_text(render_latest(summary), encoding="utf-8")


def latest_signal_summary() -> dict[str, Any]:
    if LATEST_PATH.exists():
        try:
            lines = ASSIM_JOURNAL.read_text(encoding="utf-8", errors="replace").splitlines()
            for line in reversed(lines):
                rec = json.loads(line)
                if isinstance(rec, dict) and rec.get("version") == VERSION:
                    return rec
        except (OSError, json.JSONDecodeError):
            pass
    return summarize(load_watch_entries(8), max_items=20)


def main() -> int:
    parser = argparse.ArgumentParser(description="Assimilate loning watch signals into BEDC pipeline state.")
    parser.add_argument("--watch-tail", type=int, default=8)
    parser.add_argument("--max-items", type=int, default=30)
    parser.add_argument("--json", action="store_true", help="Print the full structured signal summary.")
    parser.add_argument("--no-write", action="store_true", help="Compute without updating state files.")
    args = parser.parse_args()

    if args.json:
        print(json.dumps(latest_signal_summary(), ensure_ascii=False, sort_keys=True))
        return 0

    summary = summarize(load_watch_entries(args.watch_tail), max_items=args.max_items)
    if not args.no_write:
        write_summary(summary)
    print(json.dumps({
        "version": summary["version"],
        "relevant_commits": summary["relevant_commits"],
        "signal_counts": summary["signal_counts"],
        "latest": str(LATEST_PATH.relative_to(REPO_ROOT)) if "REPO_ROOT" in globals() else str(LATEST_PATH),
    }, ensure_ascii=False, sort_keys=True))
    return 0


REPO_ROOT = SCRIPT_DIR.parents[1]


if __name__ == "__main__":
    raise SystemExit(main())

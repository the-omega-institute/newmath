#!/usr/bin/env python3
"""Watch loning-side integration branches for pipeline and closure-discipline changes.

This is deliberately fetch-and-report only. It never merges, checks out, or
edits paper/Lean sources. The supervisor uses it to surface changes that may
require our BEDC paper pipeline to update prompts, gates, or operating rules.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[1]
STATE_DIR = SCRIPT_DIR / "state"
STATE_PATH = STATE_DIR / "loning_watch_state.json"
JOURNAL_PATH = STATE_DIR / "loning_watch.jsonl"
LATEST_PATH = STATE_DIR / "loning_watch_latest.md"
HUMAN_INBOX = SCRIPT_DIR / ".human_inbox.md"

DEFAULT_REFS = [
    "origin/auto-dev",
    "origin/codex-auto-dev",
    "origin/dev",
    "origin/feature/dossier",
]

SIGNAL_RE = re.compile(
    r"closurestatus|theoryclosure|formalstatus|leantarget|"
    r"seedClosure|obligationClosure|scopedClosure|publicClosure|"
    r"bridgedClosure|matureClosure|verified gate|two-axis|"
    r"closure-vs-verification|critical_path|phase_review|"
    r"phase_revise|codex_revise|axis-confusion|dossier",
    re.IGNORECASE,
)

WATCH_PATHS = (
    "papers/bedc/scripts/",
    "papers/bedc/parts/acceptance/",
    "papers/bedc/parts/project_governance/",
    "papers/bedc/appendices/build_and_verification_log.tex",
    "papers/bedc/frontmatter/",
    "papers/bedc/preamble.tex",
    "lean4/scripts/prompts/",
    "lean4/scripts/critical_path.py",
    "lean4/scripts/bedc_ci.py",
    "tools/bedc-deep/prompts/",
    "tools/bedc-deep/",
    "CLAUDE.md",
    "AGENTS.md",
)


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def git(args: list[str], *, timeout: int = 120, check: bool = False) -> subprocess.CompletedProcess:
    proc = subprocess.run(
        ["git", *args],
        cwd=str(REPO_ROOT),
        text=True,
        capture_output=True,
        timeout=timeout,
    )
    if check and proc.returncode != 0:
        raise RuntimeError((proc.stderr or proc.stdout or "").strip())
    return proc


def load_state() -> dict:
    if not STATE_PATH.exists():
        return {"refs": {}}
    try:
        return json.loads(STATE_PATH.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {"refs": {}}


def save_state(state: dict) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    STATE_PATH.write_text(json.dumps(state, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def append_jsonl(path: Path, entry: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "a", encoding="utf-8") as f:
        f.write(json.dumps(entry, ensure_ascii=False) + "\n")


def append_human_inbox(items: list[str]) -> None:
    if not items:
        return
    block = "\n## " + now_iso() + "\n\n" + "\n".join(f"- {item}" for item in items) + "\n"
    with open(HUMAN_INBOX, "a", encoding="utf-8") as f:
        f.write(block)


def ref_exists(ref: str) -> bool:
    return git(["rev-parse", "--verify", "--quiet", ref]).returncode == 0


def rev_parse(ref: str) -> str:
    return git(["rev-parse", ref], check=True).stdout.strip()


def commit_rows(rev_range: str, *, limit: int) -> list[dict]:
    proc = git([
        "log",
        "--reverse",
        f"--max-count={limit}",
        "--format=%H%x1f%ct%x1f%s",
        rev_range,
    ])
    rows: list[dict] = []
    for line in proc.stdout.splitlines():
        parts = line.split("\x1f", 2)
        if len(parts) != 3:
            continue
        rows.append({"sha": parts[0], "ts": int(parts[1]), "subject": parts[2]})
    return rows


def changed_files(sha: str) -> list[str]:
    proc = git(["diff-tree", "--no-commit-id", "--name-only", "-r", sha])
    return [line.strip() for line in proc.stdout.splitlines() if line.strip()]


def diff_excerpt(sha: str, *, max_chars: int = 50000) -> str:
    proc = git(["show", "--format=", "--unified=0", sha], timeout=120)
    text = proc.stdout
    if len(text) > max_chars:
        return text[:max_chars]
    return text


def classify_commit(row: dict) -> dict:
    files = changed_files(row["sha"])
    diff = diff_excerpt(row["sha"])
    haystack = "\n".join([row["subject"], *files, diff])
    signals: list[str] = []
    if SIGNAL_RE.search(haystack):
        signals.append("closure_or_prompt_signal")
    if any(path.startswith("papers/bedc/scripts/") for path in files):
        signals.append("loning_paper_pipeline")
    if any(path.startswith("lean4/scripts/") for path in files):
        signals.append("lean_or_critical_path")
    if any("closurestatus" in path or path.startswith("papers/bedc/parts/acceptance/") for path in files):
        signals.append("closure_governance")
    if any(path.startswith("tools/bedc-deep/") for path in files):
        signals.append("our_pipeline_surface")
    if any(path.startswith(prefix) or path == prefix for prefix in WATCH_PATHS for path in files):
        signals.append("watched_path")
    return {
        **row,
        "short": row["sha"][:9],
        "files": files[:40],
        "file_count": len(files),
        "signals": sorted(set(signals)),
        "relevant": bool(signals),
    }


def render_latest(summary: dict) -> str:
    lines = [
        "# loning watch latest",
        "",
        f"- checked_at: {summary['checked_at']}",
        f"- refs_checked: {', '.join(summary['refs_checked'])}",
        f"- new_commits: {summary['new_commits']}",
        f"- relevant_commits: {summary['relevant_commits']}",
        "",
    ]
    for ref in summary["refs"]:
        lines.append(f"## {ref['ref']}")
        lines.append(f"- old: {ref.get('old', '')[:12] or '(none)'}")
        lines.append(f"- new: {ref.get('new', '')[:12] or '(missing)'}")
        lines.append(f"- new_commits: {ref['new_commit_count']}")
        if ref["relevant"]:
            lines.append("- relevant:")
            for item in ref["relevant"]:
                signals = ", ".join(item["signals"])
                lines.append(f"  - {item['short']} {item['subject']} [{signals}]")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def run_once(args: argparse.Namespace) -> dict:
    if args.fetch:
        fetch = git(["fetch", "origin", "--prune"], timeout=args.fetch_timeout)
        if fetch.returncode != 0:
            raise RuntimeError((fetch.stderr or fetch.stdout or "git fetch failed").strip())

    state = load_state()
    state.setdefault("refs", {})
    checked_refs: list[str] = []
    ref_summaries: list[dict] = []
    new_total = 0
    relevant_total = 0
    inbox_items: list[str] = []

    for ref in args.refs:
        if not ref_exists(ref):
            ref_summaries.append({"ref": ref, "old": "", "new": "", "new_commit_count": 0, "relevant": [], "missing": True})
            continue
        checked_refs.append(ref)
        new_sha = rev_parse(ref)
        old_sha = str(state["refs"].get(ref, {}).get("last_seen") or "")
        if old_sha == new_sha:
            rows: list[dict] = []
        else:
            base = old_sha if old_sha else "HEAD"
            rows = commit_rows(f"{base}..{ref}", limit=args.max_commits)
        classified = [classify_commit(row) for row in rows]
        relevant = [row for row in classified if row["relevant"]]
        new_total += len(rows)
        relevant_total += len(relevant)
        ref_summaries.append({
            "ref": ref,
            "old": old_sha,
            "new": new_sha,
            "new_commit_count": len(rows),
            "relevant": relevant,
        })
        state["refs"][ref] = {"last_seen": new_sha, "updated_at": now_iso()}

        if relevant:
            bullets = "; ".join(
                f"{item['short']} {item['subject']} ({', '.join(item['signals'])})"
                for item in relevant[:5]
            )
            inbox_items.append(
                f"**loning_watch** — {ref} has {len(relevant)} relevant new commit(s): "
                f"{bullets}. Review {LATEST_PATH.relative_to(REPO_ROOT)} and decide whether "
                "our B pipeline prompts/gates need a compatibility update. Keep B outputs as "
                "concrete theorem sites; do not auto-write closurestatus blocks from this lane."
            )

    summary = {
        "checked_at": now_iso(),
        "refs_checked": checked_refs,
        "new_commits": new_total,
        "relevant_commits": relevant_total,
        "refs": ref_summaries,
    }
    append_jsonl(JOURNAL_PATH, summary)
    LATEST_PATH.write_text(render_latest(summary), encoding="utf-8")
    if inbox_items and not args.no_inbox:
        append_human_inbox(inbox_items)
    save_state(state)
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description="Watch loning-side branches for BEDC pipeline-relevant changes")
    parser.add_argument("--ref", dest="refs", action="append", default=[],
                        help="Remote ref to watch. May be repeated.")
    parser.add_argument("--no-fetch", dest="fetch", action="store_false", default=True)
    parser.add_argument("--fetch-timeout", type=int, default=120)
    parser.add_argument("--max-commits", type=int, default=80)
    parser.add_argument("--no-inbox", action="store_true")
    args = parser.parse_args()
    if not args.refs:
        args.refs = DEFAULT_REFS
    summary = run_once(args)
    print(json.dumps({
        "checked_at": summary["checked_at"],
        "refs_checked": summary["refs_checked"],
        "new_commits": summary["new_commits"],
        "relevant_commits": summary["relevant_commits"],
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Production loop for lightweight Automath-NewMath bridge outputs.

The scanner produces ignored candidates. The heavy loop synthesizes readiness.
This loop consumes those gate results and writes durable, lightweight NewMath
indexes only for Automath-to-NewMath records that are already gate-passed. It
does not write BEDC paper or Lean content.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import json
import os
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent.parent
GATE_RESULTS = SCRIPT_DIR / "out" / "bridge_gate_results.jsonl"
SYNTHESIS_RESULTS = SCRIPT_DIR / "out" / "bridge_synthesis.jsonl"
STOP_FILE = SCRIPT_DIR / ".bridge_production_loop.stop"
LOG_FILE = SCRIPT_DIR / "logs" / "bridge_production_loop.log"
INDEX_PATH = REPO_ROOT / "docs" / "bridge" / "automath-consumption-index.md"


def _now_iso() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def _log(message: str) -> None:
    LOG_FILE.parent.mkdir(parents=True, exist_ok=True)
    line = f"[{_now_iso()}] {message}"
    print(line, flush=True)
    with LOG_FILE.open("a", encoding="utf-8") as handle:
        handle.write(line + "\n")


def _git(args: list[str], *, timeout: int = 120) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["git", *args], cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=timeout, check=False)


@contextmanager
def repo_git_write_lock(timeout: int = 900):
    """Serialize local git index writes across bridge loops in this repo."""
    lock_path = REPO_ROOT / ".git" / "automath_newmath_bridge.git_write.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    deadline = time.monotonic() + timeout
    with lock_path.open("a+b") as handle:
        handle.seek(0, os.SEEK_END)
        if handle.tell() == 0:
            handle.write(b"\0")
            handle.flush()
        handle.seek(0)
        if os.name == "nt":
            import msvcrt

            while True:
                try:
                    msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
                    break
                except OSError:
                    if time.monotonic() >= deadline:
                        raise TimeoutError(f"Timed out waiting for git write lock {lock_path}")
                    time.sleep(1)
            try:
                yield
            finally:
                handle.seek(0)
                msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
        else:
            import fcntl

            while True:
                try:
                    fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                    break
                except BlockingIOError:
                    if time.monotonic() >= deadline:
                        raise TimeoutError(f"Timed out waiting for git write lock {lock_path}")
                    time.sleep(1)
            try:
                yield
            finally:
                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


def _read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            text = line.strip()
            if text:
                data = json.loads(text)
                if isinstance(data, dict):
                    rows.append(data)
    return rows


def _normalized(record: dict[str, Any], *, input_kind: str) -> dict[str, Any]:
    normalized = dict(record)
    synthesis = record.get("synthesis")
    if isinstance(synthesis, dict):
        normalized.setdefault("readiness", synthesis.get("readiness"))
        normalized.setdefault("synthesis_next_action", synthesis.get("synthesis_next_action"))
    normalized["_bridge_input_kind"] = input_kind
    return normalized


def _load_records(args: argparse.Namespace) -> tuple[list[dict[str, Any]], str]:
    gate_records = [_normalized(record, input_kind="gate") for record in _read_jsonl(Path(args.gate_results))]
    if gate_records:
        return gate_records, "gate"
    synthesis_records = [_normalized(record, input_kind="synthesis") for record in _read_jsonl(Path(args.synthesis_results))]
    return synthesis_records, "synthesis"


def _eligible(record: dict[str, Any]) -> bool:
    return (
        record.get("bridge_direction") == "automath_to_newmath"
        and record.get("gate_status") == "gate_passed"
        and record.get("destination_repo") == "the-omega-institute/newmath"
        and record.get("readiness") in {"ready_for_local_packet", "needs_operator_review"}
    )


def _review_only(record: dict[str, Any]) -> bool:
    return (
        record.get("bridge_direction") == "automath_to_newmath"
        and record.get("_bridge_input_kind") == "synthesis"
        and record.get("destination_repo") == "the-omega-institute/newmath"
        and record.get("readiness") in {"ready_for_local_packet", "needs_operator_review"}
    )


def _selected(records: list[dict[str, Any]], *, limit: int) -> list[dict[str, Any]]:
    selected = [record for record in records if _eligible(record) or _review_only(record)]
    selected.sort(key=lambda item: (-int(item.get("priority_score") or 0), str(item.get("source_path") or "")))
    selected = selected[:limit]
    selected.sort(key=lambda item: str(item.get("source_path") or ""))
    return selected


def _priority_band(record: dict[str, Any]) -> str:
    score = int(record.get("priority_score") or 0)
    if score >= 80:
        return "high"
    if score >= 50:
        return "medium"
    return "low"


def _render(records: list[dict[str, Any]], *, limit: int, input_kind: str) -> str:
    selected = _selected(records, limit=limit)
    lines = [
        "# Automath Consumption Index",
        "",
        "This index is a lightweight NewMath receiving surface for Automath evidence.",
        "It records gate-passed bridge evidence and synthesis-only review leads without creating BEDC paper or Lean",
        "content directly. BEDC-native writing remains owned by the BEDC board and",
        "supervisor pipelines.",
        "",
        f"Input source: `{input_kind}`.",
        "",
        "## Current Review Inputs",
        "",
        "| Source | Kind | Readiness | Priority | Input | NewMath action |",
        "| --- | --- | --- | ---: | --- | --- |",
    ]
    for record in selected:
        source = f"{record.get('source_repo')}@{record.get('source_branch_or_ref')}:{record.get('source_path')}"
        lines.append(
            "| `{}` | `{}` | `{}` | {} | `{}` | {} |".format(
                source,
                record.get("source_artifact_kind", ""),
                record.get("readiness", ""),
                _priority_band(record),
                record.get("_bridge_input_kind", ""),
                "review as a NewMath research-object input; do not auto-promote synthesis-only rows",
            )
        )
    if not selected:
        lines.append("| _none_ |  |  |  |  |  |")
    lines.extend(
        [
            "",
            "## Policy",
            "",
            "- Only records with `gate_status=gate_passed` may be consumed by BEDC board adapters.",
            "- `Input source: synthesis` means review-only evidence, not a deterministic gate pass.",
            "- `ready_for_local_packet` means the source may be summarized for review.",
            "- This index does not mark a bridge record accepted or consumed.",
            "- Automath paper content must pass the Automath Killo/golden writeback lane before it becomes durable Automath text.",
            "- NewMath paper and Lean writes remain behind BEDC board, TasteGate, and audit gates.",
            "- Bridge candidates must not be appended to `tools/bedc-deep/BOARD.completed.md`; completed archive entries require BEDC completion semantics.",
        ]
    )
    return "\n".join(lines) + "\n"


def _index_has_entries(text: str) -> bool:
    return "| _none_ |" not in text and "| `" in text


def _commit_if_changed(paths: list[Path], message: str, *, push: bool) -> dict[str, Any]:
    with repo_git_write_lock():
        status = _git(["status", "--porcelain", "--untracked-files=no"], timeout=30)
        if status.returncode != 0:
            return {"status": "status_failed", "stderr": status.stderr.strip()}
        add = _git(["add", *[str(path.relative_to(REPO_ROOT)) for path in paths if path.exists()]], timeout=30)
        if add.returncode != 0:
            return {"status": "add_failed", "stderr": add.stderr.strip()}
        diff = _git(["diff", "--cached", "--quiet"], timeout=30)
        if diff.returncode == 0:
            return {"status": "nothing_to_commit"}
        commit = _git(["commit", "-m", message], timeout=120)
        if commit.returncode != 0:
            return {"status": "commit_failed", "stderr": commit.stderr.strip()}
        result: dict[str, Any] = {"status": "committed", "stdout": commit.stdout.strip()}
        if push:
            branch = _git(["branch", "--show-current"], timeout=30).stdout.strip()
            if branch.startswith(("codex/", "bridge/")):
                pushed = _git(["push", "origin", branch], timeout=300)
                result["push"] = "ok" if pushed.returncode == 0 else pushed.stderr.strip()
            else:
                result["push"] = f"skipped non-bridge branch {branch}"
        return result


def run_once(args: argparse.Namespace) -> bool:
    records, input_kind = _load_records(args)
    selected = _selected(records, limit=args.limit)
    content = _render(records, limit=args.limit, input_kind=input_kind)
    INDEX_PATH.parent.mkdir(parents=True, exist_ok=True)
    old = INDEX_PATH.read_text(encoding="utf-8") if INDEX_PATH.exists() else ""
    if not selected and _index_has_entries(old) and not args.allow_empty:
        _log(
            json.dumps(
                {
                    "records": len(records),
                    "selected": 0,
                    "input_kind": input_kind,
                    "commit": {"status": "preserved_non_empty_index"},
                },
                ensure_ascii=False,
                sort_keys=True,
            )
        )
        return True
    if old != content:
        INDEX_PATH.write_text(content, encoding="utf-8")
    commit = _commit_if_changed([INDEX_PATH], "bridge(newmath): update Automath consumption index", push=args.push)
    _log(json.dumps({"records": len(records), "selected": len(selected), "input_kind": input_kind, "commit": commit}, ensure_ascii=False, sort_keys=True))
    return commit.get("status") in {"committed", "nothing_to_commit"}


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run lightweight durable bridge production")
    parser.add_argument("--gate-results", default=str(GATE_RESULTS))
    parser.add_argument("--synthesis-results", default=str(SYNTHESIS_RESULTS))
    parser.add_argument("--once", action="store_true")
    parser.add_argument("--poll-interval", type=int, default=1800)
    parser.add_argument("--limit", type=int, default=24)
    parser.add_argument("--push", action="store_true")
    parser.add_argument("--allow-empty", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    while True:
        try:
            ok = run_once(args)
        except Exception as exc:
            _log(f"production pass failed: {exc}")
            ok = False
        if args.once or STOP_FILE.exists():
            return 0 if ok else 1
        time.sleep(max(60, args.poll_interval))


if __name__ == "__main__":
    raise SystemExit(main())

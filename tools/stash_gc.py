#!/usr/bin/env python3
"""
安全清理 git stash 的只读优先工具。

默认模式只生成 manifest，不删除任何 stash。只有显式传入 --apply 时，
脚本才会对自动候选执行 drop；每条 drop 前都会把 patch 备份到
/tmp/bedc-stash-gc/<shortoid>.patch。脚本始终用 stash 的 OID 读写，
避免 stash@{N} 在 drop 后漂移导致误删。
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Iterable


BACKUP_DIR = Path("/tmp/bedc-stash-gc")
PRESERVE_TERMS = (
    "user-work",
    "user work",
    "handoff",
    "preserve",
    "protect",
    "recovered",
    "unrelated",
    "work-in-progress",
    "casefile",
    "local",
)
AUTO_CATEGORIES = {"sync_autostash", "bare_autostash", "worker"}
WORKER_SEMANTIC_RE = re.compile(r"On (formalize-[a-z0-9-]+-w[a-z0-9]+|paper-revise-[a-z0-9-]+-w[a-z0-9]+)")
WORKER_CODEX_RE = re.compile(r"On codex-R(\d+)")
WORKER_PAPER_RE = re.compile(r"On paper-P(\d+)")


@dataclass
class PathEntry:
    status: str
    paths: list[str]

    def to_json(self) -> dict[str, object]:
        return {"status": self.status, "paths": self.paths}


@dataclass
class StashEntry:
    selector: str
    oid: str
    date: str
    message: str
    category: str
    preserve: bool
    age_days: int
    paths: list[PathEntry]
    touches_sensitive: bool
    worktree_exists: bool | None
    auto_gc_candidate: bool
    reason: str
    path_error: str | None = None
    drop_status: str | None = None

    @property
    def short_oid(self) -> str:
        return self.oid[:12]

    @property
    def file_count(self) -> int:
        return sum(len(entry.paths) for entry in self.paths)

    def to_json(self) -> dict[str, object]:
        return {
            "selector": self.selector,
            "oid": self.short_oid,
            "full_oid": self.oid,
            "date": self.date,
            "message": self.message,
            "age_days": self.age_days,
            "category": self.category,
            "preserve": self.preserve,
            "auto_gc_candidate": self.auto_gc_candidate,
            "sensitive": self.touches_sensitive,
            "worktree_exists": self.worktree_exists,
            "file_count": self.file_count,
            "paths": [entry.to_json() for entry in self.paths],
            "reason": self.reason,
            "path_error": self.path_error,
            "drop_status": self.drop_status,
        }


def warn(message: str) -> None:
    print(f"警告: {message}", file=sys.stderr)


def run_git(args: list[str], check: bool = False) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            ["git", *args],
            check=check,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except subprocess.CalledProcessError as exc:
        return exc
    except OSError as exc:
        warn(f"无法执行 git {' '.join(args)}: {exc}")
        return subprocess.CompletedProcess(["git", *args], 127, "", str(exc))


def repo_root() -> Path:
    proc = run_git(["rev-parse", "--show-toplevel"])
    if proc.returncode != 0:
        raise SystemExit(f"无法定位 git 仓库根目录: {proc.stderr.strip()}")
    return Path(proc.stdout.strip())


def parse_stash_list() -> list[tuple[str, str, str, str]]:
    proc = run_git(["stash", "list", "--format=%gd%x09%H%x09%ci%x09%gs"])
    if proc.returncode != 0:
        raise SystemExit(f"读取 stash 列表失败: {proc.stderr.strip()}")

    rows: list[tuple[str, str, str, str]] = []
    for line in proc.stdout.splitlines():
        parts = line.split("\t", 3)
        if len(parts) != 4:
            warn(f"跳过无法解析的 stash 行: {line}")
            continue
        rows.append((parts[0], parts[1], parts[2], parts[3]))
    return rows


def category_for(message: str) -> str:
    if "sync_with_auto_dev autostash" in message:
        return "sync_autostash"
    if message == "autostash":
        return "bare_autostash"
    if WORKER_SEMANTIC_RE.search(message) or "On codex-R" in message or "On paper-P" in message:
        return "worker"
    if "On (no branch)" in message:
        return "detached"
    if "recovered dropped stash" in message:
        return "recovered"
    return "other"


def preserve_for(message: str, category: str) -> bool:
    lowered = message.lower()
    return category == "recovered" or any(term in lowered for term in PRESERVE_TERMS)


def age_days_for(date_text: str) -> int:
    try:
        local_dt = datetime.strptime(date_text[:19], "%Y-%m-%d %H:%M:%S")
    except ValueError:
        warn(f"无法解析日期，按 0 天处理: {date_text}")
        return 0
    return max((datetime.now() - local_dt).days, 0)


def parse_name_status(output: str) -> list[PathEntry]:
    entries: list[PathEntry] = []
    for raw in output.splitlines():
        if not raw.strip():
            continue
        parts = raw.split("\t")
        status = parts[0]
        paths = [part for part in parts[1:] if part]
        if not paths:
            warn(f"跳过无法解析的 name-status 行: {raw}")
            continue
        entries.append(PathEntry(status=status, paths=paths))
    return entries


def stash_paths(oid: str) -> tuple[list[PathEntry], set[str], str | None]:
    proc = run_git(["stash", "show", "--include-untracked", "--name-status", oid])
    if proc.returncode != 0:
        return [], set(), proc.stderr.strip() or "git stash show 失败"

    untracked_proc = run_git(["stash", "show", "--only-untracked", "--name-status", oid])
    if untracked_proc.returncode != 0:
        return parse_name_status(proc.stdout), set(), untracked_proc.stderr.strip() or "git stash show --only-untracked 失败"

    untracked_paths: set[str] = set()
    for entry in parse_name_status(untracked_proc.stdout):
        untracked_paths.update(entry.paths)
    return parse_name_status(proc.stdout), untracked_paths, None


def path_is_sensitive(entry: PathEntry, untracked_paths: set[str]) -> bool:
    for path_text in entry.paths:
        path = path_text.replace(os.sep, "/")
        if path == "CLAUDE.md" or path == "AGENTS.md" or path == "MEMORY.md":
            return True
        if path.startswith("docs/"):
            return True
        if is_untracked_derived_path(path, untracked_paths):
            return True
    return False


def is_untracked_derived_path(path: str, untracked_paths: set[str]) -> bool:
    if not path.startswith("lean4/BEDC/Derived/"):
        return False
    parts = path.split("/")
    if len(parts) < 5:
        return False
    return path in untracked_paths


def worker_worktree_exists(root: Path, message: str, category: str) -> bool | None:
    if category != "worker":
        return None

    semantic_match = WORKER_SEMANTIC_RE.search(message)
    if semantic_match:
        branch = semantic_match.group(1)
        prefix = "formalize-" if branch.startswith("formalize-") else "paper-revise-"
        body = branch[len(prefix):]
        slug, _, lease_id = body.rpartition("-")
        if slug and lease_id:
            wt_prefix = "formalize" if branch.startswith("formalize-") else "paper_revise"
            return (root / ".worktrees" / f"{wt_prefix}_{slug.replace('-', '_')}_{lease_id}").exists()

    codex_match = WORKER_CODEX_RE.search(message)
    if codex_match:
        return (root / ".worktrees" / ("round_R" + codex_match.group(1))).exists()

    paper_match = WORKER_PAPER_RE.search(message)
    if paper_match:
        return (root / ".worktrees" / ("paper_P" + paper_match.group(1))).exists()

    return False


def decision_reason(entry: StashEntry) -> str:
    if entry.preserve:
        return "含保留词或 recovered，交给人工审查"
    if entry.touches_sensitive:
        return "触及敏感路径，交给人工审查"
    if entry.category not in AUTO_CATEGORIES:
        return "类别不在自动清理集合，交给人工审查"
    if entry.category == "bare_autostash" and entry.age_days < 7:
        return "裸 autostash 未满 7 天，暂不自动清理"
    if entry.category == "worker" and entry.worktree_exists:
        return "对应 worker worktree 仍存在，暂不自动清理"
    if entry.file_count == 0:
        return "路径列表为空，交给人工确认"
    return "满足自动清理判据"


def classify(root: Path, row: tuple[str, str, str, str]) -> StashEntry:
    selector, oid, date_text, message = row
    category = category_for(message)
    preserve = preserve_for(message, category)
    age_days = age_days_for(date_text)
    paths, untracked_paths, path_error = stash_paths(oid)
    touches_sensitive = any(path_is_sensitive(entry, untracked_paths) for entry in paths)
    worktree_exists = worker_worktree_exists(root, message, category)

    placeholder = StashEntry(
        selector=selector,
        oid=oid,
        date=date_text,
        message=message,
        category=category,
        preserve=preserve,
        age_days=age_days,
        paths=paths,
        touches_sensitive=touches_sensitive,
        worktree_exists=worktree_exists,
        auto_gc_candidate=False,
        reason="",
        path_error=path_error,
    )
    reason = decision_reason(placeholder)
    auto_gc_candidate = reason == "满足自动清理判据"
    placeholder.reason = reason
    placeholder.auto_gc_candidate = auto_gc_candidate
    return placeholder


def summarize(entries: Iterable[StashEntry]) -> dict[str, object]:
    rows = list(entries)
    categories = Counter(entry.category for entry in rows)
    auto_count = sum(1 for entry in rows if entry.auto_gc_candidate)
    preserve_count = sum(1 for entry in rows if entry.preserve)
    return {
        "total": len(rows),
        "categories": dict(sorted(categories.items())),
        "auto_gc_candidates": auto_count,
        "manual_review": len(rows) - auto_count,
        "preserve": preserve_count,
    }


def print_human_manifest(entries: list[StashEntry], summary: dict[str, object]) -> None:
    print("stash GC manifest（默认 dry-run，不会删除任何 stash）")
    print(
        "selector | oid | date | age_days | category | preserve | auto | "
        "sensitive | worktree_exists | files | reason"
    )
    for entry in entries:
        worktree_text = "n/a" if entry.worktree_exists is None else str(entry.worktree_exists)
        print(
            f"{entry.selector} | {entry.short_oid} | {entry.date} | {entry.age_days} | "
            f"{entry.category} | {entry.preserve} | {entry.auto_gc_candidate} | "
            f"{entry.touches_sensitive} | {worktree_text} | {entry.file_count} | {entry.reason}"
        )

    print("")
    print("汇总")
    print(f"总数: {summary['total']}")
    print("各 category 计数:")
    for category, count in summary["categories"].items():
        print(f"  {category}: {count}")
    print(f"自动候选数: {summary['auto_gc_candidates']}")
    print(f"人工审查数: {summary['manual_review']}")
    print(f"preserve 数: {summary['preserve']}")


def write_backup_patch(entry: StashEntry) -> Path | None:
    BACKUP_DIR.mkdir(parents=True, exist_ok=True)
    backup_path = BACKUP_DIR / f"{entry.short_oid}.patch"
    proc = run_git(["stash", "show", "-p", entry.oid])
    if proc.returncode != 0:
        warn(f"{entry.short_oid} 备份失败: {proc.stderr.strip()}")
        return None
    try:
        backup_path.write_text(proc.stdout, encoding="utf-8")
    except OSError as exc:
        warn(f"{entry.short_oid} 写入备份失败: {exc}")
        return None
    return backup_path


def apply_gc(entries: list[StashEntry], max_count: int) -> int:
    candidates = sorted(
        (entry for entry in entries if entry.auto_gc_candidate),
        key=lambda entry: entry.date,
    )
    dropped = 0
    for entry in candidates:
        if dropped >= max_count:
            break
        backup_path = write_backup_patch(entry)
        if backup_path is None:
            entry.drop_status = "backup_failed"
            continue

        proc = run_git(["stash", "drop", entry.oid])
        if proc.returncode != 0:
            warn(f"{entry.short_oid} drop 失败: {proc.stderr.strip()}")
            entry.drop_status = "drop_failed"
            continue

        dropped += 1
        entry.drop_status = "dropped"
        print(f"已 drop {entry.short_oid}，备份: {backup_path}")

    remaining = max(len(candidates) - dropped, 0)
    print(f"本次实际 drop: {dropped}")
    print(f"备份目录: {BACKUP_DIR}")
    print(f"剩余自动候选: {remaining}")
    return dropped


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="安全清理 git stash，默认 dry-run。")
    parser.add_argument("--json", action="store_true", help="以 JSON 输出 manifest。")
    parser.add_argument("--apply", action="store_true", help="实际 drop 自动候选 stash。")
    parser.add_argument("--max", type=int, default=50, help="--apply 单次最多 drop 的条数，默认 50。")
    args = parser.parse_args()
    if args.max < 0:
        parser.error("--max 不能为负数")
    if args.max > 50:
        parser.error("--max 安全上限为 50")
    return args


def main() -> int:
    args = parse_args()
    root = repo_root()
    os.chdir(root)

    entries = [classify(root, row) for row in parse_stash_list()]
    summary = summarize(entries)

    if args.apply:
        apply_gc(entries, args.max)
        summary = summarize(entries)

    manifest = {
        "dry_run": not args.apply,
        "backup_dir": str(BACKUP_DIR),
        "summary": summary,
        "entries": [entry.to_json() for entry in entries],
    }

    if args.json:
        print(json.dumps(manifest, ensure_ascii=False, indent=2))
    else:
        print_human_manifest(entries, summary)

    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        warn("收到中断信号，已停止")
        raise SystemExit(130)

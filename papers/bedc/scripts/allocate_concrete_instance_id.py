#!/usr/bin/env python3
"""Allocate a globally unique concrete-instance chapter number."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
PAPER_ROOT = SCRIPT_DIR.parent
REPO_ROOT = PAPER_ROOT.parent.parent
CONCRETE_INSTANCES = PAPER_ROOT / "parts" / "concrete_instances"
COUNTER_NAME = "concrete_instance_next"
PREFIX_RE = re.compile(r"^(\d+)_")


def _git_common_dir() -> Path:
    out = subprocess.check_output(
        ["git", "rev-parse", "--git-common-dir"],
        cwd=REPO_ROOT,
        text=True,
        stderr=subprocess.DEVNULL,
    ).strip()
    path = Path(out)
    if not path.is_absolute():
        path = (REPO_ROOT / path).resolve()
    return path


def _counter_path() -> Path:
    return _git_common_dir() / COUNTER_NAME


def _install_tools_path() -> None:
    candidates = []
    try:
        candidates.append(_git_common_dir().parent / "tools")
    except Exception:
        pass
    candidates.append(REPO_ROOT / "tools")
    for path in candidates:
        if (path / "repo_push_lock.py").exists():
            text = str(path)
            if text not in sys.path:
                sys.path.insert(0, text)
            return


def _files_max() -> int:
    max_id = 0
    if not CONCRETE_INSTANCES.exists():
        return max_id
    for path in CONCRETE_INSTANCES.iterdir():
        if not path.is_file():
            continue
        match = PREFIX_RE.match(path.name)
        if match:
            max_id = max(max_id, int(match.group(1)))
    return max_id


def _read_counter(path: Path) -> int:
    try:
        text = path.read_text(encoding="utf-8").strip()
    except FileNotFoundError:
        return 0
    if not text:
        return 0
    try:
        return int(text)
    except ValueError:
        print(
            f"warning: ignoring malformed concrete-instance counter at {path}",
            file=sys.stderr,
        )
        return 0


def _peek() -> tuple[int, int, int]:
    files_max = _files_max()
    counter = _read_counter(_counter_path())
    return files_max, counter, max(files_max, counter) + 1


def _allocate_locked() -> int:
    path = _counter_path()
    files_max = _files_max()
    counter = _read_counter(path)
    next_id = max(files_max, counter) + 1
    path.write_text(f"{next_id}\n", encoding="utf-8")
    return next_id


def allocate() -> int:
    _install_tools_path()
    try:
        from repo_push_lock import acquire_push_lock
    except Exception as exc:
        fallback = _files_max() + 1
        print(
            f"warning: concrete-instance-id lock unavailable ({exc}); "
            f"falling back to {fallback}",
            file=sys.stderr,
        )
        return fallback

    try:
        with acquire_push_lock("concrete-instance-id", timeout=30):
            return _allocate_locked()
    except TimeoutError as exc:
        fallback = _files_max() + 1
        print(
            f"warning: concrete-instance-id lock timed out ({exc}); "
            f"falling back to {fallback}",
            file=sys.stderr,
        )
        return fallback
    except Exception as exc:
        fallback = _files_max() + 1
        print(
            f"warning: concrete-instance-id allocation failed ({exc}); "
            f"falling back to {fallback}",
            file=sys.stderr,
        )
        return fallback


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Allocate a unique concrete-instance chapter number."
    )
    parser.add_argument(
        "--peek",
        action="store_true",
        help="show files_max, counter, and next id without allocating",
    )
    args = parser.parse_args()

    if args.peek:
        files_max, counter, next_id = _peek()
        print(f"files_max={files_max} counter={counter} next={next_id}")
        return 0

    print(allocate())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

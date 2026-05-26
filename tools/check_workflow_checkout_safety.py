#!/usr/bin/env python3
from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW_DIR = ROOT / ".github" / "workflows"

RUN_RE = re.compile(r"^(\s*)run:\s*\|")
SAFE_RE = re.compile(r"git\s+config\s+--global\s+--add\s+safe\.directory\s+")
WORKSPACE_GIT_RE = re.compile(r"git\s+-C\s+[\"']?\$GITHUB_WORKSPACE[\"']?\b")
DEPTH_ONE_FETCH_RE = re.compile(r"git\s+-C\s+[\"']?\$GITHUB_WORKSPACE[\"']?\s+fetch\b.*--depth=1\b")


def scan_workflow(path: Path) -> list[str]:
    errors: list[str] = []
    lines = path.read_text(encoding="utf-8").splitlines()
    in_run = False
    run_indent = 0
    saw_safe_directory = False

    for index, line in enumerate(lines, start=1):
        run_match = RUN_RE.match(line)
        if run_match:
            in_run = True
            run_indent = len(run_match.group(1))
            saw_safe_directory = False
            continue

        if in_run:
            stripped = line.strip()
            indent = len(line) - len(line.lstrip(" "))
            if stripped and indent <= run_indent:
                in_run = False
                saw_safe_directory = False

        if not in_run:
            continue

        if SAFE_RE.search(line):
            saw_safe_directory = True
            continue

        if WORKSPACE_GIT_RE.search(line) and not saw_safe_directory:
            errors.append(
                f"{path.relative_to(ROOT)}:{index}: "
                "git -C \"$GITHUB_WORKSPACE\" must be preceded in the same run block "
                "by git config --global --add safe.directory \"$GITHUB_WORKSPACE\""
            )
        if DEPTH_ONE_FETCH_RE.search(line):
            errors.append(
                f"{path.relative_to(ROOT)}:{index}: "
                "custom checkout fetch depth must keep HEAD~1 available for audit new-vs-legacy gates"
            )

    return errors


def main() -> int:
    errors: list[str] = []
    for path in sorted(WORKFLOW_DIR.glob("*.yml")):
        errors.extend(scan_workflow(path))

    if errors:
        print("workflow checkout safety check failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1

    print("workflow checkout safety check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

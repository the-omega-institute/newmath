#!/usr/bin/env python3
from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

DEFINITION_RE = re.compile(
    r"\\(?:providecommand|newcommand|renewcommand)\s*\{\s*\\([A-Za-z][A-Za-z0-9]*Up)\s*\}"
)
USE_RE = re.compile(r"\\([A-Z][A-Za-z0-9]*Up)\b")

SOURCE_GLOBS = [
    "preamble*.tex",
    "parts/**/*.tex",
    "appendices/**/*.tex",
    "frontmatter/**/*.tex",
]


def tex_files() -> list[Path]:
    files: set[Path] = set()
    for pattern in SOURCE_GLOBS:
        files.update(path for path in ROOT.glob(pattern) if path.is_file())
    return sorted(files)


def defined_up_macros(files: list[Path]) -> set[str]:
    defined: set[str] = set()
    for path in files:
        text = path.read_text(encoding="utf-8", errors="ignore")
        defined.update(match.group(1) for match in DEFINITION_RE.finditer(text))
    return defined


def strip_comments(text: str) -> str:
    out: list[str] = []
    for line in text.splitlines(keepends=True):
        escaped = False
        kept: list[str] = []
        for char in line:
            if char == "%" and not escaped:
                break
            kept.append(char)
            escaped = char == "\\" and not escaped
            if char != "\\":
                escaped = False
        out.append("".join(kept))
    return "".join(out)


def main() -> int:
    files = tex_files()
    defined = defined_up_macros(files)
    errors: list[str] = []

    for path in files:
        text = strip_comments(path.read_text(encoding="utf-8", errors="ignore"))
        for match in USE_RE.finditer(text):
            name = match.group(1)
            if name in defined:
                continue
            line = text.count("\n", 0, match.start()) + 1
            errors.append(f"{path.relative_to(ROOT)}:{line}: undefined \\{name}")

    if errors:
        print("undefined Up macro check failed:", file=sys.stderr)
        for error in errors[:200]:
            print(f"- {error}", file=sys.stderr)
        if len(errors) > 200:
            print(f"- ... {len(errors) - 200} more", file=sys.stderr)
        return 1

    print("undefined Up macro check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

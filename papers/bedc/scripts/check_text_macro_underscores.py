#!/usr/bin/env python3
from __future__ import annotations

import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TEXT_MACROS = ("falsifiablePrediction", "independenceWitness")


def matching_brace(text: str, open_index: int) -> int | None:
    depth = 0
    escaped = False
    for index in range(open_index, len(text)):
        char = text[index]
        if escaped:
            escaped = False
            continue
        if char == "\\":
            escaped = True
            continue
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return index
    return None


def has_bare_underscore(text: str) -> bool:
    escaped = False
    in_math = False
    for char in text:
        if escaped:
            escaped = False
            continue
        if char == "\\":
            escaped = True
            continue
        if char == "$":
            in_math = not in_math
            continue
        if in_math:
            continue
        if char == "_":
            return True
    return False


def main() -> int:
    errors: list[str] = []
    for path in sorted((ROOT / "parts").rglob("*.tex")):
        text = path.read_text(encoding="utf-8", errors="ignore")
        for macro in TEXT_MACROS:
            needle = "\\" + macro + "{"
            start = 0
            while True:
                pos = text.find(needle, start)
                if pos < 0:
                    break
                open_index = pos + len(needle) - 1
                close_index = matching_brace(text, open_index)
                if close_index is None:
                    start = open_index + 1
                    continue
                body = text[open_index + 1:close_index]
                if has_bare_underscore(body):
                    line = text.count("\n", 0, pos) + 1
                    rel = path.relative_to(ROOT)
                    errors.append(f"{rel}:{line}: bare underscore inside \\{macro}{{...}}")
                start = close_index + 1

    if errors:
        print("text macro underscore check failed:", file=sys.stderr)
        for error in errors[:200]:
            print(f"- {error}", file=sys.stderr)
        if len(errors) > 200:
            print(f"- ... {len(errors) - 200} more", file=sys.stderr)
        return 1

    print("text macro underscore check passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
from __future__ import annotations

import re
from pathlib import Path


IMPORT_PATTERN = re.compile(
    r"^\s*import\b.*\b(Mathlib(?:\.|\b)|BedcMathlibBridge(?:\.|\b))"
)
MATHLIB_REQUIRE_PATTERN = re.compile(r"^\s*require\s+mathlib\b")
BRIDGE_REQUIRE_PATTERN = re.compile(
    r"^\s*require\s+[A-Za-z0-9_]*bridge[A-Za-z0-9_]*\b",
    re.IGNORECASE,
)


def find_repo_root() -> Path:
    here = Path(__file__).resolve()
    candidates = [Path.cwd().resolve(), here.parent, *here.parents]
    for candidate in candidates:
        if (candidate / "lean4" / "lakefile.lean").exists() and (
            candidate / "papers" / "bedc_mathlib_bridge"
        ).exists():
            return candidate
    raise RuntimeError("cannot locate repository root")


def scan_file(path: Path, pattern: re.Pattern[str], label: str) -> list[str]:
    violations: list[str] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except UnicodeDecodeError:
        lines = path.read_text().splitlines()
    for line_no, line in enumerate(lines, start=1):
        if pattern.search(line):
            violations.append(f"{path}:{line_no}: {label}: {line.strip()}")
    return violations


def main() -> int:
    try:
        repo_root = find_repo_root()
    except RuntimeError as exc:
        print(f"[no-back-edge] FAIL: {exc}")
        return 2

    violations: list[str] = []
    bedc_dir = repo_root / "lean4" / "BEDC"
    if not bedc_dir.exists():
        print(f"[no-back-edge] FAIL: missing {bedc_dir}")
        return 2

    for path in sorted(bedc_dir.rglob("*.lean")):
        violations.extend(scan_file(path, IMPORT_PATTERN, "forbidden import"))

    lakefile = repo_root / "lean4" / "lakefile.lean"
    for pattern, label in (
        (MATHLIB_REQUIRE_PATTERN, "forbidden mathlib requirement"),
        (BRIDGE_REQUIRE_PATTERN, "forbidden bridge requirement"),
    ):
        violations.extend(scan_file(lakefile, pattern, label))

    if violations:
        for violation in violations:
            print(violation)
        print(f"[no-back-edge] FAIL: {len(violations)} forbidden back-edge(s)")
        return 1

    print("[no-back-edge] PASS: BEDC imports no Mathlib or bridge modules")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

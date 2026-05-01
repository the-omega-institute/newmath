#!/usr/bin/env python3
"""Assert that finite-kernel Lean files do not import derived interfaces."""

from __future__ import annotations

import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
LEAN_ROOT = SCRIPT_DIR.parent
KERNEL_ROOTS = [LEAN_ROOT / "BEDC" / "FKernel", LEAN_ROOT / "BEDC" / "BaseReflection"]
IMPORT_RE = re.compile(r"^\s*import\s+(BEDC\.[A-Za-z0-9_'.]+)\s*$")


def lean_file_for_module(module: str) -> Path:
    parts = module.split(".")
    return LEAN_ROOT.joinpath(*parts).with_suffix(".lean")


def direct_imports(path: Path) -> list[str]:
    imports: list[str] = []
    try:
        text = path.read_text(encoding="utf-8")
    except FileNotFoundError:
        return imports
    for line in text.splitlines():
        match = IMPORT_RE.match(line)
        if match:
            imports.append(match.group(1))
    return imports


def main() -> int:
    kernel_files = sorted(path for root in KERNEL_ROOTS for path in root.rglob("*.lean"))
    violations: list[tuple[Path, str]] = []
    visited: set[str] = set()

    def visit(origin: Path, module: str) -> None:
        if module in visited:
            return
        visited.add(module)
        if module.startswith("BEDC.Derived."):
            violations.append((origin, module))
            return
        if not (module.startswith("BEDC.FKernel.") or module.startswith("BEDC.BaseReflection.")):
            return
        for imported in direct_imports(lean_file_for_module(module)):
            visit(origin, imported)

    for path in kernel_files:
        for imported in direct_imports(path):
            visit(path, imported)

    if violations:
        print("[kernel-minimality] derived imports reached from finite kernel:")
        for origin, module in violations:
            print(f"  {origin.relative_to(LEAN_ROOT)} -> {module}")
        return 1

    print(f"[kernel-minimality] ok: checked {len(kernel_files)} kernel files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

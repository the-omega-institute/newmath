#!/usr/bin/env python3
from __future__ import annotations

import subprocess
from pathlib import Path


GUARD_MODULE = "BedcMathlibBridge.Audit.ConstructiveAxiomGuard"


def find_bridge_root() -> Path:
    here = Path(__file__).resolve()
    for parent in (here.parent, *here.parents):
        candidate = parent / "lean4" / "lakefile.lean"
        if candidate.exists() and parent.name == "bedc_mathlib_bridge":
            return parent
    raise RuntimeError("cannot locate papers/bedc_mathlib_bridge root")


def main() -> int:
    try:
        bridge_root = find_bridge_root()
    except RuntimeError as exc:
        print(f"[bridge-axioms] FAIL: {exc}")
        return 2

    lean_dir = bridge_root / "lean4"
    result = subprocess.run(
        ["lake", "build", GUARD_MODULE],
        cwd=lean_dir,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    output = result.stdout
    if output:
        print(output, end="" if output.endswith("\n") else "\n")

    if result.returncode != 0:
        print(f"[bridge-axioms] FAIL: {GUARD_MODULE} exited {result.returncode}")
        return result.returncode

    print("[bridge-axioms] PASS: constructive namespace is 0-axiom")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

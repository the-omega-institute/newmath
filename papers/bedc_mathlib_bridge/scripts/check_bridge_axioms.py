#!/usr/bin/env python3
from __future__ import annotations

import re
import subprocess
from pathlib import Path


FORBIDDEN_AXIOMS = ("Classical.choice", "Quot.sound", "propext")
AUDIT_TARGETS = (
    "BedcMathlibBridge.Constructive.Bool.bmarkBoolEquiv",
    "BedcMathlibBridge.Constructive.Bool.bmarkBoolRelEquiv",
    "BedcMathlibBridge.Constructive.Bool.msame_iff_toBool_eq",
    "BedcMathlibBridge.Constructive.Bool.toBool_b0_ne_b1",
    "BedcMathlibBridge.Constructive.Bool.not_msame_b0_b1_via_bridge",
    "BedcMathlibBridge.Constructive.Int.relIff",
    "BedcMathlibBridge.Constructive.Int.rightInv",
    "BedcMathlibBridge.Constructive.Int.leftInvRel",
    "BedcMathlibBridge.Constructive.Int.intRelQuotEquiv",
    "BedcMathlibBridge.Constructive.Int.pairAdd_toInt",
    "BedcMathlibBridge.Constructive.Int.pairNeg_toInt",
    "BedcMathlibBridge.Constructive.Int.zero_toInt",
)


def find_bridge_root() -> Path:
    here = Path(__file__).resolve()
    for parent in (here.parent, *here.parents):
        candidate = parent / "lean4" / "lakefile.lean"
        if candidate.exists() and parent.name == "bedc_mathlib_bridge":
            return parent
    raise RuntimeError("cannot locate papers/bedc_mathlib_bridge root")


def parse_axiom_report(output: str) -> tuple[list[str], list[str]]:
    missing: list[str] = []
    failures: list[str] = []
    for target in AUDIT_TARGETS:
        escaped = re.escape(target)
        clean_pattern = re.compile(rf"'?{escaped}'? does not depend on any axioms")
        if clean_pattern.search(output):
            continue

        depends_pattern = re.compile(
            rf"'?{escaped}'? depends on axioms:\s*(?P<axioms>[^\n]*)"
        )
        depends = depends_pattern.search(output)
        if depends:
            axioms = depends.group("axioms")
            forbidden = [name for name in FORBIDDEN_AXIOMS if name in axioms]
            if forbidden:
                failures.append(f"{target}: forbidden axioms {', '.join(forbidden)}")
            else:
                failures.append(f"{target}: depends on axioms: {axioms.strip()}")
            continue

        missing.append(target)
    return missing, failures


def main() -> int:
    try:
        bridge_root = find_bridge_root()
    except RuntimeError as exc:
        print(f"[bridge-axioms] FAIL: {exc}")
        return 2

    lean_dir = bridge_root / "lean4"
    audit_file = Path("BedcMathlibBridge/Audit/Constructive.lean")
    result = subprocess.run(
        ["lake", "env", "lean", str(audit_file)],
        cwd=lean_dir,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    output = result.stdout
    if output:
        print(output, end="" if output.endswith("\n") else "\n")

    if result.returncode != 0:
        print(f"[bridge-axioms] FAIL: lean exited {result.returncode}")
        return result.returncode

    missing, failures = parse_axiom_report(output)
    if missing or failures:
        for target in missing:
            print(f"[bridge-axioms] FAIL: missing axiom report for {target}")
        for failure in failures:
            print(f"[bridge-axioms] FAIL: {failure}")
        return 1

    print(f"[bridge-axioms] PASS: {len(AUDIT_TARGETS)} constructive target(s) are 0-axiom")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

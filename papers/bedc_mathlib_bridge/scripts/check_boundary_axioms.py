#!/usr/bin/env python3
from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

from matrix_metadata import MatrixMetadataError, boundary_rows, lean_name, lean_string


TOKEN = "BEDC_GATE_E_SCHEMA"


def find_bridge_root() -> Path:
    here = Path(__file__).resolve()
    for parent in (here.parent, *here.parents):
        if (parent / "lean4" / "lakefile.lean").exists() and parent.name == "bedc_mathlib_bridge":
            return parent
    raise RuntimeError("cannot locate papers/bedc_mathlib_bridge root")


def render_audit(rows: list[tuple[str, str, list[str], str, str]]) -> str:
    entries = []
    for row_id, decl, axioms, _class_name, _instance_name in rows:
        axiom_terms = ", ".join(lean_name(axiom) for axiom in axioms)
        entries.append(
            "{ rowId := "
            + lean_string(row_id)
            + f", decl := {lean_name(decl)}, expectedAxioms := #[{axiom_terms}] }}"
        )
    body = ",\n  ".join(entries)
    return (
        "import BedcMathlibBridge.Audit.BoundaryFactAxiomGuard\n\n"
        "run_cmd do\n"
        f"  BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.audit #[\n  {body}\n]\n"
    )


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit("usage: check_boundary_axioms.py MATRIX.md")
    matrix_path = Path(sys.argv[1])
    try:
        bridge_root = find_bridge_root()
        rows = boundary_rows(matrix_path)
    except (RuntimeError, MatrixMetadataError) as exc:
        print(f"{TOKEN}: {exc}", file=sys.stderr)
        return 1

    lean_dir = bridge_root / "lean4"
    build = subprocess.run(
        ["lake", "build", "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard"],
        cwd=lean_dir,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if build.stdout:
        print(build.stdout, end="" if build.stdout.endswith("\n") else "\n")
    if build.returncode != 0:
        print(f"[boundary-axioms] FAIL: BoundaryFactAxiomGuard build exited {build.returncode}")
        return build.returncode

    with tempfile.TemporaryDirectory(prefix="bedc-boundary-audit.") as tmp:
        audit_path = Path(tmp) / "BoundaryMatrixAudit.lean"
        audit_path.write_text(render_audit(rows), encoding="utf-8")
        result = subprocess.run(
            ["lake", "env", "lean", str(audit_path)],
            cwd=lean_dir,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    if result.stdout:
        print(result.stdout, end="" if result.stdout.endswith("\n") else "\n")
    if result.returncode != 0:
        print(f"[boundary-axioms] FAIL: Gate E exited {result.returncode}")
        return result.returncode
    print(f"[boundary-axioms] PASS: {len(rows)} boundary row(s) match Lean axiom footprints")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

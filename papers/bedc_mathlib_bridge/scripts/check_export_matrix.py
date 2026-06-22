#!/usr/bin/env python3
from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

from matrix_metadata import (
    MatrixMetadataError,
    classification_rows,
    export_rows,
    lean_name,
    lean_string,
)


TOKEN = "BEDC_GATE_D_SCHEMA"


def find_bridge_root() -> Path:
    here = Path(__file__).resolve()
    for parent in (here.parent, *here.parents):
        if (parent / "lean4" / "lakefile.lean").exists() and parent.name == "bedc_mathlib_bridge":
            return parent
    raise RuntimeError("cannot locate papers/bedc_mathlib_bridge root")


KIND_TO_LEAN = {
    "exported_core": "BedcMathlibBridge.CI.IntMetadata.ClassificationKind.exportedCore",
    "subsumed_by_core": "BedcMathlibBridge.CI.IntMetadata.ClassificationKind.subsumedByCore",
    "measured_boundary": "BedcMathlibBridge.CI.IntMetadata.ClassificationKind.measuredBoundary",
    "out_of_scope_generic": "BedcMathlibBridge.CI.IntMetadata.ClassificationKind.outOfScopeGeneric",
}


def render_audit(
    rows: list[tuple[str, str, str, str]],
    classifications: list[tuple[str, str, str, str]],
) -> str:
    entries = []
    for row_id, witness, _class_name, _instance_name in rows:
        entries.append(f"{{ rowId := {lean_string(row_id)}, witness := {lean_name(witness)} }}")
    body = ",\n  ".join(entries)
    class_entries = []
    for row_id, kind, class_name, instance_name in classifications:
        class_entries.append(
            "{ rowId := "
            + lean_string(row_id)
            + f", kind := {KIND_TO_LEAN[kind]}, className := {lean_name(class_name)}, "
            + f"instanceName := {lean_name(instance_name)} }}"
        )
    class_body = ",\n  ".join(class_entries)
    return (
        "import BedcMathlibBridge.CI.ExportAudit\n\n"
        "run_cmd do\n"
        f"  BedcMathlibBridge.CI.ExportAudit.audit #[\n  {body}\n]\n"
        f"    #[\n  {class_body}\n]\n"
    )


def main() -> int:
    if len(sys.argv) != 2:
        raise SystemExit("usage: check_export_matrix.py MATRIX.md")
    matrix_path = Path(sys.argv[1])
    try:
        bridge_root = find_bridge_root()
        rows = export_rows(matrix_path)
        classifications = classification_rows(matrix_path)
    except (RuntimeError, MatrixMetadataError) as exc:
        print(f"{TOKEN}: {exc}", file=sys.stderr)
        return 1

    lean_dir = bridge_root / "lean4"
    build = subprocess.run(
        ["lake", "build", "BedcMathlibBridge.CI.ExportAudit"],
        cwd=lean_dir,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if build.stdout:
        print(build.stdout, end="" if build.stdout.endswith("\n") else "\n")
    if build.returncode != 0:
        print(f"[export-matrix] FAIL: ExportAudit build exited {build.returncode}")
        return build.returncode

    with tempfile.TemporaryDirectory(prefix="bedc-export-audit.") as tmp:
        audit_path = Path(tmp) / "ExportMatrixAudit.lean"
        audit_path.write_text(render_audit(rows, classifications), encoding="utf-8")
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
        print(f"[export-matrix] FAIL: Gate D exited {result.returncode}")
        return result.returncode
    print(f"[export-matrix] PASS: {len(rows)} export witness row(s) match Lean registry")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

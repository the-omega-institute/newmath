#!/usr/bin/env python3
from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

from matrix_metadata import (
    MatrixMetadataError,
    correspondence_rows,
    lean_name,
    lean_string,
)


TOKEN = "BEDC_GATE_W_NO_MATHLIB_CORRESPONDENCE"


def find_bridge_root() -> Path:
    here = Path(__file__).resolve()
    for parent in (here.parent, *here.parents):
        if (parent / "lean4" / "lakefile.lean").exists() and parent.name == "bedc_mathlib_bridge":
            return parent
    raise RuntimeError("cannot locate papers/bedc_mathlib_bridge root")


def render_audit(rows: list[dict[str, str]]) -> str:
    entries = []
    for row in rows:
        entries.append(
            "{ rowId := "
            + lean_string(row["row_id"])
            + f", correspondenceDecl := {lean_name(row['mathlib_correspondence_decl'])}"
            + f", bedcDecl := {lean_name(row['bedc_irreducible_decl'])}"
            + f", mathlibDecl := {lean_name(row['mathlib_decl'])} }}"
        )
    body = ",\n  ".join(entries)
    return (
        "\n\nrun_cmd do\n"
        f"  BedcMathlibBridge.CI.MathlibCorrespondence.audit #[\n  {body}\n]\n"
    )


def read_fixtures(paths: list[Path]) -> str:
    blocks = []
    for path in paths:
        blocks.append(path.read_text(encoding="utf-8"))
    if not blocks:
        return "import BedcMathlibBridge.CI.MathlibCorrespondence\n"
    return "\n\n".join(blocks) + "\n"


def main() -> int:
    if len(sys.argv) < 2:
        raise SystemExit("usage: check_mathlib_correspondence.py MATRIX.md [fixture.lean ...]")
    matrix_path = Path(sys.argv[1])
    fixture_paths = [Path(arg) for arg in sys.argv[2:]]
    try:
        bridge_root = find_bridge_root()
        rows = correspondence_rows(matrix_path)
    except (RuntimeError, MatrixMetadataError) as exc:
        print(f"{TOKEN}: {exc}", file=sys.stderr)
        return 1

    lean_dir = bridge_root / "lean4"
    build = subprocess.run(
        ["lake", "build", "BedcMathlibBridge.CI.MathlibCorrespondence"],
        cwd=lean_dir,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if build.stdout:
        print(build.stdout, end="" if build.stdout.endswith("\n") else "\n")
    if build.returncode != 0:
        print(f"[mathlib-correspondence] FAIL: Gate W module build exited {build.returncode}")
        return build.returncode

    with tempfile.TemporaryDirectory(prefix="bedc-correspondence-audit.") as tmp:
        audit_path = Path(tmp) / "MathlibCorrespondenceMatrixAudit.lean"
        audit_path.write_text(
            read_fixtures(fixture_paths) + render_audit(rows),
            encoding="utf-8",
        )
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
        print(f"[mathlib-correspondence] FAIL: Gate W exited {result.returncode}")
        return result.returncode
    print(f"[mathlib-correspondence] PASS: {len(rows)} exported_core row(s) have mathlib correspondence")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

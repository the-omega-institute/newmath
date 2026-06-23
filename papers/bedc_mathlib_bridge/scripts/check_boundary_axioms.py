#!/usr/bin/env python3
from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

from matrix_metadata import MatrixMetadataError, boundary_rows, lean_name, lean_string


TOKEN = "BEDC_GATE_E_SCHEMA"


CHOICE_STATUS_TO_LEAN = {
    "eliminated": "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.ChoiceStatus.eliminated",
    "principled_irreducible": (
        "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.ChoiceStatus.principledIrreducible"
    ),
    "unprobed": "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.ChoiceStatus.unprobed",
}

PLACE_TO_LEAN = {
    "finite_p": "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.Place.finiteP",
    "infinite_archimedean": (
        "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.Place.infiniteArchimedean"
    ),
    "object_base": "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.Place.objectBase",
    "n_a": "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.Place.nA",
}

LOCATEDNESS_TO_LEAN = {
    "located": "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.Locatedness.located",
    "arbitrary": "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.Locatedness.arbitrary",
    "n_a": "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.Locatedness.nA",
}

QUOTIENT_STATUS_TO_LEAN = {
    "structural_quotient": (
        "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.QuotientStatus.structuralQuotient"
    ),
    "quotient_free": (
        "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.QuotientStatus.quotientFree"
    ),
    "n_a": "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.QuotientStatus.nA",
}

AXIOM_STATUS_TO_LEAN = {
    "eliminated": "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.AxiomStatus.eliminated",
    "mathlib_intrinsic": (
        "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.AxiomStatus.mathlibIntrinsic"
    ),
    "structural_quotient": (
        "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.AxiomStatus.structuralQuotient"
    ),
    "principled_irreducible": (
        "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.AxiomStatus.principledIrreducible"
    ),
    "unprobed": "BedcMathlibBridge.Audit.BoundaryFactAxiomGuard.AxiomStatus.unprobed",
}


def find_bridge_root() -> Path:
    here = Path(__file__).resolve()
    for parent in (here.parent, *here.parents):
        if (parent / "lean4" / "lakefile.lean").exists() and parent.name == "bedc_mathlib_bridge":
            return parent
    raise RuntimeError("cannot locate papers/bedc_mathlib_bridge root")


def render_axioms(axioms: list[str]) -> str:
    return ", ".join(lean_name(axiom) for axiom in axioms)


def render_axiom_status(status: dict[str, str]) -> str:
    entries = [
        f"({lean_name(axiom)}, {AXIOM_STATUS_TO_LEAN[value]})"
        for axiom, value in sorted(status.items())
    ]
    return ", ".join(entries)


def render_audit(rows: list[dict[str, object]]) -> str:
    entries = []
    for row in rows:
        choice_status = str(row["choice_status"])
        place = str(row["place"])
        locatedness = str(row["locatedness"])
        quotient_status = str(row["quotient_status"])
        axiom_status = row["axiom_status"]
        if not isinstance(axiom_status, dict):
            raise MatrixMetadataError("axiom_status must be a dictionary after parsing")
        entries.append(
            "{ rowId := "
            + lean_string(str(row["row_id"]))
            + f", mathlibDecl := {lean_name(str(row['mathlib_decl']))}"
            + f", mathlibFootprint := #[{render_axioms(row['mathlib_footprint'])}]"
            + f", bedcIrreducibleDecl := {lean_name(str(row['bedc_irreducible_decl']))}"
            + f", bedcIrreducibleFootprint := #[{render_axioms(row['bedc_irreducible_footprint'])}]"
            + f", choiceStatus := {CHOICE_STATUS_TO_LEAN[choice_status]}"
            + f", place := {PLACE_TO_LEAN[place]}"
            + f", locatedness := {LOCATEDNESS_TO_LEAN[locatedness]}"
            + f", quotientStatus := {QUOTIENT_STATUS_TO_LEAN[quotient_status]}"
            + f", axiomStatus := #[{render_axiom_status(axiom_status)}] }}"
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

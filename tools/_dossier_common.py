#!/usr/bin/env python3
"""Shared helpers for BEDC dossier tooling.

Single source of truth for:
  - Region classification (region_name_from_lean_file, lean_module_to_region, etc.)
  - Lean import / paper autoref parsers
  - Re-exports of the Lean declaration scanner from lean4/scripts/bedc_ci.py

stdlib only (project rule: no third-party deps in tools).
"""

from __future__ import annotations

import re
from pathlib import Path

# ---------------------------------------------------------------------------
# Repo-level path constants
# ---------------------------------------------------------------------------

ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "lean4" / "BEDC"
DERIVED_DIR = LEAN_DIR / "Derived"
PAPER_INSTANCES = ROOT / "papers" / "bedc" / "parts" / "concrete_instances"

# ---------------------------------------------------------------------------
# Compiled regex constants
# ---------------------------------------------------------------------------

LEAN_IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)", re.MULTILINE)
PAPER_AUTOREF_RE = re.compile(
    r"\\autoref\{ch:concrete-instances-([a-z][a-z0-9\-]*?)(?:-namecert)?\}"
)
PAPER_CAPSTONE_AUTOREF_RE = re.compile(r"\\autoref\{ch:capstones-([a-z][a-z0-9\-]*?)\}")

# ---------------------------------------------------------------------------
# Region mapping tables
# ---------------------------------------------------------------------------

CAPSTONE_FILE_TO_REGION: dict[str, str] = {
    "observer_hist_identity": "observer",
    "inter_hist_locality": "interhist",
}

REGION_ALIASES: dict[str, str] = {
    "analyticcontinuation": "anacont",
    "contourintegral":      "contour",
    "criticalstrip":        "critstrip",
    "zetacontinuation":     "zetacont",
    "complexdifferentiability": "complexdiff",
    "realanalytic": "real",
    "complexanalytic": "anacont",
    "complextopology": "complex",
    "gammafunction": "zetacont",
}

NAMECERT_CHAPTER_KEYWORDS = (
    "_namecert_construction",
    "_operation",
    "_application",
    "_certificate",
)

# ---------------------------------------------------------------------------
# Region classification helpers
# ---------------------------------------------------------------------------


def region_name_from_lean_file(path: Path) -> str:
    """Map BEDC/Derived/RatUp.lean -> 'rat', /FieldUp/Foo.lean -> 'field'."""
    stem = path.stem
    if path.parent != DERIVED_DIR:
        stem = path.parent.name
    name = stem.replace("Up", "")
    return re.sub(r"([a-z])([A-Z])", r"\1_\2", name).lower()


def paper_file_to_region(filename: str) -> str | None:
    name = filename.lower()
    # explicit overrides where the substring heuristic would misfire
    overrides = {
        "complex_limit": "complexlimit",
        "complex_differentiability": "complexdiff",
        "complex_series": "complexseries",
        "convergence_radius": "convergenceradius",
        "dirichlet_series": "dirichletseries",
        "zeta_basic": "zetabasic",
        "zeta_continuation": "zetacont",
        "zeta_zeros": "zetazeros",
        "critical_strip": "critstrip",
        "contour_integral": "contour",
        "analytic_continuation": "anacont",
        "complex_analytic": "anacont",  # 54_complex_analytic falls under anacont scope
        "real_analytic": "real",
        "complex_topology": "complex",
        "gamma_function": "zetacont",  # gamma is inside zeta-continuation chapter scope
        "nattrans": "nattrans",
        "totalorder": "totalorder",
        "abgroup": "abgroup",
        "commring": "commring",
        "linearmap": "linearmap",
        "vecspace": "vecspace",
    }
    for key, region in overrides.items():
        if key in name:
            return region
    # fallback: split on _, take the segment after numeric prefix
    base = name.replace(".tex", "")
    parts = base.split("_")
    # skip leading numeric prefix tokens like "08", "34b"
    while parts and (parts[0].isdigit() or (parts[0][:-1].isdigit() and parts[0][-1].isalpha())):
        parts.pop(0)
    if not parts:
        return None
    candidate = parts[0]
    return candidate if candidate else None


def canonical(region: str | None) -> str | None:
    if region is None:
        return None
    return REGION_ALIASES.get(region, region)


def lean_module_to_region(module: str) -> str | None:
    """Map a Lean module path to a canonical region id.

    Examples:
        BEDC.FKernel.Cont                  -> 'kernel'
        BEDC.Derived.RatUp                 -> 'rat'
        BEDC.Derived.AbGroupUp             -> 'abgroup'
        BEDC.Derived.BoolUpEndpoint        -> 'bool'        (sub-module of Bool)
        BEDC.Derived.OptionUpNullableBridge -> 'option'
        BEDC.Derived.FieldUp.Foo            -> 'field'
        BEDC.Derived.ComplexLimitUp        -> 'complexlimit'
    """
    parts = module.split(".")
    if len(parts) < 2 or parts[0] != "BEDC":
        return None
    if parts[1] == "FKernel":
        return "kernel"
    if parts[1] == "Derived" and len(parts) >= 3:
        name = parts[2]
        # Take the prefix before the first 'Up' if present (handles
        # both `XxxUp` and `XxxUpYyy` sub-module names).
        if "Up" in name:
            name = name.split("Up", 1)[0]
        if not name:
            return None
        return canonical(name.lower())
    return None


def lean_file_to_region(f: Path) -> str | None:
    """Map a .lean file path to the region it belongs to."""
    try:
        rel = f.relative_to(ROOT)
    except ValueError:
        return None
    # rel = lean4/BEDC/Derived/RatUp.lean  or  lean4/BEDC/Derived/FieldUp/Foo.lean
    parts = rel.with_suffix("").parts
    if len(parts) < 3 or parts[0] != "lean4" or parts[1] != "BEDC":
        return None
    module = ".".join(parts[1:])
    return lean_module_to_region(module)


def paper_label_to_region(label_segment: str) -> str:
    """`complex-limit` -> 'complexlimit'; `nat` -> 'nat'."""
    return label_segment.replace("-", "")


def is_namecert_chapter_file(filename: str) -> bool:
    name = filename.lower()
    return any(k in name for k in NAMECERT_CHAPTER_KEYWORDS)


def paper_chapter_to_region(f: Path) -> str | None:
    """Map a paper .tex file path to a region id."""
    rel = f.relative_to(PAPER_INSTANCES.parent)
    # rel = concrete_instances/40_complex_limit_namecert_construction.tex
    # or concrete_instances/field/foo.tex
    if rel.parts[0] == "concrete_instances":
        if len(rel.parts) > 2:
            # Sub-directory files always belong to the parent region (e.g. field/...)
            return rel.parts[1]
        # Top-level: only keep recognised namecert / operation / certificate chapters
        if not is_namecert_chapter_file(rel.name):
            return None
        return paper_file_to_region(rel.name)
    if rel.parts[0] == "capstones":
        stem = f.stem
        return CAPSTONE_FILE_TO_REGION.get(stem)
    return None


def parse_lean_imports(f: Path) -> list[str]:
    text = f.read_text(encoding="utf-8", errors="ignore")
    return [m.group(1) for m in LEAN_IMPORT_RE.finditer(text)]


def parse_paper_autorefs(f: Path) -> list[str]:
    text = f.read_text(encoding="utf-8", errors="ignore")
    refs = []
    for m in PAPER_AUTOREF_RE.finditer(text):
        refs.append(paper_label_to_region(m.group(1)))
    for m in PAPER_CAPSTONE_AUTOREF_RE.finditer(text):
        cap = m.group(1).replace("-", "_")
        if cap in CAPSTONE_FILE_TO_REGION:
            refs.append(CAPSTONE_FILE_TO_REGION[cap])
    return refs


# ---------------------------------------------------------------------------
# Re-export Lean declaration scanner from bedc_ci.py — Issue 1A from /plan-eng-review.
# Cross-directory import via path injection (lean4/scripts/ is not a package).
# ---------------------------------------------------------------------------

import sys as _sys

_BEDC_SCRIPTS = str(Path(__file__).resolve().parents[1] / "lean4" / "scripts")
_sys.path.insert(0, _BEDC_SCRIPTS)
try:
    from bedc_ci import (  # type: ignore[import]
        DeclarationRecord,
        FieldRecord,
        collect_declarations,
        update_namespace_stack,
        qualified_name,
        declaration_namespace,
        resolve_namespace,
        build_declaration_inventory,
    )
finally:
    # Don't pollute sys.path for callers that import _dossier_common
    if _BEDC_SCRIPTS in _sys.path:
        _sys.path.remove(_BEDC_SCRIPTS)

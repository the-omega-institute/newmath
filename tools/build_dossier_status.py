#!/usr/bin/env python3
"""Generate dossier visualization data files.

Reads BEDC state (Lean theorem counts per region, paper marker counts per
chapter, git activity timeline, critical path scheduler output) and writes
three JSON files consumed by `docs/dossier/visualization.qmd`:

- docs/dossier/data/status.json     -- charts data
- docs/dossier/data/glossary.json   -- bilingual term dictionary
- docs/dossier/data/dependency.json -- node/edge graph for Cytoscape

stdlib only (project rule: no third-party deps in tools).
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "lean4" / "BEDC"
DERIVED_DIR = LEAN_DIR / "Derived"
PAPER_INSTANCES = ROOT / "papers" / "bedc" / "parts" / "concrete_instances"
DATA_DIR = ROOT / "docs" / "dossier" / "data"

THEOREM_RE = re.compile(r"^(?:theorem|lemma)\s+(\w+)", re.MULTILINE)
DEF_RE = re.compile(r"^(?:def|inductive|structure|class)\s+(\w+)", re.MULTILINE)
MARKER_RE = re.compile(r"\\(leanchecked|leanstmt|leandef|leanvariant|leansorryd)\{")


def shell(cmd: list[str]) -> str:
    return subprocess.check_output(cmd, cwd=ROOT, text=True, stderr=subprocess.DEVNULL)


def region_name_from_lean_file(path: Path) -> str:
    """Map BEDC/Derived/RatUp.lean -> 'rat', /FieldUp/Foo.lean -> 'field'."""
    stem = path.stem
    if path.parent != DERIVED_DIR:
        stem = path.parent.name
    name = stem.replace("Up", "")
    return re.sub(r"([a-z])([A-Z])", r"\1_\2", name).lower()


def count_lean_theorems_per_region() -> dict[str, dict[str, int]]:
    """Walk lean4/BEDC/Derived/ and count theorems / lemmas / defs per region."""
    out: dict[str, dict[str, int]] = defaultdict(lambda: {"theorems": 0, "defs": 0, "files": 0})
    for f in DERIVED_DIR.rglob("*.lean"):
        text = f.read_text(encoding="utf-8", errors="ignore")
        region = region_name_from_lean_file(f)
        out[region]["theorems"] += len(THEOREM_RE.findall(text))
        out[region]["defs"] += len(DEF_RE.findall(text))
        out[region]["files"] += 1
    # also count kernel theorems (FKernel)
    fkernel = LEAN_DIR / "FKernel"
    if fkernel.exists():
        for f in fkernel.rglob("*.lean"):
            text = f.read_text(encoding="utf-8", errors="ignore")
            out["kernel"]["theorems"] += len(THEOREM_RE.findall(text))
            out["kernel"]["defs"] += len(DEF_RE.findall(text))
            out["kernel"]["files"] += 1
    return dict(out)


def count_paper_markers_per_chapter() -> list[dict]:
    """Scan concrete_instances/**/*.tex for marker counts.

    Files in subdirectories like `field/foo.tex` are tagged with the parent
    directory name as the region hint, so they roll up under the right region.
    """
    rows = []
    for f in sorted(PAPER_INSTANCES.rglob("*.tex")):
        text = f.read_text(encoding="utf-8", errors="ignore")
        counts = Counter(MARKER_RE.findall(text))
        rel = f.relative_to(PAPER_INSTANCES)
        # subdirectory name (e.g. 'field') is a strong region hint when present
        subdir_hint = rel.parts[0] if len(rel.parts) > 1 else None
        rows.append({
            "file": str(rel),
            "name": f.name,
            "subdir": subdir_hint,
            "checked": counts.get("leanchecked", 0),
            "stmt": counts.get("leanstmt", 0),
            "def": counts.get("leandef", 0),
            "variant": counts.get("leanvariant", 0),
            "sorry": counts.get("leansorryd", 0),
        })
    return rows


# Match every paper marker target that looks like a namecert theorem (the
# "completion theorem" of an object in BEDC's framework). Catches both:
#   - CamelCase    e.g. CategoryHomCarrier_semanticNameCert
#   - snake_case   e.g. bool_history_semantic_name_certificate
# Modules can live under BEDC.Derived.<X> (most regions) or BEDC.FKernel.<X>
# (kernel-level objects like Nat / Add via FKernel.Unary).
NAMECERT_TARGET_RE = re.compile(
    r"\\(leanchecked|leanstmt)\{"
    r"(BEDC\.(?:Derived|FKernel)\.([A-Za-z]+)\.[A-Za-z0-9_\\]*?"
    # Strict definition: only NameCert / Name(_)Certificate-shaped
    # theorems count as object-completion proofs. Other completion-
    # related naming (*_laws, *_certificate_fields, *_stability_*) is
    # NOT folded in here; the detail panel adds an explicit fallback
    # message when a closurestatus block has no canonical namecert
    # to surface.
    r"[Nn]ame[A-Za-z0-9_\\]{0,3}[Cc]ert(?:ificate)?[A-Za-z0-9_\\]*)"
    r"\}"
)

# Author-declared chapter closure block. Same source-of-truth used by
# critical_path.py and bedc_ci.py.
CLOSURESTATUS_BEGIN_RE = re.compile(
    r"\\begin\{closurestatus\}\{\s*\\?([A-Z][A-Za-z]*)Up\s*\}"
)
CLOSURESTATUS_END_RE = re.compile(r"\\end\{closurestatus\}")
THEORYCLOSURE_RE = re.compile(r"\\theoryclosure\{\\(\w+)\}")
FORMALSTATUS_RE = re.compile(r"\\formalstatus\{\\(\w+)\}")
LEANTARGET_RE = re.compile(r"\\leantarget\{([^}]+)\}")
BRIDGESTATUS_RE = re.compile(r"\\bridgestatus\{([^}]+)\}")

CLOSURE_GRADE_ORDER = [
    "seedClosure", "obligationClosure", "scopedClosure",
    "publicClosure", "bridgedClosure", "matureClosure",
]
FORMAL_GRADE_ORDER = [
    "unformalizedV", "formalTargetV", "encodedDefV",
    "scaffoldCheckedV", "theoremCheckedV", "auditCleanV",
    "axiomCleanV", "bridgeCheckedV",
]


def _macro_arg(text: str, name: str) -> str | None:
    start = text.find("\\" + name + "{")
    if start < 0:
        return None
    i = start + len(name) + 2
    depth = 1
    out: list[str] = []
    while i < len(text):
        ch = text[i]
        if ch == "{":
            depth += 1
            out.append(ch)
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return "".join(out).strip()
            out.append(ch)
        else:
            out.append(ch)
        i += 1
    return None


# FKernel namespaces that own a region's namecert (the region lives in
# `Derived/` conceptually but its proof tree is in the kernel).
FKERNEL_REGION_OVERRIDES: dict[str, str] = {
    "Unary": "nat",       # nat_up_name_certificate, etc.
    "NameCert": "kernel", # FKernel.NameCert.* — kernel-level certificate machinery
    "Cont": "kernel",     # FKernel.Cont.* — kernel continuation lemmas
    "Package": "kernel",
    "Bundle": "kernel",
    "Ask": "kernel",
    "Hist": "kernel",
}

# Paper directories scanned for namecert markers. concrete_instances holds
# per-region object certificates; core / hardening / proof_standing /
# proof_sprint / capstones contain kernel-level and meta certificates that
# nonetheless ground a region's stage.
PAPER_NAMECERT_DIRS = [
    PAPER_INSTANCES,
    ROOT / "papers" / "bedc" / "parts" / "core",
    ROOT / "papers" / "bedc" / "parts" / "hardening",
    ROOT / "papers" / "bedc" / "parts" / "proof_standing",
    ROOT / "papers" / "bedc" / "parts" / "proof_sprint",
    ROOT / "papers" / "bedc" / "parts" / "capstones",
]


def collect_namecert_theorems_per_region() -> dict[str, list[dict]]:
    """Walk all paper chapters that may carry namecert markers; return
    {region_id: [{name, status, file}, ...]}.

    A 'namecert theorem' is any \\leanchecked / \\leanstmt target whose Lean
    name matches *NameCert* or *Name(_)Certificate* (the BEDC convention for
    the object-completion theorems). Stripped underscore escapes are resolved.
    Markers in core / hardening / proof_standing also count: they ground the
    kernel and nat / add regions whose proofs live in FKernel.
    """
    out: dict[str, list[dict]] = defaultdict(list)
    paper_root = ROOT / "papers" / "bedc" / "parts"
    for top in PAPER_NAMECERT_DIRS:
        if not top.exists():
            continue
        for f in top.rglob("*.tex"):
            try:
                rel = f.relative_to(paper_root)
                text = f.read_text(encoding="utf-8", errors="ignore")
            except Exception:
                continue
            for m in NAMECERT_TARGET_RE.finditer(text):
                status = m.group(1).removeprefix("lean")  # 'checked' or 'stmt'
                full_target = m.group(2).replace("\\_", "_")
                module = m.group(3)  # e.g. 'FieldUp', 'NatUp', 'Unary', 'NameCert'
                if "FKernel" in m.group(2):
                    region = FKERNEL_REGION_OVERRIDES.get(module, "kernel")
                    short = full_target.split(".")[-1].lower()
                    if short.startswith("add"):
                        region = "add"
                    elif short.startswith("nat"):
                        region = "nat"
                else:
                    region = canonical(lean_module_to_region(f"BEDC.Derived.{module}"))
                if not region:
                    continue
                out[region].append({
                    "name": full_target,
                    "short": full_target.split(".")[-1],
                    "status": status,
                    "file": str(rel),
                })
    # Deduplicate (same target may appear in multiple chapters)
    for region in out:
        seen = set()
        unique = []
        for entry in out[region]:
            if entry["name"] in seen:
                continue
            seen.add(entry["name"])
            unique.append(entry)
        out[region] = sorted(unique, key=lambda e: (0 if e["status"] == "checked" else 1, e["short"]))
    return dict(out)


# Map a paper chapter filename to a region id in HIERARCHY.
# Most chapters follow `NN_<region>_namecert_construction.tex` or similar;
# the substring matches below cover all current concrete_instances files.
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


# Regions that are intentionally schema-only horizons. These should NOT be
# coloured the same as "scaffold" (paper exists, Lean awaits): they are by
# design without closed Lean witnesses.
SCHEMA_ONLY_REGIONS: set[str] = {
    "interhist",  # multi-Hist locality capstone — entire chapter schema-only
    "observer",   # observer-Hist identity capstone — declarative re-reading, no Lean obligations yet
}


def aggregate_markers_per_region(per_chapter: list[dict]) -> dict[str, dict[str, int]]:
    """Sum paper marker counts across chapters belonging to each region.

    Region resolution priority:
      1. subdir name (e.g. files in concrete_instances/field/ -> 'field')
      2. paper_file_to_region heuristic on the basename
    """
    out: dict[str, dict[str, int]] = defaultdict(lambda: {"checked": 0, "stmt": 0, "def": 0})
    for row in per_chapter:
        region = row.get("subdir") or paper_file_to_region(row.get("name", row["file"]))
        if not region:
            continue
        out[region]["checked"] += row["checked"]
        out[region]["stmt"] += row["stmt"]
        out[region]["def"] += row["def"]
    return dict(out)


# Constants used by the new auto-derived dep graph
SCHEMA_HORIZON_HINT = re.compile(r"SCHEMA-ONLY HORIZON|schema-only horizon", re.IGNORECASE)


def detect_schema_only_regions() -> set[str]:
    """Detect regions whose primary chapter explicitly flags itself as
    schema-only horizon. Returns a set of region ids. Combined with
    SCHEMA_ONLY_REGIONS hardcoded list."""
    detected: set[str] = set()
    capstones_dir = PAPER_INSTANCES.parent / "capstones"
    for f in capstones_dir.rglob("*.tex") if capstones_dir.exists() else []:
        text = f.read_text(encoding="utf-8", errors="ignore")
        # only flag a capstone as schema-only when it ALSO has zero \leanchecked
        # markers (lots of "schema-only" mentions inside a normal proof chapter
        # would be a false positive otherwise)
        if SCHEMA_HORIZON_HINT.search(text) and "\\leanchecked{" not in text:
            region = CAPSTONE_FILE_TO_REGION.get(f.stem)
            if region:
                detected.add(region)
    return detected | SCHEMA_ONLY_REGIONS


def monthly_commit_activity() -> list[dict]:
    """Group git log by month, return commits per month over the project lifetime."""
    out = shell(["git", "log", "--all", "--pretty=format:%aI"])
    months: Counter[str] = Counter()
    for line in out.splitlines():
        try:
            d = datetime.fromisoformat(line.strip())
        except ValueError:
            continue
        ym = d.strftime("%Y-%m")
        months[ym] += 1
    return [{"month": m, "commits": c} for m, c in sorted(months.items())]


def critical_path_targets() -> dict:
    """Run lean4/scripts/critical_path.py and return its JSON."""
    try:
        out = shell(["python3", "lean4/scripts/critical_path.py"])
        return json.loads(out)
    except Exception as e:
        return {"top": [], "error": str(e)}


# Capstone files don't follow the concrete_instances naming convention; map them
# to region ids so they show up as nodes in the graph alongside namecert regions.
CAPSTONE_FILE_TO_REGION: dict[str, str] = {
    "observer_hist_identity": "observer",
    "inter_hist_locality": "interhist",
}

# A region is treated as a deliberate schema-only horizon (purple in the viz)
# rather than a scaffold-pending entry (gray) when its identifier is in this
# small set. The rest of the project's structure is derived from sources.
SCHEMA_ONLY_REGIONS: set[str] = {"interhist", "observer"}

LEAN_IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)", re.MULTILINE)
PAPER_AUTOREF_RE = re.compile(r"\\autoref\{ch:concrete-instances-([a-z][a-z0-9\-]*?)(?:-namecert)?\}")
PAPER_CAPSTONE_AUTOREF_RE = re.compile(r"\\autoref\{ch:capstones-([a-z][a-z0-9\-]*?)\}")


# Aliases that fold paper-side and Lean-side spellings into a single region id.
# Whenever a piece of source data names something on the left, treat it as the
# right-hand canonical id. Add an entry here only when both forms refer to the
# *same* mathematical object split across two source-naming conventions.
REGION_ALIASES: dict[str, str] = {
    "analyticcontinuation": "anacont",
    "contourintegral":      "contour",
    "criticalstrip":        "critstrip",
    "zetacontinuation":     "zetacont",
    "complexdifferentiability": "complexdiff",
    # `52_real_analytic_namecert_construction.tex` lives under the real region
    "realanalytic": "real",
    # `54_complex_analytic` is the analytic-continuation operation specialized
    "complexanalytic": "anacont",
    # `55_complex_topology` extends the complex namecert
    "complextopology": "complex",
    # `53_gamma_function` is the schema-only Gamma block inside zeta-continuation
    "gammafunction": "zetacont",
}


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


# Top-level concrete_instances chapters are kept only if their filename
# indicates a namecert / operation / application / certificate construction.
# This drops framework chapters (01_signature, 02_concrete_gap, 03_globalize)
# from the node set without needing per-chapter blacklists.
NAMECERT_CHAPTER_KEYWORDS = (
    "_namecert_construction",
    "_operation",
    "_application",
    "_certificate",
)


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


def derive_dependency_edges() -> tuple[dict[str, set[str]], set[str]]:
    """Walk sources to build the dep graph in two phases.

    Phase 1 -- discover canonical region ids from FILE existence (Lean files
              under BEDC/Derived/, namecert chapters in concrete_instances/,
              and the listed capstone files).

    Phase 2 -- walk text content (Lean `import` lines, paper
              `\\autoref{ch:...}` references) and add edges only between
              already-known regions. References to non-region targets (e.g.
              meta-chapters like `concrete-gap-policy`) are ignored as edge
              endpoints.

    This keeps spurious / non-namecert chapter labels out of the node set.
    """
    regions: set[str] = set()

    # Phase 1: regions from files
    for f in LEAN_DIR.rglob("*.lean"):
        r = lean_file_to_region(f)
        if r:
            regions.add(r)
    if PAPER_INSTANCES.exists():
        for f in PAPER_INSTANCES.rglob("*.tex"):
            r = paper_chapter_to_region(f)
            if r:
                regions.add(canonical(r) or r)
    capstones_dir = PAPER_INSTANCES.parent / "capstones"
    if capstones_dir.exists():
        for f in capstones_dir.rglob("*.tex"):
            r = CAPSTONE_FILE_TO_REGION.get(f.stem)
            if r:
                regions.add(r)

    # Always include kernel even if FKernel scan finds no .lean (defensive)
    regions.add("kernel")

    deps: dict[str, set[str]] = defaultdict(set)

    # Phase 2: collect edges between known regions only
    for f in LEAN_DIR.rglob("*.lean"):
        my_region = lean_file_to_region(f)
        if not my_region or my_region not in regions:
            continue
        for imp in parse_lean_imports(f):
            dep = lean_module_to_region(imp)
            if dep and dep in regions and dep != my_region:
                deps[my_region].add(dep)

    if PAPER_INSTANCES.exists():
        for f in PAPER_INSTANCES.rglob("*.tex"):
            my_region = canonical(paper_chapter_to_region(f))
            if not my_region or my_region not in regions:
                continue
            for r in parse_paper_autorefs(f):
                rc = canonical(r)
                if rc and rc in regions and rc != my_region:
                    deps[my_region].add(rc)

    if capstones_dir.exists():
        for f in capstones_dir.rglob("*.tex"):
            my_region = CAPSTONE_FILE_TO_REGION.get(f.stem)
            if not my_region:
                continue
            for r in parse_paper_autorefs(f):
                rc = canonical(r)
                if rc and rc in regions and rc != my_region:
                    deps[my_region].add(rc)

    for r in regions:
        deps.setdefault(r, set())
    return dict(deps), regions


def compute_levels(deps: dict[str, set[str]]) -> dict[str, int]:
    """Longest-path level from leaves (nodes without deps) to each node, with cycle guard."""
    level: dict[str, int] = {}
    visiting: set[str] = set()

    def lvl(n: str) -> int:
        if n in level:
            return level[n]
        if n in visiting:
            return 0  # cycle: fall back to 0
        visiting.add(n)
        d = deps.get(n, set())
        if not d:
            level[n] = 0
        else:
            level[n] = 1 + max(lvl(p) for p in d)
        visiting.discard(n)
        return level[n]

    for n in deps:
        lvl(n)
    return level


def _grade_index(grade: str | None, order: list[str]) -> int:
    if grade in order:
        return order.index(grade)
    return -1


def collect_closure_per_region() -> dict[str, dict]:
    """Scan paper for closurestatus blocks.

    Returns {region_id: {
        'theory_closure': str|None,
        'formal_status': str|None,
        'lean_target': str|None,
        'bridge_status': str|None,
        'scope_closed': str|None,
        'not_claimed': str|None,
        'upgrade_path': str|None,
    }}.
    """
    out: dict[str, dict] = {}
    paper_root = ROOT / "papers" / "bedc" / "parts"
    for tex in paper_root.rglob("*.tex"):
        try:
            text = tex.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue
        for m in CLOSURESTATUS_BEGIN_RE.finditer(text):
            region = canonical(m.group(1).lower())
            if not region:
                continue

            tail = text[m.end():]
            end_match = CLOSURESTATUS_END_RE.search(tail)
            body = tail[:end_match.start()] if end_match else tail

            tc_match = THEORYCLOSURE_RE.search(body)
            fs_match = FORMALSTATUS_RE.search(body)
            lt_match = LEANTARGET_RE.search(body)
            bs_match = BRIDGESTATUS_RE.search(body)
            theory_closure = tc_match.group(1) if tc_match else None
            formal_status = fs_match.group(1) if fs_match else None
            lean_target = (
                lt_match.group(1).replace("\\_", "_").strip()
                if lt_match else None
            )
            bridge_status = bs_match.group(1).strip() if bs_match else None
            scope_closed = _macro_arg(body, "scopeclosed")
            not_claimed = _macro_arg(body, "notclaimed")
            upgrade_path = _macro_arg(body, "upgradepath")

            current = {
                "theory_closure": theory_closure,
                "formal_status": formal_status,
                "lean_target": lean_target,
                "bridge_status": bridge_status,
                "scope_closed": scope_closed,
                "not_claimed": not_claimed,
                "upgrade_path": upgrade_path,
            }
            prev = out.get(region)
            if prev is None:
                out[region] = current
                continue

            prev_theory = _grade_index(prev.get("theory_closure"), CLOSURE_GRADE_ORDER)
            cur_theory = _grade_index(theory_closure, CLOSURE_GRADE_ORDER)
            if cur_theory > prev_theory:
                out[region] = current
                continue

            if cur_theory == prev_theory:
                prev_formal = _grade_index(prev.get("formal_status"), FORMAL_GRADE_ORDER)
                cur_formal = _grade_index(formal_status, FORMAL_GRADE_ORDER)
                if cur_formal > prev_formal:
                    prev["formal_status"] = formal_status
                if prev.get("lean_target") is None and lean_target:
                    prev["lean_target"] = lean_target
                if prev.get("bridge_status") is None and bridge_status:
                    prev["bridge_status"] = bridge_status
                if prev.get("scope_closed") is None and scope_closed:
                    prev["scope_closed"] = scope_closed
                if prev.get("not_claimed") is None and not_claimed:
                    prev["not_claimed"] = not_claimed
                if prev.get("upgrade_path") is None and upgrade_path:
                    prev["upgrade_path"] = upgrade_path
    return out


def build_dependency_graph() -> dict:
    """Build cytoscape graph by analysing Lean imports and paper \\autoref
    cross-references. Augmented with theorem counts, paper marker counts,
    and critical-path scores from current state."""
    cp = critical_path_targets()
    region_thms = count_lean_theorems_per_region()
    paper_per_chapter = count_paper_markers_per_chapter()
    paper_per_region = aggregate_markers_per_region(paper_per_chapter)
    namecert_per_region = collect_namecert_theorems_per_region()
    closure_per_region = collect_closure_per_region()

    deps_map, all_regions = derive_dependency_edges()
    schema_set = detect_schema_only_regions()
    levels = compute_levels(deps_map)
    max_level = max(levels.values()) if levels else 0

    # critical_path data, but only for regions we know about
    cp_data: dict[str, dict] = {}
    for entry in cp.get("top", []):
        name = entry.get("name", "")
        if name in all_regions:
            cp_data[name] = entry

    nodes: list[dict] = []
    for nid in sorted(all_regions):
        thms = region_thms.get(nid, {}).get("theorems", 0)
        cp_entry = cp_data.get(nid, {})
        markers = paper_per_region.get(nid, {"checked": 0, "stmt": 0, "def": 0})
        namecerts = namecert_per_region.get(nid, [])
        namecerts_checked = [t for t in namecerts if t["status"] == "checked"]
        namecerts_stmt    = [t for t in namecerts if t["status"] == "stmt"]
        if nid == "kernel":
            label_en, label_zh = "Kernel", "内核"
        else:
            label_en = nid + "Up"
            label_zh = nid + "Up"
        nodes.append({
            "id": nid,
            "label_en": label_en,
            "label_zh": label_zh,
            "thms": cp_entry.get("thms", thms),
            "level": levels.get(nid, 0),
            "downstream": cp_entry.get("downstream", 0),
            "score": cp_entry.get("score", 0.0),
            "checked": markers["checked"],
            "stmt": markers["stmt"],
            "defs": markers["def"],
            "schema_only": nid in schema_set,
            # Author-declared chapter closure block, shared with critical_path.py.
            # null until the author writes both axes in a closurestatus block.
            "closed_theoryclosure": (
                closure_per_region.get(nid) or {}
            ).get("theory_closure"),
            "closed_formalstatus": (
                closure_per_region.get(nid) or {}
            ).get("formal_status"),
            "closure_grounding": (
                closure_per_region.get(nid) or {}
            ).get("lean_target"),
            "closed_bridge_status": (
                closure_per_region.get(nid) or {}
            ).get("bridge_status"),
            "scope_closed": (
                closure_per_region.get(nid) or {}
            ).get("scope_closed"),
            "not_claimed": (
                closure_per_region.get(nid) or {}
            ).get("not_claimed"),
            "upgrade_path": (
                closure_per_region.get(nid) or {}
            ).get("upgrade_path"),
            # Namecert-theorem-grounded data (kept for the detail panel,
            # NOT used for proven/progress classification; closure is).
            "namecert_theorems": namecerts,
            "namecert_checked": len(namecerts_checked),
            "namecert_stmt": len(namecerts_stmt),
        })

    edges: list[dict] = []
    for nid, dep_set in deps_map.items():
        for d in dep_set:
            edges.append({"source": d, "target": nid})

    return {"nodes": nodes, "edges": edges, "max_level": max_level}


def build_glossary() -> dict:
    """Load bilingual glossary from the source-of-truth JSON file.

    The canonical glossary lives in
    `docs/dossier/data_source/glossary.json` (committed to git). This
    function strips the `_meta` block and per-entry `aliases` list
    (both used by `tools/check_glossary.py` as gating data, not needed
    by the front-end renderer).
    """
    src = ROOT / "docs" / "dossier" / "data_source" / "glossary.json"
    with src.open(encoding="utf-8") as fh:
        data = json.load(fh)
    out: dict[str, dict] = {}
    for k, v in data.items():
        if k.startswith("_"):
            continue
        out[k] = {ek: ev for ek, ev in v.items() if ek != "aliases"}
    return out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        help="write dependency graph JSON to this path",
    )
    args = parser.parse_args()

    DATA_DIR.mkdir(parents=True, exist_ok=True)

    print("[build-dossier-status] scanning Lean theorem counts...", file=sys.stderr)
    region_thms = count_lean_theorems_per_region()

    print("[build-dossier-status] scanning paper markers...", file=sys.stderr)
    paper_markers = count_paper_markers_per_chapter()

    print("[build-dossier-status] computing monthly activity...", file=sys.stderr)
    activity = monthly_commit_activity()

    print("[build-dossier-status] running critical_path.py...", file=sys.stderr)
    cp = critical_path_targets()

    print("[build-dossier-status] building dependency graph...", file=sys.stderr)
    deps = build_dependency_graph()

    print("[build-dossier-status] building glossary...", file=sys.stderr)
    glossary = build_glossary()

    # ensure every dependency-graph node has a glossary entry; default to its id
    for node in deps["nodes"]:
        nid = node["id"]
        if nid in glossary:
            node["label_en"] = glossary[nid]["en"]["label"]
            node["label_zh"] = glossary[nid]["zh"]["label"]

    total_thms = sum(r["theorems"] for r in region_thms.values())
    valid_region_ids = {n["id"] for n in deps["nodes"]}
    status = {
        "generated_at": datetime.utcnow().isoformat() + "Z",
        "total_theorems": total_thms,
        "regions": [
            {"name": name, **stats}
            for name, stats in sorted(region_thms.items(), key=lambda kv: -kv[1]["theorems"])
        ],
        "paper_markers": paper_markers,
        "monthly_activity": activity,
        "critical_path": [
            entry for entry in cp.get("top", [])
            if entry.get("name", "") in valid_region_ids
        ][:15],
        "top_root_unblocks": [
            entry for entry in cp.get("top_root_unblocks", [])
            if entry.get("name", "") in valid_region_ids
        ][:10],
        "top_transitions": cp.get("top_transitions", {}),
        "closed_horizons": cp.get("closed_horizons", {}),
        "open_horizons": cp.get("open_horizons", 0),
        "granularity": cp.get("granularity", "chapter"),
    }

    (DATA_DIR / "status.json").write_text(json.dumps(status, indent=2), encoding="utf-8")
    (DATA_DIR / "glossary.json").write_text(json.dumps(glossary, indent=2, ensure_ascii=False), encoding="utf-8")
    (DATA_DIR / "dependency.json").write_text(json.dumps(deps, indent=2, ensure_ascii=False), encoding="utf-8")
    if args.output:
        args.output.write_text(json.dumps(deps, indent=2, ensure_ascii=False), encoding="utf-8")

    print(
        f"[build-dossier-status] wrote {DATA_DIR.relative_to(ROOT)}/{{status,glossary,dependency}}.json "
        f"-- {total_thms} theorems, {len(deps['nodes'])} nodes, {len(deps['edges'])} edges, "
        f"{len(glossary)} glossary entries",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

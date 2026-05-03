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


def build_dependency_graph() -> dict:
    """Build cytoscape graph by analysing Lean imports and paper \\autoref
    cross-references. Augmented with theorem counts, paper marker counts,
    and critical-path scores from current state."""
    cp = critical_path_targets()
    region_thms = count_lean_theorems_per_region()
    paper_per_chapter = count_paper_markers_per_chapter()
    paper_per_region = aggregate_markers_per_region(paper_per_chapter)

    deps_map, all_regions = derive_dependency_edges()
    schema_set = detect_schema_only_regions()
    levels = compute_levels(deps_map)
    max_level = max(levels.values()) if levels else 0

    # critical_path data, but only for regions we know about
    cp_data: dict[str, dict] = {}
    for entry in cp.get("top", []) + cp.get("rest", []) + cp.get("saturated", []):
        name = entry.get("name", "")
        if name in all_regions:
            cp_data[name] = entry

    nodes: list[dict] = []
    for nid in sorted(all_regions):
        thms = region_thms.get(nid, {}).get("theorems", 0)
        cp_entry = cp_data.get(nid, {})
        markers = paper_per_region.get(nid, {"checked": 0, "stmt": 0, "def": 0})
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
        })

    edges: list[dict] = []
    for nid, dep_set in deps_map.items():
        for d in dep_set:
            edges.append({"source": d, "target": nid})

    return {"nodes": nodes, "edges": edges, "max_level": max_level}


def build_glossary() -> dict:
    """Hand-curated bilingual glossary of BEDC kernel + namecert terms.

    Each entry: { en: {label, desc}, zh: {label, desc} }.
    """
    G = {
        # Kernel primitives
        "BHist": {
            "en": {"label": "BHist", "desc": "Closed-inductive type of distinction histories. Empty / E0 / E1."},
            "zh": {"label": "BHist", "desc": "区分历史的闭合归纳类型. Empty / E0 / E1."},
        },
        "Hist": {
            "en": {"label": "Hist", "desc": "A specific value of BHist; the trace of an observer's distinctions."},
            "zh": {"label": "Hist", "desc": "BHist 的具体值; 一个观察者的区分轨迹."},
        },
        "Cont": {
            "en": {"label": "Cont", "desc": "Continuation relation: Cont(h, m, h') means h continues to h' by emitting mark m."},
            "zh": {"label": "Cont", "desc": "延展关系: Cont(h, m, h') 表示 h 通过 emit mark m 延续为 h'."},
        },
        "hsame": {
            "en": {"label": "hsame", "desc": "History sameness: identifies two Hists as the same observer trace."},
            "zh": {"label": "hsame", "desc": "历史同一性: 把两个 Hist 认定为同一个观察者轨迹."},
        },
        "psame": {
            "en": {"label": "psame", "desc": "Package sameness: classifier on Package values."},
            "zh": {"label": "psame", "desc": "Package 同一性: Package 值上的分类器."},
        },
        "msame": {
            "en": {"label": "msame", "desc": "Mark sameness: identifies two BMarks."},
            "zh": {"label": "msame", "desc": "Mark 同一性: 识别两个 BMark."},
        },
        "E0": {
            "en": {"label": "E0", "desc": "One of two binary distinction constructors on BHist."},
            "zh": {"label": "E0", "desc": "BHist 上两个二元区分构造子之一."},
        },
        "E1": {
            "en": {"label": "E1", "desc": "The other binary distinction constructor on BHist."},
            "zh": {"label": "E1", "desc": "BHist 上另一个二元区分构造子."},
        },
        # NameCert framework
        "NameCert": {
            "en": {"label": "NameCert", "desc": "Naming certificate: 5-field structure (carrier, classifier, closure laws) replacing Quot."},
            "zh": {"label": "NameCert", "desc": "命名证书: 5 字段结构(载体, 分类器, 闭合律), 替代 Quot."},
        },
        "SourceSpec": {
            "en": {"label": "SourceSpec", "desc": "Source specification: which Hists qualify as carriers."},
            "zh": {"label": "SourceSpec", "desc": "源规范: 哪些 Hist 满足载体条件."},
        },
        "PatternSpec": {
            "en": {"label": "PatternSpec", "desc": "Pattern specification: shape of admissible patterns."},
            "zh": {"label": "PatternSpec", "desc": "模式规范: 可接受模式的形状."},
        },
        "ClassifierSpec": {
            "en": {"label": "ClassifierSpec", "desc": "Classifier specification: when two carriers are equivalent."},
            "zh": {"label": "ClassifierSpec", "desc": "分类器规范: 两个载体何时等价."},
        },
        "StabilityCert": {
            "en": {"label": "StabilityCert", "desc": "Stability certificate: hsame-respect of carrier and classifier."},
            "zh": {"label": "StabilityCert", "desc": "稳定证书: 载体和分类器对 hsame 的尊重."},
        },
        "LedgerPolicy": {
            "en": {"label": "LedgerPolicy", "desc": "Ledger policy: structural laws of the certificate."},
            "zh": {"label": "LedgerPolicy", "desc": "账本策略: 证书的结构性律法."},
        },
        # Methodology
        "axiom-purity": {
            "en": {"label": "axiom-purity", "desc": "BEDC invariant: no Classical.choice, no Quot.sound, no propext."},
            "zh": {"label": "axiom-purity", "desc": "BEDC 不变量: 禁 Classical.choice / Quot.sound / propext."},
        },
        "schema-only": {
            "en": {"label": "schema-only horizon", "desc": "Interface formalized but closed witnesses deferred."},
            "zh": {"label": "schema-only 视界", "desc": "接口已形式化但闭合 witness 推迟."},
        },
        # Number-system Up types
        "nat": {
            "en": {"label": "Nat", "desc": "Unary natural numbers as Hist segments."},
            "zh": {"label": "自然数", "desc": "一元自然数, 作为 Hist 段."},
        },
        "int": {
            "en": {"label": "Int", "desc": "Integers as signed pairs of Nat."},
            "zh": {"label": "整数", "desc": "整数, 作为带符号 Nat 对."},
        },
        "rat": {
            "en": {"label": "Rat", "desc": "Rationals as Int / positive Nat pairs."},
            "zh": {"label": "有理数", "desc": "有理数, 作为 Int / 正 Nat 对."},
        },
        "real": {
            "en": {"label": "Real", "desc": "Reals as regular Cauchy sequences over Rat."},
            "zh": {"label": "实数", "desc": "实数, 作为 Rat 上的正则 Cauchy 序列."},
        },
        "complex": {
            "en": {"label": "Complex", "desc": "Complex numbers as pairs of Reals."},
            "zh": {"label": "复数", "desc": "复数, 作为实数对."},
        },
        "bool": {
            "en": {"label": "BoolUp", "desc": "Booleans as a 2-element finite Hist type."},
            "zh": {"label": "BoolUp", "desc": "布尔值, 作为 2-元素有限 Hist 类型."},
        },
        "option": {
            "en": {"label": "OptionUp", "desc": "Optional values: none / some(x)."},
            "zh": {"label": "OptionUp", "desc": "可选值: none / some(x)."},
        },
        "prod": {
            "en": {"label": "ProdUp", "desc": "Product types A x B as Hist pairs."},
            "zh": {"label": "ProdUp", "desc": "乘积类型 A x B, 作为 Hist 对."},
        },
        "sum": {
            "en": {"label": "SumUp", "desc": "Sum types A + B as tagged Hist."},
            "zh": {"label": "SumUp", "desc": "和类型 A + B, 作为带标签 Hist."},
        },
        "list": {
            "en": {"label": "ListUp", "desc": "Lists over a base type, as Hist sequences."},
            "zh": {"label": "ListUp", "desc": "列表, 作为 Hist 序列."},
        },
        "prime": {
            "en": {"label": "PrimeUp", "desc": "Primality predicate; Euclid's infinitude; FTA."},
            "zh": {"label": "PrimeUp", "desc": "素数谓词; Euclid 无穷性; 算术基本定理."},
        },
        # Algebraic Up types
        "monoid": {
            "en": {"label": "MonoidUp", "desc": "Monoid: associative binary op + unit."},
            "zh": {"label": "MonoidUp", "desc": "幺半群: 结合性二元运算 + 单位."},
        },
        "group": {
            "en": {"label": "GroupUp", "desc": "Group: monoid + inverse element."},
            "zh": {"label": "GroupUp", "desc": "群: 幺半群 + 逆元."},
        },
        "abgroup": {
            "en": {"label": "AbGroupUp", "desc": "Abelian group: commutative group."},
            "zh": {"label": "AbGroupUp", "desc": "阿贝尔群: 可交换群."},
        },
        "ring": {
            "en": {"label": "RingUp", "desc": "Ring: AbGroup + multiplicative monoid + distributivity."},
            "zh": {"label": "RingUp", "desc": "环: AbGroup + 乘法幺半群 + 分配律."},
        },
        "commring": {
            "en": {"label": "CommRingUp", "desc": "Commutative ring."},
            "zh": {"label": "CommRingUp", "desc": "交换环."},
        },
        "field": {
            "en": {"label": "FieldUp", "desc": "Field: commutative ring + multiplicative inverses for nonzero."},
            "zh": {"label": "FieldUp", "desc": "域: 交换环 + 非零元有乘法逆."},
        },
        "module": {
            "en": {"label": "ModuleUp", "desc": "Module over a ring."},
            "zh": {"label": "ModuleUp", "desc": "环上的模."},
        },
        "vecspace": {
            "en": {"label": "VecSpaceUp", "desc": "Vector space over a field."},
            "zh": {"label": "VecSpaceUp", "desc": "域上的向量空间."},
        },
        "linearmap": {
            "en": {"label": "LinearMapUp", "desc": "Linear map between modules."},
            "zh": {"label": "LinearMapUp", "desc": "模之间的线性映射."},
        },
        "matrix": {
            "en": {"label": "MatrixUp", "desc": "Matrices over a ring."},
            "zh": {"label": "MatrixUp", "desc": "环上的矩阵."},
        },
        "polynomial": {
            "en": {"label": "PolynomialUp", "desc": "Polynomials in one variable."},
            "zh": {"label": "PolynomialUp", "desc": "单变量多项式."},
        },
        "fps": {
            "en": {"label": "FormalPowerSeriesUp", "desc": "Formal power series."},
            "zh": {"label": "FormalPowerSeriesUp", "desc": "形式幂级数."},
        },
        "add": {
            "en": {"label": "AddUp", "desc": "Additive structure on natural numbers."},
            "zh": {"label": "AddUp", "desc": "自然数上的加法结构."},
        },
        # Order / lattice
        "preorder": {
            "en": {"label": "PreorderUp", "desc": "Preorder: reflexive + transitive."},
            "zh": {"label": "PreorderUp", "desc": "预序: 自反 + 传递."},
        },
        "poset": {
            "en": {"label": "POSetUp", "desc": "Partial order: preorder + antisymmetry."},
            "zh": {"label": "POSetUp", "desc": "偏序: 预序 + 反对称."},
        },
        "totalorder": {
            "en": {"label": "TotalOrderUp", "desc": "Total order: poset + trichotomy."},
            "zh": {"label": "TotalOrderUp", "desc": "全序: 偏序 + 三分律."},
        },
        "lattice": {
            "en": {"label": "LatticeUp", "desc": "Lattice: poset with binary join and meet."},
            "zh": {"label": "LatticeUp", "desc": "格: 带二元 join / meet 的偏序."},
        },
        "interval": {
            "en": {"label": "IntervalUp", "desc": "Closed interval [a, b] over a totally-ordered carrier."},
            "zh": {"label": "IntervalUp", "desc": "全序载体上的闭区间 [a, b]."},
        },
        # Topology
        "metric": {
            "en": {"label": "MetricSpaceUp", "desc": "Metric space: distance with triangle inequality."},
            "zh": {"label": "MetricSpaceUp", "desc": "度量空间: 满足三角不等式的距离."},
        },
        "compact": {
            "en": {"label": "CompactUp", "desc": "Compactness: total boundedness + completeness."},
            "zh": {"label": "CompactUp", "desc": "紧致性: 全有界 + 完备."},
        },
        "continuous": {
            "en": {"label": "ContinuousUp", "desc": "Continuous functions with explicit modulus."},
            "zh": {"label": "ContinuousUp", "desc": "带显式模量的连续函数."},
        },
        "s1": {
            "en": {"label": "S1Up", "desc": "Circle S^1 as a quotient of the unit interval."},
            "zh": {"label": "S1Up", "desc": "圆 S^1, 作为单位区间的商."},
        },
        "circle": {
            "en": {"label": "CircleUp", "desc": "Circle as compact 1-manifold."},
            "zh": {"label": "CircleUp", "desc": "圆, 作为紧致 1-流形."},
        },
        # Categorical
        "category": {
            "en": {"label": "CategoryUp", "desc": "Category as Hist of objects + Cont as Hom."},
            "zh": {"label": "CategoryUp", "desc": "范畴, 对象=Hist, Hom=Cont."},
        },
        "functor": {
            "en": {"label": "FunctorUp", "desc": "Functor between categories."},
            "zh": {"label": "FunctorUp", "desc": "范畴间的函子."},
        },
        "nattrans": {
            "en": {"label": "NatTransUp", "desc": "Natural transformation."},
            "zh": {"label": "NatTransUp", "desc": "自然变换."},
        },
        # RH chain (current scaffold) -- short labels match preamble \Up macros.
        "complexlimit": {
            "en": {"label": "CplxLim", "desc": "Convergence of complex sequences with explicit modulus."},
            "zh": {"label": "复极限", "desc": "带显式模量的复数列收敛."},
        },
        "convergenceradius": {
            "en": {"label": "ConvRad", "desc": "Radius of convergence of a power series."},
            "zh": {"label": "收敛半径", "desc": "幂级数的收敛半径."},
        },
        "complexdiff": {
            "en": {"label": "CplxDiff", "desc": "Complex differentiability + Cauchy-Riemann."},
            "zh": {"label": "复可微", "desc": "复可微 + Cauchy-Riemann."},
        },
        "holomorphic": {
            "en": {"label": "Holo", "desc": "Holomorphic functions on open disks."},
            "zh": {"label": "全纯", "desc": "开盘上的全纯函数."},
        },
        "complexseries": {
            "en": {"label": "CplxSer", "desc": "Convergent infinite complex sums."},
            "zh": {"label": "复级数", "desc": "收敛的无限复求和."},
        },
        "dirichletseries": {
            "en": {"label": "Dirichlet", "desc": "Dirichlet series with abscissa of absolute convergence."},
            "zh": {"label": "Dirichlet", "desc": "Dirichlet 级数及其绝对收敛 abscissa."},
        },
        "zetabasic": {
            "en": {"label": "ZetaBasic", "desc": "Riemann zeta on Re(s) > 1, with Euler product."},
            "zh": {"label": "ζ 基础", "desc": "Re(s)>1 上的 Riemann zeta 加 Euler 乘积."},
        },
        "zetacont": {
            "en": {"label": "ZetaCont", "desc": "Analytic continuation of zeta to C \\ {1}."},
            "zh": {"label": "ζ 延拓", "desc": "zeta 解析延拓到 C \\ {1}."},
        },
        "critstrip": {
            "en": {"label": "CritStrip", "desc": "The critical strip 0 < Re(s) < 1 and the line Re(s) = 1/2."},
            "zh": {"label": "关键带", "desc": "关键带 0<Re(s)<1 与关键线 Re(s)=1/2."},
        },
        "zetazeros": {
            "en": {"label": "ZetaZeros", "desc": "Zero predicate of zeta; trivial vs non-trivial zeros."},
            "zh": {"label": "ζ 零点", "desc": "zeta 零点谓词; 平凡零点 vs 非平凡零点."},
        },
        "contour": {
            "en": {"label": "Contour", "desc": "Contour integration as operation on holomorphic functions."},
            "zh": {"label": "围道积分", "desc": "围道积分, 作为全纯函数上的操作."},
        },
        "anacont": {
            "en": {"label": "AnaCont", "desc": "Analytic continuation as operation on holomorphic charts."},
            "zh": {"label": "解析延拓", "desc": "解析延拓, 作为全纯图册上的操作."},
        },
        # Reflection / capstones (recent)
        "observer": {
            "en": {"label": "Observer-Hist Identity", "desc": "Observer = Hist; observation = Cont; time = Hist growth."},
            "zh": {"label": "观察者-Hist 同一性", "desc": "观察者 = Hist; 观察 = Cont; 时间 = Hist 增长."},
        },
        "interhist": {
            "en": {"label": "Inter-Hist Locality", "desc": "Multi-Hist roadmap: from no global frame to a constant max-causal-rate."},
            "zh": {"label": "跨-Hist 局部性", "desc": "多 Hist 路线图: 从无全局 frame 到常数最大因果率."},
        },
        "kernel": {
            "en": {"label": "Finite Kernel", "desc": "BHist + Cont + hsame: the three primitives everything is built on."},
            "zh": {"label": "有限内核", "desc": "BHist + Cont + hsame: 一切都建在这三个原语上."},
        },
        # --- Roadmap / future Up types (declared in preamble, not yet active regions) ---
        "rh": {
            "en": {"label": "RHUp", "desc": "The Riemann Hypothesis as a BEDC conjecture interface."},
            "zh": {"label": "RHUp", "desc": "黎曼猜想作为 BEDC 猜想接口."},
        },
        "zeta": {
            "en": {"label": "ZetaUp", "desc": "Riemann zeta function — umbrella interface (basic + cont + zeros)."},
            "zh": {"label": "ZetaUp", "desc": "Riemann zeta 函数 — 综合接口(基础+延拓+零点)."},
        },
        "padic": {
            "en": {"label": "PadicUp", "desc": "p-adic numbers; completion of Q under p-adic norm."},
            "zh": {"label": "PadicUp", "desc": "p-adic 数; Q 在 p-adic 范数下的完备化."},
        },
        "adele": {
            "en": {"label": "AdeleUp", "desc": "Adele ring; restricted product of all completions of Q."},
            "zh": {"label": "AdeleUp", "desc": "Adele 环; Q 所有完备化的限制积."},
        },
        "norm": {
            "en": {"label": "NormUp", "desc": "Normed space interface: vector space with a length function."},
            "zh": {"label": "NormUp", "desc": "赋范空间接口: 带长度函数的向量空间."},
        },
        "hilbert": {
            "en": {"label": "HilbertUp", "desc": "Hilbert space: complete inner-product space."},
            "zh": {"label": "HilbertUp", "desc": "Hilbert 空间: 完备的内积空间."},
        },
        "magma": {
            "en": {"label": "MagmaUp", "desc": "Magma: a set with a binary operation, no further laws."},
            "zh": {"label": "MagmaUp", "desc": "Magma: 带二元运算的集合, 无更多律法."},
        },
        "semigroup": {
            "en": {"label": "SemigroupUp", "desc": "Semigroup: associative magma."},
            "zh": {"label": "SemigroupUp", "desc": "半群: 满足结合律的 magma."},
        },
        "topology": {
            "en": {"label": "TopologyUp", "desc": "Topological space interface; opens / continuity / connectedness."},
            "zh": {"label": "TopologyUp", "desc": "拓扑空间接口; 开集/连续/连通."},
        },
        "completion": {
            "en": {"label": "CompletionUp", "desc": "Completion of a metric space; Cauchy-equivalence quotient."},
            "zh": {"label": "CompletionUp", "desc": "度量空间的完备化; Cauchy 等价商."},
        },
        "calculus": {
            "en": {"label": "CalculusUp", "desc": "Differential / integral calculus on Real-valued functions."},
            "zh": {"label": "CalculusUp", "desc": "实值函数上的微分/积分."},
        },
        "measure": {
            "en": {"label": "MeasureUp", "desc": "Measure theory; Lebesgue / Borel structure."},
            "zh": {"label": "MeasureUp", "desc": "测度论; Lebesgue / Borel 结构."},
        },
        "functionalanalysis": {
            "en": {"label": "FunctionalAnalysisUp", "desc": "Banach / Hilbert spaces; bounded operators."},
            "zh": {"label": "FunctionalAnalysisUp", "desc": "Banach / Hilbert 空间; 有界算子."},
        },
        "manifold": {
            "en": {"label": "ManifoldUp", "desc": "Smooth manifold; locally Euclidean with charts."},
            "zh": {"label": "ManifoldUp", "desc": "光滑流形; 局部欧式 + 图卡."},
        },
        "bundle": {
            "en": {"label": "BundleUp", "desc": "Fiber bundle; total space + base space + projection."},
            "zh": {"label": "BundleUp", "desc": "纤维丛; 全空间 + 底空间 + 投影."},
        },
        "homology": {
            "en": {"label": "HomologyUp", "desc": "Singular / chain homology; topological invariants."},
            "zh": {"label": "HomologyUp", "desc": "奇异/链同调; 拓扑不变量."},
        },
        "eq": {
            "en": {"label": "EqUp", "desc": "Equality / sameness interface generalising hsame."},
            "zh": {"label": "EqUp", "desc": "等同接口, 泛化 hsame."},
        },
        "func": {
            "en": {"label": "FuncUp", "desc": "Function interface; generic Hist-to-Hist mapping."},
            "zh": {"label": "FuncUp", "desc": "函数接口; 通用 Hist→Hist 映射."},
        },
        "limit": {
            "en": {"label": "LimitUp", "desc": "Limit interface; generic convergence carrier."},
            "zh": {"label": "LimitUp", "desc": "极限接口; 通用收敛载体."},
        },
        "fold": {
            "en": {"label": "FoldUp", "desc": "Fold / catamorphism interface over inductive carriers."},
            "zh": {"label": "FoldUp", "desc": "归纳载体上的 fold/catamorphism 接口."},
        },
        "setlike": {
            "en": {"label": "SetLikeUp", "desc": "Set-like membership interface, finite / decidable."},
            "zh": {"label": "SetLikeUp", "desc": "类集合的成员关系接口, 有限/可判定."},
        },
        "typelike": {
            "en": {"label": "TypeLikeUp", "desc": "Type-like inhabitation interface; carriers as types."},
            "zh": {"label": "TypeLikeUp", "desc": "类类型的居留接口; 载体作类型."},
        },
        "mul": {
            "en": {"label": "MulUp", "desc": "Multiplicative monoid interface."},
            "zh": {"label": "MulUp", "desc": "乘法 monoid 接口."},
        },
        "order": {
            "en": {"label": "OrderUp", "desc": "Generic order-relation interface."},
            "zh": {"label": "OrderUp", "desc": "通用序关系接口."},
        },
    }
    return G


def main() -> int:
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
    }

    (DATA_DIR / "status.json").write_text(json.dumps(status, indent=2), encoding="utf-8")
    (DATA_DIR / "glossary.json").write_text(json.dumps(glossary, indent=2, ensure_ascii=False), encoding="utf-8")
    (DATA_DIR / "dependency.json").write_text(json.dumps(deps, indent=2, ensure_ascii=False), encoding="utf-8")

    print(
        f"[build-dossier-status] wrote {DATA_DIR.relative_to(ROOT)}/{{status,glossary,dependency}}.json "
        f"-- {total_thms} theorems, {len(deps['nodes'])} nodes, {len(deps['edges'])} edges, "
        f"{len(glossary)} glossary entries",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())

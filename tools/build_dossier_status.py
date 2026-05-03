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


# Canonical BEDC mathematical dependency tree.
# Each entry: region -> list of regions it depends on (its direct parents).
# Edge in output graph: parent -> region (the dependency points DOWN the chain).
# This is hand-curated knowledge: critical_path.py only knows the deps it was
# explicitly told about, but the BEDC layering is fixed and well-known.
HIERARCHY: dict[str, list[str]] = {
    # --- Layer 0: Kernel ---
    "kernel": [],
    # --- Layer 1: Discrete primitives (built directly on Hist/Cont) ---
    "bool": ["kernel"],
    "option": ["kernel"],
    "nat": ["kernel"],
    # --- Layer 2: Generic structure on a base type ---
    "prod": ["kernel"],
    "sum": ["kernel"],
    "list": ["kernel"],
    # --- Layer 3: Number-system tower over Nat ---
    "add": ["nat"],
    "int": ["nat"],
    "rat": ["int", "nat"],
    "real": ["rat"],
    "complex": ["real"],
    # --- Layer 3b: Prime over Nat (sibling to Int/Rat) ---
    "prime": ["nat"],
    # --- Layer 4: Algebra over Nat ---
    "monoid": ["nat"],
    "group": ["monoid"],
    "abgroup": ["group"],
    "ring": ["abgroup"],
    "commring": ["ring"],
    "field": ["commring"],
    "module": ["ring"],
    "vecspace": ["module", "field"],
    "linearmap": ["vecspace"],
    "matrix": ["vecspace"],
    "polynomial": ["commring"],
    "fps": ["polynomial"],
    # --- Layer 5: Order / lattice ---
    "preorder": ["kernel"],
    "poset": ["preorder"],
    "totalorder": ["poset"],
    "lattice": ["poset"],
    "interval": ["totalorder", "real"],
    # --- Layer 6: Topology over Real ---
    "metric": ["real"],
    "compact": ["metric"],
    "continuous": ["real"],
    "s1": ["interval"],
    "circle": ["compact"],
    # --- Layer 7: Categorical (built on Cont as Hom) ---
    "category": ["kernel"],
    "functor": ["category"],
    "nattrans": ["functor"],
    # --- Layer 8: Complex analysis (RH dependency chain) ---
    "complexlimit": ["complex"],
    "convergenceradius": ["complexlimit", "fps"],
    "complexdiff": ["complexlimit"],
    "holomorphic": ["complexdiff", "convergenceradius"],
    "complexseries": ["complexlimit"],
    "contour": ["holomorphic", "continuous"],
    "anacont": ["holomorphic"],
    # --- Layer 9: Dirichlet / Zeta tower ---
    "dirichletseries": ["complexseries", "prime"],
    "zetabasic": ["dirichletseries"],
    "zetacont": ["zetabasic", "anacont"],
    "critstrip": ["complex"],
    "zetazeros": ["zetacont", "critstrip"],
    # --- Reflection capstones (live above everything) ---
    "observer": ["kernel"],
    "interhist": ["observer"],
}


def compute_levels(hierarchy: dict[str, list[str]]) -> dict[str, int]:
    """Longest-path level from any root (kernel) to each node."""
    level: dict[str, int] = {}

    def lvl(n: str, stack: tuple[str, ...] = ()) -> int:
        if n in level:
            return level[n]
        if n in stack:
            return 0  # cycle guard
        deps = hierarchy.get(n, [])
        if not deps:
            level[n] = 0
        else:
            level[n] = 1 + max(lvl(d, stack + (n,)) for d in deps)
        return level[n]

    for n in hierarchy:
        lvl(n)
    return level


def build_dependency_graph() -> dict:
    """Build cytoscape graph using HIERARCHY as ground truth, augmented with
    theorem counts and critical-path scores from current state."""
    cp = critical_path_targets()
    region_thms = count_lean_theorems_per_region()

    cp_data: dict[str, dict] = {}
    valid_regions = set(HIERARCHY.keys())
    for entry in cp.get("top", []) + cp.get("rest", []) + cp.get("saturated", []):
        name = entry.get("name", "")
        if name in valid_regions:
            cp_data[name] = entry

    levels = compute_levels(HIERARCHY)
    max_level = max(levels.values()) if levels else 0

    paper_per_chapter = count_paper_markers_per_chapter()
    paper_per_region = aggregate_markers_per_region(paper_per_chapter)

    nodes: list[dict] = []
    for nid in HIERARCHY:
        thms = region_thms.get(nid, {}).get("theorems", 0)
        if nid == "kernel":
            # kernel theorem count comes from FKernel scan
            thms = region_thms.get("kernel", {}).get("theorems", 0)
        cp_entry = cp_data.get(nid, {})
        markers = paper_per_region.get(nid, {"checked": 0, "stmt": 0, "def": 0})
        nodes.append({
            "id": nid,
            "label_en": nid + "Up" if nid != "kernel" else "Kernel",
            "label_zh": nid + "Up" if nid != "kernel" else "内核",
            "thms": cp_entry.get("thms", thms),
            "level": levels[nid],
            "downstream": cp_entry.get("downstream", 0),
            "score": cp_entry.get("score", 0.0),
            "checked": markers["checked"],
            "stmt": markers["stmt"],
            "defs": markers["def"],
            "schema_only": nid in SCHEMA_ONLY_REGIONS,
        })

    edges: list[dict] = []
    for nid, deps in HIERARCHY.items():
        for d in deps:
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
            "en": {"label": "NatUp", "desc": "Unary natural numbers as Hist segments."},
            "zh": {"label": "NatUp", "desc": "一元自然数, 作为 Hist 段."},
        },
        "int": {
            "en": {"label": "IntUp", "desc": "Integers as signed pairs of Nat."},
            "zh": {"label": "IntUp", "desc": "整数, 作为带符号 Nat 对."},
        },
        "rat": {
            "en": {"label": "RatUp", "desc": "Rationals as Int / positive Nat pairs."},
            "zh": {"label": "RatUp", "desc": "有理数, 作为 Int / 正 Nat 对."},
        },
        "real": {
            "en": {"label": "RealUp", "desc": "Reals as regular Cauchy sequences over Rat."},
            "zh": {"label": "RealUp", "desc": "实数, 作为 Rat 上的正则 Cauchy 序列."},
        },
        "complex": {
            "en": {"label": "ComplexUp", "desc": "Complex numbers as pairs of Reals."},
            "zh": {"label": "ComplexUp", "desc": "复数, 作为实数对."},
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
        # RH chain (current scaffold)
        "complexlimit": {
            "en": {"label": "ComplexLimitUp", "desc": "Convergence of complex sequences with explicit modulus."},
            "zh": {"label": "ComplexLimitUp", "desc": "带显式模量的复数列收敛."},
        },
        "convergenceradius": {
            "en": {"label": "ConvergenceRadiusUp", "desc": "Radius of convergence of a power series."},
            "zh": {"label": "ConvergenceRadiusUp", "desc": "幂级数的收敛半径."},
        },
        "complexdiff": {
            "en": {"label": "ComplexDiffUp", "desc": "Complex differentiability + Cauchy-Riemann."},
            "zh": {"label": "ComplexDiffUp", "desc": "复可微 + Cauchy-Riemann."},
        },
        "holomorphic": {
            "en": {"label": "HolomorphicUp", "desc": "Holomorphic functions on open disks."},
            "zh": {"label": "HolomorphicUp", "desc": "开盘上的全纯函数."},
        },
        "complexseries": {
            "en": {"label": "ComplexSeriesUp", "desc": "Convergent infinite complex sums."},
            "zh": {"label": "ComplexSeriesUp", "desc": "收敛的无限复求和."},
        },
        "dirichletseries": {
            "en": {"label": "DirichletSeriesUp", "desc": "Dirichlet series with abscissa of absolute convergence."},
            "zh": {"label": "DirichletSeriesUp", "desc": "Dirichlet 级数及其绝对收敛 abscissa."},
        },
        "zetabasic": {
            "en": {"label": "ZetaBasicUp", "desc": "Riemann zeta on Re(s) > 1, with Euler product."},
            "zh": {"label": "ZetaBasicUp", "desc": "Re(s)>1 上的 Riemann zeta 加 Euler 乘积."},
        },
        "zetacont": {
            "en": {"label": "ZetaContUp", "desc": "Analytic continuation of zeta to C \\ {1}."},
            "zh": {"label": "ZetaContUp", "desc": "zeta 解析延拓到 C \\ {1}."},
        },
        "critstrip": {
            "en": {"label": "CritStripUp", "desc": "The critical strip 0 < Re(s) < 1 and the line Re(s) = 1/2."},
            "zh": {"label": "CritStripUp", "desc": "关键带 0<Re(s)<1 与关键线 Re(s)=1/2."},
        },
        "zetazeros": {
            "en": {"label": "ZetaZerosUp", "desc": "Zero predicate of zeta; trivial vs non-trivial zeros."},
            "zh": {"label": "ZetaZerosUp", "desc": "zeta 零点谓词; 平凡零点 vs 非平凡零点."},
        },
        "contour": {
            "en": {"label": "ContourUp", "desc": "Contour integration as operation on holomorphic functions."},
            "zh": {"label": "ContourUp", "desc": "围道积分, 作为全纯函数上的操作."},
        },
        "anacont": {
            "en": {"label": "AnalyticContUp", "desc": "Analytic continuation as operation on holomorphic charts."},
            "zh": {"label": "AnalyticContUp", "desc": "解析延拓, 作为全纯图册上的操作."},
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
            if entry.get("name", "") in HIERARCHY
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

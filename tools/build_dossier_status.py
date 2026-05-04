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

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _dossier_common import (
    ROOT,
    LEAN_DIR,
    DERIVED_DIR,
    PAPER_INSTANCES,
    CAPSTONE_FILE_TO_REGION,
    region_name_from_lean_file,
    paper_file_to_region,
    canonical,
    lean_module_to_region,
    lean_file_to_region,
    paper_chapter_to_region,
    parse_lean_imports,
    parse_paper_autorefs,
)

DATA_DIR = ROOT / "docs" / "dossier" / "data"

THEOREM_RE = re.compile(r"^(?:theorem|lemma)\s+(\w+)", re.MULTILINE)
DEF_RE = re.compile(r"^(?:def|inductive|structure|class)\s+(\w+)", re.MULTILINE)
MARKER_RE = re.compile(r"\\(leanchecked|leanstmt|leandef|leanvariant|leansorryd)\{")


def shell(cmd: list[str]) -> str:
    return subprocess.check_output(cmd, cwd=ROOT, text=True, stderr=subprocess.DEVNULL)


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
    r"[Nn]ame[A-Za-z0-9_\\]{0,3}[Cc]ert(?:ificate)?"
    r"[A-Za-z0-9_\\]*)"
    r"\}"
)

# FKernel namespaces that own a region's namecert (the region lives in
# `Derived/` conceptually but its proof tree is in the kernel).
FKERNEL_REGION_OVERRIDES: dict[str, str] = {
    "Unary": "nat",  # nat_up_name_certificate, add_up_name_certificate_exists
}


def collect_namecert_theorems_per_region() -> dict[str, list[dict]]:
    """Walk all paper chapters; return {region_id: [{name, status, file}, ...]}.

    A 'namecert theorem' is any \\leanchecked / \\leanstmt target whose Lean
    name matches *NameCert* or *Name(_)Certificate* (the BEDC convention for
    the object-completion theorems). Stripped underscore escapes are resolved.
    """
    out: dict[str, list[dict]] = defaultdict(list)
    for f in PAPER_INSTANCES.rglob("*.tex"):
        try:
            rel = f.relative_to(PAPER_INSTANCES)
            text = f.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue
        for m in NAMECERT_TARGET_RE.finditer(text):
            status = m.group(1).removeprefix("lean")  # 'checked' or 'stmt'
            full_target = m.group(2).replace("\\_", "_")
            module = m.group(3)  # e.g. 'FieldUp', 'NatUp', 'Unary'
            # Determine region: Derived modules use the standard Up-stripping;
            # FKernel modules like 'Unary' may map to a specific region via
            # the override table (FKernel.Unary owns nat / add namecerts).
            if "FKernel" in m.group(2):
                region = FKERNEL_REGION_OVERRIDES.get(module)
                # add_up_name_certificate also lives under FKernel.Unary -- detect.
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
    namecert_per_region = collect_namecert_theorems_per_region()

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
            # Namecert-theorem-grounded status: these are the actual
            # object-completion proofs. Node stage is decided by these
            # counts, not by aggregate chapter marker counts.
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

#!/usr/bin/env python3
"""Build per-theorem inventory and search index for the BEDC dossier.

Outputs:
  docs/dossier/data/theorem_graph.json        -- full per-declaration records
  docs/dossier/data/theorem_search_index.json -- slim (name, region, status) search index

stdlib only (project rule: no third-party deps in tools).
Duplicate qualified names in source emit a stderr warning but do not fail the build.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _dossier_common import (
    ROOT,
    LEAN_DIR,
    DERIVED_DIR,
    canonical,
    lean_module_to_region,
    lean_file_to_region,
    DeclarationRecord,
    collect_declarations,
    update_namespace_stack,
    qualified_name,
    build_declaration_inventory,
)

_PAPER_MARKER_RE = re.compile(
    r"\\(leanchecked|leanvariant|leansorryd|leanstmt|leandef)\{([^}]+)\}"
)
_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")

DATA_DIR = ROOT / "docs" / "dossier" / "data"

TARGET_KINDS = {"theorem", "lemma", "def", "inductive", "structure", "class"}
GITHUB_BLOB_BASE = "https://github.com/the-omega-institute/newmath/blob"


def _get_git_sha() -> str:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return result.stdout.strip()


def _load_checked_fullnames() -> set[str]:
    """Return the set of fully-qualified names that have status 'checked' in dependency.json's namecert_theorems."""
    dep_path = DATA_DIR / "dependency.json"
    if not dep_path.exists():
        raise FileNotFoundError(
            f"{dep_path} not found. Run tools/build_dossier_status.py first."
        )
    with dep_path.open(encoding="utf-8") as fh:
        data = json.load(fh)  # let JSONDecodeError propagate
    checked: set[str] = set()
    for node in data.get("nodes", []):
        for entry in node.get("namecert_theorems", []):
            if entry.get("status") == "checked":
                full = entry.get("name", "")
                if full:
                    checked.add(full)
    return checked


def _derive_status(decl: DeclarationRecord, checked_fullnames: set[str]) -> str:
    """Coarse v0 heuristic: checked if fully-qualified name is in checked_fullnames, else
    stmt for theorem/lemma, def-only for everything else."""
    if decl.qualified_name in checked_fullnames:
        return "checked"
    if decl.kind in ("theorem", "lemma"):
        return "stmt"
    return "def-only"


def _extract_paper_marker_sites() -> dict[str, list[dict]]:
    """Walk papers/bedc/parts/**/*.tex and build an inverted index of lean marker sites.

    Returns a dict mapping normalized theorem qualified_name ->
    list of {tex_file, label, pdf_anchor, marker_kind} records,
    sorted by (tex_file, label) for deterministic output.
    """
    parts_root = ROOT / "papers" / "bedc" / "parts"
    sites: dict[str, list[dict]] = {}

    for tex_path in sorted(parts_root.rglob("*.tex")):
        try:
            text = tex_path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue

        rel_tex = tex_path.relative_to(ROOT).as_posix()
        current_label = ""

        for line in text.splitlines():
            stripped = line.lstrip()
            if stripped.startswith("%"):
                continue

            # Update most-recent label as we scan top-to-bottom
            for lm in _LABEL_RE.finditer(line):
                current_label = lm.group(1).strip()

            # Check for lean marker macros
            for mm in _PAPER_MARKER_RE.finditer(line):
                macro = mm.group(1)
                raw_name = mm.group(2)
                # Normalize LaTeX-escaped underscores to real underscores
                norm_name = raw_name.replace(r"\_", "_").strip()
                pdf_anchor = current_label.replace(":", ".")
                site: dict = {
                    "tex_file": rel_tex,
                    "label": current_label,
                    "pdf_anchor": pdf_anchor,
                    "marker_kind": macro,
                }
                sites.setdefault(norm_name, []).append(site)

    # Sort each list for deterministic output
    for name in sites:
        sites[name].sort(key=lambda s: (s["tex_file"], s["label"]))

    return sites


def attach_paper_marker_sites(records: list[dict], sites_by_name: dict[str, list[dict]]) -> None:
    """Mutate each record in-place to add paper_marker_sites field."""
    for record in records:
        record["paper_marker_sites"] = sites_by_name.get(record["name"], [])


def build_theorem_graph(sha: str) -> list[dict]:
    """Scan lean4/BEDC/**/*.lean and build the full record list."""
    checked_fullnames = _load_checked_fullnames()

    decls, _ = build_declaration_inventory()

    records: list[dict] = []
    for decl in decls:
        if decl.is_private:
            continue
        if not decl.qualified_name.startswith("BEDC."):
            continue
        if decl.kind not in TARGET_KINDS:
            continue

        # file path relative to repo root, POSIX form
        rel_path = Path(decl.file).as_posix()

        # region: module lookup first, file lookup fallback
        region = lean_module_to_region(decl.module)
        if region is None:
            region = lean_file_to_region(ROOT / decl.file)
        if region is None:
            region = "other"

        status = _derive_status(decl, checked_fullnames)
        permalink = f"{GITHUB_BLOB_BASE}/{sha}/{rel_path}#L{decl.line}"

        records.append({
            "name": decl.qualified_name,
            "kind": decl.kind,
            "file": rel_path,
            "line": decl.line,
            "region": region,
            "status": status,
            "permalink": permalink,
        })

    return records


def build_search_index(records: list[dict]) -> list[dict]:
    """Slim (name, region, status) records for fast client-side matching."""
    return [
        {"name": r["name"], "region": r["region"], "status": r["status"]}
        for r in records
    ]


def _self_check(records: list[dict]) -> None:
    """Sanity assertions on the produced records."""
    assert records, "no records produced"
    sample = records[0]
    for k in ("name", "kind", "file", "line", "region", "status", "permalink", "paper_marker_sites"):
        assert k in sample, f"missing key {k!r} in record {sample}"
    valid_kinds = {"theorem", "lemma", "def", "inductive", "structure", "class"}
    for r in records:
        assert r["kind"] in valid_kinds, f"bad kind {r['kind']!r} in {r['name']}"
        assert r["status"] in {"checked", "stmt", "def-only"}, f"bad status in {r['name']}"
        assert r["line"] > 0, f"bad line in {r['name']}"
        assert r["permalink"].startswith("https://github.com/"), f"bad permalink in {r['name']}"
        assert isinstance(r["paper_marker_sites"], list), (
            f"paper_marker_sites must be a list in {r['name']}"
        )
    for r in records:
        assert r["name"].startswith("BEDC."), f"non-BEDC name leaked: {r['name']!r}"
    # Sanity: at least one record should have paper marker sites (paper references lean targets)
    with_sites = [r for r in records if r["paper_marker_sites"]]
    assert with_sites, "no records have paper_marker_sites — paper marker scan may have failed"
    from collections import Counter
    name_counts = Counter(r["name"] for r in records)
    duplicates = sorted(n for n, c in name_counts.items() if c > 1)
    if duplicates:
        import sys as _sys
        print(
            f"[build-theorem-graph] WARNING: {len(duplicates)} duplicate qualified_name(s) "
            f"in Lean source (likely codex-auto-dev race; fix at source):",
            file=_sys.stderr,
        )
        for n in duplicates:
            print(f"  {n}", file=_sys.stderr)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Build BEDC theorem graph and search index.")
    parser.add_argument(
        "--output",
        default=str(DATA_DIR / "theorem_graph.json"),
        help="Path for theorem_graph.json",
    )
    parser.add_argument(
        "--output-search",
        default=str(DATA_DIR / "theorem_search_index.json"),
        help="Path for theorem_search_index.json",
    )
    args = parser.parse_args()

    output_path = Path(args.output)
    search_path = Path(args.output_search)

    sha = _get_git_sha()
    records = build_theorem_graph(sha)
    sites_by_name = _extract_paper_marker_sites()
    attach_paper_marker_sites(records, sites_by_name)
    _self_check(records)

    search_index = build_search_index(records)

    graph_payload = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "git_sha": sha[:8],
        "total": len(records),
        "theorems": records,
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(graph_payload, indent=2), encoding="utf-8")

    search_path.parent.mkdir(parents=True, exist_ok=True)
    search_path.write_text(json.dumps(search_index, indent=2), encoding="utf-8")

    print(
        f"[build-theorem-graph] wrote {output_path} ({len(records)} declarations)"
        f" and {search_path} ({len(search_index)} entries)"
    )
    sys.exit(0)

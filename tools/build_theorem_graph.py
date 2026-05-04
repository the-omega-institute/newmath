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
from collections import defaultdict
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
    parse_lean_imports,
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

# ---------------------------------------------------------------------------
# Dependency extraction patterns
# ---------------------------------------------------------------------------

# Qualified name patterns:
# Pattern A: uppercase-namespace form — e.g. BHist.Empty, BEDC.FKernel.cont_assoc
#   The namespace component(s) must start uppercase; final component any case.
_QUALIFIED_NAME_UPPER_RE = re.compile(
    r"\b([A-Z][A-Za-z0-9_]*(?:\.[A-Z][A-Za-z0-9_]*)*\.[A-Za-z_][A-Za-z0-9_]*)\b"
)
# Pattern B: lowercase-namespace qualified form — e.g. psame.refl, bar.baz
#   At least two components, both may start lowercase.  We require the namespace
#   part is a single identifier (no further dots) to avoid over-matching.
_QUALIFIED_NAME_LOWER_RE = re.compile(
    r"\b([a-z_][A-Za-z0-9_]*\.[a-z_][A-Za-z0-9_]*)\b"
)
# Combined: run both patterns and union results.
_QUALIFIED_NAME_RES = (_QUALIFIED_NAME_UPPER_RE, _QUALIFIED_NAME_LOWER_RE)

# apply/exact/refine followed by a name (qualified or unqualified)
_TACTIC_REF_RE = re.compile(
    r"\b(?:apply|exact|refine)\s+([A-Za-z_][A-Za-z0-9_.]*)(?:\s|$|\(|\{)"
)

# Boundary keywords that signal end of a declaration body
_DECL_BOUNDARY_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+|scoped\s+|mutual\s+)*"
    r"(?:theorem|lemma|def|abbrev|inductive|class|structure)\s",
    re.MULTILINE,
)

# end keyword signals namespace closure (also a boundary)
_END_KEYWORD_RE = re.compile(r"^\s*end\b", re.MULTILINE)


def _build_short_name_index(
    all_decls: list[DeclarationRecord],
) -> dict[str, list[str]]:
    """Build dict: short_name -> list[fully_qualified_name] for fast lookup.

    Used to resolve unqualified names from apply/exact/refine patterns.
    Only BEDC.* names are indexed.
    """
    index: dict[str, list[str]] = defaultdict(list)
    for d in all_decls:
        if not d.qualified_name.startswith("BEDC."):
            continue
        short = d.name
        index[short].append(d.qualified_name)
    return dict(index)


def _extract_proof_body(file_lines: list[str], decl_line: int, next_decl_line: int) -> str:
    """Return the raw text of a declaration's body.

    Slices from decl_line (1-indexed, inclusive) to next_decl_line (1-indexed, exclusive).
    If next_decl_line <= decl_line or out of range, returns the single declaration line.
    """
    start = decl_line - 1  # convert to 0-indexed
    end = next_decl_line - 1 if next_decl_line > decl_line else start + 1
    end = min(end, len(file_lines))
    return "\n".join(file_lines[start:end])


def _resolve_raw_name(
    raw: str,
    decl_module: str,
    known_fqn_set: set[str],
    short_name_index: dict[str, list[str]],
) -> str | None:
    """Attempt to resolve a raw token to a BEDC fully-qualified name.

    Resolution order:
    1. If raw already starts with 'BEDC.' and is in inventory -> use as-is.
    2. Try prefixing with decl_module namespace components (walk down from full module).
    3. Look up raw as short name in short_name_index; if exactly one match -> use it.
       If multiple, prefer same-module match; if still ambiguous, prefer alphabetically first.
    4. Otherwise return None (not a known BEDC declaration).
    """
    # Already fully qualified BEDC name
    if raw.startswith("BEDC.") and raw in known_fqn_set:
        return raw

    # Try prefixing with namespace components of decl_module
    # e.g. module 'BEDC.FKernel.Cont', try 'BEDC.FKernel.Cont.<raw>', 'BEDC.FKernel.<raw>'
    parts = decl_module.split(".")
    for depth in range(len(parts), 0, -1):
        prefix = ".".join(parts[:depth])
        candidate = f"{prefix}.{raw}"
        if candidate in known_fqn_set:
            return candidate

    # Short name lookup (raw has no dots, or has dots that look unresolved)
    # Only use the final component as the short name to avoid false matches
    short = raw.split(".")[-1] if "." in raw else raw
    # But also try the raw itself if it contains dots (partial qualified name)
    candidates_from_short = short_name_index.get(short, [])

    # If raw contains dots, also try matching suffix
    if "." in raw:
        suffix_candidates = [fqn for fqn in known_fqn_set if fqn.endswith(f".{raw}") or fqn == raw]
        if suffix_candidates:
            # Prefer same module
            same_mod = [c for c in suffix_candidates if c.startswith(decl_module)]
            return same_mod[0] if same_mod else sorted(suffix_candidates)[0]

    if not candidates_from_short:
        return None
    if len(candidates_from_short) == 1:
        return candidates_from_short[0]
    # Multiple matches: prefer same-module first
    same_mod = [c for c in candidates_from_short if c.startswith(decl_module)]
    if same_mod:
        return sorted(same_mod)[0]
    return sorted(candidates_from_short)[0]


def extract_dependencies(
    decl: DeclarationRecord,
    file_lines: list[str],
    next_decl_line: int,
    known_fqn_set: set[str],
    short_name_index: dict[str, list[str]],
) -> list[str]:
    """Extract per-declaration dependencies from its proof body.

    Known holes (intentional; partially compensated by dep_file_imports):
    - simp [foo, bar]: lemmas inside simp set are NOT extracted.
    - rw [foo, bar]: rewrite lemmas are NOT extracted.
    - induction h with | ctor => ...: case names are NOT extracted.
    - (by tac) term-mode inner tactic: proof body NOT recursively scanned.
    - open Foo.Bar: short names introduced by open are NOT resolved via
      open declarations; only qualified prefixes via module namespace stack
      are handled.

    These holes are partially compensated by dep_file_imports, which lists
    all BEDC.* imports of the file as potential (dashed-edge) dependencies.
    """
    body = _extract_proof_body(file_lines, decl.line, next_decl_line)

    raw_names: set[str] = set()

    # Pattern 1: qualified names (uppercase-namespace form + lowercase-namespace form)
    for pat in _QUALIFIED_NAME_RES:
        for m in pat.finditer(body):
            raw_names.add(m.group(1))

    # Pattern 2: apply/exact/refine NAME
    for m in _TACTIC_REF_RE.finditer(body):
        raw_names.add(m.group(1))

    resolved: set[str] = set()
    for raw in raw_names:
        fqn = _resolve_raw_name(raw, decl.module, known_fqn_set, short_name_index)
        if fqn is None:
            continue
        # Do not list a declaration as its own dependency
        if fqn == decl.qualified_name:
            continue
        resolved.add(fqn)

    return sorted(resolved)


def extract_dep_file_imports(file_path: Path) -> list[str]:
    """Return sorted, deduplicated list of BEDC.* module names from import statements in file_path."""
    try:
        all_imports = parse_lean_imports(file_path)
    except OSError:
        return []
    bedc_imports = sorted(set(imp for imp in all_imports if imp.startswith("BEDC.")))
    return bedc_imports


# ---------------------------------------------------------------------------
# File-level cache for proof body slicing
# ---------------------------------------------------------------------------


def _build_file_line_cache(
    decls: list[DeclarationRecord],
) -> dict[str, tuple[list[str], dict[int, int]]]:
    """Pre-read all source files and compute next-declaration-line maps.

    Returns:
        Dict mapping file path (relative) -> (file_lines, line_to_next_decl_line).
        line_to_next_decl_line maps each decl's start line (1-indexed) to the
        line where the next declaration in the same file starts (or len+1 for last).
    """
    # Group decls by file
    by_file: dict[str, list[int]] = defaultdict(list)
    for d in decls:
        by_file[d.file].append(d.line)

    cache: dict[str, tuple[list[str], dict[int, int]]] = {}
    for rel_file, lines_list in by_file.items():
        abs_path = ROOT / rel_file
        try:
            text = abs_path.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            cache[rel_file] = ([], {})
            continue
        file_lines = text.splitlines()
        total_lines = len(file_lines)
        sorted_lines = sorted(set(lines_list))
        next_line_map: dict[int, int] = {}
        for i, ln in enumerate(sorted_lines):
            if i + 1 < len(sorted_lines):
                next_line_map[ln] = sorted_lines[i + 1]
            else:
                next_line_map[ln] = total_lines + 1
        cache[rel_file] = (file_lines, next_line_map)

    return cache


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


def attach_dependencies(
    records: list[dict],
    all_decls: list[DeclarationRecord],
) -> None:
    """Mutate each record in-place to add dependencies and dep_file_imports fields.

    Reads source files once per file (cached), then for each declaration extracts
    its proof body text and runs the token-scan extraction.
    """
    # Build lookup structures
    known_fqn_set: set[str] = {d.qualified_name for d in all_decls if d.qualified_name.startswith("BEDC.")}
    short_name_index = _build_short_name_index(all_decls)

    # Build file-level line cache for all decls (not just filtered TARGET_KINDS)
    file_cache = _build_file_line_cache(all_decls)

    # Build a fast lookup: (file, line) -> DeclarationRecord
    decl_lookup: dict[tuple[str, int], DeclarationRecord] = {}
    for d in all_decls:
        decl_lookup[(d.file, d.line)] = d

    # Per-file import cache to avoid re-parsing the same file
    import_cache: dict[str, list[str]] = {}

    for record in records:
        rel_file = record["file"]
        decl_line = record["line"]

        # Retrieve the matching DeclarationRecord
        decl = decl_lookup.get((rel_file, decl_line))
        if decl is None:
            record["dependencies"] = []
            record["dep_file_imports"] = []
            continue

        # Get file lines and next-decl-line map
        file_lines, next_line_map = file_cache.get(rel_file, ([], {}))
        next_decl_line = next_line_map.get(decl_line, len(file_lines) + 1)

        # Extract dependencies
        deps = extract_dependencies(
            decl,
            file_lines,
            next_decl_line,
            known_fqn_set,
            short_name_index,
        )
        record["dependencies"] = deps

        # Extract file-level imports (cached)
        if rel_file not in import_cache:
            abs_path = ROOT / rel_file
            import_cache[rel_file] = extract_dep_file_imports(abs_path)
        record["dep_file_imports"] = import_cache[rel_file]


def build_theorem_graph(sha: str) -> tuple[list[dict], list[DeclarationRecord]]:
    """Scan lean4/BEDC/**/*.lean and build the full record list.

    Returns (records, all_decls) so caller can pass all_decls to attach_dependencies.
    """
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

    return records, decls


def compute_upstream_closure(
    record_name: str,
    name_to_record: dict[str, dict],
    cache: dict[str, frozenset[str]],
) -> frozenset[str]:
    """Return the set of names in record_name's transitive upstream closure.

    Inclusion rule:
    - The closure is the set of ALL names that record_name transitively depends on,
      via BFS over the `dependencies` field.
    - record_name ITSELF is NOT included in the returned set (upstream only).
    - Names referenced in `dependencies` that are not present in name_to_record are
      silently skipped (T6 filters to BEDC.* but some private declarations may be absent).

    Cycle defense: the BFS visited set prevents re-visiting any name, so cycles in the
    dependency graph cannot cause an infinite loop.  If a cycle is detected (a name is
    queued while already visited), a one-line warning is emitted to stderr.

    Memoization: results are stored in `cache` keyed by record_name.  On a cache hit
    the frozen set is returned immediately without re-traversal.
    """
    if record_name in cache:
        return cache[record_name]

    visited: set[str] = set()
    queue: list[str] = list(name_to_record.get(record_name, {}).get("dependencies", []))

    # BFS over confirmed deps. The visited set both deduplicates the diamond-DAG
    # (multiple paths to the same node) and terminates any latent cycle. We do
    # NOT distinguish — both produce the same correct closure. A true Tarjan SCC
    # pass would be needed to flag actual cycles, out of v2 scope.
    while queue:
        current = queue.pop()
        if current == record_name:
            continue
        if current in visited:
            continue
        visited.add(current)
        rec = name_to_record.get(current)
        if rec is None:
            # Not in inventory (private or out-of-scope) — skip.
            continue
        for dep in rec.get("dependencies", []):
            if dep not in visited:
                queue.append(dep)

    result = frozenset(visited)
    cache[record_name] = result
    return result


# Kinds treated as "defs" in the upstream closure summary
_DEF_KINDS = {"def", "inductive", "structure", "class"}
# Kinds treated as "theorems" in the upstream closure summary
_THEOREM_KINDS = {"theorem", "lemma"}


def compute_summary(
    record: dict,
    name_to_record: dict[str, dict],
    cache: dict[str, frozenset[str]],
) -> dict:
    """Return the 5-field upstream_closure_summary dict for a single record.

    Fields:
    - axioms_count:        ALWAYS 0 (project-level invariant; not computed per-theorem).
    - sorry_count:         ALWAYS 0 (project-level invariant; not computed per-theorem).
    - defs_count:          count of def/inductive/structure/class records in closure(R) \\ {R}.
    - theorems_count:      count of theorem/lemma records in closure(R) \\ {R}.
    - paper_markers_count: sum of len(paper_marker_sites) over all records in
                           closure(R) UNION {R}  (self is included for paper markers).
    """
    record_name = record["name"]
    closure = compute_upstream_closure(record_name, name_to_record, cache)

    defs_count = 0
    theorems_count = 0
    paper_markers_count = len(record.get("paper_marker_sites", []))

    for name in closure:
        rec = name_to_record.get(name)
        if rec is None:
            continue
        kind = rec.get("kind", "")
        if kind in _DEF_KINDS:
            defs_count += 1
        elif kind in _THEOREM_KINDS:
            theorems_count += 1
        paper_markers_count += len(rec.get("paper_marker_sites", []))

    return {
        "axioms_count": 0,
        "sorry_count": 0,
        "defs_count": defs_count,
        "theorems_count": theorems_count,
        "paper_markers_count": paper_markers_count,
    }


def attach_upstream_closure_summaries(records: list[dict]) -> None:
    """Orchestrator: build name->record index and cache once, then mutate each record in-place.

    Adds `upstream_closure_summary` to every record.  The index and cache are shared
    across all records so repeated BFS traversals benefit from memoization.
    """
    # Build name->record index ONCE (O(n) lookup for BFS)
    name_to_record: dict[str, dict] = {r["name"]: r for r in records}
    # Shared memoization cache: name -> frozenset[str] of upstream closure names
    closure_cache: dict[str, frozenset[str]] = {}

    for record in records:
        record["upstream_closure_summary"] = compute_summary(
            record, name_to_record, closure_cache
        )


def build_search_index(records: list[dict]) -> list[dict]:
    """Slim (name, region, status) records for fast client-side matching."""
    return [
        {"name": r["name"], "region": r["region"], "status": r["status"]}
        for r in records
    ]


_SUMMARY_REQUIRED_KEYS = frozenset(
    {"axioms_count", "sorry_count", "defs_count", "theorems_count", "paper_markers_count"}
)


def _self_check(records: list[dict]) -> None:
    """Sanity assertions on the produced records."""
    assert records, "no records produced"
    sample = records[0]
    required_keys = (
        "name", "kind", "file", "line", "region", "status", "permalink",
        "paper_marker_sites", "dependencies", "dep_file_imports",
        "upstream_closure_summary",
    )
    for k in required_keys:
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
        assert isinstance(r["dependencies"], list), f"dependencies must be a list in {r['name']}"
        assert isinstance(r["dep_file_imports"], list), (
            f"dep_file_imports must be a list in {r['name']}"
        )
        # Dependencies must be sorted and deduplicated
        assert r["dependencies"] == sorted(set(r["dependencies"])), (
            f"dependencies not sorted/deduped in {r['name']}"
        )
        assert r["dep_file_imports"] == sorted(set(r["dep_file_imports"])), (
            f"dep_file_imports not sorted/deduped in {r['name']}"
        )
        # upstream_closure_summary: must be a dict with exactly 5 keys
        s = r["upstream_closure_summary"]
        assert isinstance(s, dict), f"upstream_closure_summary must be a dict in {r['name']}"
        assert set(s.keys()) == _SUMMARY_REQUIRED_KEYS, (
            f"upstream_closure_summary has wrong keys in {r['name']}: {set(s.keys())}"
        )
        # Project invariants: axioms and sorry always 0
        assert s["axioms_count"] == 0, (
            f"axioms_count must be 0 (project invariant) in {r['name']}, got {s['axioms_count']}"
        )
        assert s["sorry_count"] == 0, (
            f"sorry_count must be 0 (project invariant) in {r['name']}, got {s['sorry_count']}"
        )
        # Non-negative integer counts
        for field in ("defs_count", "theorems_count", "paper_markers_count"):
            assert isinstance(s[field], int) and s[field] >= 0, (
                f"{field} must be non-negative int in {r['name']}, got {s[field]!r}"
            )
    for r in records:
        assert r["name"].startswith("BEDC."), f"non-BEDC name leaked: {r['name']!r}"
    # Sanity: at least one record should have paper marker sites (paper references lean targets)
    with_sites = [r for r in records if r["paper_marker_sites"]]
    assert with_sites, "no records have paper_marker_sites — paper marker scan may have failed"
    # Sanity: at least some records should have dependencies
    with_deps = [r for r in records if r["dependencies"]]
    assert with_deps, "no records have dependencies — dependency extraction may have failed"
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
    records, all_decls = build_theorem_graph(sha)
    sites_by_name = _extract_paper_marker_sites()
    attach_paper_marker_sites(records, sites_by_name)
    attach_dependencies(records, all_decls)
    attach_upstream_closure_summaries(records)
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

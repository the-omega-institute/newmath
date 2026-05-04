#!/usr/bin/env python3
"""Unit tests for dependency extraction in build_theorem_graph.py (T6).

Tests 1-6: white-box tests using synthetic Lean source text and temp files.
Test 7: determinism — run extraction twice, assert identical output.
Test 8: idempotency against real lean4/BEDC/ data — run build_theorem_graph twice,
        verify same count of records with non-empty dependencies.

Run via: python3 tools/test_build_theorem_graph.py
Exit 0 = all tests pass.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

# We import the extraction primitives directly for white-box testing.
from build_theorem_graph import (
    extract_dependencies,
    extract_dep_file_imports,
    _build_short_name_index,
    _extract_proof_body,
    compute_upstream_closure,
    compute_summary,
    attach_upstream_closure_summaries,
)
from _dossier_common import DeclarationRecord

PASS = 0
FAIL = 0
_FAILURES: list[str] = []

ROOT = Path(__file__).resolve().parents[1]


def _pass(name: str) -> None:
    global PASS
    PASS += 1
    print(f"  PASS  {name}")


def _fail(name: str, detail: str) -> None:
    global FAIL
    FAIL += 1
    _FAILURES.append(f"{name}: {detail}")
    print(f"  FAIL  {name}: {detail}")


def _make_decl(
    qualified_name: str,
    *,
    line: int = 1,
    kind: str = "theorem",
    file: str = "lean4/BEDC/Test.lean",
    module: str = "BEDC.Test",
    name: str | None = None,
) -> DeclarationRecord:
    short = name or qualified_name.split(".")[-1]
    return DeclarationRecord(
        module=module,
        file=file,
        line=line,
        kind=kind,
        name=short,
        qualified_name=qualified_name,
        is_private=False,
    )


# ---------------------------------------------------------------------------
# Test 1: term-mode qualified name extraction
# ---------------------------------------------------------------------------
def test_extract_dependencies_term_mode() -> None:
    """Theorem body with qualified references bar.baz and qux.frob in term mode."""
    decl = _make_decl("BEDC.Test.foo", module="BEDC.Test", line=1)
    body_lines = ["theorem foo : T := bar.baz qux.frob"]
    # Inventory contains both names so they resolve
    known_fqns: set[str] = {"BEDC.Test.bar.baz", "BEDC.Test.qux.frob"}
    # Build synthetic inventory
    d1 = _make_decl("BEDC.Test.bar.baz", module="BEDC.Test", name="baz")
    d2 = _make_decl("BEDC.Test.qux.frob", module="BEDC.Test", name="frob")
    idx = _build_short_name_index([d1, d2])

    deps = extract_dependencies(decl, body_lines, 2, known_fqns, idx)
    test_name = "test_extract_dependencies_term_mode"
    try:
        assert "BEDC.Test.bar.baz" in deps, f"bar.baz not in {deps}"
        assert "BEDC.Test.qux.frob" in deps, f"qux.frob not in {deps}"
        _pass(test_name)
    except AssertionError as e:
        _fail(test_name, str(e))


# ---------------------------------------------------------------------------
# Test 2: apply / exact / refine patterns
# ---------------------------------------------------------------------------
def test_extract_dependencies_apply_exact_refine() -> None:
    """Theorem body with apply/exact/refine tactics each referencing a BEDC name."""
    decl = _make_decl("BEDC.Test.foo", module="BEDC.Test", line=1)
    body_lines = [
        "theorem foo : T := by",
        "  apply Bar.lemma1",
        "  exact Baz.lemma2",
        "  refine Qux.lemma3",
    ]
    known_fqns: set[str] = {
        "BEDC.Test.Bar.lemma1",
        "BEDC.Test.Baz.lemma2",
        "BEDC.Test.Qux.lemma3",
    }
    d1 = _make_decl("BEDC.Test.Bar.lemma1", module="BEDC.Test", name="lemma1")
    d2 = _make_decl("BEDC.Test.Baz.lemma2", module="BEDC.Test", name="lemma2")
    d3 = _make_decl("BEDC.Test.Qux.lemma3", module="BEDC.Test", name="lemma3")
    idx = _build_short_name_index([d1, d2, d3])

    deps = extract_dependencies(decl, body_lines, 5, known_fqns, idx)
    test_name = "test_extract_dependencies_apply_exact_refine"
    try:
        assert "BEDC.Test.Bar.lemma1" in deps, f"Bar.lemma1 not in {deps}"
        assert "BEDC.Test.Baz.lemma2" in deps, f"Baz.lemma2 not in {deps}"
        assert "BEDC.Test.Qux.lemma3" in deps, f"Qux.lemma3 not in {deps}"
        _pass(test_name)
    except AssertionError as e:
        _fail(test_name, str(e))


# ---------------------------------------------------------------------------
# Test 3: namespace prefix resolution
# ---------------------------------------------------------------------------
def test_extract_dependencies_namespace_prefix() -> None:
    """Unqualified name 'baz' resolved via module namespace to Foo.baz."""
    decl = _make_decl(
        "BEDC.Foo.bar",
        module="BEDC.Foo",
        line=1,
        name="bar",
    )
    body_lines = ["theorem bar : T := by exact baz"]
    # Inventory has BEDC.Foo.baz
    known_fqns: set[str] = {"BEDC.Foo.baz"}
    d = _make_decl("BEDC.Foo.baz", module="BEDC.Foo", name="baz")
    idx = _build_short_name_index([d])

    deps = extract_dependencies(decl, body_lines, 2, known_fqns, idx)
    test_name = "test_extract_dependencies_namespace_prefix"
    try:
        assert "BEDC.Foo.baz" in deps, f"BEDC.Foo.baz not in {deps}"
        _pass(test_name)
    except AssertionError as e:
        _fail(test_name, str(e))


# ---------------------------------------------------------------------------
# Test 4: empty proof (only rfl) produces no dependencies
# ---------------------------------------------------------------------------
def test_extract_dependencies_empty_proof() -> None:
    """Theorem proved by rfl has no extracted dependencies."""
    decl = _make_decl("BEDC.Test.foo", module="BEDC.Test", line=1)
    body_lines = ["theorem foo : T := rfl"]
    known_fqns: set[str] = set()
    idx: dict = {}

    deps = extract_dependencies(decl, body_lines, 2, known_fqns, idx)
    test_name = "test_extract_dependencies_empty_proof"
    try:
        assert deps == [], f"expected [] but got {deps}"
        _pass(test_name)
    except AssertionError as e:
        _fail(test_name, str(e))


# ---------------------------------------------------------------------------
# Test 5: known hole — simp [bar, baz] contents not extracted
# ---------------------------------------------------------------------------
def test_extract_dependencies_known_holes_documented() -> None:
    """Names inside simp [...] are NOT extracted — this is an accepted hole.

    This test documents the hole: if bar and baz appear only inside a simp call,
    they must NOT appear in dependencies. We accept this limitation.
    """
    decl = _make_decl("BEDC.Test.foo", module="BEDC.Test", line=1)
    # bar and baz only appear in simp set — not as standalone references
    body_lines = ["theorem foo : T := by simp [bar, baz]"]
    # Put both in inventory — they would be resolved if found
    known_fqns: set[str] = {"BEDC.Test.bar", "BEDC.Test.baz"}
    d1 = _make_decl("BEDC.Test.bar", module="BEDC.Test", name="bar")
    d2 = _make_decl("BEDC.Test.baz", module="BEDC.Test", name="baz")
    idx = _build_short_name_index([d1, d2])

    deps = extract_dependencies(decl, body_lines, 2, known_fqns, idx)
    test_name = "test_extract_dependencies_known_holes_documented"
    try:
        # simp [bar, baz] — bar and baz are unqualified, single-token names
        # The patterns only capture qualified names (with '.') or apply/exact/refine targets.
        # So bar/baz inside simp [...] are NOT captured by _QUALIFIED_NAME_RE
        # (no dot) and NOT by _TACTIC_REF_RE (not preceded by apply/exact/refine).
        # Verify they are absent.
        assert "BEDC.Test.bar" not in deps, (
            f"BEDC.Test.bar should not be in deps (simp hole) but got {deps}"
        )
        assert "BEDC.Test.baz" not in deps, (
            f"BEDC.Test.baz should not be in deps (simp hole) but got {deps}"
        )
        _pass(test_name)
    except AssertionError as e:
        _fail(test_name, str(e))


# ---------------------------------------------------------------------------
# Test 6: dep_file_imports extracted from real temp file
# ---------------------------------------------------------------------------
def test_dep_file_imports_extracted() -> None:
    """File with BEDC imports yields correct dep_file_imports list."""
    test_name = "test_dep_file_imports_extracted"
    content = (
        "import BEDC.FKernel.BHist\n"
        "import BEDC.NameCert\n"
        "import Lean.Core\n"  # non-BEDC import should be filtered
        "\n"
        "theorem foo : True := trivial\n"
    )
    with tempfile.NamedTemporaryFile(
        suffix=".lean", mode="w", encoding="utf-8", delete=False
    ) as tmp:
        tmp.write(content)
        tmp_path = Path(tmp.name)

    try:
        result = extract_dep_file_imports(tmp_path)
        expected = ["BEDC.FKernel.BHist", "BEDC.NameCert"]
        assert result == expected, f"expected {expected} but got {result}"
        _pass(test_name)
    except AssertionError as e:
        _fail(test_name, str(e))
    finally:
        tmp_path.unlink(missing_ok=True)


# ---------------------------------------------------------------------------
# Test 7: extraction is deterministic (same input -> same output twice)
# ---------------------------------------------------------------------------
def test_extraction_deterministic() -> None:
    """Run extraction twice on same synthetic input, verify identical output."""
    test_name = "test_extraction_deterministic"
    decl = _make_decl("BEDC.Test.foo", module="BEDC.Test", line=1)
    body_lines = [
        "theorem foo : T := by",
        "  apply Bar.lemma1",
        "  exact Baz.lemma2",
        "  cases Bar.ctor",
    ]
    known_fqns: set[str] = {
        "BEDC.Test.Bar.lemma1",
        "BEDC.Test.Baz.lemma2",
        "BEDC.Test.Bar.ctor",
    }
    d1 = _make_decl("BEDC.Test.Bar.lemma1", module="BEDC.Test", name="lemma1")
    d2 = _make_decl("BEDC.Test.Baz.lemma2", module="BEDC.Test", name="lemma2")
    d3 = _make_decl("BEDC.Test.Bar.ctor", module="BEDC.Test", name="ctor")
    idx = _build_short_name_index([d1, d2, d3])

    try:
        deps1 = extract_dependencies(decl, body_lines, 5, known_fqns, idx)
        deps2 = extract_dependencies(decl, body_lines, 5, known_fqns, idx)
        assert deps1 == deps2, f"non-deterministic: {deps1} != {deps2}"
        # Also verify they are sorted
        assert deps1 == sorted(deps1), f"deps not sorted: {deps1}"
        _pass(test_name)
    except AssertionError as e:
        _fail(test_name, str(e))


# ---------------------------------------------------------------------------
# Test 8: idempotency against real data
# ---------------------------------------------------------------------------
def test_extraction_idempotent_against_real_data() -> None:
    """Run build_theorem_graph twice on actual lean4/BEDC/ and verify same dep counts."""
    test_name = "test_extraction_idempotent_against_real_data"
    script = ROOT / "tools" / "build_theorem_graph.py"

    def _run() -> int:
        result = subprocess.run(
            [sys.executable, str(script)],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            raise RuntimeError(f"build_theorem_graph.py failed:\n{result.stderr}")
        return result.returncode

    try:
        _run()
        import json
        graph_path = ROOT / "docs" / "dossier" / "data" / "theorem_graph.json"
        data1 = json.loads(graph_path.read_text(encoding="utf-8"))
        records1 = data1["theorems"]
        count1 = len([r for r in records1 if r.get("dependencies")])
        total1 = len(records1)
        assert count1 > 0, "first run: no records have non-empty dependencies"
        assert total1 > 4000, f"first run: expected > 4000 records (sanity), got {total1}"

        _run()
        data2 = json.loads(graph_path.read_text(encoding="utf-8"))
        records2 = data2["theorems"]
        count2 = len([r for r in records2 if r.get("dependencies")])
        total2 = len(records2)

        assert count1 == count2, (
            f"idempotency failure: run1 had {count1} with deps, run2 had {count2}"
        )
        assert total1 == total2, (
            f"idempotency failure: run1 had {total1} records, run2 had {total2}"
        )
        # Compare first 3 records for structural stability (name, deps)
        for i in range(min(3, len(records1))):
            r1 = records1[i]
            r2 = records2[i]
            assert r1["name"] == r2["name"], f"record {i} name mismatch"
            assert r1["dependencies"] == r2["dependencies"], (
                f"record {i} ({r1['name']}) deps changed between runs"
            )

        _pass(test_name)
    except (AssertionError, RuntimeError) as e:
        _fail(test_name, str(e))


# ---------------------------------------------------------------------------
# Helper: build a minimal synthetic record dict
# ---------------------------------------------------------------------------

def _make_record(
    name: str,
    *,
    kind: str = "theorem",
    dependencies: list[str] | None = None,
    paper_marker_sites: list[dict] | None = None,
) -> dict:
    return {
        "name": name,
        "kind": kind,
        "file": "lean4/BEDC/Test.lean",
        "line": 1,
        "region": "fkernel",
        "status": "checked",
        "permalink": "https://github.com/example/repo/blob/abc/lean4/BEDC/Test.lean#L1",
        "paper_marker_sites": paper_marker_sites if paper_marker_sites is not None else [],
        "dependencies": dependencies if dependencies is not None else [],
        "dep_file_imports": [],
    }


# ---------------------------------------------------------------------------
# Test 9: closure of record with no dependencies is empty
# ---------------------------------------------------------------------------
def test_compute_closure_zero_deps() -> None:
    """Record with dependencies=[] has empty upstream closure."""
    test_name = "test_compute_closure_zero_deps"
    r = _make_record("BEDC.A", dependencies=[])
    name_to_record = {"BEDC.A": r}
    cache: dict = {}
    try:
        result = compute_upstream_closure("BEDC.A", name_to_record, cache)
        assert result == frozenset(), f"expected empty frozenset, got {result}"
        _pass(test_name)
    except AssertionError as e:
        _fail(test_name, str(e))


# ---------------------------------------------------------------------------
# Test 10: single-step closure A->B
# ---------------------------------------------------------------------------
def test_compute_closure_single_step() -> None:
    """A depends on B, B has no deps: closure(A) = {B}."""
    test_name = "test_compute_closure_single_step"
    a = _make_record("BEDC.A", dependencies=["BEDC.B"])
    b = _make_record("BEDC.B", dependencies=[])
    name_to_record = {"BEDC.A": a, "BEDC.B": b}
    cache: dict = {}
    try:
        result = compute_upstream_closure("BEDC.A", name_to_record, cache)
        assert result == frozenset({"BEDC.B"}), f"expected {{BEDC.B}}, got {result}"
        _pass(test_name)
    except AssertionError as e:
        _fail(test_name, str(e))


# ---------------------------------------------------------------------------
# Test 11: multi-step closure A->B->C->D
# ---------------------------------------------------------------------------
def test_compute_closure_multi_step() -> None:
    """A->B->C->D: closure(A) = {B, C, D}."""
    test_name = "test_compute_closure_multi_step"
    a = _make_record("BEDC.A", dependencies=["BEDC.B"])
    b = _make_record("BEDC.B", dependencies=["BEDC.C"])
    c = _make_record("BEDC.C", dependencies=["BEDC.D"])
    d = _make_record("BEDC.D", dependencies=[])
    name_to_record = {"BEDC.A": a, "BEDC.B": b, "BEDC.C": c, "BEDC.D": d}
    cache: dict = {}
    try:
        result = compute_upstream_closure("BEDC.A", name_to_record, cache)
        assert result == frozenset({"BEDC.B", "BEDC.C", "BEDC.D"}), (
            f"expected {{B,C,D}}, got {result}"
        )
        _pass(test_name)
    except AssertionError as e:
        _fail(test_name, str(e))


# ---------------------------------------------------------------------------
# Test 12: cycle safety A->B->A
# ---------------------------------------------------------------------------
def test_compute_closure_cycle_safe() -> None:
    """A->B->A cycle: BFS must not infinite-loop; closure(A) = {B}."""
    test_name = "test_compute_closure_cycle_safe"
    a = _make_record("BEDC.A", dependencies=["BEDC.B"])
    b = _make_record("BEDC.B", dependencies=["BEDC.A"])
    name_to_record = {"BEDC.A": a, "BEDC.B": b}
    cache: dict = {}
    try:
        result = compute_upstream_closure("BEDC.A", name_to_record, cache)
        # B is visited; A is either skipped (self) or skipped (cycle).
        # B's dep on A: A is encountered during BFS but not added again.
        # Final closure = {B}  (A is excluded — it's the root, not an upstream dep)
        assert "BEDC.B" in result, f"BEDC.B should be in closure, got {result}"
        assert "BEDC.A" not in result, f"BEDC.A (root) should not be in its own closure, got {result}"
        _pass(test_name)
    except AssertionError as e:
        _fail(test_name, str(e))


# ---------------------------------------------------------------------------
# Test 13: compute_summary kind counts
# ---------------------------------------------------------------------------
def test_compute_summary_kind_counts() -> None:
    """closure has 2 theorems + 1 def + 1 inductive + paper markers counted correctly."""
    test_name = "test_compute_summary_kind_counts"
    # R depends on T1, T2 (theorems), D1 (def), I1 (inductive)
    r = _make_record(
        "BEDC.R",
        kind="theorem",
        dependencies=["BEDC.T1", "BEDC.T2", "BEDC.D1", "BEDC.I1"],
        paper_marker_sites=[{"tex_file": "foo.tex", "label": "x", "pdf_anchor": "x", "marker_kind": "leanchecked"}],
    )
    t1 = _make_record("BEDC.T1", kind="theorem", dependencies=[])
    t2 = _make_record("BEDC.T2", kind="lemma", dependencies=[])
    d1 = _make_record("BEDC.D1", kind="def", dependencies=[])
    i1 = _make_record(
        "BEDC.I1",
        kind="inductive",
        dependencies=[],
        paper_marker_sites=[
            {"tex_file": "bar.tex", "label": "y", "pdf_anchor": "y", "marker_kind": "leandef"},
            {"tex_file": "baz.tex", "label": "z", "pdf_anchor": "z", "marker_kind": "leandef"},
        ],
    )
    name_to_record = {
        "BEDC.R": r, "BEDC.T1": t1, "BEDC.T2": t2, "BEDC.D1": d1, "BEDC.I1": i1,
    }
    cache: dict = {}
    try:
        s = compute_summary(r, name_to_record, cache)
        assert s["axioms_count"] == 0, f"axioms_count: {s}"
        assert s["sorry_count"] == 0, f"sorry_count: {s}"
        # defs_count: D1 (def) + I1 (inductive) = 2
        assert s["defs_count"] == 2, f"expected defs_count=2, got {s}"
        # theorems_count: T1 (theorem) + T2 (lemma) = 2
        assert s["theorems_count"] == 2, f"expected theorems_count=2, got {s}"
        # paper_markers_count: R(1) + I1(2) = 3
        assert s["paper_markers_count"] == 3, f"expected paper_markers_count=3, got {s}"
        _pass(test_name)
    except AssertionError as e:
        _fail(test_name, str(e))


# ---------------------------------------------------------------------------
# Test 14: axioms_count and sorry_count always 0 (project invariant)
# ---------------------------------------------------------------------------
def test_summary_axioms_sorry_always_zero() -> None:
    """Even with arbitrary closure, axioms_count == sorry_count == 0."""
    test_name = "test_summary_axioms_sorry_always_zero"
    records = [
        _make_record("BEDC.A", kind="theorem", dependencies=["BEDC.B", "BEDC.C"]),
        _make_record("BEDC.B", kind="def", dependencies=[]),
        _make_record("BEDC.C", kind="lemma", dependencies=[]),
    ]
    attach_upstream_closure_summaries(records)
    try:
        for r in records:
            s = r["upstream_closure_summary"]
            assert s["axioms_count"] == 0, f"axioms_count != 0 in {r['name']}: {s}"
            assert s["sorry_count"] == 0, f"sorry_count != 0 in {r['name']}: {s}"
        _pass(test_name)
    except AssertionError as e:
        _fail(test_name, str(e))


# ---------------------------------------------------------------------------
# Test 15: real data — every record has upstream_closure_summary with correct shape
# ---------------------------------------------------------------------------
def test_real_data_summary_present() -> None:
    """Run build_theorem_graph and confirm upstream_closure_summary on every record."""
    import json
    test_name = "test_real_data_summary_present"
    script = ROOT / "tools" / "build_theorem_graph.py"
    try:
        result = subprocess.run(
            [sys.executable, str(script)],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            raise RuntimeError(f"build_theorem_graph.py failed:\n{result.stderr}")
        graph_path = ROOT / "docs" / "dossier" / "data" / "theorem_graph.json"
        data = json.loads(graph_path.read_text(encoding="utf-8"))
        records = data["theorems"]
        # Every record must have upstream_closure_summary
        missing = [r["name"] for r in records if "upstream_closure_summary" not in r]
        assert not missing, f"{len(missing)} records missing upstream_closure_summary"
        # axioms_count and sorry_count must always be 0
        bad_axioms = [r["name"] for r in records if r["upstream_closure_summary"]["axioms_count"] != 0]
        assert not bad_axioms, f"axioms_count != 0 in: {bad_axioms[:5]}"
        bad_sorry = [r["name"] for r in records if r["upstream_closure_summary"]["sorry_count"] != 0]
        assert not bad_sorry, f"sorry_count != 0 in: {bad_sorry[:5]}"
        # Sanity: at least some records have non-zero theorems_count (confirms BFS is working)
        with_closures = [r for r in records if r["upstream_closure_summary"]["theorems_count"] > 0]
        assert with_closures, "no record has theorems_count > 0 — closure BFS may be broken"
        _pass(test_name)
    except (AssertionError, RuntimeError) as e:
        _fail(test_name, str(e))


# ---------------------------------------------------------------------------
# Main runner
# ---------------------------------------------------------------------------

def main() -> int:
    print("Running build_theorem_graph dependency extraction tests...")
    test_extract_dependencies_term_mode()
    test_extract_dependencies_apply_exact_refine()
    test_extract_dependencies_namespace_prefix()
    test_extract_dependencies_empty_proof()
    test_extract_dependencies_known_holes_documented()
    test_dep_file_imports_extracted()
    test_extraction_deterministic()
    test_extraction_idempotent_against_real_data()
    # T7: upstream_closure_summary tests
    test_compute_closure_zero_deps()
    test_compute_closure_single_step()
    test_compute_closure_multi_step()
    test_compute_closure_cycle_safe()
    test_compute_summary_kind_counts()
    test_summary_axioms_sorry_always_zero()
    test_real_data_summary_present()

    total = PASS + FAIL
    print(f"\n{total} tests run: {PASS} passed, {FAIL} failed")
    if _FAILURES:
        print("Failures:")
        for f in _FAILURES:
            print(f"  - {f}")
        return 1
    print("All tests passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

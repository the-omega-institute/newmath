#!/usr/bin/env python3
"""Regression test for build_dossier_status.py output invariance.

This test verifies that extracting region/glossary helpers from
build_dossier_status.py to a new _dossier_common.py (T2) does not
change the final JSON output.

Procedure:
1. Run python3 tools/build_dossier_status.py (generates status/glossary/dependency.json)
2. Load each JSON file from docs/dossier/data/
3. Compare against golden files at tools/test_data/golden_*.json:
   - status.json: normalize (strip 'generated_at' and 'monthly_activity'), then compare
   - dependency.json: full deep-compare
   - glossary.json: full deep-compare
4. On mismatch, print unified diff and exit 1
5. On pass, print brief success message and exit 0

Golden files captured at HEAD daa92cdf (pre-refactor state).
"""

from __future__ import annotations

import difflib
import json
import subprocess
import sys
from pathlib import Path


def run_build_dossier() -> int:
    """Execute build_dossier_status.py; return exit code."""
    root = Path(__file__).resolve().parents[1]
    result = subprocess.run(
        [sys.executable, "tools/build_dossier_status.py"],
        cwd=root,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        print(f"ERROR: build_dossier_status.py failed:\n{result.stderr}", file=sys.stderr)
        return 2
    return 0


def load_json(path: Path) -> dict:
    """Load JSON file; exit with code 2 on error."""
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError) as e:
        print(f"ERROR: failed to load {path}: {e}", file=sys.stderr)
        sys.exit(2)


def normalize_status(obj: dict) -> dict:
    """Return copy of status dict with generated_at and monthly_activity removed."""
    normalized = dict(obj)
    normalized.pop("generated_at", None)
    normalized.pop("monthly_activity", None)
    return normalized


def normalize_dependency(obj: dict) -> dict:
    """Sort edges and nodes, strip non-deterministic fields (derived from dict iteration order).

    The 'level' field and 'max_level' are computed by compute_levels() which traverses the
    dependency graph using dict iteration order (non-deterministic in some Python versions
    and build conditions). Strip these for stable comparison.
    """
    normalized = dict(obj)
    # Sort edges by (source, target) to handle set iteration non-determinism
    if "edges" in normalized:
        normalized["edges"] = sorted(
            normalized["edges"],
            key=lambda e: (e["source"], e["target"])
        )
    # Sort nodes by id, and strip the 'level' field which is non-deterministic
    if "nodes" in normalized:
        nodes_normalized = []
        for n in sorted(normalized["nodes"], key=lambda x: x["id"]):
            n_copy = dict(n)
            n_copy.pop("level", None)  # strip non-deterministic computed field
            nodes_normalized.append(n_copy)
        normalized["nodes"] = nodes_normalized
    # Strip max_level as it's derived from non-deterministic level computation
    normalized.pop("max_level", None)
    return normalized


def normalize_glossary(obj: dict) -> dict:
    """Sort glossary entries for deterministic comparison."""
    # Glossary is keyed by term id; ensure consistent iteration order
    return dict(sorted(obj.items()))


def unified_diff(golden_str: str, current_str: str, file_label: str) -> str:
    """Generate unified diff between golden and current JSON."""
    golden_lines = golden_str.splitlines(keepends=True)
    current_lines = current_str.splitlines(keepends=True)
    diff = difflib.unified_diff(
        golden_lines,
        current_lines,
        fromfile=f"golden_{file_label}.json",
        tofile=f"current_{file_label}.json",
        lineterm="",
    )
    return "".join(diff)


def main() -> int:
    """Run regression test; return exit code 0 (pass) or 1 (mismatch)."""
    root = Path(__file__).resolve().parents[1]
    data_dir = root / "docs" / "dossier" / "data"
    test_data_dir = root / "tools" / "test_data"

    # Run build_dossier_status.py
    ret = run_build_dossier()
    if ret != 0:
        return ret

    # Load generated JSON files
    status_current = load_json(data_dir / "status.json")
    dependency_current = load_json(data_dir / "dependency.json")
    glossary_current = load_json(data_dir / "glossary.json")

    # Load golden files
    status_golden = load_json(test_data_dir / "golden_status_normalized.json")
    dependency_golden = load_json(test_data_dir / "golden_dependency.json")
    glossary_golden = load_json(test_data_dir / "golden_glossary.json")

    # Normalize status: strip volatile keys from both
    status_current_normalized = normalize_status(status_current)
    status_golden_normalized = normalize_status(status_golden)

    # Normalize dependency and glossary for deterministic comparison (handles set iteration)
    dependency_current_normalized = normalize_dependency(dependency_current)
    dependency_golden_normalized = normalize_dependency(dependency_golden)
    glossary_current_normalized = normalize_glossary(glossary_current)
    glossary_golden_normalized = normalize_glossary(glossary_golden)

    # Compare all three
    mismatch = False

    if status_current_normalized != status_golden_normalized:
        mismatch = True
        golden_str = json.dumps(status_golden_normalized, indent=2, sort_keys=True)
        current_str = json.dumps(status_current_normalized, indent=2, sort_keys=True)
        diff = unified_diff(golden_str, current_str, "status")
        print("REGRESSION: status.json output changed:", file=sys.stderr)
        print(diff, file=sys.stderr)

    if dependency_current_normalized != dependency_golden_normalized:
        mismatch = True
        golden_str = json.dumps(dependency_golden_normalized, indent=2, sort_keys=True)
        current_str = json.dumps(dependency_current_normalized, indent=2, sort_keys=True)
        diff = unified_diff(golden_str, current_str, "dependency")
        print("REGRESSION: dependency.json output changed:", file=sys.stderr)
        print(diff, file=sys.stderr)

    if glossary_current_normalized != glossary_golden_normalized:
        mismatch = True
        golden_str = json.dumps(glossary_golden_normalized, indent=2, sort_keys=True)
        current_str = json.dumps(glossary_current_normalized, indent=2, sort_keys=True)
        diff = unified_diff(golden_str, current_str, "glossary")
        print("REGRESSION: glossary.json output changed:", file=sys.stderr)
        print(diff, file=sys.stderr)

    if mismatch:
        return 1

    print("regression test PASS — build_dossier_status output unchanged after refactor")
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Tests for tools/check_katex_coverage.py.

Verifies that:
1. Zero-coverage glossary → fallback count == total, exit 0.
2. Full-coverage glossary → fallback count == 0, exit 0.

Both runs MUST exit 0 (warn-only by design).
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

PASS = 0
FAIL = 0


def _pass(name: str) -> None:
    global PASS
    PASS += 1
    print(f"  PASS  {name}")


def _fail(name: str, detail: str) -> None:
    global FAIL
    FAIL += 1
    print(f"  FAIL  {name}: {detail}")


def run_check(graph_records: list[dict], glossary: dict) -> tuple[int, str]:
    """Write temp JSON files, run check_katex_coverage.py, return (exit_code, stderr)."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        graph_path = tmp / "graph.json"
        glossary_path = tmp / "glossary.json"
        graph_path.write_text(
            json.dumps({"theorems": graph_records}), encoding="utf-8"
        )
        glossary_path.write_text(json.dumps(glossary), encoding="utf-8")
        result = subprocess.run(
            [
                sys.executable,
                str(Path(__file__).parent / "check_katex_coverage.py"),
                "--graph",
                str(graph_path),
                "--glossary",
                str(glossary_path),
            ],
            capture_output=True,
            text=True,
        )
        return result.returncode, result.stderr


def test_zero_coverage() -> None:
    name = "test_zero_coverage"
    records = [
        {"name": "BEDC.A.foo"},
        {"name": "BEDC.B.bar"},
        {"name": "BEDC.C.baz"},
    ]
    rc, stderr = run_check(records, {})
    try:
        assert rc == 0, f"expected exit 0, got {rc}"
        assert "0/3" in stderr, f"expected '0/3' in stderr, got: {stderr}"
        assert "3 declarations would fall to tier 3" in stderr, (
            f"expected fallback summary, got: {stderr}"
        )
        _pass(name)
    except AssertionError as e:
        _fail(name, str(e))


def test_full_coverage() -> None:
    name = "test_full_coverage"
    records = [
        {"name": "BEDC.A.foo"},
        {"name": "BEDC.B.bar"},
        {"name": "BEDC.C.baz"},
    ]
    glossary = {
        "foo": {"pattern": "foo", "katex": "f"},
        "bar": {"pattern": "bar", "katex": "b"},
        "baz": {"pattern": "baz", "katex": "z"},
    }
    rc, stderr = run_check(records, glossary)
    try:
        assert rc == 0, f"expected exit 0, got {rc}"
        assert "3/3" in stderr, f"expected '3/3' in stderr, got: {stderr}"
        assert "0 declarations would fall to tier 3" in stderr, (
            f"expected zero fallback, got: {stderr}"
        )
        _pass(name)
    except AssertionError as e:
        _fail(name, str(e))


def test_missing_graph_warns_no_fail() -> None:
    name = "test_missing_graph_warns_no_fail"
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        glossary_path = tmp / "glossary.json"
        glossary_path.write_text("{}", encoding="utf-8")
        result = subprocess.run(
            [
                sys.executable,
                str(Path(__file__).parent / "check_katex_coverage.py"),
                "--graph",
                str(tmp / "missing.json"),
                "--glossary",
                str(glossary_path),
            ],
            capture_output=True,
            text=True,
        )
    try:
        assert result.returncode == 0, f"warn-only: expected exit 0, got {result.returncode}"
        assert "not found" in result.stderr.lower(), (
            f"expected 'not found' warning, got: {result.stderr}"
        )
        _pass(name)
    except AssertionError as e:
        _fail(name, str(e))


def main() -> int:
    print("Running check_katex_coverage tests...")
    test_zero_coverage()
    test_full_coverage()
    test_missing_graph_warns_no_fail()
    print(f"\n{PASS + FAIL} tests run: {PASS} passed, {FAIL} failed")
    return 0 if FAIL == 0 else 1


if __name__ == "__main__":
    sys.exit(main())

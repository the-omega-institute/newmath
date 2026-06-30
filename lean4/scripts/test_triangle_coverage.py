#!/usr/bin/env python3
"""Unit checks for triangle_coverage.py."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
from pathlib import Path


SCRIPT = Path(__file__).resolve().with_name("triangle_coverage.py")
spec = importlib.util.spec_from_file_location("triangle_coverage", SCRIPT)
assert spec is not None and spec.loader is not None
triangle_coverage = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = triangle_coverage
spec.loader.exec_module(triangle_coverage)


def decl(name: str, body: str) -> triangle_coverage.LeanDeclaration:
    return triangle_coverage.LeanDeclaration(
        kind="theorem",
        name=name,
        qualified_name=f"BEDC.Test.{name}",
        file="lean4/BEDC/Test.lean",
        line=1,
        header=body.split(":=", 1)[0],
        body=body,
    )


def test_hollow_tgs_true_intro_is_rejected() -> None:
    bad = decl(
        "bad",
        "theorem bad : IsProjectionOf TriAxisObjCode.base TriAxisProfile.zero := True.intro",
    )
    violations = triangle_coverage.anti_vacuity_violations([bad])
    assert violations
    assert "trivial True proof" in violations[0].reason


def test_constant_default_profile_is_rejected() -> None:
    bad = decl(
        "bad_profile",
        "def bad_profile : TriAxisProfile := TriAxisProfile.zero",
    )
    violations = triangle_coverage.anti_vacuity_violations([bad])
    assert violations
    assert "all-zero/default" in violations[0].reason


def test_recursive_projection_is_accepted() -> None:
    good = decl(
        "good",
        "theorem good : triAxisProjection (TriAxisObjCode.timeGen TriAxisObjCode.base) = "
        "TriAxisProfile.timeStep (triAxisProjection TriAxisObjCode.base) := rfl",
    )
    assert triangle_coverage.anti_vacuity_violations([good]) == []


def test_non_tgs_declaration_is_not_chaff_enforced() -> None:
    ordinary = decl("ordinary", "def ordinary : Nat := 0")
    assert triangle_coverage.tgs_registrations([ordinary]) == []
    assert triangle_coverage.anti_vacuity_violations([ordinary]) == []


def test_designated_file_overrides_script_constant() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "triangle_designated.txt"
        path.write_text("BEDC.Test.Target\n", encoding="utf-8")
        assert triangle_coverage.read_designated(path) == ["BEDC.Test.Target"]


def test_designated_accepts_local_triangle_without_tgs_by_default() -> None:
    target = triangle_coverage.LeanDeclaration(
        kind="structure",
        name="Target",
        qualified_name="BEDC.Test.Target",
        file="lean4/BEDC/Test.lean",
        line=1,
        header="structure Target where",
        body="structure Target where\n  orbitProjection : Nat",
    )
    results = triangle_coverage.designated_results(
        [target],
        [],
        ["BEDC.Test.Target"],
        strict_designated=False,
    )
    assert triangle_coverage.designated_violations(results, strict_designated=False) == []
    assert triangle_coverage.designated_violations(results, strict_designated=True)


if __name__ == "__main__":
    tests = [
        test_hollow_tgs_true_intro_is_rejected,
        test_constant_default_profile_is_rejected,
        test_recursive_projection_is_accepted,
        test_non_tgs_declaration_is_not_chaff_enforced,
        test_designated_file_overrides_script_constant,
        test_designated_accepts_local_triangle_without_tgs_by_default,
    ]
    for test in tests:
        test()
    print("triangle_coverage unit checks: ok")

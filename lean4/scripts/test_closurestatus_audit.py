"""Unit tests for the closurestatus block parser in bedc_ci.py."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from bedc_ci import (  # type: ignore[import-not-found]
    CLOSURESTATUS_BEGIN_RE,
    CLOSURESTATUS_FIELD_RE,
    diagnose_closurestatus_block,
)


class ClosurestatusRegexTests(unittest.TestCase):
    def test_begin_regex_matches_simple_form(self) -> None:
        block = r"\begin{closurestatus}{\NatUp}"
        m = CLOSURESTATUS_BEGIN_RE.search(block)
        self.assertIsNotNone(m)
        assert m is not None
        self.assertEqual(m.group(1), "Nat")

    def test_field_regex_extracts_lean_target(self) -> None:
        body = r"\leantarget{BEDC.Foo.Bar\_baz}"
        m = CLOSURESTATUS_FIELD_RE.search(body)
        self.assertIsNotNone(m)
        assert m is not None
        self.assertEqual(m.group(1), "leantarget")
        self.assertEqual(m.group(2), r"BEDC.Foo.Bar\_baz")


class ClosurestatusDiagnosticsTests(unittest.TestCase):
    def _block(self, **overrides):
        base = {
            "file": "papers/bedc/parts/x.tex",
            "line": 1,
            "region": "Foo",
            "theory_closure": "scopedClosure",
            "formal_status": "theoremCheckedV",
            "lean_target": "BEDC.Foo.example",
            "bridge_status": "none",
            "has_scope": True,
            "has_notclaimed": True,
            "has_upgradepath": True,
        }
        base.update(overrides)
        return base

    def test_clean_block_passes(self) -> None:
        diags = diagnose_closurestatus_block(
            self._block(), lean_symbols={"BEDC.Foo.example"}
        )
        self.assertEqual(diags, [])

    def test_invalid_theory_closure_grade_flagged(self) -> None:
        diags = diagnose_closurestatus_block(
            self._block(theory_closure="bogusGrade"),
            lean_symbols={"BEDC.Foo.example"},
        )
        self.assertTrue(any("invalid theoryclosure" in d for d in diags))

    def test_theorem_checked_without_lean_target_flagged(self) -> None:
        diags = diagnose_closurestatus_block(
            self._block(lean_target=None),
            lean_symbols=set(),
        )
        self.assertTrue(any("requires \\leantarget" in d for d in diags))

    def test_unresolved_lean_target_flagged(self) -> None:
        diags = diagnose_closurestatus_block(
            self._block(lean_target="BEDC.Missing.thing"),
            lean_symbols={"BEDC.Foo.example"},
        )
        self.assertTrue(
            any("does not resolve under lean4/BEDC" in d for d in diags)
        )

    def test_missing_scope_flagged(self) -> None:
        diags = diagnose_closurestatus_block(
            self._block(has_scope=False),
            lean_symbols={"BEDC.Foo.example"},
        )
        self.assertTrue(any("missing \\scopeclosed" in d for d in diags))


if __name__ == "__main__":
    unittest.main(verbosity=2)

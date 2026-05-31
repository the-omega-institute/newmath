#!/usr/bin/env python3
"""CLI contract tests for the glossary coverage checker."""

from __future__ import annotations

import subprocess
import sys
import unittest
from contextlib import redirect_stderr
from io import StringIO
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "tools" / "check_glossary.py"


def run_checker(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(CHECKER), *args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


class GlossaryCheckerCliTests(unittest.TestCase):
    def test_help_lists_survey_and_strict_modes(self) -> None:
        proc = run_checker("--help")
        output = proc.stdout + proc.stderr
        self.assertEqual(proc.returncode, 0, output)
        self.assertIn("--survey", output)
        self.assertIn("--strict", output)
        self.assertIn("Survey glossary coverage", output)

    def test_survey_mode_warns_and_exits_zero_on_coverage_gap(self) -> None:
        proc = run_checker("--survey")
        output = proc.stdout + proc.stderr
        self.assertEqual(proc.returncode, 0, output)
        self.assertIn("SURVEY/WARN", output)
        self.assertIn("exit 0 by design", output)

    def test_default_mode_matches_survey_contract(self) -> None:
        proc = run_checker()
        output = proc.stdout + proc.stderr
        self.assertEqual(proc.returncode, 0, output)
        self.assertIn("SURVEY/WARN", output)
        self.assertIn("exit 0 by design", output)

    def test_strict_mode_fails_on_coverage_gap(self) -> None:
        proc = run_checker("--strict")
        output = proc.stdout + proc.stderr
        self.assertNotEqual(proc.returncode, 0, output)
        self.assertIn("STRICT/FAIL", output)
        self.assertIn("exit nonzero", output)

    def test_duplicate_alias_is_strict_failure(self) -> None:
        import importlib.util

        spec = importlib.util.spec_from_file_location("check_glossary_under_test", CHECKER)
        if spec is None or spec.loader is None:
            raise AssertionError("could not load check_glossary.py")
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)

        issues, _, _, _ = module.collect_issues(
            {
                "_meta": {},
                "TermA": {"aliases": ["Shared"], "en": {"label": "A"}, "zh": {"label": "甲"}},
                "TermB": {"aliases": ["Shared"], "en": {"label": "B"}, "zh": {"label": "乙"}},
            }
        )
        self.assertIn("duplicate alias", "\n".join(issues.duplicate_aliases))
        with redirect_stderr(StringIO()):
            self.assertEqual(module.report_issues(issues, "strict"), 1)


if __name__ == "__main__":
    unittest.main()

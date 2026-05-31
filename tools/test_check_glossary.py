#!/usr/bin/env python3
"""CLI contract tests for the glossary coverage checker."""

from __future__ import annotations

import subprocess
import sys
import unittest
import json
import tempfile
from contextlib import contextmanager, redirect_stderr
from io import StringIO
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "tools" / "check_glossary.py"


def load_checker_module():
    import importlib.util

    spec = importlib.util.spec_from_file_location("check_glossary_under_test", CHECKER)
    if spec is None or spec.loader is None:
        raise AssertionError("could not load check_glossary.py")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


CHECKER_MODULE = load_checker_module()


def run_checker(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(CHECKER), *args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


@contextmanager
def glossary_inputs(*, dependency_nodes: list[dict[str, str]], preamble_text: str):
    old_dep_data = CHECKER_MODULE.DEP_DATA
    old_preamble = CHECKER_MODULE.PREAMBLE
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        dep_data = tmp_path / "dependency.json"
        preamble = tmp_path / "preamble.tex"
        dep_data.write_text(json.dumps({"nodes": dependency_nodes}), encoding="utf-8")
        preamble.write_text(preamble_text, encoding="utf-8")
        CHECKER_MODULE.DEP_DATA = dep_data
        CHECKER_MODULE.PREAMBLE = preamble
        try:
            yield
        finally:
            CHECKER_MODULE.DEP_DATA = old_dep_data
            CHECKER_MODULE.PREAMBLE = old_preamble


def collect_fixture_issues(glossary: dict, *, dependency_nodes: list[dict[str, str]], preamble_text: str):
    with glossary_inputs(dependency_nodes=dependency_nodes, preamble_text=preamble_text):
        return CHECKER_MODULE.collect_issues(glossary)


def gap_fixture_glossary() -> dict:
    return {
        "_meta": {"exempt_macros": [], "label_identical_ok": []},
        "KnownRegion": {
            "aliases": [],
            "en": {"label": "Known region"},
            "zh": {"label": "Known region localized"},
            "constructive_story_zh": "Localized story.",
        },
    }


def complete_fixture_glossary() -> dict:
    return {
        "_meta": {"exempt_macros": [], "label_identical_ok": []},
        "KnownRegion": {
            "aliases": ["KnownMacro"],
            "en": {"label": "Known region"},
            "zh": {"label": "Known region localized"},
            "constructive_story_zh": "Localized story.",
        },
    }


class GlossaryCheckerCliTests(unittest.TestCase):
    def test_help_lists_survey_and_strict_modes(self) -> None:
        proc = run_checker("--help")
        output = proc.stdout + proc.stderr
        self.assertEqual(proc.returncode, 0, output)
        self.assertIn("--survey", output)
        self.assertIn("--strict", output)
        self.assertIn("Survey glossary coverage", output)

    def test_survey_mode_warns_and_exits_zero_on_coverage_gap(self) -> None:
        issues, _, _, _ = collect_fixture_issues(
            gap_fixture_glossary(),
            dependency_nodes=[
                {"id": "KnownRegion", "constructive_story_en": "Known story."},
                {"id": "MissingRegion", "constructive_story_en": ""},
            ],
            preamble_text="\\newcommand{\\KnownMacro}{Known}\n\\newcommand{\\MissingMacro}{Missing}\n",
        )
        stderr = StringIO()
        with redirect_stderr(stderr):
            exit_code = CHECKER_MODULE.report_issues(issues, "survey")
        output = stderr.getvalue()
        self.assertEqual(exit_code, 0, output)
        self.assertIn("SURVEY/WARN", output)
        self.assertIn("exit 0 by design", output)

    def test_default_mode_matches_survey_contract(self) -> None:
        args = CHECKER_MODULE.parse_args([])
        self.assertFalse(args.strict)
        issues, _, _, _ = collect_fixture_issues(
            gap_fixture_glossary(),
            dependency_nodes=[
                {"id": "KnownRegion", "constructive_story_en": "Known story."},
                {"id": "MissingRegion", "constructive_story_en": ""},
            ],
            preamble_text="\\newcommand{\\KnownMacro}{Known}\n\\newcommand{\\MissingMacro}{Missing}\n",
        )
        stderr = StringIO()
        with redirect_stderr(stderr):
            exit_code = CHECKER_MODULE.report_issues(issues, "survey")
        output = stderr.getvalue()
        self.assertEqual(exit_code, 0, output)
        self.assertIn("SURVEY/WARN", output)
        self.assertIn("exit 0 by design", output)

    def test_strict_mode_fails_on_coverage_gap(self) -> None:
        issues, _, _, _ = collect_fixture_issues(
            gap_fixture_glossary(),
            dependency_nodes=[
                {"id": "KnownRegion", "constructive_story_en": "Known story."},
                {"id": "MissingRegion", "constructive_story_en": ""},
            ],
            preamble_text="\\newcommand{\\KnownMacro}{Known}\n\\newcommand{\\MissingMacro}{Missing}\n",
        )
        stderr = StringIO()
        with redirect_stderr(stderr):
            exit_code = CHECKER_MODULE.report_issues(issues, "strict")
        output = stderr.getvalue()
        self.assertNotEqual(exit_code, 0, output)
        self.assertIn("STRICT/FAIL", output)
        self.assertIn("exit nonzero", output)

    def test_no_gap_reports_ok_contract(self) -> None:
        old_glossary_dir = CHECKER_MODULE.GLOSSARY_DIR
        old_load_glossary = CHECKER_MODULE.load_glossary
        with tempfile.TemporaryDirectory() as tmp:
            with glossary_inputs(
                dependency_nodes=[{"id": "KnownRegion", "constructive_story_en": "Known story."}],
                preamble_text="\\newcommand{\\KnownMacro}{Known}\n",
            ):
                CHECKER_MODULE.GLOSSARY_DIR = Path(tmp)
                CHECKER_MODULE.load_glossary = complete_fixture_glossary
                stderr = StringIO()
                try:
                    with redirect_stderr(stderr):
                        exit_code = CHECKER_MODULE.main([])
                finally:
                    CHECKER_MODULE.GLOSSARY_DIR = old_glossary_dir
                    CHECKER_MODULE.load_glossary = old_load_glossary
        output = stderr.getvalue()
        self.assertEqual(exit_code, 0, output)
        self.assertIn("[check-glossary] OK:", output)

    def test_duplicate_alias_is_strict_failure(self) -> None:
        issues, _, _, _ = collect_fixture_issues(
            {
                "_meta": {},
                "TermA": {"aliases": ["Shared"], "en": {"label": "A"}, "zh": {"label": "A localized"}},
                "TermB": {"aliases": ["Shared"], "en": {"label": "B"}, "zh": {"label": "B localized"}},
            },
            dependency_nodes=[],
            preamble_text="",
        )
        self.assertIn("duplicate alias", "\n".join(issues.duplicate_aliases))
        with redirect_stderr(StringIO()):
            self.assertEqual(CHECKER_MODULE.report_issues(issues, "strict"), 1)


if __name__ == "__main__":
    unittest.main()

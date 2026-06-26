from __future__ import annotations

import tempfile
import unittest
import sys
from contextlib import redirect_stderr
from io import StringIO
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import warn_concrete_instances


class WarnConcreteInstancesTests(unittest.TestCase):
    def run_check_e(self, files: dict[str, str]) -> list[dict]:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            paper = root / "papers" / "bedc"
            concrete = paper / "parts" / "concrete_instances"
            concrete.mkdir(parents=True)
            for name, body in files.items():
                (concrete / name).write_text(body, encoding="utf-8")

            old_paper = warn_concrete_instances.PAPER_DIR
            old_concrete = warn_concrete_instances.CONCRETE_DIR
            warn_concrete_instances.PAPER_DIR = paper
            warn_concrete_instances.CONCRETE_DIR = concrete
            try:
                return warn_concrete_instances.check_e_hub_purity()
            finally:
                warn_concrete_instances.PAPER_DIR = old_paper
                warn_concrete_instances.CONCRETE_DIR = old_concrete

    def run_check_u(self, files: dict[str, str]) -> list[dict]:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            paper = root / "papers" / "bedc"
            parts = paper / "parts"
            concrete = parts / "concrete_instances"
            concrete.mkdir(parents=True)
            for name, body in files.items():
                target = parts / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(body, encoding="utf-8")

            old_paper = warn_concrete_instances.PAPER_DIR
            old_concrete = warn_concrete_instances.CONCRETE_DIR
            old_scan_roots = warn_concrete_instances.SCAN_ROOTS
            warn_concrete_instances.PAPER_DIR = paper
            warn_concrete_instances.CONCRETE_DIR = concrete
            warn_concrete_instances.SCAN_ROOTS = [
                paper / "parts",
                paper / "frontmatter",
                paper / "appendices",
            ]
            try:
                return warn_concrete_instances.check_u_calibrated_external_boundary()
            finally:
                warn_concrete_instances.PAPER_DIR = old_paper
                warn_concrete_instances.CONCRETE_DIR = old_concrete
                warn_concrete_instances.SCAN_ROOTS = old_scan_roots

    def run_main_for_check_u(self, files: dict[str, str]) -> int:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            paper = root / "papers" / "bedc"
            parts = paper / "parts"
            concrete = parts / "concrete_instances"
            concrete.mkdir(parents=True)
            for name, body in files.items():
                target = parts / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(body, encoding="utf-8")

            old_paper = warn_concrete_instances.PAPER_DIR
            old_concrete = warn_concrete_instances.CONCRETE_DIR
            old_scan_roots = warn_concrete_instances.SCAN_ROOTS
            old_argv = sys.argv
            warn_concrete_instances.PAPER_DIR = paper
            warn_concrete_instances.CONCRETE_DIR = concrete
            warn_concrete_instances.SCAN_ROOTS = [
                paper / "parts",
                paper / "frontmatter",
                paper / "appendices",
            ]
            sys.argv = ["warn_concrete_instances.py", "--check", "U"]
            try:
                with redirect_stderr(StringIO()):
                    return warn_concrete_instances.main()
            finally:
                warn_concrete_instances.PAPER_DIR = old_paper
                warn_concrete_instances.CONCRETE_DIR = old_concrete
                warn_concrete_instances.SCAN_ROOTS = old_scan_roots
                sys.argv = old_argv

    def test_no_chapter_top_level_namecert_with_definition_fails_check_e(self) -> None:
        violations = self.run_check_e({
            "01_foo_namecert_construction.tex": "\\begin{definition}A.\\end{definition}\n",
        })

        self.assertEqual(len(violations), 1)
        self.assertEqual(violations[0]["check"], "E")
        self.assertIn("top-level no-chapter namecert hub candidate", violations[0]["msg"])
        self.assertIn("\\begin{definition}", violations[0]["msg"])

    def test_top_level_namecert_content_chapter_with_definition_skips_check_e(self) -> None:
        violations = self.run_check_e({
            "01_foo_namecert_construction.tex": (
                "\\chapter{Foo}\n"
                "\\label{ch:concrete-instances-foo-namecert}\n"
                "\\begin{definition}A.\\end{definition}\n"
            ),
        })

        self.assertEqual(violations, [])

    def test_no_chapter_hub_with_orientation_and_input_passes_check_e(self) -> None:
        violations = self.run_check_e({
            "01_foo_namecert_construction.tex": (
                "The Foo packet routes the split chapter body.\n"
                "\\input{parts/concrete_instances/foo/namecert_construction.tex}\n"
            ),
        })

        self.assertEqual(violations, [])

    def test_calibrated_reconstruction_without_boundary_fails_check_u(self) -> None:
        violations = self.run_check_u({
            "concrete_instances/01_foo_namecert_construction.tex": (
                "\\begin{closurestatus}{\\FooUp}\n"
                "  \\externalcorrespondence{\\calibratedReconstruction}\n"
                "  \\reference{mathlib v4.x p-adic corpus, commit abc123}\n"
                "\\end{closurestatus}\n"
            ),
        })

        self.assertEqual(len(violations), 1)
        self.assertEqual(violations[0]["check"], "U")
        self.assertIn("\\boundaryexhaustive{<label>}", violations[0]["msg"])

    def test_calibrated_reconstruction_without_reference_fails_check_u(self) -> None:
        violations = self.run_check_u({
            "concrete_instances/01_foo_namecert_construction.tex": (
                "\\begin{closurestatus}{\\FooUp}\n"
                "  \\externalcorrespondence{\\calibratedReconstruction}\n"
                "  \\boundaryexhaustive{tab:foo-boundary}\n"
                "\\end{closurestatus}\n"
                "\\begin{table}\n"
                "\\caption{Foo boundary.}\n"
                "\\label{tab:foo-boundary}\n"
                "\\end{table}\n"
            ),
        })

        self.assertEqual(len(violations), 1)
        self.assertEqual(violations[0]["check"], "U")
        self.assertIn("\\reference{<external reference>}", violations[0]["msg"])

    def test_calibrated_reconstruction_unresolved_boundary_label_fails_check_u(self) -> None:
        violations = self.run_check_u({
            "concrete_instances/01_foo_namecert_construction.tex": (
                "\\begin{closurestatus}{\\FooUp}\n"
                "  \\externalcorrespondence{\\calibratedReconstruction}\n"
                "  \\reference{mathlib v4.x p-adic corpus, commit abc123}\n"
                "  \\boundaryexhaustive{tab:foo-boundary}\n"
                "\\end{closurestatus}\n"
            ),
        })

        self.assertEqual(len(violations), 1)
        self.assertEqual(violations[0]["check"], "U")
        self.assertIn("has no matching \\label", violations[0]["msg"])

    def test_calibrated_reconstruction_with_reference_and_boundary_label_passes_check_u(self) -> None:
        violations = self.run_check_u({
            "concrete_instances/01_foo_namecert_construction.tex": (
                "\\begin{closurestatus}{\\FooUp}\n"
                "  \\externalcorrespondence{\\calibratedReconstruction}\n"
                "  \\reference{mathlib v4.x p-adic corpus, commit abc123}\n"
                "  \\boundaryexhaustive{tab:foo-boundary}\n"
                "\\end{closurestatus}\n"
                "\\begin{table}\n"
                "\\caption{Foo boundary.}\n"
                "\\label{tab:foo-boundary}\n"
                "\\end{table}\n"
            ),
        })

        self.assertEqual(violations, [])

    def test_calibrated_reconstruction_violation_blocks_default_check_u(self) -> None:
        exit_code = self.run_main_for_check_u({
            "concrete_instances/01_foo_namecert_construction.tex": (
                "\\begin{closurestatus}{\\FooUp}\n"
                "  \\externalcorrespondence{\\calibratedReconstruction}\n"
                "\\end{closurestatus}\n"
            ),
        })

        self.assertEqual(exit_code, 1)


if __name__ == "__main__":
    unittest.main()

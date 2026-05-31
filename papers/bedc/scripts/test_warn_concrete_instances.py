from __future__ import annotations

import tempfile
import unittest
import sys
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


if __name__ == "__main__":
    unittest.main()

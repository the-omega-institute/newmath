"""Unit tests for the derived theorem-status reader view."""
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent))
import bedc_ci  # type: ignore[import-not-found]


class TheoremStatusViewTests(unittest.TestCase):
    def test_record_shape_and_conservative_derivations(self) -> None:
        with TemporaryDirectory() as td:
            root = Path(td) / "papers" / "bedc" / "parts"
            root.mkdir(parents=True)
            paper = root / "sample.tex"
            paper.write_text(
                "\n".join(
                    [
                        r"\chapter{Sample}",
                        r"\label{ch:sample}",
                        r"\begin{definition}[Source row]",
                        r"\label{def:source-row}",
                        r"Source text.",
                        r"\end{definition}",
                        r"\leanchecked{BEDC.Sample.source\_row}",
                        r"\begin{theorem}[Main result]",
                        r"\label{thm:main-result}",
                        r"Use \autoref{def:source-row} and \ref{def:source-row}.",
                        r"\end{theorem}",
                        r"\leanchecked{BEDC.Sample.main\_result}",
                        r"\leanvariant{BEDC.Sample.missing\_variant}",
                        r"\begin{proof}",
                        r"Pointer-only proof body.",
                        r"\end{proof}",
                        r"\begin{closurestatus}{\SampleUp}",
                        r"  \theoryclosure{\scopedClosure}",
                        r"  \formalstatus{\theoremCheckedV}",
                        r"  \leantarget{BEDC.Sample.chapter\_target}",
                        r"  \bridgestatus{none}",
                        r"  \scopeclosed{scope}",
                        r"  \notclaimed{none}",
                        r"  \upgradepath{done}",
                        r"\end{closurestatus}",
                    ]
                ),
                encoding="utf-8",
            )

            with patch("bedc_ci.REPO_ROOT", Path(td)), \
                patch("bedc_ci.PAPER_PARTS_ROOT", root), \
                patch("bedc_ci.part_tex_files", return_value=[paper]), \
                patch("bedc_ci.collect_marker_existence_lean_names", return_value={
                    "BEDC.Sample.source_row",
                    "BEDC.Sample.main_result",
                }):
                records = bedc_ci.collect_theorem_status_records()

        expected_file = "papers/bedc/parts/sample.tex"
        main = next(record for record in records if record["label"] == "thm:main-result")
        self.assertEqual(main["kind"], "theorem")
        self.assertEqual(main["title"], "Main result")
        self.assertEqual(main["file"], expected_file)
        self.assertEqual(main["line"], 8)
        self.assertEqual(main["chapter_label"], "ch:sample")
        self.assertEqual(main["statement_site"], {"file": main["file"], "line": 8})
        self.assertEqual(main["proof_site"], {"file": main["file"], "line": 14})
        self.assertEqual(
            [(ref["macro"], ref["label"]) for ref in main["references"]],
            [("autoref", "def:source-row"), ("ref", "def:source-row")],
        )
        self.assertEqual(
            [(marker["macro"], marker["target"]) for marker in main["lean_markers"]],
            [
                ("leanchecked", "BEDC.Sample.main_result"),
                ("leanvariant", "BEDC.Sample.missing_variant"),
            ],
        )
        self.assertEqual(
            main["lean_resolution"],
            [
                {"target": "BEDC.Sample.main_result", "resolved": True},
                {"target": "BEDC.Sample.missing_variant", "resolved": False},
            ],
        )
        self.assertEqual(main["chapter_closurestatus"]["region"], "Sample")
        self.assertEqual(main["chapter_closurestatus"]["theory_closure"], "scopedClosure")
        self.assertNotIn("formal_status", main["chapter_closurestatus"])
        self.assertNotIn("lean_target", main["chapter_closurestatus"])
        self.assertIsNone(main["dna_roles"]["statement"])
        self.assertEqual(main["dna_roles"]["dependencies"], [])
        self.assertIsNone(main["dna_roles"]["canonical_site"])

    def test_payload_top_level_shape(self) -> None:
        with patch("bedc_ci.collect_theorem_status_records", return_value=[]):
            payload = bedc_ci.theorem_status_payload()
        self.assertEqual(payload["source"], "derived-from-canonical-sources")
        self.assertEqual(payload["records_total"], 0)
        self.assertEqual(payload["theorem_status_records"], [])


if __name__ == "__main__":
    unittest.main(verbosity=2)

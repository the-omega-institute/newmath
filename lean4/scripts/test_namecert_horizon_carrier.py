"""Unit tests for the namecert horizon-carrier visibility gate."""
from __future__ import annotations

import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent))
from bedc_ci import detect_namecert_horizon_carrier_mismatch  # type: ignore[import-not-found]


class NamecertHorizonCarrierTests(unittest.TestCase):
    def _run_gate(self, files: dict[str, str]) -> list[dict[str, object]]:
        with TemporaryDirectory() as td:
            repo = Path(td) / "repo"
            paper_root = repo / "papers" / "bedc"
            parts_root = paper_root / "parts"
            for rel, text in files.items():
                path = repo / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")
            with patch("bedc_ci.REPO_ROOT", repo), \
                patch("bedc_ci.PAPER_ROOT", paper_root), \
                patch("bedc_ci.PAPER_PARTS_ROOT", parts_root):
                return detect_namecert_horizon_carrier_mismatch()

    def _chapter(self, name: str) -> str:
        return f"papers/bedc/parts/concrete_instances/{name}"

    def test_gap_wrong_carrier_is_hard(self) -> None:
        findings = self._run_gate({
            self._chapter("001_foo_bar_namecert_construction.tex"): "\n".join([
                "% BEDC-GAP: synthetic contract",
                r"\begin{closurestatus}{\RationalUp}",
                r"\end{closurestatus}",
            ]),
        })
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["severity"], "hard")

    def test_gap_expected_and_foreign_closurestatus_is_hard(self) -> None:
        findings = self._run_gate({
            self._chapter("001_foo_bar_namecert_construction.tex"): "\n".join([
                "% BEDC-GAP: synthetic contract",
                r"\begin{closurestatus}{\FooBarUp}",
                r"\end{closurestatus}",
                r"\begin{closurestatus}{\RationalUp}",
                r"\end{closurestatus}",
            ]),
        })
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["severity"], "hard")
        self.assertEqual(
            findings[0]["reason"],
            "foreign closurestatus carrier in BEDC-GAP chapter",
        )

    def test_hub_input_resolves_relative_to_paper_root(self) -> None:
        findings = self._run_gate({
            self._chapter("112414_dyadic_interval_net_namecert_construction.tex"): "\n".join([
                r"\closureat{\DyadicIntervalNetUp}{scopedStr}",
                r"\input{parts/concrete_instances/dyadic_interval_net/namecert_construction}",
            ]),
            self._chapter("dyadic_interval_net/namecert_construction.tex"): "\n".join([
                r"\begin{closurestatus}{\DyadicIntervalNetUp}",
                r"\end{closurestatus}",
            ]),
        })
        self.assertEqual(findings, [])

    def test_commented_closurestatus_does_not_satisfy_gate(self) -> None:
        findings = self._run_gate({
            self._chapter("001_foo_bar_namecert_construction.tex"): "\n".join([
                "% BEDC-GAP: synthetic contract",
                r"% \begin{closurestatus}{\FooBarUp}",
                r"\begin{closurestatus}{\RationalUp}",
                r"\end{closurestatus}",
            ]),
        })
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["closurestatus_carriers"], ["Rational"])

    def test_closureat_does_not_mask_foreign_closurestatus(self) -> None:
        findings = self._run_gate({
            self._chapter("001_foo_bar_namecert_construction.tex"): "\n".join([
                "% BEDC-GAP: synthetic contract",
                r"\closureat{\FooBarUp}{scopedStr}",
                r"\begin{closurestatus}{\RationalUp}",
                r"\end{closurestatus}",
            ]),
        })
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["severity"], "hard")

    def test_digit_carrier_is_not_critical_path_visible(self) -> None:
        findings = self._run_gate({
            self._chapter("001_rule_namecert_construction.tex"): "\n".join([
                "% BEDC-GAP: synthetic contract",
                r"\begin{closurestatus}{\Rule110Up}",
                r"\end{closurestatus}",
            ]),
        })
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["closurestatus_carriers"], [])
        self.assertEqual(findings[0]["reason"], "no carrier matches namecert slug")

    def test_closureat_only_digit_carrier_is_hard(self) -> None:
        findings = self._run_gate({
            self._chapter("001_rule_namecert_construction.tex"): "\n".join([
                "% BEDC-GAP: synthetic contract",
                r"\closureat{\Rule110Up}{scopedStr}",
            ]),
        })
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["severity"], "hard")
        self.assertEqual(findings[0]["closureat_carriers"], [])
        self.assertEqual(findings[0]["reason"], "no carrier matches namecert slug")

    def test_no_status_chapter_is_ignored(self) -> None:
        findings = self._run_gate({
            self._chapter("001_foo_bar_namecert_construction.tex"): "% BEDC-GAP: synthetic contract\n",
        })
        self.assertEqual(findings, [])

    def test_legacy_non_gap_mismatch_is_warning(self) -> None:
        findings = self._run_gate({
            self._chapter("001_foo_bar_namecert_construction.tex"): "\n".join([
                r"\begin{closurestatus}{\RationalUp}",
                r"\end{closurestatus}",
            ]),
        })
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["severity"], "warning")


if __name__ == "__main__":
    unittest.main()

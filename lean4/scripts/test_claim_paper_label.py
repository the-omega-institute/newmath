from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

import claim_paper_label as claims


class ClaimPaperLabelTests(unittest.TestCase):
    def test_holder_claim_release(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            original_file = claims.CLAIMS_FILE
            original_parts = claims.PAPER_PARTS
            try:
                claims.CLAIMS_FILE = Path(td) / "claims.json"
                claims.PAPER_PARTS = Path(td) / "parts"
                claims.PAPER_PARTS.mkdir()

                first = claims.claim("paper-revise-foo-wabc1234", ["thm:foo"])
                second = claims.claim("paper-revise-bar-wxyz9876", ["thm:foo"])

                self.assertEqual(first["kept"], ["thm:foo"])
                self.assertEqual(second["kept"], [])
                self.assertEqual(second["dropped"][0]["reason"], "claimed_by_paper-revise-foo-wabc1234")

                released = claims.release("paper-revise-foo-wabc1234")
                self.assertEqual(released["released"], ["thm:foo"])

                third = claims.claim("paper-revise-bar-wxyz9876", ["thm:foo"])
                self.assertEqual(third["kept"], ["thm:foo"])
            finally:
                claims.CLAIMS_FILE = original_file
                claims.PAPER_PARTS = original_parts

    def test_round_compatibility_still_maps_to_holder_value(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            original_file = claims.CLAIMS_FILE
            original_parts = claims.PAPER_PARTS
            try:
                claims.CLAIMS_FILE = Path(td) / "claims.json"
                claims.PAPER_PARTS = Path(td) / "parts"
                claims.PAPER_PARTS.mkdir()

                first = claims.claim("P7", ["def:foo"])
                second = claims.claim("paper-revise-foo-wabc1234", ["def:foo"])

                self.assertEqual(first["kept"], ["def:foo"])
                self.assertEqual(second["dropped"][0]["reason"], "claimed_by_P7")
            finally:
                claims.CLAIMS_FILE = original_file
                claims.PAPER_PARTS = original_parts


if __name__ == "__main__":
    unittest.main()

import json
from pathlib import Path
import sys
import unittest


sys.path.insert(0, str(Path(__file__).resolve().parent))

import bedc_writeback_gates
import lanes


PROVENANCE_KEYS = {
    "experiment_run_id",
    "verified_at",
    "claim_id",
    "snapshot",
    "source_path",
    "commit",
    "automath_path",
}


def _json_text(value: object) -> str:
    return json.dumps(value, sort_keys=True)


class MathOnlyWritebackTest(unittest.TestCase):
    def test_sanitize_math_facts_for_author_removes_provenance(self) -> None:
        raw = {
            "claim_id": "h0.window",
            "experiment_run_id": "abc123",
            "verified_at": "2026-06-12T10:11:12Z",
            "snapshot": "tools/fibonacci_reality/state/run.json",
            "source_path": "/tmp/source.lean",
            "commit": "deadbeef",
            "automath_path": "external/theorem",
            "statement": "Finite window carrier admits a boundary count.",
            "carrier": {"window_length": 6, "finite_set": "binary words"},
            "partition": {"cells": ["U", "V"]},
            "relations": {"edge": "shift adjacency"},
            "exact_counts": {"boundary_edges": 32},
            "risk_flags": {"needs_certificate": "physical interpretation"},
            "values": {"lambda_M": 0.5},
        }

        sanitized = lanes._sanitize_math_facts_for_author(raw)
        encoded = _json_text(sanitized)

        for key in PROVENANCE_KEYS:
            self.assertNotIn(key, encoded)
        self.assertNotIn("lambda_M", encoded)
        self.assertTrue(sanitized["statement"])
        self.assertEqual(sanitized["carrier"]["window_length"], 6)
        self.assertEqual(sanitized["partition"]["cells"], ["U", "V"])
        self.assertEqual(sanitized["relations"]["edge"], "shift adjacency")
        self.assertEqual(sanitized["exact_counts"]["boundary_edges"], 32)
        self.assertEqual(sanitized["risk_flags"]["needs_certificate"], "physical interpretation")

    def test_author_prompt_payload_contains_only_sanitized_math_facts(self) -> None:
        prompt = lanes._bio_w_author_prompt(
            mode="namecert",
            claim_id="h0.window",
            slug="window",
            verified_facts={
                "claim_id": "h0.window",
                "experiment_run_id": "abc123",
                "verified_at": "2026-06-12T10:11:12Z",
                "source_path": "tools/fibonacci_reality/state/run.json",
                "statement": "Finite window carrier admits a boundary count.",
                "carrier": {"window_length": 6},
                "exact_counts": {"boundary_edges": 32},
            },
            conjecture={"informal_statement": "codon text should not enter the prompt"},
            contacts=[{"source_path": "tools/x.json"}],
            probes=[{"claim_id": "h0.window"}],
            mismatches=[],
        )

        self.assertNotIn("experiment_run_id", prompt)
        self.assertNotIn("verified_at", prompt)
        self.assertNotIn("source_path", prompt)
        self.assertNotIn("h0.window", prompt)
        self.assertNotIn("codon text should not enter", prompt)
        self.assertIn("Finite window carrier admits a boundary count.", prompt)
        self.assertIn("boundary_edges", prompt)

    def test_claim_key_wrapper_is_not_author_payload_key(self) -> None:
        sanitized = lanes._sanitize_math_facts_for_author(
            {
                "h0.window": {
                    "experiment_run_id": "abc123",
                    "statement": "Wrapped finite statement.",
                    "carrier": {"window_length": 6},
                }
            }
        )
        encoded = _json_text(sanitized)

        self.assertNotIn("h0.window", encoded)
        self.assertEqual(sanitized["statement"], "Wrapped finite statement.")
        self.assertEqual(sanitized["carrier"]["window_length"], 6)

    def test_provenance_gate_blocks_author_output(self) -> None:
        text = "See tools/fibonacci_reality/out/x.json Run abc123 verified_at 2026-06-12T10:11:12Z claim_id h0 automath"
        issues = bedc_writeback_gates.provenance_separation_gate(text)
        self.assertTrue(issues)
        self.assertTrue(any("tools/fibonacci_reality/out/x.json" in issue for issue in issues))
        self.assertTrue(any("verified_at" in issue for issue in issues))
        self.assertTrue(any("claim_id" in issue for issue in issues))
        self.assertTrue(any("automath" in issue.lower() for issue in issues))

    def test_structure_gate_passes_self_contained_math_chapter(self) -> None:
        chapter = (
            "The carrier is the finite set of six-bit words. "
            "A partition splits the carrier into four cells. "
            "The edge relation is the shift adjacency relation on the finite carrier. "
            "The exact count of boundary edges is 32 and the factorization is 32=2^5. "
            "The notclaimed boundary excludes physical identification and global flow."
        ) * 8
        facts = {
            "carrier": "six-bit words",
            "partition": ["U", "V"],
            "relations": ["edge"],
            "exact_counts": {"boundary": 32},
            "factorization": "32=2^5",
            "not_claimed": ["physical identification"],
        }

        ok, reason = bedc_writeback_gates.check_namecert_generic_prose(chapter, facts, "internal")
        self.assertTrue(ok, reason)


if __name__ == "__main__":
    unittest.main()

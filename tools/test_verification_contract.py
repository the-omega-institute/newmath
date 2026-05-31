from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import verification_contract as vc


class VerificationContractTests(unittest.TestCase):
    def test_worker_premerge_plan_marks_full_builds_deferred(self):
        plan = {row["gate"]: row for row in vc.mode_plan("worker-premerge")}

        self.assertEqual(plan["paper-full-make"]["disposition"], "deferred")
        self.assertEqual(plan["lean-full-build"]["disposition"], "deferred")
        self.assertEqual(plan["paper-precheck"]["disposition"], "required")

    def test_ship_plan_requires_full_verification_family(self):
        gates = {row["gate"] for row in vc.mode_plan("ship")}

        self.assertIn("paper-full-make", gates)
        self.assertIn("lean-full-build", gates)
        self.assertIn("axiom-audit", gates)
        self.assertIn("paper-lean-audit", gates)
        self.assertIn("axiom-purity", gates)

    def test_deferred_gate_is_not_success(self):
        sha = "a" * 40
        with tempfile.TemporaryDirectory() as td:
            ledger = Path(td) / "ledger.jsonl"
            vc.record(
                sha=sha,
                gate="paper-full-make",
                status="deferred",
                mode="worker-premerge",
                ledger_path=ledger,
            )

            status = vc.status_for(sha=sha, mode="worker-premerge", ledger_path=ledger)

        self.assertEqual(status["overall"], "deferred")
        paper_gate = next(row for row in status["gates"] if row["gate"] == "paper-full-make")
        self.assertEqual(paper_gate["status"], "deferred")

    def test_async_builder_pass_fulfills_same_sha_gate(self):
        sha = "b" * 40
        with tempfile.TemporaryDirectory() as td:
            ledger = Path(td) / "ledger.jsonl"
            vc.record(
                sha=sha,
                gate="paper-full-make",
                status="deferred",
                mode="worker-premerge",
                ledger_path=ledger,
            )
            vc.record(
                sha=sha,
                gate="paper-full-make",
                status="passed",
                mode="async-builder",
                ledger_path=ledger,
            )

            status = vc.status_for(sha=sha, mode="worker-premerge", ledger_path=ledger)

        paper_gate = next(row for row in status["gates"] if row["gate"] == "paper-full-make")
        self.assertEqual(paper_gate["status"], "passed")

    def test_failed_async_builder_blocks_status(self):
        sha = "c" * 40
        with tempfile.TemporaryDirectory() as td:
            ledger = Path(td) / "ledger.jsonl"
            vc.record(
                sha=sha,
                gate="lean-full-build",
                status="deferred",
                mode="worker-premerge",
                ledger_path=ledger,
            )
            vc.record(
                sha=sha,
                gate="lean-full-build",
                status="failed",
                mode="async-builder",
                ledger_path=ledger,
            )

            status = vc.status_for(sha=sha, mode="worker-premerge", ledger_path=ledger)

        self.assertEqual(status["overall"], "failed")
        lean_gate = next(row for row in status["gates"] if row["gate"] == "lean-full-build")
        self.assertEqual(lean_gate["status"], "failed")


if __name__ == "__main__":
    unittest.main()

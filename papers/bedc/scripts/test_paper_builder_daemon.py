from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT_PATH = REPO_ROOT / "papers" / "bedc" / "scripts" / "paper_builder_daemon.py"


def load_paper_builder_daemon():
    spec = importlib.util.spec_from_file_location("paper_builder_daemon_under_test", SCRIPT_PATH)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


class PaperBuilderDaemonVerificationContractTests(unittest.TestCase):
    def test_records_passed_and_failed_envelopes(self):
        daemon = load_paper_builder_daemon()
        with tempfile.TemporaryDirectory() as td:
            ledger = Path(td) / "ledger.jsonl"
            original_record = daemon.record
            try:
                daemon.record = lambda **kwargs: original_record(**kwargs, ledger_path=ledger)

                daemon.record_full_build_result(
                    "a" * 40,
                    ok=True,
                    tail="ok",
                    elapsed=3.0,
                    started_at="2026-05-31T00:00:00Z",
                )
                daemon.record_full_build_result(
                    "b" * 40,
                    ok=False,
                    tail="failed",
                    elapsed=4.0,
                    started_at="2026-05-31T00:00:00Z",
                )

                rows = [
                    json.loads(line)
                    for line in ledger.read_text(encoding="utf-8").splitlines()
                ]
            finally:
                daemon.record = original_record

        self.assertEqual(rows[0]["gate"], "paper-full-make")
        self.assertEqual(rows[0]["status"], "passed")
        self.assertEqual(rows[1]["gate"], "paper-full-make")
        self.assertEqual(rows[1]["status"], "failed")


if __name__ == "__main__":
    unittest.main()

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT_PATH = REPO_ROOT / "papers" / "bedc" / "scripts" / "codex_revise.py"


def load_codex_revise():
    spec = importlib.util.spec_from_file_location("codex_revise_under_test", SCRIPT_PATH)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


class CodexReviseVerificationContractTests(unittest.TestCase):
    def test_deferred_pdf_build_records_envelope(self):
        cr = load_codex_revise()
        with tempfile.TemporaryDirectory() as td:
            ledger = Path(td) / "ledger.jsonl"
            wt = cr.WorktreeInfo(
                path=Path(td),
                branch="paper-test",
                round_number=1,
                base_sha="a" * 40,
            )
            original_record = cr.record
            original_current_sha = cr.current_sha
            try:
                cr.record = lambda **kwargs: original_record(**kwargs, ledger_path=ledger)
                cr.current_sha = lambda _path: "b" * 40

                envelope = cr.record_deferred_pdf_build(wt)

                row = json.loads(ledger.read_text(encoding="utf-8").strip())
                self.assertEqual(envelope.status, "deferred")
                self.assertEqual(row["gate"], "paper-full-make")
                self.assertEqual(row["status"], "deferred")
                self.assertEqual(row["owner"], "paper_builder_daemon")
            finally:
                cr.record = original_record
                cr.current_sha = original_current_sha

    def test_deferred_pdf_build_accepts_explicit_merge_sha(self):
        cr = load_codex_revise()
        with tempfile.TemporaryDirectory() as td:
            ledger = Path(td) / "ledger.jsonl"
            wt = cr.WorktreeInfo(
                path=Path(td),
                branch="paper-test",
                round_number=1,
                base_sha="a" * 40,
            )
            original_record = cr.record
            original_current_sha = cr.current_sha
            try:
                cr.record = lambda **kwargs: original_record(**kwargs, ledger_path=ledger)
                cr.current_sha = lambda _path: "b" * 40

                envelope = cr.record_deferred_pdf_build(wt, sha="c" * 40)

                self.assertEqual(envelope.sha, "c" * 40)
                row = json.loads(ledger.read_text(encoding="utf-8").strip())
                self.assertEqual(row["sha"], "c" * 40)
            finally:
                cr.record = original_record
                cr.current_sha = original_current_sha


if __name__ == "__main__":
    unittest.main()

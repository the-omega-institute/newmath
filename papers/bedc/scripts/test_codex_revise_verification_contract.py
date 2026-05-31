from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from contextlib import nullcontext
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT_PATH = REPO_ROOT / "papers" / "bedc" / "scripts" / "codex_revise.py"


def load_codex_revise():
    spec = importlib.util.spec_from_file_location("codex_revise_under_test", SCRIPT_PATH)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def completed(stdout: str = "", stderr: str = "", returncode: int = 0):
    return subprocess.CompletedProcess([], returncode, stdout, stderr)


def clean_gate_results(cr):
    return {name: [] for name in cr.PAPER_GATE_POLICY}


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

    def test_verify_worktree_commits_records_deferred_pdf_for_head_sha(self):
        cr = load_codex_revise()
        expected_sha = "d" * 40
        with tempfile.TemporaryDirectory() as td:
            ledger = Path(td) / "ledger.jsonl"
            wt = cr.WorktreeInfo(
                path=Path(td),
                branch="paper-test",
                round_number=7,
                base_sha="a" * 40,
            )
            original_record = cr.record
            try:
                cr.record = lambda **kwargs: original_record(**kwargs, ledger_path=ledger)
                with (
                    patch.object(
                        cr,
                        "run_cmd",
                        return_value=completed("1234567 P7: verify branch\n"),
                    ),
                    patch.object(
                        cr,
                        "_run_phase_paper_gates",
                        return_value=cr.PhasePaperGateOutcome.ok(clean_gate_results(cr)),
                    ),
                    patch.object(cr, "current_sha", return_value=expected_sha),
                    patch.object(cr, "run_drift_audit", return_value=(True, "ok")),
                    patch.object(cr, "_changed_files", return_value=[]),
                ):
                    ok, new = cr.verify_worktree_commits(wt, pre_commits=[])

                row = json.loads(ledger.read_text(encoding="utf-8").strip())
                self.assertTrue(ok)
                self.assertEqual(new, ["1234567 P7: verify branch"])
                self.assertEqual(row["sha"], expected_sha)
                self.assertEqual(row["gate"], "paper-full-make")
                self.assertEqual(row["status"], "deferred")
            finally:
                cr.record = original_record

    def test_merge_worktree_to_base_records_deferred_pdf_after_origin_contains_tip(self):
        cr = load_codex_revise()
        expected_sha = "e" * 40
        with tempfile.TemporaryDirectory() as td:
            ledger = Path(td) / "ledger.jsonl"
            wt = cr.WorktreeInfo(
                path=Path(td),
                branch="paper-test",
                round_number=8,
                base_sha="a" * 40,
            )
            original_record = cr.record
            try:
                cr.record = lambda **kwargs: original_record(**kwargs, ledger_path=ledger)

                def fake_run_cmd(cmd, **_kwargs):
                    if cmd[:3] == ["git", "merge", "--no-ff"]:
                        return completed()
                    if cmd[:3] == ["git", "log", "--oneline"]:
                        return completed("abcdef0 P8: push branch\n")
                    if cmd[:3] == ["git", "rev-parse", "HEAD"]:
                        return completed(expected_sha)
                    if cmd[:3] == ["git", "rev-parse", cr.BASE_BRANCH]:
                        return completed("b" * 40)
                    if cmd[:4] == ["git", "rev-parse", f"origin/{cr.BASE_BRANCH}"]:
                        return completed("b" * 40)
                    if cmd[:4] == ["git", "merge-base", "--is-ancestor", expected_sha]:
                        return completed()
                    if cmd[:3] == ["git", "push", "origin"]:
                        return completed()
                    if cmd[:3] == ["git", "fetch", "origin"]:
                        return completed()
                    self.fail(f"unexpected git command: {cmd}")

                with (
                    patch.dict(
                        sys.modules,
                        {
                            "repo_push_lock": SimpleNamespace(
                                acquire_push_lock=lambda *_args, **_kwargs: nullcontext()
                            )
                        },
                    ),
                    patch.object(cr, "_sync_local_with_origin", return_value=True),
                    patch.object(cr, "run_cmd", side_effect=fake_run_cmd),
                    patch.object(cr, "run_drift_audit", return_value=(True, "ok")),
                    patch.object(cr, "_ff_local_branch_to", return_value=(True, "")),
                ):
                    self.assertTrue(cr.merge_worktree_to_base(wt))

                row = json.loads(ledger.read_text(encoding="utf-8").strip())
                self.assertEqual(row["sha"], expected_sha)
                self.assertEqual(row["gate"], "paper-full-make")
                self.assertEqual(row["status"], "deferred")
            finally:
                cr.record = original_record

    def test_codex_revise_source_excludes_skipped_pdf_success_path(self):
        source = SCRIPT_PATH.read_text(encoding="utf-8")

        self.assertNotIn("run_pdf_build", source)
        self.assertNotIn("PDF build skipped", source)
        self.assertNotIn("skipped build OK", source)
        self.assertNotIn("skipped build as OK", source)

    def test_phase_paper_gate_runner_timeout_fails_verification(self):
        cr = load_codex_revise()
        with tempfile.TemporaryDirectory() as td:
            ledger = Path(td) / "ledger.jsonl"
            wt = cr.WorktreeInfo(
                path=Path(td),
                branch="paper-test",
                round_number=9,
                base_sha="a" * 40,
            )
            original_record = cr.record
            try:
                cr.record = lambda **kwargs: original_record(**kwargs, ledger_path=ledger)
                with (
                    patch.object(
                        cr,
                        "run_cmd",
                        return_value=completed("1234567 P9: verify branch\n"),
                    ),
                    patch.object(
                        cr.subprocess,
                        "run",
                        side_effect=subprocess.TimeoutExpired(["phase"], 300),
                    ),
                    patch.object(cr, "run_drift_audit") as drift_audit,
                ):
                    ok, new = cr.verify_worktree_commits(wt, pre_commits=[])

                self.assertFalse(ok)
                self.assertEqual(new, ["1234567 P9: verify branch"])
                self.assertFalse(ledger.exists())
                drift_audit.assert_not_called()
            finally:
                cr.record = original_record

    def test_phase_paper_gate_invalid_json_fails_verification(self):
        cr = load_codex_revise()
        with tempfile.TemporaryDirectory() as td:
            wt = cr.WorktreeInfo(
                path=Path(td),
                branch="paper-test",
                round_number=10,
                base_sha="a" * 40,
            )
            with (
                patch.object(
                    cr,
                    "run_cmd",
                    return_value=completed("1234567 P10: verify branch\n"),
                ),
                patch.object(cr.subprocess, "run", return_value=completed("{not-json")),
            ):
                outcome = cr._run_phase_paper_gates(wt)
                ok, new = cr.verify_worktree_commits(wt, pre_commits=[])

            self.assertFalse(outcome.ok)
            self.assertEqual(outcome.failure_code, "invalid-json")
            self.assertIn("invalid JSON", outcome.detail)
            self.assertFalse(ok)
            self.assertEqual(new, ["1234567 P10: verify branch"])

    def test_phase_paper_gate_missing_key_fails_closed(self):
        cr = load_codex_revise()
        results = clean_gate_results(cr)
        results.pop("math")
        with tempfile.TemporaryDirectory() as td:
            wt = cr.WorktreeInfo(
                path=Path(td),
                branch="paper-test",
                round_number=11,
                base_sha="a" * 40,
            )
            with (
                patch.object(
                    cr,
                    "run_cmd",
                    return_value=completed("1234567 P11: verify branch\n"),
                ),
                patch.object(
                    cr.subprocess,
                    "run",
                    return_value=completed(json.dumps(results)),
                ),
            ):
                outcome = cr._run_phase_paper_gates(wt)
                ok, new = cr.verify_worktree_commits(wt, pre_commits=[])

            self.assertFalse(outcome.ok)
            self.assertEqual(outcome.failure_code, "invalid-schema")
            self.assertIn("missing=['math']", outcome.detail)
            self.assertFalse(ok)
            self.assertEqual(new, ["1234567 P11: verify branch"])

    def test_phase_paper_gate_advisory_violations_do_not_block(self):
        cr = load_codex_revise()
        expected_sha = "f" * 40
        results = clean_gate_results(cr)
        results["vocab"] = ["paper.tex:1: forbidden token"]
        results["leanvariant"] = ["paper.tex:2: new \\leanvariant{X}"]
        with tempfile.TemporaryDirectory() as td:
            ledger = Path(td) / "ledger.jsonl"
            wt = cr.WorktreeInfo(
                path=Path(td),
                branch="paper-test",
                round_number=12,
                base_sha="a" * 40,
            )
            original_record = cr.record
            try:
                cr.record = lambda **kwargs: original_record(**kwargs, ledger_path=ledger)
                with (
                    patch.object(
                        cr,
                        "run_cmd",
                        return_value=completed("1234567 P12: verify branch\n"),
                    ),
                    patch.object(
                        cr.subprocess,
                        "run",
                        return_value=completed(json.dumps(results)),
                    ),
                    patch.object(cr, "current_sha", return_value=expected_sha),
                    patch.object(cr, "run_drift_audit", return_value=(True, "ok")) as drift_audit,
                    patch.object(cr, "_changed_files", return_value=[]),
                ):
                    ok, new = cr.verify_worktree_commits(wt, pre_commits=[])

                row = json.loads(ledger.read_text(encoding="utf-8").strip())
                self.assertTrue(ok)
                self.assertEqual(new, ["1234567 P12: verify branch"])
                self.assertEqual(row["gate"], "paper-full-make")
                self.assertEqual(row["status"], "deferred")
                self.assertEqual(row["sha"], expected_sha)
                drift_audit.assert_called_once_with(wt)
            finally:
                cr.record = original_record

    def test_phase_paper_gate_hard_violation_blocks(self):
        cr = load_codex_revise()
        results = clean_gate_results(cr)
        results["math"] = ["paper.tex:3: forbidden math env \\begin{align}"]
        with tempfile.TemporaryDirectory() as td:
            ledger = Path(td) / "ledger.jsonl"
            wt = cr.WorktreeInfo(
                path=Path(td),
                branch="paper-test",
                round_number=13,
                base_sha="a" * 40,
            )
            original_record = cr.record
            try:
                cr.record = lambda **kwargs: original_record(**kwargs, ledger_path=ledger)
                with (
                    patch.object(
                        cr,
                        "run_cmd",
                        return_value=completed("1234567 P13: verify branch\n"),
                    ),
                    patch.object(
                        cr.subprocess,
                        "run",
                        return_value=completed(json.dumps(results)),
                    ),
                    patch.object(cr, "run_drift_audit") as drift_audit,
                ):
                    ok, new = cr.verify_worktree_commits(wt, pre_commits=[])

                self.assertFalse(ok)
                self.assertEqual(new, ["1234567 P13: verify branch"])
                self.assertFalse(ledger.exists())
                drift_audit.assert_not_called()
            finally:
                cr.record = original_record


if __name__ == "__main__":
    unittest.main()

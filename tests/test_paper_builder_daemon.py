#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_PATH = REPO_ROOT / "papers" / "bedc" / "scripts" / "paper_builder_daemon.py"


def load_daemon():
    spec = importlib.util.spec_from_file_location("paper_builder_daemon_under_test", SCRIPT_PATH)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


daemon = load_daemon()

CONCRETE_TARGETS = [
    "concrete_instances_opening",
    "concrete_instances_middle",
    "concrete_instances_analysis",
    "concrete_instances_completion",
]


class PaperBuilderDaemonTests(unittest.TestCase):
    def test_retry_state_uses_target_key_and_accepts_sha_only_rows(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            state = Path(td) / "broken.txt"
            original = daemon.BROKEN_SHAS_FILE
            try:
                daemon.BROKEN_SHAS_FILE = state
                state.write_text(
                    "oldsha\n"
                    "newsha main\n"
                    "newsha concrete_instances_opening\n",
                    encoding="utf-8",
                )

                self.assertEqual(daemon.fix_attempts_for("oldsha", "main"), 1)
                self.assertEqual(daemon.fix_attempts_for("oldsha", "concrete_instances_opening"), 1)
                self.assertEqual(daemon.fix_attempts_for("newsha", "main"), 1)
                self.assertEqual(daemon.fix_attempts_for("newsha", "concrete_instances_opening"), 1)
                self.assertEqual(daemon.fix_attempts_for("newsha", "other"), 0)

                daemon.record_fix_attempt("newsha", "main")
                self.assertEqual(daemon.fix_attempts_for("newsha", "main"), 2)
                self.assertEqual(daemon.fix_attempts_for("newsha", "concrete_instances_opening"), 1)
                self.assertIn("newsha main", state.read_text(encoding="utf-8").splitlines())
            finally:
                daemon.BROKEN_SHAS_FILE = original

    def test_pdf_targets_are_main_plus_four_concrete_roots(self) -> None:
        self.assertEqual(daemon.PDF_TARGETS, ("main", *CONCRETE_TARGETS))

    def test_run_full_build_calls_target_pdf_make(self) -> None:
        calls: list[tuple[list[str], str]] = []

        def fake_run(cmd, cwd=None, capture_output=None, text=None, errors=None, timeout=None):
            calls.append((list(cmd), str(cwd)))
            return subprocess.CompletedProcess(cmd, 0, stdout="ok", stderr="")

        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "papers" / "bedc").mkdir(parents=True)
            original_dir = daemon.BUILDER_DIR
            original_run = daemon.subprocess.run
            try:
                daemon.BUILDER_DIR = root
                daemon.subprocess.run = fake_run
                ok_main, _, _ = daemon.run_full_build("main")
                ok_concrete, _, _ = daemon.run_full_build("concrete_instances_analysis")
            finally:
                daemon.BUILDER_DIR = original_dir
                daemon.subprocess.run = original_run

        self.assertTrue(ok_main)
        self.assertTrue(ok_concrete)
        self.assertEqual([cmd for cmd, _ in calls], [["make", "main.pdf"], ["make", "concrete_instances_analysis.pdf"]])

    def test_run_full_build_timeout_names_target(self) -> None:
        def fake_run(*args, **kwargs):
            raise subprocess.TimeoutExpired(["make", "concrete_instances_completion.pdf"], 30)

        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "papers" / "bedc").mkdir(parents=True)
            original_dir = daemon.BUILDER_DIR
            original_run = daemon.subprocess.run
            original_timeout = daemon.BUILD_TIMEOUT_S
            try:
                daemon.BUILDER_DIR = root
                daemon.subprocess.run = fake_run
                daemon.BUILD_TIMEOUT_S = 30
                ok, tail, _ = daemon.run_full_build("concrete_instances_completion")
            finally:
                daemon.BUILDER_DIR = original_dir
                daemon.subprocess.run = original_run
                daemon.BUILD_TIMEOUT_S = original_timeout

        self.assertFalse(ok)
        self.assertIn("make concrete_instances_completion.pdf timed out", tail)

    def test_build_sha_once_runs_both_targets_and_records_failed_target(self) -> None:
        events: list[tuple[str, str]] = []

        def fake_checkout(sha: str) -> bool:
            events.append(("checkout", sha))
            return True

        def fake_build(target: str):
            events.append(("build", target))
            if target == "main":
                return True, "ok", 1.0
            if target == "concrete_instances_completion":
                return False, "broken concrete", 2.0
            return True, "ok", 1.0

        def fake_attempts(sha: str, target: str) -> int:
            events.append(("attempts", f"{sha}:{target}"))
            return 0

        def fake_record(sha: str, target: str) -> None:
            events.append(("record", f"{sha}:{target}"))

        def fake_fix(sha: str, target: str, tail: str, elapsed: float) -> bool:
            events.append(("fix", f"{sha}:{target}:{tail}:{elapsed:.0f}"))
            return False

        def fake_write(sha: str) -> None:
            events.append(("write_last", sha))

        originals = (
            daemon.checkout,
            daemon.run_full_build,
            daemon.fix_attempts_for,
            daemon.record_fix_attempt,
            daemon.codex_fix,
            daemon.write_last_built,
            daemon.log,
        )
        try:
            daemon.checkout = fake_checkout
            daemon.run_full_build = fake_build
            daemon.fix_attempts_for = fake_attempts
            daemon.record_fix_attempt = fake_record
            daemon.codex_fix = fake_fix
            daemon.write_last_built = fake_write
            daemon.log = lambda msg: None

            tip_moved, consecutive_fail = daemon._build_sha_once("abc123", consecutive_fail=0)
        finally:
            (
                daemon.checkout,
                daemon.run_full_build,
                daemon.fix_attempts_for,
                daemon.record_fix_attempt,
                daemon.codex_fix,
                daemon.write_last_built,
                daemon.log,
            ) = originals

        self.assertFalse(tip_moved)
        self.assertEqual(consecutive_fail, 1)
        self.assertEqual([event for event in events if event[0] == "build"], [("build", "main"), *[("build", target) for target in CONCRETE_TARGETS]])
        self.assertIn(("record", "abc123:concrete_instances_completion"), events)
        self.assertIn(("fix", "abc123:concrete_instances_completion:broken concrete:2"), events)
        self.assertIn(("write_last", "abc123"), events)

    def test_build_sha_once_leaves_last_built_when_fix_advances_tip(self) -> None:
        events: list[tuple[str, str]] = []

        originals = (
            daemon.checkout,
            daemon.run_full_build,
            daemon.fix_attempts_for,
            daemon.record_fix_attempt,
            daemon.codex_fix,
            daemon.write_last_built,
            daemon.log,
        )
        try:
            daemon.checkout = lambda sha: True
            daemon.run_full_build = lambda target: (False, "broken", 1.0)
            daemon.fix_attempts_for = lambda sha, target: 0
            daemon.record_fix_attempt = lambda sha, target: events.append(("record", f"{sha}:{target}"))
            daemon.codex_fix = lambda sha, target, tail, elapsed: True
            daemon.write_last_built = lambda sha: events.append(("write_last", sha))
            daemon.log = lambda msg: None

            tip_moved, consecutive_fail = daemon._build_sha_once("def456", consecutive_fail=0)
        finally:
            (
                daemon.checkout,
                daemon.run_full_build,
                daemon.fix_attempts_for,
                daemon.record_fix_attempt,
                daemon.codex_fix,
                daemon.write_last_built,
                daemon.log,
            ) = originals

        self.assertTrue(tip_moved)
        self.assertEqual(consecutive_fail, 1)
        self.assertIn(("record", "def456:main"), events)
        self.assertNotIn(("write_last", "def456"), events)


if __name__ == "__main__":
    unittest.main()

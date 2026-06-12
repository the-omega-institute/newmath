#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import subprocess
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace


REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT_PATH = REPO_ROOT / "papers" / "bedc" / "scripts" / "codex_revise.py"
TOOLS_PATH = REPO_ROOT / "tools"
if str(TOOLS_PATH) not in sys.path:
    sys.path.insert(0, str(TOOLS_PATH))


def load_codex_revise():
    spec = importlib.util.spec_from_file_location(
        "codex_revise_push_retry_under_test", SCRIPT_PATH
    )
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


cr = load_codex_revise()


def _cp(cmd=None, returncode: int = 0, stdout: str = "", stderr: str = ""):
    return subprocess.CompletedProcess(cmd or [], returncode, stdout, stderr)


class _NullContext:
    def __enter__(self):
        return None

    def __exit__(self, *_args):
        return False


class PushNotAncestorRetryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.wt = cr.WorktreeInfo(
            path=Path("/tmp/paper-push-retry"),
            branch="paper-worker",
            round_number=71,
            base_sha="a" * 40,
        )
        self.old_sync = cr._sync_local_with_origin
        self.old_run_cmd = cr.run_cmd
        self.old_ff = cr._ff_local_branch_to
        self.old_sleep = cr.time.sleep
        self.old_drift = cr.run_drift_audit
        self.old_record = cr.record_deferred_pdf_build
        self.old_codex_resolve = cr._codex_resolve_conflicts
        self.old_post_rebase_audit = cr._codex_resolve_post_rebase_audit
        self.old_lock_module = sys.modules.get("repo_push_lock")
        self.lock_marker = object()
        if "repo_push_lock" not in sys.modules:
            self.old_lock_module = self.lock_marker
        sys.modules["repo_push_lock"] = SimpleNamespace(
            acquire_push_lock=lambda *_a, **_k: _NullContext()
        )
        cr._sync_local_with_origin = lambda **_kwargs: True
        cr.time.sleep = lambda _seconds: None
        cr.run_drift_audit = lambda _wt: (True, "ok")
        cr.record_deferred_pdf_build = lambda *_a, **_k: None
        cr._codex_resolve_conflicts = lambda *_a, **_k: True
        cr._codex_resolve_post_rebase_audit = lambda *_a, **_k: True

    def tearDown(self) -> None:
        cr._sync_local_with_origin = self.old_sync
        cr.run_cmd = self.old_run_cmd
        cr._ff_local_branch_to = self.old_ff
        cr.time.sleep = self.old_sleep
        cr.run_drift_audit = self.old_drift
        cr.record_deferred_pdf_build = self.old_record
        cr._codex_resolve_conflicts = self.old_codex_resolve
        cr._codex_resolve_post_rebase_audit = self.old_post_rebase_audit
        if self.old_lock_module is self.lock_marker:
            sys.modules.pop("repo_push_lock", None)
        else:
            sys.modules["repo_push_lock"] = self.old_lock_module

    def _install_run_cmd(
        self,
        *,
        tips: list[str] | None = None,
        base_sequence: list[str] | None = None,
        origin_base_sequence: list[str] | None = None,
        merge_returncodes: list[int] | None = None,
        unmerged_outputs: list[str] | None = None,
    ):
        calls: list[list[str]] = []
        tip_values = list(tips or ["c" * 40])
        base_values = list(base_sequence or ["b" * 40])
        origin_base_values = list(origin_base_sequence or ["b" * 40])
        merge_results = list(merge_returncodes or [])
        unmerged_values = list(unmerged_outputs or ["conflicted.tex\n"])

        def fake_run_cmd(cmd, *, cwd=None, timeout=120, check=False):
            calls.append(list(cmd))
            if cmd == ["git", "merge", "--no-ff", "--no-edit", cr.BASE_BRANCH]:
                if merge_results:
                    rc = merge_results.pop(0)
                    return _cp(
                        cmd,
                        returncode=rc,
                        stderr="Your local changes would be overwritten by merge." if rc else "",
                    )
                return _cp(cmd)
            if cmd == ["git", "diff", "--name-only", "--diff-filter=U"]:
                value = (
                    unmerged_values.pop(0)
                    if len(unmerged_values) > 1
                    else unmerged_values[0]
                )
                return _cp(cmd, stdout=value)
            if cmd == ["git", "stash", "--include-untracked"]:
                return _cp(cmd)
            if cmd[:3] == ["git", "log", "--oneline"]:
                return _cp(cmd, stdout="abc123 P71: worker commit\n")
            if cmd == ["git", "rev-parse", cr.BASE_BRANCH]:
                value = base_values.pop(0) if len(base_values) > 1 else base_values[0]
                return _cp(cmd, stdout=value + "\n")
            if cmd == ["git", "rev-parse", f"origin/{cr.BASE_BRANCH}"]:
                value = (
                    origin_base_values.pop(0)
                    if len(origin_base_values) > 1
                    else origin_base_values[0]
                )
                return _cp(cmd, stdout=value + "\n")
            if cmd == ["git", "rev-parse", "HEAD"]:
                tip = tip_values.pop(0) if len(tip_values) > 1 else tip_values[0]
                return _cp(cmd, stdout=tip + "\n")
            if cmd[:2] == ["git", "fetch"]:
                return _cp(cmd)
            if cmd[:3] == ["git", "merge-base", "--is-ancestor"]:
                return _cp(cmd)
            if cmd[:3] == ["git", "push", "origin"]:
                return _cp(cmd)
            return _cp(cmd)

        cr.run_cmd = fake_run_cmd
        return calls

    def test_ff_not_ancestor_retries_after_merging_local_base(self):
        ff_calls: list[str] = []

        def fake_ff(tip: str):
            ff_calls.append(tip)
            if len(ff_calls) == 1:
                return False, "skipped-not-ancestor"
            return True, ""

        cr._ff_local_branch_to = fake_ff
        calls = self._install_run_cmd(
            tips=["c" * 40, "d" * 40],
            base_sequence=["b" * 40],
            origin_base_sequence=["b" * 40],
        )

        with self.assertLogs("codex-revise", level="INFO") as logs:
            merged = cr.merge_worktree_to_base(self.wt)

        self.assertTrue(merged)
        self.assertEqual(ff_calls, ["c" * 40, "d" * 40])
        merge_count = sum(
            cmd == ["git", "merge", "--no-ff", "--no-edit", cr.BASE_BRANCH]
            for cmd in calls
        )
        self.assertEqual(merge_count, 2)
        self.assertTrue(
            any("retry merging current local" in line for line in logs.output)
        )
        self.assertTrue(any(cmd[:3] == ["git", "push", "origin"] for cmd in calls))

    def test_static_origin_dirty_ff_failure_does_not_remerge(self):
        cr._ff_local_branch_to = lambda _tip: (False, "skipped-dirty")
        calls = self._install_run_cmd(
            tips=["c" * 40],
            base_sequence=["b" * 40],
            origin_base_sequence=["b" * 40],
        )

        merged = cr.merge_worktree_to_base(self.wt)

        self.assertFalse(merged)
        merge_count = sum(
            cmd == ["git", "merge", "--no-ff", "--no-edit", cr.BASE_BRANCH]
            for cmd in calls
        )
        self.assertEqual(merge_count, 1)
        self.assertFalse(any(cmd[:3] == ["git", "push", "origin"] for cmd in calls))

    def test_retry_reason_resets_after_followup_attempt_succeeds(self):
        ff_calls: list[str] = []

        def fake_ff(tip: str):
            ff_calls.append(tip)
            if len(ff_calls) == 1:
                return False, "skipped-not-ancestor"
            return True, ""

        cr._ff_local_branch_to = fake_ff
        calls = self._install_run_cmd(
            tips=["c" * 40, "d" * 40],
            base_sequence=["b" * 40],
            origin_base_sequence=["b" * 40],
        )

        merged = cr.merge_worktree_to_base(self.wt)

        self.assertTrue(merged)
        self.assertEqual(len(ff_calls), 2)
        merge_count = sum(
            cmd == ["git", "merge", "--no-ff", "--no-edit", cr.BASE_BRANCH]
            for cmd in calls
        )
        self.assertEqual(merge_count, 2)
        self.assertTrue(any(cmd[:3] == ["git", "push", "origin"] for cmd in calls))

    def test_retry_merge_dirty_blocked_stashes_and_retries_without_codex(self):
        ff_calls: list[str] = []
        codex_calls: list[str] = []

        def fake_ff(tip: str):
            ff_calls.append(tip)
            if len(ff_calls) == 1:
                return False, "skipped-not-ancestor"
            return True, ""

        cr._ff_local_branch_to = fake_ff
        cr._codex_resolve_conflicts = lambda *_a, **_k: codex_calls.append("codex") or True
        calls = self._install_run_cmd(
            tips=["c" * 40, "d" * 40],
            base_sequence=["b" * 40],
            origin_base_sequence=["b" * 40],
            merge_returncodes=[0, 1, 0],
            unmerged_outputs=[""],
        )

        merged = cr.merge_worktree_to_base(self.wt)

        self.assertTrue(merged)
        self.assertEqual(codex_calls, [])
        merge_indexes = [
            i for i, cmd in enumerate(calls)
            if cmd == ["git", "merge", "--no-ff", "--no-edit", cr.BASE_BRANCH]
        ]
        stash_indexes = [
            i for i, cmd in enumerate(calls)
            if cmd == ["git", "stash", "--include-untracked"]
        ]
        self.assertEqual(len(merge_indexes), 3)
        self.assertEqual(len(stash_indexes), 1)
        self.assertLess(merge_indexes[1], stash_indexes[0])
        self.assertLess(stash_indexes[0], merge_indexes[2])
        self.assertTrue(any(cmd[:3] == ["git", "push", "origin"] for cmd in calls))

    def test_retry_merge_true_conflict_invokes_codex_without_stash(self):
        ff_calls: list[str] = []
        codex_calls: list[str] = []

        def fake_ff(tip: str):
            ff_calls.append(tip)
            if len(ff_calls) == 1:
                return False, "skipped-not-ancestor"
            return True, ""

        cr._ff_local_branch_to = fake_ff
        cr._codex_resolve_conflicts = lambda *_a, **_k: codex_calls.append("codex") or True
        calls = self._install_run_cmd(
            tips=["c" * 40, "d" * 40],
            base_sequence=["b" * 40],
            origin_base_sequence=["b" * 40],
            merge_returncodes=[0, 1],
            unmerged_outputs=["parts/conflicted.tex\n"],
        )

        merged = cr.merge_worktree_to_base(self.wt)

        self.assertTrue(merged)
        self.assertEqual(codex_calls, ["codex"])
        self.assertFalse(any(cmd == ["git", "stash", "--include-untracked"] for cmd in calls))
        merge_count = sum(
            cmd == ["git", "merge", "--no-ff", "--no-edit", cr.BASE_BRANCH]
            for cmd in calls
        )
        self.assertEqual(merge_count, 2)


if __name__ == "__main__":
    unittest.main()

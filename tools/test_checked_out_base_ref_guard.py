#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import subprocess
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT / "tools") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "tools"))


def _load_module(name: str, rel_path: str):
    path = REPO_ROOT / rel_path
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {rel_path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


MODULES = [
    _load_module("checked_out_guard_codex_formalize", "lean4/scripts/codex_formalize.py"),
    _load_module("checked_out_guard_codex_revise", "papers/bedc/scripts/codex_revise.py"),
]


def _cp(cmd, returncode=0, stdout="", stderr=""):
    return subprocess.CompletedProcess(cmd, returncode, stdout=stdout, stderr=stderr)


class FakeGit:
    def __init__(self, worktree_porcelain: str, status_stdout: str = "", merge_returncode: int = 0):
        self.worktree_porcelain = worktree_porcelain
        self.status_stdout = status_stdout
        self.merge_returncode = merge_returncode
        self.calls = []

    def run_cmd(self, cmd, *, cwd=None, timeout=120, check=False):
        self.calls.append((list(cmd), cwd, timeout, check))
        if cmd == ["git", "worktree", "list", "--porcelain"]:
            return _cp(cmd, stdout=self.worktree_porcelain)
        if cmd == ["git", "symbolic-ref", "--short", "-q", "HEAD"]:
            return _cp(cmd, stdout="base\n")
        if cmd == ["git", "status", "--porcelain=v1", "--untracked-files=no"]:
            return _cp(cmd, stdout=self.status_stdout)
        if cmd == ["git", "merge", "--ff-only", "origin/base"]:
            return _cp(cmd, returncode=self.merge_returncode)
        if cmd == ["git", "rev-parse", "base"]:
            return _cp(cmd, stdout="aaa\n")
        if cmd == ["git", "rev-parse", "origin/base"]:
            return _cp(cmd, stdout="bbb\n")
        if cmd == ["git", "merge-base", "--is-ancestor", "aaa", "bbb"]:
            return _cp(cmd)
        if cmd == ["git", "update-ref", "refs/heads/base", "bbb", "aaa"]:
            return _cp(cmd)
        raise AssertionError(f"unexpected git command: {cmd!r}")

    def commands(self):
        return [cmd for cmd, _cwd, _timeout, _check in self.calls]


class CheckedOutBaseRefGuardTests(unittest.TestCase):
    def _with_fake_git(self, module, fake):
        old_run_cmd = module.run_cmd
        old_repo_root = module.REPO_ROOT
        try:
            module.run_cmd = fake.run_cmd
            module.REPO_ROOT = Path("/repo")
            return module._advance_local_base_ref("base", "origin/base")
        finally:
            module.run_cmd = old_run_cmd
            module.REPO_ROOT = old_repo_root

    def test_base_not_checked_out_uses_ref_only_fast_forward(self):
        for module in MODULES:
            with self.subTest(module=module.__name__):
                fake = FakeGit("worktree /repo\nHEAD aaa\n\n")
                outcome = self._with_fake_git(module, fake)

                self.assertEqual(outcome, "ref-only-ff")
                self.assertIn(["git", "update-ref", "refs/heads/base", "bbb", "aaa"], fake.commands())
                self.assertNotIn(["git", "merge", "--ff-only", "origin/base"], fake.commands())

    def test_base_checked_out_clean_uses_worktree_merge(self):
        for module in MODULES:
            with self.subTest(module=module.__name__):
                fake = FakeGit("worktree /repo\nHEAD aaa\nbranch refs/heads/base\n\n")
                outcome = self._with_fake_git(module, fake)

                self.assertEqual(outcome, "ff-merged")
                self.assertIn(["git", "merge", "--ff-only", "origin/base"], fake.commands())
                self.assertFalse(any(cmd[:2] == ["git", "update-ref"] for cmd in fake.commands()))

    def test_base_checked_out_dirty_skips_without_ref_write(self):
        for module in MODULES:
            with self.subTest(module=module.__name__):
                fake = FakeGit(
                    "worktree /repo\nHEAD aaa\nbranch refs/heads/base\n\n",
                    status_stdout="M  staged.txt\n M modified.txt\nUU conflict.txt\n",
                )
                outcome = self._with_fake_git(module, fake)

                self.assertEqual(outcome, "skipped-dirty")
                self.assertFalse(any(cmd[:2] == ["git", "update-ref"] for cmd in fake.commands()))
                self.assertNotIn(["git", "merge", "--ff-only", "origin/base"], fake.commands())

    def test_outcome_sets_are_mirrored(self):
        outcome_sets = [module.BASE_REF_ADVANCE_OUTCOMES for module in MODULES]
        self.assertEqual(outcome_sets[0], outcome_sets[1])


if __name__ == "__main__":
    unittest.main()

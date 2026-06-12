#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import subprocess
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT_PATH = REPO_ROOT / "lean4" / "scripts" / "codex_formalize.py"
TOOLS_PATH = REPO_ROOT / "tools"
if str(TOOLS_PATH) not in sys.path:
    sys.path.insert(0, str(TOOLS_PATH))


def load_codex_formalize():
    spec = importlib.util.spec_from_file_location("codex_formalize_push_gate_under_test", SCRIPT_PATH)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


cf = load_codex_formalize()


def _cp(cmd=None, returncode: int = 0, stdout: str = "", stderr: str = ""):
    return subprocess.CompletedProcess(cmd or [], returncode, stdout, stderr)


class _NullContext:
    def __enter__(self):
        return None

    def __exit__(self, *_args):
        return False


class _FlagContext:
    def __init__(self, state: dict[str, bool], key: str):
        self.state = state
        self.key = key

    def __enter__(self):
        self.state[self.key] = True
        return None

    def __exit__(self, *_args):
        self.state[self.key] = False
        return False


class PushGateTipVerifyTests(unittest.TestCase):
    def setUp(self) -> None:
        self.wt = cf.WorktreeInfo(path=Path("/tmp/lean-push-gate"), branch="worker", round_number=7)
        self.old_sync = cf._sync_local_with_origin
        self.old_detect_dup = cf.detect_duplicate_symbols
        self.old_gates = cf.run_pre_merge_hard_gates
        self.old_audit_gate = cf.run_pre_merge_audit_gate
        self.old_phase_d = cf.run_phase_d_lints
        self.old_run_cmd = cf.run_cmd
        self.old_ff = cf._ff_local_branch_to
        self.old_sleep = cf.time.sleep
        self.old_lock_module = sys.modules.get("repo_push_lock")
        self.lock_marker = object()
        if "repo_push_lock" not in sys.modules:
            self.old_lock_module = self.lock_marker
        sys.modules["repo_push_lock"] = SimpleNamespace(
            acquire_push_lock=lambda *_a, **_k: _NullContext()
        )
        cf._sync_local_with_origin = lambda **_kwargs: True
        cf.detect_duplicate_symbols = lambda _wt: []
        cf._ff_local_branch_to = lambda _tip: (True, "")
        cf.time.sleep = lambda _seconds: None

    def tearDown(self) -> None:
        cf._sync_local_with_origin = self.old_sync
        cf.detect_duplicate_symbols = self.old_detect_dup
        cf.run_pre_merge_hard_gates = self.old_gates
        cf.run_pre_merge_audit_gate = self.old_audit_gate
        cf.run_phase_d_lints = self.old_phase_d
        cf.run_cmd = self.old_run_cmd
        cf._ff_local_branch_to = self.old_ff
        cf.time.sleep = self.old_sleep
        if self.old_lock_module is self.lock_marker:
            sys.modules.pop("repo_push_lock", None)
        else:
            sys.modules["repo_push_lock"] = self.old_lock_module

    def _install_run_cmd(
        self,
        tips: list[str] | None = None,
        lean_trees: dict[str, str] | None = None,
        check_axioms_blobs: dict[str, str] | None = None,
        base_lean_tree: str = "b" * 40,
    ):
        calls: list[list[str]] = []
        tip_values = list(tips or ["c" * 40])
        tree_values = lean_trees or {}
        check_axioms_values = check_axioms_blobs or {}

        def fake_run_cmd(cmd, *, cwd=None, timeout=120, check=False):
            calls.append(list(cmd))
            if cmd == ["git", "merge", "--no-ff", "--no-edit", cf.BASE_BRANCH]:
                return _cp(cmd)
            if cmd[:3] == ["git", "log", "--oneline"]:
                return _cp(cmd, stdout="abc123 R7: worker commit\n")
            if cmd == ["git", "rev-parse", cf.BASE_BRANCH]:
                return _cp(cmd, stdout="b" * 40 + "\n")
            if cmd == ["git", "rev-parse", f"origin/{cf.BASE_BRANCH}"]:
                return _cp(cmd, stdout="b" * 40 + "\n")
            if cmd == ["git", "rev-parse", "HEAD"]:
                tip = tip_values.pop(0) if len(tip_values) > 1 else tip_values[0]
                return _cp(cmd, stdout=tip + "\n")
            if cmd[:2] == ["git", "rev-parse"] and len(cmd) == 3 and cmd[2].endswith(":lean4"):
                ref = cmd[2][:-len(":lean4")]
                tree = base_lean_tree if ref == cf.BASE_BRANCH else tree_values.get(ref, ref if len(ref) == 40 else "t" * 40)
                return _cp(cmd, stdout=tree + "\n")
            if (
                cmd[:2] == ["git", "rev-parse"]
                and len(cmd) == 3
                and cmd[2].endswith(":tools/check-axioms.py")
            ):
                ref = cmd[2][:-len(":tools/check-axioms.py")]
                blob = check_axioms_values.get(ref, "a" * 40)
                return _cp(cmd, stdout=blob + "\n")
            if cmd[:2] == ["git", "fetch"]:
                return _cp(cmd)
            if cmd[:3] == ["git", "merge-base", "--is-ancestor"]:
                return _cp(cmd)
            if cmd[:3] == ["git", "push", "origin"]:
                return _cp(cmd)
            return _cp(cmd)

        cf.run_cmd = fake_run_cmd
        return calls

    def test_gates_passed_tip_push_does_not_repeat_gates(self):
        gate_calls: list[str] = []
        cf.run_pre_merge_hard_gates = lambda _wt: gate_calls.append("gate") or (True, None, None)
        calls = self._install_run_cmd(["c" * 40])

        merged = cf.merge_worktree_to_base(self.wt)

        self.assertTrue(merged)
        self.assertEqual(gate_calls, ["gate"])
        self.assertTrue(any(cmd[:3] == ["git", "push", "origin"] for cmd in calls))

    def test_changed_tip_runs_gates_before_push(self):
        gate_calls: list[str] = []
        cf.run_pre_merge_hard_gates = lambda _wt: gate_calls.append("gate") or (True, None, None)
        calls = self._install_run_cmd(["c" * 40, "c" * 40, "d" * 40, "d" * 40])

        merged = cf.merge_worktree_to_base(self.wt)

        self.assertTrue(merged)
        self.assertEqual(gate_calls, ["gate", "gate"])
        self.assertTrue(any(cmd[:3] == ["git", "push", "origin"] for cmd in calls))

    def test_initial_gate_changed_tip_runs_gates_before_push(self):
        gate_calls: list[str] = []
        cf.run_pre_merge_hard_gates = lambda _wt: gate_calls.append("gate") or (True, None, None)
        calls = self._install_run_cmd(["c" * 40, "d" * 40, "d" * 40])

        merged = cf.merge_worktree_to_base(self.wt)

        self.assertTrue(merged)
        self.assertEqual(gate_calls, ["gate", "gate"])
        self.assertTrue(any(cmd[:3] == ["git", "push", "origin"] for cmd in calls))

    def test_changed_tip_gate_failure_blocks_push(self):
        gate_calls: list[str] = []

        def fake_gates(_wt):
            gate_calls.append("gate")
            return (len(gate_calls) == 1, None if len(gate_calls) == 1 else "lake_build", "bad")

        cf.run_pre_merge_hard_gates = fake_gates
        calls = self._install_run_cmd(["c" * 40, "c" * 40, "d" * 40])

        merged = cf.merge_worktree_to_base(self.wt)

        self.assertFalse(merged)
        self.assertEqual(gate_calls, ["gate", "gate"])
        self.assertFalse(any(cmd[:3] == ["git", "push", "origin"] for cmd in calls))

    def test_tip_changed_during_gate_is_not_marked_verified(self):
        old_tip = "c" * 40
        new_tip = "d" * 40
        gate_calls: list[str] = []
        cf.run_pre_merge_hard_gates = lambda _wt: gate_calls.append("gate") or (True, None, None)
        self._install_run_cmd([old_tip, new_tip, new_tip])
        verified: set[str] = set()
        verified_gate_keys: set[str] = set()

        self.assertTrue(cf._ensure_push_tip_verified(self.wt, verified, verified_gate_keys))

        self.assertEqual(gate_calls, ["gate", "gate"])
        self.assertNotIn(old_tip, verified)
        self.assertEqual(verified, {new_tip})

    def test_lock_scope_tip_miss_retries_without_running_gates_in_lock(self):
        state = {"push_lock": False}
        sys.modules["repo_push_lock"] = SimpleNamespace(
            acquire_push_lock=lambda *_a, **_k: _FlagContext(state, "push_lock")
        )
        gate_calls: list[bool] = []

        def fake_gates(_wt):
            gate_calls.append(state["push_lock"])
            return True, None, None

        cf.run_pre_merge_hard_gates = fake_gates
        calls = self._install_run_cmd(["c" * 40, "c" * 40, "d" * 40, "d" * 40])

        merged = cf.merge_worktree_to_base(self.wt)

        self.assertTrue(merged)
        self.assertEqual(gate_calls, [False, False])
        self.assertTrue(any(cmd[:3] == ["git", "push", "origin"] for cmd in calls))

    def test_changed_tip_same_lean_tree_runs_cheap_gates_before_push(self):
        gate_calls: list[str] = []
        audit_calls: list[str] = []
        phase_d_calls: list[str] = []
        initial_tip = "c" * 40
        changed_tip = "d" * 40
        lean_tree = "1" * 40
        cf.run_pre_merge_hard_gates = lambda _wt: gate_calls.append("gate") or (True, None, None)
        cf.run_pre_merge_audit_gate = lambda _wt: audit_calls.append("audit") or (True, None, None)
        cf.run_phase_d_lints = lambda _wt: phase_d_calls.append("phase_d") or (True, None, None)
        calls = self._install_run_cmd(
            [initial_tip, initial_tip, changed_tip, changed_tip],
            {initial_tip: lean_tree, changed_tip: lean_tree},
        )

        merged = cf.merge_worktree_to_base(self.wt)

        self.assertTrue(merged)
        self.assertEqual(gate_calls, ["gate"])
        self.assertEqual(audit_calls, ["audit"])
        self.assertEqual(phase_d_calls, ["phase_d"])
        self.assertTrue(any(cmd[:3] == ["git", "push", "origin"] for cmd in calls))

    def test_changed_tip_changed_lean_tree_runs_full_gates_before_push(self):
        gate_calls: list[str] = []
        audit_calls: list[str] = []
        initial_tip = "c" * 40
        changed_tip = "d" * 40
        cf.run_pre_merge_hard_gates = lambda _wt: gate_calls.append("gate") or (True, None, None)
        cf.run_pre_merge_audit_gate = lambda _wt: audit_calls.append("audit") or (True, None, None)
        calls = self._install_run_cmd(
            [initial_tip, initial_tip, changed_tip, changed_tip],
            {initial_tip: "1" * 40, changed_tip: "2" * 40},
        )

        merged = cf.merge_worktree_to_base(self.wt)

        self.assertTrue(merged)
        self.assertEqual(gate_calls, ["gate", "gate"])
        self.assertEqual(audit_calls, [])
        self.assertTrue(any(cmd[:3] == ["git", "push", "origin"] for cmd in calls))

    def test_changed_tip_changed_base_lean_tree_runs_full_gates_before_push(self):
        gate_calls: list[str] = []
        audit_calls: list[str] = []
        initial_tip = "c" * 40
        changed_tip = "d" * 40
        cf.run_pre_merge_hard_gates = lambda _wt: gate_calls.append("gate") or (True, None, None)
        cf.run_pre_merge_audit_gate = lambda _wt: audit_calls.append("audit") or (True, None, None)
        self._install_run_cmd(
            [initial_tip, initial_tip],
            {initial_tip: "1" * 40},
            base_lean_tree="2" * 40,
        )
        verified = {changed_tip}
        verified_gate_keys = {"1" * 40 + ":" + "a" * 40 + ":" + "3" * 40}

        self.assertTrue(cf._ensure_push_tip_verified(self.wt, verified, verified_gate_keys))

        self.assertEqual(gate_calls, ["gate"])
        self.assertEqual(audit_calls, [])
        self.assertEqual(verified, {initial_tip, changed_tip})

    def test_changed_tip_changed_check_axioms_blob_runs_full_gates_before_push(self):
        gate_calls: list[str] = []
        audit_calls: list[str] = []
        initial_tip = "c" * 40
        changed_tip = "d" * 40
        lean_tree = "1" * 40
        cf.run_pre_merge_hard_gates = lambda _wt: gate_calls.append("gate") or (True, None, None)
        cf.run_pre_merge_audit_gate = lambda _wt: audit_calls.append("audit") or (True, None, None)
        self._install_run_cmd(
            [initial_tip, initial_tip],
            {initial_tip: lean_tree},
            {initial_tip: "2" * 40},
            base_lean_tree="3" * 40,
        )
        verified = {changed_tip}
        verified_gate_keys = {lean_tree + ":" + "a" * 40 + ":" + "3" * 40}

        self.assertTrue(cf._ensure_push_tip_verified(self.wt, verified, verified_gate_keys))

        self.assertEqual(gate_calls, ["gate"])
        self.assertEqual(audit_calls, [])
        self.assertEqual(verified, {initial_tip, changed_tip})

    def test_changed_tip_same_lean_tree_audit_failure_blocks_push(self):
        gate_calls: list[str] = []
        audit_calls: list[str] = []
        initial_tip = "c" * 40
        changed_tip = "d" * 40
        lean_tree = "1" * 40
        cf.run_pre_merge_hard_gates = lambda _wt: gate_calls.append("gate") or (True, None, None)
        cf.run_pre_merge_audit_gate = lambda _wt: audit_calls.append("audit") or (False, "audit", "bad")
        calls = self._install_run_cmd(
            [initial_tip, initial_tip, changed_tip],
            {initial_tip: lean_tree, changed_tip: lean_tree},
        )

        merged = cf.merge_worktree_to_base(self.wt)

        self.assertFalse(merged)
        self.assertEqual(gate_calls, ["gate"])
        self.assertEqual(audit_calls, ["audit"])
        self.assertFalse(any(cmd[:3] == ["git", "push", "origin"] for cmd in calls))


if __name__ == "__main__":
    unittest.main()

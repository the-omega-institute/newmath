#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace


REPO_ROOT = Path(__file__).resolve().parents[3]
PHASE_PATH = REPO_ROOT / "papers" / "bedc" / "scripts" / "phase_paper_gates.py"
REVISE_PATH = REPO_ROOT / "papers" / "bedc" / "scripts" / "codex_revise.py"
TOOLS_PATH = REPO_ROOT / "tools"
if str(TOOLS_PATH) not in sys.path:
    sys.path.insert(0, str(TOOLS_PATH))


def _load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


phase = _load_module("phase_paper_gates_under_test", PHASE_PATH)


class _NullContext:
    def __enter__(self):
        return None

    def __exit__(self, *_args):
        return False


def _cp(stdout: str = "", returncode: int = 0, stderr: str = ""):
    return subprocess.CompletedProcess([], returncode, stdout=stdout, stderr=stderr)


def _git(repo: Path, *args: str, check: bool = True) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=repo,
        capture_output=True,
        text=True,
        check=False,
    )
    if check and result.returncode != 0:
        raise AssertionError(
            f"git {' '.join(args)} failed\nstdout={result.stdout}\nstderr={result.stderr}"
        )
    return result.stdout.strip()


def _write(repo: Path, rel: str, text: str) -> None:
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _commit(repo: Path, message: str) -> str:
    _git(repo, "add", ".")
    _git(repo, "commit", "-m", message)
    return _git(repo, "rev-parse", "HEAD")


def _chapter_text(slug: str, extra: str = "") -> str:
    title = slug.replace("_", " ").title()
    return (
        f"\\chapter{{{title} NameCert}}\n"
        f"\\label{{ch:concrete-instances-{slug.replace('_', '-')}-namecert}}\n"
        "\\origin{ai}\n"
        f"\\begin{{theorem}}\\label{{thm:{slug.replace('_', '-')}-carrier}}Self.\\end{{theorem}}\n"
        f"{extra}\n"
    )


class OwnCommitGateScopeTests(unittest.TestCase):
    def setUp(self) -> None:
        phase._ADDED_LINES_CACHE.clear()
        phase._OWN_COMMITS_CACHE.clear()
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Path(self.tmp.name)
        _git(self.repo, "init")
        _git(self.repo, "config", "user.email", "bedc@example.invalid")
        _git(self.repo, "config", "user.name", "BEDC Test")
        _write(self.repo, "papers/bedc/parts/concrete_instances/0001_seed_namecert_construction.tex", "% seed\n")
        self.base = _commit(self.repo, "base")

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def _branch_from_base(self, branch: str) -> None:
        _git(self.repo, "checkout", "-B", branch, self.base)

    def test_own_orphan_chapter_reports(self):
        self._branch_from_base("worker")
        rel = "papers/bedc/parts/concrete_instances/1234_orphan_namecert_construction.tex"
        _write(self.repo, rel, _chapter_text("orphan"))
        _commit(self.repo, "worker orphan chapter")

        violations = phase.detect_orphan_new_chapter(worktree=self.repo, base_sha=self.base)

        self.assertEqual(len(violations), 1)
        self.assertIn(rel, violations[0])

    def test_origin_side_orphan_after_merge_is_not_this_round(self):
        self._branch_from_base("origin-side")
        rel = "papers/bedc/parts/concrete_instances/1235_origin_namecert_construction.tex"
        _write(self.repo, rel, _chapter_text("origin"))
        _commit(self.repo, "origin orphan chapter")

        self._branch_from_base("worker")
        _write(self.repo, "papers/bedc/parts/local_note.tex", "worker line\n")
        _commit(self.repo, "worker paper note")
        _git(self.repo, "merge", "--no-ff", "--no-edit", "origin-side")

        violations = phase.detect_orphan_new_chapter(worktree=self.repo, base_sha=self.base)

        self.assertEqual(violations, [])

    def test_own_chapter_with_sibling_cross_ref_passes(self):
        self._branch_from_base("worker")
        rel = "papers/bedc/parts/concrete_instances/1236_linked_namecert_construction.tex"
        body = _chapter_text(
            "linked",
            "\\autoref{ch:concrete-instances-seed-namecert} supplies the nearby anchor.",
        )
        _write(self.repo, rel, body)
        _commit(self.repo, "worker linked chapter")

        violations = phase.detect_orphan_new_chapter(worktree=self.repo, base_sha=self.base)

        self.assertEqual(violations, [])

    def test_own_commits_follow_first_parent_only(self):
        self._branch_from_base("origin-side")
        _write(self.repo, "papers/bedc/parts/origin_line.tex", "origin-owned\n")
        origin_commit = _commit(self.repo, "origin side line")

        self._branch_from_base("worker")
        _write(self.repo, "papers/bedc/parts/worker_line.tex", "worker-owned\n")
        worker_commit = _commit(self.repo, "worker side line")
        _git(self.repo, "merge", "--no-ff", "--no-edit", "origin-side")

        own_commits = phase._own_commits(worktree=self.repo, base_sha=self.base)

        self.assertEqual(own_commits, [worker_commit])
        self.assertNotIn(origin_commit, own_commits)

    def test_added_lines_ignore_second_parent_merge_content(self):
        self._branch_from_base("origin-side")
        origin_rel = "papers/bedc/parts/origin_lines.tex"
        _write(self.repo, origin_rel, "origin-only-line\n")
        _commit(self.repo, "origin line")

        self._branch_from_base("worker")
        worker_rel = "papers/bedc/parts/worker_lines.tex"
        _write(self.repo, worker_rel, "worker-only-line\n")
        _commit(self.repo, "worker line")
        _git(self.repo, "merge", "--no-ff", "--no-edit", "origin-side")

        origin_lines = phase._added_lines_per_file(
            worktree=self.repo, base_sha=self.base, rel_path=origin_rel
        )
        worker_lines = phase._added_lines_per_file(
            worktree=self.repo, base_sha=self.base, rel_path=worker_rel
        )

        self.assertEqual(origin_lines, [])
        self.assertIn((1, "worker-only-line"), worker_lines)


class RecoveryVerifyBeforePushTests(unittest.TestCase):
    def _install_lock_module(self, cr):
        old_module = sys.modules.get("repo_push_lock")
        marker = object()
        if "repo_push_lock" not in sys.modules:
            old_module = marker
        sys.modules["repo_push_lock"] = SimpleNamespace(
            acquire_push_lock=lambda *_a, **_k: _NullContext()
        )
        return old_module, marker

    def _restore_lock_module(self, old_module, marker) -> None:
        if old_module is marker:
            sys.modules.pop("repo_push_lock", None)
        else:
            sys.modules["repo_push_lock"] = old_module

    def test_recovery_verify_failure_blocks_push(self):
        cr = _load_module("codex_revise_recovery_gate_under_test", REVISE_PATH)
        wt = cr.WorktreeInfo(path=Path("/tmp/recovery-gate"), branch="paper-worker", round_number=31, base_sha="a" * 40)
        calls: list[list[str]] = []

        def fake_run_cmd(cmd, **_kwargs):
            calls.append(list(cmd))
            if cmd[:3] == ["git", "merge", "--no-ff"]:
                return _cp()
            if cmd[:3] == ["git", "log", "--oneline"]:
                return _cp("abc1234 P31: worker commit\n")
            if cmd == ["git", "rev-parse", cr.BASE_BRANCH]:
                return _cp("b" * 40)
            if cmd == ["git", "rev-parse", f"origin/{cr.BASE_BRANCH}"]:
                return _cp("b" * 40)
            if cmd == ["git", "rev-parse", "HEAD"]:
                return _cp("c" * 40)
            if cmd[:2] == ["git", "fetch"]:
                return _cp()
            if cmd[:3] == ["git", "push", "origin"]:
                return _cp()
            return _cp()

        old_module, marker = self._install_lock_module(cr)
        old_sync = cr._sync_local_with_origin
        old_run_cmd = cr.run_cmd
        old_drift = cr.run_drift_audit
        old_verify = cr.verify_worktree_commits
        old_ff = cr._ff_local_branch_to
        verify_calls: list[tuple[object, list[str]]] = []
        ff_calls: list[object] = []
        try:
            cr._sync_local_with_origin = lambda **_kwargs: True
            cr.run_cmd = fake_run_cmd
            cr.run_drift_audit = lambda _wt: (True, "ok")
            cr.verify_worktree_commits = lambda _wt, _pre: (
                verify_calls.append((_wt, _pre)) or (False, ["abc1234 P31: worker commit"])
            )
            cr._ff_local_branch_to = lambda _tip: ff_calls.append(_tip) or (True, "")
            merged = cr.merge_worktree_to_base(wt, verify_before_push=True)
        finally:
            cr._sync_local_with_origin = old_sync
            cr.run_cmd = old_run_cmd
            cr.run_drift_audit = old_drift
            cr.verify_worktree_commits = old_verify
            cr._ff_local_branch_to = old_ff
            self._restore_lock_module(old_module, marker)

        self.assertFalse(merged)
        self.assertEqual(verify_calls, [(wt, [])])
        self.assertEqual(ff_calls, [])
        self.assertFalse(any(cmd[:3] == ["git", "push", "origin"] for cmd in calls))

    def test_recovery_loop_retries_merge_with_pre_push_verify(self):
        cr = _load_module("codex_revise_recovery_loop_under_test", REVISE_PATH)
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            queue = root / "queue"
            dead = queue / "dead"
            wt_path = root / "worktree"
            wt_path.mkdir(parents=True)
            ticket = {
                "worktree": str(wt_path),
                "branch": "paper-worker",
                "round_number": 33,
                "base_sha": "a" * 40,
            }
            queue.mkdir(parents=True)
            ticket_path = queue / cr.recovery_ticket_name(
                "paper-revise", None, ticket["round_number"], 12345
            )
            ticket_path.write_text(json.dumps(ticket), encoding="utf-8")
            merge_calls: list[tuple[object, dict[str, object]]] = []

            def fake_merge(wt, **kwargs):
                merge_calls.append((wt, dict(kwargs)))
                cr._recovery_stop.set()
                return True

            old_queue = cr.RECOVERY_QUEUE_DIR
            old_dead = cr.RECOVERY_DEAD_DIR
            old_run_recovery = cr._run_recovery_codex
            old_merge = cr.merge_worktree_to_base
            old_force_remove = cr._force_remove_worktree
            old_run_cmd = cr.run_cmd
            try:
                cr._recovery_stop.clear()
                cr.RECOVERY_QUEUE_DIR = queue
                cr.RECOVERY_DEAD_DIR = dead
                cr._run_recovery_codex = lambda _wt, **_kwargs: True
                cr.merge_worktree_to_base = fake_merge
                cr._force_remove_worktree = lambda _path: None
                cr.run_cmd = lambda *_args, **_kwargs: _cp()

                cr._recovery_loop(poll_seconds=0.01)
            finally:
                cr._recovery_stop.clear()
                cr.RECOVERY_QUEUE_DIR = old_queue
                cr.RECOVERY_DEAD_DIR = old_dead
                cr._run_recovery_codex = old_run_recovery
                cr.merge_worktree_to_base = old_merge
                cr._force_remove_worktree = old_force_remove
                cr.run_cmd = old_run_cmd

            self.assertEqual(len(merge_calls), 1)
            merged_wt, kwargs = merge_calls[0]
            self.assertEqual(merged_wt.path, wt_path)
            self.assertEqual(merged_wt.branch, ticket["branch"])
            self.assertEqual(merged_wt.round_number, ticket["round_number"])
            self.assertIs(kwargs.get("verify_before_push"), True)

    def test_changed_tip_inside_lock_is_reverified_before_push(self):
        cr = _load_module("codex_revise_recovery_tip_reverify_under_test", REVISE_PATH)
        wt = cr.WorktreeInfo(path=Path("/tmp/recovery-tip"), branch="paper-worker", round_number=34, base_sha="a" * 40)
        tip_a = "a" * 40
        tip_b = "b" * 40
        base = "c" * 40
        calls: list[tuple[list[str], object]] = []
        wt_rev_parse_count = 0

        def fake_run_cmd(cmd, **kwargs):
            nonlocal wt_rev_parse_count
            cmd = list(cmd)
            cwd = kwargs.get("cwd")
            calls.append((cmd, cwd))
            if cmd[:3] == ["git", "merge", "--no-ff"]:
                return _cp()
            if cmd[:3] == ["git", "log", "--oneline"]:
                return _cp("abc1234 P34: worker commit\n")
            if cmd == ["git", "rev-parse", cr.BASE_BRANCH]:
                return _cp(base)
            if cmd == ["git", "rev-parse", f"origin/{cr.BASE_BRANCH}"]:
                return _cp(base)
            if cmd == ["git", "rev-parse", "HEAD"] and cwd == wt.path:
                wt_rev_parse_count += 1
                return _cp(tip_a if wt_rev_parse_count == 1 else tip_b)
            if cmd[:2] == ["git", "fetch"]:
                return _cp()
            if cmd[:4] == ["git", "merge-base", "--is-ancestor", tip_b]:
                return _cp()
            if cmd[:3] == ["git", "push", "origin"]:
                return _cp()
            return _cp()

        old_module, marker = self._install_lock_module(cr)
        old_sync = cr._sync_local_with_origin
        old_run_cmd = cr.run_cmd
        old_drift = cr.run_drift_audit
        old_verify = cr.verify_worktree_commits
        old_ff = cr._ff_local_branch_to
        old_record = cr.record_deferred_pdf_build
        old_sleep = cr.time.sleep
        verify_seen_tips: list[str] = []
        ff_calls: list[str] = []
        try:
            cr._sync_local_with_origin = lambda **_kwargs: True
            cr.run_cmd = fake_run_cmd
            cr.run_drift_audit = lambda _wt: (True, "ok")

            def fake_verify(_wt, _pre):
                verify_seen_tips.append(tip_a if not verify_seen_tips else tip_b)
                return True, []

            cr.verify_worktree_commits = fake_verify
            cr._ff_local_branch_to = lambda tip: ff_calls.append(tip) or (True, "")
            cr.record_deferred_pdf_build = lambda *_args, **_kwargs: None
            cr.time.sleep = lambda _seconds: None

            merged = cr.merge_worktree_to_base(wt, verify_before_push=True)
        finally:
            cr._sync_local_with_origin = old_sync
            cr.run_cmd = old_run_cmd
            cr.run_drift_audit = old_drift
            cr.verify_worktree_commits = old_verify
            cr._ff_local_branch_to = old_ff
            cr.record_deferred_pdf_build = old_record
            cr.time.sleep = old_sleep
            self._restore_lock_module(old_module, marker)

        self.assertTrue(merged)
        self.assertEqual(verify_seen_tips, [tip_a, tip_b])
        self.assertEqual(ff_calls, [tip_b])
        pushed = [cmd for cmd, _cwd in calls if cmd[:3] == ["git", "push", "origin"]]
        self.assertEqual(len(pushed), 1)

    def test_default_merge_path_does_not_run_pre_push_verify(self):
        cr = _load_module("codex_revise_default_merge_under_test", REVISE_PATH)
        wt = cr.WorktreeInfo(path=Path("/tmp/recovery-gate"), branch="paper-worker", round_number=32, base_sha="a" * 40)
        calls: list[list[str]] = []

        def fake_run_cmd(cmd, **_kwargs):
            calls.append(list(cmd))
            if cmd[:3] == ["git", "merge", "--no-ff"]:
                return _cp()
            if cmd[:3] == ["git", "log", "--oneline"]:
                return _cp("abc1234 P32: worker commit\n")
            if cmd == ["git", "rev-parse", cr.BASE_BRANCH]:
                return _cp("b" * 40)
            if cmd == ["git", "rev-parse", f"origin/{cr.BASE_BRANCH}"]:
                return _cp("b" * 40)
            if cmd == ["git", "rev-parse", "HEAD"]:
                return _cp("c" * 40)
            if cmd[:2] == ["git", "fetch"]:
                return _cp()
            if cmd[:3] == ["git", "push", "origin"]:
                return _cp()
            if cmd[:4] == ["git", "merge-base", "--is-ancestor", "c" * 40]:
                return _cp()
            return _cp()

        old_module, marker = self._install_lock_module(cr)
        old_sync = cr._sync_local_with_origin
        old_run_cmd = cr.run_cmd
        old_drift = cr.run_drift_audit
        old_verify = cr.verify_worktree_commits
        old_ff = cr._ff_local_branch_to
        old_record = cr.record_deferred_pdf_build
        verify_calls: list[tuple[object, list[str]]] = []
        try:
            cr._sync_local_with_origin = lambda **_kwargs: True
            cr.run_cmd = fake_run_cmd
            cr.run_drift_audit = lambda _wt: (True, "ok")
            cr.verify_worktree_commits = lambda _wt, _pre: (
                verify_calls.append((_wt, _pre)) or (False, [])
            )
            cr._ff_local_branch_to = lambda _tip: (True, "")
            cr.record_deferred_pdf_build = lambda *_args, **_kwargs: None
            merged = cr.merge_worktree_to_base(wt)
        finally:
            cr._sync_local_with_origin = old_sync
            cr.run_cmd = old_run_cmd
            cr.run_drift_audit = old_drift
            cr.verify_worktree_commits = old_verify
            cr._ff_local_branch_to = old_ff
            cr.record_deferred_pdf_build = old_record
            self._restore_lock_module(old_module, marker)

        self.assertTrue(merged)
        self.assertEqual(verify_calls, [])
        self.assertTrue(any(cmd[:3] == ["git", "push", "origin"] for cmd in calls))


if __name__ == "__main__":
    unittest.main()

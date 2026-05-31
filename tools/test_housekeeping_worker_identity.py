from __future__ import annotations

import importlib.util
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

TOOLS_DIR = Path(__file__).resolve().parent
ROOT = TOOLS_DIR.parent
if str(TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(TOOLS_DIR))

import auto_tune_concurrency
import stash_gc


def load_critical_path():
    path = ROOT / "lean4" / "scripts" / "critical_path.py"
    spec = importlib.util.spec_from_file_location("critical_path_under_test", path)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


class HousekeepingWorkerIdentityTests(unittest.TestCase):
    def test_auto_tune_cleanup_handles_semantic_and_legacy_worktrees(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            worktrees = root / ".worktrees"
            for name in (
                "formalize_sheaf_gap_wabc1234",
                "paper_revise_cauchy_gap_wxyz9876",
                "round_R42",
                "paper_P17",
                "unrelated_checkout",
            ):
                (worktrees / name).mkdir(parents=True)
            lean_log = root / "lean.log"
            paper_log = root / "paper.log"
            calls: list[tuple[str, ...]] = []

            def fake_run(args, **kwargs):
                calls.append(tuple(str(arg) for arg in args))
                if args[:3] == ["ps", "-axo", "command"]:
                    return subprocess.CompletedProcess(args, 0, "", "")
                return subprocess.CompletedProcess(args, 0, "", "")

            with patch.object(auto_tune_concurrency, "REPO_ROOT", root), \
                 patch.object(auto_tune_concurrency, "WORKTREES_DIR", worktrees), \
                 patch.object(auto_tune_concurrency, "LEAN_LOG", lean_log), \
                 patch.object(auto_tune_concurrency, "PAPER_LOG", paper_log), \
                 patch.object(auto_tune_concurrency.subprocess, "run", side_effect=fake_run):
                stats = auto_tune_concurrency.cleanup_stale_worktrees(stale_minutes=150, dry_run=False)

            self.assertEqual(stats, {"stale_removed": 4, "stale_inspected": 4})
            branch_deletes = [call[-1] for call in calls if call[:3] == ("git", "branch", "-D")]
            self.assertCountEqual(
                branch_deletes,
                [
                    "formalize-sheaf-gap-wabc1234",
                    "paper-revise-cauchy-gap-wxyz9876",
                    "codex-R42",
                    "paper-P17",
                ],
            )
            removed_paths = [Path(call[-1]).name for call in calls if call[:4] == ("git", "worktree", "remove", "--force")]
            self.assertCountEqual(
                removed_paths,
                [
                    "formalize_sheaf_gap_wabc1234",
                    "paper_revise_cauchy_gap_wxyz9876",
                    "round_R42",
                    "paper_P17",
                ],
            )

    def test_stash_gc_classifies_semantic_and_legacy_worker_stashes(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            worktrees = root / ".worktrees"
            (worktrees / "formalize_sheaf_gap_wabc1234").mkdir(parents=True)
            (worktrees / "round_R42").mkdir(parents=True)
            paths = [stash_gc.PathEntry(status="M", paths=["lean4/BEDC/Derived/FooUp.lean"])]

            def fake_paths(_oid: str):
                return paths, set(), None

            rows = [
                ("stash@{0}", "a" * 40, "2026-05-01 00:00:00 +0000", "On formalize-sheaf-gap-wabc1234: worker stash"),
                ("stash@{1}", "b" * 40, "2026-05-01 00:00:00 +0000", "On paper-revise-cauchy-gap-wxyz9876: worker stash"),
                ("stash@{2}", "c" * 40, "2026-05-01 00:00:00 +0000", "On codex-R42: worker stash"),
                ("stash@{3}", "d" * 40, "2026-05-01 00:00:00 +0000", "On paper-P17: worker stash"),
            ]

            with patch.object(stash_gc, "stash_paths", side_effect=fake_paths):
                entries = [stash_gc.classify(root, row) for row in rows]

            by_selector = {entry.selector: entry for entry in entries}
            self.assertEqual(by_selector["stash@{0}"].category, "worker")
            self.assertTrue(by_selector["stash@{0}"].worktree_exists)
            self.assertFalse(by_selector["stash@{0}"].auto_gc_candidate)
            self.assertEqual(by_selector["stash@{1}"].category, "worker")
            self.assertFalse(by_selector["stash@{1}"].worktree_exists)
            self.assertTrue(by_selector["stash@{1}"].auto_gc_candidate)
            self.assertEqual(by_selector["stash@{2}"].category, "worker")
            self.assertTrue(by_selector["stash@{2}"].worktree_exists)
            self.assertFalse(by_selector["stash@{2}"].auto_gc_candidate)
            self.assertEqual(by_selector["stash@{3}"].category, "worker")
            self.assertFalse(by_selector["stash@{3}"].worktree_exists)
            self.assertTrue(by_selector["stash@{3}"].auto_gc_candidate)

    def test_critical_path_inflight_scans_semantic_and_legacy_worktrees(self) -> None:
        critical_path = load_critical_path()
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            worktrees = root / ".worktrees"
            names = (
                "formalize_metric_gap_wabc1234",
                "paper_revise_cauchy_gap_wxyz9876",
                "round_R42",
                "paper_P17",
                "unrelated_checkout",
            )
            for name in names:
                (worktrees / name).mkdir(parents=True)
            status_by_cwd = {
                str(worktrees / "paper_revise_cauchy_gap_wxyz9876"): " M papers/bedc/parts/concrete_instances/12_cauchy_namecert_construction.tex\n",
                str(worktrees / "paper_P17"): "?? papers/bedc/parts/concrete_instances/sheaf/namecert_construction.tex\n",
                str(worktrees / "formalize_metric_gap_wabc1234"): " M lean4/BEDC/Derived/MetricUp.lean\n M papers/bedc/parts/concrete_instances/13_banach_namecert_construction.tex\n",
                str(worktrees / "round_R42"): " M lean4/BEDC/Derived/Foo/SheafUp/Lemma.lean\n",
            }
            called_cwds: list[str] = []

            def fake_run(args, **kwargs):
                cwd = str(kwargs["cwd"])
                called_cwds.append(cwd)
                return subprocess.CompletedProcess(args, 0, status_by_cwd.get(cwd, ""), "")

            with patch.object(critical_path, "ROOT", root), \
                 patch.object(critical_path.subprocess, "run", side_effect=fake_run):
                paper = critical_path._inflight_paper_attack_chapters()
                lean = critical_path._inflight_lean_attack_chapters()

            self.assertEqual(paper, {"cauchy", "sheaf"})
            self.assertEqual(lean, {"metric", "banach", "sheaf"})
            self.assertEqual(called_cwds.count(str(worktrees / "paper_revise_cauchy_gap_wxyz9876")), 1)
            self.assertEqual(called_cwds.count(str(worktrees / "paper_P17")), 1)
            self.assertEqual(called_cwds.count(str(worktrees / "formalize_metric_gap_wabc1234")), 1)
            self.assertEqual(called_cwds.count(str(worktrees / "round_R42")), 1)
            self.assertNotIn(str(worktrees / "unrelated_checkout"), called_cwds)


if __name__ == "__main__":
    unittest.main()

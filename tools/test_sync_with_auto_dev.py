from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path
from unittest import mock


REPO_ROOT = Path(__file__).resolve().parents[1]


class Result:
    def __init__(self, returncode: int = 0, stdout: str = "", stderr: str = "") -> None:
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


class NullContext:
    def __enter__(self):
        return None

    def __exit__(self, exc_type, exc, tb):
        return False


def _null_context(*args, **kwargs):
    return NullContext()


def load_sync_module():
    path = REPO_ROOT / "tools" / "sync_with_auto_dev.py"
    spec = importlib.util.spec_from_file_location("sync_with_auto_dev_test_module", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load sync_with_auto_dev.py")
    module = importlib.util.module_from_spec(spec)
    old_module = sys.modules.pop(spec.name, None)
    tools_path = str(REPO_ROOT / "tools")
    added_tools_path = False
    try:
        if tools_path not in sys.path:
            sys.path.insert(0, tools_path)
            added_tools_path = True
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        return module
    finally:
        if added_tools_path:
            sys.path.remove(tools_path)
        if old_module is not None:
            sys.modules[spec.name] = old_module
        else:
            sys.modules.pop(spec.name, None)


class SyncDevCatchupPrTests(unittest.TestCase):
    def test_closes_other_open_sync_prs_before_moving_active_pr(self) -> None:
        module = load_sync_module()
        closed_numbers: list[int] = []
        deleted_branches: list[str] = []

        active = {
            "number": 21,
            "headRefName": module.PR_BRANCH,
            "headRefOid": "active-head",
            "mergeable": "UNKNOWN",
            "statusCheckRollup": [{"conclusion": "FAILURE"}],
            "createdAt": "2026-06-03T00:00:00Z",
        }
        old_failed = {
            "number": 17,
            "headRefName": "auto-dev-sync-20260603-0501",
            "headRefOid": "old-head",
            "mergeable": "UNKNOWN",
            "statusCheckRollup": [{"conclusion": "FAILURE"}],
            "createdAt": "2026-06-03T00:00:00Z",
        }

        class Result:
            def __init__(self, returncode: int = 0, stdout: str = "") -> None:
                self.returncode = returncode
                self.stdout = stdout
                self.stderr = ""

        def fake_run(cmd, **kwargs):
            if cmd[:3] == ["git", "rev-parse", "origin/auto-dev"]:
                return Result(stdout="auto-dev-head\n")
            if cmd[:3] == ["gh", "pr", "close"]:
                closed_numbers.append(int(cmd[3]))
                return Result()
            if cmd[:4] == ["git", "push", "origin", "--delete"]:
                deleted_branches.append(cmd[4])
                return Result()
            if cmd[:2] == ["git", "fetch"]:
                return Result()
            if cmd[:4] == ["git", "push", "origin", "--force"]:
                return Result()
            raise AssertionError(f"unexpected command: {cmd}")

        with mock.patch.object(module, "_gh_available", return_value=True):
            with mock.patch.object(module, "has_remote_branch", return_value=True):
                with mock.patch.object(module, "_open_sync_prs", return_value=[active, old_failed]):
                    with mock.patch.object(module, "_auto_dev_advanced_past", return_value=3):
                        with mock.patch.object(module, "run", side_effect=fake_run):
                            module.sync_dev_catchup_pr()

        self.assertEqual(closed_numbers, [17])
        self.assertEqual(deleted_branches, ["auto-dev-sync-20260603-0501"])


class RollupPrTests(unittest.TestCase):
    def rollup_pr(self, mergeable: str, conclusions: list[str]) -> dict:
        return {
            "number": 1192,
            "mergeable": mergeable,
            "statusCheckRollup": [{"conclusion": conclusion} for conclusion in conclusions],
            "createdAt": "2026-06-03T00:00:00Z",
        }

    def test_rollup_pr_action_waits_on_pending_candidate(self) -> None:
        module = load_sync_module()
        pr = self.rollup_pr("MERGEABLE", ["SUCCESS", "IN_PROGRESS"])

        self.assertEqual(module._rollup_pr_action(pr, 1.0), "wait")

    def test_rollup_pr_action_waits_when_checks_green_but_mergeable_unknown(self) -> None:
        module = load_sync_module()
        pr = self.rollup_pr("UNKNOWN", ["SUCCESS", "SUCCESS"])

        self.assertEqual(module._rollup_pr_action(pr, 1.0), "wait")

    def test_rollup_pr_action_merges_green_mergeable_pr(self) -> None:
        module = load_sync_module()
        pr = self.rollup_pr("MERGEABLE", ["SUCCESS", "SUCCESS"])

        self.assertEqual(module._rollup_pr_action(pr, 1.0), "merge")

    def test_rollup_pr_action_rebuilds_conflicting_pr(self) -> None:
        module = load_sync_module()
        pr = self.rollup_pr("CONFLICTING", ["SUCCESS", "SUCCESS"])

        self.assertEqual(module._rollup_pr_action(pr, 1.0), "rebuild")

    def test_rollup_pr_action_waits_on_cancelled_check(self) -> None:
        module = load_sync_module()
        pr = self.rollup_pr("MERGEABLE", ["SUCCESS", "CANCELLED"])

        self.assertFalse(module._pr_has_failed_check(pr))
        self.assertEqual(module._rollup_pr_action(pr, 1.0), "wait")

    def test_rollup_pr_action_rebuilds_failed_check(self) -> None:
        module = load_sync_module()
        pr = self.rollup_pr("MERGEABLE", ["SUCCESS", "FAILURE"])

        self.assertEqual(module._rollup_pr_action(pr, 1.0), "rebuild")

    def test_rollup_pr_action_rebuilds_old_non_green_pr(self) -> None:
        module = load_sync_module()
        module.PR_REPLACE_OPEN_HOURS = 6.0
        pr = self.rollup_pr("MERGEABLE", ["SUCCESS", "IN_PROGRESS"])

        self.assertEqual(module._rollup_pr_action(pr, 7.0), "rebuild")

    def test_rollup_pr_action_creates_when_no_pr_exists(self) -> None:
        module = load_sync_module()

        self.assertEqual(module._rollup_pr_action(None, None), "create")

    def test_source_in_target_is_noop_without_pr_creation(self) -> None:
        module = load_sync_module()
        target_sha = "12837a0ec5abcdef"

        with mock.patch.object(module, "git", return_value=Result()) as git:
            with mock.patch.object(module, "has_remote_branch", return_value=True):
                with mock.patch.object(module, "_origin_sha", return_value=target_sha):
                    with mock.patch.object(module, "_merge_base_contains", return_value=True):
                        with mock.patch.object(module, "_delete_managed_rollup_branch_if_no_pr") as cleanup:
                            with mock.patch.object(module, "_open_rollup_pr") as open_pr:
                                with mock.patch.object(module, "_build_rollup_candidate") as build:
                                    ok = module.sync_rollup_pr(
                                        "codex-auto-dev",
                                        "dev",
                                        "rollup-codex-auto-dev-to-dev",
                                        no_push=False,
                                    )

        self.assertTrue(ok)
        git.assert_called_once_with("fetch", "origin", "--prune")
        cleanup.assert_called_once_with(
            "rollup-codex-auto-dev-to-dev",
            "dev",
        )
        open_pr.assert_not_called()
        build.assert_not_called()

    def test_no_push_candidate_equal_to_target_is_noop(self) -> None:
        module = load_sync_module()
        target_sha = "12837a0ec5abcdef"
        candidate = module.RollupCandidate(
            Path("/tmp/bedc-rollup-test-worktree"),
            Path("/tmp/bedc-rollup-test-root"),
            "rollup-scratch-test",
            target_sha,
        )

        with mock.patch.object(module, "git", return_value=Result()):
            with mock.patch.object(module, "has_remote_branch", return_value=True):
                with mock.patch.object(module, "_origin_sha", return_value=target_sha):
                    with mock.patch.object(module, "_merge_base_contains", return_value=False):
                        with mock.patch.object(module, "_build_rollup_candidate", return_value=candidate):
                            with mock.patch.object(module, "_remove_rollup_worktree") as remove:
                                ok = module.sync_rollup_pr(
                                    "codex-auto-dev",
                                    "dev",
                                    "rollup-codex-auto-dev-to-dev",
                                    no_push=True,
                                )

        self.assertTrue(ok)
        remove.assert_called_once_with(candidate)

    def test_no_commits_between_pr_create_is_noop_success(self) -> None:
        module = load_sync_module()

        def fake_run(cmd, **kwargs):
            if cmd[:4] == ["gh", "pr", "create", "--base"]:
                return Result(
                    returncode=1,
                    stderr=(
                        "GraphQL: No commits between dev and "
                        "rollup-codex-auto-dev-to-dev (createPullRequest)"
                    ),
                )
            raise AssertionError(f"unexpected command: {cmd}")

        with mock.patch.object(module, "run", side_effect=fake_run):
            with mock.patch.object(module, "_delete_managed_rollup_branch_if_no_pr") as cleanup:
                ok = module._create_rollup_pr(
                    "rollup-codex-auto-dev-to-dev",
                    "codex-auto-dev",
                    "dev",
                )

        self.assertTrue(ok)
        cleanup.assert_called_once_with(
            "rollup-codex-auto-dev-to-dev",
            "dev",
        )

    def test_merge_conflict_collapses_canonical_without_codex(self) -> None:
        module = load_sync_module()
        cwd = Path("/tmp/bedc-sync-test")
        commands: list[list[str]] = []

        def fake_run(cmd, **kwargs):
            commands.append(cmd)
            if cmd[:3] == ["git", "merge", "--no-ff"]:
                return Result(returncode=1, stdout="CONFLICT\n")
            if cmd[:3] == ["git", "commit", "--no-edit"]:
                return Result()
            raise AssertionError(f"unexpected command: {cmd}")

        with mock.patch.object(module, "install_canonical_generated_merge_driver", return_value=True):
            with mock.patch.object(module, "run", side_effect=fake_run):
                with mock.patch.object(module, "conflicted_files", side_effect=[
                    ["papers/bedc-quality-lab/reports/canonical/index.json"],
                    [],
                ]):
                    with mock.patch.object(module, "collapse_canonical_generated_conflicts", return_value=True) as collapse:
                        with mock.patch.object(module, "call_codex_to_resolve") as codex:
                            with mock.patch.object(module, "acquire_main_checkout_lock", _null_context):
                                ok = module.merge_with_codex_fallback("origin/source", "target <- source", cwd=cwd)

        self.assertTrue(ok)
        collapse.assert_called_once_with(cwd)
        codex.assert_not_called()
        self.assertIn(["git", "commit", "--no-edit"], commands)

    def test_merge_conflict_calls_codex_after_canonical_collapse_leaves_source(self) -> None:
        module = load_sync_module()
        cwd = Path("/tmp/bedc-sync-test")

        def fake_run(cmd, **kwargs):
            if cmd[:3] == ["git", "merge", "--no-ff"]:
                return Result(returncode=1, stdout="CONFLICT\n")
            raise AssertionError(f"unexpected command: {cmd}")

        with mock.patch.object(module, "install_canonical_generated_merge_driver", return_value=True):
            with mock.patch.object(module, "run", side_effect=fake_run):
                with mock.patch.object(module, "conflicted_files", side_effect=[
                    [
                        "papers/bedc-quality-lab/reports/canonical/index.json",
                        "papers/bedc-quality-lab/bedc_quality_lab/source_probe.py",
                    ],
                    ["papers/bedc-quality-lab/bedc_quality_lab/source_probe.py"],
                ]):
                    with mock.patch.object(module, "collapse_canonical_generated_conflicts", return_value=True):
                        with mock.patch.object(module, "call_codex_to_resolve", return_value=True) as codex:
                            with mock.patch.object(module, "acquire_main_checkout_lock", _null_context):
                                ok = module.merge_with_codex_fallback("origin/source", "target <- source", cwd=cwd)

        self.assertTrue(ok)
        codex.assert_called_once_with(cwd)


if __name__ == "__main__":
    unittest.main()

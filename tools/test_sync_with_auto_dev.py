from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path
from unittest import mock


REPO_ROOT = Path(__file__).resolve().parents[1]


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


if __name__ == "__main__":
    unittest.main()

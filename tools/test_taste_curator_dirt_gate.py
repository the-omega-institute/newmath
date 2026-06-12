#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path


MODULE_PATH = Path(__file__).resolve().with_name("taste_curator.py")


def load_taste_curator():
    spec = importlib.util.spec_from_file_location("taste_curator", MODULE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load taste_curator module")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def assert_equal(actual, expected) -> None:
    if actual != expected:
        raise AssertionError(f"expected {expected!r}, got {actual!r}")


class FakePushLock:
    def __call__(self, branch, timeout):
        self.branch = branch
        self.timeout = timeout
        return self

    def __enter__(self):
        return None

    def __exit__(self, exc_type, exc, tb):
        return False


def completed(args, returncode=0, stdout="", stderr=""):
    return subprocess.CompletedProcess(args=list(args), returncode=returncode, stdout=stdout, stderr=stderr)


def test_dossier_fetch_failure_short_circuits(taste_curator) -> None:
    calls = []
    alerts = []

    def fake_git(*args, **kwargs):
        calls.append(args)
        if args[:3] == ("status", "--porcelain", "--"):
            return completed(args, stdout=" M docs/dossier/taste-evolutions.qmd\n")
        if args == ("fetch", "origin", taste_curator.BASE_BRANCH):
            return completed(args, returncode=1, stderr="fetch failed\n")
        return completed(args)

    taste_curator.git = fake_git
    taste_curator.append_alert = lambda category, details, dry_run=False: alerts.append((category, details, dry_run))
    taste_curator.import_push_lock = lambda: FakePushLock()

    taste_curator.commit_dossier_refresh_if_needed(False, dry_run=False)

    assert_equal(("add", "docs/dossier/taste-evolutions.qmd") in calls, False)
    assert_equal(any(call and call[0] == "commit" for call in calls), False)
    assert_equal(len(alerts), 1)
    assert_equal(alerts[0][0], "dossier_snapshot_sync_failed")
    assert_equal(alerts[0][1], {"stderr": "fetch failed"})


def main() -> int:
    taste_curator = load_taste_curator()
    dossier = " M docs/dossier/taste-evolutions.qmd"
    staged_dossier = "M  docs/dossier/taste-evolutions.qmd"
    unstaged_staged_dossier = "MM docs/dossier/taste-evolutions.qmd"
    deleted_dossier = "D  docs/dossier/taste-evolutions.qmd"
    added_dossier = "A  docs/dossier/taste-evolutions.qmd"
    other = " M tools/taste_curator.py"
    deleted = "D  papers/bedc/parts/example.tex"
    renamed_dossier = "R  docs/dossier/taste-evolutions.qmd -> docs/dossier/taste-evolutions-old.qmd"

    assert_equal(taste_curator._foreign_dirty_paths([dossier]), [])
    assert_equal(taste_curator._foreign_dirty_paths([staged_dossier]), [])
    assert_equal(taste_curator._foreign_dirty_paths([unstaged_staged_dossier]), [])
    assert_equal(taste_curator._foreign_dirty_paths([deleted_dossier]), [deleted_dossier])
    assert_equal(taste_curator._foreign_dirty_paths([added_dossier]), [added_dossier])
    assert_equal(taste_curator._foreign_dirty_paths([dossier, other]), [other])
    assert_equal(taste_curator._foreign_dirty_paths([other, deleted]), [other, deleted])
    assert_equal(taste_curator._foreign_dirty_paths([renamed_dossier]), [renamed_dossier])
    test_dossier_fetch_failure_short_circuits(taste_curator)

    print("taste_curator dirt gate tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

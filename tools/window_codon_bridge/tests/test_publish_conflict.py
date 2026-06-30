#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import subprocess
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
SUPERVISOR_PATH = REPO_ROOT / "tools" / "window_codon_bridge" / "supervisor.py"


def load_supervisor():
    spec = importlib.util.spec_from_file_location("window_codon_bridge_supervisor", SUPERVISOR_PATH)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


supervisor = load_supervisor()


def run_git(repo: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess:
    proc = subprocess.run(["git", "-C", str(repo), *args], capture_output=True, text=True)
    if check and proc.returncode != 0:
        detail = ((proc.stderr or proc.stdout) or "").strip()
        raise AssertionError(f"git {' '.join(args)} failed in {repo}: {detail}")
    return proc


def configure_repo(repo: Path) -> None:
    run_git(repo, "config", "user.email", "bridge-test@example.invalid")
    run_git(repo, "config", "user.name", "Bridge Test")


def write_file(repo: Path, rel: str, text: str) -> None:
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def commit_file(repo: Path, rel: str, text: str, message: str) -> None:
    write_file(repo, rel, text)
    run_git(repo, "add", rel)
    run_git(repo, "commit", "-m", message)


def make_fixture() -> tuple[Path, Path, Path, tempfile.TemporaryDirectory]:
    tmp = tempfile.TemporaryDirectory()
    root = Path(tmp.name)
    remote = root / "remote.git"
    seed = root / "seed"
    clone_a = root / "clone-a"
    clone_b = root / "clone-b"

    subprocess.run(["git", "init", "--bare", str(remote)], check=True, capture_output=True, text=True)
    subprocess.run(["git", "init", str(seed)], check=True, capture_output=True, text=True)
    configure_repo(seed)
    run_git(seed, "checkout", "-b", "main")
    initial_paths = [
        "papers/window_codon_bridge/intake_coverage.json",
        "tools/window_codon_bridge/registries/claims.json",
    ]
    for rel in initial_paths:
        write_file(seed, rel, "base\n")
    run_git(seed, "add", *initial_paths)
    run_git(seed, "commit", "-m", "seed bridge state")
    run_git(seed, "remote", "add", "origin", str(remote))
    run_git(seed, "push", "-u", "origin", "main")
    subprocess.run(
        ["git", "--git-dir", str(remote), "symbolic-ref", "HEAD", "refs/heads/main"],
        check=True,
        capture_output=True,
        text=True,
    )

    subprocess.run(["git", "clone", str(remote), str(clone_a)], check=True, capture_output=True, text=True)
    subprocess.run(["git", "clone", str(remote), str(clone_b)], check=True, capture_output=True, text=True)
    configure_repo(clone_a)
    configure_repo(clone_b)
    return remote, clone_a, clone_b, tmp


def merge_head_exists(repo: Path) -> bool:
    return run_git(repo, "rev-parse", "-q", "--verify", "MERGE_HEAD", check=False).returncode == 0


def status_porcelain(repo: Path) -> str:
    return run_git(repo, "status", "--porcelain").stdout.strip()


class PublishConflictTests(unittest.TestCase):
    def test_classify_publish_conflicts(self) -> None:
        churn, non_churn = supervisor.classify_publish_conflicts([
            "papers/window_codon_bridge/intake_coverage.json",
            "papers/window_codon_bridge/cross_branch_concordance.md",
        ])
        self.assertEqual(non_churn, [])
        self.assertEqual(churn, [
            "papers/window_codon_bridge/intake_coverage.json",
            "papers/window_codon_bridge/cross_branch_concordance.md",
        ])

        churn, non_churn = supervisor.classify_publish_conflicts([
            "tools/window_codon_bridge/registries/claims.json",
        ])
        self.assertEqual(churn, [])
        self.assertEqual(non_churn, ["tools/window_codon_bridge/registries/claims.json"])

        churn, non_churn = supervisor.classify_publish_conflicts([
            "tools/window_codon_bridge/state/oracle_assimilation/latest_edge_defect_oracle_memo.md",
        ])
        self.assertEqual(churn, [
            "tools/window_codon_bridge/state/oracle_assimilation/latest_edge_defect_oracle_memo.md",
        ])
        self.assertEqual(non_churn, [])

        self.assertEqual(supervisor.classify_publish_conflicts([]), ([], []))

    def test_churn_conflict_is_auto_resolved_and_pushed(self) -> None:
        remote, clone_a, clone_b, tmp = make_fixture()
        self.addCleanup(tmp.cleanup)
        rel = "papers/window_codon_bridge/intake_coverage.json"

        commit_file(clone_a, rel, "local churn\n", "local churn")
        commit_file(clone_b, rel, "remote churn\n", "remote churn")
        run_git(clone_b, "push", "origin", "HEAD:main")

        old_root = supervisor.REPO_ROOT
        supervisor.REPO_ROOT = clone_a
        try:
            result = supervisor._publish_reconcile_after_push_reject("main", 1)
        finally:
            supervisor.REPO_ROOT = old_root

        self.assertTrue(result.get("pushed"), result)
        self.assertEqual(result.get("auto_resolved"), 1)
        self.assertFalse(merge_head_exists(clone_a))
        self.assertEqual(status_porcelain(clone_a), "")
        remote_head = run_git(clone_a, "ls-remote", str(remote), "refs/heads/main").stdout.split()[0]
        local_head = run_git(clone_a, "rev-parse", "HEAD").stdout.strip()
        self.assertEqual(remote_head, local_head)

    def test_science_conflict_is_deferred_and_clean(self) -> None:
        _, clone_a, clone_b, tmp = make_fixture()
        self.addCleanup(tmp.cleanup)
        rel = "tools/window_codon_bridge/registries/claims.json"

        commit_file(clone_a, rel, "local science\n", "local science")
        commit_file(clone_b, rel, "remote science\n", "remote science")
        run_git(clone_b, "push", "origin", "HEAD:main")

        old_root = supervisor.REPO_ROOT
        supervisor.REPO_ROOT = clone_a
        try:
            result = supervisor._publish_reconcile_after_push_reject("main", 1)
        finally:
            supervisor.REPO_ROOT = old_root

        self.assertFalse(result.get("pushed"), result)
        self.assertEqual(result.get("deferred"), "science_conflict")
        self.assertEqual(result.get("files"), [rel])
        self.assertFalse(merge_head_exists(clone_a))
        self.assertEqual(status_porcelain(clone_a), "")


if __name__ == "__main__":
    unittest.main(verbosity=2)

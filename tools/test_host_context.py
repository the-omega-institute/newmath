from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from host_context import host_env_candidates, load_host_context, parse_host_env_text


REPO_ROOT = Path(__file__).resolve().parents[1]


class HostContextTests(unittest.TestCase):
    def test_parse_host_env_supports_exports_quotes_and_comments(self):
        values = parse_host_env_text(
            """
            # ignored
            export INTEGRATION_BRANCH=auto-refact-dev
            REVIEW_BASE_BRANCH="main branch"
            REPO_ROOT=/tmp/example # trailing comment
            EMPTY=
            """
        )

        self.assertEqual(values["INTEGRATION_BRANCH"], "auto-refact-dev")
        self.assertEqual(values["REVIEW_BASE_BRANCH"], "main branch")
        self.assertEqual(values["REPO_ROOT"], "/tmp/example")
        self.assertEqual(values["EMPTY"], "")

    def test_cli_overrides_host_env_and_defaults(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            env_file = root / "host.env"
            env_file.write_text(
                "INTEGRATION_BRANCH=from-env\n"
                "REVIEW_BASE_BRANCH=env-base\n",
                encoding="utf-8",
            )

            context = load_host_context(
                repo_root=root,
                env_file=env_file,
                defaults={"INTEGRATION_BRANCH": "from-default"},
                overrides={"INTEGRATION_BRANCH": "from-cli"},
            )

            self.assertEqual(context.require("INTEGRATION_BRANCH"), "from-cli")
            self.assertEqual(context.require("REVIEW_BASE_BRANCH"), "env-base")

    def test_missing_key_uses_default(self):
        with tempfile.TemporaryDirectory() as td:
            context = load_host_context(
                repo_root=td,
                env_file=Path(td) / "missing.env",
                defaults={"INTEGRATION_BRANCH": "from-default"},
            )

            self.assertEqual(context.require("INTEGRATION_BRANCH"), "from-default")
            self.assertEqual(context.require("MIRROR_BRANCH"), "auto-dev")

    def test_relative_paths_resolve_against_repo_root(self):
        with tempfile.TemporaryDirectory() as td:
            context = load_host_context(
                repo_root=td,
                env_file=Path(td) / "missing.env",
                defaults={"WORKTREE_DIR": ".worktrees"},
            )

            self.assertEqual(context.path("WORKTREE_DIR"), Path(td).resolve() / ".worktrees")

    def test_linked_worktree_host_env_candidate_uses_common_checkout(self):
        with tempfile.TemporaryDirectory() as td:
            common = Path(td) / "repo"
            worktree = common / ".worktrees" / "unit"
            git_dir = common / ".git" / "worktrees" / "unit"
            host_env = common / ".refactor-loop" / "host.env"
            worktree.mkdir(parents=True)
            git_dir.mkdir(parents=True)
            host_env.parent.mkdir(parents=True)
            (worktree / ".git").write_text(f"gitdir: {git_dir}\n", encoding="utf-8")
            host_env.write_text("INTEGRATION_BRANCH=from-common\n", encoding="utf-8")

            self.assertIn(host_env.resolve(), host_env_candidates(worktree))
            context = load_host_context(repo_root=worktree)
            self.assertEqual(context.require("INTEGRATION_BRANCH"), "from-common")


class ScaffoldFrameworkDeletionTests(unittest.TestCase):
    def test_scaffold_framework_file_is_absent(self):
        self.assertFalse((REPO_ROOT / "papers" / "bedc" / "scripts" / "scaffold_framework.py").exists())

    def test_scaffold_framework_has_no_runtime_imports(self):
        roots = [REPO_ROOT / "papers", REPO_ROOT / "lean4", REPO_ROOT / "tools"]
        hits: list[str] = []
        for root in roots:
            for path in root.rglob("*"):
                if not path.is_file() or path.suffix not in {".py", ".sh", ".tex", ".md"}:
                    continue
                if path.name.startswith("test_"):
                    continue
                try:
                    text = path.read_text(encoding="utf-8", errors="ignore")
                except OSError:
                    continue
                if "scaffold_framework" in text:
                    hits.append(str(path.relative_to(REPO_ROOT)))

        self.assertEqual(hits, [])


if __name__ == "__main__":
    unittest.main()

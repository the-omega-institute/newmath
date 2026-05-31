from __future__ import annotations

import importlib.util
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from host_context import (
    MissingHostValueError,
    host_env_candidates,
    host_path,
    host_value,
    load_host_context,
    parse_host_env_text,
)


REPO_ROOT = Path(__file__).resolve().parents[1]


class HostContextTests(unittest.TestCase):
    def test_parse_host_env_supports_exports_quotes_and_comments(self):
        values = parse_host_env_text(
            """
            # ignored
            export BEDC_PIPELINE_BRANCH=bedc-pipeline
            BEDC_UPSTREAM_BRANCH="main branch"
            REPO_ROOT=/tmp/example # trailing comment
            EMPTY=
            """
        )

        self.assertEqual(values["BEDC_PIPELINE_BRANCH"], "bedc-pipeline")
        self.assertEqual(values["BEDC_UPSTREAM_BRANCH"], "main branch")
        self.assertEqual(values["REPO_ROOT"], "/tmp/example")
        self.assertEqual(values["EMPTY"], "")

    def test_explicit_overrides_env_and_host_env(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            env_file = root / "host.env"
            env_file.write_text(
                "BEDC_PIPELINE_BRANCH=from-host-env\n"
                "BEDC_UPSTREAM_BRANCH=host-base\n",
                encoding="utf-8",
            )

            context = load_host_context(
                repo_root=root,
                env_file=env_file,
                env={"BEDC_PIPELINE_BRANCH": "from-process-env"},
                overrides={"BEDC_PIPELINE_BRANCH": "from-cli"},
            )

            self.assertEqual(context.require("BEDC_PIPELINE_BRANCH"), "from-cli")
            self.assertEqual(context.require("BEDC_UPSTREAM_BRANCH"), "host-base")

    def test_process_env_overrides_host_env(self):
        with tempfile.TemporaryDirectory() as td:
            env_file = Path(td) / "host.env"
            env_file.write_text("BEDC_PIPELINE_BRANCH=from-host-env\n", encoding="utf-8")

            context = load_host_context(
                repo_root=td,
                env_file=env_file,
                env={"BEDC_PIPELINE_BRANCH": "from-process-env"},
            )

            self.assertEqual(context.require("BEDC_PIPELINE_BRANCH"), "from-process-env")

    def test_required_missing_key_fails_closed(self):
        with tempfile.TemporaryDirectory() as td:
            with self.assertRaisesRegex(MissingHostValueError, "BEDC_PIPELINE_BRANCH"):
                host_value(
                    td,
                    "BEDC_PIPELINE_BRANCH",
                    env_file=Path(td) / "missing.env",
                    env={},
                    required=True,
                )

    def test_relative_paths_resolve_against_repo_root(self):
        with tempfile.TemporaryDirectory() as td:
            value = host_path(
                td,
                "WORKTREE_DIR",
                env_file=Path(td) / "missing.env",
                env={},
                default=".worktrees",
            )

            self.assertEqual(value, Path(td).resolve() / ".worktrees")

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
            host_env.write_text("BEDC_PIPELINE_BRANCH=from-common\n", encoding="utf-8")

            self.assertIn(host_env.resolve(), host_env_candidates(worktree))
            context = load_host_context(repo_root=worktree, env={})
            self.assertEqual(context.require("BEDC_PIPELINE_BRANCH"), "from-common")


class DaemonHostIntegrationTests(unittest.TestCase):
    def import_module_with_env(self, relative_path: str, name: str):
        env = {
            "REPO_ROOT": str(REPO_ROOT),
            "BEDC_LEAN_BASE_BRANCH": "lean-host",
            "BEDC_PIPELINE_BRANCH": "pipeline-host",
            "BEDC_MIRROR_BRANCH": "mirror-host",
            "BEDC_UPSTREAM_BRANCH": "upstream-host",
            "BEDC_CODEX_PATH": "/tmp/codex-host",
            "BEDC_SYNC_VALIDATION_WORKTREE": "sync-host-wt",
        }
        path = REPO_ROOT / relative_path
        spec = importlib.util.spec_from_file_location(name, path)
        self.assertIsNotNone(spec)
        self.assertIsNotNone(spec.loader)
        old_module = sys.modules.pop(name, None)
        try:
            with mock.patch.dict(os.environ, env, clear=False):
                module = importlib.util.module_from_spec(spec)
                sys.modules[name] = module
                spec.loader.exec_module(module)
                return module
        finally:
            if old_module is not None:
                sys.modules[name] = old_module
            else:
                sys.modules.pop(name, None)

    def test_auto_heal_uses_bedc_host_branches_for_prompts_and_probes(self):
        module = self.import_module_with_env("tools/auto_heal_base.py", "auto_heal_host_test")

        self.assertEqual(module.BASE_BRANCH, "pipeline-host")
        self.assertEqual(module.MIRROR_BRANCH, "mirror-host")
        self.assertEqual(module.CODEX_PATH, "/tmp/codex-host")
        rendered = module.render_prompt_host_context(
            "codex-auto-dev receives changes before auto-dev runs CI"
        )
        self.assertEqual(rendered, "pipeline-host receives changes before mirror-host runs CI")

        branches: list[str] = []

        def fake_run(cmd, **kwargs):
            branches.append(cmd[cmd.index("--branch") + 1])

            class Result:
                returncode = 0
                stdout = "[]"

            return Result()

        with mock.patch.object(module.shutil, "which", return_value="/usr/bin/gh"):
            with mock.patch.object(module, "run", side_effect=fake_run):
                self.assertEqual(module.detect_ci_failures(), [])

        self.assertEqual(branches, ["pipeline-host", "mirror-host"])

    def test_sync_uses_bedc_host_branches_for_prompt_and_worktree(self):
        module = self.import_module_with_env("tools/sync_with_auto_dev.py", "sync_host_test")

        self.assertEqual(module.SOURCE_BRANCH, "pipeline-host")
        self.assertEqual(module.MIRROR_BRANCH, "mirror-host")
        self.assertEqual(module.UPSTREAM_BRANCH, "upstream-host")
        self.assertEqual(module.CODEX_PATH, "/tmp/codex-host")
        self.assertEqual(module.VALIDATION_WORKTREE, REPO_ROOT / "sync-host-wt")
        rendered = module.render_prompt_host_context(
            "codex-auto-dev merges auto-dev and dev"
        )
        self.assertEqual(rendered, "pipeline-host merges mirror-host and upstream-host")

    def test_codex_formalize_uses_bedc_host_values(self):
        module = self.import_module_with_env(
            "lean4/scripts/codex_formalize.py",
            "codex_formalize_host_test",
        )

        self.assertEqual(module.BASE_BRANCH_DEFAULT, "lean-host")
        self.assertEqual(module.BASE_BRANCH, "lean-host")
        self.assertEqual(module.CODEX_PATH, "/tmp/codex-host")
        self.assertEqual(module.WORKTREE_DIR, REPO_ROOT / ".worktrees")


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


class SourceRegressionTests(unittest.TestCase):
    def test_metacic_setup_route_surface_is_absent(self):
        forbidden = [
            "SubjectReductionSetup",
            "subject_reduction_via_setup",
            "SubjectReductionSetupBundleProjectionUp",
        ]
        paths = [
            *sorted((REPO_ROOT / "lean4" / "BEDC" / "MetaCIC").rglob("*.lean")),
            *sorted((REPO_ROOT / "papers" / "bedc" / "parts").rglob("*.tex")),
            REPO_ROOT / "papers" / "bedc" / "preamble.tex",
        ]

        hits: list[str] = []
        for path in paths:
            text = path.read_text(encoding="utf-8", errors="ignore")
            for needle in forbidden:
                if needle in text:
                    hits.append(f"{path.relative_to(REPO_ROOT)}: {needle}")

        self.assertEqual(hits, [])

    def test_bedc_daemons_do_not_keep_old_topology_assignments(self):
        forbidden = [
            'BASE_BRANCH_DEFAULT = "lean4-codex-auto-dev"',
            'BASE_BRANCH = "codex-auto-dev"',
            'SOURCE_BRANCH = "codex-auto-dev"',
            'MIRROR_BRANCH = "auto-dev"',
            'UPSTREAM_BRANCH = "dev"',
            '"/opt/homebrew/bin/codex"',
            'Path("/tmp/.bedc_sync_validate_wt")',
        ]
        paths = [
            REPO_ROOT / "lean4" / "scripts" / "codex_formalize.py",
            REPO_ROOT / "tools" / "auto_heal_base.py",
            REPO_ROOT / "tools" / "sync_with_auto_dev.py",
        ]

        hits: list[str] = []
        for path in paths:
            text = path.read_text(encoding="utf-8")
            for needle in forbidden:
                if needle in text:
                    hits.append(f"{path.relative_to(REPO_ROOT)}: {needle}")

        self.assertEqual(hits, [])


if __name__ == "__main__":
    unittest.main()

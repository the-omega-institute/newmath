from __future__ import annotations

import importlib.util
import inspect
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[1]
TOOLS_DIR = REPO_ROOT / "tools"
for import_root in (REPO_ROOT, TOOLS_DIR):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

from tools.host_context import (
    MissingHostValueError,
    host_path,
    host_value,
    load_host_context,
)


class HostContextTests(unittest.TestCase):
    def test_public_helpers_do_not_accept_env_file(self):
        for helper in (load_host_context, host_value, host_path):
            self.assertNotIn("env_file", inspect.signature(helper).parameters)

    def test_explicit_overrides_process_env_and_default(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)

            context = load_host_context(
                repo_root=root,
                env={"BEDC_PIPELINE_BRANCH": "from-process-env"},
                defaults={
                    "BEDC_PIPELINE_BRANCH": "from-default",
                    "BEDC_UPSTREAM_BRANCH": "default-base",
                },
                overrides={"BEDC_PIPELINE_BRANCH": "from-cli"},
            )

            self.assertEqual(context.require("BEDC_PIPELINE_BRANCH"), "from-cli")
            self.assertEqual(context.require("BEDC_UPSTREAM_BRANCH"), "default-base")

    def test_process_env_overrides_default(self):
        with tempfile.TemporaryDirectory() as td:
            context = load_host_context(
                repo_root=td,
                env={"BEDC_PIPELINE_BRANCH": "from-process-env"},
                defaults={"BEDC_PIPELINE_BRANCH": "from-default"},
            )

            self.assertEqual(context.require("BEDC_PIPELINE_BRANCH"), "from-process-env")

    def test_in_code_default_supplies_value(self):
        with tempfile.TemporaryDirectory() as td:
            value = host_value(
                td,
                "BEDC_PIPELINE_BRANCH",
                env={},
                default="codex-auto-dev",
                required=True,
            )

            self.assertEqual(value, "codex-auto-dev")

    def test_required_missing_key_fails_closed(self):
        with tempfile.TemporaryDirectory() as td:
            with self.assertRaisesRegex(MissingHostValueError, "BEDC_PIPELINE_BRANCH"):
                host_value(
                    td,
                    "BEDC_PIPELINE_BRANCH",
                    env={},
                    required=True,
                )

    def test_relative_paths_resolve_against_repo_root(self):
        with tempfile.TemporaryDirectory() as td:
            value = host_path(
                td,
                "WORKTREE_DIR",
                env={},
                default=".worktrees",
            )

            self.assertEqual(value, Path(td).resolve() / ".worktrees")


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

    def test_paper_builder_uses_bedc_host_values(self):
        module = self.import_module_with_env(
            "papers/bedc/scripts/paper_builder_daemon.py",
            "paper_builder_host_test",
        )

        self.assertEqual(module.BASE_BRANCH, "pipeline-host")
        self.assertEqual(module.CODEX_PATH, "/tmp/codex-host")

    def test_paper_builder_codex_fix_uses_host_codex_and_branch(self):
        module = self.import_module_with_env(
            "papers/bedc/scripts/paper_builder_daemon.py",
            "paper_builder_fix_host_test",
        )
        captured: dict[str, str | list[str]] = {}
        git_revs = iter(["pre-tip\n", "post-tip\n"])

        def fake_subprocess_run(cmd, **kwargs):
            if cmd[0] == "git":
                class GitResult:
                    stdout = next(git_revs)

                return GitResult()
            captured["argv"] = cmd
            captured["prompt"] = cmd[-1]

            class CodexResult:
                stdout = ""

            return CodexResult()

        with mock.patch.object(module, "run_git", return_value=(0, "")):
            with mock.patch.object(module, "log"):
                with mock.patch.object(module.subprocess, "run", side_effect=fake_subprocess_run):
                    self.assertTrue(module.codex_fix("abcdef123456", "build tail", 2.0))

        argv = captured["argv"]
        prompt = captured["prompt"]
        self.assertEqual(argv[0], "/tmp/codex-host")
        self.assertIn("pipeline-host", prompt)
        self.assertIn("git push origin HEAD:pipeline-host", prompt)
        self.assertNotIn("git push origin HEAD:codex-auto-dev", prompt)


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

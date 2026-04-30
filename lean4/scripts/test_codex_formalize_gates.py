#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT_PATH = REPO_ROOT / "lean4" / "scripts" / "codex_formalize.py"


def load_codex_formalize():
    spec = importlib.util.spec_from_file_location("codex_formalize_under_test", SCRIPT_PATH)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


cf = load_codex_formalize()


class QualityGateTests(unittest.TestCase):
    def init_repo(self) -> tuple[tempfile.TemporaryDirectory[str], Path, str]:
        td = tempfile.TemporaryDirectory()
        root = Path(td.name)
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        subprocess.run(["git", "config", "user.email", "test@example.com"], cwd=root, check=True)
        subprocess.run(["git", "config", "user.name", "Test User"], cwd=root, check=True)
        (root / "lean4" / "BEDC" / "FKernel").mkdir(parents=True)
        (root / "papers" / "bedc" / "parts" / "core").mkdir(parents=True)
        (root / "lean4" / "BEDC" / "Base.lean").write_text(
            "namespace BEDC\n"
            "inductive BMark where\n"
            "  | zero\n"
            "inductive BHist where\n"
            "  | empty\n"
            "def hsame (a b : BHist) : Prop := a = b\n"
            "theorem existing_kernel_theorem : hsame BHist.empty BHist.empty := by rfl\n"
            "end BEDC\n",
            encoding="utf-8",
        )
        (root / "papers" / "bedc" / "parts" / "core" / "base.tex").write_text(
            "\\leanchecked{BEDC.existing\_kernel\_theorem}\n",
            encoding="utf-8",
        )
        subprocess.run(["git", "add", "."], cwd=root, check=True)
        subprocess.run(["git", "commit", "-q", "-m", "base"], cwd=root, check=True)
        base_sha = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=root, check=True, text=True, capture_output=True
        ).stdout.strip()
        return td, root, base_sha

    def wt(self, root: Path, base_sha: str):
        return cf.WorktreeInfo(path=root, branch="test", round_number=1, base_sha=base_sha)

    def test_forbidden_placeholders_reject_constant_and_opaque(self):
        td, root, base_sha = self.init_repo()
        with td:
            path = root / "lean4" / "BEDC" / "FKernel" / "Placeholder.lean"
            path.write_text(
                "namespace BEDC.FKernel\n"
                "constant bad_constant : BEDC.BHist\n"
                "opaque bad_opaque : BEDC.BHist := BEDC.BHist.empty\n"
                "end BEDC.FKernel\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "placeholder"], cwd=root, check=True)

            violations = cf.detect_sorry_literals(self.wt(root, base_sha))

            self.assertEqual(len(violations), 2)
            self.assertTrue(any("constant" in v for v in violations))
            self.assertTrue(any("opaque" in v for v in violations))

    def test_hollow_semantic_patterns_reject_unit_true_and_minimal_namecert(self):
        td, root, base_sha = self.init_repo()
        with td:
            path = root / "lean4" / "BEDC" / "FKernel" / "Hollow.lean"
            path.write_text(
                "namespace BEDC.FKernel\n"
                "def hollow_unit : Unit := ()\n"
                "theorem hollow_true : True := True.intro\n"
                "def hollow_cert := NameCert.mk () () () () ()\n"
                "def hollow_setup := MinimalNameCertSetup\n"
                "end BEDC.FKernel\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "hollow"], cwd=root, check=True)

            violations = cf.detect_hollow_semantic_patterns(self.wt(root, base_sha))

            self.assertGreaterEqual(len(violations), 4)
            self.assertTrue(any("NameCert.mk" in v for v in violations))
            self.assertTrue(any("MinimalNameCertSetup" in v for v in violations))

    def test_multi_commit_round_checks_all_commits_after_formalization_base(self):
        td, root, base_sha = self.init_repo()
        with td:
            upstream_sha = subprocess.run(
                ["git", "rev-parse", "HEAD"], cwd=root, check=True, text=True, capture_output=True
            ).stdout.strip()
            (root / "lean4" / "BEDC" / "FKernel" / "First.lean").write_text(
                "namespace BEDC.FKernel\n"
                "def first_history : BEDC.BHist := BEDC.BHist.empty\n"
                "end BEDC.FKernel\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "first"], cwd=root, check=True)
            (root / "lean4" / "BEDC" / "FKernel" / "Second.lean").write_text(
                "namespace BEDC.FKernel\n"
                "constant second_placeholder : BEDC.BHist\n"
                "end BEDC.FKernel\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "second"], cwd=root, check=True)
            wt = cf.WorktreeInfo(
                path=root,
                branch="test",
                round_number=1,
                base_sha=base_sha,
                formalization_base_sha=upstream_sha,
            )

            changed = cf._changed_lean_files(wt)
            violations = cf.detect_sorry_literals(wt)

            self.assertIn("lean4/BEDC/FKernel/First.lean", changed)
            self.assertIn("lean4/BEDC/FKernel/Second.lean", changed)
            self.assertEqual(len(violations), 1)
            self.assertIn("second_placeholder", violations[0])

    def test_shell_pattern_uses_round_diff_base_not_origin_branch(self):
        td, root, base_sha = self.init_repo()
        with td:
            subprocess.run(["git", "checkout", "-q", "-b", cf.BASE_BRANCH], cwd=root, check=True)
            upstream_sha = subprocess.run(
                ["git", "rev-parse", "HEAD"], cwd=root, check=True, text=True, capture_output=True
            ).stdout.strip()
            subprocess.run(["git", "update-ref", f"refs/remotes/origin/{cf.BASE_BRANCH}", base_sha], cwd=root, check=True)
            (root / "lean4" / "BEDC" / "FKernel" / "AllowedShell.lean").write_text(
                "namespace BEDC.FKernel\n"
                "structure PaperShell where\n"
                "  P : Prop\n"
                "  Q : Prop\n"
                "  P_h : P\n"
                "theorem paper_shell (D : PaperShell) : D.P := D.P_h\n"
                "end BEDC.FKernel\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "upstream shell"], cwd=root, check=True)
            wt = cf.WorktreeInfo(
                path=root,
                branch="test",
                round_number=1,
                base_sha=base_sha,
                formalization_base_sha=upstream_sha,
            )

            violations = cf.detect_shell_pattern(wt)

            self.assertEqual(violations, [])

    def test_register_only_round_is_rejected(self):
        td, root, base_sha = self.init_repo()
        with td:
            tex = root / "papers" / "bedc" / "parts" / "core" / "base.tex"
            tex.write_text(
                tex.read_text(encoding="utf-8")
                + "\\leanchecked{BEDC.another\_paper\_marker}\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "paper only"], cwd=root, check=True)

            violations = cf.detect_register_only_round(self.wt(root, base_sha))

            self.assertEqual(len(violations), 1)
            self.assertIn("no Lean declarations", violations[0])

    def test_new_leanvariant_marker_is_rejected(self):
        td, root, base_sha = self.init_repo()
        with td:
            (root / "lean4" / "BEDC" / "FKernel" / "Good.lean").write_text(
                "namespace BEDC.FKernel\n"
                "def good_kernel_touchpoint : BEDC.BHist := BEDC.BHist.empty\n"
                "end BEDC.FKernel\n",
                encoding="utf-8",
            )
            tex = root / "papers" / "bedc" / "parts" / "core" / "base.tex"
            tex.write_text(
                tex.read_text(encoding="utf-8")
                + "\\leanvariant{BEDC.FKernel.good\_kernel\_touchpoint}\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "variant"], cwd=root, check=True)

            violations = cf.detect_new_leanvariant_markers(self.wt(root, base_sha))

            self.assertEqual(len(violations), 1)
            self.assertIn("leanvariant", violations[0])

    def test_new_leanvariant_marker_ignores_non_tex_prompt_templates(self):
        td, root, base_sha = self.init_repo()
        with td:
            (root / "papers" / "bedc" / "scripts" / "prompts").mkdir(parents=True)
            (root / "papers" / "bedc" / "scripts" / "prompts" / "phase_revise.txt").write_text(
                "Do not add \\leanvariant{X} markers.\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "prompt template"], cwd=root, check=True)

            violations = cf.detect_new_leanvariant_markers(self.wt(root, base_sha))

            self.assertEqual(violations, [])

    def test_marker_must_reference_current_round_declaration(self):
        td, root, base_sha = self.init_repo()
        with td:
            (root / "lean4" / "BEDC" / "FKernel" / "Fresh.lean").write_text(
                "namespace BEDC.FKernel\n"
                "def fresh_history : BEDC.BHist := BEDC.BHist.empty\n"
                "end BEDC.FKernel\n",
                encoding="utf-8",
            )
            tex = root / "papers" / "bedc" / "parts" / "core" / "base.tex"
            tex.write_text(
                tex.read_text(encoding="utf-8")
                + "\\leanchecked{BEDC.existing\_kernel\_theorem}\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "old marker"], cwd=root, check=True)

            violations = cf.detect_markers_not_backed_by_new_decls(self.wt(root, base_sha))

            self.assertEqual(len(violations), 1)
            self.assertIn("existing_kernel_theorem", violations[0])

    def test_rebased_upstream_marker_is_not_treated_as_current_round_marker(self):
        td, root, base_sha = self.init_repo()
        with td:
            subprocess.run(["git", "checkout", "-q", "-b", "upstream"], cwd=root, check=True)
            tex = root / "papers" / "bedc" / "parts" / "core" / "base.tex"
            tex.write_text(
                tex.read_text(encoding="utf-8")
                + "\\leanchecked{BEDC.existing\_kernel\_theorem}\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "upstream marker"], cwd=root, check=True)
            upstream_sha = subprocess.run(
                ["git", "rev-parse", "HEAD"], cwd=root, check=True, text=True, capture_output=True
            ).stdout.strip()

            subprocess.run(["git", "checkout", "-q", "-B", "test", base_sha], cwd=root, check=True)
            subprocess.run(["git", "rebase", "upstream"], cwd=root, check=True)
            (root / "lean4" / "BEDC" / "FKernel" / "Fresh.lean").write_text(
                "namespace BEDC.FKernel\n"
                "def fresh_history : BEDC.BHist := BEDC.BHist.empty\n"
                "end BEDC.FKernel\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "fresh lean"], cwd=root, check=True)
            wt = cf.WorktreeInfo(
                path=root,
                branch="test",
                round_number=1,
                base_sha=base_sha,
                formalization_base_sha=upstream_sha,
            )

            violations = cf.detect_markers_not_backed_by_new_decls(wt)

            self.assertEqual(violations, [])

    def test_new_declaration_without_kernel_touchpoint_is_rejected(self):
        td, root, base_sha = self.init_repo()
        with td:
            (root / "lean4" / "BEDC" / "FKernel" / "PaperShell.lean").write_text(
                "namespace PaperShell\n"
                "theorem paper_shell (P Q : Prop) (h : P) : P := h\n"
                "end PaperShell\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "shell"], cwd=root, check=True)

            violations = cf.detect_decls_without_kernel_touchpoint(self.wt(root, base_sha))

            self.assertEqual(len(violations), 1)
            self.assertIn("paper_shell", violations[0])
    def test_hollow_semantic_patterns_reject_exact_unit_proof_body(self):
        td, root, base_sha = self.init_repo()
        with td:
            path = root / "lean4" / "BEDC" / "FKernel" / "ExactUnit.lean"
            path.write_text(
                "namespace BEDC.FKernel\n"
                "def exact_unit : Unit := by\n"
                "  exact ()\n"
                "theorem exact_true : True := by\n"
                "  exact True.intro\n"
                "end BEDC.FKernel\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "exact unit"], cwd=root, check=True)

            violations = cf.detect_hollow_semantic_patterns(self.wt(root, base_sha))

            self.assertEqual(len(violations), 2)
            self.assertTrue(any("exact ()" in v for v in violations))
            self.assertTrue(any("True.intro" in v for v in violations))

    def test_marker_accepts_relative_dotted_declaration_in_namespace(self):
        td, root, base_sha = self.init_repo()
        with td:
            (root / "lean4" / "BEDC" / "FKernel" / "Dotted.lean").write_text(
                "namespace BEDC.FKernel\n"
                "def Dotted.fresh_history : BEDC.BHist := BEDC.BHist.empty\n"
                "end BEDC.FKernel\n",
                encoding="utf-8",
            )
            tex = root / "papers" / "bedc" / "parts" / "core" / "base.tex"
            tex.write_text(
                tex.read_text(encoding="utf-8")
                + "\\leandef{BEDC.FKernel.Dotted.fresh\_history}\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "dotted"], cwd=root, check=True)

            violations = cf.detect_markers_not_backed_by_new_decls(self.wt(root, base_sha))

            self.assertEqual(violations, [])

    def test_marker_accepts_nested_namespace_declaration(self):
        td, root, base_sha = self.init_repo()
        with td:
            (root / "lean4" / "BEDC" / "FKernel" / "Nested.lean").write_text(
                "namespace BEDC\n"
                "namespace FKernel\n"
                "def nested_history : BEDC.BHist := BEDC.BHist.empty\n"
                "end FKernel\n"
                "end BEDC\n",
                encoding="utf-8",
            )
            tex = root / "papers" / "bedc" / "parts" / "core" / "base.tex"
            tex.write_text(
                tex.read_text(encoding="utf-8")
                + "\\leandef{BEDC.FKernel.nested\_history}\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "nested"], cwd=root, check=True)

            violations = cf.detect_markers_not_backed_by_new_decls(self.wt(root, base_sha))

            self.assertEqual(violations, [])

    def test_kernel_touchpoint_in_signature_is_accepted(self):
        td, root, base_sha = self.init_repo()
        with td:
            (root / "lean4" / "BEDC" / "FKernel" / "KernelSig.lean").write_text(
                "namespace BEDC.FKernel\n"
                "theorem kernel_sig (h : BEDC.BHist) : h = h := by rfl\n"
                "end BEDC.FKernel\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "kernel sig"], cwd=root, check=True)

            violations = cf.detect_decls_without_kernel_touchpoint(self.wt(root, base_sha))

            self.assertEqual(violations, [])

    def test_parameter_echo_theorem_is_rejected(self):
        td, root, base_sha = self.init_repo()
        with td:
            (root / "lean4" / "BEDC" / "FKernel" / "Echo.lean").write_text(
                "namespace BEDC.FKernel\n"
                "theorem echo_le_refl "
                "(le_refl : forall h : BEDC.BHist, BEDC.hsame h h) : "
                "forall h : BEDC.BHist, BEDC.hsame h h := by\n"
                "  exact le_refl\n"
                "end BEDC.FKernel\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "echo"], cwd=root, check=True)

            violations = cf.detect_shallow_growth_patterns(self.wt(root, base_sha))

            self.assertEqual(len(violations), 1)
            self.assertIn("parameter echo", violations[0])

    def test_carrier_only_round_is_rejected(self):
        td, root, base_sha = self.init_repo()
        with td:
            (root / "lean4" / "BEDC" / "FKernel" / "CarrierOnly.lean").write_text(
                "namespace BEDC.FKernel\n"
                "def RatCarrier (h : BEDC.BHist) : Prop := BEDC.hsame h h\n"
                "def RatSourceSpec (h : BEDC.BHist) : Prop := RatCarrier h\n"
                "end BEDC.FKernel\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "carrier only"], cwd=root, check=True)

            violations = cf.detect_shallow_growth_patterns(self.wt(root, base_sha))

            self.assertEqual(len(violations), 1)
            self.assertIn("carrier/spec definitions", violations[0])

    def test_duplicate_theorem_conclusions_are_rejected(self):
        td, root, base_sha = self.init_repo()
        with td:
            (root / "lean4" / "BEDC" / "FKernel" / "DuplicateShape.lean").write_text(
                "namespace BEDC.FKernel\n"
                "theorem first_carrier_fact (h : BEDC.BHist) : BEDC.hsame h h := by rfl\n"
                "theorem second_carrier_fact (h : BEDC.BHist) : BEDC.hsame h h := by rfl\n"
                "end BEDC.FKernel\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "duplicate shape"], cwd=root, check=True)

            violations = cf.detect_shallow_growth_patterns(self.wt(root, base_sha))

            self.assertEqual(len(violations), 1)
            self.assertIn("duplicate theorem conclusion", violations[0])

    def test_carrier_with_concrete_closure_is_accepted(self):
        td, root, base_sha = self.init_repo()
        with td:
            (root / "lean4" / "BEDC" / "FKernel" / "CarrierClosure.lean").write_text(
                "namespace BEDC.FKernel\n"
                "def RatCarrier (h : BEDC.BHist) : Prop := BEDC.hsame h h\n"
                "theorem RatCarrier_self (h : BEDC.BHist) : RatCarrier h := by rfl\n"
                "end BEDC.FKernel\n",
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-q", "-m", "carrier closure"], cwd=root, check=True)

            violations = cf.detect_shallow_growth_patterns(self.wt(root, base_sha))

            self.assertEqual(violations, [])


class PromptVersionTests(unittest.TestCase):
    def test_phase_prompts_declare_version_once(self):
        for name in ("phase_b", "phase_c"):
            prompt = cf._load_prompt(name)
            version = cf._prompt_version(prompt)
            self.assertEqual(prompt.count(version), 1, name)

    def test_phase_c_prompt_keeps_commit_version_as_placeholder(self):
        prompt = cf.build_phase_c_prompt(1, [])

        version = cf._prompt_version(prompt)
        self.assertEqual(prompt.count(version), 1)
        self.assertIn("prompts: <PROMPTS_VERSION>", prompt)


class PipelinePidTokenTests(unittest.TestCase):
    def test_pipeline_token_is_current_only_when_pid_file_matches_process(self):
        with tempfile.TemporaryDirectory() as td:
            pid_file = Path(td) / ".pipeline.pid"
            cf.write_pipeline_pid(pid_file, 1234)

            self.assertTrue(cf.pipeline_token_is_current(pid_file, 1234))
            self.assertFalse(cf.pipeline_token_is_current(pid_file, 5678))

    def test_missing_pipeline_token_requests_drain(self):
        with tempfile.TemporaryDirectory() as td:
            pid_file = Path(td) / ".pipeline.pid"

            self.assertFalse(cf.pipeline_token_is_current(pid_file, 1234))

    def test_stale_or_malformed_pipeline_token_requests_drain(self):
        with tempfile.TemporaryDirectory() as td:
            pid_file = Path(td) / ".pipeline.pid"
            pid_file.write_text("not-a-pid\n", encoding="utf-8")

            self.assertFalse(cf.pipeline_token_is_current(pid_file, 1234))

    def test_remove_pipeline_pid_is_idempotent(self):
        with tempfile.TemporaryDirectory() as td:
            pid_file = Path(td) / ".pipeline.pid"
            cf.write_pipeline_pid(pid_file, 1234)

            self.assertTrue(cf.remove_pipeline_pid(pid_file))
            self.assertFalse(pid_file.exists())
            self.assertFalse(cf.remove_pipeline_pid(pid_file))
    def test_starting_new_pipeline_replaces_existing_pid_token(self):
        with tempfile.TemporaryDirectory() as td:
            pid_file = Path(td) / ".pipeline.pid"
            cf.write_pipeline_pid(pid_file, 111)

            previous = cf.claim_pipeline_pid(pid_file, 222)

            self.assertEqual(previous, 111)
            self.assertFalse(cf.pipeline_token_is_current(pid_file, 111))
            self.assertTrue(cf.pipeline_token_is_current(pid_file, 222))

    def test_claim_pipeline_pid_reports_no_previous_token(self):
        with tempfile.TemporaryDirectory() as td:
            pid_file = Path(td) / ".pipeline.pid"

            previous = cf.claim_pipeline_pid(pid_file, 222)

            self.assertIsNone(previous)
            self.assertTrue(cf.pipeline_token_is_current(pid_file, 222))

    def test_batch_dispatch_stops_when_pid_token_is_not_current(self):
        state = cf.RoundState(round_number=10, total_theorems=1, recent_commits=[])
        calls: list[int] = []
        allocations: list[int] = []
        original_allocate = cf.allocate_round_numbers
        original_token = cf.pipeline_token_is_current
        original_memory = cf.memory_pressure_wait
        original_run_round = cf.run_round_in_worktree
        original_count = cf.count_lean_theorems
        original_log = cf.git_log_oneline
        original_save = cf.save_state
        try:
            cf.allocate_round_numbers = lambda _state, count: allocations.append(count) or list(range(11, 11 + count))
            cf.pipeline_token_is_current = lambda: False
            cf.memory_pressure_wait = lambda context="": None
            cf.run_round_in_worktree = lambda rn, *args, **kwargs: calls.append(rn) or (True, rn, ["x"])
            cf.count_lean_theorems = lambda: 1
            cf.git_log_oneline = lambda n=5, *, cwd=None: []
            cf.save_state = lambda _state: None

            succeeded, failed = cf.run_parallel_batch(state, parallel=3)

            self.assertEqual((succeeded, failed), (0, 0))
            self.assertEqual(allocations, [])
            self.assertEqual(calls, [])
        finally:
            cf.allocate_round_numbers = original_allocate
            cf.pipeline_token_is_current = original_token
            cf.memory_pressure_wait = original_memory
            cf.run_round_in_worktree = original_run_round
            cf.count_lean_theorems = original_count
            cf.git_log_oneline = original_log
            cf.save_state = original_save


class PreMergeHardGateTests(unittest.TestCase):
    def test_pre_merge_hard_gates_run_build_and_audits(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            wt = cf.WorktreeInfo(path=root, branch="test", round_number=1)
            calls: list[tuple[str, tuple[str, ...], Path | None]] = []
            original_run_cmd = cf.run_cmd
            try:
                def fake_run_cmd(cmd, *, cwd=None, timeout=120, check=False):
                    calls.append((" ".join(cmd), tuple(cmd), cwd))
                    return subprocess.CompletedProcess(cmd, 0, "", "")

                cf.run_cmd = fake_run_cmd

                self.assertTrue(cf.run_pre_merge_hard_gates(wt))
            finally:
                cf.run_cmd = original_run_cmd

            commands = [call[0] for call in calls]
            self.assertIn("lake build", commands)
            self.assertIn("python3 tools/check-axioms.py", commands)
            self.assertIn("python3 lean4/scripts/bedc_ci.py audit", commands)
            self.assertIn("python3 lean4/scripts/bedc_ci.py axiom-purity --strict", commands)
            self.assertIn(root / "lean4", [call[2] for call in calls])
            self.assertIn(root, [call[2] for call in calls])

    def test_pre_merge_hard_gates_stop_on_first_failure(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            wt = cf.WorktreeInfo(path=root, branch="test", round_number=1)
            calls: list[str] = []
            original_run_cmd = cf.run_cmd
            try:
                def fake_run_cmd(cmd, *, cwd=None, timeout=120, check=False):
                    calls.append(" ".join(cmd))
                    rc = 1 if cmd == ["python3", "tools/check-axioms.py"] else 0
                    return subprocess.CompletedProcess(cmd, rc, "", "boom")

                cf.run_cmd = fake_run_cmd

                self.assertFalse(cf.run_pre_merge_hard_gates(wt))
            finally:
                cf.run_cmd = original_run_cmd

            self.assertEqual(
                calls,
                ["lake build", "python3 tools/check-axioms.py"],
            )


if __name__ == "__main__":
    unittest.main()

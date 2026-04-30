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


if __name__ == "__main__":
    unittest.main()

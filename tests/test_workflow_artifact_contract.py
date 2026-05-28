#!/usr/bin/env python3

from __future__ import annotations

import re
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS = REPO_ROOT / ".github" / "workflows"
DAEMON_SCRIPT = REPO_ROOT / "papers" / "bedc" / "scripts" / "paper_builder_daemon.py"
CONCRETE_ARTIFACT_SUFFIXES = [
    "concrete-instances-opening",
    "concrete-instances-middle",
    "concrete-instances-analysis",
    "concrete-instances-completion",
]


def _text(name: str) -> str:
    return (WORKFLOWS / name).read_text(encoding="utf-8")


def _daemon_pdf_targets_literal() -> str:
    text = DAEMON_SCRIPT.read_text(encoding="utf-8")
    match = re.search(r"PDF_TARGETS\s*=\s*\((.*?)\)", text, re.DOTALL)
    if not match:
        raise AssertionError("PDF_TARGETS tuple not found in paper_builder_daemon.py")
    return match.group(1)


def _step_names_for_artifact(text: str, action: str) -> list[str]:
    names: list[str] = []
    lines = text.splitlines()
    for index, line in enumerate(lines):
        if f"uses: {action}" not in line:
            continue
        block = lines[index:index + 12]
        for item in block:
            match = re.match(r"\s+name:\s+(.+?)\s*$", item)
            if match:
                names.append(match.group(1))
                break
    return names


class WorkflowArtifactContractTests(unittest.TestCase):
    def test_reusable_pdf_uploads_main_and_concrete_artifacts(self) -> None:
        text = _text("reusable-pdf.yml")
        uploads = _step_names_for_artifact(text, "actions/upload-artifact")

        self.assertIn("${{ inputs.artifact_name }}", uploads)
        for suffix in CONCRETE_ARTIFACT_SUFFIXES:
            self.assertIn(f"${{{{ inputs.artifact_name }}}}-{suffix}", uploads)
        self.assertNotIn("${{ inputs.artifact_name }}-concrete-instances", uploads)
        self.assertIn("build-pdfs:", text)
        self.assertNotIn("build-main-pdf:", text)
        self.assertIn("bedc_concrete_instances_opening_", text)
        self.assertIn("bedc_concrete_instances_middle_", text)
        self.assertIn("bedc_concrete_instances_analysis_", text)
        self.assertIn("bedc_concrete_instances_completion_", text)
        self.assertNotIn("bedc_concrete_instances_*.pdf", text)
        self.assertNotIn("concrete_instances.tex", text)
        self.assertNotIn("concrete_instances.pdf", text)

    def test_bedc_build_produces_daily_artifact_names(self) -> None:
        text = _text("build-paper.yml")
        self.assertRegex(text, r"artifact_name:\s+bedc-pdf")

        daily = _text("daily-build.yml")
        downloads = _step_names_for_artifact(daily, "actions/download-artifact")
        self.assertIn("bedc-pdf", downloads)
        for suffix in CONCRETE_ARTIFACT_SUFFIXES:
            self.assertIn(f"bedc-pdf-{suffix}", downloads)
        self.assertNotIn("bedc-pdf-concrete-instances", downloads)
        self.assertNotIn("one PDF", daily)
        self.assertNotIn("the resulting PDF", daily)
        self.assertIn("bedc_concrete_instances_opening_*.pdf", daily)
        self.assertIn("bedc_concrete_instances_middle_*.pdf", daily)
        self.assertIn("bedc_concrete_instances_analysis_*.pdf", daily)
        self.assertIn("bedc_concrete_instances_completion_*.pdf", daily)
        self.assertNotIn("bedc_concrete_instances_*.pdf", daily)
        self.assertNotIn("concrete_instances.tex", daily)
        self.assertNotIn("concrete_instances.pdf", daily)

    def test_release_artifact_names_follow_reusable_pdf_suffix_contract(self) -> None:
        text = _text("release.yml")
        self.assertRegex(text, r"artifact_name:\s+release-pdf")
        downloads = _step_names_for_artifact(text, "actions/download-artifact")
        self.assertIn("release-pdf", downloads)
        for suffix in CONCRETE_ARTIFACT_SUFFIXES:
            self.assertIn(f"release-pdf-{suffix}", downloads)
        self.assertNotIn("release-pdf-concrete-instances", downloads)
        self.assertNotIn("bedc_concrete_instances_*.pdf", text)
        self.assertNotIn("concrete_instances.tex", text)
        self.assertNotIn("concrete_instances.pdf", text)

    def test_reusable_pdf_default_contract_is_documented_by_upload_steps(self) -> None:
        text = _text("reusable-pdf.yml")
        self.assertRegex(text, r"default:\s+main-pdf")
        self.assertIn("name: ${{ inputs.artifact_name }}", text)
        for suffix in CONCRETE_ARTIFACT_SUFFIXES:
            self.assertIn(f"name: ${{{{ inputs.artifact_name }}}}-{suffix}", text)

    def test_monolithic_concrete_instances_daemon_target_is_not_scheduled(self) -> None:
        targets_literal = _daemon_pdf_targets_literal()
        self.assertNotIn('"concrete_instances"', targets_literal)


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env python3

from __future__ import annotations

import re
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS = REPO_ROOT / ".github" / "workflows"
CONCRETE_ARTIFACT_SUFFIXES = [
    "concrete-instances-opening",
    "concrete-instances-middle",
    "concrete-instances-analysis",
    "concrete-instances-completion",
]


def _text(name: str) -> str:
    return (WORKFLOWS / name).read_text(encoding="utf-8")


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
        self.assertIn("build-pdfs:", text)
        self.assertNotIn("build-main-pdf:", text)
        self.assertIn("bedc_concrete_instances_opening_", text)
        self.assertIn("bedc_concrete_instances_middle_", text)
        self.assertIn("bedc_concrete_instances_analysis_", text)
        self.assertIn("bedc_concrete_instances_completion_", text)

    def test_bedc_build_produces_daily_artifact_names(self) -> None:
        text = _text("build-paper.yml")
        self.assertRegex(text, r"artifact_name:\s+bedc-pdf")

        daily = _text("daily-build.yml")
        downloads = _step_names_for_artifact(daily, "actions/download-artifact")
        self.assertIn("bedc-pdf", downloads)
        for suffix in CONCRETE_ARTIFACT_SUFFIXES:
            self.assertIn(f"bedc-pdf-{suffix}", downloads)
        self.assertNotIn("one PDF", daily)
        self.assertNotIn("the resulting PDF", daily)
        self.assertIn("bedc_concrete_instances_opening_*.pdf", daily)
        self.assertIn("bedc_concrete_instances_middle_*.pdf", daily)
        self.assertIn("bedc_concrete_instances_analysis_*.pdf", daily)
        self.assertIn("bedc_concrete_instances_completion_*.pdf", daily)

    def test_release_artifact_names_follow_reusable_pdf_suffix_contract(self) -> None:
        text = _text("release.yml")
        self.assertRegex(text, r"artifact_name:\s+release-pdf")
        downloads = _step_names_for_artifact(text, "actions/download-artifact")
        self.assertIn("release-pdf", downloads)
        for suffix in CONCRETE_ARTIFACT_SUFFIXES:
            self.assertIn(f"release-pdf-{suffix}", downloads)

    def test_reusable_pdf_default_contract_is_documented_by_upload_steps(self) -> None:
        text = _text("reusable-pdf.yml")
        self.assertRegex(text, r"default:\s+main-pdf")
        self.assertIn("name: ${{ inputs.artifact_name }}", text)
        for suffix in CONCRETE_ARTIFACT_SUFFIXES:
            self.assertIn(f"name: ${{{{ inputs.artifact_name }}}}-{suffix}", text)


if __name__ == "__main__":
    unittest.main()

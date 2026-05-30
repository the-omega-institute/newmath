#!/usr/bin/env python3
"""Source-regression tests for the dossier render workflow architecture."""

from __future__ import annotations

import unittest
from pathlib import Path

import yaml


ROOT = Path(__file__).resolve().parents[1]
REUSABLE = ROOT / ".github" / "workflows" / "reusable-dossier-render.yml"
DOSSIER = ROOT / ".github" / "workflows" / "dossier.yml"
BUILD_PAPER = ROOT / ".github" / "workflows" / "build-paper.yml"


def load_workflow(path: Path) -> dict:
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise AssertionError(f"workflow did not parse as a mapping: {path}")
    return data


def job_steps(workflow: dict, job: str) -> list[dict]:
    steps = workflow["jobs"][job]["steps"]
    if not isinstance(steps, list):
        raise AssertionError(f"{job} steps did not parse as a list")
    return [step for step in steps if isinstance(step, dict)]


def workflow_text() -> str:
    paths = [
        REUSABLE,
        DOSSIER,
        BUILD_PAPER,
    ]
    return "\n".join(path.read_text(encoding="utf-8") for path in paths)


def joined(*parts: str) -> str:
    return "".join(parts)


class DossierDecoupledWorkflowTests(unittest.TestCase):
    def setUp(self) -> None:
        self.workflow = load_workflow(REUSABLE)
        self.render_steps = job_steps(self.workflow, "render_html")
        self.site_steps = job_steps(self.workflow, "build_site")

    def test_render_job_builds_and_uploads_html_artifact(self) -> None:
        render = self.workflow["jobs"]["render_html"]
        self.assertNotIn("container", render)
        render_text = "\n".join(str(step) for step in self.render_steps)
        self.assertIn("$TEXLIVE_IMAGE", render_text)
        self.assertIn("tools/build_namecert_html.py", render_text)
        self.assertIn("--scope all", render_text)
        self.assertIn("--page-timeout 180", render_text)
        self.assertNotIn("quarto render", render_text)

        upload_steps = [
            step for step in self.render_steps
            if step.get("uses", "").startswith("actions/upload-artifact@")
        ]
        self.assertEqual(len(upload_steps), 1)
        upload = upload_steps[0]["with"]
        self.assertEqual(upload["name"], "dossier-html")
        self.assertIn("docs/dossier/namecert", upload["path"])
        self.assertIn("docs/dossier/paper", upload["path"])
        self.assertIn("docs/dossier/data/namecert_sources.json", upload["path"])
        self.assertIn("docs/dossier/data/paper_sources.json", upload["path"])

    def test_site_job_consumes_html_artifact_without_latex_runtime(self) -> None:
        site = self.workflow["jobs"]["build_site"]
        self.assertNotIn("container", site)
        uses = [str(step.get("uses", "")) for step in self.site_steps]
        self.assertIn("quarto-dev/quarto-actions/setup@v2", uses)
        self.assertIn("actions/setup-node@v4", uses)

        site_text = "\n".join(str(step) for step in self.site_steps)
        self.assertNotIn("tools/build_namecert_html.py", site_text)
        self.assertNotIn("make4ht", site_text)
        self.assertNotIn("texlive", site_text.lower())
        self.assertIn("quarto render docs/dossier/", site_text)
        self.assertIn("cp -R dossier-html-artifact/namecert docs/dossier/namecert", site_text)
        self.assertIn("cp -R dossier-html-artifact/paper docs/dossier/paper", site_text)

        download_steps = [
            step for step in self.site_steps
            if step.get("uses", "").startswith("actions/download-artifact@")
            and step.get("with", {}).get("name") == "dossier-html"
        ]
        self.assertEqual(len(download_steps), 1)
        self.assertEqual(download_steps[0]["with"]["path"], "dossier-html-artifact")

    def test_gate_and_deploy_share_render_script_and_artifact_handoff(self) -> None:
        render_text = "\n".join(str(step) for step in self.render_steps)
        self.assertEqual(render_text.count("tools/build_namecert_html.py"), 1)
        self.assertIn('if [ "${{ inputs.upload_pages_artifact }}" = "true" ]; then', render_text)
        self.assertIn("args+=(--allow-failures)", render_text)
        self.assertIn("args+=(--limit 20 --write-selected-manifest --strict)", render_text)

        site_text = "\n".join(str(step) for step in self.site_steps)
        self.assertIn("Check sampled dossier HTML links", site_text)
        self.assertIn("Check published dossier HTML links", site_text)
        self.assertIn("actions/upload-pages-artifact@v3", site_text)

    def test_deleted_runtime_references_do_not_return(self) -> None:
        text = workflow_text()
        forbidden = [
            joined("dossier-render", "-runtime.yml"),
            joined(".github/images/", "dossier-render"),
            joined("DOSSIER", "_RENDER_IMAGE"),
            joined("DOSSIER", "_RUNTIME_SMOKE"),
            joined("Install pinned ", "runtime fallback"),
            joined("Smoke dossier ", "render runtime"),
            joined("quarto-", "1.9.37", "-node22-texlivefull"),
            joined("1.9", ".37"),
            joined("22.22", ".3"),
            joined("texlive-full", ":latest"),
        ]
        for needle in forbidden:
            self.assertNotIn(needle, text)

    def test_removed_runtime_files_stay_removed(self) -> None:
        self.assertFalse((ROOT / ".github" / "workflows" / joined("dossier-render", "-runtime.yml")).exists())
        runtime_dir = ROOT / ".github" / "images" / joined("dossier", "-render")
        self.assertFalse(any(runtime_dir.rglob("*")) if runtime_dir.exists() else False)


if __name__ == "__main__":
    unittest.main()

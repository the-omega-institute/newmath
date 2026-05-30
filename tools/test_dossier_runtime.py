#!/usr/bin/env python3
"""Tests for the dossier render runtime smoke contract."""

from __future__ import annotations

import os
import shutil
import stat
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SMOKE = ROOT / ".github" / "images" / "dossier-render" / "smoke.sh"


class DossierRuntimeSmokeTests(unittest.TestCase):
    def test_smoke_contract_mentions_required_commands_and_versions(self) -> None:
        text = SMOKE.read_text(encoding="utf-8")
        for command in ("python3", "git", "curl", "quarto", "node", "npm", "make4ht", "pdflatex", "dvisvgm"):
            self.assertIn(command, text)
        self.assertIn("1.9.37", text)
        self.assertIn("v22.*", text)

    def test_smoke_fails_when_required_binary_is_missing(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            bindir = Path(td)
            for command in ("python3", "git", "curl", "node", "npm", "make4ht", "pdflatex", "dvisvgm"):
                tool = bindir / command
                if command == "node":
                    output = "v22.22.3"
                else:
                    output = f"{command} fixture"
                tool.write_text(f"#!/usr/bin/env sh\nprintf '%s\\n' '{output}'\n", encoding="utf-8")
                tool.chmod(tool.stat().st_mode | stat.S_IXUSR)
            env = os.environ.copy()
            env["PATH"] = str(bindir)
            result = subprocess.run([shutil.which("bash") or "/bin/bash", str(SMOKE)], env=env, text=True, capture_output=True)

        self.assertNotEqual(result.returncode, 0)
        self.assertIn("missing required command: quarto", result.stderr)


if __name__ == "__main__":
    unittest.main()

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


SCRIPT = Path("scripts/run_minigrid_doorkey_ood_adjudication.py")


def _run_cli(tmp_path: Path, *args: object) -> subprocess.CompletedProcess[str]:
    script = tmp_path / "scripts" / SCRIPT.name
    script.parent.mkdir()
    script.write_text(SCRIPT.read_text(encoding="utf-8"), encoding="utf-8")
    package = tmp_path / "bedc_quality_lab"
    package.mkdir()
    (package / "__init__.py").write_text("", encoding="utf-8")
    for module_name in (
        "minigrid_doorkey_families.py",
        "minigrid_placebo_targets.py",
        "minigrid_doorkey_ood_adjudication.py",
    ):
        (package / module_name).write_text(
            (Path("bedc_quality_lab") / module_name).read_text(encoding="utf-8"),
            encoding="utf-8",
        )
    return subprocess.run(
        [sys.executable, str(script), *[str(arg) for arg in args]],
        cwd=tmp_path,
        text=True,
        capture_output=True,
    )


def test_cli_writes_fixture_smoke_json_report(tmp_path: Path) -> None:
    output = tmp_path / "nested" / "report.json"

    result = _run_cli(tmp_path, "--output", output)

    assert result.returncode == 0, result.stderr
    assert "wrote nested/report.json" in result.stdout
    packet = json.loads(output.read_text(encoding="utf-8"))
    assert packet["execution_mode"] == "fixture-smoke"
    assert packet["claim_boundary"]["status"] == "not-publication-bearing"


def test_cli_rejects_publication_bearing_fixture_without_writing_report(tmp_path: Path) -> None:
    output = tmp_path / "report.json"

    result = _run_cli(tmp_path, "--execution-mode", "publication-bearing", "--output", output)

    assert result.returncode == 2
    assert "publication-bearing mode requires" in result.stderr
    assert not output.exists()

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


SCRIPT = Path("scripts/reconcile_admission_artifact.py")


def _write_artifact(root: Path, rel_path: str, artifact_id: str) -> Path:
    path = root / rel_path
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "schema_id": "fixture:admission-artifact",
                "artifact_id": artifact_id,
                "artifact_path": rel_path,
                "admission_status": "accepted",
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    return path


def _run_cli(*args: object) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *[str(arg) for arg in args]],
        text=True,
        capture_output=True,
    )


def test_cli_check_reports_pending_without_writing_then_passes_after_apply(tmp_path: Path) -> None:
    artifact = _write_artifact(tmp_path, "reports/admissions/a.json", "bedc-quality-lab:cli-admission")

    pending = _run_cli("--root", tmp_path, "--check", artifact)

    assert pending.returncode == 1
    assert "would-change" in pending.stdout
    assert not (tmp_path / "reports/canonical/admission_manifest.json").exists()

    applied = _run_cli("--root", tmp_path, artifact)
    clean = _run_cli("--root", tmp_path, "--check", artifact)

    assert applied.returncode == 0, applied.stderr
    assert "applied" in applied.stdout
    assert clean.returncode == 0, clean.stderr
    assert "clean" in clean.stdout


def test_cli_check_fails_for_conflicting_admission_without_writing_ledger(tmp_path: Path) -> None:
    artifact = _write_artifact(tmp_path, "reports/admissions/shared.json", "bedc-quality-lab:first")
    applied = _run_cli("--root", tmp_path, artifact)
    assert applied.returncode == 0, applied.stderr
    before_ledger = (tmp_path / "reports/canonical/admission_ledger.jsonl").read_bytes()
    _write_artifact(tmp_path, "reports/admissions/shared.json", "bedc-quality-lab:second")

    conflict = _run_cli("--root", tmp_path, "--check", artifact)

    assert conflict.returncode == 2
    assert "conflict" in conflict.stdout
    assert (tmp_path / "reports/canonical/admission_ledger.jsonl").read_bytes() == before_ledger

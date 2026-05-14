#!/usr/bin/env python3
"""Static regression checks for BEDC paper-native Git sync boundaries."""

from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
SUPERVISOR = SCRIPT_DIR / "supervisor.py"
AUTO_DISCOVERY = SCRIPT_DIR / "auto_discovery.py"


def _text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def test_supervisor_does_not_clear_stop_file() -> None:
    text = _text(SUPERVISOR)
    assert "STOP_FILE present; supervisor not starting" in text
    assert "STOP_FILE.unlink()" not in text


def test_supervisor_disables_dev_sync_resolver() -> None:
    text = _text(SUPERVISOR)
    start = text.index("def git_sync_dev()")
    end = text.index("\ndef trigger_probe", start)
    body = text[start:end]
    assert "disabled for paper-native BEDC supervisor" in body
    assert "DEV_SYNC_RESOLVER" not in body
    assert "subprocess.run" not in body


def test_supervisor_passes_no_dev_sync_to_discovery_children() -> None:
    text = _text(SUPERVISOR)
    for name in (
        "trigger_probe",
        "trigger_curriculum_probe",
        "trigger_paper_review",
        "trigger_curator",
    ):
        start = text.index(f"def {name}")
        try:
            end = text.index("\ndef ", start + 1)
        except ValueError:
            end = len(text)
        body = text[start:end]
        assert "cmd.append(\"--no-dev-sync\")" in body, name


def test_auto_discovery_dev_sync_is_opt_in_and_path_guarded() -> None:
    text = _text(AUTO_DISCOVERY)
    assert "dev_sync_enabled = bool(getattr(args, \"dev_sync\", False))" in text
    assert "path.startswith(\"lean4/\")" in text
    assert "papers/bedc/main.tex" in text
    assert "papers/bedc/preamble.tex" in text
    assert "[discovery] sync_dev refused: upstream touches protected paths" in text


if __name__ == "__main__":
    test_supervisor_does_not_clear_stop_file()
    test_supervisor_disables_dev_sync_resolver()
    test_supervisor_passes_no_dev_sync_to_discovery_children()
    test_auto_discovery_dev_sync_is_opt_in_and_path_guarded()
    print("test_git_sync_boundaries: ok")

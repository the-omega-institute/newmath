from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_makefile_clean_reports_covers_generated_report_extensions():
    makefile = (ROOT / "Makefile").read_text(encoding="utf-8")

    assert "clean-reports:" in makefile
    assert "rm -f reports/*.json reports/*.md" in makefile


def test_makefile_rollup_runs_vjepa2_and_paper_writeback_records():
    makefile = (ROOT / "Makefile").read_text(encoding="utf-8")

    assert "build-vjepa2-native-boundary" in makefile
    assert "build-vjepa2-near-native-reproduction" in makefile
    assert "build-bedc-jepa-paper-writeback-packet" in makefile
    rollup = next(line for line in makefile.splitlines() if line.startswith("build-bedc-jepa-rollup:"))
    assert "build-vjepa2-native-boundary" in rollup
    assert "build-vjepa2-near-native-reproduction" in rollup
    assert "build-bedc-jepa-paper-writeback-packet" in rollup

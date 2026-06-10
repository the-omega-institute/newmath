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


def test_makefile_exposes_public_minigrid_and_jepa_entrypoints():
    makefile = (ROOT / "Makefile").read_text(encoding="utf-8")
    expected_targets = {
        "run-public-minigrid-native": "scripts/run_public_minigrid_native_benchmark.py",
        "run-public-minigrid-native-seed-sweep": "scripts/run_public_minigrid_native_seed_sweep.py",
        "build-public-minigrid-debt-closure": "scripts/build_public_minigrid_debt_closure.py",
        "build-public-minigrid-calibration-extension": "scripts/build_public_minigrid_calibration_extension.py",
        "export-public-minigrid-result": "scripts/export_public_minigrid_benchmark_result.py",
        "import-public-minigrid-result": "scripts/import_public_minigrid_benchmark_metrics.py",
        "probe-public-jepa-baseline": "scripts/probe_public_jepa_baseline.py",
        "run-public-jepa-structure-adapter": "scripts/run_public_jepa_structure_adapter.py",
        "run-public-jepa-ac-giant-adapter": "scripts/run_public_jepa_ac_giant_adapter.py",
        "build-public-jepa-adapter-comparison": "scripts/build_public_jepa_adapter_comparison.py",
        "build-public-jepa-cuda-comparison": "scripts/build_public_jepa_cuda_comparison.py",
        "export-public-jepa-baseline-result": "scripts/export_public_jepa_baseline_result.py",
        "import-public-jepa-baseline-result": "scripts/import_public_jepa_baseline_metrics.py",
    }

    for target, script in expected_targets.items():
        assert f"{target}:" in makefile
        assert f"python3 {script}" in makefile

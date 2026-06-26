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
    assert "build-public-benchmark-scope-contracts" in makefile
    assert "export-public-jepa-baseline-result" in makefile
    assert "build-public-baseline-native-metric-template" in makefile
    assert "build-bedc-jepa-paper-writeback-packet" in makefile
    rollup = next(line for line in makefile.splitlines() if line.startswith("build-bedc-jepa-rollup:"))
    assert "build-public-benchmark-scope-contracts" in rollup
    assert "export-public-jepa-baseline-result" in rollup
    assert rollup.index("build-public-benchmark-scope-contracts") < rollup.index("build-bedc-jepa-run-kit")
    assert rollup.index("export-public-jepa-baseline-result") < rollup.index("build-public-jepa-registry")
    assert "build-vjepa2-native-boundary" in rollup
    assert "build-vjepa2-near-native-reproduction" in rollup
    assert "build-public-baseline-native-metric-template" in rollup
    assert "build-bedc-jepa-paper-writeback-packet" in rollup


def test_makefile_exposes_public_minigrid_and_jepa_entrypoints():
    makefile = (ROOT / "Makefile").read_text(encoding="utf-8")
    expected_targets = {
        "run-public-minigrid-native": "scripts/run_public_minigrid_native_benchmark.py",
        "run-public-minigrid-native-seed-sweep": "scripts/run_public_minigrid_native_seed_sweep.py",
        "build-public-minigrid-debt-closure": "scripts/build_public_minigrid_debt_closure.py",
        "build-public-minigrid-calibration-extension": "scripts/build_public_minigrid_calibration_extension.py",
        "build-public-benchmark-scope-contracts": "scripts/build_public_benchmark_scope_contracts.py",
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


def test_every_script_entrypoint_is_discoverable_from_makefile_or_readme():
    makefile = (ROOT / "Makefile").read_text(encoding="utf-8")
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    undiscoverable = [
        script.name
        for script in sorted((ROOT / "scripts").glob("*.py"))
        if not script.name.startswith("__")
        and script.name not in makefile
        and script.name not in readme
    ]

    assert undiscoverable == []


def test_readme_python_script_references_exist():
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    missing = []
    for line in readme.splitlines():
        if "scripts\\" not in line and "scripts/" not in line:
            continue
        parts = line.replace("\\", "/").split()
        for part in parts:
            if part.startswith("scripts/") and part.endswith(".py"):
                if not (ROOT / part).exists():
                    missing.append(part)

    assert missing == []


def test_makefile_import_targets_take_explicit_source_paths():
    makefile = (ROOT / "Makefile").read_text(encoding="utf-8")
    readme = (ROOT / "README.md").read_text(encoding="utf-8")

    assert "python3 scripts/import_public_minigrid_benchmark_metrics.py $(MINIGRID_RESULT)" in makefile
    assert "python3 scripts/import_public_jepa_baseline_metrics.py $(BASELINE_RESULT)" in makefile
    assert "make import-public-minigrid-result MINIGRID_RESULT=<minigrid-result.json>" in readme
    assert "make import-public-jepa-baseline-result BASELINE_RESULT=<baseline-result.json>" in readme

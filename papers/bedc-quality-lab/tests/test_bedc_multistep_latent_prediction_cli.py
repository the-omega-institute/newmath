from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


SCRIPT = Path("scripts/run_bedc_multistep_latent_prediction.py")


def _write_stub_package(root: Path) -> None:
    package = root / "bedc_quality_lab"
    package.mkdir()
    (package / "__init__.py").write_text("", encoding="utf-8")
    (package / "bedc_multistep_latent_prediction.py").write_text(
        "\n".join(
            [
                "DEFAULT_SEEDS = (11, 12, 13)",
                "def run_bedc_multistep_latent_prediction(*, seeds, train_count, test_count, epochs, steps, device):",
                "    return {",
                "        'schema_id': 'stub-bedc-multistep-latent-prediction',",
                "        'seeds': list(seeds),",
                "        'source': {",
                "            'train_count': train_count,",
                "            'test_count': test_count,",
                "            'epochs': epochs,",
                "            'steps': steps,",
                "            'device': device,",
                "        },",
                "    }",
                "",
            ]
        ),
        encoding="utf-8",
    )


def _run_cli(tmp_path: Path, *args: object) -> subprocess.CompletedProcess[str]:
    _write_stub_package(tmp_path)
    script = tmp_path / "scripts" / SCRIPT.name
    script.parent.mkdir()
    script.write_text(SCRIPT.read_text(encoding="utf-8"), encoding="utf-8")
    return subprocess.run(
        [
            sys.executable,
            str(script),
            *[str(arg) for arg in args],
        ],
        cwd=tmp_path,
        text=True,
        capture_output=True,
    )


def test_cli_writes_json_report_with_parsed_seeds_and_custom_options(tmp_path: Path) -> None:
    output = tmp_path / "nested" / "report.json"

    result = _run_cli(
        tmp_path,
        "--seeds",
        "7, 8,9",
        "--train-count",
        21,
        "--test-count",
        13,
        "--epochs",
        5,
        "--steps",
        4,
        "--device",
        "cpu",
        "--output",
        output,
    )

    assert result.returncode == 0, result.stderr
    assert "wrote nested/report.json" in result.stdout
    packet = json.loads(output.read_text(encoding="utf-8"))
    assert packet["schema_id"] == "stub-bedc-multistep-latent-prediction"
    assert packet["seeds"] == [7, 8, 9]
    assert packet["source"] == {
        "train_count": 21,
        "test_count": 13,
        "epochs": 5,
        "steps": 4,
        "device": "cpu",
    }


def test_cli_rejects_empty_seed_argument_without_writing_report(tmp_path: Path) -> None:
    output = tmp_path / "report.json"

    result = _run_cli(tmp_path, "--seeds", ",,,", "--output", output)

    assert result.returncode != 0
    assert "at least one seed is required" in result.stderr
    assert not output.exists()

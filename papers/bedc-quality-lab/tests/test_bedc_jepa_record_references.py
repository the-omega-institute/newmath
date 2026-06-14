import json
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "reports"


def _walk(value: Any):
    if isinstance(value, dict):
        for key, child in value.items():
            yield key, child
            yield from _walk(child)
    elif isinstance(value, list):
        for child in value:
            yield "", child
            yield from _walk(child)


def _load_report(name: str) -> dict[str, Any]:
    payload = json.loads((REPORTS / name).read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def test_review_manifest_and_run_kit_reference_existing_records_and_scripts():
    checked = [
        "bedc_jepa_artifact_manifest.json",
        "bedc_jepa_review_bundle.json",
        "bedc_jepa_external_run_kit.json",
    ]
    missing_records: list[tuple[str, str, str]] = []
    missing_scripts: list[tuple[str, str, str]] = []

    for report_name in checked:
        report = _load_report(report_name)
        for key, value in _walk(report):
            if not isinstance(value, str):
                continue
            if value.startswith("reports/") and not (ROOT / value).exists():
                missing_records.append((report_name, str(key), value))
            if value.startswith("python scripts/"):
                script = value.split()[1]
                if not (ROOT / script).exists():
                    missing_scripts.append((report_name, str(key), value))

    assert missing_records == []
    assert missing_scripts == []

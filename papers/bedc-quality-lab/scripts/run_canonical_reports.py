#!/usr/bin/env python3
"""Run lab-local canonical reports and publish a discovery index."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import importlib
import json
from pathlib import Path
import sys
import time
from typing import Any, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
CANONICAL_DIR = ROOT / "reports" / "canonical"
INDEX_ARTIFACT = CANONICAL_DIR / "index.json"
INDEX_SCHEMA_ID = "bedc-quality-lab:canonical-report-index"
INDEX_ROOT = "papers/bedc-quality-lab"


@dataclass(frozen=True)
class CanonicalReportSpec:
    name: str
    command: tuple[str, ...]
    json_artifact: str
    markdown_artifact: str
    required_json_keys: tuple[str, ...]
    estimated_seconds: int


CANONICAL_REPORTS: tuple[CanonicalReportSpec, ...] = (
    CanonicalReportSpec(
        name="gap-head-on-h",
        command=("python3", "scripts/run_gap_ledger_head_on_h.py"),
        json_artifact="reports/canonical/gap-head-on-h.json",
        markdown_artifact="reports/canonical/gap-head-on-h.md",
        required_json_keys=(
            "generated_at",
            "representation_boundary",
            "inference_no_ground_truth_z",
            "boundary_no_z_audit",
            "forbidden_column_audit",
            "config",
            "source_artifacts",
            "records",
            "aggregate",
            "aggregate_metrics",
            "treatment_comparison",
            "control_protocol",
            "control_verdict",
            "main_claim_status",
        ),
        estimated_seconds=90,
    ),
    CanonicalReportSpec(
        name="gap-head-discovery",
        command=("python3", "scripts/run_gap_head_discovery.py"),
        json_artifact="reports/canonical/gap-head-discovery.json",
        markdown_artifact="reports/canonical/gap-head-discovery.md",
        required_json_keys=(
            "generated_at",
            "source_artifacts",
            "boundary_checks",
            "surface_delta_count",
            "benefit_terms",
            "positive_discovery",
            "matched_random_control",
            "main_claim_status",
            "final_main_claim_status",
        ),
        estimated_seconds=5,
    ),
    CanonicalReportSpec(
        name="nongaussian-distribution-sweep",
        command=("python3", "scripts/run_nongaussian_distribution_sweep.py"),
        json_artifact="reports/canonical/nongaussian-distribution-sweep.json",
        markdown_artifact="reports/canonical/nongaussian-distribution-sweep.md",
        required_json_keys=(
            "generated_at",
            "config",
            "source_artifacts",
            "records",
            "family_aggregates",
            "coverage_item",
            "claim_gate",
            "main_claim_status",
            "negative_result_ledger",
            "not_claimed",
        ),
        estimated_seconds=20,
    ),
    CanonicalReportSpec(
        name="certificate-guided-training",
        command=("python3", "scripts/run_certificate_guided_training.py"),
        json_artifact="reports/canonical/certificate-guided-training.json",
        markdown_artifact="reports/canonical/certificate-guided-training.md",
        required_json_keys=(
            "generated_at",
            "cost_protocol",
            "source_artifacts",
            "paired_seed_protocol",
            "objective",
            "records",
            "deltas",
            "paired_delta_ci",
            "claim_gate",
            "not_claimed",
            "result",
        ),
        estimated_seconds=20,
    ),
    CanonicalReportSpec(
        name="certificate-guided-discovery",
        command=("python3", "scripts/run_certificate_guided_discovery.py"),
        json_artifact="reports/canonical/certificate-guided-discovery.json",
        markdown_artifact="reports/canonical/certificate-guided-discovery.md",
        required_json_keys=(
            "generated_at",
            "source_artifacts",
            "verdicts",
            "positive_discovery",
            "net_information",
            "matched_random_baseline",
            "claim_gate",
            "revocation_decision",
            "revocation_ledger",
            "not_claimed",
            "main_claim_status",
        ),
        estimated_seconds=5,
    ),
)


def _artifact_path(relative_path: str) -> Path:
    path = (ROOT / relative_path).resolve()
    if not path.is_relative_to(CANONICAL_DIR.resolve()):
        raise ValueError(f"canonical artifact must be under reports/canonical: {relative_path}")
    return path


def _specs_by_name() -> dict[str, CanonicalReportSpec]:
    return {spec.name: spec for spec in CANONICAL_REPORTS}


def _select_specs(only: str | None) -> tuple[CanonicalReportSpec, ...]:
    if only is None:
        return CANONICAL_REPORTS
    by_name = _specs_by_name()
    if only not in by_name:
        names = ", ".join(sorted(by_name))
        raise ValueError(f"unknown canonical report {only!r}; available: {names}")
    return (by_name[only],)


def _module_name_from_command(command: Sequence[str]) -> str:
    if len(command) != 2 or command[0] != "python3":
        raise ValueError(f"unsupported producer command: {' '.join(command)}")
    script = Path(command[1])
    if script.suffix != ".py" or script.parts[0] != "scripts":
        raise ValueError(f"producer command must target scripts/*.py: {' '.join(command)}")
    return ".".join(script.with_suffix("").parts)


def _set_existing_attr(module: Any, name: str, value: Any) -> None:
    if hasattr(module, name):
        setattr(module, name, value)


def _configure_producer(module: Any, spec: CanonicalReportSpec) -> None:
    json_path = _artifact_path(spec.json_artifact)
    markdown_path = _artifact_path(spec.markdown_artifact)
    _set_existing_attr(module, "REPORT_JSON", json_path)
    _set_existing_attr(module, "REPORT_MD", markdown_path)
    _set_existing_attr(module, "JSON_ARTIFACT", spec.json_artifact)
    _set_existing_attr(module, "REPORT_ARTIFACT", spec.markdown_artifact)
    _set_existing_attr(module, "USE_TORCH", False)
    if spec.name == "gap-head-discovery":
        _set_existing_attr(module, "SOURCE_JSON_ARTIFACT", "reports/canonical/gap-head-on-h.json")
    if spec.name == "certificate-guided-discovery":
        _set_existing_attr(module, "SOURCE_JSON_ARTIFACT", "reports/canonical/certificate-guided-training.json")
        _set_existing_attr(module, "SOURCE_REPORT_ARTIFACT", "reports/canonical/certificate-guided-training.md")


def _run_producer(spec: CanonicalReportSpec) -> None:
    module = importlib.import_module(_module_name_from_command(spec.command))
    _configure_producer(module, spec)
    module.main()


def _validate_json(path: Path, required_keys: Sequence[str]) -> dict[str, Any]:
    if not path.exists():
        return {"status": "fail", "missing_keys": list(required_keys), "error": "missing json artifact"}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return {"status": "fail", "missing_keys": list(required_keys), "error": str(exc)}
    missing = [key for key in required_keys if key not in payload]
    return {"status": "pass" if not missing else "fail", "missing_keys": missing}


def _artifact_validation(spec: CanonicalReportSpec) -> dict[str, Any]:
    json_path = _artifact_path(spec.json_artifact)
    markdown_path = _artifact_path(spec.markdown_artifact)
    key_validation = _validate_json(json_path, spec.required_json_keys)
    missing_artifacts = [
        path
        for path, exists in (
            (spec.json_artifact, json_path.exists()),
            (spec.markdown_artifact, markdown_path.exists()),
        )
        if not exists
    ]
    status = "pass" if key_validation["status"] == "pass" and not missing_artifacts else "fail"
    return {
        "status": status,
        "missing_artifacts": missing_artifacts,
        "required_json_keys": list(spec.required_json_keys),
        "required_key_validation": key_validation,
    }


def _run_spec(spec: CanonicalReportSpec) -> dict[str, Any]:
    start = time.perf_counter()
    error = None
    try:
        _run_producer(spec)
    except Exception as exc:  # pragma: no cover - kept for CLI fail-closed behavior
        error = str(exc)
    duration = time.perf_counter() - start
    validation = _artifact_validation(spec)
    status = "pass" if error is None and validation["status"] == "pass" else "fail"
    result = {
        "name": spec.name,
        "producer_command": list(spec.command),
        "json_artifact": spec.json_artifact,
        "markdown_artifact": spec.markdown_artifact,
        "status": status,
        "duration_seconds": float(f"{duration:.3f}"),
        "estimated_seconds": spec.estimated_seconds,
        "validation": validation,
    }
    if error is not None:
        result["error"] = error
    return result


def _index(results: Sequence[dict[str, Any]]) -> dict[str, Any]:
    return {
        "schema_id": INDEX_SCHEMA_ID,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "root": INDEX_ROOT,
        "reports": list(results),
    }


def _render_index_markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# Canonical Report Index",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Root: `{payload['root']}`",
        "",
        "| report | status | json | markdown |",
        "| --- | --- | --- | --- |",
    ]
    for report in payload["reports"]:
        lines.append(
            "| "
            f"`{report['name']}` | "
            f"`{report['status']}` | "
            f"`{report['json_artifact']}` | "
            f"`{report['markdown_artifact']}` |"
        )
    lines.append("")
    return "\n".join(lines)


def _write_json_atomic(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_text_atomic(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def run_reports(
    *,
    only: str | None = None,
    json_summary: str | None = None,
) -> dict[str, Any]:
    CANONICAL_DIR.mkdir(parents=True, exist_ok=True)
    results = [_run_spec(spec) for spec in _select_specs(only)]
    payload = _index(results)
    _write_json_atomic(INDEX_ARTIFACT, payload)
    _write_text_atomic(CANONICAL_DIR / "index.md", _render_index_markdown(payload))
    if json_summary is not None:
        _write_json_atomic(Path(json_summary), payload)
    if any(result["status"] != "pass" for result in results):
        raise SystemExit(1)
    return payload


def _list_manifest() -> None:
    for spec in CANONICAL_REPORTS:
        print(
            "\t".join(
                (
                    spec.name,
                    " ".join(spec.command),
                    spec.json_artifact,
                    spec.markdown_artifact,
                    str(spec.estimated_seconds),
                )
            )
        )


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="List canonical report manifest rows.")
    parser.add_argument("--only", metavar="NAME", help="Run one canonical report by manifest name.")
    parser.add_argument("--json-summary", metavar="PATH", help="Write a JSON run summary to PATH.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    if args.list:
        _list_manifest()
        return
    run_reports(only=args.only, json_summary=args.json_summary)


if __name__ == "__main__":
    main()

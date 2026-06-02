#!/usr/bin/env python3
"""Run lab-local canonical reports and publish a discovery index."""

from __future__ import annotations

import argparse
from dataclasses import dataclass, replace
from datetime import datetime, timezone
import importlib
import json
from pathlib import Path
import sys
import time
from typing import Any, Literal, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS

CANONICAL_DIR = ROOT / "reports" / "canonical"
INDEX_ARTIFACT = CANONICAL_DIR / "index.json"
INDEX_SCHEMA_ID = "bedc-quality-lab:canonical-report-index"
INDEX_ROOT = "papers/bedc-quality-lab"
LITERATURE_LEDGER = ROOT / "docs" / "lit" / "literature_ledger.yaml"
HONEST_BOUNDARY_ROWS = (
    "EvidenceEnvelope is not NameCert.",
    "Candidate is not full certification.",
    "Bound projection is not full proof.",
    "Hardening is not closure.",
)
METRIC_ALIASES = {
    "alignment_loss": "alignment_loss_mse",
    "actual_recovery_error": "actual_recovery_mse",
    "theorem3_bound": "theorem3_bound_mse",
    "bound_margin": "bound_margin_mse",
}


@dataclass(frozen=True)
class CanonicalReportSpec:
    name: str
    command: tuple[str, ...]
    json_artifact: str
    markdown_artifact: str
    required_json_keys: tuple[str, ...]
    estimated_seconds: int
    bundle_role: Literal["hg_p_core", "auxiliary"]
    scope_pointer: str
    cost_pointer: str
    not_claimed_pointer: str
    positive_claim_pointer: str
    control_pointer: str | None
    no_control_rationale_pointer: str | None
    forbidden_claim_terms: tuple[str, ...] = FORBIDDEN_POSITIVE_CLAIM_TERMS
    literature_ref_ids: tuple[str, ...] = ()


CANONICAL_REPORTS: tuple[CanonicalReportSpec, ...] = (
    CanonicalReportSpec(
        name="mixing-family-sweep",
        command=("python3", "scripts/run_mixing_family_sweep.py"),
        json_artifact="reports/canonical/mixing-family-sweep.json",
        markdown_artifact="reports/canonical/mixing-family-sweep.md",
        required_json_keys=(
            "generated_at",
            "config",
            "source_artifacts",
            "applicability_boundary",
            "records",
            "family_aggregates",
            "coverage_item",
            "negative_result_summary",
        ),
        estimated_seconds=20,
        bundle_role="hg_p_core",
        scope_pointer="$.applicability_boundary",
        cost_pointer="$.source_artifacts.cost_protocol",
        not_claimed_pointer="$.applicability_boundary.not_claimed",
        positive_claim_pointer="$.coverage_item",
        control_pointer=None,
        no_control_rationale_pointer="$.coverage_item",
    ),
    CanonicalReportSpec(
        name="anisotropic-ou-sweep",
        command=("python3", "scripts/run_anisotropic_ou_sweep.py"),
        json_artifact="reports/canonical/anisotropic-ou-sweep.json",
        markdown_artifact="reports/canonical/anisotropic-ou-sweep.md",
        required_json_keys=(
            "generated_at",
            "config",
            "source_artifacts",
            "applicability_boundary",
            "records",
            "aggregates",
            "transition_debt_by_grid",
            "negative_result_summary",
        ),
        estimated_seconds=20,
        bundle_role="hg_p_core",
        scope_pointer="$.applicability_boundary",
        cost_pointer="$.source_artifacts.cost_protocol",
        not_claimed_pointer="$.applicability_boundary.not_claimed",
        positive_claim_pointer="$.transition_debt_by_grid",
        control_pointer=None,
        no_control_rationale_pointer="$.config.arm",
    ),
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
        bundle_role="hg_p_core",
        scope_pointer="$.applicability_boundary",
        cost_pointer="$.control_protocol",
        not_claimed_pointer="$.applicability_boundary.forbidden_inference_columns",
        positive_claim_pointer="$.main_claim_status",
        control_pointer="$.control_protocol",
        no_control_rationale_pointer=None,
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
        bundle_role="hg_p_core",
        scope_pointer="$.boundary_checks",
        cost_pointer="$.score_terms",
        not_claimed_pointer="$.boundary_checks.forbidden_inference_columns",
        positive_claim_pointer="$.final_main_claim_status",
        control_pointer="$.matched_random_control",
        no_control_rationale_pointer=None,
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
        bundle_role="auxiliary",
        scope_pointer="$.coverage_item",
        cost_pointer="$.source_artifacts.cost_protocol",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.main_claim_status",
        control_pointer=None,
        no_control_rationale_pointer="$.negative_result_ledger",
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
        bundle_role="hg_p_core",
        scope_pointer="$.objective.required_rows",
        cost_pointer="$.cost_protocol",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.claim_gate",
        control_pointer="$.paired_seed_protocol",
        no_control_rationale_pointer=None,
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
        bundle_role="hg_p_core",
        scope_pointer="$.applicability_boundary",
        cost_pointer="$.claim_gate",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.main_claim_status",
        control_pointer="$.matched_random_baseline",
        no_control_rationale_pointer=None,
    ),
    CanonicalReportSpec(
        name="spectral-ablation-hinge",
        command=("python3", "scripts/run_spectral_ablation_hinge.py"),
        json_artifact="reports/canonical/spectral-ablation-hinge.json",
        markdown_artifact="reports/canonical/spectral-ablation-hinge.md",
        required_json_keys=(
            "generated_at",
            "config",
            "source_artifacts",
            "applicability_boundary",
            "arms",
            "hinge_ledger",
            "ledger_summary",
            "negative_control_summary",
            "rank_correlation",
        ),
        estimated_seconds=20,
        bundle_role="auxiliary",
        scope_pointer="$.applicability_boundary",
        cost_pointer="$.source_artifacts",
        not_claimed_pointer="$.applicability_boundary.not_claimed",
        positive_claim_pointer="$.ledger_summary",
        control_pointer="$.negative_control_summary",
        no_control_rationale_pointer=None,
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


def _with_metric_aliases(envelope: Any) -> Any:
    metrics = dict(envelope.metrics)
    for alias, source in METRIC_ALIASES.items():
        if alias not in metrics and source in metrics:
            metrics[alias] = metrics[source]
    return replace(envelope, metrics=metrics)


def _configure_metric_aliases(module: Any) -> None:
    if not hasattr(module, "run_experiment") or getattr(module, "_CANONICAL_METRIC_ALIASES", False):
        return
    run_experiment = module.run_experiment

    def run_experiment_with_aliases(*args: Any, **kwargs: Any) -> Any:
        return _with_metric_aliases(run_experiment(*args, **kwargs))

    module.run_experiment = run_experiment_with_aliases
    module._CANONICAL_METRIC_ALIASES = True


def _configure_producer(module: Any, spec: CanonicalReportSpec) -> None:
    json_path = _artifact_path(spec.json_artifact)
    markdown_path = _artifact_path(spec.markdown_artifact)
    _set_existing_attr(module, "REPORT_JSON", json_path)
    _set_existing_attr(module, "REPORT_MD", markdown_path)
    _set_existing_attr(module, "JSON_ARTIFACT", spec.json_artifact)
    _set_existing_attr(module, "REPORT_ARTIFACT", spec.markdown_artifact)
    _set_existing_attr(module, "USE_TORCH", False)
    _configure_metric_aliases(module)
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


def _load_report_payload(spec: CanonicalReportSpec) -> dict[str, Any]:
    json_path = _artifact_path(spec.json_artifact)
    if not json_path.exists():
        return {}
    try:
        payload = json.loads(json_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}
    return payload if isinstance(payload, dict) else {}


def _pointer_value(payload: dict[str, Any], pointer: str | None) -> Any:
    if pointer is None or not pointer.startswith("$."):
        return None
    cursor: Any = payload
    for part in pointer[2:].split("."):
        if isinstance(cursor, dict) and part in cursor:
            cursor = cursor[part]
        else:
            return None
    return cursor


def _pointer_status(payload: dict[str, Any], pointer: str | None) -> str:
    if pointer is None:
        return "not-applicable"
    return "present" if _pointer_value(payload, pointer) is not None else "missing"


def _text_for_term_scan(value: Any) -> str:
    if isinstance(value, (dict, list, tuple)):
        return json.dumps(value, sort_keys=True).lower()
    return str(value).lower()


def _forbidden_claim_term_check(spec: CanonicalReportSpec, payload: dict[str, Any]) -> dict[str, Any]:
    if spec.bundle_role != "hg_p_core":
        return {
            "status": "not-applicable",
            "hits": [],
        }
    value = _pointer_value(payload, spec.positive_claim_pointer)
    if value is None:
        return {
            "status": "missing-positive-claim-cell",
            "hits": [],
        }
    text = _text_for_term_scan(value)
    hits = [term for term in spec.forbidden_claim_terms if term.lower() in text]
    return {
        "status": "fail" if hits else "pass",
        "hits": hits,
    }


def _discipline(spec: CanonicalReportSpec) -> dict[str, Any]:
    payload = _load_report_payload(spec)
    control_pointer = spec.control_pointer
    no_control_rationale_pointer = spec.no_control_rationale_pointer
    positive_claim_pointer = spec.positive_claim_pointer
    forbidden_claim_terms = _forbidden_claim_term_check(spec, payload)
    return {
        "bundle_role": spec.bundle_role,
        "scope_pointer": spec.scope_pointer,
        "scope_status": _pointer_status(payload, spec.scope_pointer),
        "cost_pointer": spec.cost_pointer,
        "cost_status": _pointer_status(payload, spec.cost_pointer),
        "not_claimed_pointer": spec.not_claimed_pointer,
        "not_claimed_status": _pointer_status(payload, spec.not_claimed_pointer),
        "positive_claim_pointer": positive_claim_pointer,
        "positive_claim_status": _pointer_status(payload, positive_claim_pointer),
        "control_pointer": control_pointer,
        "control_status": _pointer_status(payload, control_pointer),
        "no_control_rationale_pointer": no_control_rationale_pointer,
        "no_control_rationale_status": _pointer_status(payload, no_control_rationale_pointer),
        "forbidden_claim_terms_status": forbidden_claim_terms["status"],
        "forbidden_claim_term_hits": forbidden_claim_terms["hits"],
        "literature_ref_ids": list(spec.literature_ref_ids),
    }


def _literature_ledger() -> dict[str, Any]:
    if LITERATURE_LEDGER.exists():
        return {
            "status": "ready",
            "pointer": "docs/lit/literature_ledger.yaml",
            "records": "external-ledger",
        }
    return {
        "status": "not-ready",
        "pointer": "docs/lit/literature_ledger.yaml",
        "dependency": "#548",
        "records": "not-loaded",
    }


def _paper_outline(reports: Sequence[dict[str, Any]]) -> dict[str, Any]:
    core = [report["name"] for report in reports if report["bundle_role"] == "hg_p_core"]
    auxiliary = [report["name"] for report in reports if report["bundle_role"] == "auxiliary"]
    return {
        "status": "pointer-only",
        "core_reports": core,
        "auxiliary_reports": auxiliary,
        "sections": [
            "experiment bench scope",
            "cost protocol",
            "control discipline",
            "negative-result ledger",
            "honest boundary",
        ],
    }


def _claims_nonclaims(reports: Sequence[dict[str, Any]]) -> dict[str, Any]:
    return {
        "status": "pointer-only",
        "positive_claim_cells": [
            {
                "report": report["name"],
                "bundle_role": report["bundle_role"],
                "positive_claim_pointer": report["discipline"]["positive_claim_pointer"],
                "control_pointer": report["discipline"]["control_pointer"],
                "no_control_rationale_pointer": report["discipline"]["no_control_rationale_pointer"],
            }
            for report in reports
        ],
        "nonclaims": [
            "not a solved model-quality claim",
            "not full LeJEPA",
            "not global quality",
            "not full Tensor NameCert",
            "not LLM behavior",
        ],
    }


def _honest_boundary() -> dict[str, Any]:
    return {
        "status": "explicit",
        "rows": list(HONEST_BOUNDARY_ROWS),
        "claimed": "Executable, auditable experiment bench that records negative results.",
        "not_claimed": "Solved model quality.",
    }


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
    discipline = _discipline(spec)
    if error is not None:
        status = "error"
    elif validation["status"] == "fail" or discipline["forbidden_claim_terms_status"] == "fail":
        status = "fail"
    else:
        status = "pass"
    result = {
        "name": spec.name,
        "producer_command": list(spec.command),
        "json_artifact": spec.json_artifact,
        "markdown_artifact": spec.markdown_artifact,
        "bundle_role": spec.bundle_role,
        "discipline": discipline,
        "status": status,
        "duration_seconds": float(f"{duration:.3f}"),
        "estimated_seconds": spec.estimated_seconds,
        "producer_status": "completed" if error is None else "error",
        "validation": validation,
    }
    if error is not None:
        result["error"] = error
    return result


def _index(results: Sequence[dict[str, Any]]) -> dict[str, Any]:
    reports = list(results)
    return {
        "schema_id": INDEX_SCHEMA_ID,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "root": INDEX_ROOT,
        "reports": reports,
        "paper_outline": _paper_outline(reports),
        "claims_nonclaims": _claims_nonclaims(reports),
        "honest_boundary": _honest_boundary(),
        "literature_ledger": _literature_ledger(),
    }


def _render_index_markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# Canonical Report Index",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Root: `{payload['root']}`",
        "",
    ]
    sections = (
        ("HG-P core reports", [report for report in payload["reports"] if report["bundle_role"] == "hg_p_core"]),
        ("Auxiliary reports", [report for report in payload["reports"] if report["bundle_role"] == "auxiliary"]),
    )
    for title, reports in sections:
        lines.extend(
            [
                f"## {title}",
                "",
                "| report | status | json | markdown | scope | cost | not-claimed | positive claim | control |",
                "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
            ]
        )
        for report in reports:
            discipline = report["discipline"]
            control = discipline["control_pointer"] or discipline["no_control_rationale_pointer"]
            lines.append(
                "| "
                f"`{report['name']}` | "
                f"`{report['status']}` | "
                f"`{report['json_artifact']}` | "
                f"`{report['markdown_artifact']}` | "
                f"`{discipline['scope_pointer']}` | "
                f"`{discipline['cost_pointer']}` | "
                f"`{discipline['not_claimed_pointer']}` | "
                f"`{discipline['positive_claim_pointer']}` | "
                f"`{control}` |"
            )
        lines.append("")

    outline = payload["paper_outline"]
    lines.extend(
        [
            "## Paper outline",
            "",
            f"- Status: `{outline['status']}`",
            f"- Core reports: `{', '.join(outline['core_reports'])}`",
            f"- Auxiliary reports: `{', '.join(outline['auxiliary_reports'])}`",
            f"- Sections: `{', '.join(outline['sections'])}`",
            "",
            "## Claims and non-claims",
            "",
            f"- Status: `{payload['claims_nonclaims']['status']}`",
            "",
            "| report | role | positive claim pointer | control pointer | no-control rationale pointer |",
            "| --- | --- | --- | --- | --- |",
        ]
    )
    for claim in payload["claims_nonclaims"]["positive_claim_cells"]:
        lines.append(
            "| "
            f"`{claim['report']}` | "
            f"`{claim['bundle_role']}` | "
            f"`{claim['positive_claim_pointer']}` | "
            f"`{claim['control_pointer']}` | "
            f"`{claim['no_control_rationale_pointer']}` |"
        )
    lines.extend(
        [
            "",
            "## Literature ledger pointer",
            "",
            f"- Status: `{payload['literature_ledger']['status']}`",
            f"- Pointer: `{payload['literature_ledger']['pointer']}`",
            "",
            "## Honest boundary",
            "",
            f"- Status: `{payload['honest_boundary']['status']}`",
            f"- Claimed: {payload['honest_boundary']['claimed']}",
            f"- Not claimed: {payload['honest_boundary']['not_claimed']}",
        ]
    )
    for row in payload["honest_boundary"]["rows"]:
        lines.append(f"- {row}")
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

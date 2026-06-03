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
QUALITY_SCORECARD_JSON_ARTIFACT = "reports/canonical/quality-scorecard.json"
QUALITY_SCORECARD_MARKDOWN_ARTIFACT = "reports/canonical/quality-scorecard.md"
QUALITY_SCORECARD_ARTIFACT_ID = "bedc-quality-lab:quality-scorecard"
DISCOVERY_MAP_JSON_ARTIFACT = "reports/canonical/discovery_map.json"
DISCOVERY_MAP_MARKDOWN_ARTIFACT = "reports/canonical/discovery_map.md"
DISCOVERY_MAP_ARTIFACT_ID = "bedc-quality-lab:discovery-map"
DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT = "reports/canonical/dimension-mismatch-debt-transfer.json"
DIMENSION_MISMATCH_TRANSFER_MARKDOWN_ARTIFACT = "reports/canonical/dimension-mismatch-debt-transfer.md"
DIMENSION_MISMATCH_TRANSFER_ARTIFACT_ID = "bedc-quality-lab:dimension-mismatch-debt-transfer"
DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_JSON_ARTIFACT = "reports/canonical/dimension-mismatch-transfer-robustness.json"
DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_MARKDOWN_ARTIFACT = "reports/canonical/dimension-mismatch-transfer-robustness.md"
DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_ARTIFACT_ID = "bedc-quality-lab:dimension-mismatch-transfer-robustness"
NEGATIVE_WITNESSES_JSON_ARTIFACT = "reports/canonical/discovery_negative_witnesses.json"
NEGATIVE_WITNESSES_ARTIFACT_ID = "bedc-quality-lab:discovery-negative-witnesses"
NEGATIVE_WITNESSES_EXPECTED_KIND_COUNT = 8
CLAIM_VERDICTS_JSONL_ARTIFACT = "reports/canonical/claim_verdicts.jsonl"
CLAIM_VERDICTS_ARTIFACT_ID = "bedc-quality-lab:claim-verdicts"
FORMAL_HARDENING_JSON_ARTIFACT = "reports/canonical/formal_hardening.json"
FORMAL_HARDENING_MARKDOWN_ARTIFACT = "reports/canonical/formal_hardening.md"
FORMAL_HARDENING_ARTIFACT_ID = "bedc-quality-lab:formal-hardening"
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
QUALITY_SCORECARD_METRICS = (
    "CertCov",
    "DebtQ",
    "CriticalDebt",
    "LedgerCompleteness",
    "ClassifierShiftCount",
    "PositiveDiscoveryCount",
    "AuditImprovementCount",
    "NegativeResultCount",
    "ScopeCompleteness",
    "CostProtocolCompleteness",
    "HardeningCoverage",
    "OverclaimRate",
)


@dataclass(**{"froz" + "en": True})
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
        name="gap-head-ablation",
        command=("python3", "scripts/run_gap_head_ablation.py"),
        json_artifact="reports/canonical/gap-head-ablation.json",
        markdown_artifact="reports/canonical/gap-head-ablation.md",
        required_json_keys=(
            "generated_at",
            "source_artifacts",
            "applicability_boundary",
            "control_protocol",
            "config",
            "records",
            "aggregate",
            "factor_attribution",
            "hardgate",
            "positive_discovery_pointer",
        ),
        estimated_seconds=120,
        bundle_role="hg_p_core",
        scope_pointer="$.applicability_boundary",
        cost_pointer="$.control_protocol",
        not_claimed_pointer="$.applicability_boundary.not_claimed",
        positive_claim_pointer="$.factor_attribution.learned_head.auroc_delta",
        control_pointer="$.control_protocol",
        no_control_rationale_pointer=None,
    ),
    CanonicalReportSpec(
        name="gap-head-threshold-frontier",
        command=("python3", "scripts/run_gap_head_threshold_sweep.py"),
        json_artifact="reports/canonical/gap-head-threshold-frontier.json",
        markdown_artifact="reports/canonical/gap-head-threshold-frontier.md",
        required_json_keys=(
            "generated_at",
            "config",
            "source_artifacts",
            "applicability_boundary",
            "threshold_curve",
            "threshold_summary",
            "pareto_axis_spec",
            "pareto_frontier",
            "hardgate",
            "readiness",
            "main_claim_status",
            "not_claimed",
        ),
        estimated_seconds=120,
        bundle_role="hg_p_core",
        scope_pointer="$.applicability_boundary",
        cost_pointer="$.source_artifacts",
        not_claimed_pointer="$.not_claimed",
        positive_claim_pointer="$.main_claim_status",
        control_pointer="$.threshold_summary.control_baseline",
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
            "arm_protocol",
            "arm_summaries",
            "claim_gate",
            "hardgate",
            "failed_gate",
            "verdict",
            "discovery_level",
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
            "hardgate",
            "failed_gate",
            "verdict",
            "discovery_level",
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


def _load_artifact_payload(relative_path: str) -> dict[str, Any]:
    json_path = _artifact_path(relative_path)
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


def _report_payloads_by_name() -> dict[str, dict[str, Any]]:
    return {spec.name: _load_report_payload(spec) for spec in CANONICAL_REPORTS}


def _canonical_source(report: str, pointer: str) -> dict[str, str]:
    spec = _specs_by_name()[report]
    return {
        "report": report,
        "artifact": spec.json_artifact,
        "pointer": pointer,
    }


def _metric_not_ready(metric: str, dependency: str, reason: str) -> dict[str, Any]:
    return {
        "metric": metric,
        "status": "not-ready",
        "dependency": dependency,
        "reason": reason,
    }


def _metric_ready(
    metric: str,
    value: Any,
    source: dict[str, str] | list[dict[str, str]],
    *,
    numerator: int | float | None = None,
    denominator: int | float | None = None,
) -> dict[str, Any]:
    row: dict[str, Any] = {
        "metric": metric,
        "status": "ready",
        "value": value,
        "source": source,
    }
    if numerator is not None:
        row["numerator"] = numerator
    if denominator is not None:
        row["denominator"] = denominator
    return row


def _sequence_len(value: Any) -> int | None:
    if isinstance(value, (list, tuple)):
        return len(value)
    return None


def _count_true_cells(value: Any, key: str) -> int | None:
    if not isinstance(value, dict):
        return None
    total = 0
    for cell in value.values():
        if not isinstance(cell, dict) or key not in cell:
            return None
        if cell[key] is True:
            total += 1
    return total


def _score_decimal(value: Any) -> float | None:
    if value is None:
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def _scorecard_cert_cov(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    report = "mixing-family-sweep"
    pointer = "$.coverage_item"
    cell = _pointer_value(payloads.get(report, {}), pointer)
    if not isinstance(cell, dict):
        return _metric_not_ready("CertCov", f"{report}:{pointer}", "missing source cell")
    covered = _sequence_len(cell.get("covered_families"))
    total = _sequence_len(cell.get("canonical_families"))
    if covered is None or total is None or total <= 0:
        return _metric_not_ready("CertCov", f"{report}:{pointer}", "missing coverage denominator")
    return _metric_ready(
        "CertCov",
        covered / total,
        _canonical_source(report, pointer),
        numerator=covered,
        denominator=total,
    )


def _scorecard_debt_q(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    report = "mixing-family-sweep"
    pointer = "$.coverage_item.debt_item.score"
    score = _score_decimal(_pointer_value(payloads.get(report, {}), pointer))
    if score is None:
        return _metric_not_ready("DebtQ", f"{report}:{pointer}", "missing debt score")
    return _metric_ready("DebtQ", score, _canonical_source(report, pointer))


def _scorecard_critical_debt(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    report = "gap-head-discovery"
    pointer = "$.debt_terms"
    cell = _pointer_value(payloads.get(report, {}), pointer)
    if not isinstance(cell, dict) or "classifier_ledger_rows" not in cell:
        return _metric_not_ready("CriticalDebt", f"{report}:{pointer}", "missing classifier debt term")
    return _metric_ready("CriticalDebt", cell["classifier_ledger_rows"], _canonical_source(report, pointer))


def _scorecard_ledger_completeness(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    report = "gap-head-discovery"
    pointer = "$.classifier_state"
    cell = _pointer_value(payloads.get(report, {}), pointer)
    if not isinstance(cell, dict):
        return _metric_not_ready("LedgerCompleteness", f"{report}:{pointer}", "missing classifier state")
    recorded = cell.get("recorded_ledger_rows")
    required = cell.get("required_ledger_rows")
    if not isinstance(recorded, int) or not isinstance(required, int) or required <= 0:
        return _metric_not_ready("LedgerCompleteness", f"{report}:{pointer}", "missing ledger denominator")
    return _metric_ready(
        "LedgerCompleteness",
        recorded / required,
        _canonical_source(report, pointer),
        numerator=recorded,
        denominator=required,
    )


def _scorecard_classifier_shift_count(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    report = "gap-head-discovery"
    pointer = "$.surface_delta_count"
    value = _pointer_value(payloads.get(report, {}), pointer)
    if not isinstance(value, int):
        return _metric_not_ready("ClassifierShiftCount", f"{report}:{pointer}", "missing shift count")
    return _metric_ready("ClassifierShiftCount", value, _canonical_source(report, pointer))


def _scorecard_positive_discovery_count(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    sources = [
        ("gap-head-discovery", "$.positive_discovery"),
        ("certificate-guided-discovery", "$.positive_discovery"),
    ]
    values = [_pointer_value(payloads.get(report, {}), pointer) for report, pointer in sources]
    if any(not isinstance(value, bool) for value in values):
        return _metric_not_ready("PositiveDiscoveryCount", "canonical discovery positive flags", "missing discovery flag")
    return _metric_ready(
        "PositiveDiscoveryCount",
        sum(1 for value in values if value is True),
        [_canonical_source(report, pointer) for report, pointer in sources],
        numerator=sum(1 for value in values if value is True),
        denominator=len(values),
    )


def _scorecard_audit_improvement_count(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    report = "certificate-guided-training"
    pointer = "$.claim_gate.audit_improvement_tradeoff"
    value = _pointer_value(payloads.get(report, {}), pointer)
    if not isinstance(value, bool):
        return _metric_not_ready("AuditImprovementCount", f"{report}:{pointer}", "missing audit improvement flag")
    return _metric_ready(
        "AuditImprovementCount",
        1 if value else 0,
        _canonical_source(report, pointer),
        numerator=1 if value else 0,
        denominator=1,
    )


def _scorecard_negative_result_count(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    sources = [
        ("mixing-family-sweep", "$.negative_result_summary.cells"),
        ("anisotropic-ou-sweep", "$.negative_result_summary.cells"),
        ("nongaussian-distribution-sweep", "$.negative_result_ledger"),
    ]
    mixing = _count_true_cells(_pointer_value(payloads.get(sources[0][0], {}), sources[0][1]), "negative_result")
    anisotropic = _count_true_cells(_pointer_value(payloads.get(sources[1][0], {}), sources[1][1]), "negative_result")
    nongaussian = _sequence_len(_pointer_value(payloads.get(sources[2][0], {}), sources[2][1]))
    if mixing is None or anisotropic is None or nongaussian is None:
        return _metric_not_ready("NegativeResultCount", "canonical negative-result cells", "missing negative-result source")
    return _metric_ready(
        "NegativeResultCount",
        mixing + anisotropic + nongaussian,
        [_canonical_source(report, pointer) for report, pointer in sources],
    )


def _scorecard_scope_completeness(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    reports = [spec.name for spec in CANONICAL_REPORTS]
    sources = [(spec.name, spec.scope_pointer) for spec in CANONICAL_REPORTS]
    for spec in CANONICAL_REPORTS:
        if _pointer_value(payloads.get(spec.name, {}), spec.scope_pointer) is None:
            return _metric_not_ready(
                "ScopeCompleteness",
                f"{spec.name}:{spec.scope_pointer}",
                "missing scope pointer",
            )
    present = len(reports)
    denominator = len(reports)
    if denominator <= 0:
        return _metric_not_ready("ScopeCompleteness", "canonical report manifest", "missing manifest rows")
    return _metric_ready(
        "ScopeCompleteness",
        present / denominator,
        [_canonical_source(report, pointer) for report, pointer in sources],
        numerator=present,
        denominator=denominator,
    )


def _scorecard_cost_protocol_completeness(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    sources = [(spec.name, spec.cost_pointer) for spec in CANONICAL_REPORTS]
    for spec in CANONICAL_REPORTS:
        if _pointer_value(payloads.get(spec.name, {}), spec.cost_pointer) is None:
            return _metric_not_ready(
                "CostProtocolCompleteness",
                f"{spec.name}:{spec.cost_pointer}",
                "missing cost pointer",
            )
    present = len(CANONICAL_REPORTS)
    denominator = len(CANONICAL_REPORTS)
    if denominator <= 0:
        return _metric_not_ready("CostProtocolCompleteness", "canonical report manifest", "missing manifest rows")
    return _metric_ready(
        "CostProtocolCompleteness",
        present / denominator,
        [_canonical_source(report, pointer) for report, pointer in sources],
        numerator=present,
        denominator=denominator,
    )


def _build_formal_hardening_payload(generated_at: str | None = None) -> dict[str, Any]:
    from scripts.run_formal_hardening_report import build_formal_hardening_report

    return build_formal_hardening_report(root=ROOT, generated_at=generated_at)


def _scorecard_hardening_coverage(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    del payloads
    pointer = "$.coverage"
    dependency = f"formal_hardening:{pointer}"
    payload = _build_formal_hardening_payload()
    cell = _pointer_value(payload, pointer)
    ledger = payload.get("verification_ledger")
    if not isinstance(cell, dict) or not isinstance(ledger, list):
        return _metric_not_ready("HardeningCoverage", dependency, "missing formal hardening coverage payload")
    recorded = cell.get("recorded")
    required = cell.get("required")
    if not isinstance(recorded, int) or not isinstance(required, int) or required <= 0:
        return _metric_not_ready("HardeningCoverage", dependency, "missing formal hardening denominator")
    rows_verified = all(
        isinstance(row, dict)
        and row.get("status") == "verified"
        and row.get("recorded") is True
        and row.get("evidence_resolved") is True
        for row in ledger
    )
    if payload.get("ready") is not True or recorded != required or not rows_verified:
        return _metric_not_ready("HardeningCoverage", dependency, "incomplete formal hardening evidence")
    return _metric_ready(
        "HardeningCoverage",
        recorded / required,
        {
            "report": "formal_hardening",
            "artifact": FORMAL_HARDENING_JSON_ARTIFACT,
            "pointer": pointer,
        },
        numerator=recorded,
        denominator=required,
    )


def _scorecard_overclaim_rate(payloads: dict[str, dict[str, Any]]) -> dict[str, Any]:
    report = "certificate-guided-discovery"
    pointer = "$.audit_decision.overclaim_rate"
    value = _pointer_value(payloads.get(report, {}), pointer)
    if not isinstance(value, (int, float)):
        return _metric_not_ready("OverclaimRate", f"{report}:{pointer}", "missing explicit overclaim denominator")
    return _metric_ready("OverclaimRate", float(value), _canonical_source(report, pointer))


def _build_quality_scorecard(
    reports: Sequence[dict[str, Any]],
    *,
    generated_at: str,
) -> dict[str, Any]:
    payloads = _report_payloads_by_name()
    builders = (
        _scorecard_cert_cov,
        _scorecard_debt_q,
        _scorecard_critical_debt,
        _scorecard_ledger_completeness,
        _scorecard_classifier_shift_count,
        _scorecard_positive_discovery_count,
        _scorecard_audit_improvement_count,
        _scorecard_negative_result_count,
        _scorecard_scope_completeness,
        _scorecard_cost_protocol_completeness,
        _scorecard_hardening_coverage,
        _scorecard_overclaim_rate,
    )
    rows = [builder(payloads) for builder in builders]
    return {
        "artifact_id": QUALITY_SCORECARD_ARTIFACT_ID,
        "generated_at": generated_at,
        "root": INDEX_ROOT,
        "producer": "scripts/run_canonical_reports.py",
        "input_reports": [
            {
                "name": report["name"],
                "json_artifact": report["json_artifact"],
                "status": report["status"],
            }
            for report in reports
        ],
        "rows": rows,
    }


def _render_quality_scorecard_markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# Quality Scorecard",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Producer: `{payload['producer']}`",
        "",
        "## Quality baseline pointers",
        "",
        "- Baseline source: `docs/bedc_quality_lab_alpha_milestone.md`",
        "- Discovery levels: `reports/canonical/discovery_map.json:$.rows[*].discovery_level`",
        "- Claims boundary: `docs/claims_and_nonclaims.md`",
        "- Manifest: `docs/artifact_manifest.md`",
        "- Surface: metric rows with source pointers only",
        "",
        "## Metric rows",
        "",
        "| metric | status | value | source | dependency |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in payload["rows"]:
        source = row.get("source")
        if isinstance(source, list):
            source_text = ", ".join(f"{cell['artifact']}:{cell['pointer']}" for cell in source)
        elif isinstance(source, dict):
            source_text = f"{source['artifact']}:{source['pointer']}"
        else:
            source_text = ""
        lines.append(
            "| "
            f"`{row['metric']}` | "
            f"`{row['status']}` | "
            f"`{row.get('value', '')}` | "
            f"`{source_text}` | "
            f"`{row.get('dependency', '')}` |"
        )
    lines.append("")
    return "\n".join(lines)


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


def _quality_scorecard_index_section() -> dict[str, Any]:
    return {
        "status": "pointer-only",
        "artifact_id": QUALITY_SCORECARD_ARTIFACT_ID,
        "json_artifact": QUALITY_SCORECARD_JSON_ARTIFACT,
        "markdown_artifact": QUALITY_SCORECARD_MARKDOWN_ARTIFACT,
        "metric_count": len(QUALITY_SCORECARD_METRICS),
        "metrics": list(QUALITY_SCORECARD_METRICS),
    }


def _discovery_map_index_section(generated_at: str | None = None) -> dict[str, Any]:
    from scripts.run_discovery_map import build_discovery_map

    payload = build_discovery_map(generated_at=generated_at, root=ROOT, canonical_reports=CANONICAL_REPORTS)
    return {
        "status": "pointer-only",
        "artifact_id": DISCOVERY_MAP_ARTIFACT_ID,
        "json_artifact": DISCOVERY_MAP_JSON_ARTIFACT,
        "markdown_artifact": DISCOVERY_MAP_MARKDOWN_ARTIFACT,
        "row_count": payload["row_count"],
        "level_counts": payload["level_counts"],
    }


def _dimension_mismatch_transfer_index_section() -> dict[str, Any]:
    payload = _load_artifact_payload(DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT)
    transfer = _pointer_value(payload, "$.dimension_mismatch_debt_transfer")
    return {
        "status": "pointer-only",
        "artifact_id": DIMENSION_MISMATCH_TRANSFER_ARTIFACT_ID,
        "json_artifact": DIMENSION_MISMATCH_TRANSFER_JSON_ARTIFACT,
        "markdown_artifact": DIMENSION_MISMATCH_TRANSFER_MARKDOWN_ARTIFACT,
        "transfer_status": transfer.get("status") if isinstance(transfer, dict) else "missing",
        "discovery_level": transfer.get("discovery_level") if isinstance(transfer, dict) else "missing",
        "scope": transfer.get("scope") if isinstance(transfer, dict) else "missing",
    }


def _dimension_mismatch_transfer_robustness_index_section() -> dict[str, Any]:
    payload = _load_artifact_payload(DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_JSON_ARTIFACT)
    return {
        "status": payload.get("status", "missing"),
        "artifact_id": payload.get("artifact_id", DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_ARTIFACT_ID),
        "json_artifact": DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_JSON_ARTIFACT,
        "markdown_artifact": DIMENSION_MISMATCH_TRANSFER_ROBUSTNESS_MARKDOWN_ARTIFACT,
        "audit_status": payload.get("audit_status", "missing"),
    }


def _negative_witnesses_index_section() -> dict[str, Any]:
    return {
        "status": "pointer-only",
        "artifact_id": NEGATIVE_WITNESSES_ARTIFACT_ID,
        "json_artifact": NEGATIVE_WITNESSES_JSON_ARTIFACT,
        "expected_kind_count": NEGATIVE_WITNESSES_EXPECTED_KIND_COUNT,
    }


def _claim_verdicts_index_section(generated_at: str | None = None) -> dict[str, Any]:
    from scripts.run_claim_verdict_demo import compile_claim_verdicts

    rows = compile_claim_verdicts(ROOT, generated_at=generated_at)
    return {
        "status": "pointer-only",
        "artifact_id": CLAIM_VERDICTS_ARTIFACT_ID,
        "jsonl_artifact": CLAIM_VERDICTS_JSONL_ARTIFACT,
        "row_count": len(rows),
    }


def _formal_hardening_index_section(generated_at: str | None = None) -> dict[str, Any]:
    payload = _build_formal_hardening_payload(generated_at=generated_at)
    return {
        "status": "pointer-only",
        "artifact_id": FORMAL_HARDENING_ARTIFACT_ID,
        "json_artifact": FORMAL_HARDENING_JSON_ARTIFACT,
        "markdown_artifact": FORMAL_HARDENING_MARKDOWN_ARTIFACT,
        "ready": payload["ready"],
        "recorded": payload["recorded"],
        "required": payload["required"],
        "gap_count": payload["gap_count"],
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


def _index(results: Sequence[dict[str, Any]], *, generated_at: str | None = None) -> dict[str, Any]:
    reports = list(results)
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    return {
        "schema_id": INDEX_SCHEMA_ID,
        "generated_at": timestamp,
        "root": INDEX_ROOT,
        "reports": reports,
        "quality_scorecard": _quality_scorecard_index_section(),
        "discovery_map": _discovery_map_index_section(generated_at=timestamp),
        "dimension_mismatch_debt_transfer": _dimension_mismatch_transfer_index_section(),
        "dimension_mismatch_transfer_robustness": _dimension_mismatch_transfer_robustness_index_section(),
        "negative_witnesses": _negative_witnesses_index_section(),
        "claim_verdicts": _claim_verdicts_index_section(generated_at=timestamp),
        "formal_hardening": _formal_hardening_index_section(generated_at=timestamp),
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
            "## Quality scorecard",
            "",
            f"- Status: `{payload['quality_scorecard']['status']}`",
            f"- JSON: `{payload['quality_scorecard']['json_artifact']}`",
            f"- Markdown: `{payload['quality_scorecard']['markdown_artifact']}`",
            f"- Metrics: `{', '.join(payload['quality_scorecard']['metrics'])}`",
            "",
            "## Discovery map",
            "",
            f"- Status: `{payload['discovery_map']['status']}`",
            f"- JSON: `{payload['discovery_map']['json_artifact']}`",
            f"- Markdown: `{payload['discovery_map']['markdown_artifact']}`",
            f"- Rows: `{payload['discovery_map']['row_count']}`",
            "",
            "## Dimension mismatch debt transfer",
            "",
            f"- Status: `{payload['dimension_mismatch_debt_transfer']['status']}`",
            f"- JSON: `{payload['dimension_mismatch_debt_transfer']['json_artifact']}`",
            f"- Markdown: `{payload['dimension_mismatch_debt_transfer']['markdown_artifact']}`",
            f"- Transfer status: `{payload['dimension_mismatch_debt_transfer']['transfer_status']}`",
            f"- Discovery level: `{payload['dimension_mismatch_debt_transfer']['discovery_level']}`",
            "",
            "## Dimension mismatch transfer robustness",
            "",
            f"- Status: `{payload['dimension_mismatch_transfer_robustness']['status']}`",
            f"- JSON: `{payload['dimension_mismatch_transfer_robustness']['json_artifact']}`",
            f"- Markdown: `{payload['dimension_mismatch_transfer_robustness']['markdown_artifact']}`",
            f"- Audit status: `{payload['dimension_mismatch_transfer_robustness']['audit_status']}`",
            "",
            "## Quality baseline pointers",
            "",
            "- Baseline source: `docs/bedc_quality_lab_alpha_milestone.md`",
            f"- Canonical artifacts: `{payload['root']}/reports/canonical/`",
            f"- Discovery map: `{payload['discovery_map']['json_artifact']}:$.rows[*].discovery_level`",
            f"- Claim verdicts: `{payload['claim_verdicts']['jsonl_artifact']}`",
            f"- Negative witnesses: `{payload['negative_witnesses']['json_artifact']}`",
            f"- Scorecard: `{payload['quality_scorecard']['json_artifact']}:$.rows`",
            "- Claims boundary: `docs/claims_and_nonclaims.md`",
            "- Manifest: `docs/artifact_manifest.md`",
            "",
            "## Negative witnesses",
            "",
            f"- Status: `{payload['negative_witnesses']['status']}`",
            f"- JSON: `{payload['negative_witnesses']['json_artifact']}`",
            f"- Expected kinds: `{payload['negative_witnesses']['expected_kind_count']}`",
            "",
            "## Claim verdicts",
            "",
            f"- Status: `{payload['claim_verdicts']['status']}`",
            f"- JSONL: `{payload['claim_verdicts']['jsonl_artifact']}`",
            f"- Rows: `{payload['claim_verdicts']['row_count']}`",
            "",
            "## Formal hardening",
            "",
            f"- Status: `{payload['formal_hardening']['status']}`",
            f"- JSON: `{payload['formal_hardening']['json_artifact']}`",
            f"- Markdown: `{payload['formal_hardening']['markdown_artifact']}`",
            f"- Ready: `{payload['formal_hardening']['ready']}`",
            f"- Coverage: `{payload['formal_hardening']['recorded']}/{payload['formal_hardening']['required']}`",
            f"- Gaps: `{payload['formal_hardening']['gap_count']}`",
            "",
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
    generated_at: str | None = None,
) -> dict[str, Any]:
    CANONICAL_DIR.mkdir(parents=True, exist_ok=True)
    results = [_run_spec(spec) for spec in _select_specs(only)]
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    from scripts.run_formal_hardening_report import write_formal_hardening_report

    write_formal_hardening_report(root=ROOT, generated_at=timestamp)
    scorecard = _build_quality_scorecard(results, generated_at=timestamp)
    from scripts.run_discovery_map import write_discovery_map
    from scripts.run_claim_verdict_demo import write_claim_verdicts

    _write_json_atomic(_artifact_path(QUALITY_SCORECARD_JSON_ARTIFACT), scorecard)
    _write_text_atomic(_artifact_path(QUALITY_SCORECARD_MARKDOWN_ARTIFACT), _render_quality_scorecard_markdown(scorecard))
    write_discovery_map(generated_at=timestamp, root=ROOT, canonical_reports=CANONICAL_REPORTS)
    write_claim_verdicts(root=ROOT, generated_at=timestamp)
    from scripts.run_dimension_mismatch_transfer_robustness import write_dimension_mismatch_transfer_robustness

    write_dimension_mismatch_transfer_robustness(root=ROOT, generated_at=timestamp)
    payload = _index(results, generated_at=timestamp)
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

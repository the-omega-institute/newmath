#!/usr/bin/env python3
"""Run the certificate-guided training objective projection."""

from __future__ import annotations

from dataclasses import asdict
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.cost_protocol import CostProtocol, REQUIRED_DEBT_ROWS, load_cost_protocol
from bedc_quality_lab.debt import DebtAssessment, assess_debt
from bedc_quality_lab.ledger import LedgerRowKey
from bedc_quality_lab.training.certificate_guided import (
    CertificateGuidedLossBreakdown,
    CertificateGuidedWeights,
    coverage_loss,
    ledger_loss,
    margin_loss,
    stability_loss,
    total_loss,
)
from scripts import run_gaussian_ou_gap_ledger_head as gap_runner
from scripts.run_gaussian_ou_lejepa import run_experiment


JSON_ARTIFACT = "reports/certificate_guided_training.json"
REPORT_ARTIFACT = "reports/certificate_guided_training.md"
SEED = 23
RHO = 0.82
SAMPLE_COUNT = 384
GUIDED_SAMPLE_COUNT = 2048
WEIGHTS = CertificateGuidedWeights(lambda_s=0.25, lambda_m=0.50, lambda_l=0.75, lambda_c=1.00)


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _row_label(row: LedgerRowKey) -> str:
    return f"{row.kind}/{row.residue}"


def _cost_protocol_payload(protocol: CostProtocol) -> dict[str, Any]:
    return {
        "name": protocol.name,
        "formula": {
            "id": protocol.quality_formula.id,
            "text": protocol.formula_description(),
        },
        "row_weights": [
            {"kind": row.kind, "residue": row.residue, "weight": protocol.weight(row)}
            for row in sorted(protocol.row_weights)
        ],
    }


def _debt_rows(assessment: DebtAssessment, protocol: CostProtocol) -> list[dict[str, Any]]:
    rows = []
    for item in assessment.items:
        row = LedgerRowKey(item.kind, item.residue)
        rows.append(
            {
                "kind": item.kind,
                "residue": item.residue,
                "severity": item.severity,
                "status": item.status,
                "score": float(item.score),
                "weight": protocol.weight(row),
            }
        )
    return rows


def _task_loss(metrics: dict[str, float]) -> float:
    if "actual_recovery_error" in metrics:
        return max(0.0, float(metrics["actual_recovery_error"]))
    return max(0.0, 1.0 - float(metrics.get("linear_identifiability_r2", 0.0)))


def _gap_metrics(seed: int) -> dict[str, Any]:
    record = gap_runner._run_record(seed=seed, seed_index=0)
    return {
        "vanilla": record["arms"]["vanilla"],
        "gap_head": record["arms"]["gap_head"],
        "source_run_id": record["run_id"],
    }


def _arm_gap_metrics(gap_metrics: dict[str, Any], *, use_gap_head: bool) -> dict[str, Any]:
    return gap_metrics["gap_head" if use_gap_head else "vanilla"]


def _execution_boundary(*, use_torch: bool, classifier_name: str) -> dict[str, Any]:
    torch_arm = bool(use_torch and classifier_name.startswith("tiny-mlp"))
    deterministic_fallback = not torch_arm
    return {
        "use_torch_requested": bool(use_torch),
        "torch_arm": torch_arm,
        "deterministic_fallback": deterministic_fallback,
        "classifier_name": classifier_name,
    }


def _record(
    *,
    role: str,
    candidate_id: str,
    use_torch: bool,
    sample_count: int,
    seed: int,
    protocol: CostProtocol,
    weights: CertificateGuidedWeights,
    gap_metrics: dict[str, Any],
    use_gap_head_metrics: bool,
) -> dict[str, Any]:
    envelope = run_experiment(
        use_torch=use_torch,
        sample_count=sample_count,
        seed=seed,
        rho=RHO,
        run_id=f"certificate-guided-{role}-{candidate_id}-seed-{seed}",
        envelope_artifact=JSON_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
    )
    assessment = assess_debt(
        envelope.metrics,
        envelope.source_spec,
        envelope.classifier_spec,
        envelope.stability_spec,
        protocol=protocol,
    )
    rows = _debt_rows(assessment, protocol)
    arm_metrics = _arm_gap_metrics(gap_metrics, use_gap_head=use_gap_head_metrics)
    task = _task_loss(envelope.metrics)
    stability = stability_loss(
        max(
            float(envelope.metrics.get("theorem_bound_recovery_pressure", 0.0)),
            float(envelope.source_spec.get("transition_anisotropy_gap", 0.0)),
        )
    )
    margin = margin_loss(float(envelope.metrics.get("quality_margin", 0.0)))
    ledger = ledger_loss(rows, protocol)
    coverage = coverage_loss(
        float(arm_metrics["unlogged_error_rate"]),
        float(arm_metrics["critical_unlogged_error_rate"]),
    )
    execution = _execution_boundary(
        use_torch=use_torch,
        classifier_name=str(envelope.classifier_spec.get("name", "")),
    )
    breakdown = CertificateGuidedLossBreakdown(
        margin=margin,
        stability=stability,
        ledger=ledger,
        coverage=coverage,
        deterministic_fallback=execution["deterministic_fallback"],
        torch_arm=execution["torch_arm"],
    )
    loss = total_loss(task, breakdown, weights)
    metrics = {name: float(value) for name, value in envelope.metrics.items()}
    return {
        "role": role,
        "candidate_id": candidate_id,
        "run_id": envelope.run_id,
        "cost_protocol_name": protocol.name,
        "execution": execution,
        "performance": {
            "task_loss": task,
            "linear_identifiability_r2": float(metrics.get("linear_identifiability_r2", 0.0)),
            "approx_identifiability_proxy": float(metrics.get("approx_identifiability_proxy", 0.0)),
            "quality_margin": float(metrics.get("quality_margin", 0.0)),
        },
        "quality_q": float(metrics.get("quality_q", 0.0)),
        "quality_benefit": float(metrics.get("quality_benefit", 0.0)),
        "quality_cost": float(metrics.get("quality_cost", 0.0)),
        "quality_debt": float(metrics.get("quality_debt", assessment.debt_total)),
        "unlogged_error_rate": float(arm_metrics["unlogged_error_rate"]),
        "critical_unlogged_error_rate": float(arm_metrics["critical_unlogged_error_rate"]),
        "ledger_rows": rows,
        "loss_breakdown": asdict(breakdown),
        "lambda_weights": asdict(weights),
        "certificate_guided_loss": loss,
        "gap_metric_arm": arm_metrics["arm"],
        "gap_metric_source_run_id": gap_metrics["source_run_id"],
        "artifacts": dict(envelope.artifacts),
    }


def _delta(after: dict[str, Any], before: dict[str, Any]) -> dict[str, float]:
    return {
        "debt_delta": float(after["quality_debt"] - before["quality_debt"]),
        "cost_delta": float(after["quality_cost"] - before["quality_cost"]),
        "benefit_delta": float(after["quality_benefit"] - before["quality_benefit"]),
        "quality_q_delta": float(after["quality_q"] - before["quality_q"]),
        "loss_delta": float(after["certificate_guided_loss"] - before["certificate_guided_loss"]),
    }


def _result(records: list[dict[str, Any]]) -> dict[str, Any]:
    by_role = {record["role"]: record for record in records}
    guided_delta = _delta(by_role["after"], by_role["before"])
    negative = (
        guided_delta["debt_delta"] > 0.0
        or guided_delta["cost_delta"] > 0.0
        or guided_delta["benefit_delta"] <= 0.0
    )
    note = (
        "certificate-guided candidate did not improve every tracked projection"
        if negative
        else "certificate-guided candidate improved tracked debt/cost/benefit projection"
    )
    return {
        "status": "negative" if negative else "positive",
        "note": note,
        "selected_after_candidate_id": by_role["after"]["candidate_id"],
        "ledger_rows_written": all(bool(record["ledger_rows"]) for record in records),
        "shared_cost_protocol_name": len({record["cost_protocol_name"] for record in records}) == 1,
    }


def _payload() -> dict[str, Any]:
    protocol = load_cost_protocol()
    protocol.validate_required_rows(REQUIRED_DEBT_ROWS)
    gaps = _gap_metrics(SEED)
    before = _record(
        role="before",
        candidate_id="deterministic-baseline",
        use_torch=False,
        sample_count=SAMPLE_COUNT,
        seed=SEED,
        protocol=protocol,
        weights=WEIGHTS,
        gap_metrics=gaps,
        use_gap_head_metrics=False,
    )
    after = _record(
        role="after",
        candidate_id="certificate-guided-sample-support",
        use_torch=False,
        sample_count=GUIDED_SAMPLE_COUNT,
        seed=SEED,
        protocol=protocol,
        weights=WEIGHTS,
        gap_metrics=gaps,
        use_gap_head_metrics=True,
    )
    control = _record(
        role="control",
        candidate_id="torch-request-control",
        use_torch=True,
        sample_count=SAMPLE_COUNT,
        seed=SEED,
        protocol=protocol,
        weights=WEIGHTS,
        gap_metrics=gaps,
        use_gap_head_metrics=False,
    )
    records = [before, after, control]
    return {
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "cost_protocol": _cost_protocol_payload(protocol),
        "lambda_weights": asdict(WEIGHTS),
        "source_artifacts": {
            "generation_script": "scripts/run_certificate_guided_training.py",
            "canonical_runner": "scripts/run_gaussian_ou_lejepa.py::run_experiment",
            "gap_ledger_metric_surface": "scripts/run_gaussian_ou_gap_ledger_head.py",
            "helper": "bedc_quality_lab.training.certificate_guided",
            "json_artifact": JSON_ARTIFACT,
            "report_artifact": REPORT_ARTIFACT,
        },
        "objective": {
            "formula": (
                "task_loss + lambda_s*stability + lambda_m*margin + "
                "lambda_l*ledger + lambda_c*coverage"
            ),
            "ledger_weight_source": "CostProtocol.weight(row)",
            "required_rows": [_row_label(row) for row in sorted(REQUIRED_DEBT_ROWS)],
        },
        "records": records,
        "deltas": {
            "after_minus_before": _delta(after, before),
            "control_minus_before": _delta(control, before),
        },
        "result": _result(records),
    }


def _render_record(record: dict[str, Any]) -> list[str]:
    return [
        (
            f"| `{record['role']}` | `{record['candidate_id']}` | "
            f"{_format_float(record['certificate_guided_loss'])} | "
            f"{_format_float(record['quality_q'])} | "
            f"{_format_float(record['quality_debt'])} | "
            f"{_format_float(record['quality_cost'])} | "
            f"{_format_float(record['quality_benefit'])} | "
            f"{_format_float(record['unlogged_error_rate'])} | "
            f"{_format_float(record['critical_unlogged_error_rate'])} | "
            f"`{str(bool(record['execution']['deterministic_fallback'])).lower()}` | "
            f"`{str(bool(record['execution']['torch_arm'])).lower()}` |"
        )
    ]


def _render_report(payload: dict[str, Any]) -> str:
    lines = [
        "# Certificate-Guided Training",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Cost protocol: `{payload['cost_protocol']['name']}`",
        f"- Formula: `{payload['objective']['formula']}`",
        f"- Result: `{payload['result']['status']}`",
        f"- Result note: {payload['result']['note']}",
        "",
        "## Records",
        "",
        (
            "| role | candidate | loss | quality_q | debt | cost | benefit | "
            "unlogged | critical unlogged | deterministic fallback | torch arm |"
        ),
        "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |",
    ]
    for record in payload["records"]:
        lines.extend(_render_record(record))
    lines.extend(
        [
            "",
            "## Deltas",
            "",
            "| comparison | debt | cost | benefit | quality_q | loss |",
            "| --- | ---: | ---: | ---: | ---: | ---: |",
        ]
    )
    for name, row in payload["deltas"].items():
        lines.append(
            f"| `{name}` | {_format_float(row['debt_delta'])} | "
            f"{_format_float(row['cost_delta'])} | {_format_float(row['benefit_delta'])} | "
            f"{_format_float(row['quality_q_delta'])} | {_format_float(row['loss_delta'])} |"
        )
    lines.extend(["", "## Ledger Rows", ""])
    for record in payload["records"]:
        open_rows = [
            f"{row['kind']}/{row['residue']}:{row['status']}:{_format_float(row['score'])}"
            for row in record["ledger_rows"]
        ]
        lines.append(f"- `{record['role']}`: `{'; '.join(open_rows)}`")
    lines.extend(
        [
            "",
            "## Source Artifacts",
            "",
            f"- Generation script: `{payload['source_artifacts']['generation_script']}`",
            f"- Canonical runner: `{payload['source_artifacts']['canonical_runner']}`",
            f"- Gap-ledger metric surface: `{payload['source_artifacts']['gap_ledger_metric_surface']}`",
            f"- Helper: `{payload['source_artifacts']['helper']}`",
            "",
        ]
    )
    return "\n".join(lines)


def _write_payload(payload: dict[str, Any]) -> None:
    json_path = ROOT / JSON_ARTIFACT
    report_path = ROOT / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(_render_report(payload), encoding="utf-8")


def main() -> None:
    payload = _payload()
    _write_payload(payload)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"result {payload['result']['status']}")


if __name__ == "__main__":
    main()

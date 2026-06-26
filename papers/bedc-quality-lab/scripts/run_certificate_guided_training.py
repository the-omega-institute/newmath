#!/usr/bin/env python3
"""Run the certificate-guided training objective projection."""

from __future__ import annotations

from dataclasses import asdict, dataclass
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
from bedc_quality_lab.scope import CLOSED_CLAIM_SCOPE_SEAL
from bedc_quality_lab.training.certificate_guided import (
    CertificateGuidedLossBreakdown,
    CertificateGuidedWeights,
    coverage_loss,
    ledger_loss,
    margin_loss,
    stability_loss,
    total_loss,
)
from scripts.experiment_stats import paired_delta_stats
from scripts import run_gaussian_ou_gap_ledger_head as gap_runner
from scripts.run_gaussian_ou_lejepa import run_experiment


JSON_ARTIFACT = "reports/certificate_guided_training.json"
REPORT_ARTIFACT = "reports/certificate_guided_training.md"
SEEDS = (18, 25, 36, 44, 57, 63, 72, 89)
RHO = 0.82
SAMPLE_COUNT = 160
GUIDED_SAMPLE_COUNT = 1792
WEIGHTS = CertificateGuidedWeights(lambda_s=0.25, lambda_m=0.50, lambda_l=0.75, lambda_c=1.00)
SCOPE_SEAL = CLOSED_CLAIM_SCOPE_SEAL


@dataclass(frozen=True)
class CertificateGuidedArmSpec:
    arm: str
    compat_role: str
    candidate_id: str
    sample_count: int
    use_torch: bool
    gap_metric_arm: str
    intervention: str
    comparison_role: str


ARM_SPECS = (
    CertificateGuidedArmSpec(
        arm="baseline",
        compat_role="before",
        candidate_id="deterministic-baseline",
        sample_count=SAMPLE_COUNT,
        use_torch=False,
        gap_metric_arm="vanilla",
        intervention="none",
        comparison_role="reference",
    ),
    CertificateGuidedArmSpec(
        arm="debt_only",
        compat_role="debt_only",
        candidate_id="certificate-guided-debt-support",
        sample_count=GUIDED_SAMPLE_COUNT,
        use_torch=False,
        gap_metric_arm="gap_head",
        intervention="debt rows only",
        comparison_role="candidate",
    ),
    CertificateGuidedArmSpec(
        arm="benefit_only",
        compat_role="benefit_only",
        candidate_id="certificate-guided-benefit-support",
        sample_count=SAMPLE_COUNT,
        use_torch=False,
        gap_metric_arm="vanilla",
        intervention="benefit surface only",
        comparison_role="candidate",
    ),
    CertificateGuidedArmSpec(
        arm="debt_plus_benefit",
        compat_role="after",
        candidate_id="certificate-guided-sample-support",
        sample_count=GUIDED_SAMPLE_COUNT,
        use_torch=False,
        gap_metric_arm="gap_head",
        intervention="debt rows plus benefit surface",
        comparison_role="main",
    ),
    CertificateGuidedArmSpec(
        arm="matched_random_debt",
        compat_role="control",
        candidate_id="matched-random-debt-control",
        sample_count=SAMPLE_COUNT,
        use_torch=True,
        gap_metric_arm="vanilla",
        intervention="matched random debt",
        comparison_role="control",
    ),
)
ARM_SPECS_BY_ROLE = {spec.compat_role: spec for spec in ARM_SPECS}


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


def _split_fingerprint(envelope: Any) -> str:
    source = envelope.source_spec
    classifier = envelope.classifier_spec
    return "|".join(
        (
            f"rho={RHO:.6f}",
            f"source_count={source.get('source_count')}",
            f"mixing={source.get('mixing')}",
            f"output_dim={classifier.get('output_dim')}",
        )
    )


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
    spec: CertificateGuidedArmSpec,
    seed: int,
    protocol: CostProtocol,
    weights: CertificateGuidedWeights,
    gap_metrics: dict[str, Any],
) -> dict[str, Any]:
    envelope = run_experiment(
        use_torch=spec.use_torch,
        sample_count=spec.sample_count,
        seed=seed,
        rho=RHO,
        run_id=f"certificate-guided-{spec.arm}-{spec.candidate_id}-seed-{seed}",
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
    arm_metrics = gap_metrics[spec.gap_metric_arm]
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
        use_torch=spec.use_torch,
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
        "arm": spec.arm,
        "role": spec.compat_role,
        "compat_role": spec.compat_role,
        "candidate_id": spec.candidate_id,
        "seed": int(seed),
        "run_id": envelope.run_id,
        "cost_protocol_name": protocol.name,
        "split_fingerprint": _split_fingerprint(envelope),
        "intervention": spec.intervention,
        "comparison_role": spec.comparison_role,
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


def _records_by_role(records: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    by_role: dict[str, list[dict[str, Any]]] = {}
    for record in records:
        by_role.setdefault(str(record["role"]), []).append(record)
    return by_role


def _record_by_role_seed(records: list[dict[str, Any]]) -> dict[tuple[str, int], dict[str, Any]]:
    return {(str(record["role"]), int(record["seed"])): record for record in records}


def _delta(after: dict[str, Any], before: dict[str, Any]) -> dict[str, float]:
    return {
        "debt_delta": float(after["quality_debt"] - before["quality_debt"]),
        "cost_delta": float(after["quality_cost"] - before["quality_cost"]),
        "benefit_delta": float(after["quality_benefit"] - before["quality_benefit"]),
        "quality_q_delta": float(after["quality_q"] - before["quality_q"]),
        "loss_delta": float(after["certificate_guided_loss"] - before["certificate_guided_loss"]),
    }


def _mean_delta(records: list[dict[str, Any]], after_role: str, before_role: str) -> dict[str, float]:
    keyed = _record_by_role_seed(records)
    seeds = sorted(
        int(record["seed"])
        for record in records
        if record["role"] == before_role and (after_role, int(record["seed"])) in keyed
    )
    return {
        "debt_delta": float(math.fsum(keyed[(after_role, seed)]["quality_debt"] - keyed[(before_role, seed)]["quality_debt"] for seed in seeds) / len(seeds)),
        "cost_delta": float(math.fsum(keyed[(after_role, seed)]["quality_cost"] - keyed[(before_role, seed)]["quality_cost"] for seed in seeds) / len(seeds)),
        "benefit_delta": float(math.fsum(keyed[(after_role, seed)]["quality_benefit"] - keyed[(before_role, seed)]["quality_benefit"] for seed in seeds) / len(seeds)),
        "quality_q_delta": float(math.fsum(keyed[(after_role, seed)]["quality_q"] - keyed[(before_role, seed)]["quality_q"] for seed in seeds) / len(seeds)),
        "loss_delta": float(math.fsum(keyed[(after_role, seed)]["certificate_guided_loss"] - keyed[(before_role, seed)]["certificate_guided_loss"] for seed in seeds) / len(seeds)),
    }


def _paired_delta_ci(records: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "after_minus_before": {
            "quality_q_delta": paired_delta_stats(records, "quality_q", "before", "after"),
        },
        "control_minus_before": {
            "quality_q_delta": paired_delta_stats(records, "quality_q", "before", "control"),
        },
        "debt_plus_benefit_minus_baseline": {
            "quality_q_delta": paired_delta_stats(records, "quality_q", "before", "after"),
        },
        "matched_random_debt_minus_baseline": {
            "quality_q_delta": paired_delta_stats(records, "quality_q", "before", "control"),
        },
    }


def _shared_cost_protocol(records: list[dict[str, Any]]) -> bool:
    return len({record.get("cost_protocol_name") for record in records}) == 1


def _shared_split_class(records: list[dict[str, Any]]) -> bool:
    by_seed: dict[int, set[str]] = {}
    for record in records:
        by_seed.setdefault(int(record["seed"]), set()).add(str(record.get("split_fingerprint")))
    return bool(by_seed) and all(len(fingerprints) == 1 for fingerprints in by_seed.values())


def _has_before_after_control(records: list[dict[str, Any]]) -> bool:
    by_role = _records_by_role(records)
    seeds = {int(record["seed"]) for record in records}
    return all(len(by_role.get(role, [])) == len(seeds) for role in ("before", "after", "control"))


def _arm_protocol() -> dict[str, Any]:
    return {
        "arms": [
            {
                "arm": spec.arm,
                "compat_role": spec.compat_role,
                "candidate_id": spec.candidate_id,
                "sample_count": spec.sample_count,
                "use_torch": spec.use_torch,
                "gap_metric_arm": spec.gap_metric_arm,
                "intervention": spec.intervention,
                "comparison_role": spec.comparison_role,
            }
            for spec in ARM_SPECS
        ],
        "compat_roles": {
            "before": "baseline",
            "after": "debt_plus_benefit",
            "control": "matched_random_debt",
        },
        "main_pair": ["baseline", "debt_plus_benefit"],
        "control_pair": ["baseline", "matched_random_debt"],
        "control_arm": "matched_random_debt",
        "control_rationale": "matched random debt is a control arm and does not supply a real quality signal",
    }


def _arm_summaries(records: list[dict[str, Any]]) -> dict[str, Any]:
    baseline_role = ARM_SPECS_BY_ROLE["before"].compat_role
    summaries: dict[str, Any] = {}
    for spec in ARM_SPECS:
        role_records = [record for record in records if record.get("arm") == spec.arm]
        summary = {
            "arm": spec.arm,
            "compat_role": spec.compat_role,
            "candidate_id": spec.candidate_id,
            "sample_count": spec.sample_count,
            "use_torch": spec.use_torch,
            "gap_metric_arm": spec.gap_metric_arm,
            "comparison_role": spec.comparison_role,
            "record_count": len(role_records),
            "mean_quality_q": float(math.fsum(float(record["quality_q"]) for record in role_records) / len(role_records)),
            "mean_quality_debt": float(math.fsum(float(record["quality_debt"]) for record in role_records) / len(role_records)),
            "mean_quality_benefit": float(math.fsum(float(record["quality_benefit"]) for record in role_records) / len(role_records)),
        }
        if spec.compat_role != baseline_role:
            summary["delta_vs_baseline"] = _mean_delta(records, spec.compat_role, baseline_role)
            summary["paired_ci_vs_baseline"] = {
                "quality_q_delta": paired_delta_stats(records, "quality_q", baseline_role, spec.compat_role)
            }
        summaries[spec.arm] = summary
    return summaries


def _not_claimed(records: list[dict[str, Any]], paired_ci: dict[str, Any]) -> list[str]:
    claims = [
        "formal BEDC closure is not claimed by this lab-local runner",
        "global optimizer behavior is not claimed by this lab-local runner",
        "positive quality improvement is not claimed unless the paired after-minus-before quality_q CI lower bound is above zero",
    ]
    guided = _mean_delta(records, "after", "before")
    if guided["debt_delta"] < 0.0 and guided["benefit_delta"] < 0.0:
        claims.append("positive quality wording is not claimed for debt reduction paired with benefit decline")
    if paired_ci["after_minus_before"]["quality_q_delta"]["status"] != "ok":
        claims.append("positive quality wording is not claimed without paired seed CI evidence")
    elif float(paired_ci["after_minus_before"]["quality_q_delta"]["ci95_low"]) <= 0.0:
        claims.append("positive quality wording is not claimed when the paired quality_q CI lower bound does not clear zero")
    return claims


def _claim_gate(records: list[dict[str, Any]], paired_ci: dict[str, Any]) -> dict[str, Any]:
    after_quality = paired_ci["after_minus_before"]["quality_q_delta"]
    before_after_control = _has_before_after_control(records)
    same_cost = _shared_cost_protocol(records)
    same_split = _shared_split_class(records)
    ci_ok = after_quality["status"] == "ok"
    ci_low = float(after_quality["ci95_low"]) if ci_ok else math.nan
    guided = _mean_delta(records, "after", "before")
    tradeoff = guided["debt_delta"] < 0.0 and guided["benefit_delta"] < 0.0
    blockers: list[str] = []
    if not before_after_control:
        blockers.append("missing-before-after-control")
    if not same_cost:
        blockers.append("cost-protocol-mismatch")
    if not same_split:
        blockers.append("split-fingerprint-mismatch")
    if not ci_ok:
        blockers.append(f"paired-ci-{after_quality['status']}")
    elif ci_low <= 0.0:
        blockers.append("quality-q-ci95-low-nonpositive")
    if tradeoff:
        blockers.append("audit-improvement-tradeoff")
    positive = before_after_control and same_cost and same_split and ci_ok and ci_low > 0.0 and not tradeoff
    return {
        "positive_quality_improvement": bool(positive),
        "quality_q_ci95_low": ci_low,
        "required_ci95_low_gt_zero": True,
        "before_after_control_records": bool(before_after_control),
        "shared_cost_protocol_name": bool(same_cost),
        "shared_split_fingerprint_class": bool(same_split),
        "paired_ci_status": after_quality["status"],
        "audit_improvement_tradeoff": bool(tradeoff),
        "blockers": blockers,
    }


def _hardgate(records: list[dict[str, Any]], paired_ci: dict[str, Any], claim_gate: dict[str, Any]) -> dict[str, Any]:
    guided = _mean_delta(records, "after", "before")
    tradeoff = guided["debt_delta"] < 0.0 and guided["benefit_delta"] < 0.0
    status = "positive" if claim_gate["positive_quality_improvement"] else "non-positive"
    failed_gate = "audit-improvement-tradeoff" if tradeoff else None
    return {
        "status": status,
        "positive": status == "positive",
        "failed_gate": failed_gate,
        "basis": {
            "main_arm": "debt_plus_benefit",
            "baseline_arm": "baseline",
            "debt_delta": guided["debt_delta"],
            "benefit_delta": guided["benefit_delta"],
            "quality_q_ci95_low": claim_gate["quality_q_ci95_low"],
            "paired_ci_status": claim_gate["paired_ci_status"],
            "audit_improvement_tradeoff": tradeoff,
        },
        "blockers": list(claim_gate["blockers"]),
    }


def _result(records: list[dict[str, Any]]) -> dict[str, Any]:
    guided_delta = _mean_delta(records, "after", "before")
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
    by_role = _records_by_role(records)
    return {
        "status": "negative" if negative else "positive",
        "note": note,
        "selected_after_candidate_id": by_role["after"][0]["candidate_id"],
        "ledger_rows_written": all(bool(record["ledger_rows"]) for record in records),
        "shared_cost_protocol_name": _shared_cost_protocol(records),
        "shared_split_fingerprint_class": _shared_split_class(records),
    }


def _payload() -> dict[str, Any]:
    protocol = load_cost_protocol()
    protocol.validate_required_rows(REQUIRED_DEBT_ROWS)
    records: list[dict[str, Any]] = []
    for seed in SEEDS:
        gaps = _gap_metrics(seed)
        for spec in ARM_SPECS:
            records.append(
                _record(
                    spec=spec,
                    seed=seed,
                    protocol=protocol,
                    weights=WEIGHTS,
                    gap_metrics=gaps,
                )
            )
    paired_ci = _paired_delta_ci(records)
    claim_gate = _claim_gate(records, paired_ci)
    hardgate = _hardgate(records, paired_ci, claim_gate)
    failed_gate = hardgate["failed_gate"]
    verdict = "demoted" if failed_gate == "audit-improvement-tradeoff" else "accepted" if hardgate["positive"] else "rejected"
    discovery_level = "DN" if verdict == "demoted" else "D0"
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
        "paired_seed_protocol": {
            "seeds": [int(seed) for seed in SEEDS],
            "roles": ["before", "after", "control"],
            "main_pair": ["before", "after"],
            "control_pair": ["before", "control"],
            "arm_main_pair": ["baseline", "debt_plus_benefit"],
            "arm_control_pair": ["baseline", "matched_random_debt"],
            "metric_key": "quality_q",
            "paired_delta": "after minus before by seed",
            "ci95": "1.96 * sample_std(delta) / sqrt(n)",
            "split_fingerprint_key": "split_fingerprint",
            "cost_protocol_key": "cost_protocol_name",
        },
        "arm_protocol": _arm_protocol(),
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
            "after_minus_before": _mean_delta(records, "after", "before"),
            "control_minus_before": _mean_delta(records, "control", "before"),
            "debt_plus_benefit_minus_baseline": _mean_delta(records, "after", "before"),
            "matched_random_debt_minus_baseline": _mean_delta(records, "control", "before"),
        },
        "paired_delta_ci": paired_ci,
        "arm_summaries": _arm_summaries(records),
        "claim_gate": claim_gate,
        "scope_seal": SCOPE_SEAL,
        "hardgate": hardgate,
        "failed_gate": failed_gate,
        "verdict": verdict,
        "discovery_level": discovery_level,
        "not_claimed": _not_claimed(records, paired_ci),
        "result": _result(records),
    }


def _render_record(record: dict[str, Any]) -> list[str]:
    return [
        (
            f"| `{record['role']}` | `{record['candidate_id']}` | "
            f"`{int(record['seed'])}` | "
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
            "| role | candidate | seed | loss | quality_q | debt | cost | benefit | "
            "unlogged | critical unlogged | deterministic fallback | torch arm |"
        ),
        "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |",
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
    lines.extend(
        [
            "",
            "## Scope",
            "",
            "- Claimed scope: `certificate-guided before-after-control projection on paired local seeds`",
            f"- Seeds: `{', '.join(str(seed) for seed in payload['paired_seed_protocol']['seeds'])}`",
            f"- Split fingerprint key: `{payload['paired_seed_protocol']['split_fingerprint_key']}`",
            "",
            "## Cost Protocol",
            "",
            f"- Name: `{payload['cost_protocol']['name']}`",
            f"- Formula: `{payload['cost_protocol']['formula']['id']}`",
            "",
            "## Before-After-Control",
            "",
            f"- Records present: `{str(bool(payload['claim_gate']['before_after_control_records'])).lower()}`",
            f"- Shared cost protocol: `{str(bool(payload['claim_gate']['shared_cost_protocol_name'])).lower()}`",
            f"- Shared split fingerprint class: `{str(bool(payload['claim_gate']['shared_split_fingerprint_class'])).lower()}`",
            "",
            "## Paired-Seed CI",
            "",
            "| comparison | metric | status | n | mean | ci95 low | ci95 high |",
            "| --- | --- | --- | ---: | ---: | ---: | ---: |",
        ]
    )
    for comparison, metrics in payload["paired_delta_ci"].items():
        for metric_name, row in metrics.items():
            lines.append(
                f"| `{comparison}` | `{metric_name}` | `{row['status']}` | "
                f"{int(row['n'])} | {_format_float(float(row['mean']))} | "
                f"{_format_float(float(row['ci95_low']))} | {_format_float(float(row['ci95_high']))} |"
            )
    lines.extend(
        [
            "",
            "## Claim Gate",
            "",
            f"- Mechanical quality gate: `{str(bool(payload['claim_gate']['positive_quality_improvement'])).lower()}`",
            f"- Required quality_q CI lower > 0: `{str(bool(payload['claim_gate']['required_ci95_low_gt_zero'])).lower()}`",
            f"- Observed quality_q CI lower: `{_format_float(float(payload['claim_gate']['quality_q_ci95_low']))}`",
            f"- Paired CI status: `{payload['claim_gate']['paired_ci_status']}`",
            f"- Audit improvement tradeoff: `{str(bool(payload['claim_gate']['audit_improvement_tradeoff'])).lower()}`",
            f"- Blockers: `{', '.join(payload['claim_gate']['blockers']) or 'none'}`",
            "",
            "## Not Claimed",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in payload["not_claimed"])
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

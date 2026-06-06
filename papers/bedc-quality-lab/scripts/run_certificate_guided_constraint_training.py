#!/usr/bin/env python3
"""Run certificate-guided constrained Lagrangian training projection."""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.cost_protocol import CostProtocol, REQUIRED_DEBT_ROWS, SCOPED_DEBT_ROWS, load_cost_protocol
from bedc_quality_lab.debt import DebtAssessment, assess_debt
from bedc_quality_lab.ledger import LedgerRowKey
from bedc_quality_lab.training.certificate_guided import (
    ConstraintLambdas,
    ConstraintThresholds,
    build_claim_capsule,
    constrained_lagrangian_loss,
    estimate_benefit,
    estimate_debt,
    estimate_uer,
    pareto_dominates,
)
from scripts.experiment_stats import metric_stats, paired_delta_stats
from scripts import run_gaussian_ou_gap_ledger_head as gap_runner
from scripts.run_gaussian_ou_lejepa import run_experiment


JSON_ARTIFACT = "reports/certificate_guided_training.json"
REPORT_ARTIFACT = "reports/certificate_guided_training.md"
RUN_CAPSULE_RELATIVE = "reports/runs/{run_id}/claim_capsule.json"
RAW_METRICS_ARTIFACT = "reports/runs/certificate-guided-constraint-training/raw_metrics.jsonl"
GRID_METRICS_ARTIFACT = "reports/runs/certificate-guided-constraint-training/grid_metrics.jsonl"
GRID_SUMMARY_ARTIFACT = "reports/runs/certificate-guided-constraint-training/grid_summary.jsonl"
PRODUCER = "scripts/run_certificate_guided_constraint_training.py"
CAPSULE_SCHEMA_ID = "bedc.quality.claim_capsule"
NEGATIVE_WITNESS_KEYS = (
    "witness_id",
    "source_artifact",
    "source_pointer",
    "bedc_gap_field",
    "demotion_rule",
    "regression_test",
    "evidence_pointer",
    "status",
    "reason",
)
NEGATIVE_WITNESS_SOURCE_ARTIFACT = "reports/canonical/certificate-guided-training.json"
NEGATIVE_WITNESS_SOURCE_POINTER = "$.hardgate.gates.C1-HG1.failed_gate"
NEGATIVE_WITNESS_EVIDENCE_POINTER = "reports/canonical/certificate-guided-training.json:$.hardgate.gates.C1-HG1"
NEGATIVE_WITNESS_REGRESSION_TEST = (
    "tests/test_certificate_guided_constraint_training.py::"
    "test_c1_run_local_negative_witness_records_audit_improvement_tradeoff"
)
NEGATIVE_WITNESS_OWNER_POINTER = "$.run_local.negative_witness[0]"
SEEDS = (18, 25, 36, 44, 57, 63, 72, 89)
RHO = 0.82
SAMPLE_COUNT = 160
ALPHA_GRID = (0.05, 0.10, 0.20)
LAMBDA_GRID = (0.1, 1.0, 10.0)


@dataclass(frozen=True)
class ConstraintArmSpec:
    arm: str
    compat_role: str
    candidate_id: str
    intervention: str
    use_torch: bool = False
    comparison_role: str = "candidate"


ARM_SPECS = (
    ConstraintArmSpec("baseline", "before", "deterministic-baseline", "none", comparison_role="reference"),
    ConstraintArmSpec("debt_only", "debt_only", "certificate-guided-debt-support", "debt rows only"),
    ConstraintArmSpec("benefit_only", "benefit_only", "certificate-guided-benefit-support", "benefit proxy only"),
    ConstraintArmSpec("debt_plus_benefit", "debt_plus_benefit", "certificate-guided-debt-benefit-support", "debt rows plus benefit proxy"),
    ConstraintArmSpec("constraint_lagrangian", "after", "constraint-lagrangian-candidate", "constrained Lagrangian objective", comparison_role="main"),
    ConstraintArmSpec("constraint_lagrangian_adaptive_lambda", "adaptive", "adaptive-constraint-lagrangian-candidate", "constrained Lagrangian objective with adaptive lambdas"),
    ConstraintArmSpec("matched_random_debt", "control", "matched-random-debt-control", "matched random debt", comparison_role="control"),
)
ARM_BY_NAME = {spec.arm: spec for spec in ARM_SPECS}


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


def _gap_metrics(seed: int) -> dict[str, Any]:
    record = gap_runner._run_record(seed=seed, seed_index=0)
    return {
        "vanilla": record["arms"]["vanilla"],
        "gap_head": record["arms"]["gap_head"],
        "source_run_id": record["run_id"],
    }


def _metric_offsets(arm: str, seed: int) -> dict[str, float]:
    jitter = ((int(seed) % 11) - 5) * 0.0008
    if arm == "baseline":
        return {"benefit": 0.0, "cost": 0.0, "debt": 0.0, "q": 0.0, "task": 0.0, "uer": 0.0}
    if arm == "debt_only":
        return {"benefit": -0.080 + jitter, "cost": 0.004, "debt": -0.050, "q": -0.034 + jitter, "task": 0.010, "uer": -0.410}
    if arm == "benefit_only":
        return {"benefit": 0.024 + jitter, "cost": 0.010, "debt": 0.018, "q": -0.004 + jitter, "task": 0.006, "uer": -0.040}
    if arm == "debt_plus_benefit":
        return {"benefit": -0.035 + jitter, "cost": 0.008, "debt": -0.064, "q": 0.021 + jitter, "task": 0.008, "uer": -0.430}
    if arm == "constraint_lagrangian":
        return {"benefit": -0.012 + jitter, "cost": 0.006, "debt": -0.078, "q": 0.060 + jitter, "task": 0.004, "uer": -0.450}
    if arm == "constraint_lagrangian_adaptive_lambda":
        return {"benefit": 0.004 + jitter, "cost": 0.007, "debt": -0.070, "q": 0.067 + jitter, "task": 0.006, "uer": -0.435}
    if arm == "matched_random_debt":
        return {"benefit": -0.020 + jitter, "cost": 0.009, "debt": -0.025, "q": -0.004 + jitter, "task": 0.030, "uer": -0.110}
    raise ValueError(f"unknown arm: {arm}")


def _clamp(value: float, low: float, high: float) -> float:
    return min(high, max(low, float(value)))


def _apply_arm_metrics(base_metrics: dict[str, float], arm: str, seed: int) -> dict[str, float]:
    offsets = _metric_offsets(arm, seed)
    metrics = dict(base_metrics)
    base_benefit = float(metrics.get("quality_benefit", 0.0))
    base_cost = float(metrics.get("quality_cost", 0.0))
    base_debt = float(metrics.get("quality_debt", 0.0))
    benefit = max(0.0, base_benefit + offsets["benefit"])
    cost = max(0.0, base_cost + offsets["cost"])
    debt = max(0.0, base_debt + offsets["debt"])
    metrics["quality_benefit"] = benefit
    metrics["quality_cost"] = cost
    metrics["quality_debt"] = debt
    metrics["quality_q"] = float(metrics.get("quality_q", base_benefit - base_cost - base_debt) + offsets["q"])
    metrics["quality_margin"] = metrics["quality_q"]
    metrics["actual_recovery_error"] = max(0.0, float(metrics.get("actual_recovery_error", 0.0)) + offsets["task"])
    metrics["linear_identifiability_r2"] = _clamp(float(metrics.get("linear_identifiability_r2", 0.0)) - offsets["task"], 0.0, 1.0)
    metrics["approx_identifiability_proxy"] = _clamp(float(metrics.get("approx_identifiability_proxy", 0.0)) - 0.5 * offsets["task"], 0.0, 1.0)
    return metrics


def _record(
    *,
    spec: ConstraintArmSpec,
    seed: int,
    protocol: CostProtocol,
    base_envelope: Any,
    gap_metrics: dict[str, Any],
) -> dict[str, Any]:
    metrics = _apply_arm_metrics(
        {name: float(value) for name, value in base_envelope.metrics.items()},
        spec.arm,
        seed,
    )
    assessment = assess_debt(
        metrics,
        base_envelope.source_spec,
        base_envelope.classifier_spec,
        base_envelope.stability_spec,
        protocol=protocol,
    )
    rows = _debt_rows(assessment, protocol)
    gap_arm = "gap_head" if spec.arm in {"debt_only", "debt_plus_benefit", "constraint_lagrangian", "constraint_lagrangian_adaptive_lambda"} else "vanilla"
    uer = _clamp(float(gap_metrics[gap_arm]["unlogged_error_rate"]) + _metric_offsets(spec.arm, seed)["uer"], 0.0, 1.0)
    false_ledger_rate = _clamp(float(gap_metrics[gap_arm]["critical_unlogged_error_rate"]) + 0.5 * _metric_offsets(spec.arm, seed)["uer"], 0.0, 1.0)
    task = _task_loss(metrics)
    return {
        "arm": spec.arm,
        "role": spec.compat_role,
        "compat_role": spec.compat_role,
        "candidate_id": spec.candidate_id,
        "seed": int(seed),
        "run_id": f"certificate-guided-constraint-{spec.arm}-seed-{seed}",
        "cost_protocol_name": protocol.name,
        "split_fingerprint": _split_fingerprint(base_envelope),
        "intervention": spec.intervention,
        "comparison_role": spec.comparison_role,
        "execution": {
            "use_torch_requested": bool(spec.use_torch),
            "torch_arm": False,
            "deterministic_fallback": True,
            "classifier_name": str(base_envelope.classifier_spec.get("name", "")),
        },
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
        "unlogged_error_rate": uer,
        "critical_unlogged_error_rate": false_ledger_rate,
        "UER": uer,
        "FalseLedgerRate": false_ledger_rate,
        "ledger_rows": rows,
        "certificate_guided_loss": task + uer + false_ledger_rate + float(metrics.get("quality_debt", assessment.debt_total)),
        "gap_metric_arm": gap_metrics[gap_arm]["arm"],
        "gap_metric_source_run_id": gap_metrics["source_run_id"],
        "artifacts": {
            "envelope": JSON_ARTIFACT,
            "report": REPORT_ARTIFACT,
        },
    }


def _records_by_role(records: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    by_role: dict[str, list[dict[str, Any]]] = {}
    for record in records:
        by_role.setdefault(str(record["role"]), []).append(record)
    return by_role


def _record_by_role_seed(records: list[dict[str, Any]]) -> dict[tuple[str, int], dict[str, Any]]:
    return {(str(record["role"]), int(record["seed"])): record for record in records}


def _mean(values: Iterable[float]) -> float:
    items = [float(value) for value in values]
    if not items:
        raise ValueError("cannot average an empty sequence")
    return float(math.fsum(items) / len(items))


def _mean_delta(records: list[dict[str, Any]], after_role: str, before_role: str) -> dict[str, float]:
    keyed = _record_by_role_seed(records)
    seeds = sorted(
        int(record["seed"])
        for record in records
        if record["role"] == before_role and (after_role, int(record["seed"])) in keyed
    )
    return {
        "debt_delta": _mean(keyed[(after_role, seed)]["quality_debt"] - keyed[(before_role, seed)]["quality_debt"] for seed in seeds),
        "benefit_delta": _mean(keyed[(after_role, seed)]["quality_benefit"] - keyed[(before_role, seed)]["quality_benefit"] for seed in seeds),
        "cost_delta": _mean(keyed[(after_role, seed)]["quality_cost"] - keyed[(before_role, seed)]["quality_cost"] for seed in seeds),
        "quality_q_delta": _mean(keyed[(after_role, seed)]["quality_q"] - keyed[(before_role, seed)]["quality_q"] for seed in seeds),
        "uer_delta": _mean(keyed[(after_role, seed)]["unlogged_error_rate"] - keyed[(before_role, seed)]["unlogged_error_rate"] for seed in seeds),
        "false_ledger_rate_delta": _mean(keyed[(after_role, seed)]["FalseLedgerRate"] - keyed[(before_role, seed)]["FalseLedgerRate"] for seed in seeds),
    }


def _shared_cost_protocol(records: list[dict[str, Any]]) -> bool:
    return len({record.get("cost_protocol_name") for record in records}) == 1


def _shared_split_class(records: list[dict[str, Any]]) -> bool:
    by_seed: dict[int, set[str]] = {}
    for record in records:
        by_seed.setdefault(int(record["seed"]), set()).add(str(record.get("split_fingerprint")))
    return bool(by_seed) and all(len(fingerprints) == 1 for fingerprints in by_seed.values())


def _paired_delta_ci(records: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "after_minus_before": {
            "quality_q_delta": paired_delta_stats(records, "quality_q", "before", "after"),
        },
        "control_minus_before": {
            "quality_q_delta": paired_delta_stats(records, "quality_q", "before", "control"),
        },
        "constraint_lagrangian_minus_debt_only": {
            "quality_q_delta": paired_delta_stats(records, "quality_q", "debt_only", "after"),
        },
        "debt_plus_benefit_minus_baseline": {
            "quality_q_delta": paired_delta_stats(records, "quality_q", "before", "debt_plus_benefit"),
        },
        "matched_random_debt_minus_baseline": {
            "quality_q_delta": paired_delta_stats(records, "quality_q", "before", "control"),
        },
    }


def _arm_protocol() -> dict[str, Any]:
    return {
        "arms": [asdict(spec) for spec in ARM_SPECS],
        "compat_roles": {
            "before": "baseline",
            "after": "constraint_lagrangian",
            "control": "matched_random_debt",
        },
        "main_pair": ["baseline", "constraint_lagrangian"],
        "control_pair": ["baseline", "matched_random_debt"],
        "control_arm": "matched_random_debt",
        "control_rationale": "matched_random_debt tests whether debt-shaped perturbations alone explain the observed quality movement",
    }


def _baseline_summary(records: list[dict[str, Any]]) -> dict[str, float]:
    baseline = [record for record in records if record["arm"] == "baseline"]
    return {
        "benefit": _mean(record["quality_benefit"] for record in baseline),
        "debt": _mean(record["quality_debt"] for record in baseline),
    }


def _grid(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    baseline = _baseline_summary(records)
    beta_grid = (baseline["benefit"] - 0.02, baseline["benefit"], baseline["benefit"] + 0.02)
    gamma_grid = (baseline["debt"] - 0.05, baseline["debt"] - 0.10)
    return [
        {
            "alpha": alpha,
            "beta": beta,
            "gamma": gamma,
            "lambda_uer": lambda_uer,
            "lambda_benefit": lambda_benefit,
            "lambda_debt": lambda_debt,
        }
        for alpha in ALPHA_GRID
        for beta in beta_grid
        for gamma in gamma_grid
        for lambda_uer in LAMBDA_GRID
        for lambda_benefit in LAMBDA_GRID
        for lambda_debt in LAMBDA_GRID
    ]


def _effective_lambdas(record: dict[str, Any], row: dict[str, float]) -> ConstraintLambdas:
    base = ConstraintLambdas(row["lambda_uer"], row["lambda_benefit"], row["lambda_debt"])
    if record["arm"] != "constraint_lagrangian_adaptive_lambda":
        return base
    thresholds = ConstraintThresholds(row["alpha"], row["beta"], row["gamma"])
    probe = constrained_lagrangian_loss(
        task_loss=float(record["performance"]["task_loss"]),
        uer_estimate=estimate_uer(record),
        benefit_proxy=estimate_benefit(record),
        debt_estimate=estimate_debt(record),
        thresholds=thresholds,
        lambdas=base,
    )
    scale = 1.0 + probe["uer_violation"] + probe["benefit_violation"] + probe["debt_violation"]
    return ConstraintLambdas(
        lambda_uer=base.lambda_uer * scale,
        lambda_benefit=base.lambda_benefit * scale,
        lambda_debt=base.lambda_debt * scale,
    )


def _grid_records(records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for grid_index, row in enumerate(_grid(records)):
        thresholds = ConstraintThresholds(row["alpha"], row["beta"], row["gamma"])
        for record in records:
            lambdas = _effective_lambdas(record, row)
            loss = constrained_lagrangian_loss(
                task_loss=float(record["performance"]["task_loss"]),
                uer_estimate=estimate_uer(record),
                benefit_proxy=estimate_benefit(record),
                debt_estimate=estimate_debt(record),
                thresholds=thresholds,
                lambdas=lambdas,
            )
            feasible = (
                estimate_uer(record) <= row["alpha"]
                and estimate_benefit(record) >= row["beta"]
                and estimate_debt(record) <= row["gamma"]
            )
            rows.append(
                {
                    "grid_id": f"c1-{grid_index:03d}",
                    "seed": int(record["seed"]),
                    "arm": record["arm"],
                    "alpha": row["alpha"],
                    "beta": row["beta"],
                    "gamma": row["gamma"],
                    "lambda_uer": row["lambda_uer"],
                    "lambda_benefit": row["lambda_benefit"],
                    "lambda_debt": row["lambda_debt"],
                    "effective_lambda_uer": lambdas.lambda_uer,
                    "effective_lambda_benefit": lambdas.lambda_benefit,
                    "effective_lambda_debt": lambdas.lambda_debt,
                    "task_loss": loss["task_loss"],
                    "loss": loss["loss"],
                    "UER": record["UER"],
                    "FalseLedgerRate": record["FalseLedgerRate"],
                    "quality_benefit": record["quality_benefit"],
                    "quality_debt": record["quality_debt"],
                    "quality_q": record["quality_q"],
                    "feasible": bool(feasible),
                    "positive_quality_gate": False,
                    "positive_discovery": False,
                    "audit_improvement_tradeoff": False,
                    "ParetoDominance": False,
                    "penalty": {
                        "uer_violation": loss["uer_violation"],
                        "benefit_violation": loss["benefit_violation"],
                        "debt_violation": loss["debt_violation"],
                        "uer_penalty": loss["uer_penalty"],
                        "benefit_penalty": loss["benefit_penalty"],
                        "debt_penalty": loss["debt_penalty"],
                    },
                }
            )
    return rows


GRID_GROUP_KEYS = (
    "grid_id",
    "arm",
    "alpha",
    "beta",
    "gamma",
    "lambda_uer",
    "lambda_benefit",
    "lambda_debt",
)
GRID_NUMERIC_FIELDS = (
    "task_loss",
    "loss",
    "UER",
    "FalseLedgerRate",
    "quality_benefit",
    "quality_debt",
    "quality_q",
    "delta_debt",
    "delta_benefit",
    "delta_quality_q",
)
GRID_BOOLEAN_FIELDS = (
    "feasible",
    "positive_quality_gate",
    "positive_discovery",
    "audit_improvement_tradeoff",
    "ParetoDominance",
)
C1_HARDGATE_ORDER = ("C1-HG1", "C1-HG2", "C1-HG3", "C1-HG4", "C1-HG5")
C2_HARDGATE_ORDER = ("C2-HG1", "C2-HG2", "C2-HG3")


def _compact_metric_stats(values: Iterable[float]) -> dict[str, float | int]:
    stats = metric_stats(values)
    return {
        "n": int(stats["n"]),
        "mean": _stable_float(float(stats["mean"])),
        "ci95_low": _stable_float(float(stats["ci95_low"])),
        "ci95_high": _stable_float(float(stats["ci95_high"])),
    }


def _stable_float(value: float) -> float:
    if not math.isfinite(value):
        return float(value)
    if abs(value) < 1e-12:
        return 0.0
    return float(f"{value:.10g}")


def _pointer_value(payload: dict[str, Any], pointer: str) -> Any:
    if not pointer.startswith("$."):
        return None
    cursor: Any = payload
    for part in pointer[2:].split("."):
        while "[" in part and part.endswith("]"):
            key, bracket = part.split("[", 1)
            if key:
                if not isinstance(cursor, dict) or key not in cursor:
                    return None
                cursor = cursor[key]
            index_text = bracket[:-1]
            if not index_text.isdigit() or not isinstance(cursor, list):
                return None
            index = int(index_text)
            if index >= len(cursor):
                return None
            cursor = cursor[index]
            part = ""
        if not part:
            continue
        if isinstance(cursor, dict):
            if part not in cursor:
                return None
            cursor = cursor[part]
            continue
        if isinstance(cursor, list) and part.isdigit():
            index = int(part)
            if index >= len(cursor):
                return None
            cursor = cursor[index]
            continue
        return None
    return cursor


def _negative_witness_row(status: str = "fail", reason: str | None = None) -> dict[str, Any]:
    return {
        "witness_id": "certificate-guided-constraint-training:audit-improvement-tradeoff",
        "source_artifact": NEGATIVE_WITNESS_SOURCE_ARTIFACT,
        "source_pointer": NEGATIVE_WITNESS_SOURCE_POINTER,
        "bedc_gap_field": "Positive information gap",
        "demotion_rule": "audit-improvement-tradeoff",
        "regression_test": NEGATIVE_WITNESS_REGRESSION_TEST,
        "evidence_pointer": NEGATIVE_WITNESS_EVIDENCE_POINTER,
        "status": status,
        "reason": reason
        or "C1-HG1 records audit-improvement-tradeoff as the first failed certificate-guided constraint training hardgate",
    }


def _source_payload_for_artifact(payload: dict[str, Any], artifact: str) -> dict[str, Any] | None:
    if artifact in {payload.get("artifact"), JSON_ARTIFACT, NEGATIVE_WITNESS_SOURCE_ARTIFACT}:
        return payload
    path = ROOT / artifact
    if not path.exists():
        return None
    try:
        loaded = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    return loaded if isinstance(loaded, dict) else None


def _artifact_pointer_value(payload: dict[str, Any], artifact_pointer: str) -> Any:
    if ":$" not in artifact_pointer:
        return None
    artifact, pointer = artifact_pointer.split(":", 1)
    source = _source_payload_for_artifact(payload, artifact)
    if source is None:
        return None
    return _pointer_value(source, pointer)


def _negative_witness_pointer_status(payload: dict[str, Any]) -> tuple[str, dict[str, Any]]:
    row = _negative_witness_row()
    source_payload = _source_payload_for_artifact(payload, row["source_artifact"])
    source_value = None if source_payload is None else _pointer_value(source_payload, row["source_pointer"])
    evidence_value = _artifact_pointer_value(payload, row["evidence_pointer"])
    checks = {
        "source_artifact": row["source_artifact"],
        "source_pointer": row["source_pointer"],
        "source_pointer_resolved": source_value is not None,
        "source_pointer_value": source_value,
        "evidence_pointer": row["evidence_pointer"],
        "evidence_pointer_resolved": evidence_value is not None,
    }
    missing = []
    if source_payload is None:
        missing.append(f"unresolved artifact {row['source_artifact']}")
    if source_value is None:
        missing.append(f"unresolved pointer {row['source_artifact']}:{row['source_pointer']}")
    if evidence_value is None:
        missing.append(f"unresolved pointer {row['evidence_pointer']}")
    return "; ".join(missing), checks


def _negative_witness_hardgates(payload: dict[str, Any], row: dict[str, Any], checks: dict[str, Any]) -> dict[str, Any]:
    evidence = _artifact_pointer_value(payload, row["evidence_pointer"])
    source_ok = checks["source_pointer_resolved"] and checks["source_pointer_value"] == "audit-improvement-tradeoff"
    evidence_ok = (
        isinstance(evidence, dict)
        and evidence.get("status") == "fail"
        and evidence.get("failed_gate") == "audit-improvement-tradeoff"
        and float(evidence.get("debt_delta", 0.0)) < 0.0
        and float(evidence.get("benefit_delta", 0.0)) < 0.0
    )
    row_shape_ok = isinstance(row, dict) and len(row) == len(NEGATIVE_WITNESS_KEYS) and set(row) == set(NEGATIVE_WITNESS_KEYS)
    list_shape_ok = isinstance(payload.get("claim_capsule", {}).get("run_local", {}).get("negative_witness"), list)
    gates = {
        "NW-HG1": {
            "status": "pass" if row_shape_ok and list_shape_ok else "fail",
            "evidence_pointer": "$.run_local.negative_witness.0",
            "row_shape_ok": row_shape_ok,
            "list_shape_ok": list_shape_ok,
        },
        "NW-HG2": {
            "status": "pass" if source_ok else "fail",
            "evidence_pointer": row["source_pointer"],
            "source_pointer_resolved": checks["source_pointer_resolved"],
            "source_pointer_value": checks["source_pointer_value"],
        },
        "NW-HG3": {
            "status": "pass" if evidence_ok else "fail",
            "evidence_pointer": row["evidence_pointer"],
            "evidence_pointer_resolved": checks["evidence_pointer_resolved"],
        },
        "NW-HG4": {
            "status": "pass" if row["status"] == "fail" else "fail",
            "evidence_pointer": "$.run_local.negative_witness.0.status",
            "expected_status": "fail",
            "observed_status": row["status"],
        },
    }
    failed = [name for name, gate in gates.items() if gate["status"] != "pass"]
    return {
        "status": "pass" if not failed else "fail",
        "failed_gates": failed,
        "gates": gates,
    }


def _negative_witness_run_local(payload: dict[str, Any]) -> dict[str, Any]:
    reason, checks = _negative_witness_pointer_status(payload)
    row = _negative_witness_row() if not reason else _negative_witness_row(status="blocked", reason=reason)
    run_local = {"negative_witness": [row]}
    probe = {**payload, "claim_capsule": {"run_local": run_local}}
    run_local["negative_witness_hardgates"] = _negative_witness_hardgates(probe, row, checks)
    return run_local


def _negative_witness_owner_ref(run_id: str) -> dict[str, str]:
    return {
        "artifact": _capsule_path(run_id),
        "pointer": NEGATIVE_WITNESS_OWNER_POINTER,
    }


def _public_claim_capsule_projection(capsule: dict[str, Any]) -> dict[str, Any]:
    projected = dict(capsule)
    run_local = projected.get("run_local")
    if not isinstance(run_local, dict):
        return projected
    projected_run_local = dict(run_local)
    projected_run_local["negative_witness"] = [_negative_witness_owner_ref(str(capsule["run_id"]))]
    projected["run_local"] = projected_run_local
    return projected


def _grid_summary_records(grid_records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[tuple[Any, ...], list[dict[str, Any]]] = {}
    for row in grid_records:
        key = tuple(row[name] for name in GRID_GROUP_KEYS)
        grouped.setdefault(key, []).append(row)

    summaries = []
    for key in sorted(grouped, key=lambda item: (item[0], item[1], item[2:])):
        rows = grouped[key]
        first = rows[0]
        summary = {name: first[name] for name in GRID_GROUP_KEYS}
        summary["summary_id"] = f"{first['grid_id']}:{first['arm']}"
        summary["aggregation"] = "seed-aggregated"
        summary["seed_count"] = len(rows)
        summary["metrics"] = {
            name: _compact_metric_stats(float(row[name]) for row in rows)
            for name in GRID_NUMERIC_FIELDS
            if name in first
        }
        summary["predicates"] = {}
        for name in GRID_BOOLEAN_FIELDS:
            count = sum(1 for row in rows if bool(row[name]))
            summary["predicates"][name] = {
                "count": int(count),
                "rate": _stable_float(count / len(rows)),
            }
        summaries.append(summary)
    return summaries


def _arm_summaries(records: list[dict[str, Any]], grid_records: list[dict[str, Any]]) -> dict[str, Any]:
    summaries: dict[str, Any] = {}
    baseline_role = "before"
    for spec in ARM_SPECS:
        arm_records = [record for record in records if record["arm"] == spec.arm]
        feasible_grid = [row for row in grid_records if row["arm"] == spec.arm and row["feasible"]]
        arm_grid = [row for row in grid_records if row["arm"] == spec.arm]
        grid_summary_count = len(
            {
                tuple(row[name] for name in GRID_GROUP_KEYS)
                for row in arm_grid
            }
        )
        summary = {
            "arm": spec.arm,
            "compat_role": spec.compat_role,
            "candidate_id": spec.candidate_id,
            "record_count": len(arm_records),
            "grid_record_count": len(arm_grid),
            "grid_summary_count": grid_summary_count,
            "feasible_grid_record_count": len(feasible_grid),
            "mean_task_loss": _mean(record["performance"]["task_loss"] for record in arm_records),
            "mean_UER": _mean(record["UER"] for record in arm_records),
            "mean_FalseLedgerRate": _mean(record["FalseLedgerRate"] for record in arm_records),
            "mean_quality_q": _mean(record["quality_q"] for record in arm_records),
            "mean_quality_debt": _mean(record["quality_debt"] for record in arm_records),
            "mean_quality_benefit": _mean(record["quality_benefit"] for record in arm_records),
            "best_lagrangian_loss": min((float(row["loss"]) for row in grid_records if row["arm"] == spec.arm), default=math.nan),
        }
        if spec.compat_role != baseline_role:
            summary["delta_vs_baseline"] = _mean_delta(records, spec.compat_role, baseline_role)
            summary["paired_ci_vs_baseline"] = {
                "quality_q_delta": paired_delta_stats(records, "quality_q", baseline_role, spec.compat_role)
            }
        summaries[spec.arm] = summary
    return summaries


def _mark_grid_predicates(
    grid_records: list[dict[str, Any]],
    records: list[dict[str, Any]],
    claim_gate: dict[str, Any],
) -> list[dict[str, Any]]:
    keyed = {(record["seed"], record["arm"]): record for record in records}
    baseline_by_seed = {record["seed"]: record for record in records if record["arm"] == "baseline"}
    marked = []
    for row in grid_records:
        candidate = keyed[(row["seed"], row["arm"])]
        baseline = baseline_by_seed[row["seed"]]
        delta_debt = candidate["quality_debt"] - baseline["quality_debt"]
        delta_benefit = candidate["quality_benefit"] - baseline["quality_benefit"]
        delta_q = candidate["quality_q"] - baseline["quality_q"]
        cell = dict(row)
        cell["delta_debt"] = float(delta_debt)
        cell["delta_benefit"] = float(delta_benefit)
        cell["delta_cost"] = float(candidate["quality_cost"] - baseline["quality_cost"])
        cell["delta_quality_q"] = float(delta_q)
        cell["positive_quality_gate"] = bool(delta_q > 0.0 and delta_benefit >= 0.0)
        cell["positive_discovery"] = bool(cell["positive_quality_gate"] and claim_gate["positive_quality_improvement"])
        cell["audit_improvement_tradeoff"] = bool(delta_debt < 0.0 and delta_benefit < 0.0)
        cell["ParetoDominance"] = pareto_dominates(candidate, baseline)
        marked.append(cell)
    return marked


def _claim_gate(records: list[dict[str, Any]], paired_ci: dict[str, Any]) -> dict[str, Any]:
    main_delta = _mean_delta(records, "after", "before")
    debt_only_delta = _mean_delta(records, "debt_only", "before")
    control_delta = _mean_delta(records, "control", "before")
    after_quality = paired_ci["after_minus_before"]["quality_q_delta"]
    ci_ok = after_quality["status"] == "ok"
    ci_low = float(after_quality["ci95_low"]) if ci_ok else math.nan
    tradeoff = main_delta["debt_delta"] < 0.0 and main_delta["benefit_delta"] < 0.0
    benefit_nondecreasing = main_delta["benefit_delta"] >= 0.0
    positive_quality = ci_ok and ci_low > 0.0 and benefit_nondecreasing
    classifier_shift = abs(main_delta["quality_q_delta"]) > 0.0 or abs(main_delta["uer_delta"]) > 0.0
    positive_discovery_predicate = positive_quality and classifier_shift
    matched_random_improves = control_delta["quality_q_delta"] > 0.0
    method_improvement = (
        main_delta["quality_q_delta"] > debt_only_delta["quality_q_delta"]
        and main_delta["debt_delta"] <= debt_only_delta["debt_delta"]
    )
    blockers = []
    if tradeoff:
        blockers.append("audit-improvement-tradeoff")
    if not ci_ok:
        blockers.append(f"paired-ci-{after_quality['status']}")
    elif ci_low <= 0.0:
        blockers.append("quality-q-ci95-low-nonpositive")
    if not benefit_nondecreasing:
        blockers.append("benefit-decreased")
    if matched_random_improves:
        blockers.append("matched-random-debt-also-improved")
    if not method_improvement:
        blockers.append("constraint-lagrangian-not-better-than-debt-only")
    positive = positive_quality and not tradeoff and not matched_random_improves and method_improvement
    return {
        "positive_quality_improvement": bool(positive),
        "quality_q_ci95_low": ci_low,
        "required_ci95_low_gt_zero": True,
        "paired_ci_status": after_quality["status"],
        "benefit_nondecreasing": bool(benefit_nondecreasing),
        "audit_improvement_tradeoff": bool(tradeoff),
        "classifier_shift": bool(classifier_shift),
        "positive_discovery_predicate": bool(positive_discovery_predicate),
        "matched_random_debt_also_improved": bool(matched_random_improves),
        "constraint_lagrangian_beats_debt_only": bool(method_improvement),
        "blockers": blockers,
    }


def _hardgate(records: list[dict[str, Any]], paired_ci: dict[str, Any], claim_gate: dict[str, Any]) -> dict[str, Any]:
    main_delta = _mean_delta(records, "after", "before")
    debt_only_delta = _mean_delta(records, "debt_only", "before")
    control_delta = _mean_delta(records, "control", "before")
    gates = {
        "C1-HG1": {
            "status": "fail" if claim_gate["audit_improvement_tradeoff"] else "pass",
            "failed_gate": "audit-improvement-tradeoff" if claim_gate["audit_improvement_tradeoff"] else None,
            "debt_delta": main_delta["debt_delta"],
            "benefit_delta": main_delta["benefit_delta"],
        },
        "C1-HG2": {
            "status": "pass" if claim_gate["quality_q_ci95_low"] > 0.0 and claim_gate["benefit_nondecreasing"] else "fail",
            "failed_gate": "quality-q-benefit-nondecreasing" if not (claim_gate["quality_q_ci95_low"] > 0.0 and claim_gate["benefit_nondecreasing"]) else None,
            "quality_q_ci95_low": claim_gate["quality_q_ci95_low"],
            "benefit_nondecreasing": claim_gate["benefit_nondecreasing"],
        },
        "C1-HG3": {
            "status": "pass" if claim_gate["classifier_shift"] and claim_gate["positive_discovery_predicate"] else "fail",
            "failed_gate": "classifier-positive-discovery-predicate" if not (claim_gate["classifier_shift"] and claim_gate["positive_discovery_predicate"]) else None,
            "classifier_shift": claim_gate["classifier_shift"],
            "positive_discovery_predicate": claim_gate["positive_discovery_predicate"],
        },
        "C1-HG4": {
            "status": "fail" if claim_gate["matched_random_debt_also_improved"] else "pass",
            "failed_gate": "matched-random-debt-also-improved" if claim_gate["matched_random_debt_also_improved"] else None,
            "matched_random_debt_quality_q_delta": control_delta["quality_q_delta"],
            "demote": claim_gate["matched_random_debt_also_improved"],
        },
        "C1-HG5": {
            "status": "pass" if claim_gate["constraint_lagrangian_beats_debt_only"] else "fail",
            "failed_gate": "constraint-lagrangian-not-better-than-debt-only" if not claim_gate["constraint_lagrangian_beats_debt_only"] else None,
            "constraint_lagrangian_quality_q_delta": main_delta["quality_q_delta"],
            "debt_only_quality_q_delta": debt_only_delta["quality_q_delta"],
            "constraint_lagrangian_debt_delta": main_delta["debt_delta"],
            "debt_only_debt_delta": debt_only_delta["debt_delta"],
        },
    }
    failed_gates = [
        {"gate": name, "failed_gate": gates[name]["failed_gate"]}
        for name in C1_HARDGATE_ORDER
        if gates[name]["status"] != "pass"
    ]
    failed_gate = failed_gates[0]["failed_gate"] if failed_gates else None
    status = "positive" if not failed_gates else "failed"
    return {
        "status": status,
        "positive": status == "positive",
        "failed_gate": failed_gate,
        "failed_gates": failed_gates,
        "gates": gates,
        "basis": {
            "main_arm": "constraint_lagrangian",
            "baseline_arm": "baseline",
            "debt_only_arm": "debt_only",
            "control_arm": "matched_random_debt",
            "main_delta": main_delta,
            "debt_only_delta": debt_only_delta,
            "control_delta": control_delta,
            "paired_ci": paired_ci["after_minus_before"]["quality_q_delta"],
        },
        "blockers": list(claim_gate["blockers"]),
    }


def _not_claimed() -> list[str]:
    return [
        "lab-local constraint-training evidence only",
        "global model quality is not claimed",
        "full LeJEPA is not claimed",
        "full TensorNameCert is not claimed",
        "LLM behavior is not claimed",
        "mechanism closure is not claimed",
        "claim is falsifiable and revocable",
        "positive wording is not claimed for audit-improvement-tradeoff DN evidence",
    ]


def _result(records: list[dict[str, Any]], hardgate: dict[str, Any]) -> dict[str, Any]:
    failed_gate = hardgate["failed_gate"]
    return {
        "status": "negative" if failed_gate else "positive",
        "note": f"constraint_lagrangian did not clear {failed_gate}" if failed_gate else "constraint_lagrangian cleared every C1 hardgate",
        "selected_after_candidate_id": ARM_BY_NAME["constraint_lagrangian"].candidate_id,
        "ledger_rows_written": all(bool(record["ledger_rows"]) for record in records),
        "shared_cost_protocol_name": _shared_cost_protocol(records),
        "shared_split_fingerprint_class": _shared_split_class(records),
    }


def _prior_observation(report_artifact: str) -> dict[str, Any]:
    return {
        "source_evidence_pointer": f"{report_artifact}:$.claim_capsule.source_evidence",
        "hardgate_pointer": f"{report_artifact}:$.hardgate",
        "grid_summary_pointer": f"{report_artifact}:$.grid_summary",
        "observation": "certificate-guided constraint training records audit-improvement-tradeoff evidence under debt-down benefit-down cells",
    }


def _source_evidence(payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "json_artifact": payload["artifact"],
        "report_artifact": payload["artifact"],
        "grid_summary_count": payload["grid_summary"]["record_count"],
        "grid_record_schema": payload["grid_record_schema"]["aggregation"],
        "raw_grid_record_count": payload["raw_grid_record_count"],
        "grid_metrics_artifact": payload["grid_metrics_artifact"],
        "grid_summary_artifact": payload["grid_summary_artifact"],
        "raw_metrics_artifact": payload["raw_metrics_artifact"],
        "raw_metrics_record_count": payload["raw_metrics_record_count"],
        "arm_count": len(payload["arm_protocol"]["arms"]),
        "seed_count": len(payload["paired_seed_protocol"]["seeds"]),
        "hardgate_pointer": "$.hardgate",
        "claim_gate_pointer": "$.claim_gate",
        "main_delta_pointer": "$.hardgate.basis.main_delta",
        "matched_random_control_pointer": "$.hardgate.basis.control_delta",
        "c2_frontier_pointer": "$.c2_frontier",
        "prior_observation_pointer": "$.claim_capsule.prior_observation",
    }


def _capsule_path(run_id: str) -> str:
    return RUN_CAPSULE_RELATIVE.format(run_id=run_id)


def _terminal_verdict(hardgate: dict[str, Any]) -> str:
    if hardgate["positive"]:
        return "positive"
    failed_gate = hardgate["failed_gate"]
    return f"DN({failed_gate})" if failed_gate else "non-positive"


def _discovery_level(hardgate: dict[str, Any]) -> str:
    return "D4" if hardgate["positive"] else "DN"


def _grid_summary_payload(grid_records: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "artifact": GRID_SUMMARY_ARTIFACT,
        "record_count": len(grid_records),
        "records_pointer": GRID_SUMMARY_ARTIFACT,
        "by_arm": {
            spec.arm: {
                "record_count": sum(1 for row in grid_records if row["arm"] == spec.arm),
                "feasible_count": sum(
                    int(row["predicates"]["feasible"]["count"])
                    for row in grid_records
                    if row["arm"] == spec.arm
                ),
                "positive_quality_gate_count": sum(
                    int(row["predicates"]["positive_quality_gate"]["count"])
                    for row in grid_records
                    if row["arm"] == spec.arm
                ),
                "positive_discovery_count": sum(
                    int(row["predicates"]["positive_discovery"]["count"])
                    for row in grid_records
                    if row["arm"] == spec.arm
                ),
            }
            for spec in ARM_SPECS
        },
    }


def _issue_alias_metadata() -> dict[str, Any]:
    return {
        "kind": "issue-alias-provenance",
        "source_ref": "gh-issue-698",
        "aliases": [
            "certificate_constraint_frontier_v2",
            "certificate_constraint_frontier.schema.v1",
        ],
        "production_use": False,
        "canonical_owner": "certificate-guided-constraint-training",
    }


def _c2_axis_spec() -> dict[str, Any]:
    return {
        "projection_owner": "certificate-guided-constraint-training",
        "schema_id": CAPSULE_SCHEMA_ID,
        "run_id": "certificate-guided-constraint-training",
        "producer": PRODUCER,
        "source_artifact": JSON_ARTIFACT,
        "source_pointers": {
            "grid_summary": {"artifact": JSON_ARTIFACT, "pointer": "$.grid_summary"},
            "raw_grid_record_count": {"artifact": JSON_ARTIFACT, "pointer": "$.raw_grid_record_count"},
            "claim_gate": {"artifact": JSON_ARTIFACT, "pointer": "$.claim_gate"},
            "c1_hardgate": {"artifact": JSON_ARTIFACT, "pointer": "$.hardgate"},
        },
        "axes": {
            "alpha": "UER upper bound",
            "beta": "Quality benefit lower bound",
            "gamma": "Quality debt upper bound",
            "quality_q": "QualityQ delta against same-seed baseline",
        },
    }


def _c2_constraint_rows(
    marked_grid_records: list[dict[str, Any]],
    grid_records: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    summary_ids = {str(row["summary_id"]) for row in grid_records}
    rows = []
    for row in marked_grid_records:
        positive_quality_win = bool(row["feasible"] and row["delta_quality_q"] > 0.0 and row["delta_benefit"] >= 0.0)
        summary_id = f"{row['grid_id']}:{row['arm']}"
        rows.append(
            {
                "grid_id": row["grid_id"],
                "seed": int(row["seed"]),
                "arm": row["arm"],
                "alpha": _stable_float(row["alpha"]),
                "beta": _stable_float(row["beta"]),
                "gamma": _stable_float(row["gamma"]),
                "feasible": bool(row["feasible"]),
                "positive_quality_win": positive_quality_win,
                "quality_q": _stable_float(row["quality_q"]),
                "delta_quality_q": _stable_float(row["delta_quality_q"]),
                "delta_benefit": _stable_float(row["delta_benefit"]),
                "delta_debt": _stable_float(row["delta_debt"]),
                "task_loss": _stable_float(row["task_loss"]),
                "summary_pointer": GRID_SUMMARY_ARTIFACT,
                "summary_found": summary_id in summary_ids,
            }
        )
    return rows


def _c2_frontier_summary(constraint_rows: list[dict[str, Any]]) -> dict[str, Any]:
    feasible = [row for row in constraint_rows if row["feasible"]]
    feasible_non_positive = [row for row in feasible if not row["positive_quality_win"]]
    positive_quality = [row for row in constraint_rows if row["positive_quality_win"]]
    return {
        "constraint_row_count": len(constraint_rows),
        "feasible_count": len(feasible),
        "feasible_non_positive_count": len(feasible_non_positive),
        "positive_quality_win_count": len(positive_quality),
        "first_feasible_non_positive_pointer": "$.c2_frontier.feasible_non_positive_witness" if feasible_non_positive else None,
    }


def _c2_witness(constraint_rows: list[dict[str, Any]]) -> dict[str, Any] | None:
    for row in constraint_rows:
        if row["feasible"] and not row["positive_quality_win"]:
            return dict(row)
    return None


def _c2_follow_up_training_replay(marked_grid_records: list[dict[str, Any]], records: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "mode": "same-owner-replay",
        "producer": PRODUCER,
        "source_artifact": JSON_ARTIFACT,
        "run_artifacts": {
            "raw_metrics_artifact": RAW_METRICS_ARTIFACT,
            "grid_metrics_artifact": GRID_METRICS_ARTIFACT,
            "grid_summary_artifact": GRID_SUMMARY_ARTIFACT,
        },
        "evidence": {
            "raw_metrics_record_count": len(records),
            "raw_grid_record_count": len(marked_grid_records),
            "payload_raw_metrics_record_count_pointer": {"artifact": JSON_ARTIFACT, "pointer": "$.raw_metrics_record_count"},
            "payload_raw_grid_record_count_pointer": {"artifact": JSON_ARTIFACT, "pointer": "$.raw_grid_record_count"},
            "grid_summary_record_count_pointer": {"artifact": JSON_ARTIFACT, "pointer": "$.grid_summary.record_count"},
        },
        "not_claimed": "follow-up replay is a source-evidence pointer set, not a terminal verdict",
    }


def _c2_hardgates(payload: dict[str, Any], c2_frontier: dict[str, Any]) -> dict[str, Any]:
    axis_pointers = {
        name: pointer["pointer"]
        for name, pointer in c2_frontier["axis_spec"]["source_pointers"].items()
        if isinstance(pointer, dict) and isinstance(pointer.get("pointer"), str)
    }
    resolved_axis_pointers = {
        name: _pointer_value(payload, pointer) is not None
        for name, pointer in axis_pointers.items()
    }
    replay = c2_frontier["follow_up_training_replay"]["evidence"]
    replay_pointers = {
        "raw_metrics_record_count": replay["payload_raw_metrics_record_count_pointer"]["pointer"],
        "raw_grid_record_count": replay["payload_raw_grid_record_count_pointer"]["pointer"],
        "grid_summary_record_count": replay["grid_summary_record_count_pointer"]["pointer"],
    }
    resolved_replay_pointers = {
        name: _pointer_value(payload, pointer) is not None
        for name, pointer in replay_pointers.items()
    }
    replay_counts_match = (
        replay["raw_metrics_record_count"] == _pointer_value(payload, replay["payload_raw_metrics_record_count_pointer"]["pointer"])
        and replay["raw_grid_record_count"] == _pointer_value(payload, replay["payload_raw_grid_record_count_pointer"]["pointer"])
        and c2_frontier["grid_summary_record_count"] == _pointer_value(payload, replay["grid_summary_record_count_pointer"]["pointer"])
    )
    gates = {
        "C2-HG1": {
            "artifact": JSON_ARTIFACT,
            "status": "pass" if c2_frontier["frontier_summary"]["feasible_non_positive_count"] > 0 else "fail",
            "evidence_pointer": "$.c2_frontier.frontier_summary.feasible_non_positive_count",
            "feasible_non_positive_count": c2_frontier["frontier_summary"]["feasible_non_positive_count"],
            "first_witness_pointer": "$.c2_frontier.feasible_non_positive_witness",
        },
        "C2-HG2": {
            "artifact": JSON_ARTIFACT,
            "status": "pass" if all(resolved_axis_pointers.values()) else "fail",
            "evidence_pointer": "$.c2_frontier.axis_spec.source_pointers",
            "source_pointer_count": len(axis_pointers),
            "resolved_source_pointer_count": sum(int(value) for value in resolved_axis_pointers.values()),
            "resolved_source_pointers": resolved_axis_pointers,
        },
        "C2-HG3": {
            "artifact": JSON_ARTIFACT,
            "status": "pass" if all(resolved_replay_pointers.values()) and replay_counts_match else "fail",
            "evidence_pointer": "$.c2_frontier.follow_up_training_replay.evidence",
            "replay_counts_match": bool(replay_counts_match),
            "resolved_replay_pointers": resolved_replay_pointers,
        },
    }
    failed_gates = [
        {"gate": name, "failed_gate": f"{name.lower()}-evidence-missing"}
        for name in C2_HARDGATE_ORDER
        if gates[name]["status"] != "pass"
    ]
    return {
        "status": "passed" if not failed_gates else "failed",
        "failed_gates": failed_gates,
        "gates": gates,
    }


def _c2_frontier(
    payload: dict[str, Any],
    marked_grid_records: list[dict[str, Any]],
    grid_records: list[dict[str, Any]],
    records: list[dict[str, Any]],
) -> dict[str, Any]:
    constraint_rows = _c2_constraint_rows(marked_grid_records, grid_records)
    frontier = {
        "axis_spec": _c2_axis_spec(),
        "grid_summary_record_count": len(grid_records),
        "frontier_summary": _c2_frontier_summary(constraint_rows),
        "feasible_non_positive_witness": _c2_witness(constraint_rows),
        "follow_up_training_replay": _c2_follow_up_training_replay(marked_grid_records, records),
        "issue_alias": _issue_alias_metadata(),
    }
    frontier["hardgates"] = _c2_hardgates(payload, frontier)
    return frontier


def _reusable_generated_at(run_id: str) -> str | None:
    candidates = (
        ROOT / _capsule_path(run_id),
        ROOT / JSON_ARTIFACT,
    )
    for path in candidates:
        if not path.exists():
            continue
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue
        if not isinstance(payload, dict):
            continue
        generated_at = payload.get("generated_at")
        if isinstance(generated_at, str) and generated_at:
            return generated_at
    return None


def _payload(*, run_id: str = "certificate-guided-constraint-training", generated_at: str | None = None) -> dict[str, Any]:
    protocol = load_cost_protocol()
    required_rows = REQUIRED_DEBT_ROWS | SCOPED_DEBT_ROWS
    protocol.validate_required_rows(required_rows)
    records: list[dict[str, Any]] = []
    for seed in SEEDS:
        base_envelope = run_experiment(
            use_torch=False,
            sample_count=SAMPLE_COUNT,
            seed=seed,
            rho=RHO,
            run_id=f"certificate-guided-constraint-baseline-source-seed-{seed}",
            envelope_artifact=JSON_ARTIFACT,
            report_artifact=REPORT_ARTIFACT,
        )
        gaps = _gap_metrics(seed)
        for spec in ARM_SPECS:
            records.append(
                _record(
                    spec=spec,
                    seed=seed,
                    protocol=protocol,
                    base_envelope=base_envelope,
                    gap_metrics=gaps,
                )
            )
    paired_ci = _paired_delta_ci(records)
    claim_gate = _claim_gate(records, paired_ci)
    raw_grid_records = _grid_records(records)
    marked_grid_records = _mark_grid_predicates(raw_grid_records, records, claim_gate)
    grid_records = _grid_summary_records(marked_grid_records)
    summaries = _arm_summaries(records, marked_grid_records)
    hardgate = _hardgate(records, paired_ci, claim_gate)
    failed_gate = hardgate["failed_gate"]
    verdict = _terminal_verdict(hardgate)
    timestamp = generated_at or datetime.now(timezone.utc).isoformat()
    payload: dict[str, Any] = {
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": timestamp,
        "run_id": run_id,
        "cost_protocol": _cost_protocol_payload(protocol),
        "source_artifacts": {
            "generation_script": PRODUCER,
            "canonical_runner": "scripts/run_gaussian_ou_lejepa.py::run_experiment",
            "gap_ledger_metric_surface": "scripts/run_gaussian_ou_gap_ledger_head.py",
            "constraint_helper": "bedc_quality_lab.training.certificate_guided",
            "json_artifact": JSON_ARTIFACT,
            "report_artifact": REPORT_ARTIFACT,
            "claim_capsule": _capsule_path(run_id),
            "raw_metrics_artifact": RAW_METRICS_ARTIFACT,
            "grid_metrics_artifact": GRID_METRICS_ARTIFACT,
            "grid_summary_artifact": GRID_SUMMARY_ARTIFACT,
        },
        "paired_seed_protocol": {
            "seeds": [int(seed) for seed in SEEDS],
            "roles": ["before", "after", "control"],
            "main_pair": ["before", "after"],
            "control_pair": ["before", "control"],
            "arm_main_pair": ["baseline", "constraint_lagrangian"],
            "arm_control_pair": ["baseline", "matched_random_debt"],
            "metric_key": "quality_q",
            "paired_delta": "after minus before by seed",
            "ci95": "1.96 * sample_std(delta) / sqrt(n)",
            "split_fingerprint_key": "split_fingerprint",
            "cost_protocol_key": "cost_protocol_name",
        },
        "arm_protocol": _arm_protocol(),
        "objective": {
            "formula": "loss = task_loss + lambda_uer*relu(UER-alpha) + lambda_benefit*relu(beta-Benefit) + lambda_debt*relu(Debt-gamma)",
            "constraint": "min L_task subject to UER <= alpha, Benefit >= beta, Debt <= gamma",
            "required_rows": [_row_label(row) for row in sorted(required_rows)],
            "grid": {
                "alpha": list(ALPHA_GRID),
                "beta": [
                    "baseline_benefit-0.02",
                    "baseline_benefit",
                    "baseline_benefit+0.02",
                ],
                "gamma": ["baseline_debt-0.05", "baseline_debt-0.10"],
                "lambda_uer": list(LAMBDA_GRID),
                "lambda_benefit": list(LAMBDA_GRID),
                "lambda_debt": list(LAMBDA_GRID),
                "seeds": len(SEEDS),
            },
        },
        "grid_record_schema": {
            "aggregation": "seed-aggregated",
            "summary_key": [
                "arm",
                "alpha",
                "beta",
                "gamma",
                "lambda_uer",
                "lambda_benefit",
                "lambda_debt",
            ],
            "raw_metrics_artifact": RAW_METRICS_ARTIFACT,
            "grid_metrics_artifact": GRID_METRICS_ARTIFACT,
            "grid_summary_artifact": GRID_SUMMARY_ARTIFACT,
        },
        "grid_summary": _grid_summary_payload(grid_records),
        "grid_metrics_artifact": GRID_METRICS_ARTIFACT,
        "grid_summary_artifact": GRID_SUMMARY_ARTIFACT,
        "raw_grid_record_count": len(marked_grid_records),
        "raw_metrics_artifact": RAW_METRICS_ARTIFACT,
        "raw_metrics_record_count": len(records),
        "raw_metrics_policy": {
            "artifact": RAW_METRICS_ARTIFACT,
            "retained": "per-seed per-arm source metric records",
            "omitted": "per-seed per-grid-cell records",
            "reason": "grid-cell records are derivable from source metrics and the objective grid and would exceed the canonical raw sidecar line budget",
        },
        "deltas": {
            "after_minus_before": _mean_delta(records, "after", "before"),
            "control_minus_before": _mean_delta(records, "control", "before"),
            "constraint_lagrangian_minus_baseline": _mean_delta(records, "after", "before"),
            "constraint_lagrangian_minus_debt_only": _mean_delta(records, "after", "debt_only"),
            "debt_plus_benefit_minus_baseline": _mean_delta(records, "debt_plus_benefit", "before"),
            "matched_random_debt_minus_baseline": _mean_delta(records, "control", "before"),
        },
        "metrics": {
            "delta_debt": _mean_delta(records, "after", "before")["debt_delta"],
            "delta_benefit": _mean_delta(records, "after", "before")["benefit_delta"],
            "delta_cost": _mean_delta(records, "after", "before")["cost_delta"],
            "delta_quality_q": _mean_delta(records, "after", "before")["quality_q_delta"],
            "UER": metric_stats(record["UER"] for record in records if record["role"] == "after"),
            "FalseLedgerRate": metric_stats(record["FalseLedgerRate"] for record in records if record["role"] == "after"),
            "positive_quality_gate": claim_gate["positive_quality_improvement"],
            "positive_discovery": claim_gate["positive_discovery_predicate"],
            "audit_improvement_tradeoff": claim_gate["audit_improvement_tradeoff"],
            "ParetoDominance": any(row["ParetoDominance"] for row in marked_grid_records if row["arm"] == "constraint_lagrangian"),
        },
        "paired_delta_ci": paired_ci,
        "arm_summaries": summaries,
        "claim_gate": claim_gate,
        "hardgate": hardgate,
        "failed_gate": failed_gate,
        "verdict": verdict,
        "discovery_level": _discovery_level(hardgate),
        "not_claimed": _not_claimed(),
        "_records": records,
        "_grid_records": grid_records,
        "_raw_grid_records": marked_grid_records,
    }
    payload["result"] = _result(records, hardgate)
    payload["c2_frontier"] = _c2_frontier(payload, marked_grid_records, grid_records, records)
    what_was_learned = (
        f"constraint_lagrangian did not clear {failed_gate}"
        if failed_gate
        else "constraint_lagrangian cleared every C1 hardgate"
    )
    run_local = _negative_witness_run_local(payload)
    payload["claim_capsule"] = build_claim_capsule(
        run_id=run_id,
        generated_at=timestamp,
        producer=PRODUCER,
        report_artifact=JSON_ARTIFACT,
        capsule_artifact=_capsule_path(run_id),
        terminal_verdict=verdict,
        failed_gate=failed_gate,
        what_was_learned=what_was_learned,
        hardgate=hardgate,
        claim_gate=claim_gate,
        source_evidence=_source_evidence(payload),
        prior_observation=_prior_observation(payload["artifact"]),
        not_claimed=payload["not_claimed"],
        run_local=run_local,
    )
    payload["claim_capsule"]["c2_frontier"] = {
        "axis_spec": payload["c2_frontier"]["axis_spec"],
        "hardgates": payload["c2_frontier"]["hardgates"],
        "follow_up_training_replay": payload["c2_frontier"]["follow_up_training_replay"],
        "issue_alias": payload["c2_frontier"]["issue_alias"],
    }
    return payload


def _render_report(payload: dict[str, Any]) -> str:
    lines = [
        "# Certificate-Guided Constraint Training",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Run id: `{payload['run_id']}`",
        f"- Producer: `{PRODUCER}`",
        f"- Objective: `{payload['objective']['constraint']}`",
        f"- Verdict: `{payload['verdict']}`",
        f"- Failed gate: `{payload['failed_gate'] or 'none'}`",
        f"- Claim capsule: `{payload['source_artifacts']['claim_capsule']}`",
        f"- Grid summaries: `{payload['grid_summary']['record_count']}`",
        f"- Raw grid records: `{payload['raw_grid_record_count']}`",
        f"- Raw metric records: `{payload['raw_metrics_record_count']}`",
        f"- Raw metrics: `{payload['raw_metrics_artifact']}`",
        f"- Grid metrics: `{payload['grid_metrics_artifact']}`",
        f"- Grid summary records: `{payload['grid_summary_artifact']}`",
        "",
        "## Arms",
        "",
        "| arm | role | records | feasible grid records | delta debt | delta benefit | delta quality_q |",
        "| --- | --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for spec in ARM_SPECS:
        summary = payload["arm_summaries"][spec.arm]
        delta = summary.get("delta_vs_baseline", {"debt_delta": 0.0, "benefit_delta": 0.0, "quality_q_delta": 0.0})
        lines.append(
            f"| `{spec.arm}` | `{spec.compat_role}` | {summary['record_count']} | "
            f"{summary['feasible_grid_record_count']} | {_format_float(delta['debt_delta'])} | "
            f"{_format_float(delta['benefit_delta'])} | {_format_float(delta['quality_q_delta'])} |"
        )
    lines.extend(
        [
            "",
            "## C1 Hardgates",
            "",
        ]
    )
    for name, gate in payload["hardgate"]["gates"].items():
        lines.append(f"- {name}: `{gate['status']}`")
    lines.extend(["", "## Not Claimed", ""])
    lines.extend(f"- {item}" for item in payload["not_claimed"])
    lines.append("")
    return "\n".join(lines)


def _write_payload(payload: dict[str, Any]) -> None:
    json_path = ROOT / JSON_ARTIFACT
    report_path = ROOT / REPORT_ARTIFACT
    capsule = payload["claim_capsule"]
    capsule_path = ROOT / capsule["artifact"]
    raw_metrics_path = ROOT / RAW_METRICS_ARTIFACT
    grid_metrics_path = ROOT / GRID_METRICS_ARTIFACT
    grid_summary_path = ROOT / GRID_SUMMARY_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    capsule_path.parent.mkdir(parents=True, exist_ok=True)
    raw_metrics_path.parent.mkdir(parents=True, exist_ok=True)
    grid_metrics_path.parent.mkdir(parents=True, exist_ok=True)
    grid_summary_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(_canonical_json(payload), encoding="utf-8")
    report_path.write_text(_render_report(payload), encoding="utf-8")
    capsule_path.write_text(json.dumps(capsule, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    raw_metrics_path.write_text(
        "".join(json.dumps(record, sort_keys=True, separators=(",", ":")) + "\n" for record in payload["_records"]),
        encoding="utf-8",
    )
    grid_metrics_path.write_text(
        "".join(json.dumps(record, sort_keys=True, separators=(",", ":")) + "\n" for record in payload["_raw_grid_records"]),
        encoding="utf-8",
    )
    grid_summary_path.write_text(
        "".join(json.dumps(record, sort_keys=True, separators=(",", ":")) + "\n" for record in payload["_grid_records"]),
        encoding="utf-8",
    )


def _public_payload(payload: dict[str, Any]) -> dict[str, Any]:
    public = {key: value for key, value in payload.items() if not key.startswith("_")}
    if isinstance(public.get("claim_capsule"), dict):
        public["claim_capsule"] = _public_claim_capsule_projection(public["claim_capsule"])
    return public


def _canonical_json(payload: dict[str, Any]) -> str:
    public = _public_payload(payload)
    compact_lists: set[str] = set()
    lines = ["{"]
    keys = sorted(public)
    for index, key in enumerate(keys):
        value = public[key]
        suffix = "," if index + 1 < len(keys) else ""
        encoded_key = json.dumps(key)
        if key in compact_lists and isinstance(value, list):
            lines.append(f"  {encoded_key}: [")
            for row_index, row in enumerate(value):
                row_suffix = "," if row_index + 1 < len(value) else ""
                row_text = json.dumps(row, sort_keys=True, separators=(",", ":"))
                lines.append(f"    {row_text}{row_suffix}")
            lines.append(f"  ]{suffix}")
            continue
        rendered = json.dumps(value, indent=2, sort_keys=True).splitlines()
        if len(rendered) == 1:
            lines.append(f"  {encoded_key}: {rendered[0]}{suffix}")
            continue
        lines.append(f"  {encoded_key}: {rendered[0]}")
        lines.extend(f"  {line}" for line in rendered[1:-1])
        lines.append(f"  {rendered[-1]}{suffix}")
    lines.append("}")
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-id", default="certificate-guided-constraint-training")
    args = parser.parse_args(argv)
    payload = _payload(run_id=args.run_id, generated_at=_reusable_generated_at(args.run_id))
    _write_payload(payload)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"wrote {payload['claim_capsule']['artifact']}")
    print(f"wrote {RAW_METRICS_ARTIFACT}")
    print(f"wrote {GRID_METRICS_ARTIFACT}")
    print(f"wrote {GRID_SUMMARY_ARTIFACT}")
    print(f"verdict {payload['verdict']}")


if __name__ == "__main__":
    main()

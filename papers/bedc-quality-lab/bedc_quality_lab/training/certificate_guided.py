"""Certificate-guided objective helpers for lab-local training runners."""

from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Any, Iterable, Mapping

from bedc_quality_lab.cost_protocol import REQUIRED_DEBT_ROWS
from bedc_quality_lab.ledger import LedgerRowKey


@dataclass(frozen=True)
class CertificateGuidedWeights:
    lambda_s: float = 0.25
    lambda_m: float = 0.50
    lambda_l: float = 0.75
    lambda_c: float = 1.00


@dataclass(frozen=True)
class CertificateGuidedLossBreakdown:
    margin: float
    stability: float
    ledger: float
    coverage: float
    deterministic_fallback: bool
    torch_arm: bool


def _finite_nonnegative(name: str, value: float) -> float:
    scalar = float(value)
    if not math.isfinite(scalar):
        raise ValueError(f"{name} must be finite")
    return max(0.0, scalar)


def _finite(name: str, value: float) -> float:
    scalar = float(value)
    if not math.isfinite(scalar):
        raise ValueError(f"{name} must be finite")
    return scalar


def _row_key(row: Any) -> LedgerRowKey:
    if isinstance(row, LedgerRowKey):
        return row
    if isinstance(row, Mapping):
        return LedgerRowKey(str(row["kind"]), str(row["residue"]))
    return LedgerRowKey(str(getattr(row, "kind")), str(getattr(row, "residue")))


def _row_status(row: Any) -> str:
    if isinstance(row, LedgerRowKey):
        return "open"
    if isinstance(row, Mapping):
        return str(row.get("status", "open"))
    return str(getattr(row, "status", "open"))


def _row_score(row: Any) -> float | None:
    if isinstance(row, LedgerRowKey):
        return None
    value = row.get("score") if isinstance(row, Mapping) else getattr(row, "score", None)
    if value is None:
        return None
    return _finite_nonnegative("ledger row score", float(value))


def margin_loss(quality_margin: float) -> float:
    return max(0.0, -_finite("quality_margin", quality_margin))


def stability_loss(stability_gap: float) -> float:
    return _finite_nonnegative("stability_gap", stability_gap)


def ledger_loss(ledger_rows: Iterable[Any], cost_protocol: Any) -> float:
    rows = tuple(ledger_rows)
    cost_protocol.validate_required_rows(REQUIRED_DEBT_ROWS)
    row_keys = frozenset(_row_key(row) for row in rows)
    missing = REQUIRED_DEBT_ROWS - row_keys
    if missing:
        labels = ", ".join(f"{row.kind}/{row.residue}" for row in sorted(missing))
        raise ValueError(f"ledger rows missing required debt rows: {labels}")

    total = 0.0
    for row in rows:
        key = _row_key(row)
        upper = _finite_nonnegative("cost protocol weight", cost_protocol.weight(key))
        if _row_status(row) == "closed":
            continue
        score = _row_score(row)
        total += upper if score is None else min(score, upper)
    return float(total)


def coverage_loss(
    unlogged_error_rate: float,
    critical_unlogged_error_rate: float,
) -> float:
    return _finite_nonnegative("unlogged_error_rate", unlogged_error_rate) + _finite_nonnegative(
        "critical_unlogged_error_rate",
        critical_unlogged_error_rate,
    )


def total_loss(
    task_loss: float,
    breakdown: CertificateGuidedLossBreakdown,
    weights: CertificateGuidedWeights,
) -> float:
    task = _finite_nonnegative("task_loss", task_loss)
    return float(
        task
        + float(weights.lambda_s) * breakdown.stability
        + float(weights.lambda_m) * breakdown.margin
        + float(weights.lambda_l) * breakdown.ledger
        + float(weights.lambda_c) * breakdown.coverage
    )


@dataclass(frozen=True)
class ConstraintThresholds:
    alpha: float
    beta: float
    gamma: float


@dataclass(frozen=True)
class ConstraintLambdas:
    lambda_uer: float
    lambda_benefit: float
    lambda_debt: float


def relu(value: float) -> float:
    return max(0.0, _finite("value", value))


def estimate_uer(record: Mapping[str, Any]) -> float:
    return _finite_nonnegative("uer", float(record["unlogged_error_rate"]))


def estimate_benefit(record: Mapping[str, Any]) -> float:
    return _finite("benefit", float(record["quality_benefit"]))


def estimate_debt(record: Mapping[str, Any]) -> float:
    return _finite_nonnegative("debt", float(record["quality_debt"]))


def lagrangian_penalty(
    *,
    uer_estimate: float,
    benefit_proxy: float,
    debt_estimate: float,
    thresholds: ConstraintThresholds,
    lambdas: ConstraintLambdas,
) -> dict[str, float]:
    uer_violation = relu(float(uer_estimate) - float(thresholds.alpha))
    benefit_violation = relu(float(thresholds.beta) - float(benefit_proxy))
    debt_violation = relu(float(debt_estimate) - float(thresholds.gamma))
    return {
        "uer_violation": uer_violation,
        "benefit_violation": benefit_violation,
        "debt_violation": debt_violation,
        "uer_penalty": float(lambdas.lambda_uer) * uer_violation,
        "benefit_penalty": float(lambdas.lambda_benefit) * benefit_violation,
        "debt_penalty": float(lambdas.lambda_debt) * debt_violation,
    }


def constrained_lagrangian_loss(
    *,
    task_loss: float,
    uer_estimate: float,
    benefit_proxy: float,
    debt_estimate: float,
    thresholds: ConstraintThresholds,
    lambdas: ConstraintLambdas,
) -> dict[str, float]:
    task = _finite_nonnegative("task_loss", task_loss)
    penalty = lagrangian_penalty(
        uer_estimate=uer_estimate,
        benefit_proxy=benefit_proxy,
        debt_estimate=debt_estimate,
        thresholds=thresholds,
        lambdas=lambdas,
    )
    total = task + penalty["uer_penalty"] + penalty["benefit_penalty"] + penalty["debt_penalty"]
    return {"task_loss": task, "loss": float(total), **penalty}


def pareto_dominates(candidate: Mapping[str, Any], baseline: Mapping[str, Any]) -> bool:
    candidate_values = {
        "task_loss": float(candidate["performance"]["task_loss"]),
        "uer": estimate_uer(candidate),
        "benefit": estimate_benefit(candidate),
        "debt": estimate_debt(candidate),
        "quality_q": float(candidate["quality_q"]),
    }
    baseline_values = {
        "task_loss": float(baseline["performance"]["task_loss"]),
        "uer": estimate_uer(baseline),
        "benefit": estimate_benefit(baseline),
        "debt": estimate_debt(baseline),
        "quality_q": float(baseline["quality_q"]),
    }
    weak = (
        candidate_values["task_loss"] <= baseline_values["task_loss"]
        and candidate_values["uer"] <= baseline_values["uer"]
        and candidate_values["benefit"] >= baseline_values["benefit"]
        and candidate_values["debt"] <= baseline_values["debt"]
        and candidate_values["quality_q"] >= baseline_values["quality_q"]
    )
    strict = any(
        (
            candidate_values["task_loss"] < baseline_values["task_loss"],
            candidate_values["uer"] < baseline_values["uer"],
            candidate_values["benefit"] > baseline_values["benefit"],
            candidate_values["debt"] < baseline_values["debt"],
            candidate_values["quality_q"] > baseline_values["quality_q"],
        )
    )
    return bool(weak and strict)


def build_claim_capsule(
    *,
    run_id: str,
    generated_at: str,
    producer: str,
    report_artifact: str,
    capsule_artifact: str,
    terminal_verdict: str,
    failed_gate: str | None,
    what_was_learned: str,
    hardgate: Mapping[str, Any],
    claim_gate: Mapping[str, Any],
    source_evidence: Mapping[str, Any],
    prior_observation: Mapping[str, Any] | None,
    not_claimed: Iterable[str],
) -> dict[str, Any]:
    source_evidence_payload = dict(source_evidence)
    if source_evidence_payload.get("prior_observation_pointer") == "$.prior_observation":
        source_evidence_payload["prior_observation_pointer"] = "$.claim_capsule.prior_observation"
    capsule = {
        "schema_id": "bedc.quality.claim_capsule",
        "run_id": str(run_id),
        "generated_at": generated_at,
        "producer": producer,
        "artifact": capsule_artifact,
        "report_artifact": report_artifact,
        "terminal_verdict": terminal_verdict,
        "failed_gate": failed_gate,
        "what_was_learned": what_was_learned,
        "hardgate": dict(hardgate),
        "claim_gate": dict(claim_gate),
        "source_evidence": source_evidence_payload,
        "prior_observation": {} if prior_observation is None else dict(prior_observation),
        "not_claimed": list(not_claimed),
        "revocable": True,
    }
    if terminal_verdict.startswith("DN") or failed_gate is not None:
        if not capsule["failed_gate"]:
            raise ValueError("DN claim capsule requires failed_gate")
        if not capsule["what_was_learned"]:
            raise ValueError("DN claim capsule requires what_was_learned")
    return capsule

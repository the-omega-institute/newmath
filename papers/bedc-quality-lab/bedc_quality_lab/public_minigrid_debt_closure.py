"""Debt decomposition and risk calibration for public MiniGrid BEDC-JEPA evidence."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

import numpy as np

from bedc_quality_lab.bedc_jepa_metrics import (
    bedc_debt_score,
    binary_accuracy,
    certified_coverage,
    false_claim_rate,
    gap_detection_auc,
    unlogged_error_rate,
)
from bedc_quality_lab.public_minigrid_native_benchmark import (
    DEFAULT_ENVIRONMENT_ID,
    _calibrate_gap_head,
    _collect_examples,
    _dependency_status,
    _fit_head,
    _margin_gap_score,
)


SYSTEM_NAMES = {
    "S0": "public-minigrid-jepa-style-latent-only",
    "S1": "public-minigrid-posthoc-probe",
    "S2": "public-minigrid-posthoc-evidence-envelope",
    "S3": "public-minigrid-trained-bedc-jepa-readout",
}

GAP_THRESHOLDS = (0.05, 0.10, 0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.80, 0.90, 0.95)
RISK_BUDGETS = (0.05, 0.10, 0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.80, 0.90, 0.95)
CONFORMAL_ALPHAS = (0.20, 0.10, 0.05, 0.02, 0.01)
PREDICATE_NAMES = (
    "door_key_context_visible",
    "has_key",
    "door_open_or_unlocked",
    "goal_reachable_with_current_state",
    "unsafe_transition",
)


def _analysis_contract(
    *,
    environment_id: str,
    train_count: int,
    test_count: int,
    planning_state_count: int,
    seed: int,
) -> dict[str, Any]:
    return {
        "run_command": "python scripts/build_public_minigrid_debt_closure.py",
        "environment_id": environment_id,
        "seed": float(seed),
        "train_seed": float(seed),
        "test_seed": float(seed + 1),
        "train_count": float(train_count),
        "test_count": float(test_count),
        "planning_state_count": float(planning_state_count),
        "systems": SYSTEM_NAMES,
        "debt_component_weights": {
            "silent_debt": 0.40,
            "false_claim_debt": 0.30,
            "ranking_debt": 0.20,
            "coverage_debt": 0.10,
        },
        "gap_thresholds": [float(item) for item in GAP_THRESHOLDS],
        "risk_budgets": [float(item) for item in RISK_BUDGETS],
        "risk_constrained_planning_rule": (
            "select the highest distinction score among candidate actions whose predicted gap is within "
            "the declared risk budget; if no action is within budget, emit no_certified_plan"
        ),
        "conformal_alphas": [float(item) for item in CONFORMAL_ALPHAS],
        "predicate_surfaces": list(PREDICATE_NAMES),
        "source_split": "train split fits readouts; test split reports debt, coverage, conformal rows, and planning states",
        "claim_boundary": "public MiniGrid debt and planning accounting only; not public benchmark superiority or native V-JEPA2-AC reproduction",
    }


def _system_scores(train: dict[str, np.ndarray], test: dict[str, np.ndarray]) -> tuple[dict[str, dict[str, np.ndarray]], dict[str, Any]]:
    distinction_head = _fit_head(train["features"], train["labels"])
    gap_head = _calibrate_gap_head(_fit_head(train["features"], train["gaps"]), train["features"], train["gaps"])
    s0_claim = np.full(test["labels"].shape[0], float(np.mean(train["labels"])), dtype=np.float64)
    s1_claim = distinction_head.score(test["features"])
    zeros = np.zeros_like(s0_claim)
    scores = {
        "S0": {"claim": s0_claim, "gap": zeros},
        "S1": {"claim": s1_claim, "gap": zeros},
        "S2": {"claim": s1_claim, "gap": _margin_gap_score(s1_claim)},
        "S3": {"claim": s1_claim, "gap": gap_head.score(test["features"])},
    }
    return scores, {"distinction": distinction_head, "gap": gap_head}


def _predicate_labels(batch: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    features = np.asarray(batch["features"], dtype=np.float64)
    labels = np.asarray(batch["labels"], dtype=bool)
    gaps = np.asarray(batch["gaps"], dtype=bool)
    visible = features[:, -28:-25] if features.shape[1] >= 28 else np.zeros((features.shape[0], 3), dtype=np.float64)
    has_key = visible[:, 0] > 0.5
    door_open = visible[:, 1] > 0.5
    goal_reachable = visible[:, 2] > 0.5
    return {
        "door_key_context_visible": labels,
        "has_key": has_key,
        "door_open_or_unlocked": door_open,
        "goal_reachable_with_current_state": goal_reachable,
        "unsafe_transition": gaps,
    }


def _predicate_source_status(name: str, labels: np.ndarray) -> str:
    if name == "door_key_context_visible":
        return "closed"
    values = np.asarray(labels, dtype=bool)
    return "closed" if np.any(values) and np.any(~values) else "source_gap"


def _conformal_rows(
    *,
    train_scores: np.ndarray,
    train_labels: np.ndarray,
    test_scores: np.ndarray,
    test_labels: np.ndarray,
    gap_labels: np.ndarray,
) -> list[dict[str, float]]:
    train_pred = train_scores >= 0.5
    nonconformity = np.where(train_pred == train_labels, 1.0 - np.abs(train_scores - 0.5) * 2.0, 1.0)
    rows = []
    for alpha in CONFORMAL_ALPHAS:
        cutoff = float(np.quantile(nonconformity, min(1.0, max(0.0, 1.0 - float(alpha)))))
        test_pred = test_scores >= 0.5
        singleton = (1.0 - np.abs(test_scores - 0.5) * 2.0) <= cutoff
        wrong = test_pred != test_labels
        certified_coverage_value = float(np.mean(singleton)) if singleton.size else 0.0
        unlogged = float(np.mean(wrong & singleton)) if singleton.size else 0.0
        gap_rate = float(np.mean(~singleton)) if singleton.size else 0.0
        outside_gap_accuracy = float(np.mean(test_pred[singleton] == test_labels[singleton])) if np.any(singleton) else 1.0
        false_claim = false_claim_rate(test_scores, test_labels, gap_labels)
        gap_auc = gap_detection_auc(np.where(singleton, 0.0, 1.0), gap_labels)
        rows.append(
            {
                "alpha": float(alpha),
                "nonconformity_cutoff": cutoff,
                "certified_coverage": certified_coverage_value,
                "unlogged_error_rate": unlogged,
                "gap_rate": gap_rate,
                "outside_gap_accuracy": outside_gap_accuracy,
                "debt_score": bedc_debt_score(
                    unlogged_error=unlogged,
                    false_claim=false_claim,
                    gap_auc=gap_auc,
                    certified=certified_coverage_value,
                ),
            }
        )
    return rows


def _conformal_certified_coverage(
    train: dict[str, np.ndarray],
    test: dict[str, np.ndarray],
) -> dict[str, Any]:
    train_labels_by_predicate = _predicate_labels(train)
    test_labels_by_predicate = _predicate_labels(test)
    result = {}
    for name in PREDICATE_NAMES:
        train_labels = train_labels_by_predicate[name]
        test_labels = test_labels_by_predicate[name]
        source_status = _predicate_source_status(name, train_labels)
        if source_status == "closed":
            head = _fit_head(train["features"], train_labels)
            train_scores = head.score(train["features"])
            test_scores = head.score(test["features"])
            rows = _conformal_rows(
                train_scores=train_scores,
                train_labels=train_labels,
                test_scores=test_scores,
                test_labels=test_labels,
                gap_labels=test["gaps"],
            )
        else:
            rows = [
                {
                    "alpha": float(alpha),
                    "nonconformity_cutoff": 1.0,
                    "certified_coverage": 0.0,
                    "unlogged_error_rate": 0.0,
                    "gap_rate": 1.0,
                    "outside_gap_accuracy": 1.0,
                    "debt_score": 1.0,
                }
                for alpha in CONFORMAL_ALPHAS
            ]
        result[name] = {
            "source_status": source_status,
            "positive_rate_train": float(np.mean(train_labels)) if train_labels.size else 0.0,
            "positive_rate_test": float(np.mean(test_labels)) if test_labels.size else 0.0,
            "rows": rows,
        }
    return {
        "alphas": [float(alpha) for alpha in CONFORMAL_ALPHAS],
        "claim_rule": "singleton conformal set emits claim; non-singleton set emits gap",
        "predicates": result,
    }


def _gap_brier(gap_scores: np.ndarray, gap_labels: np.ndarray) -> float:
    scores = np.asarray(gap_scores, dtype=np.float64)
    labels = np.asarray(gap_labels, dtype=np.float64)
    return float(np.mean((scores - labels) * (scores - labels)))


def _expected_calibration_error(gap_scores: np.ndarray, gap_labels: np.ndarray, *, bins: int = 10) -> float:
    scores = np.asarray(gap_scores, dtype=np.float64)
    labels = np.asarray(gap_labels, dtype=np.float64)
    total = scores.size
    if total == 0:
        return 0.0
    error = 0.0
    edges = np.linspace(0.0, 1.0, bins + 1)
    for index in range(bins):
        left = edges[index]
        right = edges[index + 1]
        if index == bins - 1:
            mask = (scores >= left) & (scores <= right)
        else:
            mask = (scores >= left) & (scores < right)
        if not np.any(mask):
            continue
        error += float(np.mean(mask)) * abs(float(np.mean(scores[mask])) - float(np.mean(labels[mask])))
    return float(error)


def _debt_components(claim_scores: np.ndarray, gap_scores: np.ndarray, labels: np.ndarray, gaps: np.ndarray, *, gap_threshold: float = 0.5) -> dict[str, float]:
    unlogged = unlogged_error_rate(claim_scores, labels, gap_scores, gap_threshold=gap_threshold)
    false_claim = false_claim_rate(claim_scores, labels, gaps)
    gap_auc = gap_detection_auc(gap_scores, gaps)
    coverage = certified_coverage(gap_scores, gap_threshold=gap_threshold)
    weighted = {
        "silent_debt": 0.40 * unlogged,
        "false_claim_debt": 0.30 * false_claim,
        "ranking_debt": 0.20 * (1.0 - gap_auc),
        "coverage_debt": 0.10 * (1.0 - coverage),
    }
    return {
        "distinction_accuracy": binary_accuracy(claim_scores, labels),
        "unlogged_error_rate": unlogged,
        "false_claim_rate": false_claim,
        "gap_auc": gap_auc,
        "certified_coverage": coverage,
        "bedc_debt_score": bedc_debt_score(
            unlogged_error=unlogged,
            false_claim=false_claim,
            gap_auc=gap_auc,
            certified=coverage,
        ),
        **weighted,
        "weighted_component_sum": float(sum(weighted.values())),
        "gap_brier": _gap_brier(gap_scores, gaps),
        "gap_ece": _expected_calibration_error(gap_scores, gaps),
        "abstention_rate": float(1.0 - coverage),
    }


def _threshold_curve_for_system(
    system_code: str,
    claim_scores: np.ndarray,
    gap_scores: np.ndarray,
    labels: np.ndarray,
    gaps: np.ndarray,
) -> dict[str, Any]:
    rows = []
    for threshold in GAP_THRESHOLDS:
        row = _debt_components(claim_scores, gap_scores, labels, gaps, gap_threshold=threshold)
        row["gap_threshold"] = float(threshold)
        rows.append(row)
    best = min(rows, key=lambda row: (row["bedc_debt_score"], row["unlogged_error_rate"], -row["certified_coverage"]))
    return {
        "system": system_code,
        "system_name": SYSTEM_NAMES[system_code],
        "rows": rows,
        "best_threshold": float(best["gap_threshold"]),
        "best_debt_score": float(best["bedc_debt_score"]),
        "best_unlogged_error_rate": float(best["unlogged_error_rate"]),
        "best_certified_coverage": float(best["certified_coverage"]),
    }


def _risk_constrained_rows(planning_states: list[dict[str, Any]], heads: dict[str, Any]) -> list[dict[str, Any]]:
    rows = []
    for budget in RISK_BUDGETS:
        selected_successes = []
        effective_successes = []
        high_gaps = []
        predicted_gaps = []
        no_plan = 0
        for state in planning_states:
            distinction_scores = heads["distinction"].score(state["features"])
            gap_scores = heads["gap"].score(state["features"])
            allowed = gap_scores <= float(budget)
            if not np.any(allowed):
                no_plan += 1
                effective_successes.append(False)
                continue
            allowed_indices = np.flatnonzero(allowed)
            selected = int(allowed_indices[np.argmax(distinction_scores[allowed])])
            success = bool(state["labels"][selected])
            high_gap = bool(state["gaps"][selected])
            selected_successes.append(success)
            effective_successes.append(success)
            high_gaps.append(high_gap)
            predicted_gaps.append(float(gap_scores[selected]))
        total = len(planning_states)
        selected_count = len(selected_successes)
        no_certified_plan_rate = float(no_plan / total) if total else 0.0
        decision_status = "no_certified_plan" if selected_count == 0 and total else "selected_plan"
        rows.append(
            {
                "risk_budget": float(budget),
                "planning_state_count": float(total),
                "selected_plan_count": float(selected_count),
                "decision_status": decision_status,
                "no_certified_plan_rate": no_certified_plan_rate,
                "selected_success_rate": float(np.mean(selected_successes)) if selected_successes else 0.0,
                "effective_success_rate": float(np.mean(effective_successes)) if effective_successes else 0.0,
                "high_gap_state_rate": float(np.mean(high_gaps)) if high_gaps else 0.0,
                "mean_selected_predicted_gap": float(np.mean(predicted_gaps)) if predicted_gaps else 0.0,
            }
        )
    return rows


def _risk_success_pareto(planning_rows: list[dict[str, Any]]) -> dict[str, Any]:
    if not planning_rows:
        empty = {
            "risk_budget": 0.0,
            "effective_success_rate": 0.0,
            "high_gap_state_rate": 0.0,
            "no_certified_plan_rate": 1.0,
        }
        return {"baseline": empty, "best_low_gap": empty, "best_success_under_half_risk": empty}
    baseline = planning_rows[-1]
    low_gap = min(planning_rows, key=lambda row: (row["high_gap_state_rate"], row["no_certified_plan_rate"], -row["effective_success_rate"]))
    half_risk = [row for row in planning_rows if row["risk_budget"] <= 0.5]
    best_half = max(half_risk or planning_rows, key=lambda row: (row["effective_success_rate"], -row["high_gap_state_rate"], -row["no_certified_plan_rate"]))
    frontier_rows = []
    baseline_high_gap = float(baseline["high_gap_state_rate"])
    baseline_success = float(baseline["effective_success_rate"])
    baseline_no_plan = float(baseline["no_certified_plan_rate"])
    for row in planning_rows:
        frontier_row = dict(row)
        frontier_row["baseline_minus_high_gap_rate"] = float(baseline_high_gap - float(row["high_gap_state_rate"]))
        frontier_row["success_delta_vs_baseline"] = float(float(row["effective_success_rate"]) - baseline_success)
        frontier_row["no_certified_plan_delta_vs_baseline"] = float(float(row["no_certified_plan_rate"]) - baseline_no_plan)
        if frontier_row["baseline_minus_high_gap_rate"] > 0.0 and frontier_row["success_delta_vs_baseline"] >= 0.0:
            claim_status = "risk_improvement"
        elif frontier_row["baseline_minus_high_gap_rate"] > 0.0:
            claim_status = "risk_success_tradeoff"
        elif frontier_row["no_certified_plan_rate"] >= 1.0:
            claim_status = "no_certified_plan_under_budget"
        else:
            claim_status = "no_risk_improvement"
        frontier_row["claim_status"] = claim_status
        frontier_rows.append(frontier_row)
    return {
        "baseline": {
            **baseline,
            "risk_budget": 1.0,
        },
        "best_low_gap": low_gap,
        "best_success_under_half_risk": best_half,
        "frontier_rows": frontier_rows,
        "claim_rule": (
            "risk_improvement requires lower high-gap rate without success loss; otherwise lower risk with "
            "success loss is recorded as a risk-success tradeoff, and empty feasible sets are recorded as "
            "no_certified_plan_under_budget"
        ),
    }


def _loss_ablation(scores: dict[str, dict[str, np.ndarray]], labels: np.ndarray, gaps: np.ndarray) -> dict[str, Any]:
    full = _debt_components(scores["S3"]["claim"], scores["S3"]["gap"], labels, gaps)
    minus_unlogged_gap = np.maximum(scores["S3"]["gap"] * 0.75, _margin_gap_score(scores["S3"]["claim"]) * 0.25)
    minus_gap = np.zeros_like(scores["S3"]["gap"])
    posthoc = _margin_gap_score(scores["S3"]["claim"])
    calibrated_only = scores["S3"]["gap"]
    systems = {
        "full_s3": full,
        "minus_unlogged_penalty": _debt_components(scores["S3"]["claim"], minus_unlogged_gap, labels, gaps),
        "minus_gap_bce": _debt_components(scores["S3"]["claim"], minus_gap, labels, gaps),
        "posthoc_conformal_only": _debt_components(scores["S3"]["claim"], posthoc, labels, gaps),
        "frozen_encoder_gap_calibration_only": _debt_components(scores["S3"]["claim"], calibrated_only, labels, gaps),
    }
    return {
        "systems": systems,
        "mechanism_readout": {
            "unlogged_penalty_effect": float(
                systems["minus_unlogged_penalty"]["unlogged_error_rate"] - systems["full_s3"]["unlogged_error_rate"]
            ),
            "gap_bce_effect": float(systems["minus_gap_bce"]["gap_auc"] - systems["full_s3"]["gap_auc"]),
            "posthoc_gap_debt_delta": float(
                systems["posthoc_conformal_only"]["bedc_debt_score"] - systems["full_s3"]["bedc_debt_score"]
            ),
            "not_claimed": "local score ablation; not a retraining ablation",
        },
    }


def _debt_interpretation(decomposition: dict[str, dict[str, float]]) -> dict[str, Any]:
    s0 = decomposition["S0"]
    s3 = decomposition["S3"]
    changes = {
        "silent_debt_change_s0_minus_s3": float(s0["silent_debt"] - s3["silent_debt"]),
        "coverage_debt_change_s0_minus_s3": float(s0["coverage_debt"] - s3["coverage_debt"]),
        "ranking_debt_change_s0_minus_s3": float(s0["ranking_debt"] - s3["ranking_debt"]),
        "total_debt_change_s0_minus_s3": float(s0["bedc_debt_score"] - s3["bedc_debt_score"]),
    }
    if changes["silent_debt_change_s0_minus_s3"] > 0.0 and changes["coverage_debt_change_s0_minus_s3"] < 0.0:
        diagnosis = "silent debt falls while coverage debt rises"
    elif changes["ranking_debt_change_s0_minus_s3"] > 0.0 and changes["total_debt_change_s0_minus_s3"] <= 0.0:
        diagnosis = "gap ranking improves but total debt is not closed"
    elif changes["total_debt_change_s0_minus_s3"] > 0.0:
        diagnosis = "total debt decreases under the current score"
    else:
        diagnosis = "public debt remains open under the current score"
    return {
        "diagnosis": diagnosis,
        "changes": changes,
        "not_claimed": [
            "public benchmark superiority",
            "closed total debt on all public MiniGrid seeds",
            "native V-JEPA2-AC checkpoint reproduction",
            "optimal planning calibration",
        ],
    }


def _unavailable_packet(environment_id: str, deps: dict[str, str]) -> dict[str, Any]:
    return {
        "schema_id": "bedc-jepa-public-debt-closure-analysis",
        "status": "unavailable",
        "environment_id": environment_id,
        "dependency_status": deps,
        "debt_decomposition": {},
        "certified_coverage_curve": {},
        "conformal_certified_coverage": {},
        "risk_constrained_planning": {},
        "risk_success_pareto": {},
        "loss_ablation": {},
        "cannot_claim": ["public MiniGrid debt closure analysis was not executed in this environment"],
    }


def build_public_minigrid_debt_closure_analysis(
    *,
    environment_id: str = DEFAULT_ENVIRONMENT_ID,
    train_count: int = 128,
    test_count: int = 128,
    planning_state_count: int = 32,
    seed: int = 20260602,
) -> dict[str, Any]:
    deps = _dependency_status()
    if not all(status == "installed" for status in deps.values()):
        return _unavailable_packet(environment_id, deps)

    contract = _analysis_contract(
        environment_id=environment_id,
        train_count=train_count,
        test_count=test_count,
        planning_state_count=planning_state_count,
        seed=seed,
    )
    train, _, action_count = _collect_examples(
        environment_id=environment_id,
        sample_count=train_count,
        planning_state_count=0,
        seed=seed,
    )
    test, planning_states, _ = _collect_examples(
        environment_id=environment_id,
        sample_count=test_count,
        planning_state_count=planning_state_count,
        seed=seed + 1,
    )
    scores, heads = _system_scores(train, test)
    decomposition = {
        code: {
            "system_name": SYSTEM_NAMES[code],
            **_debt_components(data["claim"], data["gap"], test["labels"], test["gaps"]),
        }
        for code, data in scores.items()
    }
    coverage_curves = {
        code: _threshold_curve_for_system(code, data["claim"], data["gap"], test["labels"], test["gaps"])
        for code, data in scores.items()
    }
    planning_rows = _risk_constrained_rows(planning_states, heads)
    conformal = _conformal_certified_coverage(train, test)
    pareto = _risk_success_pareto(planning_rows)
    ablation = _loss_ablation(scores, test["labels"], test["gaps"])
    return {
        "schema_id": "bedc-jepa-public-debt-closure-analysis",
        "status": "executed",
        "environment_id": environment_id,
        "seed": float(seed),
        "train_count": float(train_count),
        "test_count": float(test_count),
        "planning_state_count": float(len(planning_states)),
        "action_count": float(action_count),
        "dependency_status": deps,
        "analysis_contract": contract,
        "debt_decomposition": decomposition,
        "certified_coverage_curve": {
            "gap_thresholds": [float(item) for item in GAP_THRESHOLDS],
            "systems": coverage_curves,
        },
        "risk_constrained_planning": {
            "risk_budgets": [float(item) for item in RISK_BUDGETS],
            "rows": planning_rows,
        },
        "risk_success_pareto": pareto,
        "conformal_certified_coverage": conformal,
        "loss_ablation": ablation,
        "interpretation": _debt_interpretation(decomposition),
        "cannot_claim": [
            "public benchmark superiority",
            "closed total debt on all public MiniGrid seeds",
            "native V-JEPA2-AC checkpoint reproduction",
            "optimal planning calibration",
        ],
    }


def build_public_debt_closure_report(packet: dict[str, Any]) -> str:
    if packet.get("status") != "executed":
        return "# BEDC-JEPA Public Debt Closure Report\n\nStatus: unavailable.\n"
    decomposition = packet["debt_decomposition"]
    s0 = decomposition["S0"]
    s3 = decomposition["S3"]
    interp = packet["interpretation"]
    best_s3 = packet["certified_coverage_curve"]["systems"]["S3"]
    planning_rows = packet["risk_constrained_planning"]["rows"]
    conformal = packet["conformal_certified_coverage"]["predicates"]["door_key_context_visible"]["rows"][0]
    pareto = packet["risk_success_pareto"]
    ablation = packet["loss_ablation"]["mechanism_readout"]
    best_planning = min(planning_rows, key=lambda row: (row["high_gap_state_rate"], row["no_certified_plan_rate"], -row["effective_success_rate"]))
    lines = [
        "# BEDC-JEPA Public Debt Closure Report",
        "",
        "## Question",
        "",
        "Public MiniGrid reduces silent failures and improves gap ranking, but aggregate debt is not fully closed.",
        "",
        "## Debt Decomposition",
        "",
        f"- S0 silent debt: `{s0['silent_debt']:.6f}`",
        f"- S3 silent debt: `{s3['silent_debt']:.6f}`",
        f"- S0 coverage debt: `{s0['coverage_debt']:.6f}`",
        f"- S3 coverage debt: `{s3['coverage_debt']:.6f}`",
        f"- S0 total debt: `{s0['bedc_debt_score']:.6f}`",
        f"- S3 total debt: `{s3['bedc_debt_score']:.6f}`",
        f"- Diagnosis: `{interp['diagnosis']}`",
        "",
        "## Certified Coverage",
        "",
        f"- Best S3 gap threshold: `{best_s3['best_threshold']:.2f}`",
        f"- Best S3 debt: `{best_s3['best_debt_score']:.6f}`",
        f"- Best S3 certified coverage: `{best_s3['best_certified_coverage']:.6f}`",
        "",
        "## Conformal Certified Claims",
        "",
        f"- DoorKey context coverage at alpha 0.20: `{conformal['certified_coverage']:.6f}`",
        f"- DoorKey context UER at alpha 0.20: `{conformal['unlogged_error_rate']:.6f}`",
        "- Predicate surfaces: `door_key_context_visible`, `has_key`, `door_open_or_unlocked`, `goal_reachable_with_current_state`, `unsafe_transition`",
        "",
        "## Risk-Constrained Planning",
        "",
        "- Rule: select the highest distinction score among actions whose predicted gap is within the risk budget; if no such action exists, record `no_certified_plan`.",
        f"- Selected risk budget: `{best_planning['risk_budget']:.2f}`",
        f"- Claim status: `{pareto['frontier_rows'][0]['claim_status']}` at the tightest recorded budget",
        f"- High-gap state rate: `{best_planning['high_gap_state_rate']:.6f}`",
        f"- Effective success rate: `{best_planning['effective_success_rate']:.6f}`",
        f"- No-certified-plan rate: `{best_planning['no_certified_plan_rate']:.6f}`",
        f"- Pareto half-risk success: `{pareto['best_success_under_half_risk']['effective_success_rate']:.6f}`",
        "",
        "## Local Ablation",
        "",
        f"- Unlogged-penalty effect: `{ablation['unlogged_penalty_effect']:.6f}`",
        f"- Post-hoc gap debt delta: `{ablation['posthoc_gap_debt_delta']:.6f}`",
        "- Boundary: `local score ablation; not a retraining ablation`",
        "",
        "## Not Claimed",
        "",
    ]
    lines.extend(f"- {item}" for item in packet["cannot_claim"])
    return "\n".join(lines) + "\n"


def write_public_minigrid_debt_closure_analysis(report_dir: str | Path) -> dict[str, Any]:
    target_dir = Path(report_dir)
    target_dir.mkdir(parents=True, exist_ok=True)
    packet = build_public_minigrid_debt_closure_analysis()
    debt_path = target_dir / "bedc_jepa_public_debt_decomposition.json"
    coverage_path = target_dir / "bedc_jepa_certified_coverage_curve.json"
    planning_path = target_dir / "bedc_jepa_risk_constrained_planning.json"
    conformal_path = target_dir / "bedc_jepa_conformal_certified_coverage.json"
    pareto_path = target_dir / "bedc_jepa_risk_success_pareto.json"
    ablation_path = target_dir / "bedc_jepa_loss_ablation.json"
    report_path = target_dir / "bedc_jepa_public_debt_closure_report.md"
    debt_path.write_text(
        json.dumps(
            {
                "schema_id": "bedc-jepa-public-debt-decomposition",
                "status": packet["status"],
                "environment_id": packet["environment_id"],
                "analysis_contract": packet.get("analysis_contract", {}),
                "debt_decomposition": packet["debt_decomposition"],
                "interpretation": packet.get("interpretation", {}),
                "cannot_claim": packet["cannot_claim"],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    coverage_path.write_text(
        json.dumps(
            {
                "schema_id": "bedc-jepa-certified-coverage-curve",
                "status": packet["status"],
                "environment_id": packet["environment_id"],
                "analysis_contract": packet.get("analysis_contract", {}),
                "certified_coverage_curve": packet["certified_coverage_curve"],
                "cannot_claim": packet["cannot_claim"],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    planning_path.write_text(
        json.dumps(
            {
                "schema_id": "bedc-jepa-risk-constrained-planning",
                "status": packet["status"],
                "environment_id": packet["environment_id"],
                "analysis_contract": packet.get("analysis_contract", {}),
                "risk_constrained_planning": packet["risk_constrained_planning"],
                "cannot_claim": packet["cannot_claim"],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    conformal_path.write_text(
        json.dumps(
            {
                "schema_id": "bedc-jepa-conformal-certified-coverage",
                "status": packet["status"],
                "environment_id": packet["environment_id"],
                "analysis_contract": packet.get("analysis_contract", {}),
                "conformal_certified_coverage": packet["conformal_certified_coverage"],
                "cannot_claim": packet["cannot_claim"],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    pareto_path.write_text(
        json.dumps(
            {
                "schema_id": "bedc-jepa-risk-success-pareto",
                "status": packet["status"],
                "environment_id": packet["environment_id"],
                "analysis_contract": packet.get("analysis_contract", {}),
                "risk_success_pareto": packet["risk_success_pareto"],
                "cannot_claim": packet["cannot_claim"],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    ablation_path.write_text(
        json.dumps(
            {
                "schema_id": "bedc-jepa-loss-ablation",
                "status": packet["status"],
                "environment_id": packet["environment_id"],
                "analysis_contract": packet.get("analysis_contract", {}),
                "loss_ablation": packet["loss_ablation"],
                "cannot_claim": [
                    *packet["cannot_claim"],
                    "full retraining loss ablation",
                ],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    report_path.write_text(build_public_debt_closure_report(packet), encoding="utf-8")
    return packet

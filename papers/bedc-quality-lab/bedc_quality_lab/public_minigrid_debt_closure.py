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


def _risk_constrained_rows(planning_states: list[dict[str, Any]], heads: dict[str, Any]) -> list[dict[str, float]]:
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
        rows.append(
            {
                "risk_budget": float(budget),
                "planning_state_count": float(total),
                "selected_plan_count": float(selected_count),
                "no_certified_plan_rate": float(no_plan / total) if total else 0.0,
                "selected_success_rate": float(np.mean(selected_successes)) if selected_successes else 0.0,
                "effective_success_rate": float(np.mean(effective_successes)) if effective_successes else 0.0,
                "high_gap_state_rate": float(np.mean(high_gaps)) if high_gaps else 0.0,
                "mean_selected_predicted_gap": float(np.mean(predicted_gaps)) if predicted_gaps else 0.0,
            }
        )
    return rows


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
        "risk_constrained_planning": {},
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
        "debt_decomposition": decomposition,
        "certified_coverage_curve": {
            "gap_thresholds": [float(item) for item in GAP_THRESHOLDS],
            "systems": coverage_curves,
        },
        "risk_constrained_planning": {
            "risk_budgets": [float(item) for item in RISK_BUDGETS],
            "rows": planning_rows,
        },
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
        "## Risk-Constrained Planning",
        "",
        f"- Selected risk budget: `{best_planning['risk_budget']:.2f}`",
        f"- High-gap state rate: `{best_planning['high_gap_state_rate']:.6f}`",
        f"- Effective success rate: `{best_planning['effective_success_rate']:.6f}`",
        f"- No-certified-plan rate: `{best_planning['no_certified_plan_rate']:.6f}`",
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
    report_path = target_dir / "bedc_jepa_public_debt_closure_report.md"
    debt_path.write_text(
        json.dumps(
            {
                "schema_id": "bedc-jepa-public-debt-decomposition",
                "status": packet["status"],
                "environment_id": packet["environment_id"],
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
                "risk_constrained_planning": packet["risk_constrained_planning"],
                "cannot_claim": packet["cannot_claim"],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    report_path.write_text(build_public_debt_closure_report(packet), encoding="utf-8")
    return packet

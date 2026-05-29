#!/usr/bin/env python3
"""Run the locked confirmatory falsification experiment for the Phase 1 bundle."""
from __future__ import annotations

import json
import math
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_PATH = REPO_ROOT / "tools" / "bio_reality" / "data" / "phase2_confirmatory_falsification_dataset.json"
EXPERIMENT_ID = "exp.phase2.confirmatory_falsification.v1"
CLAIM_ID = "phase.one.a+phase.one.b+phase.one.c"
TARGET_CLAIMS = {
    "h0.null.model.aa_class_preserving",
    "h1.leave_one_code_out.by_family",
    "h1.leave_one_codon_out.module_classification",
}
FORBIDDEN_PROMOTIONS = {
    "translation",
    "protein structure",
    "physical admissibility",
    "biological function",
    "global biological law",
    "universal mechanism",
}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def emit(result: dict[str, Any]) -> int:
    print(json.dumps(result, sort_keys=False))
    return 0


def base_result(started_at: str) -> dict[str, Any]:
    return {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "started_at": started_at,
    }


def needs_data(started_at: str) -> int:
    result = base_result(started_at)
    result.update(
        {
            "status": "needs_data",
            "completed_at": now_iso(),
            "checks": [],
            "result": {"missing_data": [str(DATA_PATH.relative_to(REPO_ROOT))]},
            "notes": "locked independent replication/falsification data is required before this claim can be tested",
        }
    )
    return emit(result)


def parse_time(value: str) -> datetime:
    text = value.strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    return datetime.fromisoformat(text)


def rows_for(data: dict[str, Any], kind: str) -> list[dict[str, Any]]:
    rows = data.get("conditions")
    if not isinstance(rows, list):
        raise ValueError("phase2_confirmatory_falsification_dataset.json must contain a conditions list")
    return [
        row
        for row in rows
        if isinstance(row, dict) and str(row.get("condition_kind") or "") == kind
    ]


def trials_for(conditions: list[dict[str, Any]]) -> list[dict[str, Any]]:
    trials: list[dict[str, Any]] = []
    for condition in conditions:
        raw = condition.get("trials")
        if not isinstance(raw, list):
            raise ValueError(f"condition {condition.get('condition_id')} must contain a trials list")
        for trial in raw:
            if not isinstance(trial, dict):
                raise ValueError("trial rows must be objects")
            trials.append(trial)
    return trials


def count_successes(trials: list[dict[str, Any]]) -> tuple[int, int]:
    successes = 0
    for trial in trials:
        if "observed_success" not in trial:
            raise ValueError(f"trial {trial.get('trial_id')} lacks observed_success")
        successes += 1 if bool(trial["observed_success"]) else 0
    return successes, len(trials)


def binomial_upper_tail(successes: int, n: int, p: float = 0.5) -> float:
    if not 0 <= successes <= n:
        raise ValueError("successes must be between 0 and n")
    return sum(math.comb(n, k) * (p ** k) * ((1.0 - p) ** (n - k)) for k in range(successes, n + 1))


def has_all_claims(data: dict[str, Any]) -> bool:
    observed = data.get("target_claim_ids")
    if not isinstance(observed, list):
        return False
    return TARGET_CLAIMS.issubset({str(item) for item in observed if isinstance(item, str)})


def no_forbidden_promotion(data: dict[str, Any]) -> bool:
    cannot_claim = data.get("cannot_claim")
    if not isinstance(cannot_claim, list):
        return False
    text = " ".join(str(item).lower() for item in cannot_claim if isinstance(item, str))
    return all(term in text for term in FORBIDDEN_PROMOTIONS)


def preregistered_before_observation(data: dict[str, Any]) -> bool:
    if data.get("pre_registered") is not True:
        return False
    preregistered_at = str(data.get("pre_registered_at") or "")
    if not preregistered_at:
        return False
    observed_times = [
        str(trial.get("observed_at") or "")
        for trial in trials_for([condition for kind in ("replication", "negative_control", "critical_ablation", "boundary_probe") for condition in rows_for(data, kind)])
    ]
    if not observed_times or any(not item for item in observed_times):
        return False
    prereg_time = parse_time(preregistered_at)
    return all(prereg_time < parse_time(item) for item in observed_times)


def frozen_protocol(data: dict[str, Any]) -> bool:
    return all(
        data.get(key) is True
        for key in (
            "fresh_independent_data",
            "analysis_code_frozen",
            "metrics_frozen",
            "exclusion_rules_frozen",
            "pass_fail_thresholds_frozen",
        )
    )


def positive_condition_check(data: dict[str, Any], kind: str, *, min_n: int, min_rate: float, max_p: float) -> dict[str, Any]:
    trials = trials_for(rows_for(data, kind))
    successes, n = count_successes(trials)
    rate = successes / n if n else 0.0
    p_value = binomial_upper_tail(successes, n) if n else 1.0
    passed = n >= min_n and rate >= min_rate and p_value <= max_p
    return {
        "passed": passed,
        "actual": {"successes": successes, "n": n, "rate": rate, "binomial_upper_tail_p": p_value},
        "expected": {"min_n": min_n, "min_rate": min_rate, "max_binomial_upper_tail_p": max_p},
    }


def absence_condition_check(data: dict[str, Any], kind: str, *, min_n: int) -> dict[str, Any]:
    trials = trials_for(rows_for(data, kind))
    successes, n = count_successes(trials)
    passed = n >= min_n and successes == 0
    return {
        "passed": passed,
        "actual": {"unexpected_successes": successes, "n": n},
        "expected": {"min_n": min_n, "unexpected_successes": 0},
    }


def main() -> int:
    started_at = now_iso()
    if not DATA_PATH.exists() or DATA_PATH.stat().st_size == 0:
        return needs_data(started_at)

    result = base_result(started_at)
    try:
        data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
        replication = positive_condition_check(data, "replication", min_n=20, min_rate=0.80, max_p=0.01)
        boundary = positive_condition_check(data, "boundary_probe", min_n=20, min_rate=0.70, max_p=0.01)
        negative = absence_condition_check(data, "negative_control", min_n=10)
        ablation = absence_condition_check(data, "critical_ablation", min_n=10)
        checks = [
            {
                "name": "external_confirmatory_dataset_loaded",
                "passed": isinstance(data, dict) and DATA_PATH.exists(),
                "actual": str(DATA_PATH.relative_to(REPO_ROOT)),
                "expected": "curated external confirmatory dataset file",
            },
            {
                "name": "frozen_protocol_declared",
                "passed": frozen_protocol(data),
                "actual": {
                    key: data.get(key)
                    for key in (
                        "fresh_independent_data",
                        "analysis_code_frozen",
                        "metrics_frozen",
                        "exclusion_rules_frozen",
                        "pass_fail_thresholds_frozen",
                    )
                },
                "expected": "all protocol freeze flags true",
            },
            {
                "name": "preregistered_before_observation",
                "passed": preregistered_before_observation(data),
                "actual": data.get("pre_registered_at"),
                "expected": "pre-registration timestamp precedes every trial observation timestamp",
            },
            {
                "name": "all_target_claims_represented",
                "passed": has_all_claims(data),
                "actual": data.get("target_claim_ids"),
                "expected": sorted(TARGET_CLAIMS),
            },
            {"name": "independent_replication_strong_binomial", **replication},
            {"name": "negative_control_absence", **negative},
            {"name": "critical_ablation_absence", **ablation},
            {"name": "boundary_probe_strong_binomial", **boundary},
            {
                "name": "no_geometry_to_higher_layer_promotion",
                "passed": no_forbidden_promotion(data),
                "actual": data.get("cannot_claim"),
                "expected": "explicit cannot-claim boundary for translation, structure, physical admissibility, function, and global law",
            },
        ]
        result.update(
            {
                "status": "passed" if all(check["passed"] for check in checks) else "failed",
                "completed_at": now_iso(),
                "checks": checks,
                "result": {
                    "scope": "locked_confirmatory_falsification_only",
                    "source": data.get("source", ""),
                    "snapshot_date": data.get("snapshot_date", ""),
                    "target_claim_ids": data.get("target_claim_ids", []),
                    "stronger_statistic": "exact one-sided binomial tests with minimum independent trial counts plus zero-tolerance negative and ablation controls",
                },
            }
        )
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    return emit(result)


if __name__ == "__main__":
    raise SystemExit(main())

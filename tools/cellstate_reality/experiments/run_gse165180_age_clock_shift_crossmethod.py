#!/usr/bin/env python3
"""检验 GSE165180/GSE165179 MPTR Horvath353 跨方法年龄时钟方向。"""

from __future__ import annotations

import csv
import hashlib
import json
import math
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
CELLSTATE_ROOT = REPO_ROOT / "tools" / "cellstate_reality"
DATA_PATH = CELLSTATE_ROOT / "data" / "gse165180_horvath353_crossmethod_inputs.json"
OUT_DIR = CELLSTATE_ROOT / "out"
CERT_PATH = OUT_DIR / "gse165180_age_clock_shift_crossmethod_certificate.json"
SCORES_PATH = OUT_DIR / "gse165180_age_clock_shift_crossmethod_scores.csv"
PAIRS_PATH = OUT_DIR / "gse165180_age_clock_shift_crossmethod_pairs.csv"
EXPERIMENT_ID = "gse165180_age_clock_shift_crossmethod"
CLAIM_ID = "cellstate.age-clock-shift.crossmethod.gse165180"
CONJECTURE_ID = "age-clock-shift.crossmethod.gse165180"
CONTACT_ID = "k-a.gse165180.horvath353"
COVERAGE_TOTAL = 353
COVERAGE_FLOOR = 330
TAU_CPG = 0.93
NULL_TRIALS = 64
MIN_PAIR_COUNT = 3
SIGNIFICANCE_FLOOR = 0.10
ADULT_AGE = 20.0
BLOCKED_PROMOTIONS = [
    "identity",
    "function",
    "safety",
    "rejuvenation",
    "maintenance",
    "immortality",
]


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def load_inputs() -> dict[str, Any]:
    return json.loads(DATA_PATH.read_text(encoding="utf-8"))


def dnam_age(clock_sum: float) -> float:
    if clock_sum < 0.0:
        return (1.0 + ADULT_AGE) * math.exp(clock_sum) - 1.0
    return (1.0 + ADULT_AGE) * clock_sum + ADULT_AGE


def mean(values: list[float]) -> float:
    return sum(values) / float(len(values)) if values else float("nan")


def score_samples(
    payload: dict[str, Any],
    *,
    coefficient_order: dict[str, str] | None = None,
) -> list[dict[str, Any]]:
    intercept = float(payload["intercept"])
    coefficients = {str(marker): float(weight) for marker, weight in payload["clock_coefficients"].items()}
    beta = payload["beta"]
    sample_by_title = {str(sample["title"]): sample for sample in payload["samples"]}
    scores: list[dict[str, Any]] = []
    for title in sorted(sample_by_title):
        linear = intercept
        used = 0
        for marker, weight_marker in coefficient_order.items() if coefficient_order is not None else ((m, m) for m in coefficients):
            marker_values = beta.get(marker)
            if not isinstance(marker_values, dict) or title not in marker_values:
                continue
            linear += coefficients[weight_marker] * float(marker_values[title])
            used += 1
        sample = sample_by_title[title]
        scores.append(
            {
                "title": title,
                "gsm": str(sample.get("gsm") or ""),
                "donor": str(sample.get("donor") or ""),
                "condition": str(sample.get("condition") or ""),
                "day": sample.get("day"),
                "experiment": sample.get("experiment"),
                "donor_age_years": sample.get("donor_age_years"),
                "cell_type_characteristic": str(sample.get("characteristics", {}).get("cell type", "")),
                "length_of_reprogramming_phase_days": str(
                    sample.get("characteristics", {}).get("length of reprogramming phase (days)", "")
                ),
                "clock_cpg_used": used,
                "clock_linear_score": linear,
                "horvath_dnam_age": dnam_age(linear),
            }
        )
    return scores


def pair_shifts(payload: dict[str, Any], scores: list[dict[str, Any]]) -> list[dict[str, Any]]:
    score_by_title = {str(score["title"]): score for score in scores}
    sample_by_title = {str(sample["title"]): sample for sample in payload["samples"]}
    rows: list[dict[str, Any]] = []
    for pair in payload["pairs"]:
        baseline = score_by_title[str(pair["baseline_sample"])]
        treated = score_by_title[str(pair["treated_sample"])]
        baseline_sample = sample_by_title[str(pair["baseline_sample"])]
        treated_sample = sample_by_title[str(pair["treated_sample"])]
        delta = float(treated["horvath_dnam_age"]) - float(baseline["horvath_dnam_age"])
        rows.append(
            {
                "donor": str(pair["donor"]),
                "day": int(pair["day"]),
                "experiment": str(pair["experiment"]),
                "baseline_sample": str(pair["baseline_sample"]),
                "treated_sample": str(pair["treated_sample"]),
                "baseline_gsm": str(baseline["gsm"]),
                "treated_gsm": str(treated["gsm"]),
                "baseline_characteristics": baseline_sample.get("characteristics", {}),
                "treated_characteristics": treated_sample.get("characteristics", {}),
                "baseline_age": float(baseline["horvath_dnam_age"]),
                "treated_age": float(treated["horvath_dnam_age"]),
                "delta_treated_minus_baseline": delta,
            }
        )
    return rows


def permutation_order(markers: list[str], trial: int) -> dict[str, str]:
    permuted = sorted(
        markers,
        key=lambda marker: hashlib.sha256(f"{EXPERIMENT_ID}:null:{trial}:{marker}".encode("utf-8")).hexdigest(),
    )
    return {marker: weight_marker for marker, weight_marker in zip(markers, permuted)}


def deterministic_null(payload: dict[str, Any], observed_mean: float) -> dict[str, Any]:
    coefficients = payload["clock_coefficients"]
    beta = payload["beta"]
    markers = [str(marker) for marker in coefficients if marker in beta]
    null_means: list[float] = []
    for trial in range(NULL_TRIALS):
        scores = score_samples(payload, coefficient_order=permutation_order(markers, trial))
        pairs = pair_shifts(payload, scores)
        null_means.append(mean([float(pair["delta_treated_minus_baseline"]) for pair in pairs]))
    as_or_more_negative = sum(1 for value in null_means if value <= observed_mean)
    return {
        "method": "deterministic hashlib CpG-weight permutation",
        "trials": NULL_TRIALS,
        "as_or_more_negative": as_or_more_negative,
        "empirical_direction_p": (1.0 + as_or_more_negative) / (1.0 + NULL_TRIALS),
        "null_mean_min": min(null_means) if null_means else None,
        "null_mean_max": max(null_means) if null_means else None,
        "null_means": null_means,
    }


def write_csv(path: Path, rows: list[dict[str, Any]], fields: list[str]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow({field: row.get(field, "") for field in fields})


def check(name: str, passed: bool, reason: str, value: Any | None = None) -> dict[str, Any]:
    item: dict[str, Any] = {"name": name, "passed": bool(passed), "reason": reason}
    if value is not None:
        item["value"] = value
    return item


def main() -> int:
    started_at = now_iso()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = load_inputs()
    scores = score_samples(payload)
    pairs = pair_shifts(payload, scores)

    deltas = [float(pair["delta_treated_minus_baseline"]) for pair in pairs]
    covered = int(payload.get("clock_cpg_covered") or 0)
    coverage_ratio = covered / float(COVERAGE_TOTAL)
    mean_delta = mean(deltas)
    negative_count = sum(1 for delta in deltas if delta < 0.0)
    null = deterministic_null(payload, mean_delta)
    empirical_p = float(null["empirical_direction_p"])
    pair_count_ok = len(pairs) >= MIN_PAIR_COUNT
    coverage_ok = covered >= COVERAGE_FLOOR and coverage_ratio >= TAU_CPG
    mean_negative = mean_delta < 0.0
    direction_significant = empirical_p <= SIGNIFICANCE_FLOOR
    support = coverage_ok and pair_count_ok and mean_negative and direction_significant

    checks = [
        check(
            "coverage.floor",
            coverage_ok,
            "Horvath353 coverage must meet the fixed EPIC floor.",
            {"covered": covered, "total": COVERAGE_TOTAL, "ratio": coverage_ratio},
        ),
        check(
            "paired.sample.structure",
            pair_count_ok,
            "Requires at least three same-donor baseline versus MPTR transiently reprogrammed pairs.",
            {
                "n_pairs": len(pairs),
                "pairs": [
                    {
                        "donor": pair["donor"],
                        "baseline_sample": pair["baseline_sample"],
                        "treated_sample": pair["treated_sample"],
                        "baseline_characteristics": pair["baseline_characteristics"],
                        "treated_characteristics": pair["treated_characteristics"],
                    }
                    for pair in pairs
                ],
            },
        ),
        check(
            "mean.delta.negative",
            mean_negative,
            "Mean treated-minus-baseline DNAm age delta must be negative.",
            {"mean_delta_treated_minus_baseline": mean_delta, "negative_pairs": negative_count, "n_pairs": len(pairs)},
        ),
        check(
            "deterministic.null.direction",
            direction_significant,
            "Hash-seeded CpG permutation null must give a small one-sided empirical p for the negative direction.",
            {
                "empirical_direction_p": empirical_p,
                "threshold": SIGNIFICANCE_FLOOR,
                "trials": NULL_TRIALS,
                "as_or_more_negative": null["as_or_more_negative"],
            },
        ),
        check(
            "age-signature.scope-boundary",
            True,
            "The certificate is age_signature-only and does not promote identity, function, safety, rejuvenation, maintenance, or immortality.",
            {"blocked_promotions": BLOCKED_PROMOTIONS},
        ),
        check(
            "cohort.boundary",
            True,
            "GSE165180/GSE165179 MPTR and GSE142439 OSKMLN-mRNA remain separate cohorts supporting a method-independence question without sample merging.",
            {"separate_contacts": [CONTACT_ID, "k-a.gse142439.horvath353"]},
        ),
    ]
    status = "passed" if support else "needs_data"
    verdict = "support_crossmethod_age_clock_shift" if support else "needs_data_crossmethod_direction_not_significant"

    certificate = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "conjecture_id": CONJECTURE_ID,
        "contact_id": CONTACT_ID,
        "layer": "age_signature",
        "status": status,
        "verdict": verdict,
        "support": support,
        "data_path": rel(DATA_PATH),
        "source_urls": payload.get("source_urls", {}),
        "summary": {
            "n_pairs": len(pairs),
            "clock_cpg_covered": covered,
            "clock_cpg_total": COVERAGE_TOTAL,
            "coverage_ratio": coverage_ratio,
            "mean_delta_treated_minus_baseline": mean_delta,
            "negative_delta_pairs": negative_count,
            "empirical_direction_p": empirical_p,
            "null_trials": NULL_TRIALS,
            "status_reason": (
                "mean direction is negative but the deterministic permutation direction check is not small enough"
                if mean_negative and not direction_significant
                else verdict
            ),
        },
        "pairs": pairs,
        "deterministic_null": null,
        "checks": checks,
        "cannot_claim": [
            "This is only an age_signature-layer Horvath353 clock-direction test.",
            "It does not establish IdentityPreservingAgeReset↑, identity preservation, function, safety, rejuvenation, maintenance, or immortality.",
            "MPTR transient-phase samples are not treated as safety-preserving; this certificate does not touch that promotion gate.",
            "GSE165180/GSE165179 and GSE142439 are independent reality contacts and are not merged into one cohort carrier.",
        ],
        "blocked_promotions": [
            {"name": name, "blocked": True, "reason": "No layer-matched contact is supplied by this methylation age-clock test."}
            for name in BLOCKED_PROMOTIONS
        ],
    }
    CERT_PATH.write_text(json.dumps(certificate, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_csv(
        SCORES_PATH,
        scores,
        [
            "title",
            "gsm",
            "donor",
            "condition",
            "day",
            "experiment",
            "donor_age_years",
            "cell_type_characteristic",
            "length_of_reprogramming_phase_days",
            "clock_cpg_used",
            "clock_linear_score",
            "horvath_dnam_age",
        ],
    )
    write_csv(
        PAIRS_PATH,
        pairs,
        [
            "donor",
            "day",
            "experiment",
            "baseline_sample",
            "treated_sample",
            "baseline_gsm",
            "treated_gsm",
            "baseline_age",
            "treated_age",
            "delta_treated_minus_baseline",
        ],
    )

    result = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "contact_id": CONTACT_ID,
        "verdict": verdict,
        "support": support,
        "outputs": {
            "certificate": rel(CERT_PATH),
            "scores": rel(SCORES_PATH),
            "pairs": rel(PAIRS_PATH),
        },
        "summary": certificate["summary"],
        "cannot_claim": certificate["cannot_claim"],
        "blocked_promotions": certificate["blocked_promotions"],
    }
    print(
        json.dumps(
            {
                "experiment_id": EXPERIMENT_ID,
                "claim_id": CLAIM_ID,
                "started_at": started_at,
                "completed_at": now_iso(),
                "status": status,
                "checks": checks,
                "result": result,
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

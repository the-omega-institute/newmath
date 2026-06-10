#!/usr/bin/env python3
"""检验 GSE165180/GSE165179 MPTR Horvath353 全时相剂量-响应。"""

from __future__ import annotations

import csv
import hashlib
import json
import math
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
CELLSTATE_ROOT = REPO_ROOT / "tools" / "cellstate_reality"
DATA_PATH = CELLSTATE_ROOT / "data" / "gse165180_horvath353_timecourse_inputs.json"
OUT_DIR = CELLSTATE_ROOT / "out"
CERT_PATH = OUT_DIR / "gse165180_age_clock_shift_dose_response_certificate.json"
SCORES_PATH = OUT_DIR / "gse165180_age_clock_shift_dose_response_scores.csv"
OBS_PATH = OUT_DIR / "gse165180_age_clock_shift_dose_response_observations.csv"
DONOR_DAY_PATH = OUT_DIR / "gse165180_age_clock_shift_dose_response_donor_day.csv"
EXPERIMENT_ID = "gse165180_age_clock_shift_dose_response"
CLAIM_ID = "cellstate.age-clock-shift.dose-response.gse165180"
CONJECTURE_ID = "age-clock-shift.dose-response.gse165180"
CONTACT_ID = "k-a.gse165180.horvath353"
COVERAGE_TOTAL = 353
COVERAGE_FLOOR = 330
TAU_CPG = 0.93
NULL_TRIALS = 64
SIGNIFICANCE_FLOOR = 0.10
MIN_DONORS_PER_TIMEPOINT = 2
MIN_OBSERVATIONS = 6
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
        items = coefficient_order.items() if coefficient_order is not None else ((marker, marker) for marker in coefficients)
        for marker, weight_marker in items:
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


def pair_observations(payload: dict[str, Any], scores: list[dict[str, Any]]) -> list[dict[str, Any]]:
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
                "phase_length_days": int(pair["phase_length_days"]),
                "experiment": str(pair.get("experiment") or ""),
                "baseline_sample": str(pair["baseline_sample"]),
                "treated_sample": str(pair["treated_sample"]),
                "baseline_gsm": str(baseline["gsm"]),
                "treated_gsm": str(treated["gsm"]),
                "baseline_cell_type": str(baseline_sample.get("characteristics", {}).get("cell type", "")),
                "treated_cell_type": str(treated_sample.get("characteristics", {}).get("cell type", "")),
                "baseline_phase_length_days": str(
                    baseline_sample.get("characteristics", {}).get("length of reprogramming phase (days)", "")
                ),
                "treated_phase_length_days": str(
                    treated_sample.get("characteristics", {}).get("length of reprogramming phase (days)", "")
                ),
                "baseline_age": float(baseline["horvath_dnam_age"]),
                "treated_age": float(treated["horvath_dnam_age"]),
                "delta_treated_minus_baseline": delta,
            }
        )
    return rows


def donor_day_rows(observations: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[tuple[str, int], list[dict[str, Any]]] = defaultdict(list)
    for observation in observations:
        grouped[(str(observation["donor"]), int(observation["day"]))].append(observation)
    rows: list[dict[str, Any]] = []
    for (donor, day), group in sorted(grouped.items(), key=lambda item: (item[0][1], item[0][0])):
        deltas = [float(item["delta_treated_minus_baseline"]) for item in group]
        rows.append(
            {
                "donor": donor,
                "day": day,
                "observation_count": len(group),
                "experiments": ",".join(sorted({str(item["experiment"]) for item in group if item["experiment"]})),
                "mean_delta_treated_minus_baseline": mean(deltas),
                "min_delta_treated_minus_baseline": min(deltas),
                "max_delta_treated_minus_baseline": max(deltas),
            }
        )
    return rows


def per_timepoint(donor_day: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for day in sorted({int(row["day"]) for row in donor_day}):
        day_rows = [row for row in donor_day if int(row["day"]) == day]
        obs_count = sum(int(row["observation_count"]) for row in day_rows)
        deltas = [float(row["mean_delta_treated_minus_baseline"]) for row in day_rows]
        rows.append(
            {
                "day": day,
                "donor_n": len(day_rows),
                "observation_n": obs_count,
                "mean_delta_treated_minus_baseline": mean(deltas),
                "negative_donor_day_count": sum(1 for delta in deltas if delta < 0.0),
            }
        )
    return rows


def ranks(values: list[float]) -> list[float]:
    sorted_indices = sorted(range(len(values)), key=lambda index: values[index])
    result = [0.0 for _ in values]
    index = 0
    while index < len(values):
        end = index
        while end + 1 < len(values) and values[sorted_indices[end + 1]] == values[sorted_indices[index]]:
            end += 1
        rank = (index + end + 2.0) / 2.0
        for fill in range(index, end + 1):
            result[sorted_indices[fill]] = rank
        index = end + 1
    return result


def spearman(xs: list[float], ys: list[float]) -> float | None:
    if len(xs) < 2 or len(xs) != len(ys):
        return None
    x_rank = ranks(xs)
    y_rank = ranks(ys)
    x_mean = mean(x_rank)
    y_mean = mean(y_rank)
    numerator = sum((x - x_mean) * (y - y_mean) for x, y in zip(x_rank, y_rank))
    x_var = sum((x - x_mean) ** 2 for x in x_rank)
    y_var = sum((y - y_mean) ** 2 for y in y_rank)
    if x_var == 0.0 or y_var == 0.0:
        return None
    return numerator / math.sqrt(x_var * y_var)


def dose_response(donor_day: list[dict[str, Any]]) -> dict[str, Any]:
    concordant = 0
    discordant = 0
    ties = 0
    comparisons: list[dict[str, Any]] = []
    for left_index, left in enumerate(donor_day):
        for right in donor_day[left_index + 1 :]:
            left_day = int(left["day"])
            right_day = int(right["day"])
            if left_day == right_day:
                continue
            shorter, longer = (left, right) if left_day < right_day else (right, left)
            shorter_delta = float(shorter["mean_delta_treated_minus_baseline"])
            longer_delta = float(longer["mean_delta_treated_minus_baseline"])
            if longer_delta < shorter_delta:
                concordant += 1
                direction = "deeper_more_negative"
            elif longer_delta > shorter_delta:
                discordant += 1
                direction = "deeper_less_negative"
            else:
                ties += 1
                direction = "tie"
            comparisons.append(
                {
                    "shorter": {"donor": shorter["donor"], "day": int(shorter["day"]), "delta": shorter_delta},
                    "longer": {"donor": longer["donor"], "day": int(longer["day"]), "delta": longer_delta},
                    "direction": direction,
                }
            )
    total = concordant + discordant + ties
    sign_concordance = (concordant + 0.5 * ties) / float(total) if total else None
    rho = spearman(
        [float(row["day"]) for row in donor_day],
        [float(row["mean_delta_treated_minus_baseline"]) for row in donor_day],
    )
    if sign_concordance is None:
        trend_direction = "insufficient"
    elif sign_concordance > 0.5 and (rho is None or rho < 0.0):
        trend_direction = "deeper_more_negative"
    elif sign_concordance < 0.5 and (rho is None or rho > 0.0):
        trend_direction = "reverse_or_mixed"
    else:
        trend_direction = "mixed"
    return {
        "method": "donor-day collapsed pairwise sign-concordance plus Spearman rank correlation",
        "trend_direction": trend_direction,
        "concordant_deeper_more_negative": concordant,
        "discordant_deeper_less_negative": discordant,
        "ties": ties,
        "comparison_count": total,
        "sign_concordance": sign_concordance,
        "spearman_rho_day_vs_delta": rho,
        "comparisons": comparisons,
    }


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
        observations = pair_observations(payload, scores)
        null_means.append(mean([float(item["delta_treated_minus_baseline"]) for item in observations]))
    as_or_more_negative = sum(1 for value in null_means if value <= observed_mean)
    return {
        "method": "deterministic hashlib CpG-weight permutation over all treated observations",
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
    observations = pair_observations(payload, scores)
    donor_day = donor_day_rows(observations)
    timepoints = per_timepoint(donor_day)

    covered = int(payload.get("clock_cpg_covered") or 0)
    coverage_ratio = covered / float(COVERAGE_TOTAL)
    observation_deltas = [float(item["delta_treated_minus_baseline"]) for item in observations]
    donor_day_deltas = [float(item["mean_delta_treated_minus_baseline"]) for item in donor_day]
    pooled_observation_mean = mean(observation_deltas)
    pooled_donor_day_mean = mean(donor_day_deltas)
    donor_count = len({str(item["donor"]) for item in observations})
    null = deterministic_null(payload, pooled_observation_mean)
    empirical_p = float(null["empirical_direction_p"])
    trend = dose_response(donor_day)

    coverage_ok = covered >= COVERAGE_FLOOR and coverage_ratio >= TAU_CPG
    enough_observations = len(observations) >= MIN_OBSERVATIONS and donor_count >= 3
    per_timepoint_n_ok = bool(timepoints) and all(int(row["donor_n"]) >= MIN_DONORS_PER_TIMEPOINT for row in timepoints)
    mean_negative = pooled_observation_mean < 0.0
    direction_significant = empirical_p <= SIGNIFICANCE_FLOOR
    dose_response_ok = trend["trend_direction"] == "deeper_more_negative"
    support = coverage_ok and enough_observations and per_timepoint_n_ok and mean_negative and direction_significant and dose_response_ok
    status = "passed" if support else "needs_data"
    if support:
        verdict = "support_age_clock_shift_dose_response"
    elif not dose_response_ok:
        verdict = "needs_data_dose_response_reverse_or_mixed"
    elif not direction_significant:
        verdict = "needs_data_pooled_direction_not_significant"
    else:
        verdict = "needs_data_timecourse_structure_insufficient"

    checks = [
        check(
            "coverage.floor",
            coverage_ok,
            "Horvath353 coverage must meet the fixed EPIC floor.",
            {"covered": covered, "total": COVERAGE_TOTAL, "ratio": coverage_ratio},
        ),
        check(
            "timecourse.sample.structure",
            enough_observations,
            "Requires same-donor baseline fibroblast versus true transiently reprogrammed fibroblast observations across the time course.",
            {
                "donor_count": donor_count,
                "observation_count": len(observations),
                "treated_days": sorted({int(item["day"]) for item in observations}),
            },
        ),
        check(
            "per-timepoint.donor-count",
            per_timepoint_n_ok,
            "Each reported treated timepoint should have at least two donors before counting as a powered dose-response group.",
            {"minimum": MIN_DONORS_PER_TIMEPOINT, "per_timepoint": timepoints},
        ),
        check(
            "pooled.mean.delta.negative",
            mean_negative,
            "Pooled treated-minus-baseline DNAm age delta across observations must be negative.",
            {
                "pooled_observation_mean_delta": pooled_observation_mean,
                "pooled_donor_day_mean_delta": pooled_donor_day_mean,
                "negative_observations": sum(1 for delta in observation_deltas if delta < 0.0),
                "observation_count": len(observations),
            },
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
            "dose.response.direction",
            dose_response_ok,
            "Longer reprogramming phase should be directionally more negative in donor-day collapsed deltas.",
            trend,
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
            "GSE165180/GSE165179 MPTR and GSE142439 OSKMLN-mRNA remain separate reality contacts and are not sample-merged.",
            {"separate_contacts": [CONTACT_ID, "k-a.gse142439.horvath353"]},
        ),
    ]

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
            "donor_count": donor_count,
            "observation_count": len(observations),
            "donor_day_count": len(donor_day),
            "clock_cpg_covered": covered,
            "clock_cpg_total": COVERAGE_TOTAL,
            "coverage_ratio": coverage_ratio,
            "per_timepoint": timepoints,
            "pooled_observation_mean_delta_treated_minus_baseline": pooled_observation_mean,
            "pooled_donor_day_mean_delta_treated_minus_baseline": pooled_donor_day_mean,
            "empirical_direction_p": empirical_p,
            "null_trials": NULL_TRIALS,
            "dose_response_trend_direction": trend["trend_direction"],
            "status_reason": verdict,
        },
        "observations": observations,
        "donor_day": donor_day,
        "dose_response": trend,
        "deterministic_null": null,
        "checks": checks,
        "cannot_claim": [
            "This is only an age_signature-layer Horvath353 clock-direction and dose-response test.",
            "It does not establish IdentityPreservingAgeReset↑, identity preservation, function, safety, rejuvenation, maintenance, or immortality.",
            "MPTR transient-phase samples are not treated as safety-preserving; this certificate does not touch that promotion gate.",
            "GSE165180/GSE165179 and GSE142439 are independent reality contacts and are not merged into one cohort carrier.",
            "Repeated timepoints from the same donor are reported as correlated observations; per-timepoint donor counts and donor-day collapsed trends are reported separately from pooled observation counts.",
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
        OBS_PATH,
        observations,
        [
            "donor",
            "day",
            "phase_length_days",
            "experiment",
            "baseline_sample",
            "treated_sample",
            "baseline_gsm",
            "treated_gsm",
            "baseline_cell_type",
            "treated_cell_type",
            "baseline_phase_length_days",
            "treated_phase_length_days",
            "baseline_age",
            "treated_age",
            "delta_treated_minus_baseline",
        ],
    )
    write_csv(
        DONOR_DAY_PATH,
        donor_day,
        [
            "donor",
            "day",
            "observation_count",
            "experiments",
            "mean_delta_treated_minus_baseline",
            "min_delta_treated_minus_baseline",
            "max_delta_treated_minus_baseline",
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
            "observations": rel(OBS_PATH),
            "donor_day": rel(DONOR_DAY_PATH),
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

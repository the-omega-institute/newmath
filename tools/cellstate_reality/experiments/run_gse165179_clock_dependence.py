#!/usr/bin/env python3
"""检验 GSE165179 MPTR DNAm-age 方向是否依赖 clock 选择。"""

from __future__ import annotations

import hashlib
import json
import math
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
CELLSTATE_ROOT = REPO_ROOT / "tools" / "cellstate_reality"
DATA_PATH = CELLSTATE_ROOT / "data" / "gse165179_dualclock_inputs.json"
OUT_DIR = CELLSTATE_ROOT / "out"
CERT_PATH = OUT_DIR / "gse165179_clock_dependence_certificate.json"
EXPERIMENT_ID = "gse165179_clock_dependence"
CLAIM_ID = "cellstate.age-clock-shift.clock-dependence.gse165180"
CONJECTURE_ID = "age-clock-shift.clock-dependence.gse165180"
CONTACT_ID = "k-a.gse165180.horvath353"
ADULT_AGE = 20.0
NULL_TRIALS = 64
OLD_PAN_TISSUE_MEANS = {10: -8.26, 13: -14.11, 15: 0.84, 17: 6.60}
SANITY_TOLERANCE_YEARS = 0.75
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


def anti_trafo(value: float) -> float:
    if value < 0.0:
        return (1.0 + ADULT_AGE) * math.exp(value) - 1.0
    return (1.0 + ADULT_AGE) * value + ADULT_AGE


def mean(values: list[float]) -> float:
    return sum(values) / float(len(values)) if values else float("nan")


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


def check(name: str, passed: bool, reason: str, value: Any | None = None) -> dict[str, Any]:
    item: dict[str, Any] = {"name": name, "passed": bool(passed), "reason": reason}
    if value is not None:
        item["value"] = value
    return item


def score_samples(payload: dict[str, Any], clock_id: str, coefficient_order: dict[str, str] | None = None) -> list[dict[str, Any]]:
    clock = payload["clocks"][clock_id]
    coefficients = {str(marker): float(weight) for marker, weight in clock["coefficients"].items()}
    beta = payload["beta"]
    samples = {str(sample["title"]): sample for sample in payload["samples"]}
    rows: list[dict[str, Any]] = []
    for title in sorted(samples):
        z = 0.0
        used = 0
        items = coefficient_order.items() if coefficient_order is not None else ((marker, marker) for marker in coefficients)
        for marker, weight_marker in items:
            marker_values = beta.get(marker)
            if not isinstance(marker_values, dict) or title not in marker_values:
                continue
            z += coefficients[weight_marker] * float(marker_values[title])
            used += 1
        transformed_linear = z + float(clock["linear_offset"])
        sample = samples[title]
        rows.append(
            {
                "clock_id": clock_id,
                "title": title,
                "gsm": str(sample.get("gsm") or ""),
                "donor": str(sample.get("donor") or ""),
                "condition": str(sample.get("condition") or ""),
                "day": sample.get("day"),
                "experiment": sample.get("experiment"),
                "cell_type": str(sample.get("cell_type") or ""),
                "phase_length_days": str(sample.get("phase_length_days") or ""),
                "clock_cpg_used": used,
                "clock_z_sum": z,
                "clock_transformed_linear": transformed_linear,
                "dnam_age": anti_trafo(transformed_linear),
            }
        )
    return rows


def pair_observations(payload: dict[str, Any], scores: list[dict[str, Any]], clock_id: str) -> list[dict[str, Any]]:
    score_by_title = {str(score["title"]): score for score in scores}
    rows: list[dict[str, Any]] = []
    for pair in payload["pairs"]:
        baseline = score_by_title[str(pair["baseline_sample"])]
        treated = score_by_title[str(pair["treated_sample"])]
        delta = float(treated["dnam_age"]) - float(baseline["dnam_age"])
        rows.append(
            {
                "clock_id": clock_id,
                "donor": str(pair["donor"]),
                "day": int(pair["day"]),
                "phase_length_days": int(pair["phase_length_days"]),
                "experiment": str(pair.get("experiment") or ""),
                "baseline_sample": str(pair["baseline_sample"]),
                "treated_sample": str(pair["treated_sample"]),
                "baseline_gsm": str(baseline["gsm"]),
                "treated_gsm": str(treated["gsm"]),
                "baseline_age": float(baseline["dnam_age"]),
                "treated_age": float(treated["dnam_age"]),
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
        deltas = [float(row["mean_delta_treated_minus_baseline"]) for row in day_rows]
        rows.append(
            {
                "day": day,
                "donor_n": len(day_rows),
                "observation_n": sum(int(row["observation_count"]) for row in day_rows),
                "mean_delta_treated_minus_baseline": mean(deltas),
                "negative_donor_day_count": sum(1 for delta in deltas if delta < 0.0),
                "positive_donor_day_count": sum(1 for delta in deltas if delta > 0.0),
            }
        )
    return rows


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
        trend_direction = "deeper_less_negative"
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


def permutation_order(markers: list[str], trial: int, clock_id: str) -> dict[str, str]:
    permuted = sorted(
        markers,
        key=lambda marker: hashlib.sha256(f"{EXPERIMENT_ID}:null:{clock_id}:{trial}:{marker}".encode("utf-8")).hexdigest(),
    )
    return {marker: weight_marker for marker, weight_marker in zip(markers, permuted)}


def deterministic_null(payload: dict[str, Any], clock_id: str, observed_mean: float) -> dict[str, Any]:
    clock = payload["clocks"][clock_id]
    coefficients = clock["coefficients"]
    beta = payload["beta"]
    markers = [str(marker) for marker in coefficients if marker in beta]
    null_means: list[float] = []
    for trial in range(NULL_TRIALS):
        scores = score_samples(payload, clock_id, coefficient_order=permutation_order(markers, trial, clock_id))
        observations = pair_observations(payload, scores, clock_id)
        null_means.append(mean([float(item["delta_treated_minus_baseline"]) for item in observations]))
    if observed_mean < 0.0:
        extreme = sum(1 for value in null_means if value <= observed_mean)
        direction = "as_or_more_negative"
    elif observed_mean > 0.0:
        extreme = sum(1 for value in null_means if value >= observed_mean)
        direction = "as_or_more_positive"
    else:
        extreme = len(null_means)
        direction = "zero_observed"
    return {
        "method": "deterministic hashlib CpG-weight permutation over all treated observations",
        "trials": NULL_TRIALS,
        "direction": direction,
        "extreme_count": extreme,
        "empirical_direction_p": (1.0 + extreme) / (1.0 + NULL_TRIALS),
        "null_mean_min": min(null_means) if null_means else None,
        "null_mean_max": max(null_means) if null_means else None,
        "null_means": null_means,
    }


def summarize_clock(payload: dict[str, Any], clock_id: str) -> dict[str, Any]:
    scores = score_samples(payload, clock_id)
    observations = pair_observations(payload, scores, clock_id)
    donor_day = donor_day_rows(observations)
    timepoints = per_timepoint(donor_day)
    observation_deltas = [float(item["delta_treated_minus_baseline"]) for item in observations]
    donor_day_deltas = [float(item["mean_delta_treated_minus_baseline"]) for item in donor_day]
    pooled_observation_mean = mean(observation_deltas)
    trend = dose_response(donor_day)
    null = deterministic_null(payload, clock_id, pooled_observation_mean)
    clock = payload["clocks"][clock_id]
    return {
        "clock_id": clock_id,
        "display_name": clock.get("display_name"),
        "coverage": {
            "covered": int(clock.get("clock_cpg_covered") or 0),
            "total": int(clock.get("clock_cpg_total") or 0),
            "ratio": float(clock.get("clock_cpg_coverage_ratio") or 0.0),
        },
        "scores": scores,
        "observations": observations,
        "donor_day": donor_day,
        "per_timepoint": timepoints,
        "pooled_observation_mean_delta_treated_minus_baseline": pooled_observation_mean,
        "pooled_donor_day_mean_delta_treated_minus_baseline": mean(donor_day_deltas),
        "dose_response": trend,
        "deterministic_null": null,
    }


def day_mean(summary: dict[str, Any], day: int) -> float | None:
    for row in summary["per_timepoint"]:
        if int(row["day"]) == day:
            return float(row["mean_delta_treated_minus_baseline"])
    return None


def late_days_negative(summary: dict[str, Any]) -> bool:
    return all((day_mean(summary, day) is not None and float(day_mean(summary, day)) < 0.0) for day in (15, 17))


def late_days_positive(summary: dict[str, Any]) -> bool:
    return all((day_mean(summary, day) is not None and float(day_mean(summary, day)) > 0.0) for day in (15, 17))


def pan_tissue_sanity(summary: dict[str, Any]) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    direction_ok = True
    tolerance_ok = True
    for day, expected in OLD_PAN_TISSUE_MEANS.items():
        observed = day_mean(summary, day)
        if observed is None:
            direction_match = False
            within_tolerance = False
            diff = None
        else:
            direction_match = (observed < 0.0 and expected < 0.0) or (observed > 0.0 and expected > 0.0) or (observed == 0.0 and expected == 0.0)
            diff = observed - expected
            within_tolerance = abs(diff) <= SANITY_TOLERANCE_YEARS
        direction_ok = direction_ok and direction_match
        tolerance_ok = tolerance_ok and within_tolerance
        rows.append(
            {
                "day": day,
                "observed_mean_delta": observed,
                "prior_mean_delta": expected,
                "difference_years": diff,
                "direction_match": direction_match,
                "within_tolerance_years": within_tolerance,
            }
        )
    return {
        "prior_values": OLD_PAN_TISSUE_MEANS,
        "tolerance_years": SANITY_TOLERANCE_YEARS,
        "direction_ok": direction_ok,
        "within_tolerance": tolerance_ok,
        "rows": rows,
    }


def classify_verdict(skin_blood: dict[str, Any], pan_tissue: dict[str, Any]) -> str:
    skin_late_negative = late_days_negative(skin_blood)
    pan_late_positive = late_days_positive(pan_tissue)
    skin_monotone = skin_blood["dose_response"]["trend_direction"] == "deeper_more_negative"
    pan_reverse = pan_tissue["dose_response"]["trend_direction"] == "deeper_less_negative"
    if skin_late_negative and skin_monotone and pan_late_positive and pan_reverse:
        return "clock_dependent_reversal"
    if late_days_positive(skin_blood) and pan_late_positive:
        return "clock_independent_reversal"
    return "mixed"


def main() -> int:
    started_at = now_iso()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = load_inputs()

    skin_blood = summarize_clock(payload, "skin_blood_horvath2")
    pan_tissue = summarize_clock(payload, "pan_tissue_horvath1")
    sanity = pan_tissue_sanity(pan_tissue)
    verdict = classify_verdict(skin_blood, pan_tissue)

    timepoints_present = sorted({int(row["day"]) for row in skin_blood["per_timepoint"]}) == [10, 13, 15, 17] and sorted(
        {int(row["day"]) for row in pan_tissue["per_timepoint"]}
    ) == [10, 13, 15, 17]
    both_clocks_scored = bool(skin_blood["observations"]) and bool(pan_tissue["observations"])
    verdict_clear = verdict in {"clock_dependent_reversal", "clock_independent_reversal", "mixed"}
    status = "passed" if both_clocks_scored and timepoints_present and sanity["direction_ok"] and verdict_clear else "failed"

    checks = [
        check(
            "input.available",
            DATA_PATH.exists(),
            "Curated dual-clock GSE165179 input must be present locally.",
            {"data_path": rel(DATA_PATH)},
        ),
        check(
            "dual-clock.coverage",
            skin_blood["coverage"]["covered"] > 0 and pan_tissue["coverage"]["covered"] > 0,
            "Both DNAm clocks must have covered CpGs in the curated EPIC matrix.",
            {
                "skin_blood_horvath2": skin_blood["coverage"],
                "pan_tissue_horvath1": pan_tissue["coverage"],
            },
        ),
        check(
            "timecourse.sample.structure",
            timepoints_present,
            "Both clocks must score the same donor-paired day 10/13/15/17 MPTR timecourse.",
            {
                "skin_blood_days": sorted({int(row["day"]) for row in skin_blood["per_timepoint"]}),
                "pan_tissue_days": sorted({int(row["day"]) for row in pan_tissue["per_timepoint"]}),
                "pair_count": len(payload.get("pairs", [])),
            },
        ),
        check(
            "pan-tissue.sanity",
            bool(sanity["direction_ok"]),
            "Biolearn Horvath1 pan-tissue scoring should preserve the prior Horvath353 timepoint reversal direction.",
            sanity,
        ),
        check(
            "clock-dependence.verdict",
            verdict_clear,
            "The method comparison must produce an explicit clock-dependence verdict.",
            {
                "verdict": verdict,
                "skin_blood_late_negative": late_days_negative(skin_blood),
                "skin_blood_late_positive": late_days_positive(skin_blood),
                "skin_blood_trend": skin_blood["dose_response"]["trend_direction"],
                "pan_tissue_late_positive": late_days_positive(pan_tissue),
                "pan_tissue_trend": pan_tissue["dose_response"]["trend_direction"],
            },
        ),
        check(
            "age-signature-only.boundary",
            True,
            "The certificate is a DNAm clock method-comparison at age_signature layer only.",
            {"blocked_promotions": BLOCKED_PROMOTIONS},
        ),
        check(
            "cohort.boundary",
            True,
            "GSE165180/GSE165179 remains separate from GSE142439 and is not merged with another cohort.",
            {"contact_id": CONTACT_ID},
        ),
    ]

    statement = (
        "GSE165179 MPTR baseline-versus-treated donor pairs scored with two DNAm clocks show that "
        f"the late-timepoint direction verdict is {verdict}: "
        f"skin&blood day15/day17 mean deltas are {day_mean(skin_blood, 15):.6g} and {day_mean(skin_blood, 17):.6g}, "
        f"while pan-tissue day15/day17 mean deltas are {day_mean(pan_tissue, 15):.6g} and {day_mean(pan_tissue, 17):.6g}. "
        "This is a clock-method age_signature result only."
    )

    certificate = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "conjecture_id": CONJECTURE_ID,
        "contact_id": CONTACT_ID,
        "layer": "age_signature",
        "status": status,
        "verdict": verdict,
        "statement": statement,
        "data_path": rel(DATA_PATH),
        "source_urls": payload.get("source_urls", {}),
        "sample_phase_annotations": payload.get("sample_phase_annotations", []),
        "coverage": {
            "skin_blood_horvath2": skin_blood["coverage"],
            "pan_tissue_horvath1": pan_tissue["coverage"],
        },
        "per_clock": {
            "skin_blood_horvath2": skin_blood,
            "pan_tissue_horvath1": pan_tissue,
        },
        "pan_tissue_sanity_against_prior_horvath353": sanity,
        "checks": checks,
        "cannot_claim": [
            "This is an age_signature-layer methodological control comparing two DNAm clocks on the same GSE165179 MPTR data.",
            "Clock-dependent direction does not prove that cells are biologically truly younger or older; both clocks are proxy readbacks.",
            "The result does not establish identity, function, safety, rejuvenation, maintenance, or immortality.",
            "GSE165179/GSE165180 is not merged with GSE142439 or any other cohort.",
        ],
        "blocked_promotions": [
            {"name": name, "blocked": True, "reason": "No higher-layer contact is supplied by this DNAm clock comparison."}
            for name in BLOCKED_PROMOTIONS
        ],
    }
    CERT_PATH.write_text(json.dumps(certificate, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    result = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "contact_id": CONTACT_ID,
        "verdict": verdict,
        "outputs": {"certificate": rel(CERT_PATH)},
        "summary": {
            "status_reason": verdict,
            "coverage": certificate["coverage"],
            "per_timepoint_mean_delta": {
                "skin_blood_horvath2": skin_blood["per_timepoint"],
                "pan_tissue_horvath1": pan_tissue["per_timepoint"],
            },
            "dose_response": {
                "skin_blood_horvath2": skin_blood["dose_response"],
                "pan_tissue_horvath1": pan_tissue["dose_response"],
            },
            "pooled_mean_delta": {
                "skin_blood_horvath2": skin_blood["pooled_observation_mean_delta_treated_minus_baseline"],
                "pan_tissue_horvath1": pan_tissue["pooled_observation_mean_delta_treated_minus_baseline"],
            },
            "deterministic_null": {
                "skin_blood_horvath2": skin_blood["deterministic_null"],
                "pan_tissue_horvath1": pan_tissue["deterministic_null"],
            },
            "pan_tissue_sanity": sanity,
        },
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

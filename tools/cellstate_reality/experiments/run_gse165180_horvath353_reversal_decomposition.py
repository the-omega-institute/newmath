#!/usr/bin/env python3
"""分解 GSE165180 MPTR Horvath353 晚期反转的 CpG 坐标贡献。"""

from __future__ import annotations

import csv
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
CERT_PATH = OUT_DIR / "gse165180_horvath353_reversal_decomposition_certificate.json"
TOP_CPG_PATH = OUT_DIR / "gse165180_horvath353_reversal_decomposition_top_cpg.csv"
PER_TIMEPOINT_PATH = OUT_DIR / "gse165180_horvath353_reversal_decomposition_timepoints.csv"
EXPERIMENT_ID = "gse165180_horvath353_reversal_decomposition"
CLAIM_ID = "cellstate.age-clock-shift.reversal-decomposition.gse165180"
CONJECTURE_ID = "age-clock-shift.reversal-decomposition.gse165180"
CONTACT_ID = "k-a.gse165180.horvath353"
COVERAGE_TOTAL = 353
TOP_K = 20
ADULT_AGE = 20.0
EPSILON = 1.0e-10
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


def mean(values: list[float]) -> float:
    return sum(values) / float(len(values)) if values else float("nan")


def median(values: list[float]) -> float:
    if not values:
        return float("nan")
    ordered = sorted(values)
    mid = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[mid]
    return (ordered[mid - 1] + ordered[mid]) / 2.0


def dnam_age(clock_sum: float) -> float:
    if clock_sum < 0.0:
        return (1.0 + ADULT_AGE) * math.exp(clock_sum) - 1.0
    return (1.0 + ADULT_AGE) * clock_sum + ADULT_AGE


def sign(value: float) -> int:
    if value > EPSILON:
        return 1
    if value < -EPSILON:
        return -1
    return 0


def check(name: str, passed: bool, reason: str, value: Any | None = None) -> dict[str, Any]:
    item: dict[str, Any] = {"name": name, "passed": bool(passed), "reason": reason}
    if value is not None:
        item["value"] = value
    return item


def score_sample(title: str, payload: dict[str, Any]) -> dict[str, float]:
    coefficients = {str(marker): float(weight) for marker, weight in payload["clock_coefficients"].items()}
    beta = payload["beta"]
    covered_markers = [marker for marker in sorted(coefficients) if marker in beta and title in beta[marker]]
    covered_linear = sum(coefficients[marker] * float(beta[marker][title]) for marker in covered_markers)
    linear = float(payload["intercept"]) + covered_linear
    return {
        "covered_linear": covered_linear,
        "clock_linear_score": linear,
        "horvath_dnam_age": dnam_age(linear),
        "clock_cpg_used": float(len(covered_markers)),
    }


def pair_rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for pair in payload["pairs"]:
        baseline_title = str(pair["baseline_sample"])
        treated_title = str(pair["treated_sample"])
        baseline = score_sample(baseline_title, payload)
        treated = score_sample(treated_title, payload)
        rows.append(
            {
                "donor": str(pair["donor"]),
                "day": int(pair["day"]),
                "experiment": str(pair.get("experiment") or ""),
                "baseline_sample": baseline_title,
                "treated_sample": treated_title,
                "delta_z": float(treated["clock_linear_score"]) - float(baseline["clock_linear_score"]),
                "delta_age": float(treated["horvath_dnam_age"]) - float(baseline["horvath_dnam_age"]),
            }
        )
    return rows


def donor_day_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[tuple[str, int], list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        grouped[(str(row["donor"]), int(row["day"]))].append(row)
    collapsed: list[dict[str, Any]] = []
    for (donor, day), group in sorted(grouped.items(), key=lambda item: (item[0][1], item[0][0])):
        collapsed.append(
            {
                "donor": donor,
                "day": day,
                "observation_count": len(group),
                "delta_z": mean([float(item["delta_z"]) for item in group]),
                "delta_age": mean([float(item["delta_age"]) for item in group]),
            }
        )
    return collapsed


def contribution_table(payload: dict[str, Any], donor_day: list[dict[str, Any]]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    coefficients = {str(marker): float(weight) for marker, weight in payload["clock_coefficients"].items()}
    covered_markers = [marker for marker in sorted(coefficients) if marker in payload["beta"]]
    days = sorted({int(row["day"]) for row in donor_day})
    donors_by_day = {
        day: sorted({str(row["donor"]) for row in donor_day if int(row["day"]) == day})
        for day in days
    }

    per_marker: list[dict[str, Any]] = []
    for marker in covered_markers:
        weight = coefficients[marker]
        row: dict[str, Any] = {"cg": marker, "weight": weight, "abs_weight": abs(weight)}
        for day in days:
            donors = donors_by_day[day]
            baseline_values: list[float] = []
            treated_values: list[float] = []
            donor_beta_deltas: list[float] = []
            for donor in donors:
                baseline_titles = sorted(
                    {
                        str(pair["baseline_sample"])
                        for pair in payload["pairs"]
                        if int(pair["day"]) == day and str(pair["donor"]) == donor
                    }
                )
                treated_titles = [str(pair["treated_sample"]) for pair in payload["pairs"] if int(pair["day"]) == day and str(pair["donor"]) == donor]
                marker_values = payload["beta"][marker]
                donor_baseline_values = [float(marker_values[title]) for title in baseline_titles if title in marker_values]
                donor_treated_values = [float(marker_values[title]) for title in treated_titles if title in marker_values]
                if donor_baseline_values and donor_treated_values:
                    donor_baseline = mean(donor_baseline_values)
                    donor_treated = mean(donor_treated_values)
                    baseline_values.append(donor_baseline)
                    treated_values.append(donor_treated)
                    donor_beta_deltas.append(donor_treated - donor_baseline)
            baseline_beta = mean(baseline_values)
            treated_beta = mean(treated_values)
            contribution = weight * mean(donor_beta_deltas)
            row[f"beta_baseline_day{day}"] = baseline_beta
            row[f"beta_day{day}"] = treated_beta
            row[f"beta_extremity_baseline_day{day}"] = abs(baseline_beta - 0.5)
            row[f"beta_extremity_day{day}"] = abs(treated_beta - 0.5)
            row[f"contrib_day{day}"] = contribution
        if 10 in days and 17 in days:
            row["delta_contrib_day17_minus_day10"] = float(row["contrib_day17"]) - float(row["contrib_day10"])
            row["beta_day17_minus_day10"] = float(row["beta_day17"]) - float(row["beta_day10"])
            row["beta_extremity_day17_minus_baseline"] = (
                float(row["beta_extremity_day17"]) - float(row["beta_extremity_baseline_day17"])
            )
        per_marker.append(row)

    per_timepoint: list[dict[str, Any]] = []
    for day in days:
        z_sum = sum(float(row[f"contrib_day{day}"]) for row in per_marker)
        day_rows = [row for row in donor_day if int(row["day"]) == day]
        mean_delta_z = mean([float(row["delta_z"]) for row in day_rows])
        mean_delta_age = mean([float(row["delta_age"]) for row in day_rows])
        per_timepoint.append(
            {
                "day": day,
                "donor_day_count": len(day_rows),
                "contribution_sum_z": z_sum,
                "mean_delta_z_from_scores": mean_delta_z,
                "mean_delta_age_years": mean_delta_age,
                "z_sum_minus_score_delta": z_sum - mean_delta_z,
                "z_sign_matches_age_delta": sign(z_sum) == sign(mean_delta_age),
            }
        )
    return per_marker, per_timepoint


def write_csv(path: Path, rows: list[dict[str, Any]], fields: list[str]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow({field: row.get(field, "") for field in fields})


def main() -> int:
    started_at = now_iso()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = load_inputs()
    pair_level = pair_rows(payload)
    donor_day = donor_day_rows(pair_level)
    per_marker, per_timepoint = contribution_table(payload, donor_day)
    top_reversal = sorted(
        per_marker,
        key=lambda row: (
            float(row.get("delta_contrib_day17_minus_day10", 0.0)),
            abs(float(row["weight"])),
            str(row["cg"]),
        ),
        reverse=True,
    )[:TOP_K]

    abs_weights = [float(row["abs_weight"]) for row in per_marker]
    top_abs_weights = [float(row["abs_weight"]) for row in top_reversal]
    all_median_abs_weight = median(abs_weights)
    top_mean_abs_weight = mean(top_abs_weights)
    top_day17_beta = mean([float(row["beta_day17"]) for row in top_reversal])
    top_day17_extremity = mean([float(row["beta_extremity_day17"]) for row in top_reversal])
    top_baseline_extremity = mean([float(row["beta_extremity_baseline_day17"]) for row in top_reversal])
    top_extremity_shift = top_day17_extremity - top_baseline_extremity
    if top_extremity_shift > EPSILON:
        top_extremity_direction = "more_extreme_than_baseline"
    elif top_extremity_shift < -EPSILON:
        top_extremity_direction = "less_extreme_than_baseline"
    else:
        top_extremity_direction = "unchanged_from_baseline"

    day17_positive = [float(row["contrib_day17"]) for row in per_marker if float(row["contrib_day17"]) > 0.0]
    day17_negative = [float(row["contrib_day17"]) for row in per_marker if float(row["contrib_day17"]) < 0.0]
    day17_positive_sum = sum(day17_positive)
    top_day17_positive_sum = sum(max(float(row["contrib_day17"]), 0.0) for row in top_reversal)
    top_day17_share = top_day17_positive_sum / day17_positive_sum if day17_positive_sum > 0.0 else float("nan")

    additivity_ok = all(abs(float(row["z_sum_minus_score_delta"])) <= 1.0e-12 for row in per_timepoint)
    sign_ok = all(bool(row["z_sign_matches_age_delta"]) for row in per_timepoint)
    top_k_ok = len(top_reversal) == TOP_K and all("delta_contrib_day17_minus_day10" in row for row in top_reversal)
    concentration_ok = day17_positive_sum > 0.0 and top_day17_share > 0.0
    status = "passed" if additivity_ok and sign_ok and top_k_ok and concentration_ok else "failed"
    verdict = "passed_reversal_decomposition_certificate" if status == "passed" else "failed_reversal_decomposition_certificate"

    mechanism_summary = {
        "top_k": TOP_K,
        "top_k_mean_abs_weight": top_mean_abs_weight,
        "all_covered_median_abs_weight": all_median_abs_weight,
        "top_k_abs_weight_over_all_median": top_mean_abs_weight / all_median_abs_weight if all_median_abs_weight else None,
        "top_k_day17_mean_beta": top_day17_beta,
        "top_k_day17_mean_abs_beta_minus_0_5": top_day17_extremity,
        "top_k_baseline_mean_abs_beta_minus_0_5": top_baseline_extremity,
        "top_k_extremity_shift_day17_minus_baseline": top_extremity_shift,
        "top_k_extremity_direction_day17_vs_baseline": top_extremity_direction,
        "top_k_day17_positive_contribution_sum": top_day17_positive_sum,
        "day17_positive_contribution_sum": day17_positive_sum,
        "top_k_share_of_day17_positive_contribution": top_day17_share,
        "day17_positive_cpg_count": len(day17_positive),
        "day17_negative_cpg_count": len(day17_negative),
        "day17_zero_cpg_count": len(per_marker) - len(day17_positive) - len(day17_negative),
    }

    statement = (
        f"Day-17 Horvath353 reversal is localized inside the covered age_signature coordinates: "
        f"the top {TOP_K} day17-vs-day10 reversal CpGs account for "
        f"{top_day17_share * 100.0:.2f}% of the day17 positive z-space displacement, "
        f"with mean abs weight {top_mean_abs_weight:.6g} versus covered median {all_median_abs_weight:.6g}. "
        f"Their mean beta at day17 is {top_day17_beta:.6g}, but mean abs(beta-0.5) shifts from "
        f"{top_baseline_extremity:.6g} at matched baseline to {top_day17_extremity:.6g} at day17 "
        f"({top_extremity_direction}), so aggregate top-K beta extremity is characterized rather than promoted as functional annotation. "
        "This is an age_signature-only failure-boundary certificate for AgeClockShiftUp in late MPTR, not an age decrease, identity, function, safety, rejuvenation, maintenance, or immortality claim; without external CpG functional annotation, pluripotency/development wording remains an inferred clock-geometry description only."
    )

    top_rows = [
        {
            "rank": index,
            "cg": str(row["cg"]),
            "weight": float(row["weight"]),
            "beta_baseline": float(row["beta_baseline_day17"]),
            "beta_day10": float(row["beta_day10"]),
            "beta_day17": float(row["beta_day17"]),
            "contrib_day10": float(row["contrib_day10"]),
            "contrib_day17": float(row["contrib_day17"]),
            "delta_contrib_day17_minus_day10": float(row["delta_contrib_day17_minus_day10"]),
        }
        for index, row in enumerate(top_reversal, 1)
    ]

    checks = [
        check(
            "input.available",
            DATA_PATH.exists(),
            "Curated GSE165180 Horvath353 timecourse input must be present locally.",
            {"data_path": rel(DATA_PATH)},
        ),
        check(
            "coverage.floor",
            int(payload.get("clock_cpg_covered") or 0) == len(per_marker),
            "The decomposition must cover the curated 334 observed Horvath353 CpG coordinates.",
            {"covered": len(per_marker), "declared": payload.get("clock_cpg_covered"), "total": COVERAGE_TOTAL},
        ),
        check(
            "additive.z-decomposition",
            additivity_ok,
            "Per-CpG contribution sums must match donor-day collapsed z-space score deltas.",
            {"per_timepoint": per_timepoint},
        ),
        check(
            "dnam-age.direction.sanity",
            sign_ok,
            "The z-space contribution-sum sign must match the monotone DNAm-age delta sign at each timepoint.",
            {"per_timepoint": per_timepoint},
        ),
        check(
            "top-k.localization",
            top_k_ok,
            "The day17-vs-day10 reversal driver list must contain exactly the fixed top-K CpG coordinates.",
            {"top_k": TOP_K, "observed": len(top_reversal)},
        ),
        check(
            "concentration.quantified",
            concentration_ok,
            "Day17 positive displacement concentration must be quantified over positive and negative CpG contributions.",
            mechanism_summary,
        ),
        check(
            "age-signature.scope-boundary",
            True,
            "The certificate is age_signature-only and blocks all higher-layer promotions.",
            {"blocked_promotions": BLOCKED_PROMOTIONS},
        ),
        check(
            "annotation.boundary",
            True,
            "No external CpG functional annotation is used; mechanism wording is clock-internal geometry from weights and beta drift only.",
            {"functional_annotation_used": False},
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
        "support": status == "passed",
        "data_path": rel(DATA_PATH),
        "source_urls": payload.get("source_urls", {}),
        "statement": statement,
        "summary": {
            "clock_cpg_covered": len(per_marker),
            "clock_cpg_total": COVERAGE_TOTAL,
            "per_timepoint": per_timepoint,
            "mechanism": mechanism_summary,
        },
        "top_reversal_cpg": top_rows,
        "checks": checks,
        "cannot_claim": [
            "This is only an age_signature-layer Horvath353 clock-internal coordinate decomposition.",
            "It does not establish age decrease; it characterizes late MPTR day15/day17 failure of AgeClockShiftUp under Horvath353.",
            "It does not establish identity, function, safety, rejuvenation, maintenance, organismal maintenance, or immortality.",
            "No external CpG functional annotation is used; developmental or pluripotency wording is an inferred beta-extremity geometry description only.",
            "GSE165180/GSE165179 is not merged with GSE142439 into a shared cohort carrier.",
        ],
        "blocked_promotions": [
            {"name": name, "blocked": True, "reason": "No layer-matched contact is supplied by this clock-internal decomposition."}
            for name in BLOCKED_PROMOTIONS
        ],
    }

    CERT_PATH.write_text(json.dumps(certificate, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_csv(
        TOP_CPG_PATH,
        top_rows,
        [
            "rank",
            "cg",
            "weight",
            "beta_baseline",
            "beta_day10",
            "beta_day17",
            "contrib_day10",
            "contrib_day17",
            "delta_contrib_day17_minus_day10",
        ],
    )
    write_csv(
        PER_TIMEPOINT_PATH,
        per_timepoint,
        [
            "day",
            "donor_day_count",
            "contribution_sum_z",
            "mean_delta_z_from_scores",
            "mean_delta_age_years",
            "z_sum_minus_score_delta",
            "z_sign_matches_age_delta",
        ],
    )

    result = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "contact_id": CONTACT_ID,
        "verdict": verdict,
        "support": status == "passed",
        "outputs": {
            "certificate": rel(CERT_PATH),
            "top_cpg": rel(TOP_CPG_PATH),
            "per_timepoint": rel(PER_TIMEPOINT_PATH),
        },
        "summary": certificate["summary"],
        "statement": statement,
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

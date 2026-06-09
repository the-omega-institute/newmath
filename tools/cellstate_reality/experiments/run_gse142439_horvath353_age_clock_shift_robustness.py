#!/usr/bin/env python3
"""Check GSE142439 Horvath353 age-clock shift robustness within frozen inputs."""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
CELLSTATE_ROOT = REPO_ROOT / "tools" / "cellstate_reality"
DATA_PATH = CELLSTATE_ROOT / "data" / "gse142439_horvath353_clock_inputs.json"
OUT_DIR = CELLSTATE_ROOT / "out"
OUT_PATH = OUT_DIR / "age_clock_shift_robustness.json"
EXPERIMENT_ID = "gse142439_horvath353_age_clock_shift_robustness"
CLAIM_ID = "cellstate.age-clock-shift.robustness.gse142439"
CONTACT_ID = "k-a.gse142439.horvath353"
CONJECTURE_ID = "age-clock-shift.gse142439.cross-cell-type-robustness"
EXPECTED_STRATA = ("SkinFibroblasts", "VeinEndothelialCells")
BLOCKED_PROMOTIONS = [
    "IdentityPreservingAgeReset↑",
    "Rejuvenation↑",
    "PartialReprogramming↑",
    "RenewableMaintenance↑",
    "ImmortalityPotential↑",
]
BLOCKED_NULL = [
    "This robustness check remains an age_signature-layer result.",
    "It does not establish cell_identity preservation.",
    "It does not establish function_realization.",
    "It does not establish safety_boundary.",
    "It does not establish rejuvenation, renewable maintenance, organismal maintenance, or immortality potential.",
]


def load_inputs() -> dict[str, Any]:
    return json.loads(DATA_PATH.read_text(encoding="utf-8"))


def dnam_age(clock_sum: float) -> float:
    adult_age = 20.0
    if clock_sum < 0.0:
        return (1.0 + adult_age) * math.exp(clock_sum) - 1.0
    return (1.0 + adult_age) * clock_sum + adult_age


def score_samples(payload: dict[str, Any]) -> dict[str, dict[str, Any]]:
    intercept = float(payload["intercept"])
    coefficients = {str(marker): float(weight) for marker, weight in payload["clock_coefficients"].items()}
    beta = payload["beta"]
    sample_by_gsm = {str(sample["gsm"]): sample for sample in payload["samples"]}
    scores: dict[str, dict[str, Any]] = {}
    for gsm in sorted(sample_by_gsm):
        linear = intercept
        used = 0
        for marker, weight in coefficients.items():
            marker_values = beta.get(marker)
            if not isinstance(marker_values, dict) or gsm not in marker_values:
                continue
            linear += weight * float(marker_values[gsm])
            used += 1
        sample = sample_by_gsm[gsm]
        scores[gsm] = {
            "gsm": gsm,
            "person": int(sample["person"]),
            "cell_type": str(sample["cell_type"]),
            "treatment": str(sample["treatment"]),
            "clock_cpg_used": used,
            "clock_linear_score": linear,
            "horvath_dnam_age": dnam_age(linear),
        }
    return scores


def pair_shifts(payload: dict[str, Any], scores: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    pairs: list[dict[str, Any]] = []
    for pair in payload["pairs"]:
        normal = scores[str(pair["normal_gsm"])]
        treated = scores[str(pair["treated_gsm"])]
        delta = float(treated["horvath_dnam_age"]) - float(normal["horvath_dnam_age"])
        pairs.append(
            {
                "person": int(pair["person"]),
                "cell_type": str(pair["cell_type"]),
                "normal_gsm": str(pair["normal_gsm"]),
                "treated_gsm": str(pair["treated_gsm"]),
                "normal_age": float(normal["horvath_dnam_age"]),
                "treated_age": float(treated["horvath_dnam_age"]),
                "delta_treated_minus_normal": delta,
                "direction": "negative" if delta < 0.0 else "nonnegative",
            }
        )
    return pairs


def mean(values: list[float]) -> float:
    return sum(values) / float(len(values)) if values else float("nan")


def sample_sd(values: list[float]) -> float | None:
    if len(values) < 2:
        return None
    center = mean(values)
    return math.sqrt(sum((value - center) ** 2 for value in values) / float(len(values) - 1))


def describe(values: list[float]) -> dict[str, Any]:
    ordered = sorted(values)
    return {
        "n": len(values),
        "mean_delta_treated_minus_normal": mean(values),
        "min_delta": ordered[0] if ordered else None,
        "max_delta": ordered[-1] if ordered else None,
        "sample_sd": sample_sd(values),
        "negative_count": sum(1 for value in values if value < 0.0),
        "nonnegative_count": sum(1 for value in values if value >= 0.0),
    }


def per_stratum(pairs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for cell_type in EXPECTED_STRATA:
        stratum_pairs = [pair for pair in pairs if pair["cell_type"] == cell_type]
        deltas = [float(pair["delta_treated_minus_normal"]) for pair in stratum_pairs]
        summary = describe(deltas)
        rows.append(
            {
                "cell_type": cell_type,
                **summary,
                "direction": "negative" if summary["mean_delta_treated_minus_normal"] < 0.0 else "nonnegative",
                "interpretation_boundary": "n=4 stratum: descriptive direction only; no per-stratum significance claim.",
            }
        )
    return rows


def leave_one_donor_out(pairs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for donor in sorted(int(pair["person"]) for pair in pairs):
        kept = [pair for pair in pairs if int(pair["person"]) != donor]
        deltas = [float(pair["delta_treated_minus_normal"]) for pair in kept]
        mean_delta = mean(deltas)
        rows.append(
            {
                "excluded_person": donor,
                "n_pairs_kept": len(kept),
                "mean_delta_treated_minus_normal": mean_delta,
                "direction": "negative" if mean_delta < 0.0 else "nonnegative",
            }
        )
    return rows


def check(name: str, passed: bool, reason: str, value: Any | None = None) -> dict[str, Any]:
    item: dict[str, Any] = {"name": name, "passed": bool(passed), "reason": reason}
    if value is not None:
        item["value"] = value
    return item


def main() -> int:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = load_inputs()
    scores = score_samples(payload)
    pairs = pair_shifts(payload, scores)
    strata = per_stratum(pairs)
    loo = leave_one_donor_out(pairs)

    overall_deltas = [float(pair["delta_treated_minus_normal"]) for pair in pairs]
    overall = describe(overall_deltas)
    strata_counts_ok = all(row["n"] == 4 for row in strata)
    strata_negative = all(row["mean_delta_treated_minus_normal"] < 0.0 for row in strata)
    loo_negative = all(row["mean_delta_treated_minus_normal"] < 0.0 for row in loo)
    loo_means = [float(row["mean_delta_treated_minus_normal"]) for row in loo]
    support = strata_negative and loo_negative
    verdict = "directionally_robust" if support else "partially_robust"
    status = "passed" if support else "needs_data"

    checks = [
        check(
            "paired.sample.structure",
            len(pairs) == 8 and strata_counts_ok,
            "Expected frozen structure: 8 donors, with 4 SkinFibroblasts and 4 VeinEndothelialCells pairs.",
            {"n_pairs": len(pairs), "per_stratum": {row["cell_type"]: row["n"] for row in strata}},
        ),
        check(
            "per_cell_type.direction_consistency",
            strata_negative,
            "Both cell-type strata must have negative mean treated-minus-normal DNAm age delta; n=4 per stratum is descriptive only.",
            {
                row["cell_type"]: {
                    "n": row["n"],
                    "mean_delta_treated_minus_normal": row["mean_delta_treated_minus_normal"],
                    "direction": row["direction"],
                }
                for row in strata
            },
        ),
        check(
            "leave_one_donor_out.all_negative",
            loo_negative,
            "Every leave-one-donor-out recomputation of the overall mean delta must remain negative.",
            {
                "n_recomputations": len(loo),
                "min_mean_delta": min(loo_means) if loo_means else None,
                "max_mean_delta": max(loo_means) if loo_means else None,
                "all_negative": loo_negative,
            },
        ),
        check(
            "age_signature.scope_boundary",
            True,
            "Robustness is scoped to Horvath353 age_signature and cannot promote identity, function, safety, rejuvenation, maintenance, or immortality claims.",
            {"cannot_claim": BLOCKED_PROMOTIONS},
        ),
    ]

    robustness = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "conjecture_id": CONJECTURE_ID,
        "contact_id": CONTACT_ID,
        "data_path": str(DATA_PATH.relative_to(REPO_ROOT)),
        "layer": "age_signature",
        "support": support,
        "verdict": verdict,
        "status": status,
        "summary": {
            "overall": overall,
            "per_cell_type_direction_consistency": strata_negative,
            "leave_one_donor_out_all_negative": loo_negative,
            "leave_one_donor_out_min_mean_delta": min(loo_means) if loo_means else None,
            "leave_one_donor_out_max_mean_delta": max(loo_means) if loo_means else None,
            "honest_gate": "two negative strata and eight negative leave-one-donor-out means",
        },
        "per_cell_type": strata,
        "leave_one_donor_out": loo,
        "paired_deltas": pairs,
        "checks": checks,
        "cannot_claim": BLOCKED_NULL,
        "blocked_promotions": [
            {"name": name, "blocked": True, "reason": "No layer-matched reality contact in this experiment."}
            for name in BLOCKED_PROMOTIONS
        ],
    }
    OUT_PATH.write_text(json.dumps(robustness, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    result = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "contact_id": CONTACT_ID,
        "verdict": verdict,
        "support": support,
        "outputs": {"robustness": str(OUT_PATH.relative_to(REPO_ROOT))},
        "summary": robustness["summary"],
        "cannot_claim": BLOCKED_NULL,
        "blocked_promotions": robustness["blocked_promotions"],
    }
    print(
        json.dumps(
            {
                "experiment_id": EXPERIMENT_ID,
                "claim_id": CLAIM_ID,
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

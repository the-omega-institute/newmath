#!/usr/bin/env python3
"""Evaluate the GSE142439 paired Horvath353 age-clock shift certificate."""

from __future__ import annotations

import csv
import json
import math
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
CELLSTATE_ROOT = REPO_ROOT / "tools" / "cellstate_reality"
DATA_PATH = CELLSTATE_ROOT / "data" / "gse142439_horvath353_clock_inputs.json"
OUT_DIR = CELLSTATE_ROOT / "out"
EXPERIMENT_ID = "gse142439_horvath353_age_clock_shift"
CLAIM_ID = "cellstate.age-clock-shift.gse142439"
CONTACT_ID = "k-a.gse142439.horvath353"
CONJECTURE_ID = "age-clock-shift.gse142439.horvath353"
ALPHA = 0.05
COVERAGE_TOTAL = 353
COVERAGE_FLOOR = 330
TAU_CPG = 0.93
T_CRITICAL_DF7_ONE_SIDED_ALPHA_005 = 1.894578605
BLOCKED_PROMOTIONS = [
    "IdentityPreservingAgeReset↑",
    "Rejuvenation↑",
    "PartialReprogramming↑",
    "RenewableMaintenance↑",
    "ImmortalityPotential↑",
]


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def load_inputs() -> dict[str, Any]:
    return json.loads(DATA_PATH.read_text(encoding="utf-8"))


def dnam_age(clock_sum: float) -> float:
    adult_age = 20.0
    if clock_sum < 0.0:
        return (1.0 + adult_age) * math.exp(clock_sum) - 1.0
    return (1.0 + adult_age) * clock_sum + adult_age


def score_samples(payload: dict[str, Any]) -> list[dict[str, Any]]:
    intercept = float(payload["intercept"])
    coefficients = {str(marker): float(weight) for marker, weight in payload["clock_coefficients"].items()}
    beta = payload["beta"]
    sample_by_gsm = {str(sample["gsm"]): sample for sample in payload["samples"]}
    scores: list[dict[str, Any]] = []
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
        scores.append(
            {
                "gsm": gsm,
                "person": int(sample["person"]),
                "cell_type": str(sample["cell_type"]),
                "treatment": str(sample["treatment"]),
                "clock_cpg_used": used,
                "clock_linear_score": linear,
                "horvath_dnam_age": dnam_age(linear),
            }
        )
    return scores


def pair_shifts(payload: dict[str, Any], scores: list[dict[str, Any]]) -> list[dict[str, Any]]:
    score_by_gsm = {str(score["gsm"]): score for score in scores}
    pairs: list[dict[str, Any]] = []
    for pair in payload["pairs"]:
        normal = score_by_gsm[str(pair["normal_gsm"])]
        treated = score_by_gsm[str(pair["treated_gsm"])]
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
            }
        )
    return pairs


def mean(values: list[float]) -> float:
    return sum(values) / float(len(values)) if values else float("nan")


def sample_sd(values: list[float]) -> float:
    if len(values) < 2:
        return float("nan")
    center = mean(values)
    return math.sqrt(sum((value - center) ** 2 for value in values) / float(len(values) - 1))


def sign_test_one_sided_p(negative_count: int, total: int) -> float:
    if total < 0 or negative_count < 0 or negative_count > total:
        return float("nan")
    return sum(math.comb(total, k) for k in range(negative_count, total + 1)) / (2.0 ** total)


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

    deltas = [float(pair["delta_treated_minus_normal"]) for pair in pairs]
    n_pairs = len(pairs)
    fibroblast_count = sum(1 for pair in pairs if pair["cell_type"] == "SkinFibroblasts")
    endothelial_count = sum(1 for pair in pairs if pair["cell_type"] == "VeinEndothelialCells")
    covered = int(payload["clock_cpg_covered"])
    coverage_ratio = covered / float(COVERAGE_TOTAL)
    mean_delta = mean(deltas)
    negative_count = sum(1 for delta in deltas if delta < 0.0)
    zero_count = sum(1 for delta in deltas if delta == 0.0)
    sd_delta = sample_sd(deltas)
    t_statistic = abs(mean_delta) / (sd_delta / math.sqrt(n_pairs)) if n_pairs > 1 and sd_delta > 0.0 else 0.0
    sign_p = sign_test_one_sided_p(negative_count, n_pairs)
    sign_pass = zero_count == 0 and sign_p <= ALPHA
    t_pass = mean_delta < 0.0 and t_statistic >= T_CRITICAL_DF7_ONE_SIDED_ALPHA_005
    paired_stat_pass = mean_delta < 0.0 and (sign_pass or t_pass)

    checks = [
        check(
            "coverage.floor",
            covered >= COVERAGE_FLOOR and coverage_ratio >= TAU_CPG,
            f"Horvath CpG coverage {covered}/{COVERAGE_TOTAL}; required at least {COVERAGE_FLOOR}/{COVERAGE_TOTAL} and ratio >= {TAU_CPG}",
            {"covered": covered, "total": COVERAGE_TOTAL, "ratio": coverage_ratio},
        ),
        check(
            "paired.sample.structure",
            n_pairs == 8 and fibroblast_count == 4 and endothelial_count == 4,
            "Expected 8 paired samples: 4 SkinFibroblasts and 4 VeinEndothelialCells.",
            {"n_pairs": n_pairs, "fibroblast": fibroblast_count, "endothelial": endothelial_count},
        ),
        check(
            "mean.delta.negative",
            mean_delta < 0.0,
            "Mean paired delta is treated minus normal and must be negative.",
            {"mean_delta": mean_delta},
        ),
        check(
            "paired.direction.statistic",
            paired_stat_pass,
            "One-sided paired direction check requires mean(delta)<0 and sign-test or paired t threshold support.",
            {
                "negative_count": negative_count,
                "zero_count": zero_count,
                "sign_test_one_sided_p": sign_p,
                "paired_t_abs": t_statistic,
                "paired_t_critical_df7_alpha_0_05": T_CRITICAL_DF7_ONE_SIDED_ALPHA_005,
                "sign_pass": sign_pass,
                "t_pass": t_pass,
            },
        ),
    ]
    support = all(item["passed"] for item in checks)
    status = "passed" if support else "needs_data"
    verdict = "Support_A" if support else "Break_A"

    manifest = {
        "contact_id": CONTACT_ID,
        "experiment_id": EXPERIMENT_ID,
        "data_path": str(DATA_PATH.relative_to(REPO_ROOT)),
        "geo_accession": payload.get("geo_accession"),
        "platform": payload.get("platform"),
        "clock_cpg_total": COVERAGE_TOTAL,
        "clock_cpg_covered": covered,
        "coverage_ratio": coverage_ratio,
        "samples": payload.get("samples", []),
        "pairs": payload.get("pairs", []),
        "source_urls": payload.get("source_urls", {}),
    }
    certificate = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "conjecture_id": CONJECTURE_ID,
        "contact_id": CONTACT_ID,
        "local_name": "AgeClockShiftUp",
        "theorem_name": "Thm3 clock-only no-promotion",
        "layer": "age_signature",
        "support": support,
        "verdict": verdict,
        "summary": {
            "n_pairs": n_pairs,
            "fibroblast_pairs": fibroblast_count,
            "endothelial_pairs": endothelial_count,
            "clock_cpg_covered": covered,
            "clock_cpg_total": COVERAGE_TOTAL,
            "coverage_ratio": coverage_ratio,
            "mean_delta_treated_minus_normal": mean_delta,
            "negative_delta_pairs": negative_count,
            "sign_test_one_sided_p": sign_p,
            "paired_t_abs": t_statistic,
            "alpha": ALPHA,
        },
        "checks": checks,
        "blocked_promotions": [
            {
                "name": name,
                "blocked": True,
                "reason": "该层无对应 reality contact",
            }
            for name in BLOCKED_PROMOTIONS
        ],
        "cannot_claim": [
            "Horvath353 age_signature 下降不推出 cell identity 保持。",
            "Horvath353 age_signature 下降不推出 function_realization。",
            "Horvath353 age_signature 下降不推出 safety_boundary。",
            "Horvath353 age_signature 下降不推出 renewable 或 organismal maintenance。",
            "Horvath353 age_signature 下降不推出 rejuvenation、partial reprogramming 或 immortality potential。",
        ],
    }

    (OUT_DIR / "k_a_fetch_manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (OUT_DIR / "thm3_no_promotion_certificate.json").write_text(
        json.dumps(certificate, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    write_csv(
        OUT_DIR / "age_clock_scores.csv",
        scores,
        ["gsm", "person", "cell_type", "treatment", "clock_cpg_used", "clock_linear_score", "horvath_dnam_age"],
    )
    write_csv(
        OUT_DIR / "age_clock_shift_pairs.csv",
        pairs,
        ["person", "cell_type", "normal_gsm", "treated_gsm", "normal_age", "treated_age", "delta_treated_minus_normal"],
    )

    result = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "contact_id": CONTACT_ID,
        "verdict": verdict,
        "support": support,
        "outputs": {
            "manifest": str((OUT_DIR / "k_a_fetch_manifest.json").relative_to(REPO_ROOT)),
            "scores": str((OUT_DIR / "age_clock_scores.csv").relative_to(REPO_ROOT)),
            "pairs": str((OUT_DIR / "age_clock_shift_pairs.csv").relative_to(REPO_ROOT)),
            "certificate": str((OUT_DIR / "thm3_no_promotion_certificate.json").relative_to(REPO_ROOT)),
        },
        "cannot_claim": certificate["cannot_claim"],
        "blocked_promotions": certificate["blocked_promotions"],
        "summary": certificate["summary"],
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

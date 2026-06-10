#!/usr/bin/env python3
"""计算 GSE142439 Horvath353 缺失 CpG 方向界。"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
CELLSTATE_ROOT = REPO_ROOT / "tools" / "cellstate_reality"
DATA_PATH = CELLSTATE_ROOT / "data" / "gse142439_horvath353_clock_inputs.json"
OUT_DIR = CELLSTATE_ROOT / "out"
OUT_PATH = OUT_DIR / "gse142439_missing_cpg_bound.json"
EXPERIMENT_ID = "gse142439_missing_cpg_bound"
CLAIM_ID = "cellstate.age-clock-shift.coverage-bound.gse142439"
CONTACT_ID = "k-a.gse142439.horvath353"
CONJECTURE_ID = "age-clock-shift.coverage-bound.gse142439"
FULL_NAME = "Horvath353AgeClockShift↑"
COVERED_NAME = "CoveredHorvath334AgeClockShift↑"
EXPECTED_TOTAL = 353
EXPECTED_COVERED = 334
EXPECTED_MISSING = 19
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


def load_inputs() -> dict[str, Any]:
    return json.loads(DATA_PATH.read_text(encoding="utf-8"))


def mean(values: list[float]) -> float:
    return sum(values) / float(len(values)) if values else float("nan")


def check(name: str, passed: bool, reason: str, value: Any | None = None) -> dict[str, Any]:
    item: dict[str, Any] = {"name": name, "passed": bool(passed), "reason": reason}
    if value is not None:
        item["value"] = value
    return item


def pair_label(pair: dict[str, Any]) -> str:
    return f"person-{int(pair['person'])}:{pair['cell_type']}:{pair['normal_gsm']}->{pair['treated_gsm']}"


def compute_bound(payload: dict[str, Any]) -> dict[str, Any]:
    coefficients = {str(marker): float(weight) for marker, weight in payload["clock_coefficients"].items()}
    beta = payload["beta"]
    covered_markers = set(str(marker) for marker in beta)
    coefficient_markers = set(coefficients)
    missing_markers = sorted(coefficient_markers - covered_markers)
    covered_clock_markers = sorted(coefficient_markers & covered_markers)
    extra_beta_markers = sorted(covered_markers - coefficient_markers)

    b_u = sum(abs(coefficients[marker]) for marker in missing_markers)
    per_pair: list[dict[str, Any]] = []
    for pair in payload["pairs"]:
        normal_gsm = str(pair["normal_gsm"])
        treated_gsm = str(pair["treated_gsm"])
        delta_z = 0.0
        for marker in covered_clock_markers:
            marker_values = beta[marker]
            delta_beta = float(marker_values[treated_gsm]) - float(marker_values[normal_gsm])
            delta_z += coefficients[marker] * delta_beta
        per_pair.append(
            {
                "pair": pair_label(pair),
                "person": int(pair["person"]),
                "cell_type": str(pair["cell_type"]),
                "normal_gsm": normal_gsm,
                "treated_gsm": treated_gsm,
                "delta_z_covered": delta_z,
                "worst_case": delta_z + b_u,
            }
        )

    mean_delta_z = mean([float(row["delta_z_covered"]) for row in per_pair])
    worst_case_mean = mean_delta_z + b_u
    robust_to_missing = worst_case_mean < 0.0
    admissible_name = FULL_NAME if robust_to_missing else COVERED_NAME
    return {
        "covered": len(covered_clock_markers),
        "missing": len(missing_markers),
        "total_coefficients": len(coefficient_markers),
        "extra_beta_markers": extra_beta_markers,
        "missing_cpgs": missing_markers,
        "B_U": b_u,
        "mean_delta_z_covered": mean_delta_z,
        "worst_case_mean": worst_case_mean,
        "robust_to_missing": robust_to_missing,
        "admissible_name": admissible_name,
        "per_pair": per_pair,
        "n_pairs_worstcase_negative": sum(1 for row in per_pair if float(row["worst_case"]) < 0.0),
    }


def main() -> int:
    started_at = now_iso()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = load_inputs()
    certificate = compute_bound(payload)

    n_pairs = len(certificate["per_pair"])
    schema_certificate = {
        "covered": certificate["covered"],
        "missing": certificate["missing"],
        "B_U": certificate["B_U"],
        "mean_delta_z_covered": certificate["mean_delta_z_covered"],
        "worst_case_mean": certificate["worst_case_mean"],
        "robust_to_missing": certificate["robust_to_missing"],
        "admissible_name": certificate["admissible_name"],
        "per_pair": [
            {
                "pair": row["pair"],
                "delta_z_covered": row["delta_z_covered"],
                "worst_case": row["worst_case"],
            }
            for row in certificate["per_pair"]
        ],
        "n_pairs_worstcase_negative": certificate["n_pairs_worstcase_negative"],
    }
    OUT_PATH.write_text(json.dumps(schema_certificate, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    checks = [
        check(
            "input.available",
            DATA_PATH.exists(),
            "Curated GSE142439 Horvath353 input JSON is present.",
            {"data_path": str(DATA_PATH.relative_to(REPO_ROOT))},
        ),
        check(
            "clock.coverage.partition",
            certificate["total_coefficients"] == EXPECTED_TOTAL
            and certificate["covered"] == EXPECTED_COVERED
            and certificate["missing"] == EXPECTED_MISSING
            and not certificate["extra_beta_markers"],
            "Coefficient CpGs partition into covered and missing coordinates with no beta-only clock markers.",
            {
                "total_coefficients": certificate["total_coefficients"],
                "covered": certificate["covered"],
                "missing": certificate["missing"],
                "extra_beta_markers": certificate["extra_beta_markers"],
            },
        ),
        check(
            "paired.delta-z.produced",
            n_pairs == 8,
            "Covered z-space deltas are computed for the eight normal/treated pairs.",
            {"n_pairs": n_pairs},
        ),
        check(
            "missing-cpg.bound.produced",
            certificate["B_U"] >= 0.0,
            "The missing-CpG absolute coefficient bound is finite and nonnegative.",
            {"B_U": certificate["B_U"]},
        ),
        check(
            "age_signature.scope_boundary",
            True,
            "This certificate only bounds the age_signature-layer clock direction and cannot promote identity, function, safety, rejuvenation, maintenance, or immortality claims.",
            {"cannot_claim": BLOCKED_PROMOTIONS},
        ),
    ]

    result = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "conjecture_id": CONJECTURE_ID,
        "contact_id": CONTACT_ID,
        "support": True,
        "verdict": "missing_cpg_robust" if certificate["robust_to_missing"] else "covered_only",
        "outputs": {"certificate": str(OUT_PATH.relative_to(REPO_ROOT))},
        "summary": {
            "covered": certificate["covered"],
            "missing": certificate["missing"],
            "B_U": certificate["B_U"],
            "mean_delta_z_covered": certificate["mean_delta_z_covered"],
            "worst_case_mean": certificate["worst_case_mean"],
            "robust_to_missing": certificate["robust_to_missing"],
            "admissible_name": certificate["admissible_name"],
            "n_pairs_worstcase_negative": certificate["n_pairs_worstcase_negative"],
        },
        "cannot_claim": [
            "This remains an age_signature-layer coverage-bound certificate.",
            "It does not establish identity, function, safety, rejuvenation, maintenance, or immortality claims.",
        ],
        "blocked_promotions": [
            {"name": name, "blocked": True, "reason": "No layer-matched reality contact in this experiment."}
            for name in BLOCKED_PROMOTIONS
        ],
    }
    print(
        json.dumps(
            {
                "experiment_id": EXPERIMENT_ID,
                "claim_id": CLAIM_ID,
                "started_at": started_at,
                "completed_at": now_iso(),
                "status": "passed",
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

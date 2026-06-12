#!/usr/bin/env python3
"""同 donor/scope 联合检验 MPTR 年龄下降与身份保持条件。"""

from __future__ import annotations

import json
import math
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
CELLSTATE_ROOT = REPO_ROOT / "tools" / "cellstate_reality"
AGE_DATA_PATH = CELLSTATE_ROOT / "data" / "gse165179_transient_clock_inputs.json"
IDENTITY_DATA_PATH = CELLSTATE_ROOT / "data" / "k_i_gse165177_mptr_identity_inputs.json"
OUT_DIR = CELLSTATE_ROOT / "out"
OUT_PATH = OUT_DIR / "samescope_identity_age_reset.json"
EXPERIMENT_ID = "gse165180_samescope_identity_age_reset"
CLAIM_ID = "cellstate.identity-preserving-age-reset.samescope.gse165180"
CONJECTURE_ID = "identity-preserving-age-reset.gse165180-samescope"
AGE_CONTACT_ID = "k-a.gse165179-transient"
IDENTITY_CONTACT_ID = "k-i.gse165177-mptr"
COVERAGE_TOTAL = 353
TAU_CPG = 0.93
IDENTITY_RMS_THRESHOLD = 1.5
PLURIPOTENCY_MAX_DELTA = 1.0
STRICT_PLURIPOTENCY_MAX_DELTA = 0.0
REQUIRED_PLURIPOTENCY = ["POU5F1", "NANOG", "LIN28A", "LIN28B", "SOX2"]
REQUIRED_DONORS = ["O1", "O2", "O3"]
BLOCKED_PROMOTIONS = [
    "Rejuvenation↑",
    "RenewableMaintenance↑",
    "organismal maintenance",
    "immortality",
    "safety K_S",
]


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def mean(values: list[float]) -> float:
    return sum(values) / float(len(values)) if values else float("nan")


def rms(values: list[float]) -> float:
    return math.sqrt(mean([value * value for value in values])) if values else float("nan")


def check(name: str, passed: bool, reason: str, value: Any | None = None) -> dict[str, Any]:
    item: dict[str, Any] = {"name": name, "passed": bool(passed), "reason": reason}
    if value is not None:
        item["value"] = value
    return item


def sample_index(payload: dict[str, Any]) -> dict[tuple[str, str, int | None, str | None], dict[str, Any]]:
    indexed: dict[tuple[str, str, int | None, str | None], dict[str, Any]] = {}
    for sample in payload.get("samples", []):
        if not isinstance(sample, dict):
            continue
        donor = sample.get("donor")
        condition = sample.get("condition")
        day = sample.get("day")
        experiment = sample.get("experiment")
        if isinstance(donor, str) and isinstance(condition, str):
            indexed[(donor, condition, day if isinstance(day, int) else None, experiment if isinstance(experiment, str) else None)] = sample
    return indexed


def age_pairs(age_payload: dict[str, Any]) -> list[dict[str, Any]]:
    indexed = sample_index(age_payload)
    rows: list[dict[str, Any]] = []
    for donor in REQUIRED_DONORS:
        baseline = indexed.get((donor, "baseline", 0, None))
        treated = indexed.get((donor, "transiently_reprogrammed", 10, "exp2"))
        negative = indexed.get((donor, "negative_control", 10, "exp2"))
        if baseline is None or treated is None:
            continue
        baseline_age = float(baseline["dnam_age"])
        treated_age = float(treated["dnam_age"])
        row = {
            "donor": donor,
            "scope_key": {
                "donor": donor,
                "baseline_condition": "baseline",
                "treated_condition": "transiently_reprogrammed",
                "day": 10,
                "experiment": "exp2",
            },
            "baseline_sample": baseline["title"],
            "treated_sample": treated["title"],
            "negative_control_sample": negative.get("title") if isinstance(negative, dict) else None,
            "baseline_age": baseline_age,
            "treated_age": treated_age,
            "delta_treated_minus_baseline": treated_age - baseline_age,
        }
        if isinstance(negative, dict):
            negative_age = float(negative["dnam_age"])
            row["negative_control_age"] = negative_age
            row["delta_treated_minus_negative_control"] = treated_age - negative_age
        rows.append(row)
    return rows


def marker_value(payload: dict[str, Any], marker: str, sample: str) -> float | None:
    gene = payload.get("genes", {}).get(marker)
    if not isinstance(gene, dict):
        return None
    values = gene.get("log2_rpm")
    if not isinstance(values, dict) or sample not in values:
        return None
    return float(values[sample])


def identity_pairs(identity_payload: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    identity_markers = [str(marker) for marker in identity_payload.get("identity_markers", [])]
    pluripotency_markers = [str(marker) for marker in identity_payload.get("pluripotency_markers", [])]
    for pair in identity_payload.get("paired_tests", []):
        if not isinstance(pair, dict):
            continue
        donor = str(pair.get("donor") or "")
        control = str(pair.get("control_sample") or "")
        treated = str(pair.get("treated_sample") or "")
        identity_deltas: dict[str, float] = {}
        pluripotency_deltas: dict[str, float] = {}
        for marker in identity_markers:
            control_value = marker_value(identity_payload, marker, control)
            treated_value = marker_value(identity_payload, marker, treated)
            if control_value is not None and treated_value is not None:
                identity_deltas[marker] = treated_value - control_value
        for marker in pluripotency_markers:
            control_value = marker_value(identity_payload, marker, control)
            treated_value = marker_value(identity_payload, marker, treated)
            if control_value is not None and treated_value is not None:
                pluripotency_deltas[marker] = treated_value - control_value
        identity_values = list(identity_deltas.values())
        pluripotency_values = list(pluripotency_deltas.values())
        rows.append(
            {
                "donor": donor,
                "scope_key": {
                    "donor": donor,
                    "control_condition": "negative_control",
                    "treated_condition": "transiently_reprogrammed",
                    "day": int(pair.get("day") or 0),
                    "experiment": str(pair.get("experiment") or ""),
                },
                "control_sample": control,
                "treated_sample": treated,
                "identity_marker_deltas": identity_deltas,
                "pluripotency_marker_deltas": pluripotency_deltas,
                "identity_rms_delta": rms(identity_values),
                "identity_mean_abs_delta": mean([abs(value) for value in identity_values]),
                "identity_max_abs_delta": max([abs(value) for value in identity_values]) if identity_values else None,
                "pluripotency_max_delta": max(pluripotency_values) if pluripotency_values else None,
                "pluripotency_mean_delta": mean(pluripotency_values),
            }
        )
    return rows


def joined_rows(age_rows: list[dict[str, Any]], identity_rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    identity_by_donor = {row["donor"]: row for row in identity_rows}
    rows: list[dict[str, Any]] = []
    for age_row in age_rows:
        donor = str(age_row["donor"])
        identity_row = identity_by_donor.get(donor)
        if identity_row is None:
            continue
        age_scope = age_row["scope_key"]
        identity_scope = identity_row["scope_key"]
        if (
            age_scope.get("treated_condition") != identity_scope.get("treated_condition")
            or age_scope.get("day") != identity_scope.get("day")
            or age_scope.get("experiment") != identity_scope.get("experiment")
        ):
            continue
        rows.append(
            {
                "donor": donor,
                "age": age_row,
                "identity": identity_row,
                "age_shift": float(age_row["delta_treated_minus_baseline"]) < 0.0,
                "identity_distance_ok": float(identity_row["identity_rms_delta"]) <= IDENTITY_RMS_THRESHOLD,
                "pluripotency_exclusion_ok": (
                    identity_row.get("pluripotency_max_delta") is not None
                    and float(identity_row["pluripotency_max_delta"]) <= PLURIPOTENCY_MAX_DELTA
                ),
                "strict_pluripotency_no_positive_ok": all(
                    float(delta) <= STRICT_PLURIPOTENCY_MAX_DELTA
                    for delta in identity_row["pluripotency_marker_deltas"].values()
                ),
            }
        )
    return rows


def main() -> int:
    started_at = now_iso()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    age_payload = load_json(AGE_DATA_PATH)
    identity_payload = load_json(IDENTITY_DATA_PATH)

    age_rows = age_pairs(age_payload)
    identity_rows = identity_pairs(identity_payload)
    joined = joined_rows(age_rows, identity_rows)
    covered = int(age_payload.get("clock_cpg_covered") or 0)
    coverage_ratio = covered / float(COVERAGE_TOTAL)
    age_deltas = [float(row["delta_treated_minus_baseline"]) for row in age_rows]
    joined_age_deltas = [float(row["age"]["delta_treated_minus_baseline"]) for row in joined]
    positive_pluripotency_deltas = [
        {"donor": row["donor"], "marker": marker, "delta": delta}
        for row in identity_rows
        for marker, delta in row["pluripotency_marker_deltas"].items()
        if float(delta) > STRICT_PLURIPOTENCY_MAX_DELTA
    ]

    age_coverage_ok = covered >= math.ceil(COVERAGE_TOTAL * TAU_CPG) and coverage_ratio >= TAU_CPG
    age_pairing_ok = len(age_rows) == len(REQUIRED_DONORS)
    age_shift_ok = age_pairing_ok and bool(age_deltas) and all(delta < 0.0 for delta in age_deltas)
    identity_join_ok = len(joined) == len(REQUIRED_DONORS)
    identity_marker_coverage_ok = all(row["identity_marker_deltas"] for row in identity_rows)
    pluri_coverage_ok = all(
        marker in identity_payload.get("genes", {}) for marker in REQUIRED_PLURIPOTENCY
    )
    identity_distance_ok = identity_join_ok and all(row["identity_distance_ok"] for row in joined)
    pluripotency_exclusion_ok = identity_join_ok and all(row["pluripotency_exclusion_ok"] for row in joined)
    strict_pluripotency_no_positive_ok = identity_join_ok and all(
        row["strict_pluripotency_no_positive_ok"] for row in joined
    )
    same_sig_i = (
        identity_join_ok
        and identity_marker_coverage_ok
        and pluri_coverage_ok
        and identity_distance_ok
        and pluripotency_exclusion_ok
        and strict_pluripotency_no_positive_ok
    )
    joint_support = age_shift_ok and same_sig_i
    data_ready = age_coverage_ok and age_pairing_ok and identity_join_ok and identity_marker_coverage_ok and pluri_coverage_ok

    checks = [
        check(
            "age.coverage.floor",
            age_coverage_ok,
            "Horvath CpG coverage must meet the fixed EPIC floor.",
            {"covered": covered, "total": COVERAGE_TOTAL, "ratio": coverage_ratio, "threshold": TAU_CPG},
        ),
        check(
            "age.same-donor.baseline-treated-pairs",
            age_pairing_ok,
            "Age side requires O1/O2/O3 baseline and day-10 exp2 transiently reprogrammed methylation samples.",
            {"n_pairs": len(age_rows), "donors": [row["donor"] for row in age_rows]},
        ),
        check(
            "age.clock.shift",
            age_shift_ok,
            "AgeClockShift↑ requires every donor treated-minus-baseline DNAm age delta to be negative.",
            {
                "mean_delta_treated_minus_baseline": mean(age_deltas),
                "per_donor": [
                    {
                        "donor": row["donor"],
                        "delta_treated_minus_baseline": row["delta_treated_minus_baseline"],
                        "baseline_age": row["baseline_age"],
                        "treated_age": row["treated_age"],
                    }
                    for row in age_rows
                ],
            },
        ),
        check(
            "same-scope.join",
            identity_join_ok,
            "Join requires exact donor plus day-10 exp2 transiently reprogrammed condition alignment between methylation and RNA contacts.",
            {
                "joined_donors": [row["donor"] for row in joined],
                "age_donors": [row["donor"] for row in age_rows],
                "identity_donors": [row["donor"] for row in identity_rows],
            },
        ),
        check(
            "identity.marker.coverage",
            identity_marker_coverage_ok,
            "The RNA identity contact must expose marker deltas for every joined donor pair.",
            {"n_identity_pairs": len(identity_rows)},
        ),
        check(
            "pluripotency.marker.coverage",
            pluri_coverage_ok,
            "The RNA identity contact must include the fixed pluripotency exclusion panel.",
            {"required": REQUIRED_PLURIPOTENCY},
        ),
        check(
            "identity.distance.threshold",
            identity_distance_ok,
            "sameSig_I requires each joined donor identity RMS delta to remain within the fixed threshold.",
            {
                "threshold": IDENTITY_RMS_THRESHOLD,
                "per_donor": [
                    {"donor": row["donor"], "identity_rms_delta": row["identity"]["identity_rms_delta"]}
                    for row in joined
                ],
            },
        ),
        check(
            "pluripotency.exclusion",
            pluripotency_exclusion_ok,
            "sameSig_I requires no joined donor pluripotency marker increase above the fixed threshold.",
            {
                "threshold": PLURIPOTENCY_MAX_DELTA,
                "per_donor": [
                    {
                        "donor": row["donor"],
                        "pluripotency_max_delta": row["identity"]["pluripotency_max_delta"],
                    }
                    for row in joined
                ],
            },
        ),
        check(
            "pluripotency.strict.no_positive_donor-marker",
            strict_pluripotency_no_positive_ok,
            "The stricter identity-preservation boundary requires every joined donor-marker pluripotency delta to be non-positive.",
            {
                "positive_delta_count": len(positive_pluripotency_deltas),
                "positive_deltas": positive_pluripotency_deltas,
            },
        ),
        check(
            "promotion.boundary",
            True,
            "The joint carrier does not claim Rejuvenation↑, RenewableMaintenance↑, organismal maintenance, immortality, or safety K_S.",
            {"blocked_promotions": BLOCKED_PROMOTIONS},
        ),
    ]

    if not data_ready:
        status = "needs_data"
        verdict = "needs_data"
    elif joint_support:
        status = "passed"
        verdict = "support_identity_preserving_age_reset"
    else:
        status = "failed"
        verdict = "blocked_identity_preserving_age_reset"

    certificate = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "conjecture_id": CONJECTURE_ID,
        "contact_ids": [AGE_CONTACT_ID, IDENTITY_CONTACT_ID],
        "data_paths": [str(AGE_DATA_PATH.relative_to(REPO_ROOT)), str(IDENTITY_DATA_PATH.relative_to(REPO_ROOT))],
        "layer": "cross_layer_relation",
        "status": status,
        "verdict": verdict,
        "support": joint_support,
        "same_scope_join": identity_join_ok,
        "age_clock_shift": age_shift_ok,
        "sameSig_I": same_sig_i,
        "summary": {
            "joined_donors": [row["donor"] for row in joined],
            "age_mean_delta_treated_minus_baseline": mean(joined_age_deltas),
            "age_all_deltas_negative": age_shift_ok,
            "identity_distance_ok": identity_distance_ok,
            "pluripotency_exclusion_ok": pluripotency_exclusion_ok,
            "strict_pluripotency_no_positive_ok": strict_pluripotency_no_positive_ok,
            "pluripotency_positive_delta_count": len(positive_pluripotency_deltas),
        },
        "joined_rows": joined,
        "checks": checks,
        "cannot_claim": [
            "This same-scope joint carrier does not establish Rejuvenation↑.",
            "This same-scope joint carrier does not establish RenewableMaintenance↑.",
            "This same-scope joint carrier does not establish organismal maintenance or immortality.",
            "This same-scope joint carrier does not supply a safety K_S contact, functional assay, repeated-cycle assay, or organismal endpoint.",
            "When the identity side breaks through pluripotency-marker increase, IdentityPreservingAgeReset↑ is blocked even if DNAm age decreases.",
        ],
        "blocked_promotions": [
            {"name": name, "blocked": True, "reason": "No matching safety, function, repeated-cycle, or organismal contact is supplied."}
            for name in BLOCKED_PROMOTIONS
        ],
    }
    OUT_PATH.write_text(json.dumps(certificate, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    result = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "contact_ids": [AGE_CONTACT_ID, IDENTITY_CONTACT_ID],
        "verdict": verdict,
        "support": joint_support,
        "outputs": {"certificate": str(OUT_PATH.relative_to(REPO_ROOT))},
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

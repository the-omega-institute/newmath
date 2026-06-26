#!/usr/bin/env python3
"""评估 GSE165177 MPTR sameSig_I 身份 marker contact。"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
CELLSTATE_ROOT = REPO_ROOT / "tools" / "cellstate_reality"
DATA_PATH = CELLSTATE_ROOT / "data" / "k_i_gse165177_mptr_identity_inputs.json"
OUT_DIR = CELLSTATE_ROOT / "out"
OUT_PATH = OUT_DIR / "k_i_identity_samesig.json"
EXPERIMENT_ID = "gse165177_mptr_identity_samesig"
CLAIM_ID = "cellstate.identity-samesig.gse165177-mptr"
CONTACT_ID = "k-i.gse165177-mptr"
CONJECTURE_ID = "identity-preserving-age-reset.gse165177-mptr"
IDENTITY_RMS_THRESHOLD = 1.5
PLURIPOTENCY_MAX_DELTA = 1.0
STRICT_PLURIPOTENCY_MAX_DELTA = 0.0
MIN_DONOR_PAIRS = 3
REQUIRED_PLURIPOTENCY = ["POU5F1", "NANOG", "LIN28A", "LIN28B", "SOX2"]
BLOCKED_PROMOTIONS = [
    "IdentityPreservingAgeResetUp",
    "RejuvenationUp",
    "PartialReprogrammingUp",
    "RenewableMaintenanceUp",
    "ImmortalityPotentialUp",
]


def load_inputs() -> dict[str, Any]:
    return json.loads(DATA_PATH.read_text(encoding="utf-8"))


def mean(values: list[float]) -> float:
    return sum(values) / float(len(values)) if values else float("nan")


def rms(values: list[float]) -> float:
    return math.sqrt(mean([value * value for value in values])) if values else float("nan")


def check(name: str, passed: bool, reason: str, value: Any | None = None) -> dict[str, Any]:
    item: dict[str, Any] = {"name": name, "passed": bool(passed), "reason": reason}
    if value is not None:
        item["value"] = value
    return item


def marker_value(payload: dict[str, Any], marker: str, sample: str) -> float | None:
    gene = payload.get("genes", {}).get(marker)
    if not isinstance(gene, dict):
        return None
    values = gene.get("log2_rpm")
    if not isinstance(values, dict) or sample not in values:
        return None
    return float(values[sample])


def paired_deltas(payload: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    identity_markers = [str(marker) for marker in payload.get("identity_markers", [])]
    pluripotency_markers = [str(marker) for marker in payload.get("pluripotency_markers", [])]
    for pair in payload.get("paired_tests", []):
        if not isinstance(pair, dict):
            continue
        control = str(pair.get("control_sample") or "")
        treated = str(pair.get("treated_sample") or "")
        identity_deltas: dict[str, float] = {}
        pluripotency_deltas: dict[str, float] = {}
        for marker in identity_markers:
            control_value = marker_value(payload, marker, control)
            treated_value = marker_value(payload, marker, treated)
            if control_value is not None and treated_value is not None:
                identity_deltas[marker] = treated_value - control_value
        for marker in pluripotency_markers:
            control_value = marker_value(payload, marker, control)
            treated_value = marker_value(payload, marker, treated)
            if control_value is not None and treated_value is not None:
                pluripotency_deltas[marker] = treated_value - control_value
        identity_values = list(identity_deltas.values())
        pluripotency_values = list(pluripotency_deltas.values())
        rows.append(
            {
                "donor": str(pair.get("donor") or ""),
                "day": int(pair.get("day") or 0),
                "experiment": str(pair.get("experiment") or ""),
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


def main() -> int:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = load_inputs()
    rows = paired_deltas(payload)
    identity_marker_count = len(payload.get("identity_markers", []))
    pluripotency_marker_count = len(payload.get("pluripotency_markers", []))
    covered_identity = sorted(
        marker
        for marker in payload.get("identity_markers", [])
        if isinstance(payload.get("genes", {}).get(marker), dict)
    )
    covered_pluripotency = sorted(
        marker
        for marker in REQUIRED_PLURIPOTENCY
        if isinstance(payload.get("genes", {}).get(marker), dict)
    )
    n_pairs = len(rows)
    identity_rms_values = [float(row["identity_rms_delta"]) for row in rows if row["identity_rms_delta"] == row["identity_rms_delta"]]
    pluri_max_values = [
        float(row["pluripotency_max_delta"])
        for row in rows
        if row.get("pluripotency_max_delta") is not None
    ]
    pluripotency_donor_marker_deltas = [
        {
            "donor": row["donor"],
            "marker": marker,
            "delta": delta,
        }
        for row in rows
        for marker, delta in row["pluripotency_marker_deltas"].items()
    ]
    positive_pluripotency_deltas = [
        item
        for item in pluripotency_donor_marker_deltas
        if float(item["delta"]) > STRICT_PLURIPOTENCY_MAX_DELTA
    ]
    max_identity_rms = max(identity_rms_values) if identity_rms_values else None
    max_pluri_delta = max(pluri_max_values) if pluri_max_values else None
    sample_structure_ok = n_pairs >= MIN_DONOR_PAIRS and len({row["donor"] for row in rows}) >= MIN_DONOR_PAIRS
    identity_coverage_ok = len(covered_identity) == identity_marker_count and identity_marker_count >= 8
    pluri_coverage_ok = len(covered_pluripotency) == len(REQUIRED_PLURIPOTENCY)
    identity_distance_ok = max_identity_rms is not None and max_identity_rms <= IDENTITY_RMS_THRESHOLD
    pluripotency_exclusion_ok = max_pluri_delta is not None and max_pluri_delta <= PLURIPOTENCY_MAX_DELTA
    strict_pluripotency_no_positive_ok = (
        bool(pluripotency_donor_marker_deltas) and not positive_pluripotency_deltas
    )
    data_ready = sample_structure_ok and identity_coverage_ok and pluri_coverage_ok
    same_sig_support = (
        data_ready
        and identity_distance_ok
        and pluripotency_exclusion_ok
        and strict_pluripotency_no_positive_ok
    )

    checks = [
        check(
            "sample.structure",
            sample_structure_ok,
            "Expected at least three donor-matched exp2 day-10 negative_control/transiently_reprogrammed pairs.",
            {"n_pairs": n_pairs, "donors": sorted({row["donor"] for row in rows})},
        ),
        check(
            "identity.marker.coverage",
            identity_coverage_ok,
            "All predeclared fibroblast identity markers must be present in the processed matrix.",
            {"covered": covered_identity, "expected_count": identity_marker_count},
        ),
        check(
            "pluripotency.marker.coverage",
            pluri_coverage_ok,
            "POU5F1, NANOG, LIN28A, LIN28B, and SOX2 must be present for exclusion.",
            {"covered": covered_pluripotency, "expected": REQUIRED_PLURIPOTENCY},
        ),
        check(
            "identity.distance.threshold",
            identity_distance_ok,
            "sameSig_I requires every donor pair identity-marker RMS delta to stay within the fixed threshold.",
            {
                "max_identity_rms_delta": max_identity_rms,
                "threshold": IDENTITY_RMS_THRESHOLD,
                "per_pair": [
                    {
                        "donor": row["donor"],
                        "identity_rms_delta": row["identity_rms_delta"],
                        "identity_mean_abs_delta": row["identity_mean_abs_delta"],
                        "identity_max_abs_delta": row["identity_max_abs_delta"],
                    }
                    for row in rows
                ],
            },
        ),
        check(
            "pluripotency.exclusion",
            pluripotency_exclusion_ok,
            "sameSig_I contact must not show a pluripotency marker increase above the fixed delta threshold.",
            {
                "max_pluripotency_delta": max_pluri_delta,
                "threshold": PLURIPOTENCY_MAX_DELTA,
                "per_pair": [
                    {
                        "donor": row["donor"],
                        "pluripotency_max_delta": row["pluripotency_max_delta"],
                        "pluripotency_mean_delta": row["pluripotency_mean_delta"],
                    }
                    for row in rows
                ],
            },
        ),
        check(
            "pluripotency.strict.no_positive_donor_marker",
            strict_pluripotency_no_positive_ok,
            "Stronger sameSig_I exclusion requires every donor-marker pluripotency delta to be non-positive.",
            {
                "positive_delta_count": len(positive_pluripotency_deltas),
                "n_donor_marker_comparisons": len(pluripotency_donor_marker_deltas),
                "strict_threshold": STRICT_PLURIPOTENCY_MAX_DELTA,
                "positive_deltas": positive_pluripotency_deltas,
            },
        ),
        check(
            "promotion.boundary",
            True,
            "Even a positive sameSig_I result would not establish IdentityPreservingAgeResetUp without a separate safety-layer contact.",
            {"blocked_promotions": BLOCKED_PROMOTIONS},
        ),
    ]

    if not data_ready:
        status = "needs_data"
        verdict = "needs_data"
    elif same_sig_support:
        status = "passed"
        verdict = "support_i"
    else:
        status = "failed"
        verdict = "break_i"

    certificate = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "conjecture_id": CONJECTURE_ID,
        "contact_id": CONTACT_ID,
        "data_path": str(DATA_PATH.relative_to(REPO_ROOT)),
        "layer": "cell_identity",
        "sameSig_I": same_sig_support,
        "status": status,
        "verdict": verdict,
        "thresholds": {
            "identity_rms_delta_max": IDENTITY_RMS_THRESHOLD,
            "pluripotency_delta_max": PLURIPOTENCY_MAX_DELTA,
            "strict_pluripotency_delta_max": STRICT_PLURIPOTENCY_MAX_DELTA,
            "min_donor_pairs": MIN_DONOR_PAIRS,
        },
        "summary": {
            "n_pairs": n_pairs,
            "max_identity_rms_delta": max_identity_rms,
            "max_pluripotency_delta": max_pluri_delta,
            "identity_distance_ok": identity_distance_ok,
            "pluripotency_exclusion_ok": pluripotency_exclusion_ok,
            "strict_pluripotency_no_positive_ok": strict_pluripotency_no_positive_ok,
            "pluripotency_positive_delta_count": len(positive_pluripotency_deltas),
            "pluripotency_donor_marker_comparisons": len(pluripotency_donor_marker_deltas),
        },
        "paired_marker_deltas": rows,
        "checks": checks,
        "cannot_claim": [
            "sameSig_I evidence alone does not establish IdentityPreservingAgeResetUp; safety K_S remains separate.",
            "This experiment does not establish rejuvenation, functional repair, renewable maintenance, organismal maintenance, or immortality potential.",
            "This experiment does not establish the GSE142439 age-clock result because it is a separate RNA-seq contact.",
        ],
        "blocked_promotions": [
            {"name": name, "blocked": True, "reason": "The required higher-layer or safety contact is not supplied by this experiment."}
            for name in BLOCKED_PROMOTIONS
        ],
    }
    OUT_PATH.write_text(json.dumps(certificate, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    result = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "contact_id": CONTACT_ID,
        "verdict": verdict,
        "support": same_sig_support,
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

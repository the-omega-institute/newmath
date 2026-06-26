#!/usr/bin/env python3
"""分解 GSE165177 MPTR sameSig_I 的 pluripotency break。"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
CELLSTATE_ROOT = REPO_ROOT / "tools" / "cellstate_reality"
DATA_PATH = CELLSTATE_ROOT / "data" / "k_i_gse165177_mptr_identity_inputs.json"
OUT_DIR = CELLSTATE_ROOT / "out"
OUT_PATH = OUT_DIR / "gse165177_pluripotency_break_decomposition.json"

EXPERIMENT_ID = "gse165177_pluripotency_break_decomposition"
CLAIM_ID = "cellstate.identity-samesig.break-decomposition.gse165177"
CONTACT_ID = "k-i.gse165177-mptr"
DEPENDENCY_CLAIM_ID = "cellstate.identity-samesig.gse165177-mptr"
CONJECTURE_ID = "identity-samesig.break-decomposition.gse165177"

IDENTITY_RMS_THRESHOLD = 1.5
STRICT_PLURIPOTENCY_MAX_DELTA = 0.0
HARD_PLURIPOTENCY_MAX_DELTA = 1.0
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


def strict_break_markers(marker_deltas: dict[str, float]) -> list[str]:
    return sorted(marker for marker, delta in marker_deltas.items() if delta > STRICT_PLURIPOTENCY_MAX_DELTA)


def hard_break_markers(marker_deltas: dict[str, float]) -> list[str]:
    return sorted(marker for marker, delta in marker_deltas.items() if delta > HARD_PLURIPOTENCY_MAX_DELTA)


def donor_rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    identity_markers = [str(marker) for marker in payload.get("identity_markers", [])]
    pluripotency_markers = [str(marker) for marker in payload.get("pluripotency_markers", [])]
    for pair in payload.get("paired_tests", []):
        if not isinstance(pair, dict):
            continue
        donor = str(pair.get("donor") or "")
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

        identity_rms_delta = rms(list(identity_deltas.values()))
        pluripotency_values = list(pluripotency_deltas.values())
        positive_markers = strict_break_markers(pluripotency_deltas)
        hard_markers = hard_break_markers(pluripotency_deltas)
        identity_close = identity_rms_delta <= IDENTITY_RMS_THRESHOLD
        breaks_strict = bool(positive_markers)
        breaks_hard = bool(hard_markers)
        if identity_close and (breaks_strict or breaks_hard):
            case = "identity-close.safety-break"
        elif identity_close:
            case = "identity-close.safety-pass"
        elif breaks_strict or breaks_hard:
            case = "identity-far.safety-break"
        else:
            case = "identity-far.safety-pass"

        rows.append(
            {
                "donor": donor,
                "identity_rms_delta": identity_rms_delta,
                "pluripotency_max_delta": max(pluripotency_values) if pluripotency_values else None,
                "pluripotency_positive_markers": positive_markers,
                "positive_count": len(positive_markers),
                "breaks_strict": breaks_strict,
                "breaks_hard_1.0": breaks_hard,
                "case": case,
                "hard_1.0_markers": hard_markers,
                "pluripotency_marker_deltas": dict(sorted(pluripotency_deltas.items())),
            }
        )
    return rows


def pearson(xs: list[float], ys: list[float]) -> float | None:
    if len(xs) != len(ys) or len(xs) < 2:
        return None
    x_mean = mean(xs)
    y_mean = mean(ys)
    x_centered = [value - x_mean for value in xs]
    y_centered = [value - y_mean for value in ys]
    numerator = sum(x * y for x, y in zip(x_centered, y_centered))
    x_norm = math.sqrt(sum(x * x for x in x_centered))
    y_norm = math.sqrt(sum(y * y for y in y_centered))
    if x_norm == 0.0 or y_norm == 0.0:
        return None
    return numerator / (x_norm * y_norm)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    donor_count = len(rows)
    strict_break_donors = [str(row["donor"]) for row in rows if row["breaks_strict"]]
    hard_break_donors = [str(row["donor"]) for row in rows if row["breaks_hard_1.0"]]
    strict_markers = sorted({marker for row in rows for marker in row["pluripotency_positive_markers"]})
    hard_markers = sorted({marker for row in rows for marker in row["hard_1.0_markers"]})
    identity_close_donors = [
        str(row["donor"])
        for row in rows
        if float(row["identity_rms_delta"]) <= IDENTITY_RMS_THRESHOLD
    ]
    strict_removed_verdict = "break_i" if hard_break_donors else "support_i"
    strict_and_hard_verdict = "break_i" if strict_break_donors or hard_break_donors else "support_i"
    tradeoff_rows = [
        {
            "donor": row["donor"],
            "identity_rms_delta": row["identity_rms_delta"],
            "pluripotency_max_delta": row["pluripotency_max_delta"],
        }
        for row in rows
    ]
    identity_values = [float(row["identity_rms_delta"]) for row in rows]
    pmax_values = [
        float(row["pluripotency_max_delta"])
        for row in rows
        if row["pluripotency_max_delta"] is not None
    ]
    distributed = "distributed_all_donors" if donor_count and len(strict_break_donors) == donor_count else "localized_subset"
    hard_distribution = "distributed_all_donors" if donor_count and len(hard_break_donors) == donor_count else "localized_subset"
    strict_marker_scope = "multi_marker" if len(strict_markers) > 1 else "single_marker"
    hard_marker_scope = "multi_marker" if len(hard_markers) > 1 else "single_marker"
    break_mode = "hard_1.0" if hard_break_donors else "strict_only"
    return {
        "break_donors_strict": strict_break_donors,
        "break_donors_hard_1.0": hard_break_donors,
        "break_distribution_strict": distributed,
        "break_distribution_hard_1.0": hard_distribution,
        "break_markers_strict": strict_markers,
        "break_markers_hard_1.0": hard_markers,
        "marker_scope_strict": strict_marker_scope,
        "marker_scope_hard_1.0": hard_marker_scope,
        "break_mode": break_mode,
        "strict_only": break_mode == "strict_only",
        "verdict_with_strict": strict_and_hard_verdict,
        "verdict_without_strict_no_positive": strict_removed_verdict,
        "verdict_changes_when_strict_removed": strict_and_hard_verdict != strict_removed_verdict,
        "identity_close_donors": identity_close_donors,
        "identity_vs_pluripotency_tradeoff_rows": tradeoff_rows,
        "identity_vs_pluripotency_pearson_r": pearson(identity_values, pmax_values),
        "tradeoff_readout": "descriptive_rows_only",
    }


def main() -> int:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = load_inputs()
    rows = donor_rows(payload)
    covered_pluripotency = sorted(
        marker
        for marker in REQUIRED_PLURIPOTENCY
        if isinstance(payload.get("genes", {}).get(marker), dict)
    )
    donor_count = len(rows)
    summary = build_summary(rows)
    data_ready = donor_count > 0 and covered_pluripotency == sorted(REQUIRED_PLURIPOTENCY)
    decomposition_ready = data_ready and all(row["pluripotency_max_delta"] is not None for row in rows)

    checks = [
        check(
            "input.available",
            DATA_PATH.exists(),
            "The frozen curated GSE165177 MPTR identity input file is readable.",
            {"data_path": str(DATA_PATH.relative_to(REPO_ROOT))},
        ),
        check(
            "pluripotency.marker.coverage",
            covered_pluripotency == sorted(REQUIRED_PLURIPOTENCY),
            "The decomposition requires POU5F1, NANOG, LIN28A, LIN28B, and SOX2.",
            {"covered": covered_pluripotency, "expected": sorted(REQUIRED_PLURIPOTENCY)},
        ),
        check(
            "donor.decomposition.produced",
            decomposition_ready,
            "Each donor-matched day-10 pair must produce identity RMS and pluripotency marker deltas.",
            {"donor_count": donor_count, "donors": [row["donor"] for row in rows]},
        ),
        check(
            "negative_evidence.structured",
            bool(summary["break_donors_strict"]),
            "The certificate records which donor-marker comparisons carry the pluripotency break.",
            {
                "break_donors_strict": summary["break_donors_strict"],
                "break_markers_strict": summary["break_markers_strict"],
                "break_markers_hard_1.0": summary["break_markers_hard_1.0"],
            },
        ),
        check(
            "promotion.boundary",
            True,
            "This decomposition structures a failed sameSig_I contact and does not promote identity preservation or downstream claims.",
            {"blocked_promotions": BLOCKED_PROMOTIONS},
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks[:4]) else "needs_data"

    certificate = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "depends_on": [DEPENDENCY_CLAIM_ID],
        "conjecture_id": CONJECTURE_ID,
        "contact_id": CONTACT_ID,
        "data_path": str(DATA_PATH.relative_to(REPO_ROOT)),
        "layer": "cell_identity",
        "status": status,
        "verdict": "break_i_decomposed" if status == "passed" else "needs_data",
        "thresholds": {
            "identity_rms_delta_max": IDENTITY_RMS_THRESHOLD,
            "strict_pluripotency_delta_max": STRICT_PLURIPOTENCY_MAX_DELTA,
            "hard_pluripotency_delta_max": HARD_PLURIPOTENCY_MAX_DELTA,
        },
        "summary": summary,
        "donors": rows,
        "checks": checks,
        "cannot_claim": [
            "This is a structured characterization of the sameSig_I pluripotency break, not support for IdentityPreservingAgeResetUp.",
            "This certificate does not establish rejuvenation, identity preservation, safety, renewable maintenance, organismal maintenance, or immortality potential.",
        ],
        "blocked_promotions": [
            {"name": name, "blocked": True, "reason": "The underlying sameSig_I contact remains broken by pluripotency marker increases."}
            for name in BLOCKED_PROMOTIONS
        ],
    }
    OUT_PATH.write_text(json.dumps(certificate, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    result = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "depends_on": [DEPENDENCY_CLAIM_ID],
        "verdict": certificate["verdict"],
        "support": False,
        "outputs": {"certificate": str(OUT_PATH.relative_to(REPO_ROOT))},
        "summary": summary,
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

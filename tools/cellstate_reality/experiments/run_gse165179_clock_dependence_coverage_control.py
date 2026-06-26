#!/usr/bin/env python3
"""检验 GSE165179 双 clock 分歧是否可由 coverage 缺口解释。"""

from __future__ import annotations

import json
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
CELLSTATE_ROOT = REPO_ROOT / "tools" / "cellstate_reality"
DATA_PATH = CELLSTATE_ROOT / "data" / "gse165179_dualclock_inputs.json"
OUT_DIR = CELLSTATE_ROOT / "out"
OUT_PATH = OUT_DIR / "gse165179_clock_dependence_coverage_control.json"
EXPERIMENT_ID = "gse165179_clock_dependence_coverage_control"
CLAIM_ID = "cellstate.age-clock-shift.clock-dependence.coverage-control.gse165180"
CONJECTURE_ID = "age-clock-shift.clock-dependence.coverage-control.gse165180"
CONTACT_ID = "k-a.gse165180.horvath353"
BLOCKED_PROMOTIONS = ["identity", "function", "safety", "rejuvenation", "maintenance", "immortality"]


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def load_inputs() -> dict[str, Any]:
    return json.loads(DATA_PATH.read_text(encoding="utf-8"))


def mean(values: list[float]) -> float:
    return sum(values) / float(len(values)) if values else 0.0


def check(name: str, passed: bool, reason: str, value: Any | None = None) -> dict[str, Any]:
    row: dict[str, Any] = {"name": name, "passed": bool(passed), "reason": reason}
    if value is not None:
        row["value"] = value
    return row


def donor_day_intersection_delta(payload: dict[str, Any], clock_id: str, markers: set[str], day: int) -> dict[str, Any]:
    coefficients = {str(marker): float(weight) for marker, weight in payload["clocks"][clock_id]["coefficients"].items()}
    beta = payload["beta"]
    deltas_by_donor: dict[str, list[float]] = defaultdict(list)
    for pair in payload["pairs"]:
        if int(pair["day"]) != day:
            continue
        baseline_title = str(pair["baseline_sample"])
        treated_title = str(pair["treated_sample"])
        delta_z = 0.0
        used = 0
        for marker in sorted(markers):
            marker_values = beta.get(marker)
            if marker not in coefficients or not isinstance(marker_values, dict):
                continue
            if baseline_title not in marker_values or treated_title not in marker_values:
                continue
            delta_z += coefficients[marker] * (float(marker_values[treated_title]) - float(marker_values[baseline_title]))
            used += 1
        deltas_by_donor[str(pair["donor"])].append(delta_z)

    donor_rows = [
        {"donor": donor, "day": day, "observation_count": len(values), "mean_delta_z": mean(values)}
        for donor, values in sorted(deltas_by_donor.items())
    ]
    donor_day_mean = mean([float(row["mean_delta_z"]) for row in donor_rows])
    if donor_day_mean < 0.0:
        direction = "negative"
    elif donor_day_mean > 0.0:
        direction = "positive"
    else:
        direction = "zero"
    return {
        "clock_id": clock_id,
        "day": day,
        "intersection_cpg_used": len(markers),
        "donor_day_mean_delta_z": donor_day_mean,
        "direction": direction,
        "donor_day": donor_rows,
    }


def main() -> int:
    started_at = now_iso()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = load_inputs()
    skin_clock = payload["clocks"]["skin_blood_horvath2"]
    pan_clock = payload["clocks"]["pan_tissue_horvath1"]
    skin_markers = {str(marker) for marker in skin_clock["coefficients"]}
    pan_markers = {str(marker) for marker in pan_clock["coefficients"]}
    intersection = skin_markers & pan_markers
    horvath2_only = skin_markers - pan_markers
    horvath353_only = pan_markers - skin_markers

    skinblood_full_coverage = int(skin_clock.get("clock_cpg_covered") or 0) == int(skin_clock.get("clock_cpg_total") or 0) == len(skin_markers)
    full_skin_day15 = donor_day_intersection_delta(payload, "skin_blood_horvath2", skin_markers, 15)
    full_skin_day17 = donor_day_intersection_delta(payload, "skin_blood_horvath2", skin_markers, 17)
    full_pan_day15 = donor_day_intersection_delta(payload, "pan_tissue_horvath1", pan_markers, 15)
    full_pan_day17 = donor_day_intersection_delta(payload, "pan_tissue_horvath1", pan_markers, 17)
    skinblood_late_not_reversed = full_skin_day15["direction"] == "negative" and full_skin_day17["direction"] == "negative"
    pan_tissue_has_late_reversal = full_pan_day15["direction"] == "positive" and full_pan_day17["direction"] == "positive"
    reversal_explained_by_coverage = not (skinblood_full_coverage and skinblood_late_not_reversed and pan_tissue_has_late_reversal)

    day17_skin = donor_day_intersection_delta(payload, "skin_blood_horvath2", intersection, 17)
    day17_pan = donor_day_intersection_delta(payload, "pan_tissue_horvath1", intersection, 17)
    intersection_still_diverges = day17_skin["direction"] != day17_pan["direction"]
    if intersection_still_diverges:
        divergence_location = "shared_cpg_weighting"
    else:
        divergence_location = "clock-specific_cpg_or_nonshared_weighting"

    checks = [
        check(
            "input.available",
            DATA_PATH.exists(),
            "Curated dual-clock GSE165179 input must be present locally.",
            {"data_path": rel(DATA_PATH)},
        ),
        check(
            "clock.cpg.partition",
            len(intersection) + len(horvath2_only) == len(skin_markers)
            and len(intersection) + len(horvath353_only) == len(pan_markers),
            "The two clock coefficient sets must partition into shared and clock-specific CpGs.",
            {
                "intersection_size": len(intersection),
                "horvath353_only": len(horvath353_only),
                "horvath2_only": len(horvath2_only),
            },
        ),
        check(
            "skinblood.full.coverage",
            skinblood_full_coverage,
            "Skin&blood Horvath2 is fully covered in the curated EPIC matrix.",
            {
                "covered": skin_clock.get("clock_cpg_covered"),
                "total": skin_clock.get("clock_cpg_total"),
            },
        ),
        check(
            "coverage.not.explanatory",
            not reversal_explained_by_coverage,
            "A fully covered clock remains non-reversed while the pan-tissue clock reverses, so the reversal is not explained by missing CpGs.",
            {
                "skinblood_full_coverage": skinblood_full_coverage,
                "skinblood_late_not_reversed": skinblood_late_not_reversed,
                "pan_tissue_has_late_reversal": pan_tissue_has_late_reversal,
                "full_clock_late_directions": {
                    "skin_blood_horvath2_day15": full_skin_day15,
                    "skin_blood_horvath2_day17": full_skin_day17,
                    "pan_tissue_horvath1_day15": full_pan_day15,
                    "pan_tissue_horvath1_day17": full_pan_day17,
                },
            },
        ),
        check(
            "intersection.day17.control",
            len(intersection) > 0,
            "Day17 shared-CpG z-space directions are recomputed using each clock's own weights on the same CpG subset.",
            {
                "skin_blood_horvath2": day17_skin,
                "pan_tissue_horvath1": day17_pan,
                "intersection_still_diverges": intersection_still_diverges,
                "divergence_location": divergence_location,
            },
        ),
        check(
            "age-signature-only.boundary",
            True,
            "The control is a DNAm clock coverage-method result at age_signature layer only.",
            {"blocked_promotions": BLOCKED_PROMOTIONS},
        ),
    ]
    status = "passed" if all(bool(row["passed"]) for row in checks) else "failed"

    artifact = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "conjecture_id": CONJECTURE_ID,
        "contact_id": CONTACT_ID,
        "layer": "age_signature",
        "status": status,
        "started_at": started_at,
        "completed_at": now_iso(),
        "data_path": rel(DATA_PATH),
        "intersection_size": len(intersection),
        "horvath353_only": len(horvath353_only),
        "horvath2_only": len(horvath2_only),
        "skinblood_full_coverage": skinblood_full_coverage,
        "reversal_explained_by_coverage": reversal_explained_by_coverage,
        "full_clock_late_directions": {
            "skin_blood_horvath2_day15": full_skin_day15,
            "skin_blood_horvath2_day17": full_skin_day17,
            "pan_tissue_horvath1_day15": full_pan_day15,
            "pan_tissue_horvath1_day17": full_pan_day17,
        },
        "intersection_day17_directions": {
            "skin_blood_horvath2": day17_skin,
            "pan_tissue_horvath1": day17_pan,
            "intersection_still_diverges": intersection_still_diverges,
            "interpretation": (
                "The shared-CpG subset is scored with each clock's own coefficients. A shared-subset sign split is a clock-weighting "
                "difference on common probes; a shared-subset same sign places the late full-clock split in clock-specific probes or "
                "nonshared coefficient geometry. Neither case is a missing-CpG coverage explanation."
            ),
        },
        "checks": checks,
        "cannot_claim": [
            "This is an age_signature-layer coverage control; clock is a probe and clock-age is a signature.",
            "The artifact does not establish clock-independent biological rejuvenation or biological aging.",
            "It does not establish identity, function, safety, rejuvenation, maintenance, or immortality.",
        ],
        "blocked_promotions": [
            {"name": name, "blocked": True, "reason": "No higher-layer reality contact is supplied by this coverage control."}
            for name in BLOCKED_PROMOTIONS
        ],
    }
    OUT_PATH.write_text(json.dumps(artifact, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"status": status, "checks": checks, "result": artifact, "outputs": {"artifact": rel(OUT_PATH)}}, ensure_ascii=False, sort_keys=True))
    return 0 if status == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())

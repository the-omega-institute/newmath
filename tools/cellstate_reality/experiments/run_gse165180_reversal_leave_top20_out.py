#!/usr/bin/env python3
"""移除 top-20 反转驱动 CpG 后重算 GSE165180 Horvath353 z 空间轨迹。"""

from __future__ import annotations

import json
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
CELLSTATE_ROOT = REPO_ROOT / "tools" / "cellstate_reality"
DATA_PATH = CELLSTATE_ROOT / "data" / "gse165180_horvath353_timecourse_inputs.json"
OUT_DIR = CELLSTATE_ROOT / "out"
OUT_PATH = OUT_DIR / "gse165180_reversal_leave_top20_out.json"
EXPERIMENT_ID = "gse165180_reversal_leave_top20_out"
CLAIM_ID = "cellstate.age-clock-shift.reversal-leave-top20-out.gse165180"
CONJECTURE_ID = "age-clock-shift.reversal-leave-top20-out.gse165180"
CONTACT_ID = "k-a.gse165180.horvath353"
TOP_K = 20
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


def pair_rows(payload: dict[str, Any], markers: set[str] | None = None) -> list[dict[str, Any]]:
    coefficients = {str(marker): float(weight) for marker, weight in payload["clock_coefficients"].items()}
    if markers is None:
        markers = {marker for marker in coefficients if marker in payload["beta"]}
    beta = payload["beta"]
    rows: list[dict[str, Any]] = []
    for pair in payload["pairs"]:
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
        rows.append(
            {
                "donor": str(pair["donor"]),
                "day": int(pair["day"]),
                "experiment": str(pair.get("experiment") or ""),
                "baseline_sample": baseline_title,
                "treated_sample": treated_title,
                "delta_z": delta_z,
                "clock_cpg_used": used,
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
                "clock_cpg_used": min(int(item["clock_cpg_used"]) for item in group) if group else 0,
            }
        )
    return collapsed


def per_timepoint_from_donor_day(donor_day: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for day in sorted({int(row["day"]) for row in donor_day}):
        day_rows = [row for row in donor_day if int(row["day"]) == day]
        rows.append(
            {
                "day": day,
                "donor_day_count": len(day_rows),
                "mean_delta_z": mean([float(row["delta_z"]) for row in day_rows]),
                "negative_donor_day_count": sum(1 for row in day_rows if float(row["delta_z"]) < 0.0),
                "positive_donor_day_count": sum(1 for row in day_rows if float(row["delta_z"]) > 0.0),
                "covered_cpg_after_leaveout": min(int(row["clock_cpg_used"]) for row in day_rows) if day_rows else 0,
            }
        )
    return rows


def contribution_table(payload: dict[str, Any], donor_day: list[dict[str, Any]]) -> list[dict[str, Any]]:
    coefficients = {str(marker): float(weight) for marker, weight in payload["clock_coefficients"].items()}
    covered_markers = [marker for marker in sorted(coefficients) if marker in payload["beta"]]
    days = sorted({int(row["day"]) for row in donor_day})
    donors_by_day = {day: sorted({str(row["donor"]) for row in donor_day if int(row["day"]) == day}) for day in days}

    per_marker: list[dict[str, Any]] = []
    for marker in covered_markers:
        weight = coefficients[marker]
        row: dict[str, Any] = {"cg": marker, "weight": weight}
        for day in days:
            donor_beta_deltas: list[float] = []
            for donor in donors_by_day[day]:
                baseline_titles = sorted(
                    {
                        str(pair["baseline_sample"])
                        for pair in payload["pairs"]
                        if int(pair["day"]) == day and str(pair["donor"]) == donor
                    }
                )
                treated_titles = [
                    str(pair["treated_sample"])
                    for pair in payload["pairs"]
                    if int(pair["day"]) == day and str(pair["donor"]) == donor
                ]
                marker_values = payload["beta"][marker]
                baseline_values = [float(marker_values[title]) for title in baseline_titles if title in marker_values]
                treated_values = [float(marker_values[title]) for title in treated_titles if title in marker_values]
                if baseline_values and treated_values:
                    donor_beta_deltas.append(mean(treated_values) - mean(baseline_values))
            row[f"contrib_day{day}"] = weight * mean(donor_beta_deltas)
        if 10 in days and 17 in days:
            row["delta_contrib_day17_minus_day10"] = float(row["contrib_day17"]) - float(row["contrib_day10"])
        per_marker.append(row)
    return per_marker


def day_value(rows: list[dict[str, Any]], day: int, field: str) -> float:
    for row in rows:
        if int(row["day"]) == day:
            return float(row[field])
    return 0.0


def main() -> int:
    started_at = now_iso()
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = load_inputs()

    full_pair = pair_rows(payload)
    full_donor_day = donor_day_rows(full_pair)
    full_per_timepoint = per_timepoint_from_donor_day(full_donor_day)
    per_marker = contribution_table(payload, full_donor_day)
    top_reversal = sorted(
        per_marker,
        key=lambda row: (
            float(row.get("delta_contrib_day17_minus_day10", 0.0)),
            abs(float(row["weight"])),
            str(row["cg"]),
        ),
        reverse=True,
    )[:TOP_K]
    top20_markers = {str(row["cg"]) for row in top_reversal}
    remaining_markers = {str(marker) for marker in payload["clock_coefficients"] if marker in payload["beta"]} - top20_markers
    leaveout_pair = pair_rows(payload, remaining_markers)
    leaveout_donor_day = donor_day_rows(leaveout_pair)
    leaveout_per_timepoint = per_timepoint_from_donor_day(leaveout_donor_day)

    full_day17_z = day_value(full_per_timepoint, 17, "mean_delta_z")
    leaveout_day17_z = day_value(leaveout_per_timepoint, 17, "mean_delta_z")
    top20_contribution = sum(float(row["contrib_day17"]) for row in top_reversal)
    attenuation = full_day17_z - leaveout_day17_z
    attenuation_ratio = attenuation / full_day17_z if full_day17_z else None
    reversal_removed_by_leaveout = leaveout_day17_z <= 0.0 or (full_day17_z > 0.0 and leaveout_day17_z <= full_day17_z * 0.25)

    top20_rows = [
        {
            "rank": rank,
            "cg": str(row["cg"]),
            "weight": float(row["weight"]),
            "contrib_day10": float(row["contrib_day10"]),
            "contrib_day17": float(row["contrib_day17"]),
            "delta_contrib_day17_minus_day10": float(row["delta_contrib_day17_minus_day10"]),
        }
        for rank, row in enumerate(top_reversal, 1)
    ]
    checks = [
        check(
            "input.available",
            DATA_PATH.exists(),
            "Curated GSE165180 Horvath353 timecourse input must be present locally.",
            {"data_path": rel(DATA_PATH)},
        ),
        check(
            "top20.selected",
            len(top20_markers) == TOP_K,
            "Exactly the fixed top-20 day17-vs-day10 reversal-driver CpGs must be selected.",
            {"top_k": TOP_K, "observed": len(top20_markers)},
        ),
        check(
            "leaveout.coverage",
            len(remaining_markers) == int(payload.get("clock_cpg_covered") or 0) - TOP_K,
            "After removing top-20, the remaining covered coordinate count must be 314.",
            {"remaining": len(remaining_markers), "declared_covered": payload.get("clock_cpg_covered")},
        ),
        check(
            "reversal.leaveout.response",
            reversal_removed_by_leaveout,
            "Removing the top-20 reversal drivers must eliminate or strongly attenuate the day17 positive z-space reversal.",
            {
                "full_day17_z": full_day17_z,
                "leaveout_day17_z": leaveout_day17_z,
                "attenuation": attenuation,
                "attenuation_ratio": attenuation_ratio,
            },
        ),
        check(
            "age-signature-only.boundary",
            True,
            "The leave-out is a clock-internal age_signature mechanism control only.",
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
        "full_day17_z": full_day17_z,
        "leaveout_day17_z": leaveout_day17_z,
        "top20_contribution": top20_contribution,
        "reversal_removed_by_leaveout": reversal_removed_by_leaveout,
        "covered_cpg_full": int(payload.get("clock_cpg_covered") or 0),
        "covered_cpg_after_leaveout": len(remaining_markers),
        "day17_attenuation": attenuation,
        "day17_attenuation_ratio": attenuation_ratio,
        "per_timepoint_full": full_per_timepoint,
        "per_timepoint_leaveout": leaveout_per_timepoint,
        "top20_reversal_cpg": top20_rows,
        "checks": checks,
        "cannot_claim": [
            "This is an age_signature-layer clock-internal leave-out control.",
            "It does not establish an external biological mechanism or biological rejuvenation.",
            "It does not establish identity, function, safety, rejuvenation, maintenance, or immortality.",
        ],
        "blocked_promotions": [
            {"name": name, "blocked": True, "reason": "No higher-layer reality contact is supplied by this clock-coordinate leave-out."}
            for name in BLOCKED_PROMOTIONS
        ],
    }
    OUT_PATH.write_text(json.dumps(artifact, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"status": status, "checks": checks, "result": artifact, "outputs": {"artifact": rel(OUT_PATH)}}, ensure_ascii=False, sort_keys=True))
    return 0 if status == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())

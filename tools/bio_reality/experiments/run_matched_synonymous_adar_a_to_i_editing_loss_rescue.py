#!/usr/bin/env python3
"""Matched synonymous ADAR A-to-I editing loss/rescue assay skeleton."""

from __future__ import annotations

import json
import math
import pathlib
import sys
from datetime import datetime, timezone
from typing import Any


EXPERIMENT_ID = "matched-synonymous-ADAR-A-to-I-editing-loss-rescue"
CLAIM_ID = "bio-Plan.direction.new-frontier.ADAR-mediated-editing-bridge"
DATA_PATH = "tools/bio_reality/data/matched_synonymous_adar_a_to_i_editing_loss_rescue.json"

MIN_MATCHED_PAIRS = 48
MIN_ADAR_PRESENT_MEAN_DELTA = 0.10
MIN_ADAR_PRESENT_WIN_RATE = 0.75
MAX_ADAR_PRESENT_SIGN_TEST_P = 0.001
MAX_ADAR_LOSS_ABS_MEAN_DELTA = 0.03
MAX_ADAR_LOSS_WIN_RATE = 0.60
MAX_CATALYTIC_INHIBITION_ABS_MEAN_DELTA = 0.03
MAX_CATALYTIC_INHIBITION_WIN_RATE = 0.60
MIN_WILD_TYPE_RESCUE_FRACTION = 0.75
MAX_CATALYTIC_DEAD_RESCUE_FRACTION = 0.25
MAX_BINDING_DEFECTIVE_RESCUE_FRACTION = 0.25
MIN_OCCUPANCY_EDITING_CORRELATION = 0.45
MAX_CONTROL_REPRODUCTION_FRACTION = 0.25
FORBIDDEN_PROMOTIONS = [
    "translation realization",
    "protein structure",
    "physical admissibility",
    "biological function",
    "global biological law",
]


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def emit(status: str, **kwargs: Any) -> None:
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "started_at": kwargs.pop("started_at", now_iso()),
        "completed_at": now_iso(),
    }
    payload.update(kwargs)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def numeric(value: Any, field: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{field} must be numeric")
    return float(value)


def rows(data: dict[str, Any], key: str) -> list[dict[str, Any]]:
    raw = data.get(key)
    if not isinstance(raw, list):
        raise ValueError(f"{key} must be a list")
    parsed = [item for item in raw if isinstance(item, dict)]
    if len(parsed) != len(raw):
        raise ValueError(f"{key} must contain only objects")
    return parsed


def optional_rows(data: dict[str, Any], key: str) -> list[dict[str, Any]]:
    raw = data.get(key, [])
    if not isinstance(raw, list):
        raise ValueError(f"{key} must be a list when present")
    parsed = [item for item in raw if isinstance(item, dict)]
    if len(parsed) != len(raw):
        raise ValueError(f"{key} must contain only objects")
    return parsed


def binomial_upper_tail(successes: int, n: int, p: float = 0.5) -> float:
    if not 0 <= successes <= n:
        raise ValueError("successes must be between 0 and n")
    return sum(math.comb(n, k) * (p**k) * ((1.0 - p) ** (n - k)) for k in range(successes, n + 1))


def pearson(xs: list[float], ys: list[float]) -> float:
    n = len(xs)
    if n < 2 or n != len(ys):
        return 0.0
    mean_x = sum(xs) / n
    mean_y = sum(ys) / n
    var_x = sum((x - mean_x) ** 2 for x in xs)
    var_y = sum((y - mean_y) ** 2 for y in ys)
    if var_x <= 0.0 or var_y <= 0.0:
        return 0.0
    cov = sum((xs[i] - mean_x) * (ys[i] - mean_y) for i in range(n))
    return cov / math.sqrt(var_x * var_y)


def parse_time(value: Any) -> datetime | None:
    text = str(value or "").strip()
    if not text:
        return None
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    try:
        return datetime.fromisoformat(text)
    except ValueError:
        return None


def protocol_frozen_before_measurement(data: dict[str, Any]) -> dict[str, Any]:
    flags = [
        "internal_coordinate_frozen_before_outcome",
        "q_partition_frozen_before_outcome",
        "matched_design_preregistered",
        "analysis_thresholds_preregistered",
        "coordinate_used_only_as_design_axis",
    ]
    flags_ok = all(data.get(flag) is True for flag in flags)
    frozen_at = parse_time(data.get("protocol_frozen_at"))
    measured_at = parse_time(data.get("outcome_measurement_started_at"))
    passed = flags_ok and frozen_at is not None and measured_at is not None and frozen_at < measured_at
    return {
        "name": "protocol_frozen_before_measurement",
        "passed": passed,
        "actual": {
            "protocol_frozen_at": data.get("protocol_frozen_at"),
            "outcome_measurement_started_at": data.get("outcome_measurement_started_at"),
            **{flag: data.get(flag) for flag in flags},
        },
        "expected": "all freeze flags true and protocol_frozen_at before outcome_measurement_started_at",
    }


def no_forbidden_promotion(data: dict[str, Any]) -> dict[str, Any]:
    cannot_claim = [str(item).lower() for item in data.get("cannot_claim", []) if isinstance(item, str)]
    joined = " ".join(cannot_claim)
    passed = all(token in joined for token in FORBIDDEN_PROMOTIONS)
    return {
        "name": "no_geometry_to_higher_layer_promotion",
        "passed": passed,
        "actual": data.get("cannot_claim"),
        "expected": FORBIDDEN_PROMOTIONS,
    }


def matched_pair_rows(data: dict[str, Any]) -> list[dict[str, Any]]:
    pair_rows = rows(data, "matched_variant_pairs")
    required_boolean_flags = [
        "q_plus",
        "q_minus",
        "amino_acid_sequence_preserved",
        "local_rna_structure_matched",
        "editing_complementary_strength_matched",
        "gc_dinucleotide_matched",
        "codon_pair_context_matched",
        "motif_density_matched",
        "splice_context_matched",
        "transcript_abundance_matched",
        "batch_matched",
    ]
    for index, row in enumerate(pair_rows):
        for flag in required_boolean_flags:
            if row.get(flag) is not True:
                raise ValueError(f"matched_variant_pairs[{index}].{flag} must be true")
    return pair_rows


def condition_delta(row: dict[str, Any], condition: str) -> float:
    plus = numeric(row.get(f"{condition}_q_plus_editing_fraction"), f"{condition} q_plus editing fraction")
    minus = numeric(row.get(f"{condition}_q_minus_editing_fraction"), f"{condition} q_minus editing fraction")
    return plus - minus


def condition_stats(pair_rows: list[dict[str, Any]], condition: str) -> dict[str, Any]:
    deltas = [condition_delta(row, condition) for row in pair_rows]
    wins = sum(1 for delta in deltas if delta > 0.0)
    n = len(deltas)
    mean_delta = sum(deltas) / n if n else 0.0
    return {
        "condition": condition,
        "n": n,
        "wins": wins,
        "win_rate": wins / n if n else 0.0,
        "mean_delta": mean_delta,
        "abs_mean_delta": abs(mean_delta),
        "sign_test_p": binomial_upper_tail(wins, n) if n else 1.0,
    }


def rescue_fraction(pair_rows: list[dict[str, Any]], condition: str, baseline_delta: float) -> float:
    if baseline_delta <= 0.0:
        return 0.0
    rescued = 0
    for row in pair_rows:
        restored = condition_delta(row, condition) / baseline_delta
        if restored >= MIN_WILD_TYPE_RESCUE_FRACTION:
            rescued += 1
    return rescued / len(pair_rows) if pair_rows else 0.0


def false_rescue_fraction(pair_rows: list[dict[str, Any]], condition: str, baseline_delta: float) -> float:
    if baseline_delta <= 0.0:
        return 1.0
    reproduced = 0
    for row in pair_rows:
        restored = condition_delta(row, condition) / baseline_delta
        if restored >= MIN_WILD_TYPE_RESCUE_FRACTION:
            reproduced += 1
    return reproduced / len(pair_rows) if pair_rows else 1.0


def controls_reproduce_effect(data: dict[str, Any], baseline_delta: float) -> dict[str, Any]:
    controls = optional_rows(data, "structure_composition_controls")
    if not controls:
        return {
            "name": "structure_composition_controls_do_not_reproduce",
            "passed": False,
            "actual": {"control_rows": 0},
            "expected": "non-empty controls with reproduction fraction below threshold",
        }
    reproduced = 0
    for row in controls:
        control_delta = numeric(row.get("adar_present_control_delta"), "adar_present_control_delta")
        restores_substrate = row.get("restores_adar_substrate") is True
        if not restores_substrate and baseline_delta > 0 and control_delta / baseline_delta >= MIN_WILD_TYPE_RESCUE_FRACTION:
            reproduced += 1
    fraction = reproduced / len(controls)
    return {
        "name": "structure_composition_controls_do_not_reproduce",
        "passed": fraction <= MAX_CONTROL_REPRODUCTION_FRACTION,
        "actual": {"control_rows": len(controls), "reproduction_fraction": fraction},
        "expected": {"max_reproduction_fraction": MAX_CONTROL_REPRODUCTION_FRACTION},
    }


def occupancy_editing_correlation(pair_rows: list[dict[str, Any]]) -> dict[str, Any]:
    occupancy = []
    editing = []
    for row in pair_rows:
        q_plus_occ = numeric(row.get("adar_present_q_plus_occupancy"), "adar_present_q_plus_occupancy")
        q_minus_occ = numeric(row.get("adar_present_q_minus_occupancy"), "adar_present_q_minus_occupancy")
        occupancy.append(q_plus_occ - q_minus_occ)
        editing.append(condition_delta(row, "adar_present"))
    corr = pearson(occupancy, editing)
    return {
        "name": "occupancy_tracks_editing_delta",
        "passed": corr >= MIN_OCCUPANCY_EDITING_CORRELATION,
        "actual": {"pearson_r": corr, "n": len(pair_rows)},
        "expected": {"min_pearson_r": MIN_OCCUPANCY_EDITING_CORRELATION},
    }


def main() -> None:
    started_at = now_iso()
    repo = pathlib.Path(__file__).resolve().parents[3]
    data_path = repo / DATA_PATH
    if not data_path.exists():
        emit(
            "needs_data",
            started_at=started_at,
            checks=[],
            result={"missing_data": [DATA_PATH]},
            reason="curated matched synonymous ADAR A-to-I editing loss/rescue data not present",
        )
    try:
        data = json.loads(data_path.read_text(encoding="utf-8"))
        if not isinstance(data, dict):
            raise ValueError("dataset root must be an object")
        pair_rows = matched_pair_rows(data)
        present = condition_stats(pair_rows, "adar_present")
        loss = condition_stats(pair_rows, "adar_loss")
        inhibition = condition_stats(pair_rows, "catalytic_inhibition")
        baseline_delta = float(present["mean_delta"])
        wt_rescue = rescue_fraction(pair_rows, "wild_type_rescue", baseline_delta)
        catalytic_dead = false_rescue_fraction(pair_rows, "catalytic_dead_rescue", baseline_delta)
        binding_defective = false_rescue_fraction(pair_rows, "binding_defective_rescue", baseline_delta)
        checks = [
            {
                "name": "matched_synonymous_dataset_loaded",
                "passed": True,
                "actual": {"data_path": DATA_PATH, "matched_pairs": len(pair_rows)},
                "expected": {"min_matched_pairs": MIN_MATCHED_PAIRS},
            },
            protocol_frozen_before_measurement(data),
            {
                "name": "matched_pair_count",
                "passed": len(pair_rows) >= MIN_MATCHED_PAIRS,
                "actual": len(pair_rows),
                "expected": {"min_matched_pairs": MIN_MATCHED_PAIRS},
            },
            {
                "name": "adar_present_q_plus_advantage",
                "passed": (
                    present["mean_delta"] >= MIN_ADAR_PRESENT_MEAN_DELTA
                    and present["win_rate"] >= MIN_ADAR_PRESENT_WIN_RATE
                    and present["sign_test_p"] <= MAX_ADAR_PRESENT_SIGN_TEST_P
                ),
                "actual": present,
                "expected": {
                    "min_mean_delta": MIN_ADAR_PRESENT_MEAN_DELTA,
                    "min_win_rate": MIN_ADAR_PRESENT_WIN_RATE,
                    "max_sign_test_p": MAX_ADAR_PRESENT_SIGN_TEST_P,
                },
            },
            {
                "name": "adar_loss_collapses_q_association",
                "passed": loss["abs_mean_delta"] <= MAX_ADAR_LOSS_ABS_MEAN_DELTA and loss["win_rate"] <= MAX_ADAR_LOSS_WIN_RATE,
                "actual": loss,
                "expected": {"max_abs_mean_delta": MAX_ADAR_LOSS_ABS_MEAN_DELTA, "max_win_rate": MAX_ADAR_LOSS_WIN_RATE},
            },
            {
                "name": "catalytic_inhibition_collapses_q_association",
                "passed": inhibition["abs_mean_delta"] <= MAX_CATALYTIC_INHIBITION_ABS_MEAN_DELTA
                and inhibition["win_rate"] <= MAX_CATALYTIC_INHIBITION_WIN_RATE,
                "actual": inhibition,
                "expected": {
                    "max_abs_mean_delta": MAX_CATALYTIC_INHIBITION_ABS_MEAN_DELTA,
                    "max_win_rate": MAX_CATALYTIC_INHIBITION_WIN_RATE,
                },
            },
            {
                "name": "wild_type_rescue_restores_association",
                "passed": wt_rescue >= MIN_WILD_TYPE_RESCUE_FRACTION,
                "actual": {"rescue_fraction": wt_rescue},
                "expected": {"min_rescue_fraction": MIN_WILD_TYPE_RESCUE_FRACTION},
            },
            {
                "name": "catalytic_dead_rescue_fails",
                "passed": catalytic_dead <= MAX_CATALYTIC_DEAD_RESCUE_FRACTION,
                "actual": {"false_rescue_fraction": catalytic_dead},
                "expected": {"max_false_rescue_fraction": MAX_CATALYTIC_DEAD_RESCUE_FRACTION},
            },
            {
                "name": "binding_defective_rescue_fails",
                "passed": binding_defective <= MAX_BINDING_DEFECTIVE_RESCUE_FRACTION,
                "actual": {"false_rescue_fraction": binding_defective},
                "expected": {"max_false_rescue_fraction": MAX_BINDING_DEFECTIVE_RESCUE_FRACTION},
            },
            occupancy_editing_correlation(pair_rows),
            controls_reproduce_effect(data, baseline_delta),
            no_forbidden_promotion(data),
        ]
        result = {
            "scope": "site_specific_a_to_i_rna_editing_bridge_only",
            "matched_pairs": len(pair_rows),
            "primary_statistic": present,
            "loss_statistics": {"adar_loss": loss, "catalytic_inhibition": inhibition},
            "rescue_fractions": {
                "wild_type_rescue": wt_rescue,
                "catalytic_dead_rescue": catalytic_dead,
                "binding_defective_rescue": binding_defective,
            },
            "stronger_statistic": (
                "matched synonymous pair sign-test plus ADAR perturbation loss/rescue controls, "
                "requiring occupancy/editing coupling and non-reproduction by structure/composition controls"
            ),
            "forbidden_promotions": FORBIDDEN_PROMOTIONS,
        }
        emit("passed" if all(check["passed"] for check in checks) else "failed", started_at=started_at, checks=checks, result=result)
    except Exception as exc:
        emit("failed", started_at=started_at, checks=[], result={"error": str(exc)}, reason="experiment computation failed")


if __name__ == "__main__":
    main()

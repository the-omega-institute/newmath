#!/usr/bin/env python3
"""Produce the canonical irreducibility report."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
import time
from typing import Any, Mapping, Sequence

import numpy as np


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


JSON_ARTIFACT = "reports/canonical/irreducibility_report.json"
REPORT_ARTIFACT = "reports/canonical/order_residual_analysis.md"
CMI_ARTIFACT = "reports/canonical/conditional_information_table.json"
REPORT_JSON = ROOT / JSON_ARTIFACT
REPORT_MD = ROOT / REPORT_ARTIFACT
CMI_JSON = ROOT / CMI_ARTIFACT
SCHEMA_ID = "bedc-quality-lab:irreducibility-report"
ARTIFACT_ID = "bedc-quality-lab:irreducibility-report"
SAMPLE_COUNT = 512
SMOKE_SAMPLE_COUNT = 160
ORDER_VALUES = (2, 3)
SEEDS = (101, 211, 307, 401)
SMOKE_SEEDS = (101, 211)
GAIN_EPSILON = 1.0e-9
STABILITY_MIN_ABS_GAIN = 1.0e-6
CONTROL_POSITIVE_GAIN = 0.05


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def _lab_fixture(seed: int, sample_count: int) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(int(seed))
    x = rng.normal(size=(sample_count, 3))
    noise = rng.normal(scale=0.025, size=sample_count)
    pairwise = x[:, 0] * x[:, 1]
    triple = x[:, 0] * x[:, 1] * x[:, 2]
    target = 0.55 * x[:, 0] - 0.20 * x[:, 1] + 1.00 * pairwise + 0.80 * triple + noise
    permutation = rng.permutation(sample_count)
    train_count = int(sample_count * 0.55)
    train_idx = np.sort(permutation[:train_count])
    eval_idx = np.sort(permutation[train_count:])
    return {
        "x": x.astype(np.float64),
        "target": target.astype(np.float64),
        "train_idx": train_idx,
        "eval_idx": eval_idx,
    }


def _feature_builder(x: np.ndarray, order: int) -> tuple[np.ndarray, list[str]]:
    columns: list[np.ndarray] = [np.ones(x.shape[0], dtype=np.float64)]
    names = ["constant"]
    for index in range(x.shape[1]):
        columns.append(x[:, index])
        names.append(f"x{index + 1}")
    if order >= 2:
        for left in range(x.shape[1]):
            for right in range(left + 1, x.shape[1]):
                columns.append(x[:, left] * x[:, right])
                names.append(f"x{left + 1}*x{right + 1}")
    if order >= 3:
        columns.append(x[:, 0] * x[:, 1] * x[:, 2])
        names.append("x1*x2*x3")
    return np.column_stack(columns).astype(np.float64), names


def _same_split_feature_sets(surface: Mapping[str, np.ndarray], order: int) -> dict[str, Any]:
    if order <= 1:
        raise ValueError("order must be at least 2")
    low_features, low_columns = _feature_builder(surface["x"], order - 1)
    high_features, high_columns = _feature_builder(surface["x"], order)
    train_idx = np.asarray(surface["train_idx"], dtype=np.int64)
    eval_idx = np.asarray(surface["eval_idx"], dtype=np.int64)
    overlap = set(train_idx.tolist()) & set(eval_idx.tolist())
    if overlap:
        raise ValueError("train/eval split must be disjoint")
    return {
        "order": int(order),
        "train_idx": train_idx,
        "eval_idx": eval_idx,
        "low_features": low_features,
        "high_features": high_features,
        "low_columns": low_columns,
        "high_columns": high_columns,
        "added_columns": high_columns[len(low_columns) :],
    }


def _fit_linear(train_features: np.ndarray, train_target: np.ndarray) -> np.ndarray:
    coef, *_ = np.linalg.lstsq(train_features, train_target, rcond=None)
    return np.asarray(coef, dtype=np.float64)


def _mse(values: np.ndarray) -> float:
    return float(np.mean(np.square(values)))


def _residual_scorer(feature_sets: Mapping[str, Any], target: np.ndarray) -> dict[str, Any]:
    train_idx = feature_sets["train_idx"]
    eval_idx = feature_sets["eval_idx"]
    low_features = feature_sets["low_features"]
    high_features = feature_sets["high_features"]
    low_coef = _fit_linear(low_features[train_idx], target[train_idx])
    high_coef = _fit_linear(high_features[train_idx], target[train_idx])
    low_eval_residual = target[eval_idx] - low_features[eval_idx] @ low_coef
    high_eval_residual = target[eval_idx] - high_features[eval_idx] @ high_coef
    low_mse = _mse(low_eval_residual)
    high_mse = _mse(high_eval_residual)
    gain = low_mse - high_mse
    finite = all(math.isfinite(value) for value in (low_mse, high_mse, gain))
    return {
        "low_order_mse": low_mse,
        "high_order_mse": high_mse,
        "conditioned_residual_gain": gain,
        "finite": finite,
    }


def _lower_order_ablation(feature_sets: Mapping[str, Any], target: np.ndarray) -> dict[str, Any]:
    low = _residual_scorer(feature_sets, target)
    return {
        "status": "pass" if low["finite"] else "invalid",
        "baseline_pointer": "$.records[*].orders[*].low_order_mse",
        "same_split": True,
        "low_order_mse": low["low_order_mse"],
        "conditioned_residual_gain": low["conditioned_residual_gain"],
    }


def _matched_random_control(feature_sets: Mapping[str, Any], target: np.ndarray, *, seed: int) -> dict[str, Any]:
    rng = np.random.default_rng(int(seed) + 900_001)
    randomized_high = np.array(feature_sets["high_features"], copy=True)
    low_width = int(feature_sets["low_features"].shape[1])
    permutation = rng.permutation(randomized_high.shape[0])
    randomized_high[:, low_width:] = randomized_high[permutation, low_width:]
    randomized_feature_sets = dict(feature_sets)
    randomized_feature_sets["high_features"] = randomized_high
    scores = _residual_scorer(randomized_feature_sets, target)
    positive = bool(scores["finite"] and scores["conditioned_residual_gain"] > CONTROL_POSITIVE_GAIN)
    return {
        "status": "fail" if positive else "pass",
        "positive": positive,
        "matched_split": True,
        "matched_feature_shape": list(feature_sets["high_features"].shape),
        "positive_gain_threshold": CONTROL_POSITIVE_GAIN,
        "conditioned_residual_gain": scores["conditioned_residual_gain"],
        "low_order_mse": scores["low_order_mse"],
        "high_order_mse": scores["high_order_mse"],
    }


def _bounded_cmi_diagnostic(feature_sets: Mapping[str, Any], target: np.ndarray) -> dict[str, Any]:
    train_idx = feature_sets["train_idx"]
    eval_idx = feature_sets["eval_idx"]
    low_features = feature_sets["low_features"]
    high_features = feature_sets["high_features"]
    low_coef = _fit_linear(low_features[train_idx], target[train_idx])
    high_coef = _fit_linear(high_features[train_idx], target[train_idx])
    low_residual = target[eval_idx] - low_features[eval_idx] @ low_coef
    high_residual = target[eval_idx] - high_features[eval_idx] @ high_coef
    low_var = float(np.var(low_residual) + 1.0e-12)
    high_var = float(np.var(high_residual) + 1.0e-12)
    bounded_cmi = max(0.0, min(10.0, 0.5 * math.log(low_var / high_var))) if high_var > 0 else 0.0
    return {
        "diagnostic_only": True,
        "bounded_cmi": float(bounded_cmi),
        "low_residual_variance": low_var,
        "high_residual_variance": high_var,
        "can_set_positive_irreducibility": False,
    }


def _seed_order_record(seed: int, order: int, sample_count: int) -> dict[str, Any]:
    surface = _lab_fixture(seed, sample_count)
    feature_sets = _same_split_feature_sets(surface, order)
    residual = _residual_scorer(feature_sets, surface["target"])
    control = _matched_random_control(feature_sets, surface["target"], seed=seed)
    cmi = _bounded_cmi_diagnostic(feature_sets, surface["target"])
    return {
        "seed": int(seed),
        "order": int(order),
        "split": {
            "train_count": int(len(feature_sets["train_idx"])),
            "eval_count": int(len(feature_sets["eval_idx"])),
            "overlap_count": 0,
        },
        "low_order": int(order - 1),
        "high_order": int(order),
        "low_order_feature_columns": list(feature_sets["low_columns"]),
        "high_order_feature_columns": list(feature_sets["high_columns"]),
        "added_high_order_columns": list(feature_sets["added_columns"]),
        "low_order_baseline_present": bool(feature_sets["low_features"].shape[1] > 0),
        "low_order_mse": residual["low_order_mse"],
        "high_order_mse": residual["high_order_mse"],
        "conditioned_residual_gain": residual["conditioned_residual_gain"],
        "lower_order_ablation": _lower_order_ablation(feature_sets, surface["target"]),
        "matched_random_control": control,
        "conditional_information": cmi,
        "finite_metrics": bool(residual["finite"] and all(math.isfinite(float(control[key])) for key in ("conditioned_residual_gain", "low_order_mse", "high_order_mse"))),
    }


def _metric_stats(values: Sequence[float]) -> dict[str, Any]:
    arr = np.asarray(values, dtype=np.float64)
    if arr.size == 0:
        return {"n": 0, "mean": None, "min": None, "max": None, "all_positive": False}
    return {
        "n": int(arr.size),
        "mean": float(np.mean(arr)),
        "min": float(np.min(arr)),
        "max": float(np.max(arr)),
        "all_positive": bool(np.all(arr > GAIN_EPSILON)),
    }


def _seed_aggregation(records: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    by_order: dict[int, list[Mapping[str, Any]]] = {}
    for record in records:
        by_order.setdefault(int(record["order"]), []).append(record)
    rows = {}
    for order, order_records in sorted(by_order.items()):
        treatment_gain = [float(row["conditioned_residual_gain"]) for row in order_records]
        control_gain = [float(row["matched_random_control"]["conditioned_residual_gain"]) for row in order_records]
        rows[str(order)] = {
            "order": int(order),
            "seed_count": int(len({int(row["seed"]) for row in order_records})),
            "treatment_gain": _metric_stats(treatment_gain),
            "matched_random_gain": _metric_stats(control_gain),
            "stable_positive_direction": bool(all(value > STABILITY_MIN_ABS_GAIN for value in treatment_gain)),
            "matched_random_any_positive": bool(any(value > GAIN_EPSILON for value in control_gain)),
        }
    return {
        "order_count": int(len(rows)),
        "orders": rows,
    }


def _hardgate_projector(records: Sequence[Mapping[str, Any]], aggregation: Mapping[str, Any]) -> dict[str, Any]:
    gate1_pass = all(
        row.get("low_order_baseline_present") is True
        and row.get("low_order") == int(row.get("order", 0)) - 1
        and row.get("split", {}).get("overlap_count") == 0
        for row in records
    )
    gate2_pass = all(float(row.get("conditioned_residual_gain", 0.0)) > GAIN_EPSILON for row in records)
    gate3_pass = all(row.get("matched_random_control", {}).get("positive") is False for row in records)
    finite = all(row.get("finite_metrics") is True for row in records)
    order_rows = aggregation.get("orders") if isinstance(aggregation.get("orders"), Mapping) else {}
    enough_seed_count = bool(order_rows) and all(
        isinstance(row, Mapping) and int(row.get("seed_count", 0)) >= 2 for row in order_rows.values()
    )
    stable_direction = bool(order_rows) and all(
        isinstance(row, Mapping) and row.get("stable_positive_direction") is True for row in order_rows.values()
    )
    gate4_pass = bool(enough_seed_count and finite and stable_direction)
    gates = {
        "IRR-HG1": {
            "status": "pass" if gate1_pass else "fail",
            "requirement": "D^{<k} low-order baseline exists and uses the same held-out split as D^k.",
            "evidence_pointer": "$.records[*].orders[*].low_order_baseline_present",
        },
        "IRR-HG2": {
            "status": "pass" if gate2_pass else "fail",
            "requirement": "Positive irreducibility requires held-out conditioned residual gain > 0.",
            "evidence_pointer": "$.records[*].orders[*].conditioned_residual_gain",
        },
        "IRR-HG3": {
            "status": "pass" if gate3_pass else "fail",
            "requirement": "Matched-random high-order residual positives block the claim.",
            "evidence_pointer": "$.records[*].orders[*].matched_random_control",
        },
        "IRR-HG4": {
            "status": "pass" if gate4_pass else "fail",
            "requirement": "At least two seeds, finite metrics, and stable gain direction are required.",
            "evidence_pointer": "$.seed_aggregation.orders",
        },
    }
    failed = next((gate_id for gate_id, row in gates.items() if row["status"] != "pass"), None)
    return {
        "status": "pass" if failed is None else "fail",
        "failed_gate": failed,
        "gates": gates,
        "positive_irreducibility": failed is None,
    }


def _records(seeds: Sequence[int], orders: Sequence[int], sample_count: int) -> list[dict[str, Any]]:
    rows = []
    for seed in seeds:
        order_rows = [_seed_order_record(int(seed), int(order), sample_count) for order in orders]
        rows.append(
            {
                "seed": int(seed),
                "sample_count": int(sample_count),
                "orders": order_rows,
            }
        )
    return rows


def _flatten_order_records(records: Sequence[Mapping[str, Any]]) -> list[Mapping[str, Any]]:
    return [order for record in records for order in record.get("orders", [])]


def _conditional_information_table(records: Sequence[Mapping[str, Any]], generated_at: str) -> dict[str, Any]:
    rows = []
    for record in records:
        for order in record["orders"]:
            rows.append(
                {
                    "seed": int(record["seed"]),
                    "order": int(order["order"]),
                    "diagnostic_only": True,
                    "bounded_cmi": order["conditional_information"]["bounded_cmi"],
                    "low_residual_variance": order["conditional_information"]["low_residual_variance"],
                    "high_residual_variance": order["conditional_information"]["high_residual_variance"],
                    "can_set_positive_irreducibility": False,
                }
            )
    return {
        "schema_id": "bedc-quality-lab:conditional-information-table",
        "artifact_id": "bedc-quality-lab:conditional-information-table",
        "generated_at": generated_at,
        "producer": "scripts/run_irreducibility_report.py",
        "diagnostic_only": True,
        "row_count": len(rows),
        "rows": rows,
    }


def _source_artifacts() -> dict[str, Any]:
    return {
        "generation_script": "scripts/run_irreducibility_report.py",
        "toy_fixture": "scripts/run_irreducibility_report.py::_lab_fixture",
        "residual_scorer": "scripts/run_irreducibility_report.py::_residual_scorer",
        "matched_random_control": "scripts/run_irreducibility_report.py::_matched_random_control",
        "conditional_information_table": CMI_ARTIFACT,
    }


def _payload(
    *,
    records: list[dict[str, Any]],
    generated_at: str,
    elapsed_seconds: float,
    smoke: bool,
) -> tuple[dict[str, Any], dict[str, Any]]:
    flat = _flatten_order_records(records)
    aggregation = _seed_aggregation(flat)
    hardgate = _hardgate_projector(flat, aggregation)
    cmi_table = _conditional_information_table(records, generated_at)
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": "scripts/run_irreducibility_report.py",
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": REPORT_ARTIFACT,
        "conditional_information_table_artifact": CMI_ARTIFACT,
        "source_artifacts": _source_artifacts(),
        "config": {
            "sample_count": int(records[0]["sample_count"]) if records else 0,
            "seeds": [int(record["seed"]) for record in records],
            "orders": list(ORDER_VALUES if not smoke else ORDER_VALUES),
            "smoke": bool(smoke),
        },
        "scope": {
            "admitted_fixture": "deterministic Gaussian-OU style polynomial lab fixture",
            "feature_family": "same-split D^{<k} and D^k polynomial features",
            "not_claimed": [
                "No global irreducibility theorem.",
                "No production model claim.",
                "No claim from CMI alone.",
            ],
        },
        "control_protocol": {
            "low_order_baseline": "D^{<k}",
            "high_order_candidate": "D^k",
            "same_split": True,
            "matched_random_high_order_residual_control": True,
            "seed_stability_required": True,
        },
        "seed_aggregation": aggregation,
        "hardgate": hardgate,
        "positive_claim": {
            "positive_irreducibility": bool(hardgate["positive_irreducibility"]),
            "claim_pointer": "$.hardgate.positive_irreducibility",
            "blocked_by": hardgate["failed_gate"],
            "cmi_diagnostic_only": True,
        },
        "conditional_information_table": {
            "artifact": CMI_ARTIFACT,
            "pointer": "$.rows",
            "diagnostic_only": True,
            "can_set_positive_irreducibility": False,
            "row_count": cmi_table["row_count"],
        },
        "records": records,
        "elapsed_seconds": float(f"{elapsed_seconds:.3f}"),
        "not_claimed": [
            "CMI diagnostics do not set positive irreducibility.",
            "Matched-random high-order residual positives fail closed.",
            "The report is bounded to the deterministic lab fixture.",
        ],
    }
    return payload, cmi_table


def _format_float(value: Any) -> str:
    return f"{float(value):.6f}" if isinstance(value, (int, float)) and math.isfinite(float(value)) else "missing"


def _render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Irreducibility Report",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Status: `{payload['hardgate']['status']}`",
        f"- Positive irreducibility: `{payload['positive_claim']['positive_irreducibility']}`",
        f"- CMI table: `{payload['conditional_information_table_artifact']}`",
        "",
        "## Order Residual Analysis",
        "",
        "| seed | order | low-order MSE | high-order MSE | gain | matched-random gain |",
        "| ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for record in payload["records"]:
        for order in record["orders"]:
            lines.append(
                "| "
                f"{record['seed']} | "
                f"{order['order']} | "
                f"{_format_float(order['low_order_mse'])} | "
                f"{_format_float(order['high_order_mse'])} | "
                f"{_format_float(order['conditioned_residual_gain'])} | "
                f"{_format_float(order['matched_random_control']['conditioned_residual_gain'])} |"
            )
    lines.extend(["", "## Hardgates", "", "| gate | status | evidence |", "| --- | --- | --- |"])
    for gate_id, gate in payload["hardgate"]["gates"].items():
        lines.append(f"| `{gate_id}` | `{gate['status']}` | `{gate['evidence_pointer']}` |")
    lines.extend(["", "## Boundary", ""])
    for row in payload["not_claimed"]:
        lines.append(f"- {row}")
    lines.append("")
    return "\n".join(lines)


def build_payload(*, smoke: bool = False, generated_at: str | None = None) -> tuple[dict[str, Any], dict[str, Any]]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    started = time.perf_counter()
    seeds = SMOKE_SEEDS if smoke else SEEDS
    sample_count = SMOKE_SAMPLE_COUNT if smoke else SAMPLE_COUNT
    records = _records(seeds, ORDER_VALUES, sample_count)
    return _payload(
        records=records,
        generated_at=timestamp,
        elapsed_seconds=time.perf_counter() - started,
        smoke=smoke,
    )


def write_report(*, smoke: bool = False, generated_at: str | None = None) -> dict[str, Any]:
    payload, cmi_table = build_payload(smoke=smoke, generated_at=generated_at)
    _write_json(REPORT_JSON, payload)
    _write_text(REPORT_MD, _render_markdown(payload))
    _write_json(CMI_JSON, cmi_table)
    return payload


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--smoke", action="store_true", help="Run a small deterministic seed grid.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(()) if argv is None else parse_args(argv)
    if args.smoke:
        payload, cmi_table = build_payload(smoke=True)
        print(f"smoke records {sum(len(record['orders']) for record in payload['records'])}")
        print(f"smoke cmi rows {cmi_table['row_count']}")
        print(f"hardgate.status {payload['hardgate']['status']}")
        return
    payload = write_report(smoke=bool(args.smoke))
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"wrote {CMI_ARTIFACT}")
    print(f"hardgate.status {payload['hardgate']['status']}")


if __name__ == "__main__":
    main(sys.argv[1:])

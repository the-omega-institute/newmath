#!/usr/bin/env python3
"""Axis identity audit for the B*_Q6 structural-order cross-layer signal.

The experiment asks which one of the nine B*_Q6 coordinates carries the
translation-conditioned structural-order signal found in Route X3.  For each
coordinate q_i, it measures the 5-fold held-out R2 increment:

    translation + protein length + 20 amino-acid fractions + GC3 -> + q_i

and evaluates the increment against an exact fold-level sign-flip null.  It
also fits a full-sample standardized B*_Q6 direction after the same controls
to report which coordinate dominates the structural-order optimal direction.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import math
import pathlib
import sys
from types import ModuleType
from typing import Any


sys.dont_write_bytecode = True

EXPERIMENT_ID = "b_star_q6_structural_order_axis_identity_powered"
CLAIM_ID = "h3.cross_layer_relation.structural_order_axis_identity.b_star_q6_powered"

SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
DATA_DIR = pathlib.Path("/Users/lexa/Desktop/lexa/omega/newmath/tools/bio_reality/data")
CODON_TOPOLOGY_REFS = DATA_DIR / "codon_topology_refs.py"
X3_SIBLING = SCRIPT_DIR / "run_b_star_q6_translation_conditioned_structural_order_boundary_powered.py"

FOLD_COUNT = 5
SEED = f"sha256:{hashlib.sha256(EXPERIMENT_ID.encode('utf-8')).hexdigest()}"
EPS = 1e-12
MIN_JOINED = 300
SIGNIFICANCE_ALPHA = 0.05
MIN_PRIMARY_ORGANISMS = 2
FULL_DELTA_EPS = 0.001

EXPECTED_Q_NAMES = [
    "K_AAA",
    "Arg_AGR",
    "Ile_AUA",
    "Leu_CUN_vs_UUR",
    "Leu_UUA_vs_UUG",
    "Ser_UCR_vs_AGY",
    "Ser_UCA_vs_UCG",
    "Thr_ACR_vs_ACY",
    "f3_stress",
]

ORGANISMS = [
    {
        "organism": "saccharomyces_cerevisiae",
        "label": "Saccharomyces cerevisiae",
    },
    {
        "organism": "escherichia_coli_k12_mg1655",
        "label": "Escherichia coli K-12 MG1655",
    },
]


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def import_module_from_path(name: str, path: pathlib.Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot import {name} from {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def stable_hash_int(text: str) -> int:
    digest = hashlib.sha256(f"{SEED}|{text}".encode("utf-8")).digest()
    return int.from_bytes(digest[:8], "big")


def deterministic_folds(rows: list[dict[str, object]], organism: str, readout: str, fold_count: int = FOLD_COUNT) -> list[int]:
    order = sorted(
        range(len(rows)),
        key=lambda idx: stable_hash_int(f"fold|{organism}|{readout}|{rows[idx]['stable_id']}|{idx}"),
    )
    folds = [0 for _ in rows]
    for rank, index in enumerate(order):
        folds[index] = rank % fold_count
    return folds


def mean(values: list[float]) -> float | None:
    return None if not values else sum(values) / len(values)


def median(values: list[float]) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    mid = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[mid]
    return 0.5 * (ordered[mid - 1] + ordered[mid])


def summarize_numbers(values: list[float]) -> dict[str, object]:
    return {
        "n": len(values),
        "mean": mean(values),
        "median": median(values),
        "min": min(values) if values else None,
        "max": max(values) if values else None,
        "positive_count": sum(1 for value in values if value > 0.0),
        "negative_count": sum(1 for value in values if value < 0.0),
    }


def percentile_nearest_rank(values: list[float], probability: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def signflip_null(values: list[float]) -> dict[str, object]:
    nonzero = [abs(value) for value in values if abs(value) > EPS]
    observed_sum = sum(values)
    n = len(nonzero)
    if n == 0:
        return {
            "n_nonzero": 0,
            "observed_sum": observed_sum,
            "observed_mean": mean(values),
            "null_mean_sum": 0.0,
            "null95_sum": None,
            "null95_mean": None,
            "p_greater_zero": None,
        }
    if n > 22:
        positives = sum(1 for value in values if value > 0.0)
        p_value = sum(math.comb(n, k) for k in range(positives, n + 1)) / (2 ** n)
        return {
            "n_nonzero": n,
            "observed_sum": observed_sum,
            "observed_mean": mean(values),
            "null_mean_sum": 0.0,
            "null95_sum": None,
            "null95_mean": None,
            "p_greater_zero": p_value,
            "large_n_approximation": "binomial sign-count tail; exact magnitude enumeration skipped for n>22",
        }
    null_sums: list[float] = []
    extreme = 0
    total = 1 << n
    for mask in range(total):
        signed = 0.0
        for bit, magnitude in enumerate(nonzero):
            signed += magnitude if (mask >> bit) & 1 else -magnitude
        null_sums.append(signed)
        if signed >= observed_sum - EPS:
            extreme += 1
    null95_sum = percentile_nearest_rank(null_sums, 0.95)
    return {
        "n_nonzero": n,
        "observed_sum": observed_sum,
        "observed_mean": mean(values),
        "null_mean_sum": mean(null_sums),
        "null95_sum": null95_sum,
        "null95_mean": None if null95_sum is None else null95_sum / n,
        "p_greater_zero": extreme / total,
    }


def patch_x3_seed_and_folds(x3: ModuleType) -> None:
    x3.SEED = SEED
    x3.FOLD_COUNT = FOLD_COUNT
    x3.deterministic_folds = deterministic_folds


def load_q_vectors(
    x3: ModuleType,
    codons: list[str],
) -> tuple[dict[str, dict[str, float]], dict[str, object]]:
    refs_available = CODON_TOPOLOGY_REFS.exists()
    refs_has_q_vectors = False
    refs_error = None
    if refs_available:
        try:
            refs = import_module_from_path("codon_topology_refs_axis_identity", CODON_TOPOLOGY_REFS)
            refs_has_q_vectors = hasattr(refs, "q_vectors")
            if refs_has_q_vectors:
                raw = refs.q_vectors(codons)  # type: ignore[attr-defined]
                return raw, {
                    "requested_source": str(CODON_TOPOLOGY_REFS),
                    "used_source": "codon_topology_refs.q_vectors",
                    "codon_topology_refs_present": True,
                    "codon_topology_refs_has_q_vectors": True,
                }
        except Exception as exc:  # pragma: no cover - reported in payload
            refs_error = str(exc)
    raw = x3.q_vectors(codons)
    return raw, {
        "requested_source": str(CODON_TOPOLOGY_REFS),
        "used_source": "X3 sibling embedded q_vectors fallback",
        "fallback_source": str(X3_SIBLING),
        "codon_topology_refs_present": refs_available,
        "codon_topology_refs_has_q_vectors": refs_has_q_vectors,
        "codon_topology_refs_error": refs_error,
        "fallback_note": "local codon_topology_refs.py did not expose q_vectors in this checkout; using the Route X3 B*_Q6 coordinate definition verbatim",
    }


def axis_key(axis: str) -> str:
    return f"axis__{axis}"


def attach_axis_blocks(rows: list[dict[str, object]], q_names: list[str]) -> None:
    for row in rows:
        bstar = row.get("bstar")
        if not isinstance(bstar, list) or len(bstar) != len(q_names):
            raise ValueError("joined row lacks complete B*_Q6 vector")
        for index, name in enumerate(q_names):
            row[axis_key(name)] = [float(bstar[index])]


def delta_r2(newer: dict[str, object], older: dict[str, object]) -> float | None:
    r2_new = newer.get("held_out_r2")
    r2_old = older.get("held_out_r2")
    if isinstance(r2_new, float) and isinstance(r2_old, float):
        return r2_new - r2_old
    return None


def fold_deltas(newer: dict[str, object], older: dict[str, object]) -> list[float]:
    newer_folds = newer.get("fold_metrics")
    older_folds = older.get("fold_metrics")
    if not isinstance(newer_folds, list) or not isinstance(older_folds, list):
        return []
    out: list[float] = []
    for n_item, o_item in zip(newer_folds, older_folds):
        if not isinstance(n_item, dict) or not isinstance(o_item, dict):
            continue
        n_r2 = n_item.get("held_out_r2")
        o_r2 = o_item.get("held_out_r2")
        if isinstance(n_r2, float) and isinstance(o_r2, float):
            out.append(n_r2 - o_r2)
    return out


def evaluate_full_sample_direction(
    x3: ModuleType,
    rows: list[dict[str, object]],
    q_names: list[str],
) -> dict[str, object]:
    controls = x3.matrix_for(rows, ["translation", "composition_controls"])
    bstar = x3.matrix_for(rows, ["bstar"])
    y_raw = x3.y_for(rows)
    if not rows or not controls or not bstar:
        return {"status": "not_computed", "reason": "empty rows"}

    x_all = [controls[index] + bstar[index] for index in range(len(rows))]
    centers, scales = x3.train_standardize(x_all)
    x_std = x3.apply_standardize(x_all, centers, scales)
    y_mean = float(mean(y_raw))
    y_var = sum((value - y_mean) * (value - y_mean) for value in y_raw) / max(1, len(y_raw) - 1)
    y_sd = math.sqrt(y_var) if y_var > EPS else 1.0
    y_std = [(value - y_mean) / y_sd for value in y_raw]
    beta = x3.fit_ridge(x_std, y_std)
    control_count = len(controls[0])
    coeffs = [float(beta[1 + control_count + index]) for index in range(len(q_names))]
    coeff_norm = math.sqrt(sum(value * value for value in coeffs))
    unit = [0.0 for _ in coeffs] if coeff_norm <= EPS else [value / coeff_norm for value in coeffs]
    abs_sum = sum(abs(value) for value in unit)
    loadings = {
        name: {
            "standardized_coefficient": coeffs[index],
            "unit_loading": unit[index],
            "abs_unit_loading": abs(unit[index]),
            "abs_share": None if abs_sum <= EPS else abs(unit[index]) / abs_sum,
        }
        for index, name in enumerate(q_names)
    }
    dominant = max(q_names, key=lambda name: float(loadings[name]["abs_unit_loading"]))
    return {
        "status": "computed",
        "direction_kind": "full-sample standardized ridge coefficient direction for B*_Q6 after full controls; diagnostic, not held-out",
        "n_rows": len(rows),
        "control_feature_count": control_count,
        "coordinate_count": len(q_names),
        "coefficient_norm": coeff_norm,
        "dominant_axis_by_abs_loading": dominant,
        "loadings": loadings,
    }


def run_organism(
    *,
    x3: ModuleType,
    organism: str,
    label: str,
    code: dict[str, str],
    codons: list[str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
) -> dict[str, object]:
    rows, data_summary = x3.joined_rows(
        organism=organism,
        label=label,
        code=code,
        codons=codons,
        aa_order=aa_order,
        q_projected=q_projected,
        q_names=q_names,
    )
    attach_axis_blocks(rows, q_names)
    powered = len(rows) >= MIN_JOINED
    base = {
        "organism": organism,
        "label": label,
        "readout": "structural_order",
        "status": "computed" if powered else "needs_data",
        "powered": powered,
        "n_model_rows": len(rows),
        "data_summary": data_summary,
        "power_note": None if powered else f"交集不足 n={len(rows)} < {MIN_JOINED}；该 organism 不进入 headline aggregate。",
    }
    if not powered:
        return base

    readout = "structural_order"
    full_controls = x3.cross_validated_ridge(rows, ["translation", "composition_controls"], organism, readout)
    full_bstar = x3.cross_validated_ridge(rows, ["translation", "composition_controls", "bstar"], organism, readout)
    full_bstar_delta = delta_r2(full_bstar, full_controls)
    full_bstar_fold_deltas = fold_deltas(full_bstar, full_controls)
    per_axis: dict[str, dict[str, object]] = {}
    for name in q_names:
        model = x3.cross_validated_ridge(rows, ["translation", "composition_controls", axis_key(name)], organism, readout)
        deltas = fold_deltas(model, full_controls)
        per_axis[name] = {
            "axis": name,
            "held_out_r2_with_full_controls_plus_axis": model.get("held_out_r2"),
            "held_out_r2_full_controls": full_controls.get("held_out_r2"),
            "delta_held_out_r2": delta_r2(model, full_controls),
            "fold_delta_held_out_r2": deltas,
            "signflip_null": signflip_null(deltas),
            "feature_count_with_axis": model.get("feature_count"),
        }
    direction = evaluate_full_sample_direction(x3, rows, q_names)
    return {
        **base,
        "metrics": {
            "translation_plus_length_aa_gc_controls": full_controls,
            "translation_plus_length_aa_gc_controls_plus_bstar_q6": full_bstar,
        },
        "full_bstar_q6_increment": {
            "delta_held_out_r2": full_bstar_delta,
            "fold_delta_held_out_r2": full_bstar_fold_deltas,
            "signflip_null": signflip_null(full_bstar_fold_deltas),
        },
        "per_axis": per_axis,
        "optimal_direction_loadings": direction,
    }


def aggregate_axes(results: list[dict[str, object]], q_names: list[str]) -> dict[str, dict[str, object]]:
    out: dict[str, dict[str, object]] = {}
    total_rows = sum(int(result["n_model_rows"]) for result in results)
    for name in q_names:
        organism_deltas: list[float] = []
        fold_delta_values: list[float] = []
        weighted_numer = 0.0
        positive_organisms = 0
        per_organism: dict[str, object] = {}
        for result in results:
            organism = str(result["organism"])
            axis_result = result["per_axis"][name]
            delta = axis_result.get("delta_held_out_r2")
            if isinstance(delta, float):
                organism_deltas.append(delta)
                weighted_numer += int(result["n_model_rows"]) * delta
                if delta > 0.0:
                    positive_organisms += 1
            folds = [
                float(value)
                for value in axis_result.get("fold_delta_held_out_r2", [])
                if isinstance(value, (int, float))
            ]
            fold_delta_values.extend(folds)
            per_organism[organism] = {
                "n_model_rows": result["n_model_rows"],
                "delta_held_out_r2": delta,
                "signflip_null": axis_result.get("signflip_null"),
            }
        null = signflip_null(fold_delta_values)
        p_value = null.get("p_greater_zero")
        weighted = None if total_rows <= 0 else weighted_numer / total_rows
        significant = (
            isinstance(weighted, float)
            and weighted > 0.0
            and isinstance(p_value, float)
            and p_value <= SIGNIFICANCE_ALPHA
        )
        out[name] = {
            "axis": name,
            "weighted_delta_held_out_r2": weighted,
            "organism_delta_summary": summarize_numbers(organism_deltas),
            "fold_delta_summary": summarize_numbers(fold_delta_values),
            "signflip_null": null,
            "positive_primary_organism_count": positive_organisms,
            "significant_against_signflip_null": significant,
            "per_organism": per_organism,
        }
    return out


def aggregate_full_bstar(results: list[dict[str, object]]) -> dict[str, object]:
    total_rows = sum(int(result["n_model_rows"]) for result in results)
    weighted_numer = 0.0
    deltas: list[float] = []
    fold_delta_values: list[float] = []
    positive_organisms = 0
    per_organism: dict[str, object] = {}
    for result in results:
        inc = result["full_bstar_q6_increment"]
        delta = inc.get("delta_held_out_r2")
        if isinstance(delta, float):
            deltas.append(delta)
            weighted_numer += int(result["n_model_rows"]) * delta
            if delta > 0.0:
                positive_organisms += 1
        folds = [float(value) for value in inc.get("fold_delta_held_out_r2", []) if isinstance(value, (int, float))]
        fold_delta_values.extend(folds)
        per_organism[str(result["organism"])] = {
            "n_model_rows": result["n_model_rows"],
            "delta_held_out_r2": delta,
            "signflip_null": inc.get("signflip_null"),
        }
    null = signflip_null(fold_delta_values)
    p_value = null.get("p_greater_zero")
    weighted = None if total_rows <= 0 else weighted_numer / total_rows
    significant = (
        len(results) >= MIN_PRIMARY_ORGANISMS
        and positive_organisms >= MIN_PRIMARY_ORGANISMS
        and isinstance(weighted, float)
        and weighted >= FULL_DELTA_EPS
        and isinstance(p_value, float)
        and p_value <= SIGNIFICANCE_ALPHA
    )
    return {
        "weighted_delta_held_out_r2": weighted,
        "organism_delta_summary": summarize_numbers(deltas),
        "fold_delta_summary": summarize_numbers(fold_delta_values),
        "signflip_null": null,
        "positive_primary_organism_count": positive_organisms,
        "significant_against_signflip_null": significant,
        "per_organism": per_organism,
    }


def aggregate_loadings(results: list[dict[str, object]], q_names: list[str]) -> dict[str, object]:
    total_rows = sum(int(result["n_model_rows"]) for result in results)
    by_axis: dict[str, dict[str, object]] = {}
    for name in q_names:
        signed_numer = 0.0
        abs_numer = 0.0
        share_numer = 0.0
        values: list[float] = []
        for result in results:
            loadings = result["optimal_direction_loadings"].get("loadings")
            if not isinstance(loadings, dict):
                continue
            item = loadings.get(name)
            if not isinstance(item, dict):
                continue
            n_rows = int(result["n_model_rows"])
            unit = item.get("unit_loading")
            abs_unit = item.get("abs_unit_loading")
            share = item.get("abs_share")
            if isinstance(unit, float):
                signed_numer += n_rows * unit
                values.append(unit)
            if isinstance(abs_unit, float):
                abs_numer += n_rows * abs_unit
            if isinstance(share, float):
                share_numer += n_rows * share
        by_axis[name] = {
            "weighted_signed_unit_loading": None if total_rows <= 0 else signed_numer / total_rows,
            "weighted_abs_unit_loading": None if total_rows <= 0 else abs_numer / total_rows,
            "weighted_abs_share": None if total_rows <= 0 else share_numer / total_rows,
            "organism_unit_loading_summary": summarize_numbers(values),
        }
    dominant = max(q_names, key=lambda axis: float(by_axis[axis]["weighted_abs_unit_loading"] or 0.0))
    return {
        "direction_kind": "row-weighted aggregate of per-organism full-sample standardized B*_Q6 coefficient directions",
        "dominant_axis_by_weighted_abs_loading": dominant,
        "by_axis": by_axis,
        "per_organism_dominant_axis": {
            str(result["organism"]): result["optimal_direction_loadings"].get("dominant_axis_by_abs_loading")
            for result in results
        },
    }


def rank_axes(aggregate: dict[str, dict[str, object]]) -> list[dict[str, object]]:
    ranked = sorted(
        aggregate.values(),
        key=lambda item: float(item["weighted_delta_held_out_r2"] or -1e99),
        reverse=True,
    )
    return [
        {
            "rank": index + 1,
            "axis": item["axis"],
            "weighted_delta_held_out_r2": item["weighted_delta_held_out_r2"],
            "signflip_p_greater_zero": item["signflip_null"].get("p_greater_zero"),
            "significant_against_signflip_null": item["significant_against_signflip_null"],
            "positive_primary_organism_count": item["positive_primary_organism_count"],
        }
        for index, item in enumerate(ranked)
    ]


def conclusion_from_results(
    *,
    axis_aggregate: dict[str, dict[str, object]],
    loading_aggregate: dict[str, object],
    full_bstar_aggregate: dict[str, object],
) -> dict[str, object]:
    ranked = rank_axes(axis_aggregate)
    significant_axes = [
        item["axis"]
        for item in ranked
        if item["significant_against_signflip_null"] is True
    ]
    top_axis = str(ranked[0]["axis"])
    top_delta = ranked[0]["weighted_delta_held_out_r2"]
    second_delta = ranked[1]["weighted_delta_held_out_r2"] if len(ranked) > 1 else None
    loading_axis = str(loading_aggregate["dominant_axis_by_weighted_abs_loading"])
    full_signal = full_bstar_aggregate.get("significant_against_signflip_null") is True

    if not significant_axes:
        carried = "structural_order_carried_by_distributed_multi_axis" if full_signal else "structural_order_carried_by_no_single_axis"
        reason = "no single B*_Q6 coordinate passed the fold-level sign-flip gate"
    elif len(significant_axes) == 1:
        carried = f"structural_order_carried_by_{significant_axes[0]}"
        reason = "exactly one coordinate passed the fold-level sign-flip gate"
    else:
        top_is_separated = False
        if isinstance(top_delta, float) and isinstance(second_delta, float):
            top_is_separated = (top_delta - second_delta) >= max(0.0005, 0.25 * max(abs(second_delta), EPS))
        if top_is_separated and top_axis == loading_axis:
            carried = f"structural_order_carried_by_{top_axis}"
            reason = "multiple coordinates were positive, but the top increment axis also dominated the optimal-direction loading"
        else:
            carried = "structural_order_carried_by_distributed_multi_axis"
            reason = "more than one coordinate passed or the increment and loading diagnostics did not isolate the same axis"

    f3_rank = next(item["rank"] for item in ranked if item["axis"] == "f3_stress")
    f3_item = axis_aggregate["f3_stress"]
    f3_loading = loading_aggregate["by_axis"]["f3_stress"]
    return {
        "conclusion": carried,
        "dominant_increment_axis": top_axis,
        "dominant_loading_axis": loading_axis,
        "significant_axes": significant_axes,
        "full_bstar_q6_signal_significant": full_signal,
        "reason": reason,
        "f3_stress_assessment": {
            "rank_by_weighted_delta": f3_rank,
            "weighted_delta_held_out_r2": f3_item["weighted_delta_held_out_r2"],
            "signflip_p_greater_zero": f3_item["signflip_null"].get("p_greater_zero"),
            "significant_against_signflip_null": f3_item["significant_against_signflip_null"],
            "weighted_abs_unit_loading": f3_loading.get("weighted_abs_unit_loading"),
            "is_dominant_increment_axis": top_axis == "f3_stress",
            "is_dominant_loading_axis": loading_axis == "f3_stress",
        },
    }


def compact_per_organism(results: dict[str, dict[str, object]], q_names: list[str]) -> dict[str, object]:
    compact: dict[str, object] = {}
    for organism, result in results.items():
        item: dict[str, object] = {
            "status": result.get("status"),
            "powered": result.get("powered"),
            "n_model_rows": result.get("n_model_rows"),
            "power_note": result.get("power_note"),
        }
        if result.get("powered") is True:
            full = result.get("full_bstar_q6_increment")
            item["full_bstar_q6_increment"] = full
            per_axis = result.get("per_axis")
            if isinstance(per_axis, dict):
                item["per_axis"] = {
                    axis: {
                        "delta_held_out_r2": per_axis[axis].get("delta_held_out_r2"),
                        "signflip_null": per_axis[axis].get("signflip_null"),
                    }
                    for axis in q_names
                    if axis in per_axis and isinstance(per_axis[axis], dict)
                }
            direction = result.get("optimal_direction_loadings")
            if isinstance(direction, dict):
                loadings = direction.get("loadings")
                item["optimal_direction_loadings"] = {
                    "dominant_axis_by_abs_loading": direction.get("dominant_axis_by_abs_loading"),
                    "coefficient_norm": direction.get("coefficient_norm"),
                    "loadings": {
                        axis: {
                            "unit_loading": loadings[axis].get("unit_loading"),
                            "abs_share": loadings[axis].get("abs_share"),
                        }
                        for axis in q_names
                        if isinstance(loadings, dict) and axis in loadings and isinstance(loadings[axis], dict)
                    },
                }
        compact[organism] = item
    return compact


def compact_axis_aggregate(axis_aggregate: dict[str, dict[str, object]], q_names: list[str]) -> dict[str, object]:
    return {
        axis: {
            "weighted_delta_held_out_r2": axis_aggregate[axis].get("weighted_delta_held_out_r2"),
            "organism_delta_summary": axis_aggregate[axis].get("organism_delta_summary"),
            "fold_delta_summary": axis_aggregate[axis].get("fold_delta_summary"),
            "signflip_null": axis_aggregate[axis].get("signflip_null"),
            "positive_primary_organism_count": axis_aggregate[axis].get("positive_primary_organism_count"),
            "significant_against_signflip_null": axis_aggregate[axis].get("significant_against_signflip_null"),
        }
        for axis in q_names
    }


def compact_loading_aggregate(loading_aggregate: dict[str, object], q_names: list[str]) -> dict[str, object]:
    by_axis = loading_aggregate.get("by_axis")
    return {
        "direction_kind": loading_aggregate.get("direction_kind"),
        "dominant_axis_by_weighted_abs_loading": loading_aggregate.get("dominant_axis_by_weighted_abs_loading"),
        "per_organism_dominant_axis": loading_aggregate.get("per_organism_dominant_axis"),
        "by_axis": {
            axis: {
                "weighted_abs_unit_loading": by_axis[axis].get("weighted_abs_unit_loading"),
                "weighted_abs_share": by_axis[axis].get("weighted_abs_share"),
            }
            for axis in q_names
            if isinstance(by_axis, dict) and axis in by_axis and isinstance(by_axis[axis], dict)
        },
    }


def cannot_claim() -> list[str]:
    return [
        "这是横截面 held-out 预测与坐标归因实验，不是共翻译折叠或延伸速度的因果证明。",
        "structural_order 是本地 AlphaFold mean-pLDDT 派生 proxy；不是实验结构、有序度、功能或适应度测量。",
        "每坐标增量只检验单个 B*_Q6 坐标在 translation + length + AA composition + GC3 后的额外 held-out R2；相关坐标可导致信号分散。",
        "sign-flip null 是 fold-level 确定性符号翻转诊断；两个物种、十个 folds 的跨物种 power 有限。",
        "optimal-direction loadings 是全样本标准化岭回归系数方向诊断，不是 held-out 选择结果；它用于解释主导坐标，不单独决定显著性。",
        "若 f3_stress 非主导或信号分散，应解释为本数据和此模型下未支持单一 5'-ramp/f3 轴承载，不等于排除共翻译折叠机制。",
    ]


def main() -> None:
    required = [DATA_DIR / "ncbi_genetic_codes.json", X3_SIBLING]
    for item in ORGANISMS:
        organism = str(item["organism"])
        required.extend(
            [
                DATA_DIR / f"cds_codon_abundance_{organism}.json",
                DATA_DIR / f"ribosome_te_{organism}.json",
                DATA_DIR / f"structural_order_{organism}.json",
            ]
        )
    missing = [str(path) for path in required if not path.exists()]
    if missing:
        emit("needs_data", reason="required local sibling/data files not present", missing_required_data=missing)

    try:
        x3 = import_module_from_path("route_x3_structural_order_boundary", X3_SIBLING)
        patch_x3_seed_and_folds(x3)

        code = x3.standard_code()
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = x3.fibers_for(code, codons)
        aa_order = x3.standard_amino_acids(code, codons)
        raw_q, q_source = load_q_vectors(x3, codons)
        q_projected = {name: x3.project_syn(vector, fibers) for name, vector in raw_q.items()}
        q_names = list(q_projected)
        if q_names != EXPECTED_Q_NAMES:
            raise ValueError(f"B*_Q6 coordinate order drifted: {q_names}")

        all_results: dict[str, dict[str, object]] = {}
        primary_results: list[dict[str, object]] = []
        for item in ORGANISMS:
            organism = str(item["organism"])
            result = run_organism(
                x3=x3,
                organism=organism,
                label=str(item["label"]),
                code=code,
                codons=codons,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
            )
            if result.get("powered") is True:
                primary_results.append(result)
            all_results[organism] = result

        if len(primary_results) < MIN_PRIMARY_ORGANISMS:
            emit(
                "needs_data",
                reason=f"primary structural-order/CDS/translation overlap powered organisms < {MIN_PRIMARY_ORGANISMS}",
                per_organism={
                    organism: {
                        "status": result.get("status"),
                        "n_model_rows": result.get("n_model_rows"),
                        "power_note": result.get("power_note"),
                    }
                    for organism, result in all_results.items()
                },
                checks=[
                    {"name": "axes_computed", "passed": False},
                    {"name": "structural_order_axis_increment", "passed": False},
                    {"name": "dominant_axis_identified", "passed": False},
                ],
            )

        axis_aggregate = aggregate_axes(primary_results, q_names)
        full_bstar_aggregate = aggregate_full_bstar(primary_results)
        loading_aggregate = aggregate_loadings(primary_results, q_names)
        conclusion = conclusion_from_results(
            axis_aggregate=axis_aggregate,
            loading_aggregate=loading_aggregate,
            full_bstar_aggregate=full_bstar_aggregate,
        )
        ranked_axes = rank_axes(axis_aggregate)

        axes_ok = q_names == EXPECTED_Q_NAMES and all(
            axis in axis_aggregate and axis in primary_results[0]["per_axis"]
            for axis in EXPECTED_Q_NAMES
        )
        increments_ok = all(
            isinstance(axis_aggregate[axis].get("weighted_delta_held_out_r2"), float)
            and isinstance(axis_aggregate[axis].get("signflip_null"), dict)
            for axis in EXPECTED_Q_NAMES
        )
        dominant_ok = (
            isinstance(conclusion.get("conclusion"), str)
            and str(conclusion["conclusion"]).startswith("structural_order_carried_by_")
            and conclusion.get("dominant_increment_axis") in EXPECTED_Q_NAMES
            and conclusion.get("dominant_loading_axis") in EXPECTED_Q_NAMES
        )
        checks = [
            {
                "name": "axes_computed",
                "passed": axes_ok,
                "expected": "all 9 B*_Q6 coordinates computed, including f3_stress",
                "actual": q_names,
            },
            {
                "name": "structural_order_axis_increment",
                "passed": increments_ok,
                "expected": "each coordinate has full-control held-out R2 increment and fold-level sign-flip null",
                "actual": {
                    axis: {
                        "weighted_delta_held_out_r2": axis_aggregate[axis]["weighted_delta_held_out_r2"],
                        "signflip_p_greater_zero": axis_aggregate[axis]["signflip_null"].get("p_greater_zero"),
                    }
                    for axis in EXPECTED_Q_NAMES
                },
            },
            {
                "name": "dominant_axis_identified",
                "passed": dominant_ok,
                "expected": "conclusion starts with structural_order_carried_by_ and dominant increment/loading axes are named",
                "actual": conclusion,
            },
        ]

        emit(
            "passed" if all(check["passed"] for check in checks) else "failed",
            conclusion=conclusion["conclusion"],
            verdict=conclusion,
            seed=SEED,
            fold_count=FOLD_COUNT,
            min_joined=MIN_JOINED,
            q_vector_source=q_source,
            controls={
                "translation": ["log10 protein abundance ppm", "log10 measured TE", "log10 measured mRNA", "log10 ribosome footprint"],
                "full_control_addons": ["natural log CDS length nt", "20 amino-acid composition fractions in sorted one-letter AA order", "GC3 fraction"],
                "aa_order": aa_order,
                "bstar_q6_coordinates": q_names,
            },
            readout_policy={
                "configured_organisms": ORGANISMS,
                "headline_aggregate_unit": "one structural_order readout per organism",
                "readout": "structural_order from structural_order_<organism>.json",
                "readout_transform": "raw structural_order on 0..100; no log/logit transform",
                "readout_boundary": "AlphaFold mean-pLDDT derived structural-order proxy, not experimental phenotype",
            },
            full_bstar_q6_aggregate=full_bstar_aggregate,
            per_axis_aggregate=compact_axis_aggregate(axis_aggregate, q_names),
            axis_rank_by_weighted_delta=ranked_axes,
            optimal_direction_loading_aggregate=compact_loading_aggregate(loading_aggregate, q_names),
            per_organism=compact_per_organism(all_results, q_names),
            checks=checks,
            null={
                "axis_null": "exact one-sided fold-level sign-flip null over full-control axis delta R2 values pooled across primary organisms",
                "axis_significance_gate": {
                    "requires_weighted_axis_delta_gt_zero": True,
                    "requires_signflip_p_lte": SIGNIFICANCE_ALPHA,
                },
                "full_bstar_signal_gate": {
                    "requires_primary_organisms_at_least": MIN_PRIMARY_ORGANISMS,
                    "requires_positive_primary_organism_count_at_least": MIN_PRIMARY_ORGANISMS,
                    "requires_weighted_full_bstar_delta_r2_at_least": FULL_DELTA_EPS,
                    "requires_signflip_p_lte": SIGNIFICANCE_ALPHA,
                },
            },
            cannot_claim=cannot_claim(),
        )
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable axis-identity input or fit")


if __name__ == "__main__":
    main()

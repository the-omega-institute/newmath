#!/usr/bin/env python3
"""Partial-mediation certificate for B*_Q6 readout-dictionary coverage."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import run_b_star_q6_context_lift_powered as context_lift
import run_b_star_q6_irreducibility_certificate_powered as routea
import run_b_star_q6_minimal_dictionary_compression_powered as compression
import run_b_star_q6_residual_dictionary_consistency_powered as residual_dictionary
from run_b_star_q6_translation_complement_residual_powered import vector_norm2
from run_b_star_q6_translation_mediation_powered import vector_dot


EXPERIMENT_ID = "b_star_q6_partial_mediation_certificate_powered"
CLAIM_ID = "h3.cross_layer_relation.partial_mediation.b_star_q6_readout_dictionary_powered"

ORGANISM = "saccharomyces_cerevisiae"
PERMUTATION_COUNT = 120
FOLD_COUNT = 5
SEED = "sha256:b_star_q6_partial_mediation_certificate_powered:deterministic"
LAMBDA_DL = residual_dictionary.LAMBDA_DL
RHO_JOIN = residual_dictionary.RHO_JOIN
EPS = 1e-12


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def stable_digest(material: str) -> bytes:
    return hashlib.sha256(material.encode("utf-8")).digest()


def deterministic_permutation(n: int, material_prefix: str) -> list[int]:
    out = list(range(n))
    for index in range(n - 1, 0, -1):
        digest = stable_digest(f"{material_prefix}|index={index}|n={n}")
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap_index] = out[swap_index], out[index]
    return out


def bounded_unit(value: float, tol: float = 1e-8) -> float:
    if -tol <= value < 0.0:
        return 0.0
    if 1.0 < value <= 1.0 + tol:
        return 1.0
    return value


def cv_r2_for_target(*, target: list[float], models: list[dict[str, object]]) -> float:
    total_ss = 0.0
    sse = 0.0
    for model in models:
        test_indices = model["test_indices"]
        if not isinstance(test_indices, list):
            raise ValueError("cv model malformed")
        predictions = context_lift.predict_cv(model, target)
        for local_index, row_index in enumerate(test_indices):
            observed = target[int(row_index)]
            residual = observed - predictions[local_index]
            total_ss += observed * observed
            sse += residual * residual
    if total_ss <= EPS:
        return 0.0
    return 1.0 - sse / total_ss


def prepare_models(design: list[list[float]], n: int) -> list[dict[str, object]]:
    fold_indices = context_lift.folds_for_n(n, FOLD_COUNT)
    models = []
    for test in fold_indices:
        test_set = set(test)
        train = [index for index in range(n) if index not in test_set]
        models.append(context_lift.prepare_cv_model(design, train, test))
    return models


def source_is_real_check(join: dict[str, object]) -> dict[str, object]:
    x_e = join["x_e"]
    target = join["target"]
    if not isinstance(x_e, list) or not isinstance(target, list):
        raise ValueError("source input malformed")
    models = prepare_models(x_e, len(target))
    held_out_r2 = cv_r2_for_target(target=target, models=models)
    null_values: list[float] = []
    for trial in range(PERMUTATION_COUNT):
        permutation = deterministic_permutation(len(target), f"{SEED}|source-target-permutation|trial={trial}")
        permuted_target = [target[permutation[index]] for index in range(len(target))]
        null_values.append(cv_r2_for_target(target=permuted_target, models=models))
    null95 = percentile_nearest_rank(null_values, 0.95)
    return {
        "name": "source_is_real",
        "passed": held_out_r2 > null95,
        "held_out_r2": held_out_r2,
        "null95_r2": null95,
        "null_mean_r2": mean(null_values),
        "target_norm2": vector_norm2(target),
        "n_join": len(target),
        "n_features": len(x_e[0]) if x_e else 0,
        "fold_count": FOLD_COUNT,
        "permutation_count": PERMUTATION_COUNT,
        "seed": SEED,
        "null_model": "deterministic permutation of gene-to-Z-residualized protein-abundance labels with fixed B*_Q6 design and folds",
    }


def public_subset(item: dict[str, object]) -> dict[str, object]:
    return {
        key: value
        for key, value in item.items()
        if key not in {"state", "row_ids"}
    }


def candidate_key(subset: tuple[str, ...]) -> str:
    return ",".join(subset) if subset else "<empty>"


def absorption_for_permuted_target(basis: list[list[float]], target: list[float], permutation: list[int]) -> float:
    target_norm = vector_norm2(target)
    if target_norm <= EPS or not basis:
        return 0.0
    energy = 0.0
    for q in basis:
        dot = 0.0
        for index, target_index in enumerate(permutation):
            dot += target[target_index] * q[index]
        energy += dot * dot
    if energy > target_norm and energy <= target_norm + 1e-8:
        energy = target_norm
    return bounded_unit(max(0.0, energy) / target_norm)


def naive_fixed_subset_null(
    *,
    subset: tuple[str, ...],
    basis: list[list[float]],
    target: list[float],
) -> dict[str, object]:
    if not subset or not basis:
        return {
            "permutation_count": 0,
            "null95_coverage": 0.0,
            "null_mean_coverage": 0.0,
            "null_model": "empty dictionary has zero fixed-subset null coverage",
        }
    values: list[float] = []
    label = candidate_key(subset)
    for trial in range(PERMUTATION_COUNT):
        permutation = deterministic_permutation(len(target), f"{SEED}|naive-fixed-subset|subset={label}|trial={trial}")
        values.append(absorption_for_permuted_target(basis, target, permutation))
    return {
        "permutation_count": PERMUTATION_COUNT,
        "null95_coverage": percentile_nearest_rank(values, 0.95),
        "null_mean_coverage": mean(values),
        "deterministic_seed": f"{SEED}|naive-fixed-subset|subset|trial|index|n",
        "null_model": "naive fixed-subset deterministic row-label permutation of the selected readout subspace target; selection over candidate subsets is not replayed",
    }


def add_naive_null_and_score(item: dict[str, object], null: dict[str, object], rows: dict[str, dict[str, object]]) -> dict[str, object]:
    subset = tuple(str(readout) for readout in item.get("D_o", []))
    coverage = float(item["coverage"])
    null95 = float(null["null95_coverage"])
    dl = sum(compression.readout_dimensions(rows, readout) for readout in subset)
    base_n = int(item["base_n"])
    n_join = int(item["n_join"])
    join_shift = abs(n_join - base_n) / base_n if base_n else 1.0
    cost, cost_parts = compression.scaled_cost(dl, join_shift, null95)
    out = dict(item)
    out["null"] = null
    out["DL"] = dl
    out["join_shift"] = join_shift
    out["cost"] = cost
    out["cost_parts"] = cost_parts
    out["BEDC_score"] = coverage - LAMBDA_DL * cost
    out["coverage_above_null95"] = coverage > null95
    out["matched_null_computed"] = True
    return out


def selection_aware_null(candidate_items: list[dict[str, object]]) -> dict[str, object]:
    values: list[float] = []
    selected_subsets: list[list[str]] = []
    for trial in range(PERMUTATION_COUNT):
        best_coverage = -1.0
        best_subset: list[str] = []
        for item in candidate_items:
            state = item.get("state")
            if not isinstance(state, dict):
                raise ValueError("candidate state malformed")
            target = state.get("P_Q")
            basis = state.get("design_basis")
            subset = tuple(str(readout) for readout in item.get("D_o", []))
            if not isinstance(target, list) or not isinstance(basis, list):
                raise ValueError("candidate target/basis malformed")
            if not subset or not basis:
                coverage = 0.0
            else:
                permutation = deterministic_permutation(
                    len(target),
                    f"{SEED}|selection-aware-target-permutation|trial={trial}",
                )
                coverage = absorption_for_permuted_target(basis, target, permutation)
            if coverage > best_coverage:
                best_coverage = coverage
                best_subset = list(subset)
        values.append(max(0.0, best_coverage))
        selected_subsets.append(best_subset)
    top_selected: dict[str, int] = {}
    for subset in selected_subsets:
        key = candidate_key(tuple(subset))
        top_selected[key] = top_selected.get(key, 0) + 1
    return {
        "permutation_count": PERMUTATION_COUNT,
        "null95_coverage": percentile_nearest_rank(values, 0.95),
        "null_mean_coverage": mean(values),
        "null_max_coverage": max(values) if values else 0.0,
        "selected_subset_counts_top10": [
            {"D_o": [] if key == "<empty>" else key.split(","), "count": count}
            for key, count in sorted(top_selected.items(), key=lambda pair: (-pair[1], pair[0]))[:10]
        ],
        "deterministic_seed": f"{SEED}|selection-aware-target-permutation|trial|index|n",
        "null_model": "selection-aware null: each trial permutes target rows and redoes best-coverage selection over the same candidate subset family",
    }


def dictionary_captures_selection_aware_check(join: dict[str, object]) -> dict[str, object]:
    rows = join["rows"]
    selected_ids = join["selected_ids"]
    yeast_config = join["yeast_config"]
    if not isinstance(rows, dict) or not isinstance(selected_ids, list) or not isinstance(yeast_config, dict):
        raise ValueError("dictionary input malformed")

    base_ids = [str(item) for item in selected_ids]
    readouts = compression.available_readouts(yeast_config, rows, base_ids)  # type: ignore[arg-type]
    join_cache: dict[tuple[str, ...], dict[str, object]] = {}
    readout_cache: dict[tuple[tuple[str, ...], str], list[list[float]]] = {}
    preliminary = [
        compression.evaluate_subset_cached(
            organism=ORGANISM,
            rows=rows,  # type: ignore[arg-type]
            base_ids=base_ids,
            subset=subset,
            compute_null=False,
            join_cache=join_cache,
            readout_cache=readout_cache,
        )
        for subset in compression.all_subsets(readouts)
    ]
    candidate_subsets = compression.frontier_subsets(preliminary)
    candidate_items = [
        compression.evaluate_subset_cached(
            organism=ORGANISM,
            rows=rows,  # type: ignore[arg-type]
            base_ids=base_ids,
            subset=subset,
            compute_null=False,
            join_cache=join_cache,
            readout_cache=readout_cache,
        )
        for subset in candidate_subsets
    ]
    computed = [item for item in candidate_items if item.get("status") == "computed"]
    if not computed:
        return {
            "name": "dictionary_captures_selection_aware",
            "status": "needs_data",
            "passed": False,
            "reason": "no readout subset passed the join gate",
            "available_readouts": readouts,
            "preliminary_subset_count": len(preliminary),
            "candidate_subset_count": len(candidate_subsets),
            "base_n": len(base_ids),
        }

    raw_best = max(computed, key=lambda item: float(item["coverage"]))
    with_null: list[dict[str, object]] = []
    for item in computed:
        state = item.get("state")
        if not isinstance(state, dict):
            raise ValueError("candidate state malformed")
        target = state.get("P_Q")
        basis = state.get("design_basis")
        if not isinstance(target, list) or not isinstance(basis, list):
            raise ValueError("candidate target/basis malformed")
        subset = tuple(str(readout) for readout in item.get("D_o", []))
        null = naive_fixed_subset_null(subset=subset, basis=basis, target=target)
        with_null.append(add_naive_null_and_score(item, null, rows))  # type: ignore[arg-type]

    d_o_star = max(with_null, key=lambda item: float(item["BEDC_score"]))
    d_state = d_o_star.get("state")
    if not isinstance(d_state, dict):
        raise ValueError("selected dictionary state malformed")
    selection_null = selection_aware_null(computed)
    selection_null95 = float(selection_null["null95_coverage"])
    d_coverage = float(d_o_star["coverage"])
    raw_best_coverage = float(raw_best["coverage"])
    top_scoring = sorted(
        (
            {
                "D_o": item.get("D_o"),
                "n_dict": len(item.get("D_o", [])) if isinstance(item.get("D_o"), list) else None,
                "n_join": item.get("n_join"),
                "coverage": item.get("coverage"),
                "unexplained": item.get("unexplained"),
                "naive_fixed_subset_null95": item.get("null", {}).get("null95_coverage") if isinstance(item.get("null"), dict) else None,
                "BEDC_score": item.get("BEDC_score"),
                "coverage_above_naive_null95": item.get("coverage_above_null95"),
            }
            for item in with_null
        ),
        key=lambda item: float(item["BEDC_score"]) if item["BEDC_score"] is not None else -1e100,
        reverse=True,
    )[:10]
    top_coverage = sorted(
        (
            {
                "D_o": item.get("D_o"),
                "n_dict": len(item.get("D_o", [])) if isinstance(item.get("D_o"), list) else None,
                "n_join": item.get("n_join"),
                "coverage": item.get("coverage"),
                "unexplained": item.get("unexplained"),
            }
            for item in computed
        ),
        key=lambda item: float(item["coverage"]) if item["coverage"] is not None else -1e100,
        reverse=True,
    )[:10]
    naive_null = d_o_star["null"]
    if not isinstance(naive_null, dict):
        raise ValueError("naive null malformed")
    passed = d_coverage > selection_null95
    return {
        "name": "dictionary_captures_selection_aware",
        "status": "computed",
        "passed": passed,
        "D_o_star": d_o_star["D_o"],
        "n_dict": len(d_o_star["D_o"]) if isinstance(d_o_star.get("D_o"), list) else None,
        "coverage_C_star": d_coverage,
        "selection_aware_null95": selection_null95,
        "selection_aware_null_mean": selection_null["null_mean_coverage"],
        "selection_aware_null_max": selection_null["null_max_coverage"],
        "coverage_above_selection_aware_null95": passed,
        "naive_fixed_subset_null95": naive_null["null95_coverage"],
        "naive_fixed_subset_null_mean": naive_null["null_mean_coverage"],
        "selection_bias_lift_null95": selection_null95 - float(naive_null["null95_coverage"]),
        "unexplained": d_o_star["unexplained"],
        "BEDC_score": d_o_star["BEDC_score"],
        "DL": d_o_star["DL"],
        "join_shift": d_o_star["join_shift"],
        "rank_D_e": d_o_star["rank_D_e"],
        "rank_Q_e": d_o_star["rank_Q_e"],
        "n_join": d_o_star["n_join"],
        "base_n": len(base_ids),
        "raw_best_coverage_over_candidate_family": raw_best_coverage,
        "raw_best_coverage_D_o": raw_best["D_o"],
        "raw_best_coverage_n_dict": len(raw_best["D_o"]) if isinstance(raw_best.get("D_o"), list) else None,
        "raw_best_coverage_unexplained": raw_best["unexplained"],
        "raw_best_coverage_above_selection_aware_null95": raw_best_coverage > selection_null95,
        "available_readouts": readouts,
        "preliminary_subset_count": len(preliminary),
        "candidate_subset_count": len(candidate_subsets),
        "candidate_subset_selection": "sibling compression frontier: empty/single/double subsets plus each cardinality frontier and top preliminary exact-coverage candidates",
        "permutation_count": PERMUTATION_COUNT,
        "lambda_dl": LAMBDA_DL,
        "rho_join": RHO_JOIN,
        "seed": SEED,
        "coverage_metric": "sibling orthogonal projection coverage of P_Q by the Z-residualized readout dictionary on the active join",
        "selection_aware_null": selection_null,
        "naive_fixed_subset_null": naive_null,
        "top_scoring_subsets": top_scoring,
        "top_coverage_subsets": top_coverage,
        "best_public": public_subset(d_o_star),
    }


def minimal_bound_check(dictionary_check: dict[str, object]) -> dict[str, object]:
    d_o = dictionary_check.get("D_o_star")
    n_dict = len(d_o) if isinstance(d_o, list) else None
    return {
        "name": "minimal_bound",
        "passed": isinstance(n_dict, int) and n_dict <= 3,
        "D_o_star": d_o,
        "n_dict": n_dict,
        "bound": 3,
        "selection_rule": "D_o_star is selected by the sibling minimal-dictionary BEDC score after fixed-subset null penalties; selection-aware significance is checked separately",
    }


def main() -> None:
    repo = pathlib.Path.cwd()
    join = routea.build_unified_yeast_join(repo)
    if join.get("status") != "computed":
        emit(
            "needs_data",
            reason=join.get("reason", "unified yeast join unavailable"),
            checks=[],
            **{key: value for key, value in join.items() if key not in {"status", "reason"}},
        )

    source_check = source_is_real_check(join)
    dictionary_check = dictionary_captures_selection_aware_check(join)
    if dictionary_check.get("status") == "needs_data":
        emit(
            "needs_data",
            reason="readout-dictionary candidate family could not be evaluated on the unified yeast join",
            checks=[source_check, dictionary_check],
            organism="Saccharomyces cerevisiae",
            organism_key=ORGANISM,
            n_join=len(join["selected_ids"]),  # type: ignore[arg-type]
            base_n=len(join["base_ids"]),  # type: ignore[arg-type]
            permutation_count=PERMUTATION_COUNT,
            fold_count=FOLD_COUNT,
            seed=SEED,
        )
    minimal_check = minimal_bound_check(dictionary_check)
    partial_passed = bool(source_check["passed"]) and bool(dictionary_check["passed"]) and bool(minimal_check["passed"])
    partial_check = {
        "name": "partial_mediation_certified",
        "passed": partial_passed,
        "source_is_real": bool(source_check["passed"]),
        "dictionary_captures_selection_aware": bool(dictionary_check["passed"]),
        "minimal_bound": bool(minimal_check["passed"]),
        "rule": "passed iff source_is_real AND dictionary_captures_selection_aware AND minimal_bound",
    }
    checks = [source_check, dictionary_check, minimal_check, partial_check]
    failed_checks = [str(check["name"]) for check in checks if not check.get("passed")]
    status = "passed" if partial_passed else "failed"
    d_o = dictionary_check.get("D_o_star")
    coverage = dictionary_check.get("coverage_C_star")
    unexplained = 1.0 - float(coverage) if isinstance(coverage, (int, float)) and not isinstance(coverage, bool) else None
    emit(
        status,
        reason=None if status == "passed" else "one or more partial-mediation certificate subconditions failed",
        failed_checks=failed_checks,
        organism="Saccharomyces cerevisiae",
        organism_key=ORGANISM,
        n_join=len(join["selected_ids"]),  # type: ignore[arg-type]
        base_n=len(join["base_ids"]),  # type: ignore[arg-type]
        n_join_available=join.get("n_join_available"),
        D_o_star=d_o,
        coverage_C_star=coverage,
        selection_aware_null95=dictionary_check.get("selection_aware_null95"),
        naive_fixed_subset_null95=dictionary_check.get("naive_fixed_subset_null95"),
        unexplained=unexplained,
        raw_best_coverage_over_candidate_family=dictionary_check.get("raw_best_coverage_over_candidate_family"),
        raw_best_coverage_D_o=dictionary_check.get("raw_best_coverage_D_o"),
        target="log10 protein abundance residualized against sibling Z controls on the unified yeast context join",
        source_design="B*_Q6 9-dimensional synonymous residual coordinates, residualized against the same Z controls",
        reduction_family="single-codon readout dictionary family from run_b_star_q6_minimal_dictionary_compression_powered.py",
        permutation_count=PERMUTATION_COUNT,
        fold_count=FOLD_COUNT,
        seed=SEED,
        lambda_dl=LAMBDA_DL,
        rho_join=RHO_JOIN,
        z_basis_rank=join.get("z_basis_rank"),
        checks=checks,
        data_summary=join.get("data_summary"),
        ordered_cds_summary=join.get("ordered_cds_summary"),
        context_summary={key: value for key, value in join.get("context_summary", {}).items() if key != "q2_feature_names"}
        if isinstance(join.get("context_summary"), dict)
        else join.get("context_summary"),
        interpretation=(
            f"residual signal is real and partially reducible to <=3 measured readouts {d_o}; "
            f"selection-aware significant coverage leaves unexplained fraction {unexplained}"
            if status == "passed"
            else "no positive partial-reducibility certificate is emitted unless the source, selection-aware dictionary, and <=3-readout gates all pass"
        ),
        cannot_claim=[
            "held-out predictive association and projection coverage are not causal proof",
            "selection-aware significance is restricted to the tested readout-dictionary candidate family",
            "the naive fixed-subset null is reported only as a selection-bias contrast and is not used as the certification gate",
            "raw best coverage over the candidate family is reported separately from the BEDC-selected minimal D_o_star",
        ],
    )


if __name__ == "__main__":
    main()

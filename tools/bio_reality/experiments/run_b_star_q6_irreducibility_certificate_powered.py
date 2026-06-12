#!/usr/bin/env python3
"""Irreducibility certificate for B*_Q6 protein-abundance residual signal."""

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
import run_b_star_q6_minimal_dictionary_compression_powered as compression
import run_b_star_q6_residual_dictionary_consistency_powered as residual_dictionary
from run_b_star_q6_protein_omics_survival_powered import matrix_column, orthonormal_basis_from_columns
from run_b_star_q6_translation_complement_residual_powered import solve_regularized_normal_equation
from run_b_star_q6_translation_complement_residual_powered import vector_norm2
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM


EXPERIMENT_ID = "b_star_q6_irreducibility_certificate_powered"
CLAIM_ID = "h3.cross_layer_relation.irreducibility_certificate.b_star_q6_residual_primitive_powered"

ORGANISM = "saccharomyces_cerevisiae"
PERMUTATION_COUNT = 120
FOLD_COUNT = 5
SEED = "sha256:b_star_q6_irreducibility_certificate_powered:deterministic"
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


def matrix_rows(rows: list[dict[str, object]], key: str) -> list[list[float]]:
    return [list(row[key]) for row in rows]  # type: ignore[arg-type]


def stable_digest(material: str) -> bytes:
    return hashlib.sha256(material.encode("utf-8")).digest()


def deterministic_permutation(n: int, material_prefix: str) -> list[int]:
    out = list(range(n))
    for index in range(n - 1, 0, -1):
        digest = stable_digest(f"{material_prefix}|index={index}|n={n}")
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap_index] = out[swap_index], out[index]
    return out


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


def public_subset_result(item: dict[str, object]) -> dict[str, object]:
    out = {key: value for key, value in item.items() if key not in {"state", "row_ids"}}
    null = out.get("null")
    if isinstance(null, dict):
        out["null"] = dict(null)
    return out


def build_unified_yeast_join(repo: pathlib.Path) -> dict[str, object]:
    required = [
        repo / "tools/bio_reality/data/ncbi_genetic_codes.json",
        repo / residual_dictionary.ORGANISMS[0]["stability_path"],  # type: ignore[index]
        repo / context_lift.ORDERED_CDS_PATH,
        repo / context_lift.CDS_ABUNDANCE_PATH,
        repo / f"tools/bio_reality/data/ribosome_te_{ORGANISM}.json",
    ]
    missing = [str(path.relative_to(repo)) for path in required if not path.exists()]
    if missing:
        return {"status": "needs_data", "reason": "required local yeast payload missing", "missing_required_data": missing}

    context = residual_dictionary.q6_context(repo)
    yeast_config = next(config for config in residual_dictionary.ORGANISMS if config["key"] == ORGANISM)
    built = residual_dictionary.base_rows(repo=repo, context=context, config=yeast_config)
    if built.get("status") != "computed":
        return {"status": "needs_data", "reason": built.get("reason", "yeast base rows unavailable"), "data_summary": built}
    rows = built.get("rows")
    if not isinstance(rows, dict):
        raise ValueError("base rows malformed")
    attached = residual_dictionary.attach_h_readouts(repo, ORGANISM, rows)  # type: ignore[arg-type]
    base_ids = sorted(rows)
    if len(base_ids) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "status": "needs_data",
            "reason": f"base yeast join yielded n={len(base_ids)} < {MIN_PROTEINS_PER_ORGANISM}",
            "n_base": len(base_ids),
            "data_summary": built.get("summary"),
            "H_source_summaries": attached["source_summaries"],
        }

    protein_orf = context_lift.protein_to_yeast_orf(repo, rows)  # type: ignore[arg-type]
    ordered_by_orf, ordered_summary = context_lift.ordered_cds_by_orf(repo)
    if not ordered_by_orf:
        return {
            "status": "needs_data",
            "reason": "ordered CDS payload has no usable CDS records",
            "ordered_cds_summary": ordered_summary,
        }
    selected_ids, selected_rows, q2_raw, aa_pair_rows, context_summary = context_lift.build_joined_context(
        rows=rows,  # type: ignore[arg-type]
        row_ids=base_ids,
        protein_to_orf=protein_orf,
        ordered_by_orf=ordered_by_orf,
        context=context,
    )
    n_join_available = sum(1 for protein_id in base_ids if protein_orf.get(protein_id) in ordered_by_orf)
    if len(selected_ids) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "status": "needs_data",
            "reason": f"ordered-CDS context join yielded n={len(selected_ids)} < {MIN_PROTEINS_PER_ORGANISM}",
            "n_join": len(selected_ids),
            "n_join_available": n_join_available,
            "n_base": len(base_ids),
            "ordered_cds_summary": ordered_summary,
            "context_summary": context_summary,
            "data_summary": built.get("summary"),
        }

    z_rows = matrix_rows(selected_rows, "z")
    x_rows = matrix_rows(selected_rows, "x")
    p_rows = matrix_rows(selected_rows, "p")
    z_basis = orthonormal_basis_from_columns(z_rows)
    x_e = residual_dictionary.residualize_with_basis(x_rows, z_basis)
    p_e = residual_dictionary.residualize_with_basis(p_rows, z_basis)
    target = matrix_column(p_e, 0)
    if vector_norm2(target) <= EPS:
        return {
            "status": "needs_data",
            "reason": "Z-residualized protein-abundance target has zero energy",
            "n_join": len(selected_ids),
            "n_base": len(base_ids),
        }

    return {
        "status": "computed",
        "repo": repo,
        "context": context,
        "yeast_config": yeast_config,
        "rows": rows,
        "base_ids": base_ids,
        "selected_ids": selected_ids,
        "selected_rows": selected_rows,
        "q2_raw": q2_raw,
        "aa_pair_rows": aa_pair_rows,
        "z_rows": z_rows,
        "x_e": x_e,
        "target": target,
        "z_basis_rank": len(z_basis),
        "n_join_available": n_join_available,
        "data_summary": built.get("summary"),
        "ordered_cds_summary": ordered_summary,
        "context_summary": context_summary,
        "H_source_summaries": attached["source_summaries"],
    }


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
    null_mean = mean(null_values)
    passed = held_out_r2 > null95
    return {
        "name": "source_is_real",
        "passed": passed,
        "held_out_r2": held_out_r2,
        "null95_r2": null95,
        "null_mean_r2": null_mean,
        "target_norm2": vector_norm2(target),
        "n_join": len(target),
        "n_features": len(x_e[0]) if x_e else 0,
        "fold_count": FOLD_COUNT,
        "permutation_count": PERMUTATION_COUNT,
        "seed": SEED,
        "null_model": "deterministic permutation of gene-to-Z-residualized protein-abundance labels with fixed B*_Q6 design and folds",
    }


def compression_does_not_capture_check(join: dict[str, object]) -> dict[str, object]:
    rows = join["rows"]
    selected_ids = join["selected_ids"]
    yeast_config = join["yeast_config"]
    if not isinstance(rows, dict) or not isinstance(selected_ids, list) or not isinstance(yeast_config, dict):
        raise ValueError("compression input malformed")

    old_permutation_count = compression.PERMUTATION_COUNT
    compression.PERMUTATION_COUNT = PERMUTATION_COUNT
    try:
        readouts = compression.available_readouts(yeast_config, rows, [str(item) for item in selected_ids])  # type: ignore[arg-type]
        join_cache: dict[tuple[str, ...], dict[str, object]] = {}
        readout_cache: dict[tuple[tuple[str, ...], str], list[list[float]]] = {}
        preliminary = [
            compression.evaluate_subset_cached(
                organism=ORGANISM,
                rows=rows,  # type: ignore[arg-type]
                base_ids=[str(item) for item in selected_ids],
                subset=subset,
                compute_null=False,
                join_cache=join_cache,
                readout_cache=readout_cache,
            )
            for subset in compression.all_subsets(readouts)
        ]
        candidate_subsets = compression.frontier_subsets(preliminary)
        evaluated = [
            compression.evaluate_subset_cached(
                organism=ORGANISM,
                rows=rows,  # type: ignore[arg-type]
                base_ids=[str(item) for item in selected_ids],
                subset=subset,
                compute_null=True,
                join_cache=join_cache,
                readout_cache=readout_cache,
            )
            for subset in candidate_subsets
        ]
    finally:
        compression.PERMUTATION_COUNT = old_permutation_count

    computed = [item for item in evaluated if item.get("status") == "computed"]
    if not computed:
        return {
            "name": "compression_does_not_capture",
            "passed": False,
            "status": "needs_data",
            "reason": "no readout subset passed the join gate",
            "base_n": len(selected_ids),
            "available_readouts": readouts,
            "preliminary_subset_count": len(preliminary),
            "matched_null_subset_count": len(evaluated),
        }
    best = max(computed, key=lambda item: float(item["BEDC_score"]))
    coverage = float(best["coverage"])
    null = best["null"]
    if not isinstance(null, dict):
        raise ValueError("compression null malformed")
    null95 = float(null["null95_coverage"])
    passed = coverage <= null95
    top_scoring = sorted(
        (
            {
                "D_o": item.get("D_o"),
                "n_join": item.get("n_join"),
                "coverage": item.get("coverage"),
                "null95_coverage": item.get("null", {}).get("null95_coverage") if isinstance(item.get("null"), dict) else None,
                "BEDC_score": item.get("BEDC_score"),
                "coverage_above_null95": item.get("coverage_above_null95"),
            }
            for item in computed
        ),
        key=lambda item: float(item["BEDC_score"]) if item["BEDC_score"] is not None else -1e100,
        reverse=True,
    )[:10]
    return {
        "name": "compression_does_not_capture",
        "passed": passed,
        "status": "computed",
        "D_o_star": best["D_o"],
        "coverage": coverage,
        "null95_coverage": null95,
        "null_mean_coverage": null.get("null_mean_coverage"),
        "coverage_above_null95": coverage > null95,
        "unexplained": best.get("unexplained"),
        "BEDC_score": best.get("BEDC_score"),
        "DL": best.get("DL"),
        "join_shift": best.get("join_shift"),
        "rank_D_e": best.get("rank_D_e"),
        "rank_Q_e": best.get("rank_Q_e"),
        "n_join": best.get("n_join"),
        "base_n": len(selected_ids),
        "available_readouts": readouts,
        "preliminary_subset_count": len(preliminary),
        "matched_null_subset_count": len(evaluated),
        "permutation_count": PERMUTATION_COUNT,
        "lambda_dl": LAMBDA_DL,
        "rho_join": RHO_JOIN,
        "seed": f"sha256:{compression.EXPERIMENT_ID}|organism|subset|trial|index|n",
        "coverage_metric": "sibling orthogonal projection coverage of P_Q by the Z-residualized readout dictionary on the active join",
        "null_model": null.get("null_model"),
        "top_scoring_subsets": top_scoring,
        "best_public": public_subset_result(best),
    }


def context_does_not_capture_check(join: dict[str, object]) -> dict[str, object]:
    selected_ids = join["selected_ids"]
    z_rows = join["z_rows"]
    x_e = join["x_e"]
    target = join["target"]
    q2_raw = join["q2_raw"]
    aa_pair_rows = join["aa_pair_rows"]
    context_summary = join["context_summary"]
    if not all(isinstance(item, list) for item in [selected_ids, z_rows, x_e, target, q2_raw, aa_pair_rows]):
        raise ValueError("context input malformed")
    if not isinstance(context_summary, dict):
        raise ValueError("context summary malformed")

    context_control_basis = orthonormal_basis_from_columns(
        [z_rows[index] + aa_pair_rows[index] for index in range(len(selected_ids))]
    )
    q2_e = context_lift.residualize_with_basis(q2_raw, context_control_basis)
    q2_rank = len(orthonormal_basis_from_columns(q2_e))
    q2_feature_count = len(q2_e[0]) if q2_e else 0
    base_design = x_e
    full_design = [x_e[index] + q2_e[index] for index in range(len(selected_ids))]

    _source_coefficients = solve_regularized_normal_equation(base_design, target)
    fold_indices = context_lift.folds_for_n(len(selected_ids), FOLD_COUNT)
    base_models = []
    full_models = []
    for test in fold_indices:
        test_set = set(test)
        train = [index for index in range(len(selected_ids)) if index not in test_set]
        base_models.append(context_lift.prepare_cv_model(base_design, train, test))
        full_models.append(context_lift.prepare_cv_model(full_design, train, test))

    held_out_delta = context_lift.cv_delta_r2_for_target(
        target=target,
        base_models=base_models,
        full_models=full_models,
    )
    null_values: list[float] = []
    for trial in range(PERMUTATION_COUNT):
        permutation = context_lift.deterministic_permutation(
            len(target),
            f"{context_lift.SEED}|target-permutation|trial={trial}",
        )
        permuted_target = [target[permutation[index]] for index in range(len(target))]
        null_values.append(
            context_lift.cv_delta_r2_for_target(
                target=permuted_target,
                base_models=base_models,
                full_models=full_models,
            )
        )
    null95 = percentile_nearest_rank(null_values, 0.95)
    null_mean = mean(null_values)
    passed = held_out_delta <= null95
    return {
        "name": "context_does_not_capture",
        "passed": passed,
        "held_out_delta_r2": held_out_delta,
        "null95_delta_r2": null95,
        "null_mean_delta_r2": null_mean,
        "n_join": len(selected_ids),
        "n_q1_features": len(base_design[0]) if base_design else 0,
        "n_q2_features": q2_feature_count,
        "q2_residual_rank": q2_rank,
        "aa_pair_feature_count": context_summary.get("aa_pair_feature_count"),
        "fold_count": FOLD_COUNT,
        "permutation_count": PERMUTATION_COUNT,
        "seed": context_lift.SEED,
        "null_model": "deterministic permutation of gene-to-protein-abundance-residual labels with the same folds and Q1/Q2 designs",
        "target": "same Z-residualized log10 protein abundance vector used by source_is_real on the unified yeast context join",
    }


def main() -> None:
    repo = pathlib.Path.cwd()
    join = build_unified_yeast_join(repo)
    if join.get("status") != "computed":
        emit(
            "needs_data",
            reason=join.get("reason", "unified yeast join unavailable"),
            checks=[],
            **{key: value for key, value in join.items() if key not in {"status", "reason"}},
        )

    source_check = source_is_real_check(join)
    compression_check = compression_does_not_capture_check(join)
    if compression_check.get("status") == "needs_data":
        emit(
            "needs_data",
            reason="compression reduction family could not be evaluated on the unified yeast join",
            checks=[source_check, compression_check],
            organism="Saccharomyces cerevisiae",
            organism_key=ORGANISM,
            n_join=len(join["selected_ids"]),  # type: ignore[arg-type]
            base_n=len(join["base_ids"]),  # type: ignore[arg-type]
            permutation_count=PERMUTATION_COUNT,
            fold_count=FOLD_COUNT,
            seed=SEED,
        )
    context_check = context_does_not_capture_check(join)
    irreducibility_passed = bool(source_check["passed"]) and bool(compression_check["passed"]) and bool(context_check["passed"])
    irreducibility_check = {
        "name": "irreducibility_certified",
        "passed": irreducibility_passed,
        "source_is_real": bool(source_check["passed"]),
        "compression_does_not_capture": bool(compression_check["passed"]),
        "context_does_not_capture": bool(context_check["passed"]),
        "rule": "passed iff source_is_real AND compression_does_not_capture AND context_does_not_capture",
    }
    checks = [source_check, compression_check, context_check, irreducibility_check]
    failed_checks = [str(check["name"]) for check in checks if not check.get("passed")]
    status = "passed" if irreducibility_passed else "failed"
    emit(
        status,
        reason=None if status == "passed" else "one or more irreducibility certificate subconditions failed",
        failed_checks=failed_checks,
        organism="Saccharomyces cerevisiae",
        organism_key=ORGANISM,
        n_join=len(join["selected_ids"]),  # type: ignore[arg-type]
        base_n=len(join["base_ids"]),  # type: ignore[arg-type]
        n_join_available=join.get("n_join_available"),
        target="log10 protein abundance residualized against sibling Z controls on the unified yeast context join",
        source_design="B*_Q6 9-dimensional synonymous residual coordinates, residualized against the same Z controls",
        reduction_families=[
            "single-readout low-dimensional dictionary compression from run_b_star_q6_minimal_dictionary_compression_powered.py",
            "local codon-pair Q^(2) context lift from run_b_star_q6_context_lift_powered.py",
        ],
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
        cannot_claim=[
            "certified-real is a held-out predictive association against a matched permutation null, not causal proof",
            "certified-irreducible is restricted to the two tested reduction families and can be falsified by a future reduction that captures the signal",
            "compression uses the sibling projection-coverage metric and matched row-label null; it is not a universal dictionary impossibility theorem",
            "context lift tests local codon-pair Q^(2) features after amino-acid-pair controls, not all possible sequence context models",
        ],
    )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Local codon-pair context lift for B*_Q6 protein-abundance residuals."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any

import run_b_star_q6_residual_dictionary_consistency_powered as residual_dictionary
from run_b_star_q6_joint_te_stability_mediation_powered import yeast_join_keys
from run_b_star_q6_minimal_dictionary_compression_powered import BOUNDARY_GENE_SUBSAMPLE_N
from run_b_star_q6_protein_omics_survival_powered import matrix_column, orthonormal_basis_from_columns
from run_b_star_q6_translation_complement_residual_powered import solve_regularized_normal_equation
from run_b_star_q6_translation_complement_residual_powered import vector_norm2
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM, vector_dot


EXPERIMENT_ID = "b_star_q6_context_lift_powered"
CLAIM_ID = "h3.cross_layer_relation.context_lift.b_star_q6_codon_pair_residual_powered"

ORGANISM = "saccharomyces_cerevisiae"
ORDERED_CDS_PATH = "tools/bio_reality/data/cds_ordered_sequences_saccharomyces_cerevisiae.json"
CDS_ABUNDANCE_PATH = "tools/bio_reality/data/cds_codon_abundance_saccharomyces_cerevisiae.json"
PERMUTATION_COUNT = 120
FOLD_COUNT = 5
RIDGE = 1e-10
EPS = 1e-12
SEED = "sha256:b_star_q6_context_lift_powered:deterministic"
LAMBDA_DL = residual_dictionary.LAMBDA_DL
RHO_JOIN = residual_dictionary.RHO_JOIN


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def stable_digest(material: str) -> bytes:
    return hashlib.sha256(material.encode("utf-8")).digest()


def stable_subsample(row_ids: list[str], limit: int) -> list[str]:
    ordered = sorted(row_ids, key=lambda row_id: stable_digest(f"{SEED}|subsample|{row_id}"))
    return ordered[: min(limit, len(ordered))]


def deterministic_permutation(n: int, material_prefix: str) -> list[int]:
    out = list(range(n))
    for index in range(n - 1, 0, -1):
        digest = stable_digest(f"{material_prefix}|index={index}|n={n}")
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap_index] = out[swap_index], out[index]
    return out


def transpose(matrix: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    return [[row[index] for row in matrix] for index in range(len(matrix[0]))]


def residualize_with_basis(matrix: list[list[float]], basis: list[list[float]]) -> list[list[float]]:
    return residual_dictionary.residualize_with_basis(matrix, basis)


def matrix_rows(rows: list[dict[str, object]], key: str) -> list[list[float]]:
    return [list(row[key]) for row in rows]  # type: ignore[arg-type]


def protein_to_yeast_orf(repo: pathlib.Path, rows: dict[str, dict[str, object]]) -> dict[str, str]:
    path = repo / CDS_ABUNDANCE_PATH
    if not path.exists():
        return {}
    payload = load_json(path)
    joined = payload.get("joined") if isinstance(payload, dict) else None
    if not isinstance(joined, list):
        return {}
    out: dict[str, str] = {}
    for protein_id in rows:
        if protein_id.startswith("4932."):
            suffix = protein_id.split(".", 1)[1]
            if suffix:
                out[protein_id] = suffix
    for item in joined:
        if not isinstance(item, dict):
            continue
        protein_id, orf, error = yeast_join_keys(item)
        if not error and isinstance(protein_id, str) and protein_id in rows and isinstance(orf, str):
            out[protein_id] = orf
    return out


def ordered_cds_by_orf(repo: pathlib.Path) -> tuple[dict[str, list[str]], dict[str, object]]:
    path = repo / ORDERED_CDS_PATH
    if not path.exists():
        return {}, {"status": "needs_data", "missing_path": ORDERED_CDS_PATH}
    payload = load_json(path)
    cds = payload.get("cds") if isinstance(payload, dict) else None
    if not isinstance(cds, list):
        raise ValueError("ordered CDS payload must contain a cds list")
    out: dict[str, list[str]] = {}
    skipped = {"non_object": 0, "missing_gene_id": 0, "missing_codons": 0, "duplicate_gene_id": 0}
    for item in cds:
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        gene_id = item.get("gene_id")
        codons = item.get("codons")
        if not isinstance(gene_id, str) or not gene_id:
            skipped["missing_gene_id"] += 1
            continue
        if not isinstance(codons, list) or not all(isinstance(codon, str) for codon in codons):
            skipped["missing_codons"] += 1
            continue
        if gene_id in out:
            skipped["duplicate_gene_id"] += 1
            continue
        out[gene_id] = [dna_to_rna(codon) for codon in codons]
    return out, {
        "status": "computed",
        "ordered_cds_path": ORDERED_CDS_PATH,
        "n_ordered_cds": len(out),
        "skipped_ordered_cds_records": skipped,
    }


def normalized_q_vectors(context: dict[str, object]) -> dict[str, dict[str, float]]:
    codons = context["codons"]
    q_projected = context["q_projected"]
    q_names = context["q_names"]
    if not isinstance(codons, list) or not isinstance(q_projected, dict) or not isinstance(q_names, list):
        raise ValueError("q6 context malformed")
    out: dict[str, dict[str, float]] = {}
    for name in q_names:
        vector = q_projected[name]
        if not isinstance(vector, dict):
            raise ValueError("q6 projected vector malformed")
        norm = math.sqrt(sum(float(vector[codon]) * float(vector[codon]) for codon in codons))
        if norm <= EPS:
            raise ValueError("q6 projected vector has zero norm")
        out[str(name)] = {str(codon): float(vector[codon]) / norm for codon in codons}
    return out


def codon_pair_context_rows(
    *,
    row_ids: list[str],
    protein_to_orf: dict[str, str],
    ordered_by_orf: dict[str, list[str]],
    context: dict[str, object],
) -> tuple[list[list[float]], list[list[float]], dict[str, object]]:
    codons = context["codons"]
    code = context["code"]
    q_names = context["q_names"]
    aa_order = context["aa_order"]
    if not isinstance(codons, list) or not isinstance(code, dict) or not isinstance(q_names, list) or not isinstance(aa_order, list):
        raise ValueError("q6 context malformed")
    codon_set = set(str(codon) for codon in codons)
    aa_pairs = [(str(left), str(right)) for left in aa_order for right in aa_order]
    aa_pair_index = {pair: index for index, pair in enumerate(aa_pairs)}
    q_unit = normalized_q_vectors(context)
    q_pair_names = [(str(left), str(right)) for left in q_names for right in q_names]

    pair_weights: dict[tuple[str, str], list[float]] = {}
    aa_pair_for_codon_pair: dict[tuple[str, str], tuple[str, str]] = {}
    for left in codons:
        for right in codons:
            left_s = str(left)
            right_s = str(right)
            pair = (left_s, right_s)
            aa_pair_for_codon_pair[pair] = (str(code[left_s]), str(code[right_s]))
            pair_weights[pair] = [
                q_unit[q_left][left_s] * q_unit[q_right][right_s]
                for q_left, q_right in q_pair_names
            ]

    q2_rows: list[list[float]] = []
    aa_pair_rows: list[list[float]] = []
    skipped = {"missing_orf": 0, "missing_ordered_cds": 0, "too_few_sense_pairs": 0, "unknown_or_stop_pair": 0}
    used_pair_counts: list[int] = []
    for protein_id in row_ids:
        orf = protein_to_orf.get(protein_id)
        if orf is None:
            skipped["missing_orf"] += 1
            continue
        sequence = ordered_by_orf.get(orf)
        if sequence is None:
            skipped["missing_ordered_cds"] += 1
            continue
        pairs: list[tuple[str, str]] = []
        for left, right in zip(sequence, sequence[1:]):
            pair = (left, right)
            if left in codon_set and right in codon_set:
                pairs.append(pair)
            else:
                skipped["unknown_or_stop_pair"] += 1
        if not pairs:
            skipped["too_few_sense_pairs"] += 1
            continue
        scale = 1.0 / len(pairs)
        q2 = [0.0 for _ in q_pair_names]
        aa_pair_row = [0.0 for _ in aa_pairs]
        for pair in pairs:
            weights = pair_weights[pair]
            for index, value in enumerate(weights):
                q2[index] += scale * value
            aa_pair = aa_pair_for_codon_pair[pair]
            aa_pair_row[aa_pair_index[aa_pair]] += scale
        q2_rows.append(q2)
        aa_pair_rows.append(aa_pair_row)
        used_pair_counts.append(len(pairs))

    return q2_rows, aa_pair_rows, {
        "q2_feature_names": [f"{left}__{right}" for left, right in q_pair_names],
        "aa_pair_feature_count": len(aa_pairs),
        "skipped_context_rows": skipped,
        "min_sense_pair_count": min(used_pair_counts) if used_pair_counts else 0,
        "median_sense_pair_count": sorted(used_pair_counts)[len(used_pair_counts) // 2] if used_pair_counts else 0,
        "max_sense_pair_count": max(used_pair_counts) if used_pair_counts else 0,
    }


def build_joined_context(
    *,
    rows: dict[str, dict[str, object]],
    row_ids: list[str],
    protein_to_orf: dict[str, str],
    ordered_by_orf: dict[str, list[str]],
    context: dict[str, object],
) -> tuple[list[str], list[dict[str, object]], list[list[float]], list[list[float]], dict[str, object]]:
    context_ids = [
        protein_id
        for protein_id in row_ids
        if protein_to_orf.get(protein_id) is not None and protein_to_orf[protein_id] in ordered_by_orf
    ]
    selected_ids = stable_subsample(context_ids, BOUNDARY_GENE_SUBSAMPLE_N)
    q2_raw, aa_pair_rows, context_summary = codon_pair_context_rows(
        row_ids=selected_ids,
        protein_to_orf=protein_to_orf,
        ordered_by_orf=ordered_by_orf,
        context=context,
    )
    if len(q2_raw) != len(selected_ids):
        used_ids = []
        for protein_id in selected_ids:
            orf = protein_to_orf.get(protein_id)
            sequence = ordered_by_orf.get(orf) if orf is not None else None
            if sequence is not None and any(left in context["codons"] and right in context["codons"] for left, right in zip(sequence, sequence[1:])):  # type: ignore[operator]
                used_ids.append(protein_id)
        selected_ids = used_ids
    selected_rows = [rows[protein_id] for protein_id in selected_ids]
    return selected_ids, selected_rows, q2_raw, aa_pair_rows, context_summary


def regularized_inverse_from_design(design: list[list[float]], ridge: float = RIDGE) -> list[list[float]]:
    if not design:
        return []
    width = len(design[0])
    gram = [[0.0 for _ in range(width)] for _ in range(width)]
    for row in design:
        for i in range(width):
            left = row[i]
            if left == 0.0:
                continue
            for j in range(width):
                gram[i][j] += left * row[j]
    for index in range(width):
        gram[index][index] += ridge

    aug = [gram[row] + [1.0 if row == col else 0.0 for col in range(width)] for row in range(width)]
    for col in range(width):
        pivot = max(range(col, width), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= EPS:
            raise ValueError("regularized design gram is singular")
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        scale = aug[col][col]
        for item in range(2 * width):
            aug[col][item] /= scale
        for row in range(width):
            if row == col:
                continue
            factor = aug[row][col]
            if factor == 0.0:
                continue
            for item in range(2 * width):
                aug[row][item] -= factor * aug[col][item]
    return [row[width:] for row in aug]


def mat_vec(matrix: list[list[float]], vector: list[float]) -> list[float]:
    return [sum(row[index] * vector[index] for index in range(len(vector))) for row in matrix]


def dot_row(row: list[float], coeff: list[float]) -> float:
    return sum(row[index] * coeff[index] for index in range(len(coeff)))


def design_subset(design: list[list[float]], indices: list[int]) -> list[list[float]]:
    return [design[index] for index in indices]


def prepare_cv_model(design: list[list[float]], train_indices: list[int], test_indices: list[int]) -> dict[str, object]:
    train = design_subset(design, train_indices)
    test = design_subset(design, test_indices)
    return {
        "train_indices": train_indices,
        "test_indices": test_indices,
        "train": train,
        "test": test,
        "inverse": regularized_inverse_from_design(train),
    }


def predict_cv(model: dict[str, object], target: list[float]) -> list[float]:
    train_indices = model["train_indices"]
    train = model["train"]
    test = model["test"]
    inverse = model["inverse"]
    if not isinstance(train_indices, list) or not isinstance(train, list) or not isinstance(test, list) or not isinstance(inverse, list):
        raise ValueError("cv model malformed")
    width = len(train[0]) if train else 0
    rhs = [0.0 for _ in range(width)]
    for local_index, row in enumerate(train):
        value = target[int(train_indices[local_index])]
        for feature_index in range(width):
            rhs[feature_index] += row[feature_index] * value
    coeff = mat_vec(inverse, rhs)
    return [dot_row(row, coeff) for row in test]


def folds_for_n(n: int, fold_count: int) -> list[list[int]]:
    return [[index for index in range(n) if index % fold_count == fold] for fold in range(fold_count)]


def cv_delta_r2_for_target(
    *,
    target: list[float],
    base_models: list[dict[str, object]],
    full_models: list[dict[str, object]],
) -> float:
    total_ss = 0.0
    base_sse = 0.0
    full_sse = 0.0
    for base_model, full_model in zip(base_models, full_models):
        test_indices = base_model["test_indices"]
        if not isinstance(test_indices, list):
            raise ValueError("cv model malformed")
        base_predictions = predict_cv(base_model, target)
        full_predictions = predict_cv(full_model, target)
        for local_index, row_index in enumerate(test_indices):
            observed = target[int(row_index)]
            total_ss += observed * observed
            base_residual = observed - base_predictions[local_index]
            full_residual = observed - full_predictions[local_index]
            base_sse += base_residual * base_residual
            full_sse += full_residual * full_residual
    if total_ss <= EPS:
        return 0.0
    return (base_sse - full_sse) / total_ss


def in_sample_incremental_r2(base_design: list[list[float]], full_design: list[list[float]], target: list[float]) -> dict[str, object]:
    target_norm2 = vector_norm2(target)
    if target_norm2 <= EPS:
        return {"delta": 0.0, "base_r2": 0.0, "full_r2": 0.0, "base_rank": 0, "full_rank": 0}
    base_basis = orthonormal_basis_from_columns(base_design)
    full_basis = orthonormal_basis_from_columns(full_design)
    base_energy = sum(vector_dot(target, q) ** 2 for q in base_basis)
    full_energy = sum(vector_dot(target, q) ** 2 for q in full_basis)
    base_r2 = max(0.0, min(1.0, base_energy / target_norm2))
    full_r2 = max(0.0, min(1.0, full_energy / target_norm2))
    return {
        "delta": full_r2 - base_r2,
        "base_r2": base_r2,
        "full_r2": full_r2,
        "base_rank": len(base_basis),
        "full_rank": len(full_basis),
    }


def main() -> None:
    repo = pathlib.Path.cwd()
    required = [repo / ORDERED_CDS_PATH, repo / CDS_ABUNDANCE_PATH]
    missing = [str(path.relative_to(repo)) for path in required if not path.exists()]
    if missing:
        emit("needs_data", reason="required local yeast ordered-CDS or abundance payload missing", missing_required_data=missing)

    context = residual_dictionary.q6_context(repo)
    yeast_config = next(config for config in residual_dictionary.ORGANISMS if config["key"] == ORGANISM)
    built = residual_dictionary.base_rows(repo=repo, context=context, config=yeast_config)
    if built.get("status") != "computed":
        emit("needs_data", reason=built.get("reason", "yeast base rows unavailable"), data_summary=built)
    rows = built.get("rows")
    if not isinstance(rows, dict):
        raise ValueError("base rows malformed")
    base_ids = sorted(rows)
    if len(base_ids) < MIN_PROTEINS_PER_ORGANISM:
        emit(
            "needs_data",
            reason=f"base yeast join yielded n={len(base_ids)} < {MIN_PROTEINS_PER_ORGANISM}",
            n_join=len(base_ids),
            data_summary=built.get("summary"),
        )

    protein_orf = protein_to_yeast_orf(repo, rows)  # type: ignore[arg-type]
    ordered_by_orf, ordered_summary = ordered_cds_by_orf(repo)
    if not ordered_by_orf:
        emit("needs_data", reason="ordered CDS payload has no usable CDS records", ordered_cds_summary=ordered_summary)

    selected_ids, selected_rows, q2_raw, aa_pair_rows, context_summary = build_joined_context(
        rows=rows,  # type: ignore[arg-type]
        row_ids=base_ids,
        protein_to_orf=protein_orf,
        ordered_by_orf=ordered_by_orf,
        context=context,
    )
    n_join_available = sum(1 for protein_id in base_ids if protein_orf.get(protein_id) in ordered_by_orf)
    if len(selected_ids) < MIN_PROTEINS_PER_ORGANISM:
        emit(
            "needs_data",
            reason=f"ordered-CDS context join yielded n={len(selected_ids)} < {MIN_PROTEINS_PER_ORGANISM}",
            n_join=len(selected_ids),
            n_join_available=n_join_available,
            base_n=len(base_ids),
            ordered_cds_summary=ordered_summary,
            context_summary=context_summary,
        )

    z_rows = matrix_rows(selected_rows, "z")
    x_rows = matrix_rows(selected_rows, "x")
    p_rows = matrix_rows(selected_rows, "p")
    z_basis = orthonormal_basis_from_columns(z_rows)
    x_e = residualize_with_basis(x_rows, z_basis)
    p_e = residualize_with_basis(p_rows, z_basis)
    target = matrix_column(p_e, 0)

    context_control_basis = orthonormal_basis_from_columns([z_rows[index] + aa_pair_rows[index] for index in range(len(selected_ids))])
    q2_e = residualize_with_basis(q2_raw, context_control_basis)
    q2_rank = len(orthonormal_basis_from_columns(q2_e))
    q2_feature_count = len(q2_e[0]) if q2_e else 0
    base_design = x_e
    full_design = [x_e[index] + q2_e[index] for index in range(len(selected_ids))]

    # Exercise the sibling normal-equation helper on the observed base model;
    # CV permutations below reuse precomputed inverses for the same ridge fit.
    _base_coefficients = solve_regularized_normal_equation(base_design, target)

    fold_indices = folds_for_n(len(selected_ids), FOLD_COUNT)
    base_models = [prepare_cv_model(base_design, [index for index in range(len(selected_ids)) if index not in set(test)], test) for test in fold_indices]
    full_models = [prepare_cv_model(full_design, [index for index in range(len(selected_ids)) if index not in set(test)], test) for test in fold_indices]
    held_out_delta = cv_delta_r2_for_target(target=target, base_models=base_models, full_models=full_models)

    permutation_values: list[float] = []
    for trial in range(PERMUTATION_COUNT):
        permutation = deterministic_permutation(len(target), f"{SEED}|target-permutation|trial={trial}")
        permuted_target = [target[permutation[index]] for index in range(len(target))]
        permutation_values.append(
            cv_delta_r2_for_target(target=permuted_target, base_models=base_models, full_models=full_models)
        )
    null95 = percentile_nearest_rank(permutation_values, 0.95)
    null_mean = sum(permutation_values) / len(permutation_values) if permutation_values else 0.0
    in_sample = in_sample_incremental_r2(base_design, full_design, target)
    dl_penalty = LAMBDA_DL * q2_feature_count
    net_lift = held_out_delta - dl_penalty
    lift_exceeds_null = held_out_delta > null95
    dl_penalty_cleared = net_lift > 0.0
    held_out_positive = held_out_delta > 0.0

    checks = [
        {
            "name": "context_lift_computed",
            "passed": True,
            "held_out_delta_r2": held_out_delta,
            "in_sample_delta_r2": in_sample["delta"],
            "n_join": len(selected_ids),
            "n_join_available": n_join_available,
            "n_q1_features": len(base_design[0]) if base_design else 0,
            "n_q2_features": q2_feature_count,
            "q2_residual_rank": q2_rank,
            "aa_pair_feature_count": context_summary["aa_pair_feature_count"],
            "seed": SEED,
        },
        {
            "name": "lift_exceeds_matched_null",
            "passed": lift_exceeds_null,
            "held_out_delta_r2": held_out_delta,
            "null95_delta_r2": null95,
            "null_mean_delta_r2": null_mean,
            "permutation_count": PERMUTATION_COUNT,
            "null_model": "deterministic permutation of gene-to-protein-abundance-residual labels with the same folds and Q1/Q2 designs",
        },
        {
            "name": "dl_penalty_cleared",
            "passed": dl_penalty_cleared,
            "held_out_delta_r2": held_out_delta,
            "lambda_dl": LAMBDA_DL,
            "n_q2_features": q2_feature_count,
            "dl_penalty": dl_penalty,
            "net_lift_after_dl": net_lift,
        },
        {
            "name": "held_out_positive",
            "passed": held_out_positive,
            "held_out_delta_r2": held_out_delta,
            "fold_count": FOLD_COUNT,
        },
    ]

    status = "passed" if lift_exceeds_null and dl_penalty_cleared and held_out_positive else "failed"
    emit(
        status,
        organism="Saccharomyces cerevisiae",
        organism_key=ORGANISM,
        n_join=len(selected_ids),
        n_join_available=n_join_available,
        base_n=len(base_ids),
        n_q1_features=len(base_design[0]) if base_design else 0,
        n_q2_features=q2_feature_count,
        q2_residual_rank=q2_rank,
        held_out_delta_r2=held_out_delta,
        null95_delta_r2=null95,
        null_mean_delta_r2=null_mean,
        dl_penalty=dl_penalty,
        net_lift_after_dl=net_lift,
        lambda_dl=LAMBDA_DL,
        rho_join=RHO_JOIN,
        permutation_count=PERMUTATION_COUNT,
        fold_count=FOLD_COUNT,
        seed=SEED,
        checks=checks,
        in_sample_incremental=in_sample,
        data_summary=built.get("summary"),
        ordered_cds_summary=ordered_summary,
        context_summary={key: value for key, value in context_summary.items() if key != "q2_feature_names"},
        q2_feature_names=context_summary.get("q2_feature_names", []),
        interpretation=(
            "passed only if the held-out local codon-pair B*_Q6 context lift exceeds the matched permutation null, "
            "clears the sibling LAMBDA_DL complexity penalty, and is positive on held-out folds; otherwise failed is "
            "an honest negative result for local codon-pair context explaining the Q1 residual."
        ),
    )


if __name__ == "__main__":
    main()

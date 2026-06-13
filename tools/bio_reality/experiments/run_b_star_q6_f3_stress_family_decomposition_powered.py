#!/usr/bin/env python3
"""Per-family decomposition of the B*_Q6 f3_stress abundance source."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import run_b_star_q6_context_lift_powered as context_lift
import run_b_star_q6_irreducibility_certificate_powered as routea
import run_b_star_q6_residual_dictionary_consistency_powered as residual_dictionary
from run_b_star_q6_protein_omics_survival_powered import codon_counts_rna, orthonormal_basis_from_columns
from run_b_star_q6_translation_complement_residual_powered import vector_norm2
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM, vector_dot
from run_b_star_q6_translation_survival_powered import Q9_FAMILIES


EXPERIMENT_ID = "b_star_q6_f3_stress_family_decomposition_powered"
CLAIM_ID = "h3.cross_layer_relation.f3_stress_family_decomposition.b_star_q6_synonymous_identity_powered"

ORGANISM = "saccharomyces_cerevisiae"
F3_COORDINATE = "f3_stress"
PERMUTATION_COUNT = 120
FOLD_COUNT = 5
SEED = "sha256:b_star_q6_f3_stress_family_decomposition_powered:deterministic"
EPS = 1e-12
CONSISTENCY_TOL = 1e-10


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


def matrix_rows(rows: list[dict[str, object]], key: str) -> list[list[float]]:
    return [list(row[key]) for row in rows]  # type: ignore[arg-type]


def matrix_column(matrix: list[list[float]], column_index: int) -> list[float]:
    return [row[column_index] for row in matrix]


def vector_add(left: list[float], right: list[float]) -> list[float]:
    return [left[index] + right[index] for index in range(len(left))]


def vector_subtract(left: list[float], right: list[float]) -> list[float]:
    return [left[index] - right[index] for index in range(len(left))]


def project_vector(design: list[list[float]], target: list[float]) -> tuple[list[float], float, int, list[list[float]]]:
    basis = orthonormal_basis_from_columns(design)
    projected = [0.0 for _ in target]
    for q in basis:
        coeff = vector_dot(target, q)
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            projected[index] += coeff * q[index]
    return projected, vector_norm2(projected), len(basis), basis


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


def source_null_for_family(*, family_name: str, design: list[list[float]], target: list[float]) -> dict[str, object]:
    models = prepare_models(design, len(target))
    held_out_r2 = cv_r2_for_target(target=target, models=models)
    null_values: list[float] = []
    for trial in range(PERMUTATION_COUNT):
        permutation = deterministic_permutation(
            len(target),
            f"{SEED}|source-target-permutation|family={family_name}|trial={trial}",
        )
        permuted_target = [target[permutation[index]] for index in range(len(target))]
        null_values.append(cv_r2_for_target(target=permuted_target, models=models))
    null95 = percentile_nearest_rank(null_values, 0.95)
    return {
        "held_out_r2": held_out_r2,
        "null95": null95,
        "null_mean": mean(null_values),
        "source_real": held_out_r2 > null95,
    }


def correlation(left: list[float], right: list[float]) -> float:
    left_norm = math.sqrt(vector_norm2(left))
    right_norm = math.sqrt(vector_norm2(right))
    if left_norm <= EPS or right_norm <= EPS:
        return 0.0
    return vector_dot(left, right) / (left_norm * right_norm)


def raw_family_weights(family: list[str], codons: list[str]) -> dict[str, float]:
    weights = {codon: 0.0 for codon in codons}
    if len(family) < 2:
        return weights
    weights[family[0]] += 1.0
    weights[family[-1]] -= 1.0
    return weights


def family_label(family: list[str], code: dict[str, str]) -> str:
    aa = code[family[0]]
    return f"{aa}_{family[0]}_to_{family[-1]}"


def normalized_coordinate_from_weights(
    *,
    frequencies: dict[str, float],
    weights: dict[str, float],
    codons: list[str],
    full_norm: float,
) -> float:
    return sum(frequencies[codon] * weights[codon] for codon in codons) / full_norm


def cds_frequency_rows_for_selected(
    *,
    repo: pathlib.Path,
    selected_ids: list[str],
    rows: dict[str, dict[str, object]],
    codons: list[str],
) -> tuple[list[dict[str, float]], dict[str, object]]:
    protein_to_orf = context_lift.protein_to_yeast_orf(repo, rows)
    payload = context_lift.load_json(repo / context_lift.CDS_ABUNDANCE_PATH)
    joined = payload.get("joined") if isinstance(payload, dict) else None
    if not isinstance(joined, list):
        raise ValueError("yeast CDS codon payload lacks joined list")

    item_by_protein: dict[str, dict[str, object]] = {}
    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            continue
        protein_id = item.get("protein_id")
        if isinstance(protein_id, str) and protein_id:
            item_by_protein[protein_id] = item
        for joined_protein_id, orf in protein_to_orf.items():
            if joined_protein_id not in item_by_protein and isinstance(orf, str) and item.get("gene_id") == orf:
                item_by_protein[joined_protein_id] = item
        if row_index % 1000 == 999:
            missing = [protein_id for protein_id in selected_ids if protein_id not in item_by_protein]
            if not missing:
                break

    frequencies: list[dict[str, float]] = []
    skipped = {"missing_cds_row": 0, "empty_sense_codon_counts": 0}
    for local_index, protein_id in enumerate(selected_ids):
        item = item_by_protein.get(protein_id)
        if item is None:
            skipped["missing_cds_row"] += 1
            raise ValueError(f"selected protein lacks CDS codon row: {protein_id}")
        counts = codon_counts_rna(item, codons, ORGANISM, local_index)
        total = sum(counts.values())
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            raise ValueError(f"selected protein has empty sense codon counts: {protein_id}")
        frequencies.append({codon: counts[codon] / total for codon in codons})
    return frequencies, {"selected_cds_frequency_rows": len(frequencies), "skipped": skipped}


def compute_family_decomposition(join: dict[str, object]) -> dict[str, object]:
    rows = join["rows"]
    selected_ids = join["selected_ids"]
    selected_rows = join["selected_rows"]
    context = join["context"]
    if not isinstance(rows, dict) or not isinstance(selected_ids, list) or not isinstance(selected_rows, list):
        raise ValueError("unified yeast join malformed")
    if not isinstance(context, dict):
        raise ValueError("unified yeast join lacks q6 context")

    codons = context.get("codons")
    code = context.get("code")
    q_projected = context.get("q_projected")
    q_names = context.get("q_names")
    if not isinstance(codons, list) or not isinstance(code, dict) or not isinstance(q_projected, dict) or not isinstance(q_names, list):
        raise ValueError("q6 context malformed")
    codon_list = [str(codon) for codon in codons]
    code_map = {str(codon): str(aa) for codon, aa in code.items()}
    q_names_s = [str(name) for name in q_names]
    if F3_COORDINATE not in q_names_s:
        raise ValueError("B*_Q6 context lacks f3_stress coordinate")

    row_ids = [str(protein_id) for protein_id in selected_ids]
    if len(row_ids) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "status": "needs_data",
            "reason": f"unified yeast context join yielded n={len(row_ids)} < {MIN_PROTEINS_PER_ORGANISM}",
            "n_join": len(row_ids),
        }

    z_basis = orthonormal_basis_from_columns(matrix_rows(selected_rows, "z"))
    x_e = residual_dictionary.residualize_with_basis(matrix_rows(selected_rows, "x"), z_basis)
    p_e = residual_dictionary.residualize_with_basis(matrix_rows(selected_rows, "p"), z_basis)
    target = matrix_column(p_e, 0)
    target_norm2 = vector_norm2(target)
    if target_norm2 <= EPS:
        return {
            "status": "needs_data",
            "reason": "Z-residualized protein-abundance target has zero energy",
            "n_join": len(row_ids),
        }

    f3_index = q_names_s.index(F3_COORDINATE)
    f3_full = matrix_column(x_e, f3_index)
    p_f3, p_f3_norm2, rank_f3, _f3_basis = project_vector([[value] for value in f3_full], target)
    if p_f3_norm2 <= EPS:
        return {
            "status": "needs_data",
            "reason": "P_f3 has zero residual energy on unified yeast join",
            "n_join": len(row_ids),
        }

    full_projected = q_projected[F3_COORDINATE]
    if not isinstance(full_projected, dict):
        raise ValueError("projected f3 vector malformed")
    full_weights = {codon: float(full_projected[codon]) for codon in codon_list}
    full_norm = math.sqrt(sum(full_weights[codon] * full_weights[codon] for codon in codon_list))
    if full_norm <= EPS:
        raise ValueError("projected f3 vector has zero norm")

    frequency_rows, frequency_summary = cds_frequency_rows_for_selected(
        repo=pathlib.Path.cwd(),
        selected_ids=row_ids,
        rows=rows,  # type: ignore[arg-type]
        codons=codon_list,
    )

    family_rows: list[dict[str, object]] = []
    residualized_family_vectors: list[list[float]] = []
    raw_family_vectors: list[list[float]] = []
    summed_projected_weights = {codon: 0.0 for codon in codon_list}
    for family_index, raw_family in enumerate(Q9_FAMILIES):
        family = [str(codon) for codon in raw_family]
        if len(family) < 2:
            continue
        raw_weights = raw_family_weights(family, codon_list)
        projected_weights = residual_dictionary.project_syn(raw_weights, residual_dictionary.fibers_for(code_map, codon_list))
        for codon in codon_list:
            summed_projected_weights[codon] += projected_weights[codon]
        family_norm2 = sum(projected_weights[codon] * projected_weights[codon] for codon in codon_list)
        raw_values = [
            normalized_coordinate_from_weights(
                frequencies=frequencies,
                weights=projected_weights,
                codons=codon_list,
                full_norm=full_norm,
            )
            for frequencies in frequency_rows
        ]
        residualized_values = matrix_column(residual_dictionary.residualize_with_basis([[value] for value in raw_values], z_basis), 0)
        raw_family_vectors.append(raw_values)
        residualized_family_vectors.append(residualized_values)
        family_rows.append(
            {
                "family": family_label(family, code_map),
                "family_index": family_index,
                "amino_acid": code_map[family[0]],
                "codons": family,
                "first_codon_plus": family[0],
                "last_codon_minus": family[-1],
                "family_projected_weight_norm2": family_norm2,
            }
        )

    summed_family = [0.0 for _ in f3_full]
    for family_vector in residualized_family_vectors:
        summed_family = vector_add(summed_family, family_vector)
    diff = vector_subtract(summed_family, f3_full)
    diff_norm2 = vector_norm2(diff)
    f3_norm2 = vector_norm2(f3_full)
    max_abs_diff = max((abs(value) for value in diff), default=0.0)
    relative_diff = math.sqrt(diff_norm2 / f3_norm2) if f3_norm2 > EPS else 0.0
    weight_diff_norm2 = sum((summed_projected_weights[codon] - full_weights[codon]) ** 2 for codon in codon_list)
    weight_relative_diff = math.sqrt(weight_diff_norm2) / full_norm
    consistency_passed = relative_diff <= CONSISTENCY_TOL and weight_relative_diff <= CONSISTENCY_TOL

    table: list[dict[str, object]] = []
    for row, family_vector in zip(family_rows, residualized_family_vectors):
        design = [[value] for value in family_vector]
        source = source_null_for_family(family_name=str(row["family"]), design=design, target=target)
        p_family, p_family_norm2, rank_family, _basis_family = project_vector(design, target)
        signed_p_f3_share = vector_dot(p_family, p_f3) / p_f3_norm2 if p_f3_norm2 > EPS else 0.0
        row.update(
            {
                "held_out_r2": source["held_out_r2"],
                "null95": source["null95"],
                "null_mean": source["null_mean"],
                "source_real": source["source_real"],
                "corr_with_f3": correlation(family_vector, f3_full),
                "energy_fraction": bounded_unit(p_family_norm2 / p_f3_norm2) if p_f3_norm2 > EPS else 0.0,
                "signed_P_f3_projection_share": signed_p_f3_share,
                "abs_P_f3_projection_share": abs(signed_p_f3_share),
                "P_family_norm2": p_family_norm2,
                "P_family_fraction_of_target": bounded_unit(p_family_norm2 / target_norm2) if target_norm2 > EPS else 0.0,
                "rank_family": rank_family,
                "residualized_family_norm2": vector_norm2(family_vector),
                "n_join": len(row_ids),
            }
        )
        table.append(row)

    by_source = sorted(table, key=lambda item: float(item["held_out_r2"]), reverse=True)
    by_energy = sorted(table, key=lambda item: float(item["energy_fraction"]), reverse=True)
    real_source_families = [row for row in table if bool(row.get("source_real"))]
    dominant_names = {
        str(row["family"])
        for row in by_source[:8] + by_energy[:8]
        if bool(row.get("source_real"))
    }
    dominant_families = [
        {
            "family": row["family"],
            "codons": row["codons"],
            "held_out_r2": row["held_out_r2"],
            "null95": row["null95"],
            "source_real": row["source_real"],
            "energy_fraction": row["energy_fraction"],
            "corr_with_f3": row["corr_with_f3"],
            "basis": "source_real family in the union of top-8 held_out_r2 and top-8 energy_fraction ranks",
        }
        for row in sorted(
            [row for row in table if str(row["family"]) in dominant_names],
            key=lambda item: (not bool(item["source_real"]), -float(item["held_out_r2"]), -float(item["energy_fraction"]), str(item["family"])),
        )
    ]

    checks = [
        {
            "name": "family_decomposition_computed",
            "passed": len(table) == len(Q9_FAMILIES),
            "actual": len(table),
            "expected": len(Q9_FAMILIES),
        },
        {
            "name": "decomposition_consistency",
            "passed": consistency_passed,
            "relative_l2_error": relative_diff,
            "max_abs_error": max_abs_diff,
            "weight_relative_l2_error": weight_relative_diff,
            "tolerance": CONSISTENCY_TOL,
            "expected": "sum of 21 residualized family subcoordinates equals sibling residualized f3_stress coordinate",
        },
        {
            "name": "has_real_source_family",
            "passed": bool(real_source_families),
            "actual": [row["family"] for row in real_source_families],
            "expected": "at least one family has held-out R2 above its deterministic target-label permutation Null95",
        },
    ]
    status = "passed" if all(bool(check["passed"]) for check in checks) else "failed"
    return {
        "status": status,
        "checks": checks,
        "family_table": sorted(table, key=lambda item: float(item["held_out_r2"]), reverse=True),
        "dominant_families": dominant_families,
        "top_families_by_held_out_r2": [
            {
                "family": row["family"],
                "codons": row["codons"],
                "held_out_r2": row["held_out_r2"],
                "null95": row["null95"],
                "source_real": row["source_real"],
            }
            for row in by_source[:8]
        ],
        "top_families_by_energy": [
            {
                "family": row["family"],
                "codons": row["codons"],
                "energy_fraction": row["energy_fraction"],
                "corr_with_f3": row["corr_with_f3"],
                "source_real": row["source_real"],
            }
            for row in by_energy[:8]
        ],
        "decomposition_consistency": {
            "relative_l2_error": relative_diff,
            "max_abs_error": max_abs_diff,
            "weight_relative_l2_error": weight_relative_diff,
            "f3_residualized_norm2": f3_norm2,
            "summed_family_residualized_norm2": vector_norm2(summed_family),
        },
        "P_f3_norm2": p_f3_norm2,
        "P_f3_fraction_of_target": bounded_unit(p_f3_norm2 / target_norm2),
        "rank_f3": rank_f3,
        "target_norm2": target_norm2,
        "family_count": len(table),
        "q9_family_count": len(Q9_FAMILIES),
        "target": "log10 protein abundance residualized against sibling Z controls on the unified yeast context join",
        "source_design": "21 additive f3_stress synonymous-family subcoordinates, each built by retaining only that Q9_FAMILIES block's projected f3 weights and dividing by the full projected f3 norm before the same Z residualization",
        "energy_metric": "P_family_norm2 / P_f3_norm2, where P_family is the target projection onto one residualized family subcoordinate and P_f3 is the target projection onto full residualized f3_stress",
        "organism": "Saccharomyces cerevisiae",
        "organism_key": ORGANISM,
        "n_join": len(row_ids),
        "base_n": len(join.get("base_ids", [])) if isinstance(join.get("base_ids"), list) else None,
        "z_basis_rank": len(z_basis),
        "permutation_count": PERMUTATION_COUNT,
        "fold_count": FOLD_COUNT,
        "seed": SEED,
        "min_proteins_per_organism": MIN_PROTEINS_PER_ORGANISM,
        "frequency_summary": frequency_summary,
        "data_summary": join.get("data_summary"),
        "ordered_cds_summary": join.get("ordered_cds_summary"),
        "context_summary": {key: value for key, value in join.get("context_summary", {}).items() if key != "q2_feature_names"}
        if isinstance(join.get("context_summary"), dict)
        else join.get("context_summary"),
        "cannot_claim": [
            "per-family source_real is a marginal single-family held-out association, not causal proof",
            "energy_fraction values are single-family projection energies and need not sum to one because family subcoordinates are correlated",
            "dominant_families is descriptive and selected only from observed held-out R2/source_real and projection-energy ranks",
        ],
        "verdict": (
            "f3_stress 的 21 个同义家族子坐标分解自洽，且至少一个家族在 held-out/permutation 门上是真实丰度源。"
            if status == "passed"
            else "f3_stress 家族分解未同时满足自洽与至少一个真实丰度源家族的门。"
        ),
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

    result = compute_family_decomposition(join)
    status = str(result.pop("status"))
    emit(status, **result)


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        emit("failed", error=str(exc), reason="f3_stress family decomposition experiment could not be computed")

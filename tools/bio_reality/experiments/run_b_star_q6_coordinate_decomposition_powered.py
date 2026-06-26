#!/usr/bin/env python3
"""Per-coordinate B*_Q6 reducibility decomposition for yeast abundance residuals."""

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
import run_b_star_q6_minimal_dictionary_compression_powered as compression
import run_b_star_q6_residual_dictionary_consistency_powered as residual_dictionary
from run_b_star_q6_protein_omics_survival_powered import orthonormal_basis_from_columns
from run_b_star_q6_translation_complement_residual_powered import vector_norm2
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM, vector_dot


EXPERIMENT_ID = "b_star_q6_coordinate_decomposition_powered"
CLAIM_ID = "h3.cross_layer_relation.coordinate_decomposition.b_star_q6_per_coordinate_reducibility_powered"

ORGANISM = "saccharomyces_cerevisiae"
READOUT_DICTIONARY = ("measured_te", "mrna_stability", "turnover")
PERMUTATION_COUNT = 120
FOLD_COUNT = 5
SEED = "sha256:b_star_q6_coordinate_decomposition_powered:deterministic"
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


def subtract_vectors(left: list[float], right: list[float]) -> list[float]:
    return [left[index] - right[index] for index in range(len(left))]


def matrix_rows(rows: list[dict[str, object]], key: str) -> list[list[float]]:
    return [list(row[key]) for row in rows]  # type: ignore[arg-type]


def matrix_column(matrix: list[list[float]], column_index: int) -> list[float]:
    return [row[column_index] for row in matrix]


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


def absorption_for_basis(basis: list[list[float]], target: list[float]) -> float:
    target_norm = vector_norm2(target)
    if target_norm <= EPS or not basis:
        return 0.0
    energy = sum(vector_dot(target, q) ** 2 for q in basis)
    if energy > target_norm and energy <= target_norm + 1e-8:
        energy = target_norm
    return bounded_unit(max(0.0, energy) / target_norm)


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


def projection_from_basis(basis: list[list[float]], target: list[float]) -> tuple[list[float], float]:
    projected = [0.0 for _ in target]
    for q in basis:
        coeff = vector_dot(target, q)
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            projected[index] += coeff * q[index]
    return projected, vector_norm2(projected)


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


def source_null_for_coordinate(
    *,
    coordinate_name: str,
    design: list[list[float]],
    target: list[float],
) -> dict[str, object]:
    models = prepare_models(design, len(target))
    held_out_r2 = cv_r2_for_target(target=target, models=models)
    null_values: list[float] = []
    for trial in range(PERMUTATION_COUNT):
        permutation = deterministic_permutation(
            len(target),
            f"{SEED}|source-target-permutation|coordinate={coordinate_name}|trial={trial}",
        )
        permuted_target = [target[permutation[index]] for index in range(len(target))]
        null_values.append(cv_r2_for_target(target=permuted_target, models=models))
    null95 = percentile_nearest_rank(null_values, 0.95)
    return {
        "held_out_r2": held_out_r2,
        "source_null95": null95,
        "source_null_mean": mean(null_values),
        "source_real": held_out_r2 > null95,
    }


def measured_dictionary_null(
    *,
    coordinate_name: str,
    basis: list[list[float]],
    target: list[float],
) -> dict[str, object]:
    coverage = absorption_for_basis(basis, target)
    null_values: list[float] = []
    for trial in range(PERMUTATION_COUNT):
        permutation = deterministic_permutation(
            len(target),
            f"{SEED}|coverage-target-permutation|coordinate={coordinate_name}|trial={trial}",
        )
        null_values.append(absorption_for_permuted_target(basis, target, permutation))
    null95 = percentile_nearest_rank(null_values, 0.95)
    return {
        "coverage_by_measured": coverage,
        "coverage_null95": null95,
        "coverage_null_mean": mean(null_values),
        "explained": coverage > null95,
    }


def residualized_dictionary_design(
    *,
    rows: dict[str, dict[str, object]],
    row_ids: list[str],
    readouts: tuple[str, ...],
    z_basis: list[list[float]],
) -> list[list[float]]:
    raw_design: list[list[float]] = []
    for protein_id in row_ids:
        row = rows[protein_id]
        values: list[float] = []
        for readout in readouts:
            values.extend(compression.readout_values(row, readout))
        raw_design.append(values)
    return residual_dictionary.residualize_with_basis(raw_design, z_basis)


def build_coordinate_join(join: dict[str, object]) -> dict[str, object]:
    rows = join["rows"]
    selected_ids = join["selected_ids"]
    selected_rows = join["selected_rows"]
    if not isinstance(rows, dict) or not isinstance(selected_ids, list) or not isinstance(selected_rows, list):
        raise ValueError("unified yeast join malformed")

    base_ids = [str(item) for item in selected_ids]
    attached = residual_dictionary.attach_h_readouts(pathlib.Path.cwd(), ORGANISM, rows)  # type: ignore[arg-type]
    row_ids = [
        protein_id
        for protein_id in base_ids
        if all(compression.row_has_readout(rows[protein_id], readout) for readout in READOUT_DICTIONARY)  # type: ignore[index]
    ]
    if len(row_ids) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "status": "needs_data",
            "reason": f"fixed readout dictionary join yielded n={len(row_ids)} < {MIN_PROTEINS_PER_ORGANISM}",
            "base_n": len(base_ids),
            "n_join": len(row_ids),
            "readout_dictionary": list(READOUT_DICTIONARY),
            "H_source_summaries": attached["source_summaries"],
            "dropped_readouts": attached["dropped"],
        }

    selected_by_id = {str(protein_id): selected_rows[index] for index, protein_id in enumerate(base_ids)}
    active_rows = [selected_by_id[protein_id] for protein_id in row_ids]
    z_rows = matrix_rows(active_rows, "z")
    x_rows = matrix_rows(active_rows, "x")
    p_rows = matrix_rows(active_rows, "p")
    z_basis = orthonormal_basis_from_columns(z_rows)
    x_e = residual_dictionary.residualize_with_basis(x_rows, z_basis)
    p_e = residual_dictionary.residualize_with_basis(p_rows, z_basis)
    target = matrix_column(p_e, 0)
    if vector_norm2(target) <= EPS:
        return {
            "status": "needs_data",
            "reason": "Z-residualized protein-abundance target has zero energy on fixed readout join",
            "base_n": len(base_ids),
            "n_join": len(row_ids),
            "readout_dictionary": list(READOUT_DICTIONARY),
        }

    d_e = residualized_dictionary_design(rows=rows, row_ids=row_ids, readouts=READOUT_DICTIONARY, z_basis=z_basis)  # type: ignore[arg-type]
    d_basis = orthonormal_basis_from_columns(d_e)
    return {
        "status": "computed",
        "rows": rows,
        "row_ids": row_ids,
        "selected_rows": active_rows,
        "x_e": x_e,
        "target": target,
        "dictionary_design_e": d_e,
        "dictionary_basis": d_basis,
        "z_basis_rank": len(z_basis),
        "rank_D_e": len(d_basis),
        "base_n": len(base_ids),
        "n_join": len(row_ids),
        "readout_dictionary": list(READOUT_DICTIONARY),
        "H_source_summaries": attached["source_summaries"],
        "dropped_readouts": attached["dropped"],
    }


def joint_source_sanity(x_e: list[list[float]], target: list[float]) -> dict[str, object]:
    models = prepare_models(x_e, len(target))
    p_q, p_q_norm2, rank_q, _basis_q = project_vector(x_e, target)
    target_norm2 = vector_norm2(target)
    return {
        "held_out_r2": cv_r2_for_target(target=target, models=models),
        "in_sample_projection_r2": bounded_unit(p_q_norm2 / target_norm2) if target_norm2 > EPS else 0.0,
        "P_Q_norm2": p_q_norm2,
        "target_norm2": target_norm2,
        "rank_Q_e": rank_q,
    }


def sibling_unified_source_sanity(join: dict[str, object]) -> dict[str, object]:
    x_e = join["x_e"]
    target = join["target"]
    if not isinstance(x_e, list) or not isinstance(target, list):
        raise ValueError("unified source sanity state malformed")
    out = joint_source_sanity(x_e, target)
    out["n_join"] = len(target)
    out["sample_scope"] = "unified yeast context join before restricting to the fixed measured-readout dictionary"
    return out


def coordinate_decomposition(active: dict[str, object], q_names: list[str]) -> list[dict[str, object]]:
    x_e = active["x_e"]
    target = active["target"]
    d_basis = active["dictionary_basis"]
    if not isinstance(x_e, list) or not isinstance(target, list) or not isinstance(d_basis, list):
        raise ValueError("coordinate active state malformed")

    table: list[dict[str, object]] = []
    for coordinate_index, coordinate_name in enumerate(q_names):
        design = [[row[coordinate_index]] for row in x_e]
        source = source_null_for_coordinate(coordinate_name=str(coordinate_name), design=design, target=target)
        p_i, p_i_norm2, rank_i, _basis_i = project_vector(design, target)
        coverage = measured_dictionary_null(coordinate_name=str(coordinate_name), basis=d_basis, target=p_i)
        projected, projected_norm2 = projection_from_basis(d_basis, p_i)
        residual = subtract_vectors(p_i, projected)
        table.append(
            {
                "coordinate": str(coordinate_name),
                "coordinate_index": coordinate_index,
                "held_out_r2": source["held_out_r2"],
                "null95": source["source_null95"],
                "null_mean": source["source_null_mean"],
                "source_real": source["source_real"],
                "coverage_by_measured": coverage["coverage_by_measured"],
                "coverage_null95": coverage["coverage_null95"],
                "coverage_null_mean": coverage["coverage_null_mean"],
                "explained": coverage["explained"],
                "classification": "explained" if coverage["explained"] else "mysterious",
                "P_coordinate_norm2": p_i_norm2,
                "P_coordinate_fraction_of_target": bounded_unit(p_i_norm2 / vector_norm2(target)) if vector_norm2(target) > EPS else 0.0,
                "projected_norm2_by_measured": projected_norm2,
                "unexplained_norm2_after_measured": vector_norm2(residual),
                "rank_coordinate": rank_i,
                "n_join": active["n_join"],
            }
        )
    return table


def checks_for(table: list[dict[str, object]]) -> list[dict[str, object]]:
    return [
        {
            "name": "decomposition_computed",
            "passed": len(table) == 9,
            "actual": len(table),
            "expected": 9,
        },
        {
            "name": "has_real_source",
            "passed": any(bool(row.get("source_real")) for row in table),
            "actual": [row.get("coordinate") for row in table if row.get("source_real")],
            "expected": "at least one coordinate has held-out R2 above its fixed-readout target-label permutation Null95",
        },
        {
            "name": "per_coordinate_table",
            "passed": len(table) == 9 and all(
                all(
                    key in row
                    for key in (
                        "coordinate",
                        "held_out_r2",
                        "null95",
                        "source_real",
                        "coverage_by_measured",
                        "coverage_null95",
                        "explained",
                    )
                )
                for row in table
            ),
            "actual": {
                "row_count": len(table),
                "coordinates": [row.get("coordinate") for row in table],
            },
            "expected": "complete 9-row table with source and measured-coverage fields",
        },
    ]


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

    context = join.get("context")
    if not isinstance(context, dict) or not isinstance(context.get("q_names"), list):
        emit("failed", reason="unified yeast join lacks B*_Q6 coordinate names", checks=[])
    q_names = [str(name) for name in context["q_names"]]
    if len(q_names) != 9:
        emit(
            "failed",
            reason="B*_Q6 context did not expose 9 coordinates",
            q_names=q_names,
            checks=[],
        )

    active = build_coordinate_join(join)
    if active.get("status") != "computed":
        emit(
            "needs_data",
            reason=active.get("reason", "fixed readout dictionary join unavailable"),
            checks=[],
            **{key: value for key, value in active.items() if key not in {"status", "reason", "rows", "selected_rows"}},
        )

    x_e = active["x_e"]
    target = active["target"]
    if not isinstance(x_e, list) or not isinstance(target, list):
        raise ValueError("active coordinate state malformed")
    table = coordinate_decomposition(active, q_names)
    checks = checks_for(table)
    passed = all(bool(check["passed"]) for check in checks)
    explained = [str(row["coordinate"]) for row in table if row.get("explained")]
    mysterious = [str(row["coordinate"]) for row in table if not row.get("explained")]
    real_sources = [str(row["coordinate"]) for row in table if row.get("source_real")]
    real_and_explained = [str(row["coordinate"]) for row in table if row.get("source_real") and row.get("explained")]
    real_and_mysterious = [str(row["coordinate"]) for row in table if row.get("source_real") and not row.get("explained")]
    status = "passed" if passed else "failed"
    emit(
        status,
        checks=checks,
        coordinate_table=table,
        explained_coordinates=explained,
        mysterious_coordinates=mysterious,
        real_source_coordinates=real_sources,
        real_source_explained_coordinates=real_and_explained,
        real_source_mysterious_coordinates=real_and_mysterious,
        joint_source_sanity=joint_source_sanity(x_e, target),
        target="log10 protein abundance residualized against sibling Z controls on the unified yeast context join",
        source_design="B*_Q6 9-dimensional synonymous residual coordinates, residualized against the same Z controls",
        measured_dictionary=list(READOUT_DICTIONARY),
        sibling_unified_source_sanity=sibling_unified_source_sanity(join),
        coverage_metric="orthogonal projection coverage of each single-coordinate P_i = Proj_{x_i}(target) by the fixed Z-residualized measured readout dictionary",
        source_real_metric="5-fold held-out R2 of single residualized coordinate against Z-residualized target, compared to deterministic target-label permutation Null95 with fixed folds/design",
        organism=ORGANISM,
        n_join=active["n_join"],
        base_n=active["base_n"],
        z_basis_rank=active["z_basis_rank"],
        rank_D_e=active["rank_D_e"],
        permutation_count=PERMUTATION_COUNT,
        fold_count=FOLD_COUNT,
        seed=SEED,
        min_proteins_per_organism=MIN_PROTEINS_PER_ORGANISM,
        data_summary=join.get("data_summary"),
        ordered_cds_summary=join.get("ordered_cds_summary"),
        context_summary=join.get("context_summary"),
        H_source_summaries=active.get("H_source_summaries"),
        dropped_readouts=active.get("dropped_readouts"),
        cannot_claim=[
            "per-coordinate coverage is descriptive projection coverage, not causal mediation proof",
            "source_real_i uses a marginal single-coordinate held-out association and can miss suppressor/joint effects",
            "explained_i means coverage exceeds the fixed measured-dictionary permutation Null95 for that coordinate target component",
        ],
        verdict=(
            "逐坐标分解表已完整产出，且至少一个 B*_Q6 坐标在 held-out/permutation 门上是真实丰度源。"
            if status == "passed"
            else "逐坐标分解未通过完整性或真实源非平凡门。"
        ),
    )


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        emit("failed", error=str(exc), reason="coordinate decomposition experiment could not be computed")

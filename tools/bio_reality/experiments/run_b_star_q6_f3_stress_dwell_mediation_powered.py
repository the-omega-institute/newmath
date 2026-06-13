#!/usr/bin/env python3
"""Dwell mediation test for the dominant B*_Q6 f3_stress abundance component."""

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
import run_b_star_q6_wobble_dwell_coupling_powered as wobble_dwell
from run_b_star_q6_protein_omics_survival_powered import matrix_column, orthonormal_basis_from_columns
from run_b_star_q6_translation_complement_residual_powered import vector_norm2
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM, vector_dot


EXPERIMENT_ID = "b_star_q6_f3_stress_dwell_mediation_powered"
CLAIM_ID = "h3.cross_layer_relation.f3_stress_dwell_mediation.b_star_q6_dwell_abundance_powered"

ORGANISM = "saccharomyces_cerevisiae"
F3_COORDINATE = "f3_stress"
BASE_READOUTS = ("measured_te", "mrna_stability", "turnover")
DWELL_FEATURE_NAMES = (
    "ribosome_rel_dwell_mean",
    "ribosome_rel_dwell_cv",
    "f3_weighted_relative_dwell",
)
OCCUPANCY_PATH = "tools/bio_reality/data/riboseq_positional_occupancy_saccharomyces_cerevisiae.json"
ORDERED_CDS_PATH = "tools/bio_reality/data/cds_ordered_sequences_saccharomyces_cerevisiae.json"
PERMUTATION_COUNT = 120
FOLD_COUNT = 5
SEED = "sha256:b_star_q6_f3_stress_dwell_mediation_powered:deterministic"
EPS = 1e-12


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def finite_number(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def stable_digest(material: str) -> bytes:
    return hashlib.sha256(material.encode("utf-8")).digest()


def deterministic_permutation(n: int, material_prefix: str) -> list[int]:
    out = list(range(n))
    for index in range(n - 1, 0, -1):
        digest = stable_digest(f"{material_prefix}|index={index}|n={n}")
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap_index] = out[swap_index], out[index]
    return out


def matrix_rows(rows: list[dict[str, object]], key: str) -> list[list[float]]:
    return [list(row[key]) for row in rows]  # type: ignore[arg-type]


def subtract_vectors(left: list[float], right: list[float]) -> list[float]:
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


def standardize_columns(matrix: list[list[float]]) -> tuple[list[list[float]], list[dict[str, float]]]:
    if not matrix:
        return [], []
    width = len(matrix[0])
    stats: list[dict[str, float]] = []
    columns: list[list[float]] = []
    for col in range(width):
        values = [row[col] for row in matrix]
        center = mean(values)
        variance = mean([(value - center) ** 2 for value in values])
        scale = math.sqrt(variance) if variance > EPS else 1.0
        stats.append({"mean": center, "sd": scale})
        columns.append([(value - center) / scale for value in values])
    return [[columns[col][row] for col in range(width)] for row in range(len(matrix))], stats


def prepare_models(design: list[list[float]]) -> list[dict[str, object]]:
    fold_indices = context_lift.folds_for_n(len(design), FOLD_COUNT)
    models = []
    for test in fold_indices:
        test_set = set(test)
        train = [index for index in range(len(design)) if index not in test_set]
        models.append(context_lift.prepare_cv_model(design, train, test))
    return models


def cv_r2_for_target(target: list[float], models: list[dict[str, object]]) -> float:
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


def cv_delta_r2_for_target(
    target: list[float],
    base_models: list[dict[str, object]],
    full_models: list[dict[str, object]],
) -> float:
    return context_lift.cv_delta_r2_for_target(target=target, base_models=base_models, full_models=full_models)


def pearson(left: list[float], right: list[float]) -> float:
    if len(left) != len(right) or not left:
        return 0.0
    left_center = mean(left)
    right_center = mean(right)
    left_e = [value - left_center for value in left]
    right_e = [value - right_center for value in right]
    left_norm = math.sqrt(sum(value * value for value in left_e))
    right_norm = math.sqrt(sum(value * value for value in right_e))
    if left_norm <= EPS or right_norm <= EPS:
        return 0.0
    out = sum(a * b for a, b in zip(left_e, right_e)) / (left_norm * right_norm)
    return max(-1.0, min(1.0, out))


def two_sided_normal_p_from_corr(corr: float, n: int) -> float:
    if n <= 3:
        return 1.0
    bounded = max(-1.0 + 1e-15, min(1.0 - 1e-15, corr))
    z = 0.5 * math.log((1.0 + bounded) / (1.0 - bounded)) * math.sqrt(n - 3)
    return math.erfc(abs(z) / math.sqrt(2.0))


def dwell_features_for_gene(
    gene_id: str,
    joined_item: dict[str, object],
    f3_q_dna: dict[str, float],
) -> list[float] | None:
    rows = wobble_dwell.iter_gene_windows(gene_id, joined_item)
    if not rows:
        return None
    occupancies: list[float] = []
    q_values: list[float] = []
    for row in rows:
        value = row.get("occupancy")
        codon = row.get("codon")
        if not finite_number(value) or not isinstance(codon, str):
            continue
        occupancies.append(float(value))
        q_values.append(float(f3_q_dna.get(codon.upper(), 0.0)))
    if len(occupancies) < 10:
        return None

    occ_mean = mean(occupancies)
    occ_sd = math.sqrt(mean([(value - occ_mean) ** 2 for value in occupancies]))
    occ_cv = occ_sd / (abs(occ_mean) + 1e-9)
    q_weight = sum(abs(value) for value in q_values)
    if q_weight <= EPS:
        return None
    f3_weighted_relative_dwell = sum(q * occ for q, occ in zip(q_values, occupancies)) / q_weight
    return [occ_mean, occ_cv, f3_weighted_relative_dwell]


def load_dwell_feature_index(repo: pathlib.Path, f3_q_dna: dict[str, float]) -> tuple[dict[str, list[float]], dict[str, object]]:
    missing = [rel for rel in (OCCUPANCY_PATH, ORDERED_CDS_PATH) if not (repo / rel).exists()]
    if missing:
        return {}, {"status": "needs_data", "missing_required_data": missing}

    occupancy = load_json(repo / OCCUPANCY_PATH)
    ordered_cds = load_json(repo / ORDERED_CDS_PATH)
    if not isinstance(occupancy, dict) or not isinstance(ordered_cds, dict):
        raise ValueError("dwell data files must contain JSON objects")
    joined, schema = wobble_dwell.schema_and_join(occupancy, ordered_cds)
    out: dict[str, list[float]] = {}
    skipped = {"no_window_rows": 0, "no_f3_support": 0}
    for gene_id, item in joined.items():
        features = dwell_features_for_gene(gene_id, item, f3_q_dna)
        if features is None:
            skipped["no_f3_support"] += 1
            continue
        out[gene_id] = features
    summary = {
        "status": "computed",
        "dwell_gene_count": len(out),
        "dwell_feature_names": list(DWELL_FEATURE_NAMES),
        "skipped": skipped,
        "schema_and_gene_id_join": schema,
        "feature_definitions": {
            "ribosome_rel_dwell_mean": "mean of file-provided local relative A-site occupancy across retained 5prime and 3prime codon windows",
            "ribosome_rel_dwell_cv": "standard deviation divided by mean magnitude of the same local relative occupancy values",
            "f3_weighted_relative_dwell": "sum over local window positions of f3_stress projected codon weight times relative occupancy, divided by sum absolute f3 weights",
        },
    }
    return out, summary


def build_analysis_state(repo: pathlib.Path) -> dict[str, object]:
    join = routea.build_unified_yeast_join(repo)
    if join.get("status") != "computed":
        return {
            "status": "needs_data",
            "reason": join.get("reason", "unified yeast join unavailable"),
            **{key: value for key, value in join.items() if key not in {"status", "reason"}},
        }

    rows = join["rows"]
    selected_ids = join["selected_ids"]
    selected_rows = join["selected_rows"]
    context = join["context"]
    yeast_config = join["yeast_config"]
    if not isinstance(rows, dict) or not isinstance(selected_ids, list) or not isinstance(selected_rows, list):
        raise ValueError("unified yeast join malformed")
    if not isinstance(context, dict) or not isinstance(context.get("q_names"), list):
        raise ValueError("unified yeast join lacks B*_Q6 context")
    q_names = [str(name) for name in context["q_names"]]
    if F3_COORDINATE not in q_names:
        raise ValueError("B*_Q6 context lacks f3_stress coordinate")

    f3_context = wobble_dwell.q6_context(repo)
    q_projected_dna = f3_context.get("q_projected_dna")
    if not isinstance(q_projected_dna, dict) or not isinstance(q_projected_dna.get(F3_COORDINATE), dict):
        raise ValueError("wobble-dwell B*_Q6 context lacks f3_stress DNA weights")
    f3_q_dna = {str(codon): float(value) for codon, value in q_projected_dna[F3_COORDINATE].items()}  # type: ignore[index]
    dwell_index, dwell_summary = load_dwell_feature_index(repo, f3_q_dna)
    if not dwell_index:
        return {"status": "needs_data", "reason": "no per-gene dwell readouts could be computed", "dwell_summary": dwell_summary}

    if not isinstance(yeast_config, dict):
        raise ValueError("yeast config malformed")
    available = compression.available_readouts(yeast_config, rows, [str(item) for item in selected_ids])  # type: ignore[arg-type]
    missing_readouts = [readout for readout in BASE_READOUTS if readout not in available]
    if missing_readouts:
        return {
            "status": "needs_data",
            "reason": "one or more base readouts unavailable on the yeast context join",
            "missing_base_readouts": missing_readouts,
            "available_readouts": available,
            "dwell_summary": dwell_summary,
        }

    protein_to_orf = context_lift.protein_to_yeast_orf(repo, rows)  # type: ignore[arg-type]
    selected_by_id = {str(protein_id): selected_rows[index] for index, protein_id in enumerate(selected_ids)}
    active_ids = [
        str(protein_id)
        for protein_id in selected_ids
        if all(compression.row_has_readout(rows[str(protein_id)], readout) for readout in BASE_READOUTS)
        and protein_to_orf.get(str(protein_id)) in dwell_index
    ]
    if len(active_ids) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "status": "needs_data",
            "reason": f"base readout plus dwell join yielded n={len(active_ids)} < {MIN_PROTEINS_PER_ORGANISM}",
            "n_join": len(active_ids),
            "base_n": len(selected_ids),
            "available_readouts": available,
            "dwell_summary": dwell_summary,
        }

    active_rows = [selected_by_id[protein_id] for protein_id in active_ids]
    z_basis = orthonormal_basis_from_columns(matrix_rows(active_rows, "z"))
    x_e = residual_dictionary.residualize_with_basis(matrix_rows(active_rows, "x"), z_basis)
    p_e = residual_dictionary.residualize_with_basis(matrix_rows(active_rows, "p"), z_basis)
    abundance_target = matrix_column(p_e, 0)
    f3_index = q_names.index(F3_COORDINATE)
    x_f3 = [row[f3_index] for row in x_e]
    p_f3, p_f3_norm2, rank_f3, _f3_basis = project_vector([[value] for value in x_f3], abundance_target)
    if p_f3_norm2 <= EPS:
        return {
            "status": "needs_data",
            "reason": "P_f3 has zero residual energy on the base+dwell join",
            "n_join": len(active_ids),
            "dwell_summary": dwell_summary,
        }

    raw_base_design: list[list[float]] = []
    raw_dwell_design: list[list[float]] = []
    for protein_id in active_ids:
        base_values: list[float] = []
        for readout in BASE_READOUTS:
            base_values.extend(compression.readout_values(rows[protein_id], readout))
        raw_base_design.append(base_values)
        orf = protein_to_orf[protein_id]
        raw_dwell_design.append(dwell_index[orf])

    standardized_dwell, dwell_standardization = standardize_columns(raw_dwell_design)
    base_design = residual_dictionary.residualize_with_basis(raw_base_design, z_basis)
    dwell_design = residual_dictionary.residualize_with_basis(standardized_dwell, z_basis)
    full_design = [base_design[index] + dwell_design[index] for index in range(len(active_ids))]
    dwell_alone_design = dwell_design

    primary_dwell = [row[2] for row in dwell_design]
    f3_dwell_corr = pearson(x_f3, primary_dwell)
    f3_dwell_p = two_sided_normal_p_from_corr(f3_dwell_corr, len(active_ids))

    return {
        "status": "computed",
        "rows": rows,
        "active_ids": active_ids,
        "base_n": len(selected_ids),
        "available_readouts": available,
        "q_names": q_names,
        "x_f3": x_f3,
        "target": abundance_target,
        "P_f3": p_f3,
        "P_f3_norm2": p_f3_norm2,
        "P_f3_fraction_of_target": p_f3_norm2 / vector_norm2(abundance_target)
        if vector_norm2(abundance_target) > EPS
        else 0.0,
        "rank_f3": rank_f3,
        "base_design": base_design,
        "dwell_design": dwell_alone_design,
        "full_design": full_design,
        "f3_dwell_corr": f3_dwell_corr,
        "f3_dwell_p": f3_dwell_p,
        "dwell_standardization": dwell_standardization,
        "dwell_summary": dwell_summary,
        "dwell_feature_names": list(DWELL_FEATURE_NAMES),
        "z_basis_rank": len(z_basis),
        "data_summary": join.get("data_summary"),
        "ordered_cds_summary": join.get("ordered_cds_summary"),
        "context_summary": join.get("context_summary"),
        "H_source_summaries": join.get("H_source_summaries"),
    }


def run_increment_test(state: dict[str, object]) -> dict[str, object]:
    p_f3 = state["P_f3"]
    base_design = state["base_design"]
    dwell_design = state["dwell_design"]
    full_design = state["full_design"]
    if not isinstance(p_f3, list) or not isinstance(base_design, list) or not isinstance(dwell_design, list) or not isinstance(full_design, list):
        raise ValueError("analysis state malformed")

    base_models = prepare_models(base_design)  # type: ignore[arg-type]
    dwell_models = prepare_models(dwell_design)  # type: ignore[arg-type]
    full_models = prepare_models(full_design)  # type: ignore[arg-type]
    base_r2 = cv_r2_for_target(p_f3, base_models)  # type: ignore[arg-type]
    dwell_alone_r2 = cv_r2_for_target(p_f3, dwell_models)  # type: ignore[arg-type]
    full_r2 = cv_r2_for_target(p_f3, full_models)  # type: ignore[arg-type]
    held_out_delta_r2 = cv_delta_r2_for_target(p_f3, base_models, full_models)  # type: ignore[arg-type]

    null_values: list[float] = []
    for trial in range(PERMUTATION_COUNT):
        permutation = deterministic_permutation(len(p_f3), f"{SEED}|P_f3-label-permutation|trial={trial}")
        permuted = [float(p_f3[permutation[index]]) for index in range(len(p_f3))]
        null_values.append(cv_delta_r2_for_target(permuted, base_models, full_models))
    null95 = percentile_nearest_rank(null_values, 0.95)

    return {
        "base_r2": base_r2,
        "dwell_alone_r2": dwell_alone_r2,
        "full_r2": full_r2,
        "held_out_delta_r2": held_out_delta_r2,
        "null95": null95,
        "null_mean": mean(null_values),
        "null_min": min(null_values) if null_values else 0.0,
        "null_max": max(null_values) if null_values else 0.0,
    }


def main() -> None:
    try:
        repo = pathlib.Path.cwd()
        state = build_analysis_state(repo)
        if state.get("status") != "computed":
            emit("needs_data", checks=[], **{key: value for key, value in state.items() if key != "status"})

        test = run_increment_test(state)
        held_out_delta_r2 = float(test["held_out_delta_r2"])
        null95 = float(test["null95"])
        f3_dwell_corr = float(state["f3_dwell_corr"])
        f3_dwell_p = float(state["f3_dwell_p"])

        dwell_readout_computed = {
            "name": "dwell_readout_computed",
            "passed": True,
            "dwell_feature_names": state["dwell_feature_names"],
            "n_join": len(state["active_ids"]) if isinstance(state.get("active_ids"), list) else None,
            "source": OCCUPANCY_PATH,
        }
        f3_dwell_sanity = {
            "name": "f3_dwell_coupling_sanity",
            "passed": f3_dwell_corr > 0.0 and f3_dwell_p < 0.05,
            "f3_dwell_corr": f3_dwell_corr,
            "f3_dwell_p_approx": f3_dwell_p,
            "feature": "Z-residualized f3_weighted_relative_dwell",
            "rule": "passed iff correlation with Z-residualized f3_stress is positive and Fisher-normal two-sided p < 0.05",
        }
        increment_check = {
            "name": "dwell_increment_exceeds_null",
            "passed": held_out_delta_r2 > null95,
            "held_out_delta_r2": held_out_delta_r2,
            "null95": null95,
            "rule": "passed iff held-out delta R2 for base plus dwell over base exceeds fixed-readout permutation Null95",
        }
        positive_check = {
            "name": "held_out_positive",
            "passed": held_out_delta_r2 > 0.0,
            "held_out_delta_r2": held_out_delta_r2,
        }
        checks = [dwell_readout_computed, f3_dwell_sanity, increment_check, positive_check]
        status = "passed" if increment_check["passed"] and positive_check["passed"] else "failed"

        emit(
            status,
            reason=None
            if status == "passed"
            else "dwell readouts did not give a positive held-out increment beyond the fixed-readout permutation gate",
            checks=checks,
            organism="Saccharomyces cerevisiae",
            organism_key=ORGANISM,
            n_join=len(state["active_ids"]) if isinstance(state.get("active_ids"), list) else None,
            base_n=state.get("base_n"),
            held_out_delta_r2=held_out_delta_r2,
            null95=null95,
            null_mean=test["null_mean"],
            null_min=test["null_min"],
            null_max=test["null_max"],
            dwell_alone_r2=test["dwell_alone_r2"],
            base_r2=test["base_r2"],
            full_r2=test["full_r2"],
            f3_dwell_corr=f3_dwell_corr,
            f3_dwell_p_approx=f3_dwell_p,
            dwell_feature_names=state["dwell_feature_names"],
            permutation_count=PERMUTATION_COUNT,
            fold_count=FOLD_COUNT,
            seed=SEED,
            base_readouts=list(BASE_READOUTS),
            target="P_f3 = projection of Z-residualized log10 protein abundance onto Z-residualized f3_stress on the active base+dwell join",
            dwell_readout="per-gene local relative ribosome occupancy summaries computed from file-provided 5prime and 3prime A-site occupancy windows",
            null_model="deterministic row-label permutation of P_f3 with base/full designs and folds fixed",
            P_f3_norm2=state.get("P_f3_norm2"),
            P_f3_fraction_of_target=state.get("P_f3_fraction_of_target"),
            rank_f3=state.get("rank_f3"),
            z_basis_rank=state.get("z_basis_rank"),
            dwell_standardization=state.get("dwell_standardization"),
            dwell_summary=state.get("dwell_summary"),
            available_readouts=state.get("available_readouts"),
            data_summary=state.get("data_summary"),
            ordered_cds_summary=state.get("ordered_cds_summary"),
            context_summary={key: value for key, value in state.get("context_summary", {}).items() if key != "q2_feature_names"}
            if isinstance(state.get("context_summary"), dict)
            else state.get("context_summary"),
            H_source_summaries=state.get("H_source_summaries"),
            cannot_claim=[
                "local relative ribosome occupancy is a dwell proxy, not a direct elongation-rate measurement",
                "held-out incremental prediction is a mediation-style falsification test, not causal proof",
                "measured_te is intentionally retained in the base dictionary, so any passed result is an increment beyond bulk footprint/mRNA TE",
                "failed status means this fixed dwell readout family did not mediate P_f3 beyond the base dictionary under this null, not that all possible dynamic measurements fail",
            ],
            verdict=(
                "f3_stress 的 P_f3 丰度分量有 dwell 增量中介证据：base+dwell held-out ΔR2 为正且超过固定 readout permutation Null95。"
                if status == "passed"
                else "f3_stress 与局部 dwell 的正耦合可复现，但这些 dwell 标量未在 held-out 增量门中解释 P_f3 超出 {te, stability, turnover} 的部分。"
            ),
        )
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="dwell mediation experiment could not be computed")


if __name__ == "__main__":
    main()

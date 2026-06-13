#!/usr/bin/env python3
"""Explain cross-organism f3_stress strength by synonymy selection and alignment."""

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

from run_b_star_q6_f3_stress_cross_organism_powered import (  # noqa: E402
    controls_for_counts,
    cv_r2_single_predictor,
    deterministic_folds,
    full_sample_slope,
    vector_dot,
)
from run_b_star_q6_organism_specificity_meta_powered import ORGANISMS  # noqa: E402
from run_b_star_q6_protein_omics_survival_powered import (  # noqa: E402
    codon_counts_rna,
    matrix_column,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM  # noqa: E402
from run_b_star_q6_translation_survival_powered import (  # noqa: E402
    Q9_FAMILIES,
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_f3_stress_strength_driver_powered"
CLAIM_ID = "h3.cross_layer_relation.f3_stress_strength_driver.b_star_q6_translational_selection_powered"

F3_COORDINATE = "f3_stress"
FOLD_COUNT = 5
MIN_COMPLETE_ORGANISMS = 15
MIN_SPEARMAN_RHO = 0.60
MIN_DIRECTION_AGREEMENT = 2.0 / 3.0
SEED = "sha256:b_star_q6_f3_stress_strength_driver_powered:deterministic"
EPS = 1e-12


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def finite_numeric(value: object) -> bool:
    return (
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and math.isfinite(float(value))
    )


def numeric(value: object, field: str) -> float:
    if not finite_numeric(value):
        raise ValueError(f"{field} must be finite numeric")
    return float(value)


def sign_label(value: float, eps: float = EPS) -> str:
    if value > eps:
        return "positive"
    if value < -eps:
        return "negative"
    return "zero"


def stable_int(material: str) -> int:
    return int.from_bytes(hashlib.sha256(material.encode("utf-8")).digest()[:8], "big")


def vector_norm(values: list[float]) -> float:
    return math.sqrt(sum(value * value for value in values))


def transpose(matrix: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    return [[row[index] for row in matrix] for index in range(len(matrix[0]))]


def average_ranks(values: list[float]) -> list[float]:
    indexed = sorted(enumerate(values), key=lambda item: item[1])
    ranks = [0.0 for _ in values]
    cursor = 0
    while cursor < len(indexed):
        end = cursor + 1
        while end < len(indexed) and indexed[end][1] == indexed[cursor][1]:
            end += 1
        rank = (cursor + 1 + end) / 2.0
        for pos in range(cursor, end):
            ranks[indexed[pos][0]] = rank
        cursor = end
    return ranks


def pearson(left: list[float], right: list[float]) -> float | None:
    if len(left) != len(right) or len(left) < 3:
        return None
    left_mean = sum(left) / len(left)
    right_mean = sum(right) / len(right)
    left_centered = [value - left_mean for value in left]
    right_centered = [value - right_mean for value in right]
    denom = vector_norm(left_centered) * vector_norm(right_centered)
    if denom <= EPS:
        return None
    return vector_dot(left_centered, right_centered) / denom


def spearman(left: list[float], right: list[float]) -> float | None:
    return pearson(average_ranks(left), average_ranks(right))


def synonymous_contrast_columns(
    *,
    fibers: dict[str, list[str]],
) -> list[dict[str, object]]:
    columns: list[dict[str, object]] = []
    for aa in sorted(fibers):
        family = sorted(fibers[aa])
        if len(family) < 2:
            continue
        reference = family[-1]
        for codon in family[:-1]:
            columns.append({"aa": aa, "positive_codon": codon, "negative_codon": reference})
    return columns


def synonymous_contrast_row(
    *,
    frequencies: dict[str, float],
    columns: list[dict[str, object]],
) -> list[float]:
    return [
        frequencies[str(column["positive_codon"])] - frequencies[str(column["negative_codon"])]
        for column in columns
    ]


def solve_linear_system(matrix: list[list[float]], rhs: list[float]) -> tuple[list[float], int]:
    n = len(rhs)
    if n == 0:
        return [], 0
    trace = sum(matrix[index][index] for index in range(n))
    base_ridge = max(EPS, abs(trace) * 1e-12 / max(1, n))
    for ridge_step in range(8):
        ridge = 0.0 if ridge_step == 0 else base_ridge * (100.0 ** (ridge_step - 1))
        augmented = [
            [
                matrix[row][col] + (ridge if row == col else 0.0)
                for col in range(n)
            ]
            + [rhs[row]]
            for row in range(n)
        ]
        ok = True
        for col in range(n):
            pivot = max(range(col, n), key=lambda row: abs(augmented[row][col]))
            pivot_abs = abs(augmented[pivot][col])
            if pivot_abs <= max(EPS, abs(trace) * 1e-14):
                ok = False
                break
            if pivot != col:
                augmented[col], augmented[pivot] = augmented[pivot], augmented[col]
            pivot_value = augmented[col][col]
            for j in range(col, n + 1):
                augmented[col][j] /= pivot_value
            for row in range(n):
                if row == col:
                    continue
                factor = augmented[row][col]
                if factor == 0.0:
                    continue
                for j in range(col, n + 1):
                    augmented[row][j] -= factor * augmented[col][j]
        if ok:
            return [augmented[row][n] for row in range(n)], ridge_step
    return [0.0 for _ in range(n)], 8


def xtx_xty(
    x_rows: list[list[float]],
    y: list[float],
    indices: list[int] | None = None,
) -> tuple[list[list[float]], list[float]]:
    p = len(x_rows[0]) if x_rows else 0
    xtx = [[0.0 for _ in range(p)] for _ in range(p)]
    xty = [0.0 for _ in range(p)]
    row_indices = range(len(x_rows)) if indices is None else indices
    for row_index in row_indices:
        row = x_rows[row_index]
        target = y[row_index]
        for i, xi in enumerate(row):
            xty[i] += xi * target
            for j in range(i + 1):
                xtx[i][j] += xi * row[j]
    for i in range(p):
        for j in range(i):
            xtx[j][i] = xtx[i][j]
    return xtx, xty


def subtract_matrix(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    return [
        [left[row][col] - right[row][col] for col in range(len(left[row]))]
        for row in range(len(left))
    ]


def subtract_vector(left: list[float], right: list[float]) -> list[float]:
    return [left[index] - right[index] for index in range(len(left))]


def cv_r2_multivariate(
    x_rows: list[list[float]],
    y: list[float],
    folds: list[list[int]],
) -> tuple[float, dict[str, object]]:
    if not x_rows:
        return 0.0, {"ridge_refit_count": 0, "max_ridge_step": 0}
    y_energy = vector_dot(y, y)
    if y_energy <= EPS:
        return 0.0, {"ridge_refit_count": 0, "max_ridge_step": 0}
    full_xtx, full_xty = xtx_xty(x_rows, y)
    sse = 0.0
    ridge_steps: list[int] = []
    for test_indices in folds:
        test_xtx, test_xty = xtx_xty(x_rows, y, test_indices)
        train_xtx = subtract_matrix(full_xtx, test_xtx)
        train_xty = subtract_vector(full_xty, test_xty)
        beta, ridge_step = solve_linear_system(train_xtx, train_xty)
        ridge_steps.append(ridge_step)
        for row_index in test_indices:
            prediction = vector_dot(x_rows[row_index], beta)
            residual = y[row_index] - prediction
            sse += residual * residual
    return 1.0 - sse / y_energy, {
        "ridge_refit_count": sum(1 for step in ridge_steps if step > 0),
        "max_ridge_step": max(ridge_steps) if ridge_steps else 0,
    }


def codon_preference_alignment(
    *,
    codon_frequency_residualized: list[list[float]],
    y: list[float],
    codons: list[str],
    fibers: dict[str, list[str]],
    f3_projected: dict[str, float],
) -> tuple[float, dict[str, float], list[dict[str, object]]]:
    y_energy = vector_dot(y, y)
    columns = transpose(codon_frequency_residualized)
    raw_preference: dict[str, float] = {}
    for codon, column in zip(codons, columns):
        x_energy = vector_dot(column, column)
        denom = math.sqrt(x_energy * y_energy)
        raw_preference[codon] = 0.0 if denom <= EPS else vector_dot(column, y) / denom
    preference_projected = project_syn(raw_preference, fibers)
    pref_values = [preference_projected[codon] for codon in codons]
    f3_values = [f3_projected[codon] for codon in codons]
    denom = vector_norm(pref_values) * vector_norm(f3_values)
    alignment = 0.0 if denom <= EPS else vector_dot(pref_values, f3_values) / denom

    family_rows: list[dict[str, object]] = []
    for family in Q9_FAMILIES:
        values = [(codon, raw_preference[codon]) for codon in family]
        preferred_codon, preferred_corr = max(values, key=lambda item: item[1])
        avoided_codon, avoided_corr = min(values, key=lambda item: item[1])
        first = family[0]
        last = family[-1]
        family_rows.append(
            {
                "family": family,
                "first_codon": first,
                "last_codon": last,
                "first_corr": raw_preference[first],
                "last_corr": raw_preference[last],
                "first_minus_last_corr": raw_preference[first] - raw_preference[last],
                "preferred_codon": preferred_codon,
                "preferred_corr": preferred_corr,
                "avoided_codon": avoided_codon,
                "avoided_corr": avoided_corr,
            }
        )
    return alignment, raw_preference, family_rows


def organism_rows(
    *,
    payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    f3_projected: dict[str, float],
    syn_columns: list[dict[str, object]],
) -> tuple[list[float], list[list[float]], list[list[float]], list[float], list[list[float]], dict[str, object]]:
    joined = payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} cds_codon_abundance payload must contain joined list")

    f3_rows: list[float] = []
    syn_rows: list[list[float]] = []
    codon_frequency_rows: list[list[float]] = []
    y_rows: list[float] = []
    controls: list[list[float]] = []
    skipped = {
        "non_object": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }
    f3_norm = math.sqrt(sum(f3_projected[codon] * f3_projected[codon] for codon in codons))
    if f3_norm <= EPS:
        raise ValueError("projected f3_stress vector has zero norm")

    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        abundance = numeric(item.get("abundance_ppm"), f"{organism}.joined[{row_index}].abundance_ppm")
        if abundance <= 0.0:
            skipped["nonpositive_abundance"] += 1
            continue
        cds_len_nt = numeric(item.get("cds_len_nt"), f"{organism}.joined[{row_index}].cds_len_nt")
        if cds_len_nt <= 0.0:
            skipped["invalid_length"] += 1
            continue
        counts = codon_counts_rna(item, codons, organism, row_index)
        total = sum(counts.values())
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue
        frequencies = {codon: counts[codon] / total for codon in codons}
        f3_rows.append(sum(frequencies[codon] * f3_projected[codon] for codon in codons) / f3_norm)
        syn_rows.append(synonymous_contrast_row(frequencies=frequencies, columns=syn_columns))
        codon_frequency_rows.append([frequencies[codon] for codon in codons])
        y_rows.append(math.log10(abundance))
        controls.append(
            controls_for_counts(
                counts=counts,
                code=code,
                codons=codons,
                aa_order=aa_order,
                total=total,
                cds_len_nt=cds_len_nt,
            )
        )

    summary = {
        "n_joined_reported": payload.get("n_joined"),
        "join_hit_rate": payload.get("join_hit_rate"),
        "n_usable": len(y_rows),
        "skipped_records": skipped,
    }
    return f3_rows, syn_rows, codon_frequency_rows, y_rows, controls, summary


def test_organism(
    *,
    repo: pathlib.Path,
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    fibers: dict[str, list[str]],
    f3_projected: dict[str, float],
    syn_columns: list[dict[str, object]],
) -> dict[str, object]:
    data_dir = repo / "tools/bio_reality/data"
    cds_path = data_dir / f"cds_codon_abundance_{organism}.json"
    proteomics_path = data_dir / f"proteomics_abundance_{organism}.json"
    if not cds_path.exists() or not proteomics_path.exists():
        return {
            "organism": organism,
            "status": "needs_data",
            "reason": "missing cds_codon_abundance or proteomics_abundance JSON",
            "cds_exists": cds_path.exists(),
            "proteomics_exists": proteomics_path.exists(),
        }

    payload = load_json(cds_path)
    if not isinstance(payload, dict):
        return {"organism": organism, "status": "needs_data", "reason": "cds payload is not an object"}
    proteomics_payload = load_json(proteomics_path)
    proteomics_n = proteomics_payload.get("n_proteins") if isinstance(proteomics_payload, dict) else None

    f3_raw, syn_raw, codon_freq_raw, y_raw, controls, data_summary = organism_rows(
        payload=payload,
        organism=organism,
        codons=codons,
        code=code,
        aa_order=aa_order,
        f3_projected=f3_projected,
        syn_columns=syn_columns,
    )
    n_join = len(y_raw)
    base = {
        "organism": organism,
        "status": "needs_data",
        "n_join": n_join,
        "proteomics_n_proteins": proteomics_n,
        "data_summary": data_summary,
    }
    if n_join < MIN_PROTEINS_PER_ORGANISM:
        base["reason"] = f"join below gate n_join={n_join} < {MIN_PROTEINS_PER_ORGANISM}"
        return base

    y_residualized, rank_controls_y = residualize([[value] for value in y_raw], controls)
    y = matrix_column(y_residualized, 0)
    y_energy = vector_dot(y, y)
    f3_residualized, rank_controls_f3 = residualize([[value] for value in f3_raw], controls)
    f3_x = matrix_column(f3_residualized, 0)
    syn_residualized, rank_controls_syn = residualize(syn_raw, controls)
    codon_freq_residualized, rank_controls_codon = residualize(codon_freq_raw, controls)

    if vector_dot(f3_x, f3_x) <= EPS or y_energy <= EPS:
        base["reason"] = "zero residual energy for f3_stress or abundance after controls"
        base["rank_controls_y"] = rank_controls_y
        base["rank_controls_f3"] = rank_controls_f3
        return base

    folds = deterministic_folds(n_join, f"{SEED}|{organism}|folds", FOLD_COUNT)
    f3_effect = cv_r2_single_predictor(f3_x, y, folds)
    f3_slope = full_sample_slope(f3_x, y)
    total_syn_selection, syn_cv_summary = cv_r2_multivariate(syn_residualized, y, folds)
    f3_alignment, _codon_preference, family_alignment = codon_preference_alignment(
        codon_frequency_residualized=codon_freq_residualized,
        y=y,
        codons=codons,
        fibers=fibers,
        f3_projected=f3_projected,
    )
    direction = sign_label(f3_slope)
    alignment_direction = sign_label(f3_alignment)
    return {
        "organism": organism,
        "status": "computed",
        "n_join": n_join,
        "proteomics_n_proteins": proteomics_n,
        "f3_effect": f3_effect,
        "f3_strength_nonnegative": max(0.0, f3_effect),
        "f3_slope": f3_slope,
        "direction": direction,
        "total_syn_selection": total_syn_selection,
        "total_syn_selection_nonnegative": max(0.0, total_syn_selection),
        "f3_alignment": f3_alignment,
        "alignment_direction": alignment_direction,
        "alignment_direction_matches_f3_direction": (
            alignment_direction != "zero" and direction != "zero" and alignment_direction == direction
        ),
        "fold_count": FOLD_COUNT,
        "rank_controls_y": rank_controls_y,
        "rank_controls_f3": rank_controls_f3,
        "rank_controls_syn": rank_controls_syn,
        "rank_controls_codon_frequency": rank_controls_codon,
        "synonymous_design_columns": len(syn_columns),
        "synonymous_cv_summary": syn_cv_summary,
        "residual_f3_energy": vector_dot(f3_x, f3_x),
        "residual_abundance_energy": y_energy,
        "family_alignment_summary": {
            "n_families": len(family_alignment),
            "first_minus_last_positive": sum(
                1 for row in family_alignment
                if float(row["first_minus_last_corr"]) > 0.0
            ),
            "first_minus_last_negative": sum(
                1 for row in family_alignment
                if float(row["first_minus_last_corr"]) < 0.0
            ),
            "strongest_aligned_families": sorted(
                family_alignment,
                key=lambda row: abs(float(row["first_minus_last_corr"])),
                reverse=True,
            )[:5],
        },
        "data_summary": data_summary,
    }


def main() -> None:
    repo = pathlib.Path.cwd()
    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        aa_order = standard_amino_acids(code, codons)
        fibers = fibers_for(code, codons)
        syn_columns = synonymous_contrast_columns(fibers=fibers)
        f3_projected = project_syn(q_vectors(codons)[F3_COORDINATE], fibers)

        per_organism = [
            test_organism(
                repo=repo,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                fibers=fibers,
                f3_projected=f3_projected,
                syn_columns=syn_columns,
            )
            for organism in ORGANISMS
        ]
        computed = [row for row in per_organism if row.get("status") == "computed"]
        n_computed = len(computed)
        if n_computed >= 3:
            f3_strength = [float(row["f3_strength_nonnegative"]) for row in computed]
            total_syn_strength = [float(row["total_syn_selection_nonnegative"]) for row in computed]
            rho_strength = spearman(total_syn_strength, f3_strength)
        else:
            rho_strength = None

        direction_rows = [
            row for row in computed
            if row.get("direction") in {"positive", "negative"}
            and row.get("alignment_direction") in {"positive", "negative"}
        ]
        direction_agreement_count = sum(
            1 for row in direction_rows
            if row.get("alignment_direction_matches_f3_direction") is True
        )
        direction_agreement_rate = (
            None if not direction_rows else direction_agreement_count / len(direction_rows)
        )
        sulfolobus = next(
            (row for row in computed if row.get("organism") == "sulfolobus_solfataricus"),
            None,
        )
        sulfolobus_negative_alignment = (
            sulfolobus is not None
            and sulfolobus.get("alignment_direction") == "negative"
            and sulfolobus.get("direction") == "negative"
        )

        enough_data = n_computed >= MIN_COMPLETE_ORGANISMS
        selection_passed = rho_strength is not None and rho_strength >= MIN_SPEARMAN_RHO
        alignment_passed = (
            direction_agreement_rate is not None
            and direction_agreement_rate >= MIN_DIRECTION_AGREEMENT
            and sulfolobus_negative_alignment
        )
        if not enough_data:
            status = "needs_data"
        else:
            status = "passed" if selection_passed and alignment_passed else "failed"

        compact_table = [
            {
                "organism": str(row["organism"]),
                "n_join": int(row["n_join"]),
                "f3_effect": row["f3_effect"],
                "f3_strength_nonnegative": row["f3_strength_nonnegative"],
                "total_syn_selection": row["total_syn_selection"],
                "total_syn_selection_nonnegative": row["total_syn_selection_nonnegative"],
                "f3_alignment": row["f3_alignment"],
                "direction": row["direction"],
                "alignment_direction": row["alignment_direction"],
                "alignment_direction_matches_f3_direction": row["alignment_direction_matches_f3_direction"],
            }
            for row in computed
        ]
        compact_table.sort(key=lambda row: str(row["organism"]))
        checks = {
            "per_organism_drivers_computed": {
                "passed": enough_data,
                "organisms_computed": n_computed,
                "minimum": MIN_COMPLETE_ORGANISMS,
                "organisms_requested_from_sibling": len(ORGANISMS),
            },
            "selection_predicts_f3_strength": {
                "passed": selection_passed,
                "spearman_rho": rho_strength,
                "minimum_rho": MIN_SPEARMAN_RHO,
                "x": "total_syn_selection_nonnegative",
                "y": "f3_strength_nonnegative",
            },
            "alignment_predicts_direction": {
                "passed": alignment_passed,
                "agreement_count": direction_agreement_count,
                "agreement_denominator": len(direction_rows),
                "agreement_rate": direction_agreement_rate,
                "minimum_agreement_rate": MIN_DIRECTION_AGREEMENT,
                "requires_sulfolobus_negative_alignment_and_negative_f3_direction": True,
                "sulfolobus_negative_alignment_and_direction": sulfolobus_negative_alignment,
            },
        }

        emit(
            status,
            seed=SEED,
            fold_count=FOLD_COUNT,
            min_proteins_per_organism=MIN_PROTEINS_PER_ORGANISM,
            organisms_requested=len(ORGANISMS),
            organisms_computed=n_computed,
            organisms_needs_data=[
                row for row in per_organism if row.get("status") != "computed"
            ],
            spearman_total_syn_selection_vs_f3_strength=rho_strength,
            direction_agreement_rate=direction_agreement_rate,
            direction_agreement_count=direction_agreement_count,
            direction_agreement_denominator=len(direction_rows),
            sulfolobus_negative_alignment_and_direction=sulfolobus_negative_alignment,
            interpretation=(
                "f3_stress strength is explained by total synonymous selection strength times fixed-direction alignment"
                if status == "passed"
                else (
                    "needs_data"
                    if status == "needs_data"
                    else "the requested decomposition did not meet the pre-registered strength/alignment gates"
                )
            ),
            controls_used={
                "target": "log10(abundance_ppm)",
                "residualization": "full-sample residualization of predictors and target before held-out CV, matching sibling f3 cross-organism experiment",
                "controls": [
                    "intercept",
                    "log(cds_len_nt)",
                    "log(total_sense_codons)",
                    "gc3_fraction",
                    "20 standard amino-acid composition fractions",
                ],
            },
            driver_definitions={
                "f3_effect": "5-fold held-out R2 for residualized f3_stress alone; direction is the full-sample residualized slope sign",
                "total_syn_selection": "5-fold held-out R2 for the complete synonymous codon-frequency contrast design, 41 columns=sum(fiber_size-1)",
                "f3_alignment": "cosine in synonymous codon space between projected fixed f3_stress weights and the organism's codon-abundance residual correlation vector",
                "meta_strength_values": "Spearman uses nonnegative held-out strengths max(0, R2) because strength, not signed direction, is tested here",
            },
            f3_definition={
                "coordinate": F3_COORDINATE,
                "raw_rule": "for each Q9_FAMILIES block, +1 to the first listed RNA codon and -1 to the last listed RNA codon, then project within amino-acid synonymous fibers",
                "raw_family_count": len(Q9_FAMILIES),
                "projected_norm2": sum(f3_projected[codon] * f3_projected[codon] for codon in codons),
            },
            synonymous_design={
                "columns": len(syn_columns),
                "rule": "for each amino-acid fiber with m synonymous codons, use m-1 codon-frequency contrasts against the lexicographically last codon",
            },
            per_organism_table=compact_table,
            checks=checks,
            caveats=[
                "cross-organism meta correlations use n=15 computed organisms here; this is a small-sample descriptive audit",
                "no phylogenetic comparative correction is applied, so cross-species correlations are not independent causal evidence",
                "alignment is estimated from the same organism's abundance-residual codon preferences, so it tests directional compatibility rather than an external mechanistic measurement",
                "negative or near-zero held-out R2 values are retained in the detailed table; the meta strength rank uses max(0, R2) to represent predictive strength",
            ],
        )
    except Exception as exc:
        emit(
            "needs_data",
            reason=f"{type(exc).__name__}: {exc}",
            checks={
                "per_organism_drivers_computed": {"passed": False},
                "selection_predicts_f3_strength": {"passed": False},
                "alignment_predicts_direction": {"passed": False},
            },
        )


if __name__ == "__main__":
    main()

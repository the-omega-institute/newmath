#!/usr/bin/env python3
"""Fourth residual-axis audit: translation accuracy / mistranslation cost."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
import types
from typing import Any


EXPERIMENT_ID = "b_star_q6_fourth_mechanism_translation_accuracy_powered"
CLAIM_ID = "h3.cross_layer_relation.fourth_mechanism_identity.b_star_q6_translation_accuracy_powered"

SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

DATA_DIR = pathlib.Path("/Users/lexa/Desktop/lexa/omega/newmath/tools/bio_reality/data")
SEED = f"sha256:{hashlib.sha256(EXPERIMENT_ID.encode('utf-8')).hexdigest()}"
FOLD_COUNT = 5
PERMUTATION_COUNT = 200
ALPHA = 0.05
MIN_COMPLETE_ORGANISMS = 10
MIN_STRUCTURAL_ORGANISMS = 1
MIN_JOIN = 80
EPS = 1e-12
F3_COORDINATE = "f3_stress"

# Local import shim required by sibling modules that import _tai at module load.
if "_tai" not in sys.modules:
    tai_shim = types.ModuleType("_tai")
    tai_shim.AA_ONE_TO_THREE = {
        "A": "Ala",
        "R": "Arg",
        "N": "Asn",
        "D": "Asp",
        "C": "Cys",
        "Q": "Gln",
        "E": "Glu",
        "G": "Gly",
        "H": "His",
        "I": "Ile",
        "L": "Leu",
        "K": "Lys",
        "M": "Met",
        "F": "Phe",
        "P": "Pro",
        "S": "Ser",
        "T": "Thr",
        "W": "Trp",
        "Y": "Tyr",
        "V": "Val",
    }
    tai_shim.RNA_COMPLEMENT = {"A": "U", "U": "A", "C": "G", "G": "C"}
    tai_shim.DOS_REIS_2004_WOBBLE_S = {
        ("G", "U"): 0.41,
        ("U", "G"): 0.68,
        ("I", "C"): 0.28,
        ("I", "A"): 0.9999,
        ("I", "U"): 0.0,
        ("L", "A"): 0.89,
    }

    def _first_two_positions_match(codon: str, anticodon: str) -> bool:
        return tai_shim.RNA_COMPLEMENT.get(anticodon[2]) == codon[0] and tai_shim.RNA_COMPLEMENT.get(anticodon[1]) == codon[1]

    def _effective_wobble_base(aa_label: str, anticodon: str) -> str:
        wobble = anticodon[0]
        if wobble == "A":
            return "I"
        if aa_label == "Ile2" and anticodon == "CAU":
            return "L"
        return wobble

    def _wobble_penalty(wobble: str, codon_third: str) -> float | None:
        if tai_shim.RNA_COMPLEMENT.get(wobble) == codon_third:
            return 0.0
        return tai_shim.DOS_REIS_2004_WOBBLE_S.get((wobble, codon_third))

    def _shim_codon_w_values(*_args: object, **_kwargs: object) -> tuple[dict[str, float], dict[str, float], dict[str, object]]:
        raise RuntimeError("Route-C sibling codon_w_values is imported from run_b_star_q6_universal_core_is_trna_adaptation_powered")

    tai_shim.first_two_positions_match = _first_two_positions_match
    tai_shim.effective_wobble_base = _effective_wobble_base
    tai_shim.wobble_penalty = _wobble_penalty
    tai_shim.codon_w_values = _shim_codon_w_values
    sys.modules["_tai"] = tai_shim

from run_b_star_q6_f3_stress_cross_organism_powered import (  # noqa: E402
    deterministic_folds,
    deterministic_permutation,
    vector_dot,
)
from run_b_star_q6_f3_stress_strength_driver_powered import (  # noqa: E402
    solve_linear_system,
    synonymous_contrast_columns,
    synonymous_contrast_row,
    xtx_xty,
)
from run_b_star_q6_organism_specificity_meta_powered import ORGANISMS, organism_domain  # noqa: E402
from run_b_star_q6_optimal_codon_conservation_powered import f3_contrast_direction  # noqa: E402
from run_b_star_q6_optimality_axis_sufficiency_powered import orthonormal_basis, usage_frequency_axis  # noqa: E402
from run_b_star_q6_protein_omics_survival_powered import (  # noqa: E402
    codon_counts_rna,
    matrix_column,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_third_axis_identity_powered import contrast_direction_from_codon_values  # noqa: E402
from run_b_star_q6_translation_survival_powered import fibers_for, project_syn, q_vectors  # noqa: E402
from run_b_star_q6_universal_core_is_trna_adaptation_powered import (  # noqa: E402
    codon_w_values,
    load_trna_records,
    trna_contrast_direction,
)
from run_b_star_q6_universal_optimal_residual_axis_powered import (  # noqa: E402
    cosine,
    cv_r2_fixed_direction,
    finite_numeric,
    fit_optimal_direction,
    mean,
    median,
    sign_test_greater,
    t_test_mean_greater_zero,
    unit_vector,
    vector_norm,
)
from run_b_star_q6_universal_optimal_two_axis_closure_powered import (  # noqa: E402
    fixed_basis_cv_r2,
    residual_after_basis,
)


AA_ONE_TO_THREE = tai_shim.AA_ONE_TO_THREE

# Standard Grantham amino-acid substitution distances, from Grantham R. Science
# 1974;185:862-864. The table is symmetric and encoded once as upper triangles.
GRANTHAM_ROWS: dict[str, dict[str, int]] = {
    "S": {"R": 110, "L": 145, "P": 74, "T": 58, "A": 99, "V": 124, "G": 56, "I": 142, "F": 155, "Y": 144, "C": 112, "H": 89, "Q": 68, "N": 46, "K": 121, "D": 65, "E": 80, "M": 135, "W": 177},
    "R": {"L": 102, "P": 103, "T": 71, "A": 112, "V": 96, "G": 125, "I": 97, "F": 97, "Y": 77, "C": 180, "H": 29, "Q": 43, "N": 86, "K": 26, "D": 96, "E": 54, "M": 91, "W": 101},
    "L": {"P": 98, "T": 92, "A": 96, "V": 32, "G": 138, "I": 5, "F": 22, "Y": 36, "C": 198, "H": 99, "Q": 113, "N": 153, "K": 107, "D": 172, "E": 138, "M": 15, "W": 61},
    "P": {"T": 38, "A": 27, "V": 68, "G": 42, "I": 95, "F": 114, "Y": 110, "C": 169, "H": 77, "Q": 76, "N": 91, "K": 103, "D": 108, "E": 93, "M": 87, "W": 147},
    "T": {"A": 58, "V": 69, "G": 59, "I": 89, "F": 103, "Y": 92, "C": 149, "H": 47, "Q": 42, "N": 65, "K": 78, "D": 85, "E": 65, "M": 81, "W": 128},
    "A": {"V": 64, "G": 60, "I": 94, "F": 113, "Y": 112, "C": 195, "H": 86, "Q": 91, "N": 111, "K": 106, "D": 126, "E": 107, "M": 84, "W": 148},
    "V": {"G": 109, "I": 29, "F": 50, "Y": 55, "C": 192, "H": 84, "Q": 96, "N": 133, "K": 97, "D": 152, "E": 121, "M": 21, "W": 88},
    "G": {"I": 135, "F": 153, "Y": 147, "C": 159, "H": 98, "Q": 87, "N": 80, "K": 127, "D": 94, "E": 98, "M": 127, "W": 184},
    "I": {"F": 21, "Y": 33, "C": 198, "H": 94, "Q": 109, "N": 149, "K": 102, "D": 168, "E": 134, "M": 10, "W": 61},
    "F": {"Y": 22, "C": 205, "H": 100, "Q": 116, "N": 158, "K": 102, "D": 177, "E": 140, "M": 28, "W": 40},
    "Y": {"C": 194, "H": 83, "Q": 99, "N": 143, "K": 85, "D": 160, "E": 122, "M": 36, "W": 37},
    "C": {"H": 174, "Q": 154, "N": 139, "K": 202, "D": 154, "E": 170, "M": 196, "W": 215},
    "H": {"Q": 24, "N": 68, "K": 32, "D": 81, "E": 40, "M": 87, "W": 115},
    "Q": {"N": 46, "K": 53, "D": 61, "E": 29, "M": 101, "W": 130},
    "N": {"K": 94, "D": 23, "E": 42, "M": 142, "W": 174},
    "K": {"D": 101, "E": 56, "M": 95, "W": 110},
    "D": {"E": 45, "M": 160, "W": 181},
    "E": {"M": 126, "W": 152},
    "M": {"W": 67},
}


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def numeric(value: object, field: str) -> float:
    if not finite_numeric(value):
        raise ValueError(f"{field} must be finite numeric")
    return float(value)


def standard_code() -> dict[str, str]:
    raw = load_json(DATA_DIR / "ncbi_genetic_codes.json")
    table = next((item for item in raw.get("tables", []) if item.get("table_id") == 1), None)
    codons = raw.get("codon_order", [])
    if not isinstance(codons, list) or not isinstance(table, dict) or len(codons) != len(table.get("aa", "")):
        raise ValueError("NCBI standard genetic code table is missing or malformed")
    return {str(codon): aa for codon, aa in zip(codons, table["aa"])}


def summarize_values(values: list[float]) -> dict[str, object]:
    return {
        "n": len(values),
        "mean": mean(values),
        "median": median(values),
        "min": None if not values else min(values),
        "max": None if not values else max(values),
        "positive_count": sum(1 for value in values if value > EPS),
        "negative_count": sum(1 for value in values if value < -EPS),
    }


def percentile_nearest_rank(values: list[float], probability: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def grantham(left: str, right: str) -> float:
    if left == right:
        return 0.0
    if right in GRANTHAM_ROWS.get(left, {}):
        return float(GRANTHAM_ROWS[left][right])
    if left in GRANTHAM_ROWS.get(right, {}):
        return float(GRANTHAM_ROWS[right][left])
    raise KeyError(f"missing Grantham distance {left}/{right}")


def hamming_one_neighbors(codon: str, codons: set[str]) -> list[str]:
    bases = ["U", "C", "A", "G"]
    out = []
    for pos in range(3):
        for base in bases:
            if base == codon[pos]:
                continue
            candidate = codon[:pos] + base + codon[pos + 1 :]
            if candidate in codons:
                out.append(candidate)
    return out


def center_within_families(values: dict[str, float], fibers: dict[str, list[str]]) -> dict[str, float]:
    return project_syn(values, fibers)


def contrast_values(values: dict[str, float], syn_columns: list[dict[str, object]]) -> list[float]:
    return [values[str(column["positive_codon"])] - values[str(column["negative_codon"])] for column in syn_columns]


def residualize_direction(direction: list[float], basis: list[list[float]]) -> tuple[list[float] | None, dict[str, object]]:
    residual = [float(value) for value in direction]
    coefficients = []
    for basis_vector in basis:
        coefficient = vector_dot(residual, basis_vector)
        coefficients.append(coefficient)
        residual = [residual[index] - coefficient * basis_vector[index] for index in range(len(residual))]
    unit = unit_vector(residual)
    return unit, {"projection_coefficients": coefficients, "residual_norm": vector_norm(residual), "basis_rank": len(basis)}


def gc_direction(syn_columns: list[dict[str, object]]) -> list[float] | None:
    return unit_vector(
        [
            (1.0 if str(column["positive_codon"])[2] in {"G", "C"} else 0.0)
            - (1.0 if str(column["negative_codon"])[2] in {"G", "C"} else 0.0)
            for column in syn_columns
        ]
    )


def wobble_class_direction(codon_values: dict[str, float], syn_columns: list[dict[str, object]]) -> list[float] | None:
    return contrast_direction_from_codon_values(codon_values, syn_columns)


def first_two_positions_match(codon: str, anticodon: str) -> bool:
    return tai_shim.RNA_COMPLEMENT.get(anticodon[2]) == codon[0] and tai_shim.RNA_COMPLEMENT.get(anticodon[1]) == codon[1]


def effective_wobble_base(aa_label: str, anticodon: str) -> str:
    wobble = anticodon[0]
    if wobble == "A":
        return "I"
    if aa_label == "Ile2" and anticodon == "CAU":
        return "L"
    return wobble


def wobble_penalty(wobble: str, codon_third: str) -> float | None:
    if tai_shim.RNA_COMPLEMENT.get(wobble) == codon_third:
        return 0.0
    return tai_shim.DOS_REIS_2004_WOBBLE_S.get((wobble, codon_third))


def wobble_penalty_scores(
    *,
    code: dict[str, str],
    codons: list[str],
    records: list[dict[str, str]],
    fibers: dict[str, list[str]],
) -> dict[str, float]:
    scores: dict[str, float] = {}
    for codon in codons:
        aa = AA_ONE_TO_THREE[code[codon]]
        penalties = []
        for record in records:
            if record.get("aa") != aa:
                continue
            aa_label = str(record.get("aa_label", ""))
            anticodon = str(record.get("anticodon", ""))
            if len(anticodon) != 3 or not first_two_positions_match(codon, anticodon):
                continue
            penalty = wobble_penalty(effective_wobble_base(aa_label, anticodon), codon[2])
            if penalty is not None:
                penalties.append(float(penalty))
        scores[codon] = min(penalties) if penalties else 1.0
    return center_within_families(scores, fibers)


def accuracy_scores(
    *,
    code: dict[str, str],
    codons: list[str],
    raw_w: dict[str, float],
    fibers: dict[str, list[str]],
) -> tuple[dict[str, float], dict[str, object]]:
    eps = max(1e-6, 1e-6 * max(raw_w.values()))
    codon_set = set(codons)
    raw_accuracy: dict[str, float] = {}
    neighbor_counts: dict[str, int] = {}
    denom_values: list[float] = []
    for codon in codons:
        aa = code[codon]
        denom = eps
        n_missense = 0
        for neighbor in hamming_one_neighbors(codon, codon_set):
            neighbor_aa = code[neighbor]
            if neighbor_aa == "*" or neighbor_aa == aa:
                continue
            n_missense += 1
            denom += raw_w.get(neighbor, 0.0) * grantham(aa, neighbor_aa)
        raw_accuracy[codon] = math.log((raw_w.get(codon, 0.0) + eps) / denom)
        neighbor_counts[codon] = n_missense
        denom_values.append(denom)
    centered = center_within_families(raw_accuracy, fibers)
    return centered, {
        "definition": "log((cognate dos-Reis W_codon + eps)/(eps + sum_1mismatch_missense W_neighbor * Grantham(aa, neighbor_aa))), then centered within synonymous family",
        "epsilon": eps,
        "missense_neighbor_count_min": min(neighbor_counts.values()),
        "missense_neighbor_count_max": max(neighbor_counts.values()),
        "missense_neighbor_count_mean": sum(neighbor_counts.values()) / len(neighbor_counts),
        "denominator_min": min(denom_values),
        "denominator_max": max(denom_values),
        "grantham_source": "standard Grantham 1974 20x20 amino-acid distance table, hardcoded symmetrically",
        "mismatch_position_weights": "uniform over all single-nucleotide codon positions",
    }


def standardize_train_apply(
    train_rows: list[list[float]],
    test_rows: list[list[float]],
) -> tuple[list[list[float]], list[list[float]], list[dict[str, float]]]:
    if not train_rows:
        return train_rows, test_rows, []
    width = len(train_rows[0])
    means = [sum(row[col] for row in train_rows) / len(train_rows) for col in range(width)]
    scales = []
    for col in range(width):
        variance = sum((row[col] - means[col]) ** 2 for row in train_rows) / len(train_rows)
        scale = math.sqrt(variance)
        scales.append(scale if scale > EPS else 1.0)
    train = [[(row[col] - means[col]) / scales[col] for col in range(width)] for row in train_rows]
    test = [[(row[col] - means[col]) / scales[col] for col in range(width)] for row in test_rows]
    return train, test, [{"mean": means[col], "sd": scales[col]} for col in range(width)]


def subset_rows(rows: list[list[float]], indices: list[int]) -> list[list[float]]:
    return [rows[index] for index in indices]


def subset_values(values: list[float], indices: list[int]) -> list[float]:
    return [values[index] for index in indices]


def residualize_target_and_blocks(
    *,
    y: list[float],
    blocks: dict[str, list[list[float]]],
    controls: list[list[float]],
) -> tuple[list[float], dict[str, list[list[float]]], int]:
    y_resid, rank_y = residualize([[value] for value in y], controls)
    out: dict[str, list[list[float]]] = {}
    ranks = [rank_y]
    for name, matrix in blocks.items():
        resid, rank = residualize(matrix, controls)
        out[name] = resid
        ranks.append(rank)
    return matrix_column(y_resid, 0), out, max(ranks)


def ridge_cv_r2(feature_rows: list[list[float]], y: list[float], folds: list[list[int]]) -> tuple[float, list[dict[str, object]]]:
    y_energy = vector_dot(y, y)
    if y_energy <= EPS:
        return 0.0, []
    sse = 0.0
    fold_metrics: list[dict[str, object]] = []
    all_indices = list(range(len(y)))
    for fold_index, test_indices in enumerate(folds):
        test_set = set(test_indices)
        train_indices = [index for index in all_indices if index not in test_set]
        train_x_raw = subset_rows(feature_rows, train_indices)
        test_x_raw = subset_rows(feature_rows, test_indices)
        train_x, test_x, _scaling = standardize_train_apply(train_x_raw, test_x_raw)
        train_y = subset_values(y, train_indices)
        xtx, xty = xtx_xty(train_x, train_y)
        beta, ridge_step = solve_linear_system(xtx, xty)
        fold_sse = 0.0
        for local_index, row_index in enumerate(test_indices):
            predicted = sum(beta[col] * test_x[local_index][col] for col in range(len(beta)))
            residual = y[row_index] - predicted
            sse += residual * residual
            fold_sse += residual * residual
        fold_energy = sum(y[index] * y[index] for index in test_indices)
        fold_metrics.append(
            {
                "fold": fold_index,
                "n_test": len(test_indices),
                "ridge_step": ridge_step,
                "held_out_r2_center_zero": 0.0 if fold_energy <= EPS else 1.0 - fold_sse / fold_energy,
            }
        )
    return 1.0 - sse / y_energy, fold_metrics


def cv_increment(
    base_rows: list[list[float]],
    full_rows: list[list[float]],
    y: list[float],
    folds: list[list[int]],
) -> dict[str, object]:
    base_r2, base_folds = ridge_cv_r2(base_rows, y, folds)
    full_r2, full_folds = ridge_cv_r2(full_rows, y, folds)
    return {
        "base_r2": base_r2,
        "full_r2": full_r2,
        "delta_r2": full_r2 - base_r2,
        "base_fold_metrics": base_folds,
        "full_fold_metrics": full_folds,
    }


def append_columns(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    return [left[index] + right[index] for index in range(len(left))]


def gene_rows(
    *,
    payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    syn_columns: list[dict[str, object]],
    trna_direction: list[float],
    f3_direction: list[float],
    usage_direction: list[float],
    accuracy_perp_direction: list[float],
) -> tuple[dict[str, list[Any]], dict[str, object]]:
    joined = payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} cds_codon_abundance payload must contain joined list")
    rows: dict[str, list[Any]] = {
        "ids": [],
        "protein_ids": [],
        "y": [],
        "base": [],
        "accuracy": [],
        "controls": [],
        "syn": [],
    }
    skipped = {"non_object": 0, "missing_protein_id": 0, "nonpositive_abundance": 0, "invalid_length": 0, "empty_counts": 0}
    seen: set[str] = set()
    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id_raw = item.get("protein_id")
        protein_id = protein_id_raw if isinstance(protein_id_raw, str) and protein_id_raw else f"{organism}:row:{row_index}"
        if protein_id in seen:
            protein_id = f"{protein_id}:dup:{row_index}"
        seen.add(protein_id)
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
            skipped["empty_counts"] += 1
            continue
        frequencies = {codon: counts[codon] / total for codon in codons}
        syn_row = synonymous_contrast_row(frequencies=frequencies, columns=syn_columns)
        aa_counts = {aa: 0 for aa in aa_order}
        for codon in codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
        controls = [1.0, math.log(cds_len_nt), math.log(total), gc3] + [aa_counts[aa] / aa_total for aa in aa_order]
        rows["ids"].append(protein_id)
        rows["protein_ids"].append(protein_id_raw if isinstance(protein_id_raw, str) else protein_id)
        rows["y"].append(math.log10(abundance))
        rows["base"].append(
            [
                vector_dot(syn_row, trna_direction),
                vector_dot(syn_row, f3_direction),
                vector_dot(syn_row, usage_direction),
            ]
        )
        rows["accuracy"].append([vector_dot(syn_row, accuracy_perp_direction)])
        rows["controls"].append(controls)
        rows["syn"].append(syn_row)
    return rows, {"n_rows": len(rows["y"]), "skipped_records": skipped}


def structural_order_index(path: pathlib.Path, organism: str) -> tuple[dict[str, float], dict[str, object]]:
    if not path.exists():
        return {}, {"status": "missing", "path": str(path)}
    payload = load_json(path)
    proteins = payload.get("proteins") if isinstance(payload, dict) else None
    if not isinstance(proteins, list):
        return {}, {"status": "malformed", "path": str(path)}
    out: dict[str, float] = {}
    skipped = {"non_object": 0, "missing_protein_id": 0, "invalid_structural_order": 0, "duplicate": 0}
    for row_index, item in enumerate(proteins):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        value = numeric(item.get("structural_order"), f"{organism}.structural_order[{row_index}]")
        if value < 0.0 or value > 100.0:
            skipped["invalid_structural_order"] += 1
            continue
        if protein_id in out:
            skipped["duplicate"] += 1
            continue
        out[protein_id] = value
    return out, {
        "status": "computed",
        "readout_kind": payload.get("readout_kind"),
        "n_valid": len(out),
        "skipped_records": skipped,
    }


def subset_dict_rows(rows: dict[str, list[Any]], indices: list[int]) -> dict[str, list[Any]]:
    return {key: [values[index] for index in indices] for key, values in rows.items()}


def analyze_structural_split(
    *,
    organism: str,
    rows: dict[str, list[Any]],
    order_by_protein: dict[str, float],
) -> dict[str, object]:
    matched = []
    for index, protein_id in enumerate(rows["protein_ids"]):
        value = order_by_protein.get(str(protein_id))
        if value is not None:
            matched.append((index, value))
    if len(matched) < MIN_JOIN:
        return {"status": "needs_data", "organism": organism, "n_structural_join": len(matched), "reason": "structural_order join below gate"}
    order_values = [value for _index, value in matched]
    threshold = median(order_values)
    if threshold is None:
        return {"status": "needs_data", "organism": organism, "n_structural_join": len(matched), "reason": "empty structural values"}
    ordered_indices = [index for index, value in matched if value >= threshold]
    disordered_indices = [index for index, value in matched if value < threshold]
    out: dict[str, object] = {
        "status": "computed",
        "organism": organism,
        "n_structural_join": len(matched),
        "median_structural_order": threshold,
        "ordered_n": len(ordered_indices),
        "disordered_n": len(disordered_indices),
    }
    for label, indices in [("ordered", ordered_indices), ("disordered", disordered_indices)]:
        if len(indices) < max(30, FOLD_COUNT * 4):
            out[f"{label}_status"] = "needs_data"
            continue
        sub = subset_dict_rows(rows, indices)
        y_resid, blocks, rank = residualize_target_and_blocks(
            y=[float(value) for value in sub["y"]],
            blocks={"base": sub["base"], "accuracy": sub["accuracy"]},  # type: ignore[arg-type]
            controls=sub["controls"],  # type: ignore[arg-type]
        )
        folds = deterministic_folds(len(y_resid), f"{SEED}|{organism}|structure|{label}|folds", FOLD_COUNT)
        inc = cv_increment(blocks["base"], append_columns(blocks["base"], blocks["accuracy"]), y_resid, folds)
        out[f"{label}_rank_controls"] = rank
        out[f"{label}_accuracy_delta_r2"] = inc["delta_r2"]
        out[f"{label}_base_r2"] = inc["base_r2"]
        out[f"{label}_full_r2"] = inc["full_r2"]
    ordered_delta = out.get("ordered_accuracy_delta_r2")
    disordered_delta = out.get("disordered_accuracy_delta_r2")
    if isinstance(ordered_delta, float) and isinstance(disordered_delta, float):
        out["ordered_minus_disordered_delta_r2"] = ordered_delta - disordered_delta
        out["ordered_stronger"] = ordered_delta > disordered_delta and ordered_delta > 0.0
    return out


def permuted_accuracy_direction(
    *,
    values: dict[str, float],
    fibers: dict[str, list[str]],
    syn_columns: list[dict[str, object]],
    material: str,
) -> list[float] | None:
    permuted: dict[str, float] = {}
    for aa, family in sorted(fibers.items()):
        order = deterministic_permutation(len(family), f"{material}|aa={aa}")
        source = [values[codon] for codon in family]
        for index, codon in enumerate(family):
            permuted[codon] = source[order[index]]
    centered = center_within_families(permuted, fibers)
    return contrast_direction_from_codon_values(centered, syn_columns)


def analyze_organism(
    *,
    organism: str,
    code: dict[str, str],
    codons: list[str],
    aa_order: list[str],
    fibers: dict[str, list[str]],
    syn_columns: list[dict[str, object]],
    f3_direction: list[float],
    gc_dir: list[float],
) -> dict[str, object]:
    cds_path = DATA_DIR / f"cds_codon_abundance_{organism}.json"
    gtrna_path = DATA_DIR / f"gtrnadb_trna_all_copy_{organism}.json"
    trna_summary_path = DATA_DIR / f"trna_gene_copy_{organism}.json"
    if not cds_path.exists() or (not gtrna_path.exists() and not trna_summary_path.exists()):
        return {
            "organism": organism,
            "status": "needs_data",
            "reason": "missing cds_codon_abundance or GtRNAdb/tRNA JSON",
            "cds_exists": cds_path.exists(),
            "gtrnadb_exists": gtrna_path.exists(),
            "trna_summary_exists": trna_summary_path.exists(),
        }
    payload = load_json(cds_path)
    if not isinstance(payload, dict):
        return {"organism": organism, "status": "needs_data", "reason": "CDS payload is not JSON object"}

    virtual_repo = DATA_DIR.parents[2]
    trna_records, trna_summary = load_trna_records(virtual_repo, organism)
    weights, raw_w, tai_summary = codon_w_values(code=code, codons=codons, records=trna_records)
    trna_direction = trna_contrast_direction(weights=weights, syn_columns=syn_columns)
    if trna_direction is None:
        return {"organism": organism, "status": "needs_data", "reason": "zero tRNA contrast direction", "trna_source_summary": trna_summary}
    usage_direction, usage_summary = usage_frequency_axis(
        payload=payload,
        organism=organism,
        codons=codons,
        fibers=fibers,
        syn_columns=syn_columns,
    )
    if usage_direction is None:
        return {"organism": organism, "status": "needs_data", "reason": "usage direction unavailable", "usage_axis_summary": usage_summary}

    wobble_values = wobble_penalty_scores(code=code, codons=codons, records=trna_records, fibers=fibers)
    wobble_dir = wobble_class_direction(wobble_values, syn_columns)
    if wobble_dir is None:
        return {"organism": organism, "status": "needs_data", "reason": "wobble-class direction unavailable"}

    acc_values, acc_summary = accuracy_scores(code=code, codons=codons, raw_w=raw_w, fibers=fibers)
    acc_raw_direction = contrast_direction_from_codon_values(acc_values, syn_columns)
    if acc_raw_direction is None:
        return {"organism": organism, "status": "needs_data", "reason": "accuracy direction collapsed", "accuracy_score_summary": acc_summary}
    nuisance_basis, nuisance_summary = orthonormal_basis(
        [
            ("tAI", trna_direction),
            ("f3", f3_direction),
            ("usage_frequency", usage_direction),
            ("GC3", gc_dir),
            ("wobble_class", wobble_dir),
        ]
    )
    if nuisance_basis is None:
        return {"organism": organism, "status": "needs_data", "reason": "nuisance basis unavailable", "nuisance_basis_summary": nuisance_summary}
    acc_perp_direction, acc_perp_summary = residualize_direction(acc_raw_direction, nuisance_basis)
    if acc_perp_direction is None:
        return {
            "organism": organism,
            "status": "needs_data",
            "reason": "Accuracy direction collapsed after tAI/f3/usage/GC/wobble projection",
            "accuracy_perp_summary": acc_perp_summary,
            "nuisance_basis_summary": nuisance_summary,
        }

    syn_raw, y_raw, controls, gc3, data_summary = organism_abundance_rows(
        payload=payload,
        organism=organism,
        codons=codons,
        code=code,
        aa_order=aa_order,
        syn_columns=syn_columns,
    )
    n_join = len(y_raw)
    if n_join < MIN_JOIN:
        return {"organism": organism, "status": "needs_data", "reason": f"abundance join below gate n={n_join}", "data_summary": data_summary}
    syn_resid, rank_controls_syn = residualize(syn_raw, controls)
    y_resid_matrix, rank_controls_y = residualize([[value] for value in y_raw], controls)
    y_resid = matrix_column(y_resid_matrix, 0)
    optimal_direction, fit_summary = fit_optimal_direction(syn_resid, y_resid)
    if optimal_direction is None:
        return {"organism": organism, "status": "needs_data", "reason": "could not fit abundance optimal direction", "fit_summary": fit_summary}
    three_basis, three_summary = orthonormal_basis([("tAI", trna_direction), ("f3", f3_direction), ("usage", usage_direction)])
    if three_basis is None:
        return {"organism": organism, "status": "needs_data", "reason": "three-axis basis unavailable", "three_axis_basis_summary": three_summary}
    d_resid4, captured_fraction_3, projection_coefficients = residual_after_basis(optimal_direction, three_basis)
    if d_resid4 is None:
        return {"organism": organism, "status": "needs_data", "reason": "d_resid4 collapsed after Route-S three-axis projection"}

    accuracy_resid4_cos = cosine(acc_perp_direction, d_resid4)
    null_cosines = []
    null_abs = []
    for trial in range(PERMUTATION_COUNT):
        perm_dir = permuted_accuracy_direction(
            values=acc_values,
            fibers=fibers,
            syn_columns=syn_columns,
            material=f"{SEED}|{organism}|accuracy-label-null|trial={trial}",
        )
        if perm_dir is None:
            continue
        perm_perp, _summary = residualize_direction(perm_dir, nuisance_basis)
        if perm_perp is None:
            continue
        value = cosine(perm_perp, d_resid4)
        null_cosines.append(value)
        null_abs.append(abs(value))
    p_signed = None
    p_abs = None
    if null_cosines:
        if accuracy_resid4_cos >= 0:
            p_signed = (1 + sum(1 for value in null_cosines if value >= accuracy_resid4_cos)) / (len(null_cosines) + 1)
        else:
            p_signed = (1 + sum(1 for value in null_cosines if value <= accuracy_resid4_cos)) / (len(null_cosines) + 1)
        p_abs = (1 + sum(1 for value in null_abs if value >= abs(accuracy_resid4_cos))) / (len(null_abs) + 1)

    gene = gene_rows(
        payload=payload,
        organism=organism,
        codons=codons,
        code=code,
        aa_order=aa_order,
        syn_columns=syn_columns,
        trna_direction=trna_direction,
        f3_direction=f3_direction,
        usage_direction=usage_direction,
        accuracy_perp_direction=acc_perp_direction,
    )
    gene_data, gene_summary = gene
    y_gene, blocks, rank_controls_gene = residualize_target_and_blocks(
        y=[float(value) for value in gene_data["y"]],
        blocks={"base": gene_data["base"], "accuracy": gene_data["accuracy"]},  # type: ignore[arg-type]
        controls=gene_data["controls"],  # type: ignore[arg-type]
    )
    folds = deterministic_folds(len(y_gene), f"{SEED}|{organism}|gene|folds", FOLD_COUNT)
    gene_increment = cv_increment(blocks["base"], append_columns(blocks["base"], blocks["accuracy"]), y_gene, folds)

    resid4_r2, resid4_slope = cv_r2_fixed_direction(syn_resid, y_resid, d_resid4, folds)
    acc_r2, acc_slope = cv_r2_fixed_direction(syn_resid, y_resid, acc_perp_direction, folds)
    three_r2, _three_slopes, three_cv_summary = fixed_basis_cv_r2(syn_resid, y_resid, three_basis, folds)
    accuracy_plus_basis = three_basis + [acc_perp_direction]
    accuracy_plus_r2, _plus_slopes, plus_cv_summary = fixed_basis_cv_r2(syn_resid, y_resid, accuracy_plus_basis, folds)

    structural = analyze_structural_split(
        organism=organism,
        rows=gene_data,
        order_by_protein=structural_order_index(DATA_DIR / f"structural_order_{organism}.json", organism)[0],
    )

    return {
        "organism": organism,
        "status": "computed",
        "domain": organism_domain(organism),
        "n_join": n_join,
        "gc3": gc3,
        "accuracy_resid4_cos": accuracy_resid4_cos,
        "accuracy_resid4_abs_cos": abs(accuracy_resid4_cos),
        "accuracy_perp_direction": acc_perp_direction,
        "d_resid4_direction": d_resid4,
        "d_resid4_held_out_r2": resid4_r2,
        "d_resid4_slope": resid4_slope,
        "accuracy_fixed_direction_held_out_r2": acc_r2,
        "accuracy_fixed_direction_slope": acc_slope,
        "three_axis_held_out_r2": three_r2,
        "three_plus_accuracy_held_out_r2": accuracy_plus_r2,
        "three_plus_accuracy_delta_r2": accuracy_plus_r2 - three_r2,
        "gene_accuracy_increment": gene_increment,
        "gene_rows": gene_summary,
        "rank_controls_gene": rank_controls_gene,
        "rank_controls_syn": rank_controls_syn,
        "rank_controls_y": rank_controls_y,
        "fit_summary": fit_summary,
        "captured_fraction_3indep": captured_fraction_3,
        "three_axis_projection_coefficients": projection_coefficients,
        "accuracy_score_summary": acc_summary,
        "accuracy_perp_summary": acc_perp_summary,
        "nuisance_basis_summary": nuisance_summary,
        "three_axis_basis_summary": three_summary,
        "codon_axis_null": {
            "permutation_count_requested": PERMUTATION_COUNT,
            "permutation_count_valid": len(null_cosines),
            "signed_p_same_tail": p_signed,
            "abs_p": p_abs,
            "null_signed_summary": summarize_values(null_cosines),
            "null_abs_summary": summarize_values(null_abs),
            "null_abs95": percentile_nearest_rank(null_abs, 0.95),
        },
        "data_summary": data_summary,
        "usage_axis_summary": usage_summary,
        "trna_source_summary": trna_summary,
        "tai_weight_summary": {
            **tai_summary,
            "raw_W_min": min(raw_w.values()),
            "raw_W_max": max(raw_w.values()),
            "normalized_weight_min": min(weights.values()),
            "normalized_weight_max": max(weights.values()),
        },
        "three_axis_cv_summary": three_cv_summary,
        "three_plus_accuracy_cv_summary": plus_cv_summary,
        "structural_split": structural,
    }


def organism_abundance_rows(
    *,
    payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    syn_columns: list[dict[str, object]],
) -> tuple[list[list[float]], list[float], list[list[float]], float | None, dict[str, object]]:
    joined = payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} cds_codon_abundance payload must contain joined list")
    syn_rows: list[list[float]] = []
    y_rows: list[float] = []
    controls: list[list[float]] = []
    skipped = {"non_object": 0, "nonpositive_abundance": 0, "invalid_length": 0, "empty_sense_codon_counts": 0}
    total_gc3_count = 0
    total_sense_count = 0
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
        syn_rows.append(synonymous_contrast_row(frequencies=frequencies, columns=syn_columns))
        y_rows.append(math.log10(abundance))
        aa_counts = {aa: 0 for aa in aa_order}
        for codon in codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
        controls.append([1.0, math.log(cds_len_nt), math.log(total), gc3] + [aa_counts[aa] / aa_total for aa in aa_order])
        total_sense_count += total
        total_gc3_count += sum(counts[codon] for codon in codons if codon[2] in {"G", "C"})
    gc3 = None if total_sense_count <= 0 else total_gc3_count / total_sense_count
    return syn_rows, y_rows, controls, gc3, {
        "n_joined_reported": payload.get("n_joined"),
        "join_hit_rate": payload.get("join_hit_rate"),
        "n_usable": len(y_rows),
        "skipped_records": skipped,
    }


def compact_organism(row: dict[str, object]) -> dict[str, object]:
    structural = row.get("structural_split")
    struct_null = row.get("codon_axis_null")
    gene_inc = row.get("gene_accuracy_increment")
    return {
        "organism": row.get("organism"),
        "domain": row.get("domain"),
        "n_join": row.get("n_join"),
        "accuracy_resid4_cos": row.get("accuracy_resid4_cos"),
        "accuracy_resid4_abs_cos": row.get("accuracy_resid4_abs_cos"),
        "codon_axis_null_abs_p": struct_null.get("abs_p") if isinstance(struct_null, dict) else None,
        "codon_axis_null_signed_p": struct_null.get("signed_p_same_tail") if isinstance(struct_null, dict) else None,
        "gene_accuracy_delta_r2": gene_inc.get("delta_r2") if isinstance(gene_inc, dict) else None,
        "three_plus_accuracy_delta_r2": row.get("three_plus_accuracy_delta_r2"),
        "d_resid4_held_out_r2": row.get("d_resid4_held_out_r2"),
        "accuracy_fixed_direction_held_out_r2": row.get("accuracy_fixed_direction_held_out_r2"),
        "structural_ordered_delta_r2": structural.get("ordered_accuracy_delta_r2") if isinstance(structural, dict) else None,
        "structural_disordered_delta_r2": structural.get("disordered_accuracy_delta_r2") if isinstance(structural, dict) else None,
        "structural_ordered_minus_disordered_delta_r2": structural.get("ordered_minus_disordered_delta_r2") if isinstance(structural, dict) else None,
        "structural_status": structural.get("status") if isinstance(structural, dict) else None,
    }


def aggregate_verdict(computed: list[dict[str, object]]) -> tuple[str, dict[str, object], dict[str, object]]:
    cosines = [float(row["accuracy_resid4_cos"]) for row in computed]
    abs_cosines = [abs(value) for value in cosines]
    signed_p_values = [
        float(null["signed_p_same_tail"])
        for row in computed
        if isinstance((null := row.get("codon_axis_null")), dict) and finite_numeric(null.get("signed_p_same_tail"))
    ]
    abs_p_values = [
        float(null["abs_p"])
        for row in computed
        if isinstance((null := row.get("codon_axis_null")), dict) and finite_numeric(null.get("abs_p"))
    ]
    signed_positive = sum(1 for value in cosines if value > EPS)
    signed_negative = sum(1 for value in cosines if value < -EPS)
    dominant_sign = "positive" if signed_positive >= signed_negative else "negative"
    same_sign_count = signed_positive if dominant_sign == "positive" else signed_negative
    codon_axis_pass = (
        len(computed) >= MIN_COMPLETE_ORGANISMS
        and same_sign_count >= math.ceil(0.7 * len(computed))
        and median(abs_cosines) is not None
        and float(median(abs_cosines)) > 0.15
        and len(abs_p_values) == len(computed)
        and median(abs_p_values) is not None
        and float(median(abs_p_values)) <= ALPHA
    )

    gene_deltas = [
        float(inc["delta_r2"])
        for row in computed
        if isinstance((inc := row.get("gene_accuracy_increment")), dict) and finite_numeric(inc.get("delta_r2"))
    ]
    three_deltas = [float(row["three_plus_accuracy_delta_r2"]) for row in computed if finite_numeric(row.get("three_plus_accuracy_delta_r2"))]
    gene_sign = sign_test_greater(gene_deltas)
    gene_pass = (
        len(gene_deltas) >= MIN_COMPLETE_ORGANISMS
        and mean(gene_deltas) is not None
        and float(mean(gene_deltas)) > 0.0
        and gene_sign.get("p_greater") is not None
        and float(gene_sign["p_greater"]) <= ALPHA
    )

    structural_rows = [
        row
        for row in computed
        if isinstance(row.get("structural_split"), dict)
        and row["structural_split"].get("status") == "computed"  # type: ignore[index,union-attr]
        and finite_numeric(row["structural_split"].get("ordered_minus_disordered_delta_r2"))  # type: ignore[index,union-attr]
    ]
    structural_diffs = [float(row["structural_split"]["ordered_minus_disordered_delta_r2"]) for row in structural_rows]  # type: ignore[index]
    structural_ordered = [float(row["structural_split"]["ordered_accuracy_delta_r2"]) for row in structural_rows]  # type: ignore[index]
    structural_disordered = [float(row["structural_split"]["disordered_accuracy_delta_r2"]) for row in structural_rows]  # type: ignore[index]
    structural_sign = sign_test_greater(structural_diffs)
    structural_pass = (
        len(structural_diffs) >= MIN_STRUCTURAL_ORGANISMS
        and mean(structural_diffs) is not None
        and float(mean(structural_diffs)) > 0.0
        and sum(1 for value in structural_diffs if value > EPS) >= max(1, len(structural_diffs))
    )

    pass_count = sum([codon_axis_pass, gene_pass, structural_pass])
    if pass_count == 3:
        verdict = "fourth_axis_is_translation_accuracy"
    elif pass_count >= 1:
        verdict = "partial"
    else:
        verdict = "not_accuracy"
    checks = {
        "accuracy_score_computed": {
            "passed": len(computed) >= MIN_COMPLETE_ORGANISMS,
            "organisms_computed": len(computed),
            "minimum": MIN_COMPLETE_ORGANISMS,
            "definition": "Route-C dos-Reis tAI/tGCN W_codon versus one-mismatch missense near-cognate W weighted by Grantham distance, within-family centered",
        },
        "accuracy_vs_resid4_alignment": {
            "passed": codon_axis_pass,
            "dominant_sign": dominant_sign,
            "same_sign_count": same_sign_count,
            "cosine_summary": summarize_values(cosines),
            "abs_cosine_summary": summarize_values(abs_cosines),
            "signed_null_p_summary": summarize_values(signed_p_values),
            "abs_null_p_summary": summarize_values(abs_p_values),
            "gate": ">=70% cross-organism same sign, median abs cosine > 0.15, median within-family codon-label permutation abs-p <= 0.05",
        },
        "abundance_heldout_increment": {
            "passed": gene_pass,
            "delta_r2_summary": summarize_values(gene_deltas),
            "three_axis_plus_accuracy_delta_summary": summarize_values(three_deltas),
            "sign_test_greater_than_zero": gene_sign,
            "gate": "positive cross-organism held-out delta R2 after controls and known codon axes, sign-test p<=0.05",
        },
        "ordered_disordered_accuracy_gradient": {
            "passed": structural_pass,
            "structural_organisms": len(structural_diffs),
            "ordered_delta_summary": summarize_values(structural_ordered),
            "disordered_delta_summary": summarize_values(structural_disordered),
            "ordered_minus_disordered_summary": summarize_values(structural_diffs),
            "sign_test_greater_than_zero": structural_sign,
            "gate": "structural_order organisms show ordered accuracy delta > disordered delta; per-protein structural_order median split",
        },
        "fourth_mechanism_accuracy_verdict": {
            "passed": verdict in {"fourth_axis_is_translation_accuracy", "partial", "not_accuracy"},
            "verdict": verdict,
            "passed_gate_count": pass_count,
            "required_for_identify": ["accuracy_vs_resid4_alignment", "abundance_heldout_increment", "ordered_disordered_accuracy_gradient"],
        },
    }
    aggregate = {
        "codon_axis": checks["accuracy_vs_resid4_alignment"],
        "gene_abundance": checks["abundance_heldout_increment"],
        "structural_gradient": checks["ordered_disordered_accuracy_gradient"],
        "verdict": verdict,
    }
    return verdict, checks, aggregate


def main() -> None:
    try:
        if not DATA_DIR.exists():
            emit("needs_data", reason="data directory missing", data_dir=str(DATA_DIR))
        code = standard_code()
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        aa_order = standard_amino_acids(code, codons)
        fibers = fibers_for(code, codons)
        syn_columns = synonymous_contrast_columns(fibers=fibers)
        f3_projected = project_syn(q_vectors(codons)[F3_COORDINATE], fibers)
        f3_direction = f3_contrast_direction(syn_columns=syn_columns, f3_projected=f3_projected)
        gc_dir = gc_direction(syn_columns)
        if f3_direction is None or gc_dir is None or len(syn_columns) != 41:
            emit(
                "failed",
                reason="could not construct required codon contrast axes",
                checks={
                    "accuracy_score_computed": {"passed": False},
                    "accuracy_vs_resid4_alignment": {"passed": False},
                    "fourth_mechanism_accuracy_verdict": {"passed": False},
                },
                synonymous_design_columns=len(syn_columns),
            )

        per_organism = [
            analyze_organism(
                organism=organism,
                code=code,
                codons=codons,
                aa_order=aa_order,
                fibers=fibers,
                syn_columns=syn_columns,
                f3_direction=f3_direction,
                gc_dir=gc_dir,
            )
            for organism in ORGANISMS
        ]
        computed = [row for row in per_organism if row.get("status") == "computed"]
        if len(computed) < MIN_COMPLETE_ORGANISMS:
            emit(
                "needs_data",
                reason="complete CDS/tRNA/proteomics-style abundance intersection below gate",
                seed=SEED,
                fold_count=FOLD_COUNT,
                organisms_requested=len(ORGANISMS),
                organisms_computed=len(computed),
                min_complete_organisms=MIN_COMPLETE_ORGANISMS,
                checks={
                    "accuracy_score_computed": {"passed": False, "organisms_computed": len(computed), "minimum": MIN_COMPLETE_ORGANISMS},
                    "accuracy_vs_resid4_alignment": {"passed": False},
                    "fourth_mechanism_accuracy_verdict": {"passed": False},
                },
                organisms_needs_data=[row for row in per_organism if row.get("status") != "computed"],
            )
        verdict, checks, aggregate = aggregate_verdict(computed)
        emit(
            "passed",
            conclusion=verdict,
            seed=SEED,
            fold_count=FOLD_COUNT,
            permutation_count=PERMUTATION_COUNT,
            organisms_requested=len(ORGANISMS),
            organisms_computed=len(computed),
            synonymous_design_columns=len(syn_columns),
            payload={
                "per_organism": [compact_organism(row) for row in sorted(computed, key=lambda item: str(item["organism"]))],
                "aggregate": aggregate,
                "organisms_needs_data": [row for row in per_organism if row.get("status") != "computed"],
            },
            controls_used={
                "codon_axis_space": "41 synonymous contrast columns, one reference contrast basis per synonymous family",
                "accuracy_score": "log cognate dos-Reis W divided by one-mismatch missense near-cognate W weighted by Grantham distance; then synonymous-family centered",
                "accuracy_perp": "Accuracy contrast residualized against tAI, f3_stress, usage-frequency, GC3, and minimum dos-Reis wobble-penalty class",
                "d_resid4": "Route-S abundance d_opt residual after span{d_tRNA,d_f3,d_usage}; d_resid4 not used to fit Accuracy",
                "abundance_controls": ["intercept", "log(cds_len_nt)", "log(total_sense_codons)", "GC3", "20 amino-acid composition fractions"],
                "gene_increment_base": "d_tRNA + d_f3 + d_usage gene scores after residualizing target/readouts against controls",
                "gene_increment_full": "base plus Accuracy^perp gene score",
                "structural_split": "per-protein structural_order median split where structural_order payload exists; not per-residue ordered/disordered sequence annotation",
            },
            checks=checks,
            caveats=[
                "observational held-out prediction and axis alignment do not establish causal translation-error selection",
                "tRNA gene copy and dos-Reis wobble weights proxy decoding supply, not charged tRNA abundance or ribosome error rates",
                "Grantham distances are a standard biochemical severity table, not inferred from these abundance data",
                "structural-order interaction uses available per-protein AlphaFold-derived structural_order proxy; no per-residue ordered/disordered CDS segmentation was present in local payloads",
                "no phylogenetic comparative correction is applied",
                "verdict is conservative: identify requires codon-axis alignment/null, held-out abundance increment, and ordered>disordered structural gradient",
            ],
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit(
            "failed",
            reason=f"{type(exc).__name__}: {exc}",
            seed=SEED,
            checks={
                "accuracy_score_computed": {"passed": False},
                "accuracy_vs_resid4_alignment": {"passed": False},
                "fourth_mechanism_accuracy_verdict": {"passed": False},
            },
        )


if __name__ == "__main__":
    main()

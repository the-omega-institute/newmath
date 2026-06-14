#!/usr/bin/env python3
"""Test whether Route-S abundance d_resid4 is the marginal shadow of codon-pair bias."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import random
import sys
import types
from typing import Any


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

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

    def _tai_first_two_positions_match(codon: str, anticodon: str) -> bool:
        return tai_shim.RNA_COMPLEMENT.get(anticodon[2]) == codon[0] and tai_shim.RNA_COMPLEMENT.get(anticodon[1]) == codon[1]

    def _tai_effective_wobble_base(aa_label: str, anticodon: str) -> str:
        wobble = anticodon[0]
        if wobble == "A":
            return "I"
        if aa_label == "Ile2" and anticodon == "CAU":
            return "L"
        return wobble

    def _tai_wobble_penalty(wobble: str, codon_third: str) -> float | None:
        if tai_shim.RNA_COMPLEMENT.get(wobble) == codon_third:
            return 0.0
        return tai_shim.DOS_REIS_2004_WOBBLE_S.get((wobble, codon_third))

    def _tai_codon_w_values(*_args: object, **_kwargs: object) -> tuple[dict[str, float], dict[str, float], list[dict[str, object]]]:
        raise RuntimeError("import shim only; Route N codon_w_values is used")

    tai_shim.first_two_positions_match = _tai_first_two_positions_match
    tai_shim.effective_wobble_base = _tai_effective_wobble_base
    tai_shim.wobble_penalty = _tai_wobble_penalty
    tai_shim.codon_w_values = _tai_codon_w_values
    sys.modules["_tai"] = tai_shim

from run_b_star_q6_f3_stress_cross_organism_powered import (  # noqa: E402
    F3_COORDINATE,
    controls_for_counts,
    deterministic_folds,
    vector_dot,
)
from run_b_star_q6_f3_stress_strength_driver_powered import (  # noqa: E402
    cv_r2_multivariate,
    synonymous_contrast_columns,
    synonymous_contrast_row,
)
from run_b_star_q6_optimal_codon_conservation_powered import f3_contrast_direction  # noqa: E402
from run_b_star_q6_optimality_axis_sufficiency_powered import (  # noqa: E402
    orthonormal_basis,
    usage_frequency_axis,
)
from run_b_star_q6_protein_omics_survival_powered import (  # noqa: E402
    codon_counts_rna,
    matrix_column,
    orthonormal_basis_from_columns,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_third_axis_identity_powered import contrast_direction_from_codon_values  # noqa: E402
from run_b_star_q6_translation_mediation_powered import MIN_PROTEINS_PER_ORGANISM  # noqa: E402
from run_b_star_q6_translation_survival_powered import (  # noqa: E402
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)
from run_b_star_q6_universal_core_is_trna_adaptation_powered import (  # noqa: E402
    codon_w_values,
    load_trna_records,
    trna_contrast_direction,
)
from run_b_star_q6_universal_optimal_residual_axis_powered import (  # noqa: E402
    cosine,
    fit_optimal_direction,
    load_json,
    mean,
    median,
    unit_vector,
    vector_norm,
)
from run_b_star_q6_universal_optimal_two_axis_closure_powered import residual_after_basis  # noqa: E402


EXPERIMENT_ID = "b_star_q6_fourth_mechanism_codon_pair_powered"
CLAIM_ID = "h3.cross_layer_relation.fourth_mechanism_identity.b_star_q6_codon_pair_powered"

FOLD_COUNT = 5
SHUFFLE_NULL_N = 50
EPS = 1e-12
MIN_STRONG_ABS_COS = 0.35
MIN_PARTIAL_ABS_COS = 0.18
PRIMARY_ORGANISM = "saccharomyces_cerevisiae"
ORGANISMS = [
    {"organism": "saccharomyces_cerevisiae", "label": "Saccharomyces cerevisiae"},
    {"organism": "escherichia_coli_k12_mg1655", "label": "Escherichia coli K-12 MG1655"},
]
SEED = f"sha256:{hashlib.sha256(EXPERIMENT_ID.encode('utf-8')).hexdigest()}"


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def finite_numeric(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def numeric(value: object, field: str) -> float:
    if not finite_numeric(value):
        raise ValueError(f"{field} must be finite numeric")
    return float(value)


def stable_int(material: str) -> int:
    return int.from_bytes(hashlib.sha256(material.encode("utf-8")).digest()[:8], "big")


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def summarize_values(values: list[float]) -> dict[str, object]:
    if not values:
        return {"n": 0, "mean": None, "median": None, "min": None, "max": None, "positive_count": 0, "negative_count": 0}
    return {
        "n": len(values),
        "mean": mean(values),
        "median": median(values),
        "min": min(values),
        "max": max(values),
        "positive_count": sum(1 for value in values if value > EPS),
        "negative_count": sum(1 for value in values if value < -EPS),
    }


def percentile_nearest_rank(values: list[float], probability: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def compact_direction(direction: list[float], syn_columns: list[dict[str, object]], limit: int = 8) -> list[dict[str, object]]:
    rows = []
    for index, value in enumerate(direction):
        column = syn_columns[index]
        rows.append(
            {
                "contrast": f"{column['aa']}:{column['positive_codon']}>{column['negative_codon']}",
                "loading": value,
            }
        )
    return sorted(rows, key=lambda row: abs(float(row["loading"])), reverse=True)[:limit]


def ordered_records(payload: dict[str, object], organism: str, codons: list[str], code: dict[str, str]) -> tuple[list[dict[str, object]], dict[str, object]]:
    raw_records = payload.get("cds")
    if not isinstance(raw_records, list):
        raise ValueError(f"{organism} ordered CDS payload must contain cds list")
    sense = set(codons)
    records: list[dict[str, object]] = []
    skipped = {"non_object": 0, "missing_gene_id": 0, "too_short_after_sense_filter": 0}
    for row_index, item in enumerate(raw_records):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        gene_id = item.get("gene_id")
        raw_codons = item.get("codons")
        if not isinstance(gene_id, str) or not gene_id:
            skipped["missing_gene_id"] += 1
            continue
        if not isinstance(raw_codons, list):
            raise ValueError(f"{organism}.cds[{row_index}].codons must be list")
        seq = [dna_to_rna(str(codon)) for codon in raw_codons if dna_to_rna(str(codon)) in sense]
        if len(seq) < 2:
            skipped["too_short_after_sense_filter"] += 1
            continue
        records.append({"gene_id": gene_id, "codons": seq})
    return records, {
        "n_ordered_payload_records": len(raw_records),
        "n_ordered_usable_sense_sequences": len(records),
        "skipped_ordered_records": skipped,
        "ordered_payload_n_cds": payload.get("n_cds"),
    }


def compute_codon_pair_model(
    records: list[dict[str, object]],
    *,
    codons: list[str],
    code: dict[str, str],
    fibers: dict[str, list[str]],
    syn_columns: list[dict[str, object]],
) -> dict[str, object]:
    codon_counts = {codon: 0 for codon in codons}
    aa_counts: dict[str, int] = {}
    pair_counts: dict[tuple[str, str], int] = {}
    aa_pair_counts: dict[tuple[str, str], int] = {}
    total_codons = 0
    total_pairs = 0
    for record in records:
        seq = record["codons"]
        if not isinstance(seq, list):
            continue
        for codon in seq:
            codon_s = str(codon)
            aa = code[codon_s]
            codon_counts[codon_s] += 1
            aa_counts[aa] = aa_counts.get(aa, 0) + 1
            total_codons += 1
        for left, right in zip(seq, seq[1:]):
            left_s = str(left)
            right_s = str(right)
            pair = (left_s, right_s)
            aa_pair = (code[left_s], code[right_s])
            pair_counts[pair] = pair_counts.get(pair, 0) + 1
            aa_pair_counts[aa_pair] = aa_pair_counts.get(aa_pair, 0) + 1
            total_pairs += 1
    if total_pairs <= 0 or total_codons <= 0:
        raise ValueError("ordered sequences expose no sense codon pairs")

    pair_scores: dict[tuple[str, str], float] = {}
    missing_expected = 0
    for left in codons:
        left_aa = code[left]
        left_cond = codon_counts[left] / aa_counts[left_aa] if aa_counts.get(left_aa, 0) > 0 else 0.0
        for right in codons:
            right_aa = code[right]
            aa_pair = (left_aa, right_aa)
            observed = pair_counts.get((left, right), 0) / total_pairs
            expected = (
                (aa_pair_counts.get(aa_pair, 0) / total_pairs)
                * left_cond
                * (codon_counts[right] / aa_counts[right_aa] if aa_counts.get(right_aa, 0) > 0 else 0.0)
            )
            if observed <= 0.0 or expected <= 0.0:
                missing_expected += 1
                pair_scores[(left, right)] = 0.0
            else:
                pair_scores[(left, right)] = math.log(observed / expected)

    marginal = {codon: 0.0 for codon in codons}
    marginal_weight = {codon: 0 for codon in codons}
    for (left, right), count in pair_counts.items():
        score = pair_scores[(left, right)]
        marginal[left] += count * score
        marginal[right] += count * score
        marginal_weight[left] += count
        marginal_weight[right] += count
    for codon in codons:
        if marginal_weight[codon] > 0:
            marginal[codon] /= marginal_weight[codon]
    marginal_projected = project_syn(marginal, fibers)
    marginal_direction = contrast_direction_from_codon_values(marginal_projected, syn_columns)
    if marginal_direction is None:
        raise ValueError("codon-pair marginal projection collapsed to zero in synonymous contrast space")

    return {
        "pair_scores": pair_scores,
        "marginal_codon_favorability": marginal_projected,
        "marginal_direction": marginal_direction,
        "summary": {
            "definition": "CPS(c1,c2)=ln[observed codon-pair frequency / expected frequency from amino-acid-pair frequency and within-amino-acid single-codon frequencies]",
            "total_sense_codons": total_codons,
            "total_sense_adjacent_pairs": total_pairs,
            "observed_distinct_codon_pairs": len(pair_counts),
            "observed_distinct_amino_acid_pairs": len(aa_pair_counts),
            "all_possible_sense_codon_pairs": len(codons) * len(codons),
            "pair_scores_with_zero_observed_or_expected": missing_expected,
            "marginal_top_abs_loadings": compact_direction(marginal_direction, syn_columns),
        },
    }


def cpb_score_for_sequence(seq: list[str], pair_scores: dict[tuple[str, str], float]) -> float | None:
    total = 0.0
    n = 0
    for left, right in zip(seq, seq[1:]):
        total += pair_scores[(left, right)]
        n += 1
    if n <= 0:
        return None
    return total / n


def shuffled_synonymous_sequence(seq: list[str], code: dict[str, str], rng: random.Random) -> list[str]:
    positions_by_aa: dict[str, list[int]] = {}
    codons_by_aa: dict[str, list[str]] = {}
    for index, codon in enumerate(seq):
        aa = code[codon]
        positions_by_aa.setdefault(aa, []).append(index)
        codons_by_aa.setdefault(aa, []).append(codon)
    out = list(seq)
    for aa in sorted(positions_by_aa):
        values = list(codons_by_aa[aa])
        rng.shuffle(values)
        for position, codon in zip(positions_by_aa[aa], values):
            out[position] = codon
    return out


def codon_pair_scores_by_gene(
    records: list[dict[str, object]],
    pair_scores: dict[tuple[str, str], float],
) -> tuple[dict[str, float], dict[str, object]]:
    by_gene: dict[str, float] = {}
    skipped = {"empty_pair_score": 0, "duplicate_gene_id": 0}
    for record in records:
        gene_id = str(record["gene_id"])
        seq = [str(codon) for codon in record["codons"]]  # type: ignore[index]
        score = cpb_score_for_sequence(seq, pair_scores)
        if score is None:
            skipped["empty_pair_score"] += 1
            continue
        if gene_id in by_gene:
            skipped["duplicate_gene_id"] += 1
            continue
        by_gene[gene_id] = score
    return by_gene, {"n_genes_with_cpb": len(by_gene), "skipped_cpb_records": skipped}


def record_join_keys(item: dict[str, object]) -> list[str]:
    keys: list[str] = []
    for field in ["cds_match_id", "gene_key", "locus_tag"]:
        value = item.get(field)
        if isinstance(value, str) and value:
            keys.append(value)
    protein_id = item.get("protein_id")
    if isinstance(protein_id, str) and "." in protein_id:
        keys.append(protein_id.rsplit(".", 1)[-1])
    paxdb_gene_name = item.get("paxdb_gene_name")
    if isinstance(paxdb_gene_name, str) and paxdb_gene_name:
        keys.append(paxdb_gene_name)
    seen: set[str] = set()
    out = []
    for key in keys:
        if key not in seen:
            out.append(key)
            seen.add(key)
    return out


def trna_slug_for(organism: str) -> str:
    if organism == "escherichia_coli_k12_mg1655":
        return "escherichia_coli"
    return organism


def abundance_rows_with_cpb(
    *,
    payload: dict[str, object],
    cpb_by_gene: dict[str, float],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    syn_columns: list[dict[str, object]],
) -> dict[str, object]:
    joined = payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} cds_codon_abundance payload must contain joined list")
    syn_rows: list[list[float]] = []
    y_rows: list[float] = []
    controls: list[list[float]] = []
    cpb_rows: list[float] = []
    gene_ids: list[str] = []
    skipped = {
        "non_object": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
        "no_ordered_cpb_join": 0,
    }
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
        join_key = next((key for key in record_join_keys(item) if key in cpb_by_gene), None)
        if join_key is None:
            skipped["no_ordered_cpb_join"] += 1
            continue
        counts = codon_counts_rna(item, codons, organism, row_index)
        total = sum(counts.values())
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue
        frequencies = {codon: counts[codon] / total for codon in codons}
        syn_rows.append(synonymous_contrast_row(frequencies=frequencies, columns=syn_columns))
        y_rows.append(math.log10(abundance))
        cpb_rows.append(cpb_by_gene[join_key])
        gene_ids.append(join_key)
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
    return {
        "syn_rows": syn_rows,
        "y_rows": y_rows,
        "controls": controls,
        "cpb_rows": cpb_rows,
        "gene_ids": gene_ids,
        "summary": {
            "n_joined_reported": payload.get("n_joined"),
            "join_hit_rate_reported": payload.get("join_hit_rate"),
            "n_abundance_cpb_usable": len(y_rows),
            "skipped_abundance_records": skipped,
        },
    }


def regress_cpb_increment(
    *,
    syn_rows: list[list[float]],
    y_rows: list[float],
    controls: list[list[float]],
    cpb_rows: list[float],
    three_axis_basis: list[list[float]],
    organism: str,
    material: str,
) -> dict[str, object]:
    n = len(y_rows)
    if n < MIN_PROTEINS_PER_ORGANISM:
        return {"status": "needs_data", "reason": f"join below gate n={n} < {MIN_PROTEINS_PER_ORGANISM}", "n": n}
    syn_tilde, rank_x = residualize(syn_rows, controls)
    y_tilde, rank_y = residualize([[value] for value in y_rows], controls)
    cpb_tilde_matrix, rank_cpb = residualize([[value] for value in cpb_rows], controls)
    y = matrix_column(y_tilde, 0)
    cpb = matrix_column(cpb_tilde_matrix, 0)
    y_energy = vector_dot(y, y)
    if y_energy <= EPS:
        return {"status": "needs_data", "reason": "zero residual abundance energy after controls", "n": n}
    baseline_predictors = [[vector_dot(row, direction) for direction in three_axis_basis] for row in syn_tilde]
    extended_predictors = [baseline_predictors[index] + [cpb[index]] for index in range(n)]
    folds = deterministic_folds(n, f"{SEED}|{organism}|{material}|folds", FOLD_COUNT)
    baseline_r2, baseline_cv = cv_r2_multivariate(baseline_predictors, y, folds)
    extended_r2, extended_cv = cv_r2_multivariate(extended_predictors, y, folds)
    cpb_only_r2, cpb_only_cv = cv_r2_multivariate([[value] for value in cpb], y, folds)
    return {
        "status": "computed",
        "n": n,
        "rank_controls_syn": rank_x,
        "rank_controls_y": rank_y,
        "rank_controls_cpb": rank_cpb,
        "baseline_three_axis_held_out_r2": baseline_r2,
        "extended_three_axis_plus_cpb_held_out_r2": extended_r2,
        "cpb_increment_held_out_r2": extended_r2 - baseline_r2,
        "cpb_only_after_controls_held_out_r2": cpb_only_r2,
        "baseline_cv_summary": baseline_cv,
        "extended_cv_summary": extended_cv,
        "cpb_only_cv_summary": cpb_only_cv,
        "_syn_tilde": syn_tilde,
        "_y": y,
        "_cpb_tilde": cpb,
        "_folds": folds,
        "_baseline_predictors": baseline_predictors,
    }


def residualize_column_with_basis(values: list[float], basis: list[list[float]]) -> list[float]:
    out = list(values)
    for q in basis:
        coeff = vector_dot(out, q)
        for index in range(len(out)):
            out[index] -= coeff * q[index]
    return out


def null_p_greater_equal(observed: float, null_values: list[float]) -> float | None:
    if not null_values:
        return None
    return (1 + sum(1 for value in null_values if value >= observed)) / (len(null_values) + 1)


def shuffled_cpb_for_genes(
    *,
    records_by_gene: dict[str, list[str]],
    row_gene_ids: list[str],
    pair_scores: dict[tuple[str, str], float],
    code: dict[str, str],
    organism: str,
    iteration: int,
) -> list[float]:
    out: list[float] = []
    cache: dict[str, float] = {}
    for gene_id in row_gene_ids:
        if gene_id not in cache:
            seq = records_by_gene[gene_id]
            rng = random.Random(stable_int(f"{SEED}|{organism}|shuffle|{iteration}|{gene_id}"))
            shuffled = shuffled_synonymous_sequence(seq, code, rng)
            score = cpb_score_for_sequence(shuffled, pair_scores)
            if score is None:
                score = 0.0
            cache[gene_id] = score
        out.append(cache[gene_id])
    return out


def shuffle_null_increment(
    *,
    base_fit: dict[str, object],
    controls: list[list[float]],
    row_gene_ids: list[str],
    records_by_gene: dict[str, list[str]],
    pair_scores: dict[tuple[str, str], float],
    code: dict[str, str],
    organism: str,
) -> dict[str, object]:
    if base_fit.get("status") != "computed":
        return {"status": "needs_data", "reason": "observed CPB regression was not computed"}
    baseline_predictors = base_fit.get("_baseline_predictors")
    y = base_fit.get("_y")
    folds = base_fit.get("_folds")
    baseline_r2 = base_fit.get("baseline_three_axis_held_out_r2")
    if not isinstance(baseline_predictors, list) or not isinstance(y, list) or not isinstance(folds, list) or not finite_numeric(baseline_r2):
        return {"status": "failed", "reason": "observed CPB regression internals malformed"}
    null_increments: list[float] = []
    null_extended_r2: list[float] = []
    control_basis = orthonormal_basis_from_columns(controls)
    for iteration in range(SHUFFLE_NULL_N):
        shuffled_raw = shuffled_cpb_for_genes(
            records_by_gene=records_by_gene,
            row_gene_ids=row_gene_ids,
            pair_scores=pair_scores,
            code=code,
            organism=organism,
            iteration=iteration,
        )
        shuffled_tilde = residualize_column_with_basis(shuffled_raw, control_basis)
        extended_predictors = [baseline_predictors[index] + [shuffled_tilde[index]] for index in range(len(row_gene_ids))]
        extended_r2, _summary = cv_r2_multivariate(extended_predictors, y, folds)  # type: ignore[arg-type]
        null_extended_r2.append(extended_r2)
        null_increments.append(extended_r2 - float(baseline_r2))
    return {
        "status": "computed",
        "n_shuffle": SHUFFLE_NULL_N,
        "definition": "within each gene and amino-acid class, synonymous codons are permuted across fixed amino-acid positions; amino-acid sequence and single-codon counts are preserved while adjacent codon-pair order is broken",
        "increment_distribution": {
            **summarize_values(null_increments),
            "p05": percentile_nearest_rank(null_increments, 0.05),
            "p95": percentile_nearest_rank(null_increments, 0.95),
        },
        "extended_r2_distribution": summarize_values(null_extended_r2),
        "null_increments": null_increments,
    }


def analyze_organism(
    *,
    repo: pathlib.Path,
    config: dict[str, object],
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    fibers: dict[str, list[str]],
    syn_columns: list[dict[str, object]],
    f3_direction: list[float],
) -> dict[str, object]:
    organism = str(config["organism"])
    trna_organism = trna_slug_for(organism)
    data_dir = repo / "tools/bio_reality/data"
    ordered_path = data_dir / f"cds_ordered_sequences_{organism}.json"
    cds_path = data_dir / f"cds_codon_abundance_{organism}.json"
    trna_path = data_dir / f"trna_gene_copy_{trna_organism}.json"
    gtrna_path = data_dir / f"gtrnadb_trna_all_copy_{trna_organism}.json"
    missing = [str(path.relative_to(repo)) for path in [ordered_path, cds_path] if not path.exists()]
    if missing:
        return {"organism": organism, "label": config["label"], "status": "needs_data", "reason": "missing ordered-CDS or abundance payload", "missing": missing}
    if not trna_path.exists() and not gtrna_path.exists():
        return {"organism": organism, "label": config["label"], "status": "needs_data", "reason": "missing tRNA payload for d_tRNA"}

    ordered_payload = load_json(ordered_path)
    cds_payload = load_json(cds_path)
    if not isinstance(ordered_payload, dict) or not isinstance(cds_payload, dict):
        return {"organism": organism, "label": config["label"], "status": "needs_data", "reason": "ordered-CDS or abundance payload is not a JSON object"}

    records, ordered_summary = ordered_records(ordered_payload, organism, codons, code)
    cpb_model = compute_codon_pair_model(records, codons=codons, code=code, fibers=fibers, syn_columns=syn_columns)
    pair_scores = cpb_model["pair_scores"]
    if not isinstance(pair_scores, dict):
        raise ValueError("CPB pair score table malformed")
    cpb_by_gene, cpb_gene_summary = codon_pair_scores_by_gene(records, pair_scores)  # type: ignore[arg-type]
    records_by_gene = {str(record["gene_id"]): [str(codon) for codon in record["codons"]] for record in records}  # type: ignore[index]

    trna_records, trna_summary = load_trna_records(repo, trna_organism)
    trna_summary = {**trna_summary, "trna_organism_slug_used": trna_organism}
    weights, raw_w, tai_summary = codon_w_values(code=code, codons=codons, records=trna_records)
    trna_direction = trna_contrast_direction(weights=weights, syn_columns=syn_columns)
    if trna_direction is None:
        return {"organism": organism, "label": config["label"], "status": "needs_data", "reason": "zero tRNA contrast direction", "trna_source_summary": trna_summary}
    usage_direction, usage_summary = usage_frequency_axis(
        payload=cds_payload,
        organism=organism,
        codons=codons,
        fibers=fibers,
        syn_columns=syn_columns,
    )
    if usage_direction is None:
        return {"organism": organism, "label": config["label"], "status": "needs_data", "reason": "could not construct usage-frequency direction", "usage_summary": usage_summary}
    three_axis_basis, three_axis_summary = orthonormal_basis(
        [("d_tRNA", trna_direction), ("d_f3", f3_direction), ("d_usage", usage_direction)]
    )
    if three_axis_basis is None:
        return {"organism": organism, "label": config["label"], "status": "needs_data", "reason": "could not construct three-axis basis", "three_axis_summary": three_axis_summary}

    joined = abundance_rows_with_cpb(
        payload=cds_payload,
        cpb_by_gene=cpb_by_gene,
        organism=organism,
        codons=codons,
        code=code,
        aa_order=aa_order,
        syn_columns=syn_columns,
    )
    syn_rows = joined["syn_rows"]
    y_rows = joined["y_rows"]
    controls = joined["controls"]
    cpb_rows = joined["cpb_rows"]
    row_gene_ids = joined["gene_ids"]
    if not isinstance(syn_rows, list) or not isinstance(y_rows, list) or not isinstance(controls, list) or not isinstance(cpb_rows, list) or not isinstance(row_gene_ids, list):
        raise ValueError("joined CPB abundance rows malformed")

    cpb_fit = regress_cpb_increment(
        syn_rows=syn_rows,  # type: ignore[arg-type]
        y_rows=y_rows,  # type: ignore[arg-type]
        controls=controls,  # type: ignore[arg-type]
        cpb_rows=cpb_rows,  # type: ignore[arg-type]
        three_axis_basis=three_axis_basis,
        organism=organism,
        material="observed_cpb",
    )
    if cpb_fit.get("status") != "computed":
        return {
            "organism": organism,
            "label": config["label"],
            "status": "needs_data",
            "reason": "CPB abundance regression could not be computed",
            "cpb_fit": cpb_fit,
            "ordered_summary": ordered_summary,
            "cpb_summary": cpb_gene_summary,
            "join_summary": joined["summary"],
        }

    syn_tilde = cpb_fit["_syn_tilde"]
    y = cpb_fit["_y"]
    if not isinstance(syn_tilde, list) or not isinstance(y, list):
        raise ValueError("observed fit did not retain residualized synonymous rows")
    d_opt, d_opt_summary = fit_optimal_direction(syn_tilde, y)  # type: ignore[arg-type]
    if d_opt is None:
        return {"organism": organism, "label": config["label"], "status": "needs_data", "reason": "abundance d_opt could not be fit", "fit_summary": d_opt_summary}
    d_resid4, captured_fraction, projection_coefficients = residual_after_basis(d_opt, three_axis_basis)
    if d_resid4 is None:
        return {"organism": organism, "label": config["label"], "status": "needs_data", "reason": "d_opt collapsed after Route-S three-axis projection"}
    cpb_direction = cpb_model["marginal_direction"]
    if not isinstance(cpb_direction, list):
        raise ValueError("CPB marginal direction missing")

    null = shuffle_null_increment(
        base_fit=cpb_fit,
        controls=controls,  # type: ignore[arg-type]
        row_gene_ids=[str(gene_id) for gene_id in row_gene_ids],
        records_by_gene=records_by_gene,
        pair_scores=pair_scores,  # type: ignore[arg-type]
        code=code,
        organism=organism,
    )
    observed_increment = float(cpb_fit["cpb_increment_held_out_r2"])
    null_values = null.get("null_increments") if isinstance(null, dict) else None
    p_shuffle = null_p_greater_equal(observed_increment, null_values if isinstance(null_values, list) else [])  # type: ignore[arg-type]

    compact_cpb_fit = {key: value for key, value in cpb_fit.items() if not key.startswith("_")}
    compact_null = {key: value for key, value in null.items() if key != "null_increments"} if isinstance(null, dict) else {}
    return {
        "organism": organism,
        "label": config["label"],
        "status": "computed",
        "ordered_sequence_structure": "top-level JSON object with cds list; each usable row has gene_id and ordered DNA codons; stop/non-sense codons are filtered before in-frame adjacent-pair counting",
        "data_summary": {
            **ordered_summary,
            **cpb_gene_summary,
            "abundance_join": joined["summary"],
        },
        "axes": {
            "cos_trna_f3": cosine(trna_direction, f3_direction),
            "cos_trna_usage": cosine(trna_direction, usage_direction),
            "cos_f3_usage": cosine(f3_direction, usage_direction),
            "three_axis_basis_summary": three_axis_summary,
            "usage_axis_summary": usage_summary,
            "trna_source_summary": trna_summary,
            "tai_weight_summary": {
                **tai_summary,
                "raw_w_min": min(raw_w.values()) if raw_w else None,
                "raw_w_max": max(raw_w.values()) if raw_w else None,
            },
        },
        "cpb_model": {key: value for key, value in cpb_model.items() if key != "pair_scores"},
        "abundance_d_resid4": {
            "captured_fraction_span_tRNA_f3_usage": captured_fraction,
            "projection_coefficients_orthonormal_basis": projection_coefficients,
            "top_abs_loadings": compact_direction(d_resid4, syn_columns),
        },
        "cpb_abundance_increment": compact_cpb_fit,
        "cpb_projection_alignment": {
            "cos_cpb_marginal_d_resid4": cosine(cpb_direction, d_resid4),
            "abs_cos_cpb_marginal_d_resid4": abs(cosine(cpb_direction, d_resid4)),
            "cos_cpb_marginal_d_usage": cosine(cpb_direction, usage_direction),
            "abs_cos_cpb_marginal_d_usage": abs(cosine(cpb_direction, usage_direction)),
            "cos_cpb_marginal_d_tRNA": cosine(cpb_direction, trna_direction),
            "cos_cpb_marginal_d_f3": cosine(cpb_direction, f3_direction),
            "cos_d_resid4_d_usage": cosine(d_resid4, usage_direction),
            "cos_d_resid4_d_tRNA": cosine(d_resid4, trna_direction),
            "cos_d_resid4_d_f3": cosine(d_resid4, f3_direction),
            "cpb_marginal_top_abs_loadings": compact_direction(cpb_direction, syn_columns),
        },
        "shuffle_null": {
            **compact_null,
            "p_shuffle_increment_greater_equal_observed": p_shuffle,
            "observed_increment_held_out_r2": observed_increment,
        },
        "_evidence": {
            "observed_increment": observed_increment,
            "shuffle_p_greater_equal": p_shuffle,
            "abs_cos_cpb_resid4": abs(cosine(cpb_direction, d_resid4)),
            "abs_cos_cpb_usage": abs(cosine(cpb_direction, usage_direction)),
        },
    }


def verdict(primary: dict[str, object] | None) -> tuple[str, dict[str, object]]:
    if primary is None or primary.get("status") != "computed":
        return "needs_data", {"reason": "primary yeast CPB analysis was not computed"}
    evidence = primary.get("_evidence")
    if not isinstance(evidence, dict):
        return "needs_data", {"reason": "primary yeast evidence block missing"}
    increment = float(evidence["observed_increment"])
    p_shuffle = evidence.get("shuffle_p_greater_equal")
    abs_cos_resid4 = float(evidence["abs_cos_cpb_resid4"])
    abs_cos_usage = float(evidence["abs_cos_cpb_usage"])
    shuffle_beaten = finite_numeric(p_shuffle) and float(p_shuffle) <= 0.05 and increment > 0.0
    strong_alignment = abs_cos_resid4 >= MIN_STRONG_ABS_COS and abs_cos_resid4 >= abs_cos_usage
    partial_alignment = abs_cos_resid4 >= MIN_PARTIAL_ABS_COS
    if shuffle_beaten and strong_alignment:
        return (
            "fourth_axis_is_codon_pair",
            {
                "reason": "yeast CPB adds held-out abundance R2 beyond Route-S three axes, beats the synonymous codon-shuffle null, and its single-codon marginal projection aligns dominantly with d_resid4",
                "observed_increment_held_out_r2": increment,
                "shuffle_p_greater_equal_observed": p_shuffle,
                "abs_cos_cpb_resid4": abs_cos_resid4,
                "abs_cos_cpb_usage": abs_cos_usage,
            },
        )
    if increment > 0.0 and partial_alignment:
        return (
            "partial",
            {
                "reason": "yeast CPB shows some positive abundance increment and nontrivial d_resid4 alignment, but does not satisfy the fixed joint gates for a clean codon-pair identity call",
                "observed_increment_held_out_r2": increment,
                "shuffle_p_greater_equal_observed": p_shuffle,
                "abs_cos_cpb_resid4": abs_cos_resid4,
                "abs_cos_cpb_usage": abs_cos_usage,
            },
        )
    return (
        "not_codon_pair",
        {
            "reason": "yeast CPB lacks the required combination of independent held-out abundance contribution, codon-shuffle specificity, and strong d_resid4 marginal alignment; this assay excludes codon-pair bias as the dominant fourth-axis identity under the fixed gates",
            "observed_increment_held_out_r2": increment,
            "shuffle_p_greater_equal_observed": p_shuffle,
            "abs_cos_cpb_resid4": abs_cos_resid4,
            "abs_cos_cpb_usage": abs_cos_usage,
        },
    )


def compact_organism(row: dict[str, object]) -> dict[str, object]:
    return {key: value for key, value in row.items() if key != "_evidence"}


def main() -> None:
    repo = pathlib.Path.cwd()
    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        aa_order = standard_amino_acids(code, codons)
        fibers = fibers_for(code, codons)
        syn_columns = synonymous_contrast_columns(fibers=fibers)
        f3_projected = project_syn(q_vectors(codons)[F3_COORDINATE], fibers)
        f3_direction = f3_contrast_direction(syn_columns=syn_columns, f3_projected=f3_projected)
        if f3_direction is None or len(syn_columns) != 41:
            emit(
                "failed",
                reason="could not construct 41-column f3_stress synonymous contrast direction",
                seed=SEED,
                fold_count=FOLD_COUNT,
                checks={
                    "cpb_computed": {"passed": False},
                    "cpb_increment_over_single_codon": {"passed": False},
                    "fourth_mechanism_codon_pair_verdict": {"passed": False},
                },
            )

        per_organism = [
            analyze_organism(
                repo=repo,
                config=config,
                codons=codons,
                code=code,
                aa_order=aa_order,
                fibers=fibers,
                syn_columns=syn_columns,
                f3_direction=f3_direction,
            )
            for config in ORGANISMS
        ]
        computed = [row for row in per_organism if row.get("status") == "computed"]
        primary = next((row for row in computed if row.get("organism") == PRIMARY_ORGANISM), None)
        conclusion, conclusion_summary = verdict(primary)

        primary_increment = None
        primary_alignment = None
        primary_shuffle = None
        if isinstance(primary, dict):
            inc_block = primary.get("cpb_abundance_increment")
            aln_block = primary.get("cpb_projection_alignment")
            null_block = primary.get("shuffle_null")
            if isinstance(inc_block, dict):
                primary_increment = inc_block.get("cpb_increment_held_out_r2")
            if isinstance(aln_block, dict):
                primary_alignment = aln_block.get("cos_cpb_marginal_d_resid4")
            if isinstance(null_block, dict):
                primary_shuffle = null_block.get("p_shuffle_increment_greater_equal_observed")

        cpb_computed_ok = primary is not None and primary.get("status") == "computed"
        increment_ok = finite_numeric(primary_increment)
        alignment_ok = finite_numeric(primary_alignment)
        shuffle_ok = finite_numeric(primary_shuffle)
        verdict_ok = conclusion in {"fourth_axis_is_codon_pair", "not_codon_pair", "partial"}
        checks = {
            "cpb_computed": {
                "passed": cpb_computed_ok,
                "primary_organism": PRIMARY_ORGANISM,
                "organisms_computed": len(computed),
                "synonymous_design_columns": len(syn_columns),
                "expected_synonymous_design_columns": 41,
            },
            "cpb_increment_over_single_codon": {
                "passed": increment_ok and shuffle_ok,
                "primary_organism": PRIMARY_ORGANISM,
                "baseline": "controls + Route-S three independent single-codon axes d_tRNA/d_f3/d_usage",
                "added_predictor": "per-gene ordered-sequence codon-pair-bias score",
                "held_out_fold_count": FOLD_COUNT,
                "primary_increment_held_out_r2": primary_increment,
                "primary_shuffle_p_greater_equal_observed": primary_shuffle,
            },
            "fourth_mechanism_codon_pair_verdict": {
                "passed": verdict_ok and alignment_ok,
                "conclusion": conclusion,
                **conclusion_summary,
            },
        }
        status = "passed" if all(bool(block["passed"]) for block in checks.values()) else "needs_data"

        cross_species = []
        for row in computed:
            evidence = row.get("_evidence")
            cross_species.append(
                {
                    "organism": row.get("organism"),
                    "n_abundance_cpb_usable": row.get("data_summary", {}).get("abundance_join", {}).get("n_abundance_cpb_usable") if isinstance(row.get("data_summary"), dict) else None,
                    "cpb_increment_held_out_r2": evidence.get("observed_increment") if isinstance(evidence, dict) else None,
                    "abs_cos_cpb_resid4": evidence.get("abs_cos_cpb_resid4") if isinstance(evidence, dict) else None,
                    "abs_cos_cpb_usage": evidence.get("abs_cos_cpb_usage") if isinstance(evidence, dict) else None,
                    "shuffle_p_greater_equal_observed": evidence.get("shuffle_p_greater_equal") if isinstance(evidence, dict) else None,
                }
            )

        emit(
            status,
            reason=None if status == "passed" else "primary yeast CPB computation, increment, alignment, or shuffle-null evidence was unavailable",
            seed=SEED,
            fold_count=FOLD_COUNT,
            shuffle_null_n=SHUFFLE_NULL_N,
            min_proteins_per_organism=MIN_PROTEINS_PER_ORGANISM,
            synonymous_design_columns=len(syn_columns),
            conclusion=conclusion,
            payload={
                "primary_yeast": compact_organism(primary) if isinstance(primary, dict) else None,
                "cross_species": {
                    "organisms_requested": len(ORGANISMS),
                    "organisms_computed": len(computed),
                    "summary": cross_species,
                    "cpb_increment_held_out_r2": summarize_values(
                        [float(row["cpb_increment_held_out_r2"]) for row in cross_species if finite_numeric(row.get("cpb_increment_held_out_r2"))]
                    ),
                    "abs_cos_cpb_resid4": summarize_values(
                        [float(row["abs_cos_cpb_resid4"]) for row in cross_species if finite_numeric(row.get("abs_cos_cpb_resid4"))]
                    ),
                    "power_note": "yeast is primary; E. coli is a secondary descriptive replication. No phylogenetic correction and no causal perturbation are claimed.",
                },
                "organisms": [compact_organism(row) for row in per_organism],
            },
            controls_used={
                "target": "log10(abundance_ppm) from local cds_codon_abundance joined records",
                "CPB": "mean CPS over in-frame adjacent sense codon pairs from cds_ordered_sequences; CPS expected value uses amino-acid-pair frequency and within-amino-acid single-codon frequencies from the same organism ordered CDS set",
                "baseline_single_codon_axes": [
                    "d_tRNA: dos Reis tAI direction from same-organism local tRNA/GtRNAdb records",
                    "d_f3: fixed f3_stress direction from codon_topology q_vectors, projected within synonymous families",
                    "d_usage: same-organism CDS within-synonymous-family usage-frequency direction from cds_codon_abundance",
                ],
                "d_resid4": "normalize(d_opt_abundance - Proj_span{d_tRNA,d_f3,d_usage}(d_opt_abundance)); CPB is not used to construct d_resid4",
                "held_out_increment": "5-fold deterministic CV R2 for baseline three-axis predictors versus baseline plus control-residualized CPB score; fold-local slopes are refit",
                "codon_shuffle_null": "within-gene synonymous codons are permuted among fixed amino-acid positions, preserving amino-acid sequence and single-codon composition while disrupting codon-pair order",
                "controls": [
                    "intercept",
                    "log(cds_len_nt)",
                    "log(total_sense_codons)",
                    "gc3_fraction",
                    "20 standard amino-acid composition fractions",
                ],
            },
            checks=checks,
            caveats=[
                "CPB is observational and sequence-derived; abundance association is not a causal elongation or fitness estimate",
                "The CPB marginal projection is a codon-level shadow of pair scores, not a re-fit abundance direction",
                "Held-out R2 increments can be small or negative when the second-order score does not generalize beyond the three fixed single-codon axes",
                "The shuffle null preserves single-codon counts and amino-acid sequence but changes higher-order sequence features together with codon-pair order",
                "Cross-species evidence is limited to yeast primary and E. coli secondary because ordered CDS plus matched abundance/tRNA payloads are available locally for those organisms",
            ],
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit(
            "failed",
            reason=f"{type(exc).__name__}: {exc}",
            seed=SEED,
            fold_count=FOLD_COUNT,
            checks={
                "cpb_computed": {"passed": False},
                "cpb_increment_over_single_codon": {"passed": False},
                "fourth_mechanism_codon_pair_verdict": {"passed": False},
            },
        )


if __name__ == "__main__":
    main()

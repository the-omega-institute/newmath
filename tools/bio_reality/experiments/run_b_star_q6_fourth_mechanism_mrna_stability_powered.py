#!/usr/bin/env python3
"""Identify whether the Route-S fourth optimality residual is mRNA stability."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import re
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

    def _codon_w_values(*_args: object, **_kwargs: object) -> tuple[dict[str, float], dict[str, float], list[dict[str, object]]]:
        raise RuntimeError("import shim only; Route N codon_w_values is used")

    tai_shim.first_two_positions_match = _first_two_positions_match
    tai_shim.effective_wobble_base = _effective_wobble_base
    tai_shim.wobble_penalty = _wobble_penalty
    tai_shim.codon_w_values = _codon_w_values
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
from run_b_star_q6_mrna_half_life_sqm_ecoli_powered import (  # noqa: E402
    PRIMARY_GROWTH_RATE as ECOLI_PRIMARY_GROWTH_RATE,
    half_life_by_gene_id as ecoli_half_life_by_gene_id,
)
from run_b_star_q6_mrna_half_life_sqm_human_powered import (  # noqa: E402
    consensus_indices as human_consensus_indices,
    normalize_ensembl_gene_id,
    parse_cds_gene_keys,
)
from run_b_star_q6_mrna_half_life_sqm_powered import (  # noqa: E402
    half_life_by_syst as yeast_half_life_by_syst,
    yeast_orf_from_protein_id,
)
from run_b_star_q6_optimal_codon_conservation_powered import f3_contrast_direction  # noqa: E402
from run_b_star_q6_optimality_axis_sufficiency_powered import (  # noqa: E402
    orthonormal_basis,
    usage_frequency_axis,
)
from run_b_star_q6_protein_omics_survival_powered import (  # noqa: E402
    codon_counts_rna,
    matrix_column,
    residualize,
    standard_amino_acids,
)
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
    cv_r2_fixed_direction,
    fit_optimal_direction,
    load_json,
    mean,
    median,
    unit_vector,
    vector_norm,
)
from run_b_star_q6_universal_optimal_two_axis_closure_powered import (  # noqa: E402
    fixed_basis_cv_r2,
    residual_after_basis,
)


EXPERIMENT_ID = "b_star_q6_fourth_mechanism_mrna_stability_powered"
CLAIM_ID = "h3.cross_layer_relation.fourth_mechanism_identity.b_star_q6_mrna_stability_powered"

FOLD_COUNT = 5
SEED = f"sha256:{hashlib.sha256(EXPERIMENT_ID.encode('utf-8')).hexdigest()}"
EPS = 1e-12
MIN_ALIGNMENT_STRONG = 0.35
MIN_ALIGNMENT_PARTIAL = 0.18

PRIMARY_ORGANISM = "saccharomyces_cerevisiae"
ORGANISMS = [
    {
        "organism": "saccharomyces_cerevisiae",
        "label": "Saccharomyces cerevisiae",
        "halflife_path": "mrna_half_life_saccharomyces_cerevisiae_neymotin.json",
        "te_path": "ribosome_te_saccharomyces_cerevisiae.json",
    },
    {
        "organism": "escherichia_coli_k12_mg1655",
        "label": "Escherichia coli K-12 MG1655",
        "halflife_path": "mrna_half_life_escherichia_coli_esquerre.json",
        "te_path": "ribosome_te_escherichia_coli_k12_mg1655.json",
    },
    {
        "organism": "homo_sapiens",
        "label": "Homo sapiens",
        "halflife_path": "mrna_half_life_homo_sapiens_agarwal_consensus.json",
        "te_path": "ribosome_te_homo_sapiens.json",
    },
]


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


def contrast_loadings(direction: list[float], syn_columns: list[dict[str, object]]) -> dict[str, float]:
    return {
        f"{column['aa']}:{column['positive_codon']}>{column['negative_codon']}": direction[index]
        for index, column in enumerate(syn_columns)
    }


def compact_direction(direction: list[float], syn_columns: list[dict[str, object]], limit: int = 8) -> list[dict[str, object]]:
    entries = []
    for index, value in enumerate(direction):
        column = syn_columns[index]
        entries.append(
            {
                "contrast": f"{column['aa']}:{column['positive_codon']}>{column['negative_codon']}",
                "loading": value,
            }
        )
    return sorted(entries, key=lambda item: abs(float(item["loading"])), reverse=True)[:limit]


def te_indices(payload: dict[str, object], organism: str) -> tuple[dict[str, dict[str, float]], dict[str, dict[str, float]], dict[str, object]]:
    genes = payload.get("genes")
    if not isinstance(genes, list):
        raise ValueError(f"{organism} TE payload must contain genes list")
    by_protein: dict[str, dict[str, float]] = {}
    gene_buckets: dict[str, list[dict[str, float]]] = {}
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "missing_gene_key": 0,
        "nonpositive_te": 0,
        "nonpositive_mrna": 0,
        "nonpositive_footprint": 0,
        "duplicate_protein_id": 0,
    }
    for row_index, item in enumerate(genes):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        gene_key = item.get("gene_key")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        if not isinstance(gene_key, str) or not gene_key:
            skipped["missing_gene_key"] += 1
            continue
        te = numeric(item.get("te"), f"{organism}.genes[{row_index}].te")
        mrna = numeric(item.get("mrna"), f"{organism}.genes[{row_index}].mrna")
        footprint = numeric(item.get("footprint"), f"{organism}.genes[{row_index}].footprint")
        if te <= 0.0:
            skipped["nonpositive_te"] += 1
            continue
        if mrna <= 0.0:
            skipped["nonpositive_mrna"] += 1
            continue
        if footprint <= 0.0:
            skipped["nonpositive_footprint"] += 1
            continue
        record = {"te": te, "mrna": mrna, "footprint": footprint}
        if protein_id in by_protein:
            skipped["duplicate_protein_id"] += 1
        else:
            by_protein[protein_id] = record
        normalized_gene = normalize_ensembl_gene_id(gene_key) if organism == "homo_sapiens" and gene_key.startswith("ENSG") else gene_key
        if organism == "homo_sapiens" and not normalized_gene.startswith("ENSG"):
            normalized_gene = normalized_gene.upper()
        gene_buckets.setdefault(normalized_gene, []).append(record)
    by_gene = {key: bucket[0] for key, bucket in gene_buckets.items() if len(bucket) == 1}
    return by_protein, by_gene, {
        "n_genes_with_te_reported": payload.get("n_genes_with_te"),
        "join_hit_rate_reported": payload.get("join_hit_rate"),
        "n_valid_te_by_protein": len(by_protein),
        "n_unique_unambiguous_te_gene_keys": len(by_gene),
        "n_ambiguous_te_gene_keys": sum(1 for bucket in gene_buckets.values() if len(bucket) > 1),
        "te_definition": payload.get("te_definition"),
        "study_ref": payload.get("study_ref"),
        "skipped_te_records": skipped,
    }


def half_life_indices(organism: str, payload: dict[str, object]) -> tuple[dict[str, float], dict[str, float], dict[str, object]]:
    if organism == "saccharomyces_cerevisiae":
        raw, summary = yeast_half_life_by_syst(payload)
        return {key: float(value["thalf"]) for key, value in raw.items()}, {}, summary
    if organism == "escherichia_coli_k12_mg1655":
        raw, summary = ecoli_half_life_by_gene_id(payload, ECOLI_PRIMARY_GROWTH_RATE)
        return {key: float(value["half_life"]) for key, value in raw.items()}, {}, summary
    if organism == "homo_sapiens":
        by_ensg, by_symbol, summary = human_consensus_indices(payload)
        return (
            {key: float(value["consensus_relative_half_life"]) for key, value in by_ensg.items()},
            {key: float(value["consensus_relative_half_life"]) for key, value in by_symbol.items()},
            summary,
        )
    raise ValueError(f"unsupported organism {organism}")


def gene_keys_for_cds(organism: str, item: dict[str, object]) -> tuple[str | None, str | None, str | None, str]:
    protein_id = item.get("protein_id")
    if not isinstance(protein_id, str) or not protein_id:
        return None, None, None, "missing_protein_id"
    if organism == "saccharomyces_cerevisiae":
        orf = yeast_orf_from_protein_id(protein_id)
        if orf is None:
            return protein_id, None, None, "unparseable_yeast_orf"
        return protein_id, orf, None, ""
    if organism == "escherichia_coli_k12_mg1655":
        locus_tag = item.get("cds_match_id")
        if not isinstance(locus_tag, str) or not locus_tag.startswith("b"):
            return protein_id, None, None, "missing_locus_tag"
        return protein_id, locus_tag, None, ""
    if organism == "homo_sapiens":
        header = item.get("cds_header")
        if not isinstance(header, str) or not header:
            return protein_id, None, None, "missing_cds_header"
        ensg, symbol = parse_cds_gene_keys(header)
        if ensg is None and symbol is None:
            return protein_id, None, None, "missing_gene_keys"
        return protein_id, ensg, symbol, ""
    raise ValueError(f"unsupported organism {organism}")


def row_features(
    *,
    item: dict[str, object],
    row_index: int,
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    syn_columns: list[dict[str, object]],
) -> tuple[list[float], list[float]]:
    cds_len_nt = numeric(item.get("cds_len_nt"), f"{organism}.joined[{row_index}].cds_len_nt")
    if cds_len_nt <= 0.0:
        raise ValueError("invalid_length")
    counts = codon_counts_rna(item, codons, organism, row_index)
    total = sum(counts.values())
    if total <= 0:
        raise ValueError("empty_sense_codon_counts")
    frequencies = {codon: counts[codon] / total for codon in codons}
    syn_row = synonymous_contrast_row(frequencies=frequencies, columns=syn_columns)
    controls = controls_for_counts(
        counts=counts,
        code=code,
        codons=codons,
        aa_order=aa_order,
        total=total,
        cds_len_nt=cds_len_nt,
    )
    return syn_row, controls


def joined_readout_rows(
    *,
    organism: str,
    cds_payload: dict[str, object],
    half_life_payload: dict[str, object] | None,
    te_payload: dict[str, object] | None,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    syn_columns: list[dict[str, object]],
) -> dict[str, object]:
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} cds_codon_abundance payload must contain joined list")

    half_life_primary: dict[str, float] = {}
    half_life_symbol: dict[str, float] = {}
    half_life_summary: dict[str, object] = {"available": False}
    if half_life_payload is not None:
        half_life_primary, half_life_symbol, half_life_summary = half_life_indices(organism, half_life_payload)
        half_life_summary = {"available": True, **half_life_summary}

    te_by_protein: dict[str, dict[str, float]] = {}
    te_by_gene: dict[str, dict[str, float]] = {}
    te_summary: dict[str, object] = {"available": False}
    if te_payload is not None:
        te_by_protein, te_by_gene, te_summary = te_indices(te_payload, organism)
        te_summary = {"available": True, **te_summary}

    readouts = {
        "abundance": {"x": [], "y": [], "z": [], "ids": []},
        "halflife": {"x": [], "y": [], "z": [], "ids": []},
        "TE": {"x": [], "y": [], "z": [], "ids": []},
        "mRNA_level": {"x": [], "y": [], "z": [], "ids": []},
    }
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "unparseable_yeast_orf": 0,
        "missing_locus_tag": 0,
        "missing_cds_header": 0,
        "missing_gene_keys": 0,
        "duplicate_stable_id": 0,
        "nonpositive_abundance": 0,
        "no_half_life_match": 0,
        "nonpositive_half_life": 0,
        "no_te_match": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }
    join_sources = {
        "halflife_primary_key": 0,
        "halflife_gene_symbol_fallback": 0,
        "te_protein_id": 0,
        "te_gene_key": 0,
    }
    seen: set[str] = set()

    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id, primary_key, symbol_key, error = gene_keys_for_cds(organism, item)
        if error:
            skipped[error] += 1
            continue
        stable_id = primary_key or f"symbol:{symbol_key}"
        if stable_id is None:
            skipped["missing_gene_keys"] += 1
            continue
        if stable_id in seen:
            skipped["duplicate_stable_id"] += 1
            continue
        abundance = numeric(item.get("abundance_ppm"), f"{organism}.joined[{row_index}].abundance_ppm")
        if abundance <= 0.0:
            skipped["nonpositive_abundance"] += 1
            continue
        try:
            syn_row, z_row = row_features(
                item=item,
                row_index=row_index,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                syn_columns=syn_columns,
            )
        except ValueError as exc:
            key = str(exc)
            if key in skipped:
                skipped[key] += 1
                continue
            raise

        readouts["abundance"]["x"].append(syn_row)  # type: ignore[index,union-attr]
        readouts["abundance"]["y"].append(math.log10(abundance))  # type: ignore[index,union-attr]
        readouts["abundance"]["z"].append(z_row)  # type: ignore[index,union-attr]
        readouts["abundance"]["ids"].append(stable_id)  # type: ignore[index,union-attr]

        if half_life_payload is not None:
            half_life = half_life_primary.get(primary_key) if primary_key is not None else None
            if half_life is not None:
                join_sources["halflife_primary_key"] += 1
            elif symbol_key is not None:
                half_life = half_life_symbol.get(symbol_key)
                if half_life is not None:
                    join_sources["halflife_gene_symbol_fallback"] += 1
            if half_life is None:
                skipped["no_half_life_match"] += 1
            elif half_life <= 0.0:
                skipped["nonpositive_half_life"] += 1
            else:
                readouts["halflife"]["x"].append(syn_row)  # type: ignore[index,union-attr]
                readouts["halflife"]["z"].append(z_row)  # type: ignore[index,union-attr]
                readouts["halflife"]["ids"].append(stable_id)  # type: ignore[index,union-attr]
                if organism == "homo_sapiens":
                    readouts["halflife"]["y"].append(half_life)  # type: ignore[index,union-attr]
                else:
                    readouts["halflife"]["y"].append(math.log10(half_life))  # type: ignore[index,union-attr]

        if te_payload is not None:
            te_record = te_by_protein.get(str(protein_id))
            if te_record is not None:
                join_sources["te_protein_id"] += 1
            else:
                if organism == "homo_sapiens":
                    gene_key = primary_key or (symbol_key.upper() if symbol_key else None)
                else:
                    gene_key = primary_key
                te_record = te_by_gene.get(str(gene_key)) if gene_key is not None else None
                if te_record is not None:
                    join_sources["te_gene_key"] += 1
            if te_record is None:
                skipped["no_te_match"] += 1
            else:
                readouts["TE"]["x"].append(syn_row)  # type: ignore[index,union-attr]
                readouts["TE"]["y"].append(math.log10(te_record["te"]))  # type: ignore[index,union-attr]
                readouts["TE"]["z"].append(z_row)  # type: ignore[index,union-attr]
                readouts["TE"]["ids"].append(stable_id)  # type: ignore[index,union-attr]
                readouts["mRNA_level"]["x"].append(syn_row)  # type: ignore[index,union-attr]
                readouts["mRNA_level"]["y"].append(math.log10(te_record["mrna"]))  # type: ignore[index,union-attr]
                readouts["mRNA_level"]["z"].append(z_row)  # type: ignore[index,union-attr]
                readouts["mRNA_level"]["ids"].append(stable_id)  # type: ignore[index,union-attr]
        seen.add(stable_id)

    return {
        "readouts": readouts,
        "data_summary": {
            "n_cds_joined_reported": cds_payload.get("n_joined"),
            "cds_join_hit_rate_reported": cds_payload.get("join_hit_rate"),
            "n_stable_ids_seen": len(seen),
            "half_life_summary": half_life_summary,
            "te_summary": te_summary,
            "join_sources": join_sources,
            "skipped_cds_records": skipped,
        },
    }


def fit_readout_direction(
    *,
    readout: str,
    x_raw: list[list[float]],
    y_raw: list[float],
    z_raw: list[list[float]],
    organism: str,
) -> dict[str, object]:
    n = len(y_raw)
    base = {"readout": readout, "organism": organism, "status": "needs_data", "n_join": n}
    if n < MIN_PROTEINS_PER_ORGANISM:
        return {**base, "reason": f"join below gate n={n} < {MIN_PROTEINS_PER_ORGANISM}"}
    x_tilde, rank_x = residualize(x_raw, z_raw)
    y_tilde, rank_y = residualize([[value] for value in y_raw], z_raw)
    y = matrix_column(y_tilde, 0)
    y_energy = vector_dot(y, y)
    if y_energy <= EPS:
        return {**base, "reason": "zero residual readout energy after controls", "rank_controls_x": rank_x, "rank_controls_y": rank_y}
    direction, fit_summary = fit_optimal_direction(x_tilde, y)
    if direction is None:
        return {
            **base,
            "reason": str(fit_summary.get("reason", "could not fit optimal direction")),
            "rank_controls_x": rank_x,
            "rank_controls_y": rank_y,
            "fit_summary": fit_summary,
        }
    folds = deterministic_folds(n, f"{SEED}|{organism}|{readout}|folds", FOLD_COUNT)
    self_r2, self_slope = cv_r2_fixed_direction(x_tilde, y, direction, folds)
    total_r2, total_cv_summary = cv_r2_multivariate(x_tilde, y, folds)
    return {
        **base,
        "status": "computed",
        "direction": direction,
        "x_tilde": x_tilde,
        "y": y,
        "folds": folds,
        "rank_controls_x": rank_x,
        "rank_controls_y": rank_y,
        "residual_readout_energy": y_energy,
        "self_direction_held_out_r2": self_r2,
        "self_direction_slope": self_slope,
        "total_syn_selection_held_out_r2": total_r2,
        "synonymous_cv_summary": total_cv_summary,
        "fit_summary": fit_summary,
    }


def fixed_direction_on_fit(fit: dict[str, object], direction: list[float]) -> tuple[float | None, float | None]:
    if fit.get("status") != "computed":
        return None, None
    x_tilde = fit.get("x_tilde")
    y = fit.get("y")
    folds = fit.get("folds")
    if not isinstance(x_tilde, list) or not isinstance(y, list) or not isinstance(folds, list):
        return None, None
    return cv_r2_fixed_direction(x_tilde, y, direction, folds)  # type: ignore[arg-type]


def decompose_direction(
    direction: list[float],
    *,
    trna_direction: list[float],
    f3_direction: list[float],
    usage_direction: list[float],
    three_axis_basis: list[list[float]],
    fit: dict[str, object],
) -> dict[str, object]:
    residual, captured_fraction, coefficients = residual_after_basis(direction, three_axis_basis)
    trna_r2, trna_slope = fixed_direction_on_fit(fit, trna_direction)
    f3_r2, f3_slope = fixed_direction_on_fit(fit, f3_direction)
    usage_r2, usage_slope = fixed_direction_on_fit(fit, usage_direction)
    three_r2 = None
    three_slopes = None
    three_cv_summary = None
    if fit.get("status") == "computed":
        x_tilde = fit.get("x_tilde")
        y = fit.get("y")
        folds = fit.get("folds")
        if isinstance(x_tilde, list) and isinstance(y, list) and isinstance(folds, list):
            three_r2, three_slopes, three_cv_summary = fixed_basis_cv_r2(x_tilde, y, three_axis_basis, folds)  # type: ignore[arg-type]
    return {
        "captured_fraction_span_tRNA_f3_usage": captured_fraction,
        "three_axis_projection_coefficients_orthonormal_basis": coefficients,
        "residual_after_three_axis_norm": 0.0 if residual is None else vector_norm(residual),
        "cos_dopt_tRNA": cosine(direction, trna_direction),
        "cos_dopt_f3": cosine(direction, f3_direction),
        "cos_dopt_usage": cosine(direction, usage_direction),
        "held_out_R2_fixed_axes": {
            "d_opt_self": fit.get("self_direction_held_out_r2"),
            "all_41_synonymous_contrasts": fit.get("total_syn_selection_held_out_r2"),
            "d_tRNA": trna_r2,
            "d_tRNA_slope": trna_slope,
            "d_f3": f3_r2,
            "d_f3_slope": f3_slope,
            "d_usage": usage_r2,
            "d_usage_slope": usage_slope,
            "span_tRNA_f3_usage": three_r2,
            "span_tRNA_f3_usage_slopes": three_slopes,
            "span_tRNA_f3_usage_cv_summary": three_cv_summary,
        },
    }


def cross_predict_matrix(fits: dict[str, dict[str, object]]) -> dict[str, dict[str, object]]:
    out: dict[str, dict[str, object]] = {}
    for source_name, source_fit in fits.items():
        if source_fit.get("status") != "computed" or not isinstance(source_fit.get("direction"), list):
            continue
        direction = source_fit["direction"]  # type: ignore[assignment]
        row: dict[str, object] = {}
        for target_name, target_fit in fits.items():
            r2, slope = fixed_direction_on_fit(target_fit, direction)  # type: ignore[arg-type]
            row[target_name] = {"held_out_r2": r2, "slope": slope}
        out[source_name] = row
    return out


def load_payload_if_exists(path: pathlib.Path) -> dict[str, object] | None:
    if not path.exists():
        return None
    payload = load_json(path)
    if not isinstance(payload, dict):
        raise ValueError(f"{path} payload must be a JSON object")
    return payload


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
    data_dir = repo / "tools/bio_reality/data"
    cds_path = data_dir / f"cds_codon_abundance_{organism}.json"
    trna_path = data_dir / f"trna_gene_copy_{organism}.json"
    gtrna_path = data_dir / f"gtrnadb_trna_all_copy_{organism}.json"
    halflife_path = data_dir / str(config["halflife_path"])
    te_path = data_dir / str(config["te_path"])
    missing_required = [str(path.relative_to(repo)) for path in [cds_path] if not path.exists()]
    if missing_required:
        return {"organism": organism, "status": "needs_data", "reason": "missing CDS codon payload", "missing_required_data": missing_required}
    if not trna_path.exists() and not gtrna_path.exists():
        return {
            "organism": organism,
            "status": "needs_data",
            "reason": "missing tRNA payload needed for d_tRNA",
            "trna_summary_exists": trna_path.exists(),
            "gtrnadb_exists": gtrna_path.exists(),
        }

    cds_payload = load_payload_if_exists(cds_path)
    half_life_payload = load_payload_if_exists(halflife_path)
    te_payload = load_payload_if_exists(te_path)
    if cds_payload is None:
        raise ValueError("CDS payload unexpectedly unavailable")

    trna_records, trna_summary = load_trna_records(repo, organism)
    weights, raw_w, tai_summary = codon_w_values(code=code, codons=codons, records=trna_records)
    trna_direction = trna_contrast_direction(weights=weights, syn_columns=syn_columns)
    if trna_direction is None:
        return {"organism": organism, "status": "needs_data", "reason": "zero tRNA contrast direction", "trna_source_summary": trna_summary}
    usage_direction, usage_summary = usage_frequency_axis(
        payload=cds_payload,
        organism=organism,
        codons=codons,
        fibers=fibers,
        syn_columns=syn_columns,
    )
    if usage_direction is None:
        return {"organism": organism, "status": "needs_data", "reason": "could not construct usage-frequency axis", "usage_axis_summary": usage_summary}
    three_axis_basis, three_axis_basis_summary = orthonormal_basis(
        [("d_tRNA", trna_direction), ("d_f3", f3_direction), ("d_usage", usage_direction)]
    )
    if three_axis_basis is None:
        return {
            "organism": organism,
            "status": "needs_data",
            "reason": "could not construct three-axis basis",
            "three_axis_basis_summary": three_axis_basis_summary,
        }

    joined = joined_readout_rows(
        organism=organism,
        cds_payload=cds_payload,
        half_life_payload=half_life_payload,
        te_payload=te_payload,
        codons=codons,
        code=code,
        aa_order=aa_order,
        syn_columns=syn_columns,
    )
    readouts = joined["readouts"]
    if not isinstance(readouts, dict):
        raise ValueError("joined readouts malformed")
    fits: dict[str, dict[str, object]] = {}
    for readout_name, rows in readouts.items():
        if not isinstance(rows, dict):
            raise ValueError(f"{organism} {readout_name} rows malformed")
        fits[readout_name] = fit_readout_direction(
            readout=str(readout_name),
            x_raw=rows["x"],  # type: ignore[arg-type]
            y_raw=rows["y"],  # type: ignore[arg-type]
            z_raw=rows["z"],  # type: ignore[arg-type]
            organism=organism,
        )

    abundance_fit = fits["abundance"]
    if abundance_fit.get("status") != "computed" or not isinstance(abundance_fit.get("direction"), list):
        return {
            "organism": organism,
            "status": "needs_data",
            "reason": "abundance d_opt could not be computed",
            "readout_fits": {key: {k: v for k, v in value.items() if k not in {"x_tilde", "y", "folds", "direction"}} for key, value in fits.items()},
            "data_summary": joined["data_summary"],
        }
    d_resid4, abundance_captured_fraction, abundance_projection_coefficients = residual_after_basis(
        abundance_fit["direction"],  # type: ignore[arg-type]
        three_axis_basis,
    )
    if d_resid4 is None:
        return {
            "organism": organism,
            "status": "needs_data",
            "reason": "abundance d_opt collapsed after Route-S three-axis projection; d_resid4 unavailable",
            "data_summary": joined["data_summary"],
        }

    decompositions: dict[str, object] = {}
    readout_axis_cosines: dict[str, object] = {}
    compact_fits: dict[str, object] = {}
    for readout_name, fit in fits.items():
        compact = {key: value for key, value in fit.items() if key not in {"x_tilde", "y", "folds", "direction"}}
        compact_fits[readout_name] = compact
        if fit.get("status") == "computed" and isinstance(fit.get("direction"), list):
            direction = fit["direction"]  # type: ignore[assignment]
            decompositions[readout_name] = decompose_direction(
                direction,  # type: ignore[arg-type]
                trna_direction=trna_direction,
                f3_direction=f3_direction,
                usage_direction=usage_direction,
                three_axis_basis=three_axis_basis,
                fit=fit,
            )
            readout_axis_cosines[readout_name] = {
                "cos_dopt_tRNA": cosine(direction, trna_direction),  # type: ignore[arg-type]
                "cos_dopt_f3": cosine(direction, f3_direction),  # type: ignore[arg-type]
                "cos_dopt_usage": cosine(direction, usage_direction),  # type: ignore[arg-type]
                "cos_dopt_resid4_abundance": cosine(direction, d_resid4),  # type: ignore[arg-type]
            }
            compact["top_abs_loadings"] = compact_direction(direction, syn_columns)  # type: ignore[arg-type]

    halflife_fit = fits["halflife"]
    halflife_alignment = None
    if halflife_fit.get("status") == "computed" and isinstance(halflife_fit.get("direction"), list):
        d_halflife = halflife_fit["direction"]  # type: ignore[assignment]
        halflife_alignment = {
            "cos_d_opt_halflife_d_resid4_abundance": cosine(d_halflife, d_resid4),  # type: ignore[arg-type]
            "abs_cos_d_opt_halflife_d_resid4_abundance": abs(cosine(d_halflife, d_resid4)),  # type: ignore[arg-type]
            "cos_d_opt_halflife_d_usage": cosine(d_halflife, usage_direction),  # type: ignore[arg-type]
            "cos_d_opt_halflife_d_tRNA": cosine(d_halflife, trna_direction),  # type: ignore[arg-type]
            "cos_d_opt_halflife_d_f3": cosine(d_halflife, f3_direction),  # type: ignore[arg-type]
            "cos_d_resid4_abundance_d_usage": cosine(d_resid4, usage_direction),
            "cos_d_resid4_abundance_d_tRNA": cosine(d_resid4, trna_direction),
            "cos_d_resid4_abundance_d_f3": cosine(d_resid4, f3_direction),
        }

    return {
        "organism": organism,
        "label": config["label"],
        "status": "computed",
        "axes": {
            "cos_trna_f3": cosine(trna_direction, f3_direction),
            "cos_trna_usage": cosine(trna_direction, usage_direction),
            "cos_f3_usage": cosine(f3_direction, usage_direction),
            "three_axis_basis_summary": three_axis_basis_summary,
            "usage_axis_summary": usage_summary,
            "trna_source_summary": trna_summary,
            "tai_weight_summary": {
                **tai_summary,
                "raw_w_min": min(raw_w.values()) if raw_w else None,
                "raw_w_max": max(raw_w.values()) if raw_w else None,
            },
        },
        "d_resid4_abundance": {
            "captured_fraction_span_tRNA_f3_usage": abundance_captured_fraction,
            "projection_coefficients_orthonormal_basis": abundance_projection_coefficients,
            "top_abs_loadings": compact_direction(d_resid4, syn_columns),
        },
        "halflife_alignment": halflife_alignment,
        "readout_fits": compact_fits,
        "readout_axis_decomposition": decompositions,
        "readout_axis_cosines": readout_axis_cosines,
        "cross_predict_held_out_r2": cross_predict_matrix(fits),
        "data_summary": joined["data_summary"],
        "_directions": {
            "d_resid4_abundance": d_resid4,
            "d_tRNA": trna_direction,
            "d_f3": f3_direction,
            "d_usage": usage_direction,
            **{
                f"d_opt_{name}": fit["direction"]
                for name, fit in fits.items()
                if fit.get("status") == "computed" and isinstance(fit.get("direction"), list)
            },
        },
    }


def compact_organism(row: dict[str, object]) -> dict[str, object]:
    out = {key: value for key, value in row.items() if key != "_directions"}
    return out


def verdict(primary_alignment: dict[str, object] | None) -> tuple[str, str]:
    if not primary_alignment:
        return "needs_data", "yeast half-life d_opt was unavailable, so the identity test could not be run"
    cos_resid4 = float(primary_alignment["cos_d_opt_halflife_d_resid4_abundance"])
    abs_cos_resid4 = abs(cos_resid4)
    abs_other = max(
        abs(float(primary_alignment["cos_d_opt_halflife_d_usage"])),
        abs(float(primary_alignment["cos_d_opt_halflife_d_tRNA"])),
        abs(float(primary_alignment["cos_d_opt_halflife_d_f3"])),
    )
    if abs_cos_resid4 >= MIN_ALIGNMENT_STRONG and abs_cos_resid4 >= abs_other:
        return (
            "fourth_axis_is_mrna_stability",
            "yeast d_opt_halflife is strongly aligned with abundance d_resid4 and not weaker than its alignment to the named axes",
        )
    if abs_cos_resid4 >= MIN_ALIGNMENT_PARTIAL:
        return (
            "partial",
            "yeast d_opt_halflife has nontrivial alignment with abundance d_resid4, but it is not a clean dominant-axis identification under the fixed gates",
        )
    return (
        "fourth_axis_not_mrna_stability",
        "yeast d_opt_halflife has low alignment with abundance d_resid4 under the fixed gates, so this excludes mRNA stability as the dominant fourth-axis identity in this assay",
    )


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
                    "readout_optimal_directions_computed": {"passed": False},
                    "halflife_vs_resid4_alignment": {"passed": False},
                    "fourth_mechanism_verdict": {"passed": False},
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
        primary_alignment = primary.get("halflife_alignment") if isinstance(primary, dict) else None
        primary_alignment_dict = primary_alignment if isinstance(primary_alignment, dict) else None
        conclusion, conclusion_reason = verdict(primary_alignment_dict)

        readout_optimal_directions_ok = (
            primary is not None
            and isinstance(primary.get("readout_fits"), dict)
            and all(
                isinstance(primary["readout_fits"].get(name), dict) and primary["readout_fits"][name].get("status") == "computed"  # type: ignore[index]
                for name in ["abundance", "halflife", "TE", "mRNA_level"]
            )
        )
        alignment_ok = primary_alignment_dict is not None and finite_numeric(
            primary_alignment_dict.get("cos_d_opt_halflife_d_resid4_abundance")
        )
        verdict_ok = conclusion in {"fourth_axis_is_mrna_stability", "fourth_axis_not_mrna_stability", "partial"}
        checks = {
            "readout_optimal_directions_computed": {
                "passed": readout_optimal_directions_ok,
                "primary_organism": PRIMARY_ORGANISM,
                "required_readouts": ["mRNA-half-life", "TE", "mRNA-level", "abundance"],
                "synonymous_design_columns": len(syn_columns),
                "expected_synonymous_design_columns": 41,
            },
            "halflife_vs_resid4_alignment": {
                "passed": alignment_ok,
                "primary_organism": PRIMARY_ORGANISM,
                "alignment": primary_alignment_dict,
                "strong_abs_cos_threshold": MIN_ALIGNMENT_STRONG,
                "partial_abs_cos_threshold": MIN_ALIGNMENT_PARTIAL,
            },
            "fourth_mechanism_verdict": {
                "passed": verdict_ok,
                "conclusion": conclusion,
                "reason": conclusion_reason,
            },
        }
        status = "passed" if all(bool(block["passed"]) for block in checks.values()) else "needs_data"

        cross_species_alignments = []
        for row in computed:
            alignment = row.get("halflife_alignment")
            if isinstance(alignment, dict):
                cross_species_alignments.append(
                    {
                        "organism": row["organism"],
                        "n_halflife": row.get("readout_fits", {}).get("halflife", {}).get("n_join") if isinstance(row.get("readout_fits"), dict) else None,
                        "cos_halflife_resid4": alignment.get("cos_d_opt_halflife_d_resid4_abundance"),
                        "abs_cos_halflife_resid4": alignment.get("abs_cos_d_opt_halflife_d_resid4_abundance"),
                        "cos_halflife_usage": alignment.get("cos_d_opt_halflife_d_usage"),
                        "cos_halflife_tRNA": alignment.get("cos_d_opt_halflife_d_tRNA"),
                        "cos_halflife_f3": alignment.get("cos_d_opt_halflife_d_f3"),
                    }
                )
        cross_species_abs = [
            float(item["abs_cos_halflife_resid4"])
            for item in cross_species_alignments
            if finite_numeric(item.get("abs_cos_halflife_resid4"))
        ]

        emit(
            status,
            reason=None if status == "passed" else "primary yeast readout directions or half-life/resid4 alignment could not be computed under the join gates",
            seed=SEED,
            fold_count=FOLD_COUNT,
            min_proteins_per_organism=MIN_PROTEINS_PER_ORGANISM,
            synonymous_design_columns=len(syn_columns),
            conclusion=conclusion,
            conclusion_reason=conclusion_reason,
            payload={
                "primary_yeast": compact_organism(primary) if primary is not None else None,
                "cross_species": {
                    "organisms_computed": len(computed),
                    "alignments": cross_species_alignments,
                    "abs_cos_halflife_resid4_summary": summarize_values(cross_species_abs),
                    "power_note": "descriptive only: at most yeast, E.coli, and human have local half-life plus CDS/tRNA payloads, with organism-specific readout definitions and no phylogenetic correction",
                },
                "organisms": [compact_organism(row) for row in per_organism],
            },
            controls_used={
                "target_readouts": {
                    "halflife": "yeast/E.coli log10(minutes); human unlogged Agarwal consensus relative half-life, matching sibling convention",
                    "TE": "log10(te) from local ribosome_te payload",
                    "mRNA_level": "log10(mrna) from local ribosome_te payload",
                    "abundance": "log10(abundance_ppm) from local cds_codon_abundance joined proteomics field",
                },
                "predictor_space": "41-column synonymous contrast design, one m-1 reference contrast basis per amino-acid synonymous family",
                "optimal_direction": "for each readout independently, least-squares coefficients after residualizing target and synonymous contrasts against controls, then unit-normalized",
                "d_resid4_abundance": "Route-S abundance d_opt residual after orthonormal projection onto span{d_tRNA,d_f3,d_usage}; not fitted from half-life",
                "d_tRNA": "dos Reis tAI direction from same-organism local tRNA gene-copy/GtRNAdb records",
                "d_f3": "fixed f3_stress direction from codon_topology q_vectors, synonymous-family projected",
                "d_usage": "same-organism within-synonymous-family CDS usage-frequency direction from cds_codon_abundance",
                "controls": [
                    "intercept",
                    "log(cds_len_nt)",
                    "log(total_sense_codons)",
                    "gc3_fraction",
                    "20 standard amino-acid composition fractions",
                ],
                "held_out_strength": "5-fold deterministic CV R2 for fixed full-sample directions uses fold-local slope; direction-estimation R2 is optimistic and reported with caveat",
            },
            checks=checks,
            caveats=[
                "observational readout-associated codon directions are not causal mechanism estimates",
                "full-sample d_opt directions are used for alignment, so held-out R2 for those directions still inherits direction-selection optimism",
                "human half-life is a normalized cross-dataset consensus rather than raw minutes",
                "cross-species signs are descriptive because readout definitions, growth conditions, and gene joins differ",
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
                "readout_optimal_directions_computed": {"passed": False},
                "halflife_vs_resid4_alignment": {"passed": False},
                "fourth_mechanism_verdict": {"passed": False},
            },
        )


if __name__ == "__main__":
    main()

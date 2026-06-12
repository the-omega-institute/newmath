#!/usr/bin/env python3
"""B*_Q6 synonymous wobble choice versus local ribosome occupancy."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import random
import sys
from collections import defaultdict
from typing import Any

from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_wobble_dwell_coupling_powered"
CLAIM_ID = "h3.cross_layer_relation.wobble_dwell_coupling.b_star_q6_ribosome_occupancy_powered"

PERMUTATION_COUNT = 200
LAMBDA_DL = 0.01
MODEL_DF = 2
MIN_ROWS_PER_FAMILY = 200
MIN_ROWS_PER_SIGN = 40
MIN_INFORMATIVE_BINS = 20
EPS = 1e-12

OCCUPANCY_PATH = "tools/bio_reality/data/riboseq_positional_occupancy_saccharomyces_cerevisiae.json"
ORDERED_CDS_PATH = "tools/bio_reality/data/cds_ordered_sequences_saccharomyces_cerevisiae.json"
GENETIC_CODE_PATH = "tools/bio_reality/data/ncbi_genetic_codes.json"


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def finite_number(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def numeric(value: object, field: str) -> float:
    if not finite_number(value):
        raise ValueError(f"{field} must be a finite number")
    return float(value)


def dna_codon(codon: str) -> str:
    return codon.replace("U", "T")


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def sign_of(value: float) -> int:
    if value > EPS:
        return 1
    if value < -EPS:
        return -1
    return 0


def q6_context(repo: pathlib.Path) -> dict[str, object]:
    code_rna = standard_code(repo)
    codons_rna = [codon for codon in sorted(code_rna) if code_rna[codon] != "*"]
    fibers_rna = fibers_for(code_rna, codons_rna)
    projected_rna = {name: project_syn(vector, fibers_rna) for name, vector in q_vectors(codons_rna).items()}
    projected_dna = {
        name: {dna_codon(codon): value for codon, value in vector.items()}
        for name, vector in projected_rna.items()
    }
    support_map: dict[str, list[tuple[str, float]]] = defaultdict(list)
    for coordinate, vector in projected_dna.items():
        for codon, value in vector.items():
            if abs(value) > EPS:
                support_map[codon].append((coordinate, value))
    return {
        "q_projected_dna": projected_dna,
        "q_names": list(projected_dna),
        "support_map": dict(support_map),
        "aa_by_codon": {dna_codon(codon): aa for codon, aa in code_rna.items() if aa != "*"},
    }


def schema_and_join(
    occupancy: dict[str, object],
    ordered_cds: dict[str, object],
) -> tuple[dict[str, dict[str, object]], dict[str, object]]:
    genes = occupancy.get("genes")
    cds_items = ordered_cds.get("cds")
    if not isinstance(genes, dict):
        raise ValueError(f"{OCCUPANCY_PATH} must contain a genes object")
    if not isinstance(cds_items, list):
        raise ValueError(f"{ORDERED_CDS_PATH} must contain a cds list")

    cds_by_gene: dict[str, dict[str, object]] = {}
    for item in cds_items:
        if not isinstance(item, dict):
            continue
        gene_id = item.get("gene_id")
        codons = item.get("codons")
        if isinstance(gene_id, str) and isinstance(codons, list):
            cds_by_gene[gene_id] = item

    joined: dict[str, dict[str, object]] = {}
    length_mismatch = 0
    malformed_occupancy = 0
    for gene_id, raw_gene in genes.items():
        if not isinstance(gene_id, str) or not isinstance(raw_gene, dict):
            malformed_occupancy += 1
            continue
        cds = cds_by_gene.get(gene_id)
        if not isinstance(cds, dict):
            continue
        codons = cds.get("codons")
        if not isinstance(codons, list) or any(not isinstance(codon, str) for codon in codons):
            continue
        n_codons = raw_gene.get("n_codons")
        if not isinstance(n_codons, int) or n_codons != len(codons):
            length_mismatch += 1
            continue
        joined[gene_id] = {"occupancy": raw_gene, "codons": codons}

    occupancy_gene_ids = {gene_id for gene_id in genes if isinstance(gene_id, str)}
    cds_gene_ids = set(cds_by_gene)
    overlap = occupancy_gene_ids & cds_gene_ids
    summary = {
        "occupancy_path": OCCUPANCY_PATH,
        "ordered_cds_path": ORDERED_CDS_PATH,
        "occupancy_gene_count": len(occupancy_gene_ids),
        "ordered_cds_gene_count": len(cds_gene_ids),
        "gene_id_overlap": len(overlap),
        "joined_gene_count_after_length_check": len(joined),
        "occupancy_gene_alignment_rate": len(overlap) / len(occupancy_gene_ids) if occupancy_gene_ids else 0.0,
        "ordered_cds_alignment_rate": len(overlap) / len(cds_gene_ids) if cds_gene_ids else 0.0,
        "length_mismatch_count": length_mismatch,
        "malformed_occupancy_entries": malformed_occupancy,
        "occupancy_schema_keys": list(occupancy.keys()),
        "occupancy_gene_sample_keys": list(next(iter(genes.values())).keys()) if genes else [],
        "ordered_cds_schema_keys": list(ordered_cds.keys()),
        "ordered_cds_sample_keys": list(cds_items[0].keys()) if cds_items and isinstance(cds_items[0], dict) else [],
        "a_site_method": occupancy.get("a_site_method"),
        "a_site_offset_nt": occupancy.get("a_site_offset_nt"),
        "mapping_coverage": occupancy.get("mapping_coverage"),
    }
    return joined, summary


def iter_gene_windows(gene_id: str, joined_item: dict[str, object]) -> list[dict[str, object]]:
    raw_gene = joined_item["occupancy"]
    codons = joined_item["codons"]
    if not isinstance(raw_gene, dict) or not isinstance(codons, list):
        return []
    n_codons = len(codons)
    rows: list[dict[str, object]] = []
    windows = [
        ("5prime", raw_gene.get("rel_occupancy_5prime")),
        ("3prime", raw_gene.get("rel_occupancy_3prime")),
    ]
    for window, values in windows:
        if not isinstance(values, list):
            continue
        if window == "5prime":
            start_index = 0
            offsets = list(range(len(values)))
        else:
            start_index = n_codons - len(values)
            offsets = [index - len(values) for index in range(len(values))]
        for local_index, value in enumerate(values):
            codon_index = start_index + local_index
            if codon_index < 0 or codon_index >= n_codons:
                continue
            if not finite_number(value):
                continue
            rows.append(
                {
                    "gene_id": gene_id,
                    "window": window,
                    "position_offset": offsets[local_index],
                    "position_bin": f"{window}:{offsets[local_index]}",
                    "codon_index": codon_index,
                    "codon": str(codons[codon_index]).upper(),
                    "occupancy": float(value),
                }
            )
    return rows


def collect_rows(
    joined: dict[str, dict[str, object]],
    support_map: dict[str, list[tuple[str, float]]],
    aa_by_codon: dict[str, str],
) -> tuple[dict[str, list[dict[str, object]]], dict[str, object]]:
    by_coordinate: dict[str, list[dict[str, object]]] = defaultdict(list)
    window_lengths_5: list[int] = []
    window_lengths_3: list[int] = []
    skipped = {"codon_not_on_b_star_q6_support": 0, "unsupported_codon_text": 0}
    total_window_positions = 0
    for gene_id, item in joined.items():
        raw_gene = item["occupancy"]
        if isinstance(raw_gene, dict):
            values5 = raw_gene.get("rel_occupancy_5prime")
            values3 = raw_gene.get("rel_occupancy_3prime")
            if isinstance(values5, list):
                window_lengths_5.append(len(values5))
            if isinstance(values3, list):
                window_lengths_3.append(len(values3))
        for row in iter_gene_windows(gene_id, item):
            total_window_positions += 1
            codon = row["codon"]
            if not isinstance(codon, str) or len(codon) != 3:
                skipped["unsupported_codon_text"] += 1
                continue
            hits = support_map.get(codon)
            if not hits:
                skipped["codon_not_on_b_star_q6_support"] += 1
                continue
            aa = aa_by_codon.get(codon)
            if not isinstance(aa, str) or not aa:
                skipped["unsupported_codon_text"] += 1
                continue
            for coordinate, q_value in hits:
                signed = sign_of(q_value)
                if signed == 0:
                    continue
                entry = dict(row)
                entry["amino_acid"] = aa
                entry["comparison_bin"] = f"{entry['position_bin']}|aa:{aa}"
                entry["q_value"] = q_value
                entry["q_sign"] = signed
                by_coordinate[coordinate].append(entry)
    summary = {
        "total_joined_window_positions": total_window_positions,
        "file_provided_5prime_window_lengths": sorted(set(window_lengths_5)),
        "file_provided_3prime_window_lengths": sorted(set(window_lengths_3)),
        "skipped": skipped,
    }
    return dict(by_coordinate), summary


def informative_rows(rows: list[dict[str, object]]) -> tuple[list[dict[str, object]], dict[str, object]]:
    bins: dict[str, list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        bin_id = row.get("comparison_bin")
        if isinstance(bin_id, str):
            bins[bin_id].append(row)
    kept: list[dict[str, object]] = []
    dropped_single_sign_bins = 0
    informative_bin_count = 0
    for bin_rows in bins.values():
        signs = {row["q_sign"] for row in bin_rows}
        if 1 in signs and -1 in signs:
            informative_bin_count += 1
            kept.extend(bin_rows)
        else:
            dropped_single_sign_bins += 1
    return kept, {
        "position_bins_total": len(bins),
        "position_amino_acid_bins_total": len(bins),
        "position_amino_acid_bins_informative_with_both_signs": informative_bin_count,
        "position_amino_acid_bins_dropped_single_sign": dropped_single_sign_bins,
        "position_bins_informative_with_both_signs": informative_bin_count,
        "position_bins_dropped_single_sign": dropped_single_sign_bins,
        "rows_after_informative_bin_filter": len(kept),
    }


def bin_mean_adjusted_effect(rows: list[dict[str, object]]) -> dict[str, object]:
    if not rows:
        return {
            "status": "needs_data",
            "reason": "no informative rows",
        }
    bins: dict[str, list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        bins[str(row["comparison_bin"])].append(row)

    pos_values: list[float] = []
    neg_values: list[float] = []
    expanded_q: list[float] = []
    expanded_occ: list[float] = []
    per_codon: dict[str, dict[str, object]] = defaultdict(lambda: {"n": 0, "adjusted_sum": 0.0, "raw_sum": 0.0})
    per_window_values: dict[str, dict[str, list[float]]] = {
        "5prime": {"positive": [], "negative": []},
        "3prime": {"positive": [], "negative": []},
    }
    raw_pos: list[float] = []
    raw_neg: list[float] = []
    for bin_rows in bins.values():
        occ_mean = mean([float(row["occupancy"]) for row in bin_rows])
        q_mean = mean([float(row["q_value"]) for row in bin_rows])
        for row in bin_rows:
            adjusted = float(row["occupancy"]) - occ_mean
            q_adjusted = float(row["q_value"]) - q_mean
            sign = int(row["q_sign"])
            window = str(row["window"])
            codon = str(row["codon"])
            per_codon[codon]["n"] = int(per_codon[codon]["n"]) + 1
            per_codon[codon]["adjusted_sum"] = float(per_codon[codon]["adjusted_sum"]) + adjusted
            per_codon[codon]["raw_sum"] = float(per_codon[codon]["raw_sum"]) + float(row["occupancy"])
            expanded_q.append(q_adjusted)
            expanded_occ.append(adjusted)
            if sign > 0:
                pos_values.append(adjusted)
                raw_pos.append(float(row["occupancy"]))
                if window in per_window_values:
                    per_window_values[window]["positive"].append(adjusted)
            else:
                neg_values.append(adjusted)
                raw_neg.append(float(row["occupancy"]))
                if window in per_window_values:
                    per_window_values[window]["negative"].append(adjusted)

    pos_n = len(pos_values)
    neg_n = len(neg_values)
    if pos_n < MIN_ROWS_PER_SIGN or neg_n < MIN_ROWS_PER_SIGN:
        return {
            "status": "needs_data",
            "reason": f"positive/negative rows below {MIN_ROWS_PER_SIGN}",
            "positive_rows": pos_n,
            "negative_rows": neg_n,
        }

    q_norm = math.sqrt(sum(value * value for value in expanded_q))
    occ_norm = math.sqrt(sum(value * value for value in expanded_occ))
    c_h = 0.0
    if q_norm > EPS and occ_norm > EPS:
        c_h = sum(q * occ for q, occ in zip(expanded_q, expanded_occ)) / (q_norm * occ_norm)
        c_h = max(-1.0, min(1.0, c_h))

    by_window: dict[str, object] = {}
    for window, values in per_window_values.items():
        p_values = values["positive"]
        n_values = values["negative"]
        effect = mean(p_values) - mean(n_values) if p_values and n_values else None
        by_window[window] = {
            "positive_rows": len(p_values),
            "negative_rows": len(n_values),
            "adjusted_positive_minus_negative": effect,
            "has_both_signs": bool(p_values and n_values),
        }

    five_effect = by_window.get("5prime", {}).get("adjusted_positive_minus_negative") if isinstance(by_window.get("5prime"), dict) else None
    three_effect = by_window.get("3prime", {}).get("adjusted_positive_minus_negative") if isinstance(by_window.get("3prime"), dict) else None
    sign_consistent = (
        isinstance(five_effect, float)
        and isinstance(three_effect, float)
        and abs(five_effect) > EPS
        and abs(three_effect) > EPS
        and sign_of(five_effect) == sign_of(three_effect)
    )

    codon_summary = {}
    for codon, stats in sorted(per_codon.items()):
        n = int(stats["n"])
        codon_summary[codon] = {
            "n": n,
            "mean_raw_occupancy": float(stats["raw_sum"]) / n if n else 0.0,
            "mean_position_adjusted_occupancy": float(stats["adjusted_sum"]) / n if n else 0.0,
        }

    signed_effect = mean(pos_values) - mean(neg_values)
    return {
        "status": "computed",
        "positive_rows": pos_n,
        "negative_rows": neg_n,
        "raw_positive_mean_occupancy": mean(raw_pos),
        "raw_negative_mean_occupancy": mean(raw_neg),
        "raw_positive_minus_negative": mean(raw_pos) - mean(raw_neg),
        "position_adjusted_positive_mean": mean(pos_values),
        "position_adjusted_negative_mean": mean(neg_values),
        "position_adjusted_positive_minus_negative": signed_effect,
        "abs_position_adjusted_effect": abs(signed_effect),
        "C_H": c_h,
        "C_H_pass": c_h > 0.0,
        "by_window": by_window,
        "five_prime_three_prime_direction_consistent": sign_consistent,
        "five_prime_three_prime_consistency_note": (
            "same signed adjusted effect in both file-provided windows"
            if sign_consistent
            else "window-specific adjusted effects are missing, near zero, or opposite signed"
        ),
        "codon_level_occupancy": codon_summary,
    }


def prepared_permutation_bins(rows: list[dict[str, object]]) -> tuple[list[dict[str, object]], int, int]:
    bins: dict[str, list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        bins[str(row["comparison_bin"])].append(row)
    prepared: list[dict[str, object]] = []
    total_positive = 0
    total_negative = 0
    for bin_id, bin_rows in bins.items():
        occupancies = [float(row["occupancy"]) for row in bin_rows]
        occ_mean = mean(occupancies)
        adjusted = [value - occ_mean for value in occupancies]
        positive_count = sum(1 for row in bin_rows if int(row["q_sign"]) > 0)
        negative_count = len(bin_rows) - positive_count
        total_positive += positive_count
        total_negative += negative_count
        prepared.append(
            {
                "position_bin": bin_id,
                "adjusted": adjusted,
                "positive_count": positive_count,
                "negative_count": negative_count,
            }
        )
    return prepared, total_positive, total_negative


def null_effect_for_trial(
    prepared: list[dict[str, object]],
    total_positive: int,
    total_negative: int,
    trial: int,
    coordinate: str,
) -> float | None:
    if total_positive < MIN_ROWS_PER_SIGN or total_negative < MIN_ROWS_PER_SIGN:
        return None
    positive_sum = 0.0
    for item in prepared:
        adjusted = item["adjusted"]
        positive_count = int(item["positive_count"])
        if not isinstance(adjusted, list) or positive_count <= 0:
            continue
        if positive_count >= len(adjusted):
            positive_sum += sum(float(value) for value in adjusted)
            continue
        bin_id = str(item["position_bin"])
        seed_material = f"{EXPERIMENT_ID}|{coordinate}|position_bin_label_shuffle|trial={trial}|{bin_id}|n={len(adjusted)}"
        seed = int.from_bytes(hashlib.sha256(seed_material.encode("utf-8")).digest()[:8], "big")
        rng = random.Random(seed)
        positive_sum += sum(float(adjusted[index]) for index in rng.sample(range(len(adjusted)), positive_count))
    positive_mean = positive_sum / total_positive
    negative_mean = -positive_sum / total_negative
    return abs(positive_mean - negative_mean)


def permutation_null95(rows: list[dict[str, object]], coordinate: str) -> dict[str, object]:
    prepared, total_positive, total_negative = prepared_permutation_bins(rows)
    null_values: list[float] = []
    for trial in range(PERMUTATION_COUNT):
        value = null_effect_for_trial(prepared, total_positive, total_negative, trial, coordinate)
        if value is not None:
            null_values.append(value)
    return {
        "permutation_count": len(null_values),
        "null95_abs_position_adjusted_effect": percentile_nearest_rank(null_values, 0.95),
        "null_mean_abs_position_adjusted_effect": mean(null_values),
        "null_min": min(null_values) if null_values else 0.0,
        "null_max": max(null_values) if null_values else 0.0,
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|coordinate|position_bin_label_shuffle|trial|position_bin|n",
            "null_model": (
            "within each exact file-provided window/codon-index and amino-acid bin, shuffle B*_Q6 synonymous variant labels "
            "against fixed relative ribosome occupancy values; position, amino-acid, and occupancy distributions are preserved"
        ),
    }


def support_summary(q_vector: dict[str, float]) -> dict[str, object]:
    positive = sorted(codon for codon, value in q_vector.items() if value > EPS)
    negative = sorted(codon for codon, value in q_vector.items() if value < -EPS)
    return {
        "positive_q_codons": positive,
        "negative_q_codons": negative,
        "support_codon_count": len(positive) + len(negative),
    }


def mechanism_interpretation(coordinate: str, effect: float, c_h: float) -> str:
    if abs(effect) <= EPS:
        return (
            f"{coordinate}: no position-adjusted occupancy separation is resolved; no wobble-dwell mechanism is supported."
        )
    direction = "higher" if effect > 0 else "lower"
    consistency = "aligned with" if c_h > 0 else "opposite to"
    return (
        f"{coordinate}: positive-q synonymous variants have {direction} local relative ribosome occupancy than "
        f"negative-q variants after exact position-bin control; the signed occupancy vector is {consistency} "
        "the B*_Q6 coordinate support. Candidate biology remains descriptive: wobble pairing, tRNA availability, "
        "near-cognate competition, and elongation pausing are not separated by this statistic."
    )


def analyze_coordinate(coordinate: str, rows: list[dict[str, object]], q_vector: dict[str, float]) -> dict[str, object]:
    filtered, bin_summary = informative_rows(rows)
    sign_counts = {
        "positive": sum(1 for row in filtered if int(row["q_sign"]) > 0),
        "negative": sum(1 for row in filtered if int(row["q_sign"]) < 0),
    }
    base = {
        "coordinate": coordinate,
        **support_summary(q_vector),
        "n_rows_before_informative_bin_filter": len(rows),
        **bin_summary,
        "sign_counts_after_filter": sign_counts,
    }
    if len(filtered) < MIN_ROWS_PER_FAMILY:
        return {
            **base,
            "status": "needs_data",
            "reason": f"informative rows below {MIN_ROWS_PER_FAMILY}",
            "gate_pass": False,
        }
    if int(bin_summary["position_bins_informative_with_both_signs"]) < MIN_INFORMATIVE_BINS:
        return {
            **base,
            "status": "needs_data",
            "reason": f"informative position bins below {MIN_INFORMATIVE_BINS}",
            "gate_pass": False,
        }
    observed = bin_mean_adjusted_effect(filtered)
    if observed.get("status") != "computed":
        return {
            **base,
            **observed,
            "gate_pass": False,
        }
    null = permutation_null95(filtered, coordinate)
    observed_abs = float(observed["abs_position_adjusted_effect"])
    null95 = float(null["null95_abs_position_adjusted_effect"])
    raw_margin = observed_abs - null95
    score = raw_margin - LAMBDA_DL * MODEL_DF
    null95_pass = raw_margin > 0.0
    dl_pass = score > 0.0
    c_h_pass = bool(observed["C_H_pass"])
    gate_pass = null95_pass and dl_pass and c_h_pass
    return {
        **base,
        "status": "computed",
        "observed": observed,
        "permutation_null": null,
        "Null95_pass": null95_pass,
        "lambda_DL": LAMBDA_DL,
        "DL": MODEL_DF,
        "description_length_penalized_score": score,
        "DL_pass": dl_pass,
        "C_H": observed["C_H"],
        "C_H_pass": c_h_pass,
        "gate_pass": gate_pass,
        "mechanism_interpretation": mechanism_interpretation(
            coordinate,
            float(observed["position_adjusted_positive_minus_negative"]),
            float(observed["C_H"]),
        ),
    }


def checks_for(coupling_by_family: dict[str, dict[str, object]], schema: dict[str, object]) -> list[dict[str, object]]:
    computed = [item for item in coupling_by_family.values() if item.get("status") == "computed"]
    gate_pass = [item for item in computed if item.get("gate_pass")]
    null_computed = [
        item
        for item in computed
        if isinstance(item.get("permutation_null"), dict)
        and int(item["permutation_null"].get("permutation_count", 0)) >= 200
    ]
    return [
        {
            "name": "ribosome_occupancy_and_ordered_cds_joined",
            "passed": int(schema.get("joined_gene_count_after_length_check", 0)) > 0
            and schema.get("length_mismatch_count") == 0,
            "actual": {
                "occupancy_gene_count": schema.get("occupancy_gene_count"),
                "ordered_cds_gene_count": schema.get("ordered_cds_gene_count"),
                "gene_id_overlap": schema.get("gene_id_overlap"),
                "joined_gene_count_after_length_check": schema.get("joined_gene_count_after_length_check"),
                "length_mismatch_count": schema.get("length_mismatch_count"),
            },
            "expected": "ribosome occupancy genes join ordered CDS by gene_id with matching codon lengths",
        },
        {
            "name": "position_confound_controlled",
            "passed": True,
            "actual": {
                "method": "exact file-provided window/codon-index plus amino-acid bins; effect uses occupancy demeaned within bin; null shuffles synonymous labels only within the same bin",
                "windows": "5prime and 3prime arrays as supplied by the occupancy file",
            },
            "expected": "5prime ramp, stop-proximal position effects, and amino-acid identity are controlled before testing synonymous variant labels",
        },
        {
            "name": "Null95_within_position_bin_permutation",
            "passed": len(null_computed) == len(computed) and len(computed) > 0,
            "actual": {
                "computed_families": len(computed),
                "families_with_at_least_200_permutations": len(null_computed),
                "permutation_count_requested": PERMUTATION_COUNT,
            },
            "expected": "each computed B*_Q6 family uses at least 200 within-position-bin label permutations",
        },
        {
            "name": "lambda_DL_and_C_H_gate",
            "passed": len(gate_pass) > 0,
            "actual": {
                "families_passing_all_gates": [item["coordinate"] for item in gate_pass],
                "lambda_DL": LAMBDA_DL,
                "DL": MODEL_DF,
                "C_H_rule": "C_H > 0",
            },
            "expected": "at least one family passes Null95, description-length penalty, and coordinate-support direction consistency",
        },
    ]


def cannot_claim() -> list[str]:
    return [
        "Relative ribosome occupancy is treated as a local dwell proxy; it is not a direct causal dwell-time measurement.",
        "This descriptive association does not prove that synonymous codon choice causes ribosome pausing.",
        "A-site offset is inherited from the source occupancy file and remains an approximate mapping choice.",
        "The occupancy map covers only the source-mapped subset of yeast coding sequence positions.",
        "The test controls exact position bins but does not separately identify tRNA abundance, mRNA structure, nascent peptide effects, or codon-pair context.",
        "A 5prime-only signal is not promoted to a mechanism claim because initiation-ramp structure is the dominant confound.",
        "Directionality is coordinate-relative: positive-q versus negative-q labels follow the B*_Q6 basis orientation, not a universal biochemical sign convention.",
    ]


def main() -> None:
    try:
        repo = pathlib.Path(__file__).resolve().parents[3]
        missing = [path for path in [OCCUPANCY_PATH, ORDERED_CDS_PATH, GENETIC_CODE_PATH] if not (repo / path).exists()]
        if missing:
            emit("needs_data", missing_required_data=missing, reason="required positional occupancy or ordered CDS data not present")

        occupancy = load_json(repo / OCCUPANCY_PATH)
        ordered_cds = load_json(repo / ORDERED_CDS_PATH)
        if not isinstance(occupancy, dict) or not isinstance(ordered_cds, dict):
            raise ValueError("required data files must contain JSON objects")

        joined, schema = schema_and_join(occupancy, ordered_cds)
        context = q6_context(repo)
        q_projected = context["q_projected_dna"]
        support_map = context["support_map"]
        if not isinstance(q_projected, dict) or not isinstance(support_map, dict):
            raise ValueError("B*_Q6 context malformed")

        aa_by_codon = context["aa_by_codon"]
        if not isinstance(aa_by_codon, dict):
            raise ValueError("standard-code codon to amino-acid map malformed")
        rows_by_coordinate, row_collection = collect_rows(joined, support_map, aa_by_codon)  # type: ignore[arg-type]
        coupling_by_family: dict[str, dict[str, object]] = {}
        for coordinate in context["q_names"]:  # type: ignore[index]
            q_vector = q_projected[coordinate]  # type: ignore[index]
            rows = rows_by_coordinate.get(coordinate, [])
            coupling_by_family[str(coordinate)] = analyze_coordinate(str(coordinate), rows, q_vector)

        checks = checks_for(coupling_by_family, schema)
        computed = [item for item in coupling_by_family.values() if item.get("status") == "computed"]
        gate_pass = [item for item in computed if item.get("gate_pass")]
        needs_data = not computed
        if needs_data:
            status = "needs_data"
            verdict = "No B*_Q6 synonymous family had enough paired position-bin support to test wobble-dwell coupling."
        elif gate_pass:
            status = "passed"
            verdict = (
                "At least one B*_Q6 synonymous family shows position-bin-controlled local ribosome occupancy separation "
                "that exceeds the within-bin label permutation Null95 and passes lambda_DL plus C_H."
            )
        else:
            status = "failed"
            verdict = (
                "The available yeast positional ribosome occupancy data do not support a B*_Q6 wobble-dwell coupling "
                "under the within-position-bin Null95, lambda_DL, and C_H gates."
            )

        emit(
            status,
            checks=checks,
            result={
                "statement": (
                    "Descriptive, position-confound-controlled analysis of whether B*_Q6 synonymous codon choices "
                    "co-vary with local relative ribosome occupancy in the same codon windows; this is not a causal proof."
                ),
                "schema_and_gene_id_join": schema,
                "row_collection": row_collection,
                "position_confound_controlled": {
                    "controlled": True,
                    "method": (
                        "Exact position and amino-acid control: bins are file-provided 5prime/3prime offsets crossed with genetic-code amino-acid identity. "
                        "Observed effects use within-bin occupancy demeaning; Null95 shuffles synonymous labels only within the same bin."
                    ),
                    "does_not_use_preset_window_constants": True,
                },
                "coordinates": context["q_names"],
                "coupling_by_family": coupling_by_family,
                "families_passing_all_gates": [item["coordinate"] for item in gate_pass],
                "families_passing_Null95": [
                    item["coordinate"] for item in computed if item.get("Null95_pass")
                ],
                "verdict": verdict,
                "cannot_claim": cannot_claim(),
            },
        )
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="wobble-dwell coupling experiment could not be computed")


if __name__ == "__main__":
    main()

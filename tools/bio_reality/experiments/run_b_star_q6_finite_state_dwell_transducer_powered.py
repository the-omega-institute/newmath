#!/usr/bin/env python3
"""Yeast finite-state dwell transducer versus memoryless B*_Q6 codon signal."""

from __future__ import annotations

import hashlib
import json
import math
import multiprocessing
import os
import pathlib
import random
import sys
from typing import Any


EXPERIMENT_ID = "b_star_q6_finite_state_dwell_transducer_powered"
CLAIM_ID = "h3.cross_layer_relation.order_memory_execution_signal.b_star_q6_finite_state_dwell_transducer_powered"

OCCUPANCY_PATH = "tools/bio_reality/data/riboseq_positional_occupancy_saccharomyces_cerevisiae.json"
ORDERED_CDS_PATH = "tools/bio_reality/data/cds_ordered_sequences_saccharomyces_cerevisiae.json"
Q_AXES = ("K_AAA", "Arg_AGR", "f3_stress")
FOLD_COUNT = 5
INNER_FOLD_COUNT = 2
NULL_B = int(os.environ.get("FSM_DWELL_NULL_B", "100"))
NULL_WORKERS = int(os.environ.get("FSM_DWELL_NULL_WORKERS", "4"))
MIN_HEAD_CODONS = 50
MAX_CONTEXT_ORDER = 2
RIDGE_ALPHA = 1e-6
MDL_LAMBDAS = (0.0, 0.1)
SEED = "sha256:b_star_q6_finite_state_dwell_transducer_powered:deterministic"
EPS = 1e-12
BOS = 0
UNK = 1
STATE_BASE = 32
NULL_WORKER_STATE: dict[str, object] = {}
STANDARD_CODE = {
    "UUU": "F", "UUC": "F", "UUA": "L", "UUG": "L",
    "UCU": "S", "UCC": "S", "UCA": "S", "UCG": "S",
    "UAU": "Y", "UAC": "Y", "UAA": "*", "UAG": "*",
    "UGU": "C", "UGC": "C", "UGA": "*", "UGG": "W",
    "CUU": "L", "CUC": "L", "CUA": "L", "CUG": "L",
    "CCU": "P", "CCC": "P", "CCA": "P", "CCG": "P",
    "CAU": "H", "CAC": "H", "CAA": "Q", "CAG": "Q",
    "CGU": "R", "CGC": "R", "CGA": "R", "CGG": "R",
    "AUU": "I", "AUC": "I", "AUA": "I", "AUG": "M",
    "ACU": "T", "ACC": "T", "ACA": "T", "ACG": "T",
    "AAU": "N", "AAC": "N", "AAA": "K", "AAG": "K",
    "AGU": "S", "AGC": "S", "AGA": "R", "AGG": "R",
    "GUU": "V", "GUC": "V", "GUA": "V", "GUG": "V",
    "GCU": "A", "GCC": "A", "GCA": "A", "GCG": "A",
    "GAU": "D", "GAC": "D", "GAA": "E", "GAG": "E",
    "GGU": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}
Q9_FAMILIES = [
    ["UUU", "UUC"], ["UUA", "UUG"], ["UCU", "UCC", "UCA", "UCG"],
    ["UAU", "UAC"], ["UGU", "UGC"], ["CUU", "CUC", "CUA", "CUG"],
    ["CCU", "CCC", "CCA", "CCG"], ["CAU", "CAC"], ["CAA", "CAG"],
    ["CGU", "CGC", "CGA", "CGG"], ["AUU", "AUC", "AUA"],
    ["ACU", "ACC", "ACA", "ACG"], ["AAU", "AAC"], ["AAA", "AAG"],
    ["AGU", "AGC"], ["AGA", "AGG"], ["GUU", "GUC", "GUA", "GUG"],
    ["GCU", "GCC", "GCA", "GCG"], ["GAU", "GAC"], ["GAA", "GAG"],
    ["GGU", "GGC", "GGA", "GGG"],
]


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def stable_int(material: str) -> int:
    return int.from_bytes(hashlib.sha256(material.encode("utf-8")).digest()[:8], "big")


def deterministic_permutation(n: int, material: str) -> list[int]:
    out = list(range(n))
    for index in range(n - 1, 0, -1):
        swap = stable_int(f"{material}|index={index}|n={n}") % (index + 1)
        out[index], out[swap] = out[swap], out[index]
    return out


def deterministic_folds(n: int, material: str, fold_count: int) -> list[list[int]]:
    order = deterministic_permutation(n, material)
    folds = [[] for _ in range(fold_count)]
    for position, row_index in enumerate(order):
        folds[position % fold_count].append(row_index)
    return folds


def vector_dot(left: list[float], right: list[float]) -> float:
    return sum(left[index] * right[index] for index in range(len(left)))


def solve_linear_system(matrix: list[list[float]], rhs: list[float]) -> tuple[list[float], int]:
    n = len(rhs)
    if n == 0:
        return [], 0
    trace = sum(matrix[index][index] for index in range(n))
    base_ridge = max(EPS, abs(trace) * 1e-12 / max(1, n))
    for ridge_step in range(8):
        ridge = 0.0 if ridge_step == 0 else base_ridge * (100.0 ** (ridge_step - 1))
        augmented = [
            [matrix[row][col] + (ridge if row == col else 0.0) for col in range(n)] + [rhs[row]]
            for row in range(n)
        ]
        ok = True
        for col in range(n):
            pivot = max(range(col, n), key=lambda row: abs(augmented[row][col]))
            if abs(augmented[pivot][col]) <= max(EPS, abs(trace) * 1e-14):
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


def finite_number(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def rna_to_dna(codon: str) -> str:
    return codon.upper().replace("U", "T")


def standard_code(_repo: pathlib.Path) -> dict[str, str]:
    return dict(STANDARD_CODE)


def fibers_for(code: dict[str, str], codons: list[str]) -> dict[str, list[str]]:
    fibers: dict[str, list[str]] = {}
    for codon in codons:
        fibers.setdefault(code[codon], []).append(codon)
    return fibers


def project_syn(vector: dict[str, float], fibers: dict[str, list[str]]) -> dict[str, float]:
    out = dict(vector)
    for fiber in fibers.values():
        center = sum(vector[codon] for codon in fiber) / len(fiber)
        for codon in fiber:
            out[codon] = vector[codon] - center
    return out


def zero(codons: list[str]) -> dict[str, float]:
    return {codon: 0.0 for codon in codons}


def q_vectors(codons: list[str]) -> dict[str, dict[str, float]]:
    raw: dict[str, dict[str, float]] = {}
    q = zero(codons)
    q["AAA"] = 1.0
    q["AAG"] = -1.0
    raw["K_AAA"] = q
    q = zero(codons)
    for codon in ["AGA", "AGG"]:
        q[codon] = 1.0
    for codon in ["CGU", "CGC", "CGA", "CGG"]:
        q[codon] = -0.25
    raw["Arg_AGR"] = q
    q = zero(codons)
    for family in Q9_FAMILIES:
        q[family[0]] += 1.0
        q[family[-1]] -= 1.0
    raw["f3_stress"] = q
    return raw


def q_context(repo: pathlib.Path) -> dict[str, object]:
    code = standard_code(repo)
    codons = [codon for codon in sorted(code) if code[codon] != "*"]
    fibers = fibers_for(code, codons)
    projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
    missing = [name for name in Q_AXES if name not in projected]
    if missing:
        raise ValueError(f"missing required B*_Q6 axes: {missing}")
    q_by_codon: dict[str, tuple[float, float, float]] = {}
    label_by_tuple: dict[tuple[float, float, float], int] = {}
    label_by_codon: dict[str, int] = {}
    for codon in codons:
        tup = tuple(round(float(projected[name][codon]), 12) for name in Q_AXES)
        q_by_codon[codon] = tup  # type: ignore[assignment]
        if tup not in label_by_tuple:
            label_by_tuple[tup] = len(label_by_tuple)
        label_by_codon[codon] = label_by_tuple[tup]
    return {
        "code": code,
        "codons": codons,
        "q_projected": projected,
        "q_by_codon": q_by_codon,
        "q_label_by_codon": label_by_codon,
        "n_current_q_states": len(label_by_tuple),
    }


def remove_group_means(values: list[float], groups: list[int]) -> list[float]:
    n_groups = max(groups) + 1 if groups else 0
    sums = [0.0 for _ in range(n_groups)]
    counts = [0 for _ in range(n_groups)]
    for value, group in zip(values, groups):
        sums[group] += value
        counts[group] += 1
    return [value - sums[group] / counts[group] for value, group in zip(values, groups)]


def residualize_dwell(
    raw_y: list[float],
    position_ids: list[int],
    gene_ids: list[int],
    aa_ids: list[int],
) -> tuple[list[float], dict[str, object]]:
    raw_mean = mean(raw_y)
    centered = [value - raw_mean for value in raw_y]
    sst = sum(value * value for value in centered)
    after_position = remove_group_means(centered, position_ids)
    after_gene = remove_group_means(after_position, gene_ids)
    after_aa = remove_group_means(after_gene, aa_ids)
    final_sse = sum(value * value for value in after_aa)
    controls = {
        "raw_centered_sst": sst,
        "position_index_r2": 1.0 - sum(value * value for value in after_position) / sst if sst > EPS else 0.0,
        "position_then_gene_r2": 1.0 - sum(value * value for value in after_gene) / sst if sst > EPS else 0.0,
        "position_gene_then_aa_r2": 1.0 - sum(value * value for value in after_aa) / sst if sst > EPS else 0.0,
        "iterative_position_gene_aa_fixed_effect_r2": 1.0 - final_sse / sst if sst > EPS else 0.0,
        "final_residual_sse": final_sse,
        "iterations": 1,
        "control_order": ["position_index_ramp", "per_gene_mean_level", "amino_acid_identity"],
        "max_abs_control_group_mean_after": None,
    }
    return after_aa, controls


def load_event_stream(repo: pathlib.Path) -> dict[str, object]:
    occupancy = load_json(repo / OCCUPANCY_PATH)
    ordered_cds = load_json(repo / ORDERED_CDS_PATH)
    genes_raw = occupancy.get("genes")
    cds_items = ordered_cds.get("cds")
    if not isinstance(genes_raw, dict) or not isinstance(cds_items, list):
        raise ValueError("ordered CDS and occupancy payloads do not expose expected genes/cds objects")
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
    for gene_id, raw_gene in genes_raw.items():
        if not isinstance(gene_id, str) or not isinstance(raw_gene, dict):
            malformed_occupancy += 1
            continue
        cds = cds_by_gene.get(gene_id)
        if cds is None:
            continue
        codons = cds.get("codons")
        n_codons = raw_gene.get("n_codons")
        if not isinstance(codons, list) or any(not isinstance(codon, str) for codon in codons):
            continue
        if not isinstance(n_codons, int) or n_codons != len(codons):
            length_mismatch += 1
            continue
        joined[gene_id] = {"occupancy": raw_gene, "codons": codons}
    occupancy_gene_ids = {gene_id for gene_id in genes_raw if isinstance(gene_id, str)}
    cds_gene_ids = set(cds_by_gene)
    overlap = occupancy_gene_ids & cds_gene_ids
    schema = {
        "occupancy_path": OCCUPANCY_PATH,
        "ordered_cds_path": ORDERED_CDS_PATH,
        "occupancy_gene_count": len(occupancy_gene_ids),
        "ordered_cds_gene_count": len(cds_gene_ids),
        "gene_id_overlap": len(overlap),
        "joined_gene_count_after_length_check": len(joined),
        "length_mismatch_count": length_mismatch,
        "malformed_occupancy_entries": malformed_occupancy,
        "a_site_method": occupancy.get("a_site_method"),
        "a_site_offset_nt": occupancy.get("a_site_offset_nt"),
        "mapping_coverage": occupancy.get("mapping_coverage"),
    }
    context = q_context(repo)
    code: dict[str, str] = context["code"]  # type: ignore[assignment]
    q_by_codon: dict[str, tuple[float, float, float]] = context["q_by_codon"]  # type: ignore[assignment]

    genes: list[str] = []
    full_sequences: list[list[str]] = []
    event_positions_by_gene: list[list[int]] = []
    raw_y_by_gene: list[list[float]] = []
    flat_y: list[float] = []
    flat_position: list[int] = []
    flat_gene: list[int] = []
    flat_aa: list[int] = []
    aa_to_id: dict[str, int] = {}
    skipped = {
        "head_too_short": 0,
        "nonfinite_or_malformed_head": 0,
        "no_sense_events_after_stop_filter": 0,
    }
    head_lengths: list[int] = []
    zero_raw_positions = 0
    for gene_id in sorted(joined):
        item = joined[gene_id]
        raw_gene = item.get("occupancy")
        codons_raw = item.get("codons")
        if not isinstance(raw_gene, dict) or not isinstance(codons_raw, list):
            continue
        head = raw_gene.get("rel_occupancy_5prime")
        if not isinstance(head, list) or len(head) < MIN_HEAD_CODONS:
            skipped["head_too_short"] += 1
            continue
        if any(not finite_number(value) for value in head):
            skipped["nonfinite_or_malformed_head"] += 1
            continue
        full_seq = [dna_to_rna(str(codon)) for codon in codons_raw]
        positions: list[int] = []
        values: list[float] = []
        gene_index = len(genes)
        for pos, value in enumerate(head):
            if pos >= len(full_seq):
                continue
            codon = full_seq[pos]
            aa = code.get(codon)
            if aa is None or aa == "*" or codon not in q_by_codon:
                continue
            aa_id = aa_to_id.setdefault(aa, len(aa_to_id))
            y = float(value)
            if abs(y) <= EPS:
                zero_raw_positions += 1
            positions.append(pos)
            values.append(y)
            flat_y.append(y)
            flat_position.append(pos)
            flat_gene.append(gene_index)
            flat_aa.append(aa_id)
        if len(positions) < MIN_HEAD_CODONS:
            for _ in positions:
                flat_y.pop()
                flat_position.pop()
                flat_gene.pop()
                flat_aa.pop()
            skipped["no_sense_events_after_stop_filter"] += 1
            continue
        genes.append(gene_id)
        full_sequences.append(full_seq)
        event_positions_by_gene.append(positions)
        raw_y_by_gene.append(values)
        head_lengths.append(len(head))

    residual_y, control_summary = residualize_dwell(flat_y, flat_position, flat_gene, flat_aa)
    residual_y_by_gene: list[list[float]] = [[] for _ in genes]
    cursor = 0
    for gene_index, values in enumerate(raw_y_by_gene):
        n = len(values)
        residual_y_by_gene[gene_index] = residual_y[cursor : cursor + n]
        cursor += n
    if cursor != len(residual_y):
        raise RuntimeError("residual split cursor mismatch")

    return {
        "context": context,
        "genes": genes,
        "full_sequences": full_sequences,
        "event_positions_by_gene": event_positions_by_gene,
        "residual_y_by_gene": residual_y_by_gene,
        "n_obs": len(residual_y),
        "y_energy": sum(value * value for value in residual_y),
        "schema": schema,
        "control_summary": control_summary,
        "alignment_summary": {
            "n_genes": len(genes),
            "n_observations": len(residual_y),
            "min_head_codons": MIN_HEAD_CODONS,
            "head_window_lengths": sorted(set(head_lengths)),
            "zero_raw_occupancy_fraction": zero_raw_positions / len(flat_y) if flat_y else 0.0,
            "skipped": skipped,
            "occupancy_schema_head_codons_retained": occupancy.get("head_codons_retained"),
            "occupancy_schema_tail_codons_retained": occupancy.get("tail_codons_retained"),
            "joined_gene_count_after_length_check": schema.get("joined_gene_count_after_length_check"),
        },
    }


def q_label_sequences(
    sequences: list[list[str]],
    q_label_by_codon: dict[str, int],
) -> list[list[int | None]]:
    return [[q_label_by_codon.get(codon) for codon in seq] for seq in sequences]


def shuffled_synonymous_sequence(seq: list[str], code: dict[str, str], rng: random.Random) -> list[str]:
    positions_by_aa: dict[str, list[int]] = {}
    codons_by_aa: dict[str, list[str]] = {}
    for index, codon in enumerate(seq):
        aa = code.get(codon)
        if aa is None:
            continue
        positions_by_aa.setdefault(aa, []).append(index)
        codons_by_aa.setdefault(aa, []).append(codon)
    out = list(seq)
    for aa in sorted(positions_by_aa):
        values = list(codons_by_aa[aa])
        rng.shuffle(values)
        for position, codon in zip(positions_by_aa[aa], values):
            out[position] = codon
    return out


def state_key(labels: list[int | None], position: int, order: int) -> int:
    if order == 0:
        return 0
    current = UNK if position >= len(labels) or labels[position] is None else int(labels[position]) + 2
    if order == 1:
        return current
    prev_index = position - 1
    previous = BOS if prev_index < 0 else (UNK if labels[prev_index] is None else int(labels[prev_index]) + 2)
    return previous * STATE_BASE + current


def build_state_stats_by_order(
    q_labels: list[list[int | None]],
    event_positions_by_gene: list[list[int]],
    y_by_gene: list[list[float]],
) -> list[list[dict[int, tuple[int, float, float]]]]:
    # event_positions_by_gene is retained in the signature to document that q_labels
    # are already aligned to retained head-window event positions.
    by_order: list[list[dict[int, tuple[int, float, float]]]] = [[] for _ in range(MAX_CONTEXT_ORDER + 1)]
    for labels, _positions, y_values in zip(q_labels, event_positions_by_gene, y_by_gene):
        tmp0: dict[int, list[float]] = {0: [0.0, 0.0, 0.0]}
        tmp1: dict[int, list[float]] = {}
        tmp2: dict[int, list[float]] = {}
        previous = BOS
        for label, y in zip(labels, y_values):
            current = UNK if label is None else int(label) + 2
            y2 = y * y
            row0 = tmp0[0]
            row0[0] += 1.0
            row0[1] += y
            row0[2] += y2
            row1 = tmp1.setdefault(current, [0.0, 0.0, 0.0])
            row1[0] += 1.0
            row1[1] += y
            row1[2] += y2
            key2 = previous * STATE_BASE + current
            row2 = tmp2.setdefault(key2, [0.0, 0.0, 0.0])
            row2[0] += 1.0
            row2[1] += y
            row2[2] += y2
            previous = current
        by_order[0].append({key: (int(row[0]), row[1], row[2]) for key, row in tmp0.items()})
        by_order[1].append({key: (int(row[0]), row[1], row[2]) for key, row in tmp1.items()})
        by_order[2].append({key: (int(row[0]), row[1], row[2]) for key, row in tmp2.items()})
    return by_order


def build_eval_stats(
    *,
    q_labels_by_gene: list[list[int | None]],
    q_feature_by_label: list[tuple[float, float, float]],
    y_by_gene: list[list[float]],
    gene_to_fold: list[int],
    fold_count: int,
) -> tuple[list[list[dict[int, tuple[int, float, float]]]], list[list[list[float]]], list[list[float]], list[float]]:
    state_stats_by_order: list[list[dict[int, tuple[int, float, float]]]] = [[] for _ in range(MAX_CONTEXT_ORDER + 1)]
    xtx = [[[0.0 for _ in range(3)] for _ in range(3)] for _ in range(fold_count)]
    xty = [[0.0 for _ in range(3)] for _ in range(fold_count)]
    y2_by_fold = [0.0 for _ in range(fold_count)]
    zero = (0.0, 0.0, 0.0)
    for gene_index, (labels, y_values) in enumerate(zip(q_labels_by_gene, y_by_gene)):
        fold = gene_to_fold[gene_index]
        tmp0: dict[int, list[float]] = {0: [0.0, 0.0, 0.0]}
        tmp1: dict[int, list[float]] = {}
        tmp2: dict[int, list[float]] = {}
        previous = BOS
        for label, y in zip(labels, y_values):
            current = UNK if label is None else int(label) + 2
            x = zero if label is None else q_feature_by_label[int(label)]
            y2 = y * y
            row0 = tmp0[0]
            row0[0] += 1.0
            row0[1] += y
            row0[2] += y2
            row1 = tmp1.setdefault(current, [0.0, 0.0, 0.0])
            row1[0] += 1.0
            row1[1] += y
            row1[2] += y2
            key2 = previous * STATE_BASE + current
            row2 = tmp2.setdefault(key2, [0.0, 0.0, 0.0])
            row2[0] += 1.0
            row2[1] += y
            row2[2] += y2
            previous = current

            y2_by_fold[fold] += y2
            for i in range(3):
                xty[fold][i] += x[i] * y
                for j in range(i + 1):
                    xtx[fold][i][j] += x[i] * x[j]
        state_stats_by_order[0].append({key: (int(row[0]), row[1], row[2]) for key, row in tmp0.items()})
        state_stats_by_order[1].append({key: (int(row[0]), row[1], row[2]) for key, row in tmp1.items()})
        state_stats_by_order[2].append({key: (int(row[0]), row[1], row[2]) for key, row in tmp2.items()})
    for fold in range(fold_count):
        for i in range(3):
            for j in range(i):
                xtx[fold][j][i] = xtx[fold][i][j]
    return state_stats_by_order, xtx, xty, y2_by_fold


def aggregate_state_by_fold(
    *,
    state_stats_for_order: list[dict[int, tuple[int, float, float]]],
    gene_indices: list[int],
    fold_by_gene: dict[int, int],
    fold_count: int,
) -> tuple[dict[int, list[object]], list[int], list[float], list[float]]:
    states: dict[int, list[object]] = {}
    fold_counts = [0 for _ in range(fold_count)]
    fold_sums = [0.0 for _ in range(fold_count)]
    fold_sumsq = [0.0 for _ in range(fold_count)]
    for gene_index in gene_indices:
        fold = fold_by_gene[gene_index]
        for key, (g_count, g_sum, g_sumsq) in state_stats_for_order[gene_index].items():
            row = states.get(key)
            if row is None:
                row = [0, 0.0, 0.0, [0 for _ in range(fold_count)], [0.0 for _ in range(fold_count)], [0.0 for _ in range(fold_count)]]
                states[key] = row
            row[0] = int(row[0]) + g_count
            row[1] = float(row[1]) + g_sum
            row[2] = float(row[2]) + g_sumsq
            counts: list[int] = row[3]  # type: ignore[assignment]
            sums: list[float] = row[4]  # type: ignore[assignment]
            sumsq: list[float] = row[5]  # type: ignore[assignment]
            counts[fold] += g_count
            sums[fold] += g_sum
            sumsq[fold] += g_sumsq
            fold_counts[fold] += g_count
            fold_sums[fold] += g_sum
            fold_sumsq[fold] += g_sumsq
    return states, fold_counts, fold_sums, fold_sumsq


def inner_sse_for_order(states: dict[int, list[object]], fold_counts: list[int], fold_sums: list[float], fold_sumsq: list[float]) -> tuple[float, list[int], list[int]]:
    total_count = sum(fold_counts)
    total_sum = sum(fold_sums)
    sse = 0.0
    train_state_counts: list[int] = []
    train_obs_counts: list[int] = []
    for fold in range(len(fold_counts)):
        train_count_all = total_count - fold_counts[fold]
        train_sum_all = total_sum - fold_sums[fold]
        fallback = train_sum_all / train_count_all if train_count_all > 0 else 0.0
        fold_sse = 0.0
        state_count = 0
        for row in states.values():
            count = int(row[0])
            total_state_sum = float(row[1])
            counts: list[int] = row[3]  # type: ignore[assignment]
            sums: list[float] = row[4]  # type: ignore[assignment]
            sumsq: list[float] = row[5]  # type: ignore[assignment]
            val_count = counts[fold]
            if val_count <= 0:
                if count > 0:
                    state_count += 1
                continue
            train_state_count = count - val_count
            if train_state_count > 0:
                pred = (total_state_sum - sums[fold]) / train_state_count
                state_count += 1
            else:
                pred = fallback
            fold_sse += sumsq[fold] - 2.0 * pred * sums[fold] + pred * pred * val_count
        sse += fold_sse
        train_state_counts.append(state_count)
        train_obs_counts.append(train_count_all)
    return sse, train_state_counts, train_obs_counts


def select_transducer(
    *,
    state_stats_by_order: list[list[dict[int, tuple[int, float, float]]]],
    train_genes: list[int],
    material: str,
) -> dict[str, object]:
    inner_local_folds = deterministic_folds(len(train_genes), material, INNER_FOLD_COUNT)
    fold_by_gene: dict[int, int] = {}
    for fold, local_indices in enumerate(inner_local_folds):
        for local_index in local_indices:
            fold_by_gene[train_genes[local_index]] = fold
    best: tuple[float, int, float, int] | None = None
    best_summary: dict[str, object] = {}
    for order in range(MAX_CONTEXT_ORDER + 1):
        states, fold_counts, fold_sums, fold_sumsq = aggregate_state_by_fold(
            state_stats_for_order=state_stats_by_order[order],
            gene_indices=train_genes,
            fold_by_gene=fold_by_gene,
            fold_count=INNER_FOLD_COUNT,
        )
        sse, state_counts, train_obs_counts = inner_sse_for_order(states, fold_counts, fold_sums, fold_sumsq)
        for lam in MDL_LAMBDAS:
            penalty = sum(lam * state_counts[i] * math.log(max(2, train_obs_counts[i])) for i in range(len(state_counts)))
            objective = sse + penalty
            rank = (objective, order, lam, len(states))
            if best is None or rank < best:
                best = rank
                best_summary = {
                    "context_order": order,
                    "lambda": lam,
                    "inner_sse": sse,
                    "inner_mdl_objective": objective,
                    "inner_state_count_mean": mean([float(value) for value in state_counts]),
                    "inner_train_observations_mean": mean([float(value) for value in train_obs_counts]),
                }
    if best is None:
        raise RuntimeError("transducer selection produced no candidate")
    return best_summary


def state_outer_eval(
    *,
    state_stats_for_order: list[dict[int, tuple[int, float, float]]],
    train_genes: list[int],
    test_genes: list[int],
) -> dict[str, object]:
    train_states: dict[int, list[float]] = {}
    train_count = 0
    train_sum = 0.0
    for gene_index in train_genes:
        for key, (g_count, g_sum, _g_sumsq) in state_stats_for_order[gene_index].items():
            row = train_states.setdefault(key, [0.0, 0.0])
            row[0] += g_count
            row[1] += g_sum
            train_count += g_count
            train_sum += g_sum
    fallback = train_sum / train_count if train_count > 0 else 0.0
    means = {key: row[1] / row[0] for key, row in train_states.items() if row[0] > 0}
    test_sse = 0.0
    test_count = 0
    unseen_count = 0
    for gene_index in test_genes:
        for key, (g_count, g_sum, g_sumsq) in state_stats_for_order[gene_index].items():
            pred = means.get(key)
            if pred is None:
                pred = fallback
                unseen_count += g_count
            test_sse += g_sumsq - 2.0 * pred * g_sum + pred * pred * g_count
            test_count += g_count
    return {
        "sse": test_sse,
        "state_count": len(means),
        "test_observations": test_count,
        "unseen_state_observations": unseen_count,
    }


def ridge_fold_stats_from_features(
    *,
    q_features_by_gene: list[list[tuple[float, float, float]]],
    y_by_gene: list[list[float]],
    gene_to_fold: list[int],
    fold_count: int,
) -> tuple[list[list[list[float]]], list[list[float]], list[float]]:
    xtx = [[[0.0 for _ in range(3)] for _ in range(3)] for _ in range(fold_count)]
    xty = [[0.0 for _ in range(3)] for _ in range(fold_count)]
    y2 = [0.0 for _ in range(fold_count)]
    for gene_index, features in enumerate(q_features_by_gene):
        fold = gene_to_fold[gene_index]
        for x, y in zip(features, y_by_gene[gene_index]):
            y2[fold] += y * y
            for i in range(3):
                xty[fold][i] += x[i] * y
                for j in range(i + 1):
                    xtx[fold][i][j] += x[i] * x[j]
    for fold in range(fold_count):
        for i in range(3):
            for j in range(i):
                xtx[fold][j][i] = xtx[fold][i][j]
    return xtx, xty, y2


def add_matrices(mats: list[list[list[float]]]) -> list[list[float]]:
    out = [[0.0 for _ in range(3)] for _ in range(3)]
    for mat in mats:
        for i in range(3):
            for j in range(3):
                out[i][j] += mat[i][j]
    return out


def add_vectors(vectors: list[list[float]]) -> list[float]:
    out = [0.0, 0.0, 0.0]
    for vec in vectors:
        for i in range(3):
            out[i] += vec[i]
    return out


def subtract_matrix(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    return [[left[i][j] - right[i][j] for j in range(3)] for i in range(3)]


def subtract_vector(left: list[float], right: list[float]) -> list[float]:
    return [left[i] - right[i] for i in range(3)]


def quadratic(beta: list[float], mat: list[list[float]]) -> float:
    total = 0.0
    for i in range(3):
        for j in range(3):
            total += beta[i] * mat[i][j] * beta[j]
    return total


def ridge_sse_by_gene_folds(
    *,
    q_features_by_gene: list[list[tuple[float, float, float]]],
    y_by_gene: list[list[float]],
    gene_to_fold: list[int],
    fold_count: int,
) -> dict[str, object]:
    fold_xtx, fold_xty, fold_y2 = ridge_fold_stats_from_features(
        q_features_by_gene=q_features_by_gene,
        y_by_gene=y_by_gene,
        gene_to_fold=gene_to_fold,
        fold_count=fold_count,
    )
    total_xtx = add_matrices(fold_xtx)
    total_xty = add_vectors(fold_xty)
    sse = 0.0
    ridge_steps: list[int] = []
    for fold in range(fold_count):
        train_xtx = subtract_matrix(total_xtx, fold_xtx[fold])
        train_xty = subtract_vector(total_xty, fold_xty[fold])
        for i in range(3):
            train_xtx[i][i] += RIDGE_ALPHA
        beta, ridge_step = solve_linear_system(train_xtx, train_xty)
        ridge_steps.append(ridge_step)
        sse += fold_y2[fold] - 2.0 * vector_dot(beta, fold_xty[fold]) + quadratic(beta, fold_xtx[fold])
    return {
        "sse": sse,
        "ridge_alpha": RIDGE_ALPHA,
        "ridge_refit_count": sum(1 for step in ridge_steps if step > 0),
        "max_ridge_step": max(ridge_steps) if ridge_steps else 0,
    }


def ridge_sse_from_fold_stats(
    fold_xtx: list[list[list[float]]],
    fold_xty: list[list[float]],
    fold_y2: list[float],
) -> dict[str, object]:
    total_xtx = add_matrices(fold_xtx)
    total_xty = add_vectors(fold_xty)
    sse = 0.0
    ridge_steps: list[int] = []
    for fold in range(len(fold_xtx)):
        train_xtx = subtract_matrix(total_xtx, fold_xtx[fold])
        train_xty = subtract_vector(total_xty, fold_xty[fold])
        for i in range(3):
            train_xtx[i][i] += RIDGE_ALPHA
        beta, ridge_step = solve_linear_system(train_xtx, train_xty)
        ridge_steps.append(ridge_step)
        sse += fold_y2[fold] - 2.0 * vector_dot(beta, fold_xty[fold]) + quadratic(beta, fold_xtx[fold])
    return {
        "sse": sse,
        "ridge_alpha": RIDGE_ALPHA,
        "ridge_refit_count": sum(1 for step in ridge_steps if step > 0),
        "max_ridge_step": max(ridge_steps) if ridge_steps else 0,
    }


def evaluate_transducer(
    *,
    state_stats_by_order: list[list[dict[int, tuple[int, float, float]]]],
    gene_folds: list[list[int]],
    material: str,
) -> dict[str, object]:
    total_state_sse = 0.0
    total_q_state_sse = 0.0
    j_state = 0.0
    j_q_only = 0.0
    selected: list[dict[str, object]] = []
    all_genes = set(range(len(state_stats_by_order[0])))
    for outer_fold, test_genes in enumerate(gene_folds):
        test_set = set(test_genes)
        train_genes = sorted(all_genes - test_set)
        selection = select_transducer(
            state_stats_by_order=state_stats_by_order,
            train_genes=train_genes,
            material=f"{material}|outer={outer_fold}|inner",
        )
        order = int(selection["context_order"])
        lam = float(selection["lambda"])
        state_eval = state_outer_eval(
            state_stats_for_order=state_stats_by_order[order],
            train_genes=train_genes,
            test_genes=test_genes,
        )
        q_eval = state_outer_eval(
            state_stats_for_order=state_stats_by_order[1],
            train_genes=train_genes,
            test_genes=test_genes,
        )
        total_state_sse += float(state_eval["sse"])
        total_q_state_sse += float(q_eval["sse"])
        j_state += float(state_eval["sse"]) + lam * int(state_eval["state_count"]) * math.log(max(2, int(state_eval["test_observations"])))
        j_q_only += float(q_eval["sse"]) + lam * int(q_eval["state_count"]) * math.log(max(2, int(q_eval["test_observations"])))
        selected.append(
            {
                **selection,
                "outer_fold": outer_fold,
                "outer_state_count": state_eval["state_count"],
                "outer_test_observations": state_eval["test_observations"],
                "outer_unseen_state_observations": state_eval["unseen_state_observations"],
                "q_only_state_count": q_eval["state_count"],
            }
        )
    return {
        "sse": total_state_sse,
        "q_only_state_sse": total_q_state_sse,
        "j_state": j_state,
        "j_q_only": j_q_only,
        "selected": selected,
    }


def shuffled_sequences(
    sequences: list[list[str]],
    code: dict[str, str],
    iteration: int,
) -> list[list[str]]:
    out: list[list[str]] = []
    for gene_index, seq in enumerate(sequences):
        rng = random.Random(stable_int(f"{SEED}|synonymous_shuffle|iteration={iteration}|gene_index={gene_index}"))
        out.append(shuffled_synonymous_sequence(seq, code, rng))
    return out


def head_labels_and_features(
    *,
    sequences: list[list[str]],
    event_positions_by_gene: list[list[int]],
    q_label_by_codon: dict[str, int],
    q_by_codon: dict[str, tuple[float, float, float]],
) -> tuple[list[list[int | None]], list[tuple[float, float, float]]]:
    labels_by_gene: list[list[int | None]] = []
    max_label = max(q_label_by_codon.values()) if q_label_by_codon else -1
    feature_by_label = [(0.0, 0.0, 0.0) for _ in range(max_label + 1)]
    for codon, label in q_label_by_codon.items():
        feature_by_label[label] = q_by_codon[codon]
    for seq, positions in zip(sequences, event_positions_by_gene):
        labels: list[int | None] = []
        for position in positions:
            codon = seq[position]
            labels.append(q_label_by_codon.get(codon))
        labels_by_gene.append(labels)
    return labels_by_gene, feature_by_label


def shuffled_head_labels_and_features(
    *,
    observed_labels: list[list[int | None]],
    shuffle_groups_by_gene: list[list[list[int]]],
    iteration: int,
) -> list[list[int | None]]:
    labels_out: list[list[int | None]] = []
    for gene_index, groups in enumerate(shuffle_groups_by_gene):
        rng = random.Random(stable_int(f"{SEED}|synonymous_shuffle|iteration={iteration}|gene_index={gene_index}"))
        labels = list(observed_labels[gene_index])
        original_labels = observed_labels[gene_index]
        for local_indices in groups:
            source = list(local_indices)
            rng.shuffle(source)
            for target_index, source_index in zip(local_indices, source):
                labels[target_index] = original_labels[source_index]
        labels_out.append(labels)
    return labels_out


def init_null_worker(state: dict[str, object]) -> None:
    NULL_WORKER_STATE.clear()
    NULL_WORKER_STATE.update(state)


def null_worker(iteration: int) -> float:
    observed_labels: list[list[int | None]] = NULL_WORKER_STATE["observed_labels"]  # type: ignore[assignment]
    shuffle_groups_by_gene: list[list[list[int]]] = NULL_WORKER_STATE["shuffle_groups_by_gene"]  # type: ignore[assignment]
    q_feature_by_label: list[tuple[float, float, float]] = NULL_WORKER_STATE["q_feature_by_label"]  # type: ignore[assignment]
    context: dict[str, object] = NULL_WORKER_STATE["context"]  # type: ignore[assignment]
    event_positions_by_gene: list[list[int]] = NULL_WORKER_STATE["event_positions_by_gene"]  # type: ignore[assignment]
    y_by_gene: list[list[float]] = NULL_WORKER_STATE["y_by_gene"]  # type: ignore[assignment]
    gene_folds: list[list[int]] = NULL_WORKER_STATE["gene_folds"]  # type: ignore[assignment]
    gene_to_fold: list[int] = NULL_WORKER_STATE["gene_to_fold"]  # type: ignore[assignment]
    y_energy = float(NULL_WORKER_STATE["y_energy"])
    shuffled_labels = shuffled_head_labels_and_features(
        observed_labels=observed_labels,
        shuffle_groups_by_gene=shuffle_groups_by_gene,
        iteration=iteration,
    )
    fit = evaluate_once(
        q_labels_by_gene=shuffled_labels,
        q_feature_by_label=q_feature_by_label,
        context=context,
        event_positions_by_gene=event_positions_by_gene,
        y_by_gene=y_by_gene,
        gene_folds=gene_folds,
        gene_to_fold=gene_to_fold,
        y_energy=y_energy,
        material=f"{SEED}|null|iteration={iteration}",
    )
    return float(fit["delta_r2_transducer_vs_memoryless"])


def head_shuffle_groups(
    *,
    sequences: list[list[str]],
    event_positions_by_gene: list[list[int]],
    code: dict[str, str],
) -> list[list[list[int]]]:
    out: list[list[list[int]]] = []
    for seq, positions in zip(sequences, event_positions_by_gene):
        grouped: dict[str, list[int]] = {}
        for local_index, position in enumerate(positions):
            grouped.setdefault(code[seq[position]], []).append(local_index)
        out.append([grouped[aa] for aa in sorted(grouped)])
    return out


def evaluate_once(
    *,
    q_labels_by_gene: list[list[int | None]],
    q_feature_by_label: list[tuple[float, float, float]],
    context: dict[str, object],
    event_positions_by_gene: list[list[int]],
    y_by_gene: list[list[float]],
    gene_folds: list[list[int]],
    gene_to_fold: list[int],
    y_energy: float,
    material: str,
) -> dict[str, object]:
    state_stats_by_order, fold_xtx, fold_xty, fold_y2 = build_eval_stats(
        q_labels_by_gene=q_labels_by_gene,
        q_feature_by_label=q_feature_by_label,
        y_by_gene=y_by_gene,
        gene_to_fold=gene_to_fold,
        fold_count=FOLD_COUNT,
    )
    ridge = ridge_sse_from_fold_stats(fold_xtx, fold_xty, fold_y2)
    transducer = evaluate_transducer(
        state_stats_by_order=state_stats_by_order,
        gene_folds=gene_folds,
        material=material,
    )
    ridge_sse = float(ridge["sse"])
    state_sse = float(transducer["sse"])
    return {
        "memoryless_ridge_sse": ridge_sse,
        "transducer_sse": state_sse,
        "memoryless_ridge_r2": 1.0 - ridge_sse / y_energy if y_energy > EPS else 0.0,
        "transducer_r2": 1.0 - state_sse / y_energy if y_energy > EPS else 0.0,
        "delta_r2_transducer_vs_memoryless": (ridge_sse - state_sse) / y_energy if y_energy > EPS else 0.0,
        "ridge": ridge,
        "transducer": transducer,
    }


def compact_selection(selected: list[dict[str, object]]) -> dict[str, object]:
    orders = [int(row["context_order"]) for row in selected]
    lambdas = [float(row["lambda"]) for row in selected]
    counts = [int(row["outer_state_count"]) for row in selected]
    q_counts = [int(row["q_only_state_count"]) for row in selected]
    return {
        "context_orders_by_fold": orders,
        "lambdas_by_fold": lambdas,
        "state_counts_by_fold": counts,
        "q_only_state_counts_by_fold": q_counts,
        "selected_state_count_mean": mean([float(value) for value in counts]),
        "selected_state_count_max": max(counts) if counts else 0,
        "selected_context_order_max": max(orders) if orders else 0,
        "selected_memory_order_positive_in_any_fold": any(order > 1 for order in orders),
    }


def main() -> None:
    repo = pathlib.Path.cwd()
    try:
        data = load_event_stream(repo)
        n_genes = len(data["genes"])  # type: ignore[arg-type]
        n_obs = int(data["n_obs"])
        if n_genes < FOLD_COUNT or n_obs <= 0:
            emit("needs_data", reason="insufficient aligned head-window event stream", payload=data.get("alignment_summary", {}))
        y_energy = float(data["y_energy"])
        if y_energy <= EPS:
            emit("needs_data", reason="zero residualized dwell energy after fixed-effect controls")

        gene_folds = deterministic_folds(n_genes, f"{SEED}|outer_gene_folds", FOLD_COUNT)
        gene_to_fold = [0 for _ in range(n_genes)]
        for fold, genes in enumerate(gene_folds):
            for gene_index in genes:
                gene_to_fold[gene_index] = fold

        context: dict[str, object] = data["context"]  # type: ignore[assignment]
        sequences: list[list[str]] = data["full_sequences"]  # type: ignore[assignment]
        event_positions_by_gene: list[list[int]] = data["event_positions_by_gene"]  # type: ignore[assignment]
        y_by_gene: list[list[float]] = data["residual_y_by_gene"]  # type: ignore[assignment]
        q_label_by_codon: dict[str, int] = context["q_label_by_codon"]  # type: ignore[assignment]
        q_by_codon: dict[str, tuple[float, float, float]] = context["q_by_codon"]  # type: ignore[assignment]
        observed_labels, q_feature_by_label = head_labels_and_features(
            sequences=sequences,
            event_positions_by_gene=event_positions_by_gene,
            q_label_by_codon=q_label_by_codon,
            q_by_codon=q_by_codon,
        )

        observed = evaluate_once(
            q_labels_by_gene=observed_labels,
            q_feature_by_label=q_feature_by_label,
            context=context,
            event_positions_by_gene=event_positions_by_gene,
            y_by_gene=y_by_gene,
            gene_folds=gene_folds,
            gene_to_fold=gene_to_fold,
            y_energy=y_energy,
            material=f"{SEED}|observed",
        )

        code: dict[str, str] = context["code"]  # type: ignore[assignment]
        shuffle_groups_by_gene = head_shuffle_groups(
            sequences=sequences,
            event_positions_by_gene=event_positions_by_gene,
            code=code,
        )
        worker_state = {
            "observed_labels": observed_labels,
            "shuffle_groups_by_gene": shuffle_groups_by_gene,
            "q_feature_by_label": q_feature_by_label,
            "context": context,
            "event_positions_by_gene": event_positions_by_gene,
            "y_by_gene": y_by_gene,
            "gene_folds": gene_folds,
            "gene_to_fold": gene_to_fold,
            "y_energy": y_energy,
        }
        if NULL_B <= 1 or NULL_WORKERS <= 1:
            init_null_worker(worker_state)
            null_deltas = [null_worker(iteration) for iteration in range(NULL_B)]
        else:
            worker_count = max(1, min(NULL_WORKERS, NULL_B))
            ctx = multiprocessing.get_context("fork") if hasattr(os, "fork") else multiprocessing.get_context()
            with ctx.Pool(processes=worker_count, initializer=init_null_worker, initargs=(worker_state,)) as pool:
                null_deltas = list(pool.imap(null_worker, range(NULL_B), chunksize=1))

        transducer = observed["transducer"]  # type: ignore[assignment]
        selected = transducer["selected"]  # type: ignore[index]
        selection_summary = compact_selection(selected)  # type: ignore[arg-type]
        null95 = percentile_nearest_rank(null_deltas, 0.95)
        delta = float(observed["delta_r2_transducer_vs_memoryless"])
        j_state = float(transducer["j_state"])  # type: ignore[index]
        j_q_only = float(transducer["j_q_only"])  # type: ignore[index]
        collapsed_to_order0 = selection_summary["selected_context_order_max"] == 0
        positive = (
            delta > null95
            and j_state < j_q_only
            and not collapsed_to_order0
            and bool(selection_summary["selected_memory_order_positive_in_any_fold"])
        )
        conclusion = (
            "order_signal_positive: leakage-proof predictive-memory in retained 5prime dwell windows; footprint-density proxy only, not causal elongation-rate"
            if positive
            else "markov_order_0_negative: local dwell in these three B*_Q6 axes is Markov-order-0 under the memory-collapse and synonymous-order null controls; no causal elongation-rate claim"
        )
        checks = {
            "aligned_event_stream": n_genes > 0 and n_obs > 0,
            "residualized_dwell_controls": float(data["control_summary"]["iterative_position_gene_aa_fixed_effect_r2"]) >= 0.0,  # type: ignore[index]
            "memoryless_baseline": math.isfinite(float(observed["memoryless_ridge_r2"])),
            "finite_state_transducer_mdl": math.isfinite(j_state) and len(selected) == FOLD_COUNT,  # type: ignore[arg-type]
            "memory_collapse_control": math.isfinite(delta) and math.isfinite(j_q_only),
            "within_gene_synonymous_null": len(null_deltas) == NULL_B and math.isfinite(null95),
            "order_signal_verdict": conclusion.startswith("order_signal_positive") if positive else conclusion.startswith("markov_order_0_negative"),
        }
        status = "passed" if positive else "failed"
        emit(
            status,
            checks=checks,
            payload={
                "conclusion": conclusion,
                "delta_r2_transducer_vs_memoryless": delta,
                "null95_delta_r2": null95,
                "null_delta_r2_distribution": {
                    "n": len(null_deltas),
                    "mean": mean(null_deltas),
                    "min": min(null_deltas) if null_deltas else None,
                    "max": max(null_deltas) if null_deltas else None,
                    "p95": null95,
                },
                "memoryless_ridge_heldout_r2": observed["memoryless_ridge_r2"],
                "transducer_heldout_r2": observed["transducer_r2"],
                "memoryless_ridge_sse": observed["memoryless_ridge_sse"],
                "transducer_sse": observed["transducer_sse"],
                "j_state": j_state,
                "j_q_only": j_q_only,
                "selected_state_count": selection_summary["selected_state_count_mean"],
                "selected_state_summary": selection_summary,
                "actual_B": NULL_B,
                "null_workers": max(1, min(NULL_WORKERS, NULL_B)),
                "n_genes": n_genes,
                "n_observations": n_obs,
                "control_r2_before_after": data["control_summary"],
                "alignment": data["alignment_summary"],
                "model_contract": {
                    "target": "rel_occupancy_5prime residualized by position-index ramp, within-gene mean level, and amino-acid identity fixed effects",
                    "memoryless": "ridge residual dwell ~ current q_t=(K_AAA, Arg_AGR, f3_stress) only",
                    "transducer": "nested gene-fold selected variable-order finite-state context over ordered q_t stream; state means are frozen before outer test genes",
                    "memory_collapse_control": "J_state compared with forced current-q-only state model, not with unrelated TE/stability/turnover controls",
                    "null": "within-gene synonymous shuffle preserving amino-acid positions and observed dwell, with transducer refit for every shuffle",
                    "cannot_claim": "ribosome footprint occupancy is a density proxy and does not identify causal kinetic dwell or elongation rate",
                },
            },
        )
    except Exception as exc:
        emit("error", reason=str(exc), exception_type=exc.__class__.__name__)


if __name__ == "__main__":
    main()

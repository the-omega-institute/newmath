#!/usr/bin/env python3
"""tRNA decoding pressure on synonymous hidden edges at fixed e_in."""

from __future__ import annotations

import csv
import gzip
import json
import math
import random
import re
import statistics
import sys
from pathlib import Path


EXPERIMENT_ID = "trna_decoding_pressure_hidden_edges"
CLAIM_ID = "bridge.genetic_code.trna_decoding_pressure_hidden_edges"
TRNA_PATH = Path("/tmp/proteingym_cache/GSE128812_maturetRNA_ReadCount_Ecoli.csv.gz")
CDS_PATH = Path("/tmp/proteingym_cache/ecoli_cds.fna.gz")
SEEDS = (19021, 19031, 19051)
TARGET_SLICE_HITS = 50_000
TARGET_E_IN = 67
SENSE_AAS = {
    "Ala",
    "Arg",
    "Asn",
    "Asp",
    "Cys",
    "Gln",
    "Glu",
    "Gly",
    "His",
    "Ile",
    "Leu",
    "Lys",
    "Met",
    "Phe",
    "Pro",
    "Ser",
    "Thr",
    "Trp",
    "Tyr",
    "Val",
}


AA3_TO_1 = {
    "Ala": "A",
    "Arg": "R",
    "Asn": "N",
    "Asp": "D",
    "Cys": "C",
    "Gln": "Q",
    "Glu": "E",
    "Gly": "G",
    "His": "H",
    "Ile": "I",
    "Leu": "L",
    "Lys": "K",
    "Met": "M",
    "Phe": "F",
    "Pro": "P",
    "Ser": "S",
    "Thr": "T",
    "Trp": "W",
    "Tyr": "Y",
    "Val": "V",
}


STANDARD_CODE = {
    "UUU": "F",
    "UUC": "F",
    "UUA": "L",
    "UUG": "L",
    "UCU": "S",
    "UCC": "S",
    "UCA": "S",
    "UCG": "S",
    "UAU": "Y",
    "UAC": "Y",
    "UAA": "*",
    "UAG": "*",
    "UGU": "C",
    "UGC": "C",
    "UGA": "*",
    "UGG": "W",
    "CUU": "L",
    "CUC": "L",
    "CUA": "L",
    "CUG": "L",
    "CCU": "P",
    "CCC": "P",
    "CCA": "P",
    "CCG": "P",
    "CAU": "H",
    "CAC": "H",
    "CAA": "Q",
    "CAG": "Q",
    "CGU": "R",
    "CGC": "R",
    "CGA": "R",
    "CGG": "R",
    "AUU": "I",
    "AUC": "I",
    "AUA": "I",
    "AUG": "M",
    "ACU": "T",
    "ACC": "T",
    "ACA": "T",
    "ACG": "T",
    "AAU": "N",
    "AAC": "N",
    "AAA": "K",
    "AAG": "K",
    "AGU": "S",
    "AGC": "S",
    "AGA": "R",
    "AGG": "R",
    "GUU": "V",
    "GUC": "V",
    "GUA": "V",
    "GUG": "V",
    "GCU": "A",
    "GCC": "A",
    "GCA": "A",
    "GCG": "A",
    "GAU": "D",
    "GAC": "D",
    "GAA": "E",
    "GAG": "E",
    "GGU": "G",
    "GGC": "G",
    "GGA": "G",
    "GGG": "G",
}


BASES = "UCAG"
COMP = {"A": "U", "U": "A", "T": "A", "C": "G", "G": "C"}
WOBBLE = {
    "A": ("U",),
    "C": ("G",),
    "G": ("C", "U"),
    "U": ("A", "G"),
    "T": ("A", "G"),
    "I": ("U", "C", "A"),
}


def emit(verdict: str, reason: str, payload: dict[str, object] | None = None) -> int:
    out: dict[str, object] = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "status": verdict,
        "verdict": verdict,
        "reason": reason,
    }
    if payload:
        out.update(payload)
    print(json.dumps(out, sort_keys=True, separators=(",", ":")))
    if verdict == "certified":
        return 0
    if verdict == "refuted":
        return 2
    return 3


def hamming1(a: str, b: str) -> bool:
    return sum(x != y for x, y in zip(a, b)) == 1


def transition_pair(a: str, b: str) -> bool:
    diffs = [(x, y) for x, y in zip(a, b) if x != y]
    return len(diffs) == 1 and set(diffs[0]) in ({"A", "G"}, {"C", "U"})


def gc_delta_pair(a: str, b: str) -> bool:
    return sum(x in "GC" for x in a) != sum(x in "GC" for x in b)


def anticodon_decodes(aa_raw: str, anticodon_raw: str) -> tuple[str, list[str]]:
    aa = "Met" if aa_raw == "fMet" else aa_raw
    anticodon = anticodon_raw.upper().replace("T", "U")
    if aa_raw == "Ile2" and anticodon == "CAU":
        return "Ile", ["AUA"]
    if aa in ("SeC", "Und") or "N" in anticodon:
        return aa, []
    if aa not in SENSE_AAS or len(anticodon) != 3:
        return aa, []
    try:
        first = COMP[anticodon[2]]
        second = COMP[anticodon[1]]
        thirds = WOBBLE[anticodon[0]]
    except KeyError:
        return aa, []
    decoded = [first + second + third for third in thirds]
    want = AA3_TO_1[aa]
    return aa, [c for c in decoded if STANDARD_CODE.get(c) == want]


def parse_trna_counts(codons: list[str]) -> tuple[list[str], dict[str, list[float]], list[tuple[str, list[float]]], int]:
    if not TRNA_PATH.exists():
        raise FileNotFoundError(str(TRNA_PATH))
    pools = {c: [] for c in codons}
    entries: list[tuple[str, list[float]]] = []
    n_samples = None
    row_re = re.compile(r"tRNA-([A-Za-z0-9]+)-([A-Za-z]{3})")
    with gzip.open(TRNA_PATH, "rt", newline="") as handle:
        reader = csv.reader(handle)
        header = next(reader)
        sample_names = header[1:]
        n_samples = len(sample_names)
        for c in codons:
            pools[c] = [0.0] * n_samples
        n_trna = 0
        for row in reader:
            if not row:
                continue
            name = row[0]
            match = row_re.search(name)
            if not match:
                continue
            aa_raw, anticodon = match.group(1), match.group(2)
            _aa, decoded = anticodon_decodes(aa_raw, anticodon)
            if not decoded:
                continue
            counts = [float(x) if x else 0.0 for x in row[1 : 1 + n_samples]]
            if len(counts) != n_samples:
                continue
            n_trna += 1
            entries.append((",".join(decoded), counts))
            for codon in decoded:
                for i, value in enumerate(counts):
                    pools[codon][i] += value
    return sample_names, pools, entries, n_trna


def permuted_pools(codons: list[str], entries: list[tuple[str, list[float]]]) -> dict[str, list[float]]:
    rng = random.Random(777331)
    decoded_sets = [x for x, _counts in entries]
    count_sets = [counts[:] for _decoded, counts in entries]
    rng.shuffle(count_sets)
    n_samples = len(count_sets[0]) if count_sets else 0
    pools = {c: [0.0] * n_samples for c in codons}
    for decoded_joined, counts in zip(decoded_sets, count_sets):
        for codon in decoded_joined.split(","):
            for i, value in enumerate(counts):
                pools[codon][i] += value
    return pools


def parse_codon_usage(codons: list[str]) -> dict[str, float]:
    usage = {c: 0.0 for c in codons}
    if not CDS_PATH.exists():
        return {c: 1.0 for c in codons}
    seq_parts: list[str] = []
    with gzip.open(CDS_PATH, "rt") as handle:
        for line in handle:
            line = line.strip().upper().replace("T", "U")
            if not line:
                continue
            if line.startswith(">"):
                for i in range(0, len("".join(seq_parts)) - 2, 3):
                    codon = "".join(seq_parts)[i : i + 3]
                    if codon in usage:
                        usage[codon] += 1.0
                seq_parts = []
            else:
                seq_parts.append(line)
        seq = "".join(seq_parts)
        for i in range(0, len(seq) - 2, 3):
            codon = seq[i : i + 3]
            if codon in usage:
                usage[codon] += 1.0
    mean = sum(usage.values()) / max(1, len(usage))
    if mean <= 0:
        return {c: 1.0 for c in codons}
    return {c: (usage[c] / mean if usage[c] > 0 else 0.0) for c in codons}


def build_pair_weights(
    pairs: list[tuple[int, int]],
    codons: list[str],
    pools: dict[str, list[float]],
    sample_index: int | None = None,
    usage: dict[str, float] | None = None,
    predicate=None,
) -> list[float]:
    weights = []
    for i, j in pairs:
        a, b = codons[i], codons[j]
        if predicate is not None and not predicate(a, b):
            weights.append(0.0)
            continue
        if sample_index is None:
            pool_a = sum(pools[a])
            pool_b = sum(pools[b])
        else:
            pool_a = pools[a][sample_index]
            pool_b = pools[b][sample_index]
        usage_a = 1.0 if usage is None else usage[a]
        usage_b = 1.0 if usage is None else usage[b]
        weights.append(usage_a * pool_b + usage_b * pool_a)
    return weights


def h_value(labels: tuple[int, ...] | list[int], pairs: list[tuple[int, int]], weights: list[float]) -> float:
    denom = sum(weights)
    if denom <= 0:
        return float("nan")
    num = 0.0
    for k, (i, j) in enumerate(pairs):
        if labels[i] == labels[j]:
            num += weights[k]
    return num / denom


def e_in(labels: tuple[int, ...] | list[int], pairs: list[tuple[int, int]]) -> int:
    return sum(1 for i, j in pairs if labels[i] == labels[j])


def run_chain(
    seed: int,
    initial: list[int],
    pairs: list[tuple[int, int]],
    quota: int,
    main_weights: list[float],
) -> tuple[list[tuple[int, ...]], list[float], int, bool]:
    rng = random.Random(seed)
    labels = initial[:]
    current_e = e_in(labels, pairs)
    hits: list[tuple[int, ...]] = []
    h_hits: list[float] = []
    accepted = 0
    steps = 0
    max_steps = 1_800_000
    burn = 5_000
    while len(hits) < quota and steps < max_steps:
        steps += 1
        i, j = rng.sample(range(len(labels)), 2)
        if labels[i] == labels[j]:
            continue
        old_i, old_j = labels[i], labels[j]
        old_penalty = (current_e - TARGET_E_IN) ** 2
        labels[i], labels[j] = labels[j], labels[i]
        new_e = e_in(labels, pairs)
        new_penalty = (new_e - TARGET_E_IN) ** 2
        lam = 4.0 if rng.random() < 0.5 else 8.0
        accept = new_penalty <= old_penalty or rng.random() < math.exp(-lam * (new_penalty - old_penalty))
        if accept:
            current_e = new_e
            accepted += 1
        else:
            labels[i], labels[j] = old_i, old_j
        if steps > burn and current_e == TARGET_E_IN and steps % 5 == 0:
            snap = tuple(labels)
            hits.append(snap)
            h_hits.append(h_value(snap, pairs, main_weights))
    return hits, h_hits, accepted, len(hits) >= quota


def empirical_p(null_values: list[float], observed: float) -> float:
    good = sum(1 for x in null_values if x >= observed)
    return (good + 1.0) / (len(null_values) + 1.0)


def finite_or_nan(value: float) -> float | None:
    return value if math.isfinite(value) else None


def main() -> int:
    codons = [a + b + c for a in BASES for b in BASES for c in BASES if STANDARD_CODE[a + b + c] != "*"]
    codon_index = {c: i for i, c in enumerate(codons)}
    aa_names = sorted(set(STANDARD_CODE[c] for c in codons))
    aa_index = {aa: i for i, aa in enumerate(aa_names)}
    standard_labels = [aa_index[STANDARD_CODE[c]] for c in codons]
    pairs = [(i, j) for i, a in enumerate(codons) for j in range(i + 1, len(codons)) if hamming1(a, codons[j])]

    try:
        sample_names, pools, trna_entries, n_trna = parse_trna_counts(codons)
    except Exception as exc:
        return emit(
            "needs_derivation",
            "data parsing failed",
            {
                "H_tRNA_std": None,
                "p_N67": None,
                "n_slice_hits": 0,
                "mixing_ok": False,
                "per_sample_direction": [],
                "permutation_p": None,
                "codon_usage_weighted_p": None,
                "n_trna": 0,
                "error": repr(exc),
            },
        )

    if n_trna <= 0 or len(sample_names) != 9:
        return emit(
            "needs_derivation",
            "unexpected tRNA sample structure",
            {
                "H_tRNA_std": None,
                "p_N67": None,
                "n_slice_hits": 0,
                "mixing_ok": False,
                "per_sample_direction": [],
                "permutation_p": None,
                "codon_usage_weighted_p": None,
                "n_trna": n_trna,
                "n_samples": len(sample_names),
            },
        )

    main_weights = build_pair_weights(pairs, codons, pools)
    if sum(main_weights) <= 0:
        return emit(
            "needs_derivation",
            "zero decoding pressure after parser filters",
            {
                "H_tRNA_std": None,
                "p_N67": None,
                "n_slice_hits": 0,
                "mixing_ok": False,
                "per_sample_direction": [],
                "permutation_p": None,
                "codon_usage_weighted_p": None,
                "n_trna": n_trna,
            },
        )

    quotas = [TARGET_SLICE_HITS // len(SEEDS)] * len(SEEDS)
    for i in range(TARGET_SLICE_HITS % len(SEEDS)):
        quotas[i] += 1
    all_hits: list[tuple[int, ...]] = []
    chain_medians: list[float] = []
    accepted_moves = 0
    chain_ok = True
    for seed, quota in zip(SEEDS, quotas):
        hits, h_hits, accepted, ok = run_chain(seed, standard_labels, pairs, quota, main_weights)
        all_hits.extend(hits)
        accepted_moves += accepted
        chain_ok = chain_ok and ok
        chain_medians.append(statistics.median(h_hits) if h_hits else float("nan"))

    n_slice_hits = len(all_hits)
    h_std = h_value(standard_labels, pairs, main_weights)
    null_h = [h_value(labels, pairs, main_weights) for labels in all_hits]
    p_main = empirical_p(null_h, h_std) if null_h else float("nan")
    grand_median = statistics.median(chain_medians) if all(math.isfinite(x) for x in chain_medians) else float("nan")
    if math.isfinite(grand_median) and abs(grand_median) > 1e-12:
        rel_spread = max(abs(x - grand_median) / abs(grand_median) for x in chain_medians)
    else:
        rel_spread = float("inf")
    mixing_ok = chain_ok and n_slice_hits >= TARGET_SLICE_HITS and rel_spread < 0.02

    per_sample_direction = []
    per_sample_h_std = []
    for sample_i in range(len(sample_names)):
        weights = build_pair_weights(pairs, codons, pools, sample_index=sample_i)
        obs = h_value(standard_labels, pairs, weights)
        vals = [h_value(labels, pairs, weights) for labels in all_hits]
        med = statistics.median(vals) if vals else float("nan")
        per_sample_h_std.append(finite_or_nan(obs))
        per_sample_direction.append(bool(math.isfinite(obs) and math.isfinite(med) and obs > med))

    usage = parse_codon_usage(codons)
    usage_weights = build_pair_weights(pairs, codons, pools, usage=usage)
    h_usage_std = h_value(standard_labels, pairs, usage_weights)
    usage_null = [h_value(labels, pairs, usage_weights) for labels in all_hits]
    usage_p = empirical_p(usage_null, h_usage_std) if usage_null else float("nan")

    perm_pools = permuted_pools(codons, trna_entries)
    perm_weights = build_pair_weights(pairs, codons, perm_pools)
    h_perm_std = h_value(standard_labels, pairs, perm_weights)
    perm_null = [h_value(labels, pairs, perm_weights) for labels in all_hits]
    permutation_p = empirical_p(perm_null, h_perm_std) if perm_null else float("nan")

    transition_weights = build_pair_weights(pairs, codons, pools, predicate=transition_pair)
    transversion_weights = build_pair_weights(pairs, codons, pools, predicate=lambda a, b: hamming1(a, b) and not transition_pair(a, b))
    gc_delta_weights = build_pair_weights(pairs, codons, pools, predicate=gc_delta_pair)
    transition_p = empirical_p([h_value(labels, pairs, transition_weights) for labels in all_hits], h_value(standard_labels, pairs, transition_weights))
    transversion_p = empirical_p([h_value(labels, pairs, transversion_weights) for labels in all_hits], h_value(standard_labels, pairs, transversion_weights))
    gc_delta_p = empirical_p([h_value(labels, pairs, gc_delta_weights) for labels in all_hits], h_value(standard_labels, pairs, gc_delta_weights))

    permutation_destroyed = math.isfinite(permutation_p) and permutation_p > 0.05
    direction_ok = all(per_sample_direction)
    significant = math.isfinite(p_main) and p_main <= 1e-3
    if significant and direction_ok and permutation_destroyed and mixing_ok:
        verdict = "certified"
        reason = "standard code concentrates tRNA near-cognate pressure on hidden synonymous edges at fixed e_in"
    elif not mixing_ok:
        verdict = "needs_derivation"
        reason = "N_67 slice MCMC did not satisfy the preregistered mixing and hit contract"
    else:
        verdict = "refuted"
        reason = "tRNA pressure alignment did not pass the preregistered significance, direction, and permutation gates"

    payload = {
        "H_tRNA_std": finite_or_nan(h_std),
        "p_N67": finite_or_nan(p_main),
        "n_slice_hits": n_slice_hits,
        "mixing_ok": mixing_ok,
        "per_sample_direction": per_sample_direction,
        "per_sample_H_tRNA_std": per_sample_h_std,
        "permutation_p": finite_or_nan(permutation_p),
        "codon_usage_weighted_p": finite_or_nan(usage_p),
        "n_trna": n_trna,
        "chain_medians": [finite_or_nan(x) for x in chain_medians],
        "chain_median_relative_spread": finite_or_nan(rel_spread),
        "accepted_moves": accepted_moves,
        "transition_p": finite_or_nan(transition_p),
        "transversion_p": finite_or_nan(transversion_p),
        "gc_delta_p": finite_or_nan(gc_delta_p),
        "H_tRNA_usage_weighted_std": finite_or_nan(h_usage_std),
        "H_tRNA_permuted_std": finite_or_nan(h_perm_std),
        "n_samples": len(sample_names),
        "standard_e_in": e_in(standard_labels, pairs),
        "reason": reason,
    }
    return emit(verdict, reason, payload)


if __name__ == "__main__":
    raise SystemExit(main())

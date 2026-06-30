#!/usr/bin/env python3
"""Degeneracy-matched edge-hiding test for the standard genetic code.

This experiment asks whether the standard code's codon assignment is a high
outlier for Hamming-1 synonymous edges once the labeled degeneracy profile is
fixed.  The primary statistic excludes Stop-incident edges; the all-codon
statistic counts Stop as its own output class.
"""
from __future__ import annotations

from collections import Counter
from itertools import product
import json
import math
import random
import sys


EXPERIMENT_ID = "code_edge_hiding_optimality"
CLAIM_ID = "bridge.genetic_code.edge_hiding_optimality"
NULL_SEED = 620260618
NULL_DRAWS = 200000
CERTIFIED_UPPER_TAIL = 0.001
REFUTED_LOWER_TAIL = 0.001
TYPICAL_TAIL_FLOOR = 0.05

BASES = ("U", "C", "A", "G")
BASE_TO_BITS = {"U": (0, 0), "C": (0, 1), "A": (1, 0), "G": (1, 1)}

CODON_TO_OUTPUT = {
    "UUU": "Phe", "UUC": "Phe", "UUA": "Leu", "UUG": "Leu",
    "UCU": "Ser", "UCC": "Ser", "UCA": "Ser", "UCG": "Ser",
    "UAU": "Tyr", "UAC": "Tyr", "UAA": "Stop", "UAG": "Stop",
    "UGU": "Cys", "UGC": "Cys", "UGA": "Stop", "UGG": "Trp",
    "CUU": "Leu", "CUC": "Leu", "CUA": "Leu", "CUG": "Leu",
    "CCU": "Pro", "CCC": "Pro", "CCA": "Pro", "CCG": "Pro",
    "CAU": "His", "CAC": "His", "CAA": "Gln", "CAG": "Gln",
    "CGU": "Arg", "CGC": "Arg", "CGA": "Arg", "CGG": "Arg",
    "AUU": "Ile", "AUC": "Ile", "AUA": "Ile", "AUG": "Met",
    "ACU": "Thr", "ACC": "Thr", "ACA": "Thr", "ACG": "Thr",
    "AAU": "Asn", "AAC": "Asn", "AAA": "Lys", "AAG": "Lys",
    "AGU": "Ser", "AGC": "Ser", "AGA": "Arg", "AGG": "Arg",
    "GUU": "Val", "GUC": "Val", "GUA": "Val", "GUG": "Val",
    "GCU": "Ala", "GCC": "Ala", "GCA": "Ala", "GCG": "Ala",
    "GAU": "Asp", "GAC": "Asp", "GAA": "Glu", "GAG": "Glu",
    "GGU": "Gly", "GGC": "Gly", "GGA": "Gly", "GGG": "Gly",
}

OUTPUT_ORDER = (
    "Ala", "Arg", "Asn", "Asp", "Cys", "Gln", "Glu", "Gly", "His",
    "Ile", "Leu", "Lys", "Met", "Phe", "Pro", "Ser", "Stop", "Thr",
    "Trp", "Tyr", "Val",
)
STOP_ID = OUTPUT_ORDER.index("Stop")


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def codon_order() -> list[str]:
    return ["".join(chars) for chars in product(BASES, repeat=3)]


def codon_to_q6(codon: str) -> tuple[int, ...]:
    bits: list[int] = []
    for base in codon:
        bits.extend(BASE_TO_BITS[base])
    return tuple(bits)


def hamming1_edges(codons: list[str]) -> list[tuple[int, int]]:
    index = {codon: pos for pos, codon in enumerate(codons)}
    edges: list[tuple[int, int]] = []
    for codon in codons:
        left = index[codon]
        for pos in range(3):
            for base in BASES:
                if base == codon[pos]:
                    continue
                other = codon[:pos] + base + codon[pos + 1:]
                right = index[other]
                if left < right:
                    edges.append((left, right))
    return edges


def standard_labels(codons: list[str]) -> list[int]:
    output_to_id = {output: pos for pos, output in enumerate(OUTPUT_ORDER)}
    return [output_to_id[CODON_TO_OUTPUT[codon]] for codon in codons]


def degeneracy_profile(labels: list[int]) -> dict[str, int]:
    counts = Counter(labels)
    return {OUTPUT_ORDER[index]: counts[index] for index in range(len(OUTPUT_ORDER))}


def degeneracy_spectrum(profile: dict[str, int]) -> dict[str, int]:
    spectrum = Counter(profile.values())
    return {str(size): spectrum[size] for size in sorted(spectrum)}


def omega_size(profile: dict[str, int]) -> int:
    total = sum(profile.values())
    numerator = math.factorial(total)
    denominator = 1
    for size in profile.values():
        denominator *= math.factorial(size)
    return numerator // denominator


def edge_counts(labels: list[int], edges: list[tuple[int, int]]) -> tuple[int, int]:
    sense = 0
    all_codons = 0
    for left, right in edges:
        if labels[left] == labels[right]:
            all_codons += 1
            if labels[left] != STOP_ID:
                sense += 1
    return sense, all_codons


def sense_edge_universe(labels: list[int], edges: list[tuple[int, int]]) -> int:
    return sum(1 for left, right in edges if labels[left] != STOP_ID and labels[right] != STOP_ID)


def running_stats(values: list[int]) -> dict[str, object]:
    n = len(values)
    mean = sum(values) / n
    if n > 1:
        variance = sum((value - mean) * (value - mean) for value in values) / (n - 1)
    else:
        variance = 0.0
    ordered = sorted(values)
    return {
        "mean": mean,
        "sd": math.sqrt(variance),
        "min": ordered[0],
        "p01": ordered[int(0.01 * (n - 1))],
        "p05": ordered[int(0.05 * (n - 1))],
        "median": ordered[int(0.50 * (n - 1))],
        "p95": ordered[int(0.95 * (n - 1))],
        "p99": ordered[int(0.99 * (n - 1))],
        "max": ordered[-1],
    }


def z_score(observed: int, summary: dict[str, object]) -> float:
    sd = float(summary["sd"])
    if sd == 0.0:
        return 0.0
    return (observed - float(summary["mean"])) / sd


def rank_high(values: list[int], observed: int) -> dict[str, int]:
    return {
        "one_based_high_rank": 1 + sum(1 for value in values if value > observed),
        "ties": sum(1 for value in values if value == observed),
        "sample_count": len(values),
    }


def p_upper(values: list[int], observed: int) -> float:
    return sum(1 for value in values if value >= observed) / len(values)


def p_lower(values: list[int], observed: int) -> float:
    return sum(1 for value in values if value <= observed) / len(values)


def shuffled_labels(profile: dict[str, int], rng: random.Random) -> list[int]:
    labels: list[int] = []
    for output in OUTPUT_ORDER:
        labels.extend([OUTPUT_ORDER.index(output)] * profile[output])
    rng.shuffle(labels)
    return labels


def distribution_sample(
    profile: dict[str, int],
    edges: list[tuple[int, int]],
    draws: int,
    seed: int,
) -> tuple[list[int], list[int]]:
    rng = random.Random(seed)
    sense_values: list[int] = []
    all_values: list[int] = []
    for _ in range(draws):
        labels = shuffled_labels(profile, rng)
        sense, all_codons = edge_counts(labels, edges)
        sense_values.append(sense)
        all_values.append(all_codons)
    return sense_values, all_values


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def verdict(p_hide: float, p_low: float) -> tuple[str, str]:
    if p_hide <= CERTIFIED_UPPER_TAIL:
        return (
            "certified",
            "standard code is a high edge-hiding outlier under the fixed labeled degeneracy null",
        )
    if p_low <= REFUTED_LOWER_TAIL:
        return (
            "refuted",
            "standard code is a low edge-hiding outlier under the fixed labeled degeneracy null",
        )
    if p_hide >= TYPICAL_TAIL_FLOOR and p_low >= TYPICAL_TAIL_FLOOR:
        return (
            "coincidence",
            "standard code is typical under the fixed labeled degeneracy null; the statistic is not an assignment optimum here",
        )
    return (
        "needs_derivation",
        "standard code is in a tail region, but not beyond the predeclared decision thresholds",
    )


def main() -> None:
    codons = codon_order()
    edges = hamming1_edges(codons)
    q6_labels = [codon_to_q6(codon) for codon in codons]
    labels_std = standard_labels(codons)
    profile = degeneracy_profile(labels_std)
    spectrum = degeneracy_spectrum(profile)
    e_in_std_sense, e_in_std_all = edge_counts(labels_std, edges)

    sense_values, all_values = distribution_sample(profile, edges, NULL_DRAWS, NULL_SEED)
    summary_sense = running_stats(sense_values)
    summary_all = running_stats(all_values)
    p_hide_sense = p_upper(sense_values, e_in_std_sense)
    p_low_sense = p_lower(sense_values, e_in_std_sense)
    p_hide_all = p_upper(all_values, e_in_std_all)
    p_low_all = p_lower(all_values, e_in_std_all)
    status, reason = verdict(p_hide_sense, p_low_sense)

    checks = [
        check_row("codon_count", len(codons), 64),
        check_row("q6_label_count", len(set(q6_labels)), 64),
        check_row("hamming1_edge_count", len(edges), 288),
        check_row("standard_table_covers_cube", sorted(CODON_TO_OUTPUT), sorted(codons)),
        check_row("degeneracy_spectrum", spectrum, {"1": 2, "2": 9, "3": 2, "4": 5, "6": 3}),
        check_row("degeneracy_codon_sum", sum(profile.values()), 64),
        check_row("stop_degeneracy", profile["Stop"], 3),
        check_row("sense_codon_count", sum(1 for label in labels_std if label != STOP_ID), 61),
        check_row("standard_sense_edge_universe", sense_edge_universe(labels_std, edges), 263),
        check_row("null_draws", len(sense_values), NULL_DRAWS),
        check_row("null_sense_min_le_max", summary_sense["min"] <= summary_sense["max"], True),
        check_row("null_all_min_le_max", summary_all["min"] <= summary_all["max"], True),
    ]
    if not all(bool(row["ok"]) for row in checks):
        emit(
            "needs_derivation",
            e_in_std_sense=e_in_std_sense,
            e_in_std_all=e_in_std_all,
            degeneracy_profile=profile,
            omega_null_size=omega_size(profile),
            null_seed=NULL_SEED,
            null_draws=NULL_DRAWS,
            p_hide_sense=p_hide_sense,
            p_hide_all=p_hide_all,
            p_low_sense=p_low_sense,
            p_low_all=p_low_all,
            e_in_null_summary=summary_sense,
            e_in_null_summary_all=summary_all,
            z_score=z_score(e_in_std_sense, summary_sense),
            z_score_all=z_score(e_in_std_all, summary_all),
            checks=checks,
            reason="internal finite-enumeration check failed",
        )

    emit(
        status,
        e_in_std_sense=e_in_std_sense,
        e_in_std_all=e_in_std_all,
        degeneracy_profile=profile,
        degeneracy_spectrum=spectrum,
        omega_null_size=omega_size(profile),
        null_seed=NULL_SEED,
        null_draws=NULL_DRAWS,
        p_hide_sense=p_hide_sense,
        p_hide_all=p_hide_all,
        p_low_sense=p_low_sense,
        p_low_all=p_low_all,
        e_in_null_summary=summary_sense,
        e_in_null_summary_all=summary_all,
        z_score=z_score(e_in_std_sense, summary_sense),
        z_score_all=z_score(e_in_std_all, summary_all),
        rank=rank_high(sense_values, e_in_std_sense),
        rank_all=rank_high(all_values, e_in_std_all),
        thresholds={
            "certified_upper_tail": CERTIFIED_UPPER_TAIL,
            "refuted_lower_tail": REFUTED_LOWER_TAIL,
            "typical_tail_floor": TYPICAL_TAIL_FLOOR,
        },
        edge_universes={
            "all_hamming1_edges": len(edges),
            "standard_sense_to_sense_edges": sense_edge_universe(labels_std, edges),
        },
        checks=checks,
        reason=reason,
    )


if __name__ == "__main__":
    main()

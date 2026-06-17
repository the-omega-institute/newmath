#!/usr/bin/env python3
"""Ser island near-cognate error-cost audit.

The oracle memo suggests a concrete biological mechanism: UCN and AGY may be
two Ser decoding channels with different one-step error neighborhoods.  This
script tests the code-table part of that route only.  It computes a deterministic
near-cognate substitution-cost profile for every sense codon from the standard
genetic code and amino-acid property distances, then asks whether the Ser
four-plus-two split is exceptional relative to the other sixfold families and
matched random codon partitions.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import combinations, product
import json
import math
import random
import sys


EXPERIMENT_ID = "ser_island_fidelity_cost"
CLAIM_ID = "bridge.genetic_code.ser_island_fidelity_cost"
RANDOM_SEED = 20260616
NULL_DRAWS = 20000
BASES = ("U", "C", "A", "G")
SER4 = ("UCU", "UCC", "UCA", "UCG")
SER2 = ("AGU", "AGC")
SIXFOLD_PARTITIONS = {
    "Ser": (SER4, SER2),
    "Leu": (("CUU", "CUC", "CUA", "CUG"), ("UUA", "UUG")),
    "Arg": (("CGU", "CGC", "CGA", "CGG"), ("AGA", "AGG")),
}

CODE = {
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

# Kyte-Doolittle hydropathy, approximate residue volume, charge, polarity,
# aromaticity, and special structural role.  The script z-scores dimensions
# before computing Euclidean substitution distances.
AA_PROPERTIES = {
    "A": (1.8, 88.6, 0.0, 0.0, 0.0, 0.0),
    "R": (-4.5, 173.4, 1.0, 1.0, 0.0, 0.0),
    "N": (-3.5, 114.1, 0.0, 1.0, 0.0, 0.0),
    "D": (-3.5, 111.1, -1.0, 1.0, 0.0, 0.0),
    "C": (2.5, 108.5, 0.0, 0.0, 0.0, 1.0),
    "Q": (-3.5, 143.8, 0.0, 1.0, 0.0, 0.0),
    "E": (-3.5, 138.4, -1.0, 1.0, 0.0, 0.0),
    "G": (-0.4, 60.1, 0.0, 0.0, 0.0, 1.0),
    "H": (-3.2, 153.2, 0.5, 1.0, 1.0, 0.0),
    "I": (4.5, 166.7, 0.0, 0.0, 0.0, 0.0),
    "L": (3.8, 166.7, 0.0, 0.0, 0.0, 0.0),
    "K": (-3.9, 168.6, 1.0, 1.0, 0.0, 0.0),
    "M": (1.9, 162.9, 0.0, 0.0, 0.0, 0.0),
    "F": (2.8, 189.9, 0.0, 0.0, 1.0, 0.0),
    "P": (-1.6, 112.7, 0.0, 0.0, 0.0, 1.0),
    "S": (-0.8, 89.0, 0.0, 1.0, 0.0, 0.0),
    "T": (-0.7, 116.1, 0.0, 1.0, 0.0, 0.0),
    "W": (-0.9, 227.8, 0.0, 1.0, 1.0, 0.0),
    "Y": (-1.3, 193.6, 0.0, 1.0, 1.0, 0.0),
    "V": (4.2, 140.0, 0.0, 0.0, 0.0, 0.0),
}


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def codons() -> list[str]:
    return ["".join(chars) for chars in product(BASES, repeat=3)]


def sense_codons() -> list[str]:
    return [codon for codon in codons() if CODE[codon] != "*"]


def neighbors(codon: str) -> list[str]:
    out = []
    for index in range(3):
        for base in BASES:
            if base != codon[index]:
                out.append(codon[:index] + base + codon[index + 1 :])
    return out


def zscored_properties() -> dict[str, tuple[float, ...]]:
    columns = list(zip(*AA_PROPERTIES.values()))
    means = [sum(col) / len(col) for col in columns]
    sds = [
        math.sqrt(sum((value - mean) ** 2 for value in col) / len(col))
        for col, mean in zip(columns, means)
    ]
    out = {}
    for aa, values in AA_PROPERTIES.items():
        out[aa] = tuple((value - means[index]) / sds[index] for index, value in enumerate(values))
    return out


ZSCORED = zscored_properties()


def substitution_cost(source: str, target: str) -> float:
    if source == target:
        return 0.0
    if target == "*":
        return 8.0
    left = ZSCORED[source]
    right = ZSCORED[target]
    return math.sqrt(sum((left[index] - right[index]) ** 2 for index in range(len(left))))


def codon_error_profile(codon: str) -> dict[str, object]:
    source = CODE[codon]
    rows = []
    for neighbor in neighbors(codon):
        target = CODE[neighbor]
        hidden = target == source
        cost = 0.0 if hidden else substitution_cost(source, target)
        rows.append({"neighbor": neighbor, "target": target, "hidden": hidden, "cost": cost})
    visible = [row["cost"] for row in rows if not row["hidden"]]
    return {
        "codon": codon,
        "amino_acid": source,
        "hidden_edges": sum(1 for row in rows if row["hidden"]),
        "visible_edges": len(visible),
        "mean_visible_cost": sum(visible) / len(visible),
        "stop_edges": sum(1 for row in rows if row["target"] == "*"),
        "outcomes": sorted({str(row["target"]) for row in rows if not row["hidden"]}),
        "neighbors": rows,
    }


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def partition_delta(costs: dict[str, float], left: tuple[str, ...], right: tuple[str, ...]) -> float:
    return mean([costs[codon] for codon in left]) - mean([costs[codon] for codon in right])


def gc_total(codon: str) -> int:
    return sum(1 for base in codon if base in "GC")


def matched_random_delta(costs: dict[str, float], rng: random.Random) -> list[float]:
    sense = sense_codons()
    target_gc = Counter(gc_total(codon) for codon in (*SER4, *SER2))
    buckets: dict[int, list[str]] = defaultdict(list)
    for codon in sense:
        buckets[gc_total(codon)].append(codon)
    values = []
    for _draw in range(NULL_DRAWS):
        selected: list[str] = []
        for gc, count in target_gc.items():
            selected.extend(rng.sample(buckets[gc], count))
        left = tuple(rng.sample(selected, 4))
        right = tuple(codon for codon in selected if codon not in left)
        if len(right) != 2:
            continue
        values.append(partition_delta(costs, left, right))
    return values


def empirical_abs_p(observed: float, null_values: list[float]) -> float:
    return (sum(1 for value in null_values if abs(value) >= abs(observed)) + 1) / (len(null_values) + 1)


def round_float(value: float, digits: int = 6) -> float:
    return round(value, digits)


def main() -> None:
    profiles = {codon: codon_error_profile(codon) for codon in sense_codons()}
    costs = {codon: float(profile["mean_visible_cost"]) for codon, profile in profiles.items()}
    partition_rows = {}
    for family, (left, right) in SIXFOLD_PARTITIONS.items():
        partition_rows[family] = {
            "left": list(left),
            "right": list(right),
            "left_mean_cost": round_float(mean([costs[codon] for codon in left])),
            "right_mean_cost": round_float(mean([costs[codon] for codon in right])),
            "delta_left_minus_right": round_float(partition_delta(costs, left, right)),
            "left_stop_edges": sum(int(profiles[codon]["stop_edges"]) for codon in left),
            "right_stop_edges": sum(int(profiles[codon]["stop_edges"]) for codon in right),
        }

    ser_delta = partition_delta(costs, SER4, SER2)
    sixfold_null = [
        partition_delta(costs, left, right)
        for family, (left, right) in SIXFOLD_PARTITIONS.items()
        if family != "Ser"
    ]
    matched_null = matched_random_delta(costs, random.Random(RANDOM_SEED))
    status = "certified" if ser_delta > 0 and empirical_abs_p(ser_delta, matched_null) <= 0.05 else "coincidence"
    note = (
        "The code-table near-cognate cost audit finds a positive Ser UCN-minus-AGY cost delta "
        "that is extreme against the matched random null. This is a mechanistic candidate only; "
        "site-level expression and mistranslation data are still required."
        if status == "certified"
        else "The Ser UCN-minus-AGY near-cognate cost delta is not certified as exceptional under the matched null."
    )
    emit(
        status,
        note=note,
        ser_delta_ucn_minus_agy=round_float(ser_delta),
        partition_rows=partition_rows,
        codon_profiles={
            codon: {
                key: (round_float(value) if isinstance(value, float) else value)
                for key, value in profile.items()
                if key != "neighbors"
            }
            for codon, profile in profiles.items()
            if codon in (*SER4, *SER2)
        },
        sixfold_family_null={
            "deltas_left_minus_right": [round_float(value) for value in sixfold_null],
            "abs_p": round_float(empirical_abs_p(ser_delta, sixfold_null)),
        },
        matched_random_null={
            "draws": len(matched_null),
            "abs_p": round_float(empirical_abs_p(ser_delta, matched_null)),
            "mean_abs_delta": round_float(mean([abs(value) for value in matched_null])),
            "max_abs_delta": round_float(max(abs(value) for value in matched_null)),
        },
        scope=(
            "This is a code-table and amino-acid-property audit of one-step error neighborhoods. "
            "It does not use expression data, tRNA abundance, dwell, or measured mistranslation spectra."
        ),
        next_required_test=(
            "Test whether highly expressed proteins prefer UCN or AGY at Ser sites where the opposite "
            "island's measured near-cognate error spectrum has higher predicted damage."
        ),
    )


if __name__ == "__main__":
    main()

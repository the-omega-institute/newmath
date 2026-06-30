#!/usr/bin/env python3
"""Codon synonymous-fiber quotient extremality under controlled partitions.

The tested object is the assignment of codons to synonymous fibers, not the
fiber-size spectrum alone.  The size-matched null shuffles the same block
sizes over the 64 vertices of Q6 with a fixed seed.  The stringent null keeps
the standard code's box-local synonymous clusters intact, matches the same
fiber-size spectrum, and accepts only samples with the same within-box and
cross-box same-fiber Q6 edge profile.  The declared functionals use only the
quotient palette: off-diagonal block-to-block Q6 edge multiplicities and
cross-block equitability defect.
"""
from __future__ import annotations

from collections import Counter
from itertools import product
import json
import random
import sys
from typing import Iterable


EXPERIMENT_ID = "codon_synfiber_quotient_extremality"
CLAIM_ID = "bridge.genetic_code.synfiber_quotient.extremality"
RANDOM_SEED = 642611
STRINGENT_NULL_SEED = 904153
STRINGENT_NULL_NAME = "box_wobble_atom_edge_profile_preserving"
NULL_DRAWS = 50000
STRINGENT_MAX_ATTEMPTS = NULL_DRAWS * 100
EXTREME_ALPHA = 0.01
FUNCTIONAL_NAMES = (
    "cross_quotient_energy",
    "cross_equitability_defect",
)

BASES = ("U", "C", "A", "G")
BASE_TO_BITS = {"U": "00", "C": "01", "A": "10", "G": "11"}

CODON_TO_FAMILY = {
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


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def codon_order() -> list[str]:
    return ["".join(parts) for parts in product(BASES, repeat=3)]


def codon_bits(codon: str) -> str:
    return "".join(BASE_TO_BITS[base] for base in codon)


def q6_edges_and_neighbors(codons: list[str]) -> tuple[list[tuple[int, int]], list[list[int]]]:
    bitwords = [codon_bits(codon) for codon in codons]
    by_bits = {word: index for index, word in enumerate(bitwords)}
    edges: list[tuple[int, int]] = []
    neighbors: list[list[int]] = [[] for _ in codons]
    for index, word in enumerate(bitwords):
        for axis in range(6):
            flipped = word[:axis] + ("1" if word[axis] == "0" else "0") + word[axis + 1:]
            other = by_bits[flipped]
            neighbors[index].append(other)
            if index < other:
                edges.append((index, other))
    return edges, neighbors


def family_order(codons: list[str]) -> list[str]:
    counts = Counter(CODON_TO_FAMILY[codon] for codon in codons)
    return sorted(counts, key=lambda family: (-counts[family], family))


def labels_for_standard_partition(codons: list[str], families: list[str]) -> list[int]:
    family_to_block = {family: index for index, family in enumerate(families)}
    return [family_to_block[CODON_TO_FAMILY[codon]] for codon in codons]


def box_key(codon: str) -> str:
    return codon[:2]


def box_wobble_atoms(codons: list[str], labels: list[int]) -> list[tuple[int, ...]]:
    atoms: dict[tuple[str, int], list[int]] = {}
    for index, codon in enumerate(codons):
        atoms.setdefault((box_key(codon), labels[index]), []).append(index)
    return [
        tuple(indices)
        for _, indices in sorted(
            atoms.items(),
            key=lambda item: (item[0][0], min(item[1])),
        )
    ]


def same_block_box_edge_profile(
    labels: list[int],
    codons: list[str],
    edges: Iterable[tuple[int, int]],
) -> dict[str, int]:
    profile = {"within_box_same_block_edges": 0, "cross_box_same_block_edges": 0}
    for left, right in edges:
        if labels[left] != labels[right]:
            continue
        if box_key(codons[left]) == box_key(codons[right]):
            profile["within_box_same_block_edges"] += 1
        else:
            profile["cross_box_same_block_edges"] += 1
    return profile


def sample_box_wobble_partition(
    rng: random.Random,
    atoms: list[tuple[int, ...]],
    vertex_count: int,
) -> tuple[list[int], list[int]]:
    atoms_by_size: dict[int, list[int]] = {}
    for atom_index, atom in enumerate(atoms):
        atoms_by_size.setdefault(len(atom), []).append(atom_index)

    quartets = list(atoms_by_size.get(4, []))
    triplets = list(atoms_by_size.get(3, []))
    doublets = list(atoms_by_size.get(2, []))
    singlets = list(atoms_by_size.get(1, []))
    rng.shuffle(quartets)
    rng.shuffle(doublets)
    rng.shuffle(singlets)

    groups: list[list[int]] = []
    groups.extend([[quartets[index], doublets[index]] for index in range(3)])
    groups.extend([[atom_index] for atom_index in quartets[3:]])
    groups.append([triplets[0]])
    groups.append([doublets[3], singlets[0]])
    groups.extend([[atom_index] for atom_index in doublets[4:]])
    groups.extend([[atom_index] for atom_index in singlets[1:]])

    labels = [-1 for _ in range(vertex_count)]
    block_sizes: list[int] = []
    for block, group in enumerate(groups):
        block_size = 0
        for atom_index in group:
            atom = atoms[atom_index]
            block_size += len(atom)
            for vertex in atom:
                labels[vertex] = block
        block_sizes.append(block_size)
    return labels, block_sizes


def quotient_matrix(labels: list[int], block_count: int, edges: Iterable[tuple[int, int]]) -> list[list[int]]:
    matrix = [[0 for _ in range(block_count)] for _ in range(block_count)]
    for left, right in edges:
        block_left = labels[left]
        block_right = labels[right]
        if block_left == block_right:
            matrix[block_left][block_left] += 1
        else:
            matrix[block_left][block_right] += 1
            matrix[block_right][block_left] += 1
    return matrix


def quotient_row_sums(matrix: list[list[int]]) -> list[int]:
    return [sum(value for column, value in enumerate(row) if column != index) for index, row in enumerate(matrix)]


def trace_square_offdiag(matrix: list[list[int]]) -> int:
    total = 0
    for row in range(len(matrix)):
        for column in range(len(matrix)):
            if row != column:
                total += matrix[row][column] * matrix[column][row]
    return total


def trace_cube_offdiag(matrix: list[list[int]]) -> int:
    size = len(matrix)
    total = 0
    for first in range(size):
        for second in range(size):
            if first == second:
                continue
            left = matrix[first][second]
            if left == 0:
                continue
            for third in range(size):
                if third == first or third == second:
                    continue
                total += left * matrix[second][third] * matrix[third][first]
    return total


def partition_stats(
    labels: list[int],
    block_count: int,
    block_sizes: list[int],
    edges: list[tuple[int, int]],
    neighbors: list[list[int]],
) -> dict[str, int]:
    matrix = [[0 for _ in range(block_count)] for _ in range(block_count)]
    square_counts = [[0 for _ in range(block_count)] for _ in range(block_count)]

    for left, right in edges:
        block_left = labels[left]
        block_right = labels[right]
        if block_left != block_right:
            matrix[block_left][block_right] += 1
            matrix[block_right][block_left] += 1

    for vertex, block in enumerate(labels):
        local_counts: dict[int, int] = {}
        for neighbor in neighbors[vertex]:
            neighbor_block = labels[neighbor]
            if neighbor_block != block:
                local_counts[neighbor_block] = local_counts.get(neighbor_block, 0) + 1
        for other_block, count in local_counts.items():
            square_counts[block][other_block] += count * count

    cross_quotient_energy = 0
    cross_equitability_defect = 0
    for block in range(block_count):
        for other_block in range(block + 1, block_count):
            weight = matrix[block][other_block]
            cross_quotient_energy += weight * weight
        for other_block in range(block_count):
            if block == other_block:
                continue
            weight = matrix[block][other_block]
            cross_equitability_defect += block_sizes[block] * square_counts[block][other_block] - weight * weight

    return {
        "cross_quotient_energy": cross_quotient_energy,
        "cross_equitability_defect": cross_equitability_defect,
    }


def empirical_two_sided_p(values: list[int], observed: int) -> dict[str, object]:
    lower_or_equal = sum(1 for value in values if value <= observed)
    upper_or_equal = sum(1 for value in values if value >= observed)
    tail_count = min(lower_or_equal, upper_or_equal)
    p_value = min(1.0, 2.0 * (tail_count + 1) / (len(values) + 1))
    if lower_or_equal < upper_or_equal:
        side = "low"
    elif upper_or_equal < lower_or_equal:
        side = "high"
    else:
        side = "middle"
    return {
        "p": p_value,
        "tail": side,
        "lower_or_equal": lower_or_equal,
        "upper_or_equal": upper_or_equal,
    }


def summarize_null(values: list[int], observed: int) -> dict[str, object]:
    ordered = sorted(values)
    return {
        "observed": observed,
        "min": ordered[0],
        "q01": ordered[int(0.01 * (len(ordered) - 1))],
        "q05": ordered[int(0.05 * (len(ordered) - 1))],
        "median": ordered[len(ordered) // 2],
        "q95": ordered[int(0.95 * (len(ordered) - 1))],
        "q99": ordered[int(0.99 * (len(ordered) - 1))],
        "max": ordered[-1],
        "mean": round(sum(values) / len(values), 6),
    }


def round_p(value: float) -> float:
    return float(f"{value:.12g}")


def main() -> None:
    codons = codon_order()
    edges, neighbors = q6_edges_and_neighbors(codons)
    families = family_order(codons)
    labels = labels_for_standard_partition(codons, families)
    block_count = len(families)
    block_sizes = [labels.count(block) for block in range(block_count)]
    block_size_multiset = sorted(block_sizes, reverse=True)

    observed_matrix_named = quotient_matrix(labels, block_count, edges)
    block_permutation = sorted(
        range(block_count),
        key=lambda block: (-block_sizes[block], observed_matrix_named[block]),
    )
    observed_matrix = [
        [observed_matrix_named[row][column] for column in block_permutation]
        for row in block_permutation
    ]
    observed_stats = partition_stats(labels, block_count, block_sizes, edges, neighbors)
    observed_box_edge_profile = same_block_box_edge_profile(labels, codons, edges)
    box_atoms = box_wobble_atoms(codons, labels)

    rng = random.Random(RANDOM_SEED)
    null_template: list[int] = []
    for block, size in enumerate(block_size_multiset):
        null_template.extend([block] * size)
    null_values = {name: [] for name in FUNCTIONAL_NAMES}
    for _ in range(NULL_DRAWS):
        rng.shuffle(null_template)
        stats = partition_stats(null_template, block_count, block_size_multiset, edges, neighbors)
        for name in FUNCTIONAL_NAMES:
            null_values[name].append(stats[name])

    p_values = {name: empirical_two_sided_p(null_values[name], observed_stats[name]) for name in FUNCTIONAL_NAMES}
    adjusted = {
        name: min(1.0, p_values[name]["p"] * len(FUNCTIONAL_NAMES))
        for name in FUNCTIONAL_NAMES
    }
    null_summary = {
        name: summarize_null(null_values[name], observed_stats[name])
        for name in FUNCTIONAL_NAMES
    }

    stringent_rng = random.Random(STRINGENT_NULL_SEED)
    stringent_null_values = {name: [] for name in FUNCTIONAL_NAMES}
    stringent_attempts = 0
    stringent_rejections = 0
    stringent_defined = False
    while (
        len(stringent_null_values["cross_equitability_defect"]) < NULL_DRAWS
        and stringent_attempts < STRINGENT_MAX_ATTEMPTS
    ):
        stringent_attempts += 1
        candidate_labels, candidate_block_sizes = sample_box_wobble_partition(
            stringent_rng,
            box_atoms,
            len(codons),
        )
        if sorted(candidate_block_sizes, reverse=True) != block_size_multiset:
            stringent_rejections += 1
            continue
        if same_block_box_edge_profile(candidate_labels, codons, edges) != observed_box_edge_profile:
            stringent_rejections += 1
            continue

        stats = partition_stats(candidate_labels, block_count, candidate_block_sizes, edges, neighbors)
        for name in FUNCTIONAL_NAMES:
            stringent_null_values[name].append(stats[name])

    stringent_defined = len(stringent_null_values["cross_equitability_defect"]) == NULL_DRAWS
    stringent_p_values = (
        {
            name: empirical_two_sided_p(stringent_null_values[name], observed_stats[name])
            for name in FUNCTIONAL_NAMES
        }
        if stringent_defined
        else {}
    )
    stringent_adjusted = (
        {
            name: min(1.0, stringent_p_values[name]["p"] * len(FUNCTIONAL_NAMES))
            for name in FUNCTIONAL_NAMES
        }
        if stringent_defined
        else {}
    )
    stringent_null_summary = (
        {
            name: summarize_null(stringent_null_values[name], observed_stats[name])
            for name in FUNCTIONAL_NAMES
        }
        if stringent_defined
        else {}
    )

    checks = [
        {"name": "codon_count", "ok": len(codons) == 64, "observed": len(codons), "expected": 64},
        {"name": "q6_edge_count", "ok": len(edges) == 192, "observed": len(edges), "expected": 192},
        {"name": "q6_degree", "ok": all(len(set(row)) == 6 for row in neighbors), "expected": 6},
        {"name": "block_count", "ok": block_count == 21, "observed": block_count, "expected": 21},
        {
            "name": "block_size_multiset",
            "ok": block_size_multiset == [6, 6, 6, 4, 4, 4, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1],
            "observed": block_size_multiset,
        },
        {
            "name": "quotient_cross_edge_balance",
            "ok": sum(quotient_row_sums(observed_matrix_named)) == 2 * sum(
                1 for left, right in edges if labels[left] != labels[right]
            ),
        },
        {
            "name": "fixed_seed_replayable",
            "ok": RANDOM_SEED == 642611 and NULL_DRAWS == 50000,
            "seed": RANDOM_SEED,
            "draws": NULL_DRAWS,
        },
        {
            "name": "stringent_fixed_seed_replayable",
            "ok": STRINGENT_NULL_SEED == 904153 and NULL_DRAWS == 50000,
            "seed": STRINGENT_NULL_SEED,
            "draws": NULL_DRAWS,
        },
        {
            "name": "box_wobble_atoms_cover_codons",
            "ok": sorted(vertex for atom in box_atoms for vertex in atom) == list(range(len(codons))),
            "atom_size_multiset": sorted((len(atom) for atom in box_atoms), reverse=True),
            "atom_count": len(box_atoms),
        },
        {
            "name": "stringent_null_defined",
            "ok": stringent_defined,
            "accepted": len(stringent_null_values["cross_equitability_defect"]),
            "attempts": stringent_attempts,
            "max_attempts": STRINGENT_MAX_ATTEMPTS,
        },
    ]

    all_checks_ok = all(bool(check.get("ok")) for check in checks)
    weak_equitability_p = p_values["cross_equitability_defect"]["p"]
    weak_equitability_adjusted = adjusted["cross_equitability_defect"]
    energy_adjusted = adjusted["cross_quotient_energy"]
    weak_equitability_extreme = (
        p_values["cross_equitability_defect"]["tail"] == "low"
        and weak_equitability_adjusted <= EXTREME_ALPHA
    )
    stringent_equitability_p = (
        stringent_p_values["cross_equitability_defect"]["p"]
        if stringent_defined
        else None
    )
    stringent_equitability_adjusted = (
        stringent_adjusted["cross_equitability_defect"]
        if stringent_defined
        else None
    )
    stringent_equitability_extreme = (
        stringent_defined
        and stringent_p_values["cross_equitability_defect"]["tail"] == "low"
        and stringent_adjusted["cross_equitability_defect"] <= EXTREME_ALPHA
    )
    reducible = bool(weak_equitability_extreme and not stringent_equitability_extreme) if stringent_defined else None

    if not all_checks_ok:
        status = "needs_derivation"
        reason = (
            "Internal construction checks failed or the box/wobble-preserving null "
            "was inconclusive; no quotient-extremality verdict is emitted."
        )
    elif stringent_equitability_extreme:
        status = "certified"
        reason = (
            "The standard synonymous-fiber partition remains a low-tail outlier for "
            "cross_equitability_defect under both the weak size-matched null "
            f"(p={round_p(weak_equitability_p)}) and the stringent "
            f"{STRINGENT_NULL_NAME} null (p={round_p(stringent_equitability_p)}), "
            "so the equitability forcing is not reduced to the certified "
            "box/wobble composition."
        )
    elif weak_equitability_extreme:
        status = "coincidence"
        reason = (
            "The standard synonymous-fiber partition is a low-tail outlier for "
            "cross_equitability_defect under the weak size-matched null "
            f"(p={round_p(weak_equitability_p)}) but not under the stringent "
            f"{STRINGENT_NULL_NAME} null (p={round_p(stringent_equitability_p)}); "
            "the equitability extremality is reducible to the already-certified "
            "box/wobble composition."
        )
    elif all(adjusted[name] > 0.20 for name in FUNCTIONAL_NAMES):
        status = "coincidence"
        reason = (
            "The declared quotient functionals fall inside the typical range of "
            "same-size random partitions; weak-null p="
            f"{round_p(weak_equitability_p)} and stringent-null p="
            f"{round_p(stringent_equitability_p)} for cross_equitability_defect."
        )
    elif any(
        p_values[name]["tail"] == "high" and adjusted[name] <= EXTREME_ALPHA
        for name in FUNCTIONAL_NAMES
    ):
        status = "refuted"
        reason = (
            "A declared quotient functional is extreme in the opposite direction "
            "from the low-defect structural-forcing claim."
        )
    else:
        status = "needs_derivation"
        reason = (
            "The fixed-seed matched nulls are neither typical nor strong enough for "
            "the declared extremality threshold; weak-null p="
            f"{round_p(weak_equitability_p)} and stringent-null p="
            f"{round_p(stringent_equitability_p)} for cross_equitability_defect."
        )

    emit(
        status,
        block_size_multiset=block_size_multiset,
        functional_names=list(FUNCTIONAL_NAMES),
        observed_values=observed_stats,
        null_size=NULL_DRAWS,
        null_seed=RANDOM_SEED,
        outlier_p={name: round_p(p_values[name]["p"]) for name in FUNCTIONAL_NAMES},
        adjusted_outlier_p={name: round_p(adjusted[name]) for name in FUNCTIONAL_NAMES},
        outlier_tail={name: p_values[name]["tail"] for name in FUNCTIONAL_NAMES},
        multiplicity_method="Bonferroni over two predeclared functionals",
        weak_null_p=round_p(weak_equitability_p),
        stringent_null_name=STRINGENT_NULL_NAME,
        stringent_null_p=round_p(stringent_equitability_p) if stringent_equitability_p is not None else None,
        stringent_null_seed=STRINGENT_NULL_SEED,
        reducible=reducible,
        stringent_outlier_p=(
            {name: round_p(stringent_p_values[name]["p"]) for name in FUNCTIONAL_NAMES}
            if stringent_defined
            else {}
        ),
        stringent_adjusted_outlier_p=(
            {name: round_p(stringent_adjusted[name]) for name in FUNCTIONAL_NAMES}
            if stringent_defined
            else {}
        ),
        stringent_outlier_tail=(
            {name: stringent_p_values[name]["tail"] for name in FUNCTIONAL_NAMES}
            if stringent_defined
            else {}
        ),
        distinct_from_e_in=True,
        null_summary=null_summary,
        stringent_null_summary=stringent_null_summary,
        stringent_null_controls={
            "description": (
                "The null decomposes the standard partition into maximal "
                "box-local synonymous atoms, keeps each atom intact, recombines "
                "atoms to match the standard degeneracy-size multiset, and accepts "
                "only samples with the same within-box and cross-box same-fiber "
                "Q6 edge counts as the standard code."
            ),
            "observed_same_block_box_edge_profile": observed_box_edge_profile,
            "accepted_draws": len(stringent_null_values["cross_equitability_defect"]),
            "attempts": stringent_attempts,
            "rejections": stringent_rejections,
            "max_attempts": STRINGENT_MAX_ATTEMPTS,
        },
        quotient_invariants={
            "sorted_cross_row_sums": sorted(quotient_row_sums(observed_matrix_named), reverse=True),
            "offdiag_trace_square": trace_square_offdiag(observed_matrix_named),
            "offdiag_trace_cube": trace_cube_offdiag(observed_matrix_named),
        },
        quotient_matrix_label_free=observed_matrix,
        thresholds={
            "extreme_alpha_after_multiplicity": EXTREME_ALPHA,
            "certification_rule": (
                "certified iff cross_equitability_defect is low-tail and "
                "Bonferroni-adjusted p <= extreme_alpha_after_multiplicity under "
                "the stringent box/wobble-preserving null"
            ),
            "coincidence_rule": (
                "coincidence iff the weak size-matched null is extreme but the "
                "stringent box/wobble-preserving null is not extreme"
            ),
        },
        checks=checks,
        reason=reason,
        notes=(
            "The weak null fixes only the degeneracy spectrum and randomly assigns "
            "the 64 Q6 vertices to those block sizes.  The stringent null keeps "
            "box-local synonymous atoms and the same within-box versus cross-box "
            "same-fiber Q6 edge profile fixed, so a certified verdict must survive "
            "known box/wobble composition."
        ),
    )


if __name__ == "__main__":
    main()

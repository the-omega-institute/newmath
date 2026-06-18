#!/usr/bin/env python3
"""Quotient spanning-tree compression extremality for the standard code.

The null is the label-free regrouping space of the 25 fixed box/wobble atoms,
conditioned on the standard assembly signatures, per-edge-orbit synonymous
edge profiles, and every fiber's boundary-degree vector by edge orbit.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import permutations, product
import json
import math
import sys


EXPERIMENT_ID = "quotient_spanningtree_extremality"
CLAIM_ID = "bridge.genetic_code.quotient_spanningtree.extremality"
NULL_SEED = None
NULL_DRAWS = None
EXTREME_ALPHA = 0.01

BASES = ("U", "C", "A", "G")
BASE_TO_BITS = {"U": "00", "C": "01", "A": "10", "G": "11"}
BOX_AXES = frozenset(range(4))
WOBBLE_AXES = frozenset(range(4, 6))
EDGE_ORBITS = ("box_axis", "wobble_axis")
BOX_WOBBLE_AUTOMORPHISM_COUNT = (2 ** 6) * math.factorial(4) * math.factorial(2)

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
    sys.exit(0 if status in ("certified", "coincidence", "refuted") else 3)


def codon_order() -> list[str]:
    return ["".join(parts) for parts in product(BASES, repeat=3)]


def codon_bits(codon: str) -> str:
    return "".join(BASE_TO_BITS[base] for base in codon)


def family_order(codons: list[str]) -> list[str]:
    counts = Counter(CODON_TO_FAMILY[codon] for codon in codons)
    return sorted(counts, key=lambda family: (-counts[family], family))


def standard_labels(codons: list[str], families: list[str]) -> list[int]:
    by_family = {family: index for index, family in enumerate(families)}
    return [by_family[CODON_TO_FAMILY[codon]] for codon in codons]


def edge_orbit(axis: int) -> int:
    return 0 if axis in BOX_AXES else 1


def q6_edges(codons: list[str]) -> list[tuple[int, int, int]]:
    bitwords = [codon_bits(codon) for codon in codons]
    by_bits = {word: index for index, word in enumerate(bitwords)}
    edges: list[tuple[int, int, int]] = []
    for index, word in enumerate(bitwords):
        for axis in range(6):
            flipped = word[:axis] + ("1" if word[axis] == "0" else "0") + word[axis + 1:]
            other = by_bits[flipped]
            if index < other:
                edges.append((index, other, edge_orbit(axis)))
    return edges


def box_wobble_atoms(codons: list[str], labels: list[int]) -> list[tuple[int, ...]]:
    atoms: dict[tuple[str, int], list[int]] = {}
    for index, codon in enumerate(codons):
        atoms.setdefault((codon[:2], labels[index]), []).append(index)
    return [
        tuple(indices)
        for _, indices in sorted(atoms.items(), key=lambda item: (item[0][0], min(item[1])))
    ]


def atom_pair_edge_profiles(
    atoms: list[tuple[int, ...]],
    vertex_to_atom: list[int],
    edges: list[tuple[int, int, int]],
) -> dict[tuple[int, int], tuple[int, int]]:
    profiles = {(left, right): [0, 0] for left in range(len(atoms)) for right in range(left + 1, len(atoms))}
    for vertex_a, vertex_b, orbit in edges:
        atom_a = vertex_to_atom[vertex_a]
        atom_b = vertex_to_atom[vertex_b]
        if atom_a == atom_b:
            continue
        key = (atom_a, atom_b) if atom_a < atom_b else (atom_b, atom_a)
        profiles[key][orbit] += 1
    return {key: tuple(value) for key, value in profiles.items()}


def group_descriptor(
    group: tuple[int, ...],
    atom_sizes: list[int],
    pair_profiles: dict[tuple[int, int], tuple[int, int]],
) -> tuple[tuple[int, ...], tuple[int, int]]:
    sizes = tuple(sorted((atom_sizes[atom] for atom in group), reverse=True))
    if len(group) == 1:
        return sizes, (0, 0)
    if len(group) == 2:
        return sizes, pair_profiles[tuple(sorted(group))]
    raise ValueError("the standard assembly signature contains no group with more than two atoms")


def state_signature(
    groups: tuple[tuple[int, ...], ...],
    atom_sizes: list[int],
    pair_profiles: dict[tuple[int, int], tuple[int, int]],
) -> tuple[tuple[tuple[int, ...], tuple[int, int]], ...]:
    return tuple(sorted(group_descriptor(group, atom_sizes, pair_profiles) for group in groups))


def observed_atom_groups(labels: list[int], vertex_to_atom: list[int], atom_count: int) -> tuple[tuple[int, ...], ...]:
    by_label: dict[int, set[int]] = defaultdict(set)
    for vertex, label in enumerate(labels):
        by_label[label].add(vertex_to_atom[vertex])
    groups = tuple(sorted(tuple(sorted(atoms)) for atoms in by_label.values()))
    if sorted(atom for group in groups for atom in group) != list(range(atom_count)):
        raise RuntimeError("observed atom groups do not cover the atom set")
    return groups


def enumerate_conditioned_states(
    atom_sizes: list[int],
    pair_profiles: dict[tuple[int, int], tuple[int, int]],
    observed_signature: tuple[tuple[tuple[int, ...], tuple[int, int]], ...],
) -> list[tuple[tuple[int, ...], ...]]:
    by_size: dict[int, list[int]] = defaultdict(list)
    for atom, size in enumerate(atom_sizes):
        by_size[size].append(atom)

    quartets = by_size[4]
    triplets = by_size[3]
    doublets = by_size[2]
    singlets = by_size[1]
    if len(triplets) != 1:
        raise RuntimeError("unexpected standard atom size signature")

    required_pair_descriptors = Counter(
        descriptor for descriptor in observed_signature if len(descriptor[0]) == 2
    )
    states: set[tuple[tuple[int, ...], ...]] = set()

    quartet_doublet_pairs = [
        (quartet, doublet, group_descriptor((quartet, doublet), atom_sizes, pair_profiles))
        for quartet in quartets
        for doublet in doublets
    ]
    doublet_singlet_pairs = [
        (doublet, singlet, group_descriptor((doublet, singlet), atom_sizes, pair_profiles))
        for doublet in doublets
        for singlet in singlets
    ]

    def choose_quartet_doublet_pairs(
        start: int,
        chosen: list[tuple[int, int]],
        used_quartets: set[int],
        used_doublets: set[int],
        remaining: Counter[tuple[tuple[int, ...], tuple[int, int]]],
    ) -> None:
        if len(chosen) == 3:
            for doublet, singlet, descriptor in doublet_singlet_pairs:
                if doublet in used_doublets:
                    continue
                if remaining[descriptor] <= 0:
                    continue
                next_remaining = remaining.copy()
                next_remaining[descriptor] -= 1
                if any(value != 0 for value in next_remaining.values()):
                    continue
                multi_groups = [tuple(sorted(pair)) for pair in chosen]
                multi_groups.append(tuple(sorted((doublet, singlet))))
                used_atoms = {atom for group in multi_groups for atom in group}
                singletons = [(atom,) for atom in range(len(atom_sizes)) if atom not in used_atoms]
                groups = tuple(sorted(multi_groups + singletons))
                if state_signature(groups, atom_sizes, pair_profiles) == observed_signature:
                    states.add(groups)
            return

        for index in range(start, len(quartet_doublet_pairs)):
            quartet, doublet, descriptor = quartet_doublet_pairs[index]
            if quartet in used_quartets or doublet in used_doublets:
                continue
            if remaining[descriptor] <= 0:
                continue
            next_remaining = remaining.copy()
            next_remaining[descriptor] -= 1
            choose_quartet_doublet_pairs(
                index + 1,
                chosen + [(quartet, doublet)],
                used_quartets | {quartet},
                used_doublets | {doublet},
                next_remaining,
            )

    choose_quartet_doublet_pairs(0, [], set(), set(), required_pair_descriptors.copy())
    return sorted(states)


def group_vertices(group: tuple[int, ...], atoms: list[tuple[int, ...]]) -> tuple[int, ...]:
    return tuple(sorted(vertex for atom in group for vertex in atoms[atom]))


def boundary_degree_vector(vertices: tuple[int, ...], edges: list[tuple[int, int, int]]) -> tuple[int, int]:
    vertex_set = set(vertices)
    counts = [0, 0]
    for left, right, orbit in edges:
        if (left in vertex_set) != (right in vertex_set):
            counts[orbit] += 1
    return tuple(counts)


def boundary_group_descriptor(
    group: tuple[int, ...],
    atoms: list[tuple[int, ...]],
    atom_sizes: list[int],
    pair_profiles: dict[tuple[int, int], tuple[int, int]],
    edges: list[tuple[int, int, int]],
) -> tuple[tuple[tuple[int, ...], tuple[int, int]], tuple[int, int]]:
    return (
        group_descriptor(group, atom_sizes, pair_profiles),
        boundary_degree_vector(group_vertices(group, atoms), edges),
    )


def boundary_state_signature(
    groups: tuple[tuple[int, ...], ...],
    descriptor_cache: dict[tuple[int, ...], tuple[tuple[tuple[int, ...], tuple[int, int]], tuple[int, int]]],
) -> tuple[tuple[tuple[tuple[int, ...], tuple[int, int]], tuple[int, int]], ...]:
    return tuple(sorted(descriptor_cache[group] for group in groups))


def atom_labels_for_state(groups: tuple[tuple[int, ...], ...], atom_count: int) -> list[int]:
    atom_labels = [-1] * atom_count
    for block, group in enumerate(groups):
        for atom in group:
            atom_labels[atom] = block
    if any(label < 0 for label in atom_labels):
        raise RuntimeError("state leaves an atom unlabeled")
    return atom_labels


def quotient_matrix(
    state: tuple[tuple[int, ...], ...],
    vertex_to_atom: list[int],
    edges: list[tuple[int, int, int]],
) -> list[list[int]]:
    atom_labels = atom_labels_for_state(state, max(vertex_to_atom) + 1)
    size = len(state)
    matrix = [[0 for _ in range(size)] for _ in range(size)]
    for left, right, _orbit in edges:
        block_left = atom_labels[vertex_to_atom[left]]
        block_right = atom_labels[vertex_to_atom[right]]
        if block_left == block_right:
            continue
        matrix[block_left][block_right] += 1
        matrix[block_right][block_left] += 1
    return matrix


def bareiss_det(matrix: list[list[int]]) -> int:
    size = len(matrix)
    if size == 0:
        return 1
    work = [row[:] for row in matrix]
    sign = 1
    previous = 1
    for pivot_index in range(size - 1):
        pivot_row = pivot_index
        while pivot_row < size and work[pivot_row][pivot_index] == 0:
            pivot_row += 1
        if pivot_row == size:
            return 0
        if pivot_row != pivot_index:
            work[pivot_index], work[pivot_row] = work[pivot_row], work[pivot_index]
            sign *= -1
        pivot = work[pivot_index][pivot_index]
        for row in range(pivot_index + 1, size):
            for col in range(pivot_index + 1, size):
                numerator = work[row][col] * pivot - work[row][pivot_index] * work[pivot_index][col]
                if previous != 1:
                    numerator //= previous
                work[row][col] = numerator
        previous = pivot
        for row in range(pivot_index + 1, size):
            work[row][pivot_index] = 0
        for col in range(pivot_index + 1, size):
            work[pivot_index][col] = 0
    return sign * work[size - 1][size - 1]


def spanning_tree_count(matrix: list[list[int]]) -> int:
    size = len(matrix)
    laplacian = [[0 for _ in range(size)] for _ in range(size)]
    for row in range(size):
        degree = sum(matrix[row])
        for col in range(size):
            laplacian[row][col] = degree if row == col else -matrix[row][col]
    cofactor = [row[:-1] for row in laplacian[:-1]]
    tau = bareiss_det(cofactor)
    if tau < 0:
        raise ArithmeticError("weighted Laplacian cofactor is negative")
    return tau


def pair_concentration(matrix: list[list[int]]) -> int:
    total = 0
    for row in range(len(matrix)):
        for col in range(row + 1, len(matrix)):
            total += matrix[row][col] * matrix[row][col]
    return total


def quotient_canonical(matrix: list[list[int]]) -> tuple[int, ...]:
    size = len(matrix)
    descriptors = [
        (sum(matrix[row]), sorted((matrix[row][col] for col in range(size) if col != row), reverse=True), row)
        for row in range(size)
    ]
    color_to_rows: dict[tuple[int, tuple[int, ...]], list[int]] = defaultdict(list)
    for degree, weights, row in descriptors:
        color_to_rows[(degree, tuple(weights))].append(row)
    color_classes = [rows for _color, rows in sorted(color_to_rows.items(), key=lambda item: item[0])]
    permutations_by_class = [list(permutations(rows)) for rows in color_classes]

    best: tuple[int, ...] | None = None
    for parts in product(*permutations_by_class):
        order = tuple(vertex for part in parts for vertex in part)
        code = tuple(matrix[order[row]][order[col]] for row in range(size) for col in range(row + 1, size))
        if best is None or code < best:
            best = code
    if best is None:
        raise RuntimeError("empty quotient matrix")
    return best


def state_vertex_partition(
    state: tuple[tuple[int, ...], ...],
    atoms: list[tuple[int, ...]],
) -> tuple[tuple[int, ...], ...]:
    return tuple(sorted(group_vertices(group, atoms) for group in state))


def automorphism_permutations(codons: list[str]) -> list[tuple[int, ...]]:
    bitwords = [codon_bits(codon) for codon in codons]
    index_by_word = {word: index for index, word in enumerate(bitwords)}
    permutations_out: list[tuple[int, ...]] = []
    box_axis_permutations = list(permutations(range(4)))
    wobble_axis_permutations = [tuple(4 + axis for axis in perm) for perm in permutations(range(2))]
    for box_perm in box_axis_permutations:
        for wobble_perm in wobble_axis_permutations:
            axis_image = box_perm + wobble_perm
            for flips in product((0, 1), repeat=6):
                mapping = []
                for word in bitwords:
                    image = ["0"] * 6
                    for axis in range(6):
                        bit = int(word[axis]) ^ flips[axis]
                        image[axis_image[axis]] = str(bit)
                    mapping.append(index_by_word["".join(image)])
                permutations_out.append(tuple(mapping))
    return permutations_out


def partition_canonical(
    partition: tuple[tuple[int, ...], ...],
    automorphisms: list[tuple[int, ...]],
) -> tuple[tuple[int, ...], ...]:
    best: tuple[tuple[int, ...], ...] | None = None
    for mapping in automorphisms:
        image = tuple(sorted(tuple(sorted(mapping[vertex] for vertex in block)) for block in partition))
        if best is None or image < best:
            best = image
    if best is None:
        raise RuntimeError("empty automorphism group")
    return best


def has_multiple_automorphism_orbits(
    states: list[tuple[tuple[int, ...], ...]],
    atoms: list[tuple[int, ...]],
    codons: list[str],
    distinct_tau_values: int,
    vertex_to_atom: list[int],
    edges: list[tuple[int, int, int]],
) -> tuple[bool, int, int, str]:
    if distinct_tau_values >= 2:
        return True, 2, BOX_WOBBLE_AUTOMORPHISM_COUNT, "distinct exact spanning-tree counts"
    quotient_topologies: set[tuple[int, ...]] = set()
    for state in states:
        quotient_topologies.add(quotient_canonical(quotient_matrix(state, vertex_to_atom, edges)))
        if len(quotient_topologies) >= 2:
            return True, 2, BOX_WOBBLE_AUTOMORPHISM_COUNT, "distinct label-free weighted quotient topologies"
    automorphisms = automorphism_permutations(codons)
    orbit_representatives: set[tuple[tuple[int, ...], ...]] = set()
    for state in states:
        representative = partition_canonical(state_vertex_partition(state, atoms), automorphisms)
        orbit_representatives.add(representative)
        if len(orbit_representatives) >= 2:
            return True, len(orbit_representatives), len(automorphisms), (
                "canonicalization under the box/wobble-preserving automorphism group"
            )
    return False, len(orbit_representatives), len(automorphisms), (
        "canonicalization under the box/wobble-preserving automorphism group"
    )


def mean_variance_int(values: list[int]) -> tuple[float, float]:
    mean = sum(values) / len(values)
    if len(values) <= 1:
        return mean, 0.0
    variance = sum((value - mean) ** 2 for value in values) / (len(values) - 1)
    return mean, variance


def round_float(value: float | None) -> float | None:
    if value is None:
        return None
    return float(f"{value:.12g}")


def main() -> None:
    codons = codon_order()
    families = family_order(codons)
    labels = standard_labels(codons, families)
    edges = q6_edges(codons)
    atoms = box_wobble_atoms(codons, labels)
    atom_sizes = [len(atom) for atom in atoms]
    vertex_to_atom = [-1] * len(codons)
    for atom_index, atom in enumerate(atoms):
        for vertex in atom:
            vertex_to_atom[vertex] = atom_index

    pair_profiles = atom_pair_edge_profiles(atoms, vertex_to_atom, edges)
    observed_groups = observed_atom_groups(labels, vertex_to_atom, len(atoms))
    observed_signature = state_signature(observed_groups, atom_sizes, pair_profiles)
    base_states = enumerate_conditioned_states(atom_sizes, pair_profiles, observed_signature)
    observed_state = tuple(sorted(tuple(sorted(group)) for group in observed_groups))

    all_base_groups = sorted({group for state in base_states for group in state})
    descriptor_cache = {
        group: boundary_group_descriptor(group, atoms, atom_sizes, pair_profiles, edges)
        for group in all_base_groups
    }
    observed_boundary_signature = boundary_state_signature(observed_state, descriptor_cache)
    states = [
        state
        for state in base_states
        if boundary_state_signature(state, descriptor_cache) == observed_boundary_signature
    ]
    observed_state_index = states.index(observed_state) if observed_state in states else -1

    checks = [
        {"name": "codon_count", "ok": len(codons) == 64, "observed": len(codons), "expected": 64},
        {"name": "q6_edge_count", "ok": len(edges) == 192, "observed": len(edges), "expected": 192},
        {"name": "fiber_count", "ok": len(families) == 21, "observed": len(families), "expected": 21},
        {
            "name": "atom_count",
            "ok": len(atoms) == 25,
            "observed": len(atoms),
            "expected": 25,
            "atom_size_multiset": sorted(atom_sizes, reverse=True),
        },
        {
            "name": "base_conditioned_null_exact_enumeration",
            "ok": len(base_states) > 0,
            "omega_size": len(base_states),
            "method": "direct enumeration of all label-free atom regroupings with standard assembly-signature and edge-profile descriptors",
        },
        {
            "name": "boundary_degree_conditioned_null_exact_filter",
            "ok": len(states) > 0,
            "omega_size": len(states),
            "base_omega_size": len(base_states),
        },
        {
            "name": "observed_state_in_conditioned_null",
            "ok": observed_state_index >= 0,
            "observed_state_index": observed_state_index,
        },
    ]

    if not all(bool(check["ok"]) for check in checks):
        emit(
            "needs_derivation",
            gate_nonzero_variance=False,
            gate_multi_orbit=False,
            omega_size=len(states),
            tau_observed=None,
            T_chan_obs=None,
            p_value=None,
            C_pair_secondary=None,
            null_method="exact_enumeration",
            null_seed=NULL_SEED,
            null_draws=NULL_DRAWS,
            conditions_out=["e_in", "box", "wobble", "edge_margins", "boundary_degrees"],
            checks=checks,
            reason="The boundary-degree-conditioned exact null could not be constructed with the observed partition included.",
        )

    tau_values: list[int] = []
    c_pair_values: list[int] = []
    observed_tau: int | None = None
    observed_c_pair: int | None = None
    observed_total_weight: int | None = None
    observed_degree_sequence: list[int] | None = None

    for state in states:
        matrix = quotient_matrix(state, vertex_to_atom, edges)
        tau = spanning_tree_count(matrix)
        c_pair = pair_concentration(matrix)
        tau_values.append(tau)
        c_pair_values.append(c_pair)
        if state == observed_state:
            observed_tau = tau
            observed_c_pair = c_pair
            observed_total_weight = sum(matrix[row][col] for row in range(len(matrix)) for col in range(row + 1, len(matrix)))
            observed_degree_sequence = sorted((sum(row) for row in matrix), reverse=True)

    if observed_tau is None or observed_c_pair is None:
        emit(
            "needs_derivation",
            gate_nonzero_variance=False,
            gate_multi_orbit=False,
            omega_size=len(states),
            tau_observed=None,
            T_chan_obs=None,
            p_value=None,
            C_pair_secondary=None,
            null_method="exact_enumeration",
            null_seed=NULL_SEED,
            null_draws=NULL_DRAWS,
            conditions_out=["e_in", "box", "wobble", "edge_margins", "boundary_degrees"],
            checks=checks + [{"name": "observed_statistic_defined", "ok": False}],
            reason="The observed quotient statistic was not recovered after exact null construction.",
        )

    tau_mean, tau_variance = mean_variance_int(tau_values)
    gate_nonzero_variance = len(set(tau_values)) >= 2
    distinct_tau_values = len(set(tau_values))
    distinct_c_pair_values = len(set(c_pair_values))
    gate_multi_orbit, detected_orbits, automorphism_count, orbit_certificate = has_multiple_automorphism_orbits(
        states,
        atoms,
        codons,
        distinct_tau_values,
        vertex_to_atom,
        edges,
    )

    upper_count = sum(1 for tau in tau_values if tau <= observed_tau)
    lower_count = sum(1 for tau in tau_values if tau >= observed_tau)
    p_value = upper_count / len(tau_values)
    lower_tail_p_value = lower_count / len(tau_values)
    ordered_tau = sorted(tau_values)

    checks.extend(
        [
            {
                "name": "boundary_degree_vectors_conditioned",
                "ok": all(boundary_state_signature(state, descriptor_cache) == observed_boundary_signature for state in states),
                "description": "the exact null fixes the unlabeled multiset of fiber boundary-degree vectors by edge orbit",
            },
            {
                "name": "weighted_degree_sequence_conditioned",
                "ok": True,
                "description": "each weighted quotient degree equals the sum of the conditioned boundary-degree vector",
            },
            {
                "name": "laplacian_cofactor_exact_integer",
                "ok": all(tau > 0 for tau in tau_values),
                "method": "fraction-free Bareiss determinant on the integer weighted Laplacian principal cofactor",
            },
            {
                "name": "nonzero_variance_gate",
                "ok": gate_nonzero_variance,
                "distinct_tau_values": distinct_tau_values,
                "tau_variance": round_float(tau_variance),
            },
            {
                "name": "multi_orbit_gate",
                "ok": gate_multi_orbit,
                "detected_orbits_before_stop": detected_orbits,
                "automorphism_count": automorphism_count,
                "certificate": orbit_certificate,
                "automorphism_model": "coordinate flips and coordinate permutations preserving box axes and wobble axes",
            },
        ]
    )

    forced_reason = "spanning-tree statistic is algebraically forced by block-size + boundary-degree structure"
    if not gate_nonzero_variance or not gate_multi_orbit:
        status = "coincidence"
        reason = forced_reason
    elif p_value <= EXTREME_ALPHA:
        status = "certified"
        reason = (
            "The standard code is an upper-tail outlier for the predeclared quotient "
            f"spanning-tree compression statistic under exact boundary-degree-conditioned enumeration (p={round_float(p_value)})."
        )
    elif lower_tail_p_value <= EXTREME_ALPHA:
        status = "refuted"
        reason = (
            "The standard code is extreme in the high-spanning-tree tail, opposite to the "
            f"compression claim (lower-tail p={round_float(lower_tail_p_value)})."
        )
    else:
        status = "coincidence"
        reason = (
            "The prerequisite gates pass, but the standard code is typical for quotient "
            f"spanning-tree compression (upper-tail p={round_float(p_value)})."
        )

    emit(
        status,
        gate_nonzero_variance=gate_nonzero_variance,
        gate_multi_orbit=gate_multi_orbit,
        omega_size=len(states),
        tau_observed=observed_tau,
        T_chan_obs=round_float(-math.log(observed_tau)),
        p_value=round_float(p_value),
        C_pair_secondary=observed_c_pair,
        null_method="exact_enumeration",
        null_seed=NULL_SEED,
        null_draws=NULL_DRAWS,
        conditions_out=["e_in", "box", "wobble", "edge_margins", "boundary_degrees"],
        checks=checks,
        reason=reason,
        threshold={"compression_upper_tail_alpha": EXTREME_ALPHA},
        lower_tail_p_value=round_float(lower_tail_p_value),
        null_summary={
            "tau_min": ordered_tau[0],
            "tau_mean": round_float(tau_mean),
            "tau_variance": round_float(tau_variance),
            "tau_median": ordered_tau[len(ordered_tau) // 2],
            "tau_max": ordered_tau[-1],
            "tau_le_observed": upper_count,
            "tau_ge_observed": lower_count,
            "distinct_tau_values": distinct_tau_values,
            "distinct_C_pair_values": distinct_c_pair_values,
            "C_pair_min": min(c_pair_values),
            "C_pair_max": max(c_pair_values),
        },
        observed_quotient_summary={
            "total_cross_fiber_weight": observed_total_weight,
            "weighted_degree_sequence_desc": observed_degree_sequence,
        },
        observed_boundary_signature_counts={
            str(signature): count
            for signature, count in sorted(Counter(observed_boundary_signature).items())
        },
        automorphism_structure={
            "vertex_model": "Q6 with codon bases encoded as two bits each",
            "edge_orbits": list(EDGE_ORBITS),
            "box_axes": sorted(BOX_AXES),
            "wobble_axes": sorted(WOBBLE_AXES),
        },
    )


if __name__ == "__main__":
    main()

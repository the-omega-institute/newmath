#!/usr/bin/env python3
"""External bypass-conductance extremality for disconnected synonymous fibers.

The null is the label-free regrouping space of the 25 fixed box/wobble atoms,
conditioned on the standard assembly signatures, per-edge-orbit synonymous
edge profiles, boundary-degree vectors, and component structures.
"""
from __future__ import annotations

from collections import Counter, defaultdict, deque
from itertools import combinations, permutations, product
import json
import math
import sys


EXPERIMENT_ID = "bypass_conductance_extremality"
CLAIM_ID = "bridge.genetic_code.bypass_conductance.extremality"
NULL_SEED = None
NULL_DRAWS = None
EXTREME_ALPHA = 0.01
ZERO_TOL = 1e-10

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


def q6_edges_and_neighbors(codons: list[str]) -> tuple[list[tuple[int, int, int]], list[list[int]]]:
    bitwords = [codon_bits(codon) for codon in codons]
    by_bits = {word: index for index, word in enumerate(bitwords)}
    edges: list[tuple[int, int, int]] = []
    neighbors: list[list[int]] = [[] for _ in codons]
    for index, word in enumerate(bitwords):
        for axis in range(6):
            flipped = word[:axis] + ("1" if word[axis] == "0" else "0") + word[axis + 1:]
            other = by_bits[flipped]
            neighbors[index].append(other)
            if index < other:
                edges.append((index, other, edge_orbit(axis)))
    return edges, neighbors


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


def component_canonical(vertices: tuple[int, ...], edge_set: set[tuple[int, int]]) -> str:
    ordered = tuple(sorted(vertices))
    if len(ordered) <= 1:
        return ""
    index_by_vertex = {vertex: index for index, vertex in enumerate(ordered)}
    edge_bits = [[0 for _ in ordered] for _ in ordered]
    for left, right in combinations(ordered, 2):
        if (left, right) in edge_set:
            row = index_by_vertex[left]
            col = index_by_vertex[right]
            edge_bits[row][col] = 1
            edge_bits[col][row] = 1
    best: str | None = None
    for perm in permutations(range(len(ordered))):
        bits = []
        for row in range(len(ordered)):
            for col in range(row + 1, len(ordered)):
                bits.append("1" if edge_bits[perm[row]][perm[col]] else "0")
        code = "".join(bits)
        if best is None or code < best:
            best = code
    return best or ""


def connected_components(vertices: tuple[int, ...], neighbors: list[list[int]]) -> tuple[tuple[int, ...], ...]:
    vertex_set = set(vertices)
    seen: set[int] = set()
    components: list[tuple[int, ...]] = []
    for start in sorted(vertices):
        if start in seen:
            continue
        queue = deque([start])
        seen.add(start)
        component: list[int] = []
        while queue:
            vertex = queue.popleft()
            component.append(vertex)
            for neighbor in neighbors[vertex]:
                if neighbor in vertex_set and neighbor not in seen:
                    seen.add(neighbor)
                    queue.append(neighbor)
        components.append(tuple(sorted(component)))
    return tuple(sorted(components))


def boundary_degree_vector(vertices: tuple[int, ...], edges: list[tuple[int, int, int]]) -> tuple[int, int]:
    vertex_set = set(vertices)
    counts = [0, 0]
    for left, right, orbit in edges:
        if (left in vertex_set) != (right in vertex_set):
            counts[orbit] += 1
    return tuple(counts)


def component_structure(
    vertices: tuple[int, ...],
    neighbors: list[list[int]],
    edge_set: set[tuple[int, int]],
) -> tuple[tuple[int, str], ...]:
    components = connected_components(vertices, neighbors)
    return tuple(sorted((len(component), component_canonical(component, edge_set)) for component in components))


def group_vertices(group: tuple[int, ...], atoms: list[tuple[int, ...]]) -> tuple[int, ...]:
    return tuple(sorted(vertex for atom in group for vertex in atoms[atom]))


def full_group_descriptor(
    group: tuple[int, ...],
    atoms: list[tuple[int, ...]],
    atom_sizes: list[int],
    pair_profiles: dict[tuple[int, int], tuple[int, int]],
    edges: list[tuple[int, int, int]],
    neighbors: list[list[int]],
    edge_set: set[tuple[int, int]],
) -> tuple[tuple[tuple[int, ...], tuple[int, int]], tuple[int, int], tuple[tuple[int, str], ...]]:
    vertices = group_vertices(group, atoms)
    return (
        group_descriptor(group, atom_sizes, pair_profiles),
        boundary_degree_vector(vertices, edges),
        component_structure(vertices, neighbors, edge_set),
    )


def full_state_signature(
    groups: tuple[tuple[int, ...], ...],
    descriptor_cache: dict[
        tuple[int, ...],
        tuple[tuple[tuple[int, ...], tuple[int, int]], tuple[int, int], tuple[tuple[int, str], ...]],
    ],
) -> tuple[tuple[tuple[tuple[int, ...], tuple[int, int]], tuple[int, int], tuple[tuple[int, str], ...]], ...]:
    return tuple(sorted(descriptor_cache[group] for group in groups))


def solve_linear(matrix: list[list[float]], rhs: list[float], tol: float = 1e-12) -> list[float]:
    size = len(matrix)
    work = [matrix[row][:] + [rhs[row]] for row in range(size)]
    for col in range(size):
        pivot = max(range(col, size), key=lambda row: abs(work[row][col]))
        if abs(work[pivot][col]) <= tol:
            raise ArithmeticError("singular conductance system")
        work[col], work[pivot] = work[pivot], work[col]
        scale = work[col][col]
        work[col] = [value / scale for value in work[col]]
        for row in range(size):
            if row == col:
                continue
            factor = work[row][col]
            if abs(factor) > tol:
                work[row] = [value - factor * base for value, base in zip(work[row], work[col])]
    return [work[row][-1] for row in range(size)]


def contracted_adjacency(
    fiber_vertices: tuple[int, ...],
    left_component: tuple[int, ...],
    right_component: tuple[int, ...],
    edges: list[tuple[int, int, int]],
) -> list[dict[int, int]]:
    left_set = set(left_component)
    right_set = set(right_component)
    deleted = set(fiber_vertices) - left_set - right_set
    outside = sorted(set(range(64)) - deleted - left_set - right_set)
    node_by_vertex = {vertex: index + 2 for index, vertex in enumerate(outside)}
    for vertex in left_set:
        node_by_vertex[vertex] = 0
    for vertex in right_set:
        node_by_vertex[vertex] = 1

    adjacency: list[dict[int, int]] = [defaultdict(int) for _ in range(len(outside) + 2)]
    for vertex_a, vertex_b, _orbit in edges:
        if vertex_a in deleted or vertex_b in deleted:
            continue
        node_a = node_by_vertex[vertex_a]
        node_b = node_by_vertex[vertex_b]
        if node_a == node_b:
            continue
        adjacency[node_a][node_b] += 1
        adjacency[node_b][node_a] += 1
    return [dict(row) for row in adjacency]


def effective_conductance(adjacency: list[dict[int, int]]) -> float:
    interior = [node for node in range(len(adjacency)) if node not in (0, 1)]
    if not interior:
        return float(adjacency[0].get(1, 0))
    row_by_node = {node: row for row, node in enumerate(interior)}
    matrix = [[0.0 for _ in interior] for _ in interior]
    rhs = [0.0 for _ in interior]
    for node in interior:
        row = row_by_node[node]
        degree = sum(adjacency[node].values())
        matrix[row][row] = float(degree)
        for other, weight in adjacency[node].items():
            if other == 0:
                rhs[row] += float(weight)
            elif other == 1:
                continue
            else:
                matrix[row][row_by_node[other]] -= float(weight)
    potentials = solve_linear(matrix, rhs)
    potential_by_node = {0: 1.0, 1: 0.0}
    for node, value in zip(interior, potentials):
        potential_by_node[node] = value
    current = 0.0
    for other, weight in adjacency[0].items():
        current += weight * (1.0 - potential_by_node[other])
    return 0.0 if abs(current) <= ZERO_TOL else current


def shortest_external_audit(adjacency: list[dict[int, int]]) -> tuple[int | None, int]:
    distances = [-1 for _ in adjacency]
    path_counts = [0 for _ in adjacency]
    distances[0] = 0
    path_counts[0] = 1
    queue = deque([0])
    while queue:
        node = queue.popleft()
        for other, multiplicity in adjacency[node].items():
            if distances[other] < 0:
                distances[other] = distances[node] + 1
                path_counts[other] = path_counts[node] * multiplicity
                queue.append(other)
            elif distances[other] == distances[node] + 1:
                path_counts[other] += path_counts[node] * multiplicity
    if distances[1] < 0:
        return None, 0
    return distances[1], path_counts[1]


def group_bypass_data(
    group: tuple[int, ...],
    atoms: list[tuple[int, ...]],
    edges: list[tuple[int, int, int]],
    neighbors: list[list[int]],
) -> tuple[float, list[tuple[int | None, int]], int]:
    vertices = group_vertices(group, atoms)
    components = connected_components(vertices, neighbors)
    if len(components) < 2:
        return 0.0, [], 0
    total = 0.0
    audit: list[tuple[int | None, int]] = []
    for left_index in range(len(components)):
        for right_index in range(left_index + 1, len(components)):
            adjacency = contracted_adjacency(vertices, components[left_index], components[right_index], edges)
            total += effective_conductance(adjacency)
            audit.append(shortest_external_audit(adjacency))
    return total, sorted(audit), len(components)


def state_bypass_statistic(
    state: tuple[tuple[int, ...], ...],
    group_cache: dict[tuple[int, ...], tuple[float, list[tuple[int | None, int]], int]],
) -> tuple[float, tuple[tuple[int | None, int], ...], int]:
    total = 0.0
    audit: list[tuple[int | None, int]] = []
    disconnected_count = 0
    for group in state:
        group_total, group_audit, component_count = group_cache[group]
        if component_count >= 2:
            disconnected_count += 1
            total += group_total
            audit.extend(group_audit)
    return total, tuple(sorted(audit)), disconnected_count


def state_vertex_partition(state: tuple[tuple[int, ...], ...], atoms: list[tuple[int, ...]]) -> tuple[tuple[int, ...], ...]:
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
    distinct_values: int,
    distinct_audits: int,
) -> tuple[bool, int, int]:
    if distinct_values >= 2:
        return True, 2, BOX_WOBBLE_AUTOMORPHISM_COUNT
    if distinct_audits >= 2:
        return True, 2, BOX_WOBBLE_AUTOMORPHISM_COUNT
    automorphisms = automorphism_permutations(codons)
    orbit_representatives: set[tuple[tuple[int, ...], ...]] = set()
    for state in states:
        representative = partition_canonical(state_vertex_partition(state, atoms), automorphisms)
        orbit_representatives.add(representative)
        if len(orbit_representatives) >= 2:
            return True, len(orbit_representatives), len(automorphisms)
    return False, len(orbit_representatives), len(automorphisms)


def mean_variance(values: list[float]) -> tuple[float, float]:
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
    edges, neighbors = q6_edges_and_neighbors(codons)
    edge_set = {(left, right) for left, right, _orbit in edges}
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
        group: full_group_descriptor(group, atoms, atom_sizes, pair_profiles, edges, neighbors, edge_set)
        for group in all_base_groups
    }
    observed_full_signature = full_state_signature(observed_state, descriptor_cache)
    states = [
        state
        for state in base_states
        if full_state_signature(state, descriptor_cache) == observed_full_signature
    ]
    observed_state_index = states.index(observed_state) if observed_state in states else -1

    all_groups = sorted({group for state in states for group in state})
    group_cache = {
        group: group_bypass_data(group, atoms, edges, neighbors)
        for group in all_groups
    }

    checks = [
        {"name": "codon_count", "ok": len(codons) == 64, "observed": len(codons), "expected": 64},
        {"name": "q6_edge_count", "ok": len(edges) == 192, "observed": len(edges), "expected": 192},
        {"name": "q6_degree", "ok": all(len(set(row)) == 6 for row in neighbors), "expected": 6},
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
            "name": "component_conditioned_null_exact_filter",
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
            n_disconnected_fibers=None,
            gate_nonzero_variance=False,
            gate_multi_orbit=False,
            omega_size_or_bound=len(states),
            T_obs=None,
            p_value=None,
            null_method="exact_enumeration",
            null_seed=NULL_SEED,
            null_draws=NULL_DRAWS,
            conditions_out=["e_in", "box", "wobble", "edge_margins", "boundary_degrees", "component_structure"],
            not_tailored_to_named_fiber=True,
            checks=checks,
            reason="The component-conditioned exact null could not be constructed with the observed partition included.",
        )

    values: list[float] = []
    audit_values: list[tuple[tuple[int | None, int], ...]] = []
    disconnected_counts: list[int] = []
    observed_t: float | None = None
    observed_audit: tuple[tuple[int | None, int], ...] | None = None
    observed_disconnected_count: int | None = None
    for state in states:
        value, audit, disconnected_count = state_bypass_statistic(state, group_cache)
        values.append(value)
        audit_values.append(audit)
        disconnected_counts.append(disconnected_count)
        if state == observed_state:
            observed_t = value
            observed_audit = audit
            observed_disconnected_count = disconnected_count

    if observed_t is None or observed_audit is None or observed_disconnected_count is None:
        emit(
            "needs_derivation",
            n_disconnected_fibers=None,
            gate_nonzero_variance=False,
            gate_multi_orbit=False,
            omega_size_or_bound=len(states),
            T_obs=None,
            p_value=None,
            null_method="exact_enumeration",
            null_seed=NULL_SEED,
            null_draws=NULL_DRAWS,
            conditions_out=["e_in", "box", "wobble", "edge_margins", "boundary_degrees", "component_structure"],
            not_tailored_to_named_fiber=True,
            checks=checks + [{"name": "observed_statistic_defined", "ok": False}],
            reason="The observed statistic was not recovered after exact null construction.",
        )

    mean, variance = mean_variance(values)
    gate_nonzero_variance = variance > ZERO_TOL
    upper_count = sum(1 for value in values if value + ZERO_TOL >= observed_t)
    lower_count = sum(1 for value in values if value <= observed_t + ZERO_TOL)
    p_value = upper_count / len(values)
    lower_p_value = lower_count / len(values)
    distinct_values = len({round(value, 12) for value in values})
    distinct_audits = len(set(audit_values))
    gate_multi_orbit, detected_orbits, automorphism_count = has_multiple_automorphism_orbits(
        states,
        atoms,
        codons,
        distinct_values,
        distinct_audits,
    )

    checks.extend(
        [
            {
                "name": "not_tailored_to_named_fiber",
                "ok": True,
                "description": "the primary sum ranges over every disconnected fiber in each state",
            },
            {
                "name": "component_structure_conditioned",
                "ok": all(full_state_signature(state, descriptor_cache) == observed_full_signature for state in states),
            },
            {
                "name": "boundary_degree_vectors_conditioned",
                "ok": True,
                "description": "boundary-degree vectors are part of the exact full-state descriptor",
            },
            {
                "name": "nonzero_variance_gate",
                "ok": gate_nonzero_variance,
                "variance": round_float(variance),
                "distinct_T_values": distinct_values,
            },
            {
                "name": "multi_orbit_gate",
                "ok": gate_multi_orbit,
                "detected_orbits_before_stop": detected_orbits,
                "automorphism_count": automorphism_count,
                "certificate": (
                    "distinct label-free bypass statistic or audit"
                    if distinct_values >= 2 or distinct_audits >= 2
                    else "canonicalization under the box/wobble-preserving automorphism group"
                ),
                "automorphism_model": "coordinate flips and coordinate permutations preserving box axes and wobble axes",
            },
        ]
    )

    forced_reason = "no label-free invariant of this type exists beyond the already-fixed structure"
    if not gate_nonzero_variance or not gate_multi_orbit:
        status = "coincidence"
        reason = forced_reason
    elif p_value <= EXTREME_ALPHA:
        status = "certified"
        reason = (
            "The standard code is an upper-tail outlier for the predeclared external "
            f"bypass-conductance statistic under exact component-conditioned enumeration (p={round_float(p_value)})."
        )
    elif lower_p_value <= EXTREME_ALPHA:
        status = "refuted"
        reason = (
            "The standard code is extreme in the low-conductance tail, opposite to the "
            f"near-merge compensation claim (lower-tail p={round_float(lower_p_value)})."
        )
    else:
        status = "coincidence"
        reason = (
            "The prerequisite gates pass, but the standard code is typical for the "
            f"external bypass-conductance statistic (upper-tail p={round_float(p_value)})."
        )

    ordered_values = sorted(values)
    emit(
        status,
        n_disconnected_fibers=observed_disconnected_count,
        gate_nonzero_variance=gate_nonzero_variance,
        gate_multi_orbit=gate_multi_orbit,
        omega_size_or_bound=len(states),
        T_obs=round_float(observed_t),
        p_value=round_float(p_value),
        null_method="exact_enumeration",
        null_seed=NULL_SEED,
        null_draws=NULL_DRAWS,
        conditions_out=["e_in", "box", "wobble", "edge_margins", "boundary_degrees", "component_structure"],
        not_tailored_to_named_fiber=True,
        checks=checks,
        reason=reason,
        threshold={"upper_tail_alpha": EXTREME_ALPHA},
        lower_tail_p_value=round_float(lower_p_value),
        null_summary={
            "min": round_float(ordered_values[0]),
            "mean": round_float(mean),
            "variance": round_float(variance),
            "median": round_float(ordered_values[len(ordered_values) // 2]),
            "max": round_float(ordered_values[-1]),
            "ge_observed": upper_count,
            "le_observed": lower_count,
            "distinct_T_values": distinct_values,
            "distinct_external_shortest_audits": distinct_audits,
        },
        observed_external_shortest_audit=[
            {"d_ext": distance, "N_ext": count}
            for distance, count in observed_audit
        ],
        disconnected_fiber_count_multiset=dict(sorted(Counter(disconnected_counts).items())),
        observed_component_structure_counts={
            str(signature): count
            for signature, count in sorted(Counter(item[2] for item in observed_full_signature).items())
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

#!/usr/bin/env python3
"""Fibonacci-cube versus codon-family graph-isomorphism test.

This experiment compares the abstract six-dimensional Fibonacci cube Gamma_6
with quotient graphs obtained from the standard genetic code.  It uses only
label-free graph invariants, so no codon-coordinate convention enters the
verdict path.
"""
from __future__ import annotations

from collections import Counter
from itertools import combinations, product
import json
import sys


EXPERIMENT_ID = "fibcube_codonfamily_graphiso_test"
CLAIM_ID = "bridge.window6_codon_q6.fibcube_codonfamily_graphiso_test"

BASES = ("U", "C", "A", "G")

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


def check_row(name: str, ok: bool, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": ok, "observed": observed, "expected": expected}


def hamming_distance(left: tuple[int, ...] | str, right: tuple[int, ...] | str) -> int:
    return sum(1 for a, b in zip(left, right) if a != b)


def codon_order() -> list[str]:
    return ["".join(chars) for chars in product(BASES, repeat=3)]


def no_adjacent_ones(word: tuple[int, ...]) -> bool:
    return all(not (word[index] and word[index + 1]) for index in range(len(word) - 1))


def gamma6_graph() -> tuple[list[str], set[tuple[int, int]]]:
    vertices = [
        "".join(str(bit) for bit in word)
        for word in product((0, 1), repeat=6)
        if no_adjacent_ones(tuple(word))
    ]
    edges = set()
    for left, right in combinations(range(len(vertices)), 2):
        if hamming_distance(vertices[left], vertices[right]) == 1:
            edges.add((left, right))
    return vertices, edges


def codon_family_graph(include_stop: bool) -> tuple[list[str], set[tuple[int, int]], dict[str, int]]:
    codons = [
        codon
        for codon in codon_order()
        if include_stop or CODON_TO_FAMILY[codon] != "Stop"
    ]
    families = sorted({CODON_TO_FAMILY[codon] for codon in codons})
    family_index = {family: index for index, family in enumerate(families)}
    codon_family_edges = 0
    edges: set[tuple[int, int]] = set()
    for left, right in combinations(codons, 2):
        if hamming_distance(left, right) != 1:
            continue
        left_family = CODON_TO_FAMILY[left]
        right_family = CODON_TO_FAMILY[right]
        if left_family == right_family:
            continue
        codon_family_edges += 1
        a = family_index[left_family]
        b = family_index[right_family]
        edges.add((a, b) if a < b else (b, a))
    metadata = {
        "codons": len(codons),
        "codon_level_between_family_hamming1_edges": codon_family_edges,
    }
    return families, edges, metadata


def adjacency_masks(vertex_count: int, edges: set[tuple[int, int]]) -> list[int]:
    masks = [0] * vertex_count
    for left, right in edges:
        masks[left] |= 1 << right
        masks[right] |= 1 << left
    return masks


def degree_sequence(masks: list[int]) -> list[int]:
    return sorted(mask.bit_count() for mask in masks)


def matrix_from_masks(masks: list[int]) -> list[list[int]]:
    n = len(masks)
    return [[1 if (masks[row] >> col) & 1 else 0 for col in range(n)] for row in range(n)]


def matmul(left: list[list[int]], right: list[list[int]]) -> list[list[int]]:
    n = len(left)
    out = [[0] * n for _ in range(n)]
    for row in range(n):
        out_row = out[row]
        for mid in range(n):
            value = left[row][mid]
            if value == 0:
                continue
            right_row = right[mid]
            for col in range(n):
                out_row[col] += value * right_row[col]
    return out


def spectral_moments(masks: list[int], max_power: int = 6) -> list[int]:
    matrix = matrix_from_masks(masks)
    n = len(matrix)
    power = [[1 if row == col else 0 for col in range(n)] for row in range(n)]
    moments = []
    for _ in range(max_power):
        power = matmul(power, matrix)
        moments.append(sum(power[index][index] for index in range(n)))
    return moments


def triangle_count(masks: list[int]) -> int:
    n = len(masks)
    triangles = 0
    for a in range(n):
        for b in range(a + 1, n):
            if not ((masks[a] >> b) & 1):
                continue
            common = masks[a] & masks[b]
            for c in range(b + 1, n):
                if (common >> c) & 1:
                    triangles += 1
    return triangles


def two_step_summary(masks: list[int]) -> dict[str, object]:
    n = len(masks)
    counts: Counter[int] = Counter()
    row_sums = []
    for left in range(n):
        row_sum = 0
        for right in range(n):
            value = (masks[left] & masks[right]).bit_count()
            if left != right:
                counts[value] += 1
            row_sum += value
        row_sums.append(row_sum)
    return {
        "offdiagonal_count_histogram": {str(key): counts[key] for key in sorted(counts)},
        "sorted_row_sums": sorted(row_sums),
    }


def graph_summary(
    name: str,
    vertices: list[str],
    edges: set[tuple[int, int]],
    metadata: dict[str, int] | None = None,
) -> dict[str, object]:
    masks = adjacency_masks(len(vertices), edges)
    summary: dict[str, object] = {
        "name": name,
        "vertices": len(vertices),
        "edges": len(edges),
        "degseq": degree_sequence(masks),
        "triangle_count": triangle_count(masks),
        "spectral_moments_1_to_6": spectral_moments(masks),
        "two_step_summary": two_step_summary(masks),
    }
    if metadata:
        summary.update(metadata)
    return summary


def first_mismatch(left: dict[str, object], right: dict[str, object]) -> str | None:
    for key in (
        "vertices",
        "edges",
        "degseq",
        "triangle_count",
        "spectral_moments_1_to_6",
        "two_step_summary",
    ):
        if left[key] != right[key]:
            return key
    return None


def comparison_row(gamma: dict[str, object], family: dict[str, object]) -> dict[str, object]:
    mismatch = first_mismatch(gamma, family)
    return {
        "family_graph": family["name"],
        "necessary_invariants_match": mismatch is None,
        "first_mismatch": mismatch,
        "gamma_observed": None if mismatch is None else gamma[mismatch],
        "family_observed": None if mismatch is None else family[mismatch],
    }


def main() -> None:
    gamma_vertices, gamma_edges = gamma6_graph()
    families_with_stop, edges_with_stop, metadata_with_stop = codon_family_graph(include_stop=True)
    sense_families, sense_edges, sense_metadata = codon_family_graph(include_stop=False)

    gamma = graph_summary("gamma6_no_adjacent_ones", gamma_vertices, gamma_edges)
    family_variants = [
        graph_summary(
            "standard_code_21_families_including_stop",
            families_with_stop,
            edges_with_stop,
            metadata_with_stop,
        ),
        graph_summary(
            "standard_code_20_sense_families_excluding_stop",
            sense_families,
            sense_edges,
            sense_metadata,
        ),
    ]
    comparisons = [comparison_row(gamma, variant) for variant in family_variants]
    decisive = next((row for row in comparisons if row["first_mismatch"] is not None), None)
    all_refuted = all(not row["necessary_invariants_match"] for row in comparisons)

    checks = [
        check_row("gamma6_vertex_count", gamma["vertices"] == 21, gamma["vertices"], 21),
        check_row("standard_code_codon_count", len(codon_order()) == 64, len(codon_order()), 64),
        check_row(
            "standard_code_family_count_including_stop",
            len(families_with_stop) == 21,
            len(families_with_stop),
            21,
        ),
        check_row(
            "standard_code_sense_family_count",
            len(sense_families) == 20,
            len(sense_families),
            20,
        ),
        check_row(
            "all_tested_family_graphs_fail_necessary_iso_invariants",
            all_refuted,
            [row["first_mismatch"] for row in comparisons],
            "no None entries",
        ),
    ]

    if not all(row["ok"] for row in checks):
        emit(
            "needs_derivation",
            gamma6_vertices=gamma["vertices"],
            gamma6_edges=gamma["edges"],
            gamma6_degseq=gamma["degseq"],
            family_graph_variants=family_variants,
            decisive_invariant=None,
            comparisons=comparisons,
            checks=checks,
            reason="Internal finite-enumeration checks did not all pass.",
        )

    if all_refuted:
        primary = comparisons[0]
        emit(
            "refuted",
            gamma6_vertices=gamma["vertices"],
            gamma6_edges=gamma["edges"],
            gamma6_degseq=gamma["degseq"],
            gamma6_summary=gamma,
            family_graph_variants=family_variants,
            decisive_invariant={
                "variant": primary["family_graph"],
                "name": primary["first_mismatch"],
                "gamma_observed": primary["gamma_observed"],
                "family_observed": primary["family_observed"],
            },
            comparisons=comparisons,
            checks=checks,
            reason=(
                "The convention-free graph-isomorphism route is closed: Gamma_6 "
                "and the codon-family adjacency graph fail necessary abstract-graph "
                "isomorphism invariants.  The 21-to-21 match is a graph-level "
                "coincidence rather than forcing evidence."
            ),
        )

    emit(
        "needs_derivation",
        gamma6_vertices=gamma["vertices"],
        gamma6_edges=gamma["edges"],
        gamma6_degseq=gamma["degseq"],
        gamma6_summary=gamma,
        family_graph_variants=family_variants,
        decisive_invariant=None,
        comparisons=comparisons,
        checks=checks,
        reason=(
            "Cheap necessary invariants did not refute every tested family graph; "
            "a full graph-isomorphism and canonicity analysis would be required."
        ),
    )


if __name__ == "__main__":
    main()

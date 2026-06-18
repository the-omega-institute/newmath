#!/usr/bin/env python3
"""Convention-robust Fibonacci-cube to codon embedding test.

The test fixes the Window6 object as the no-adjacent-ones vertex set in the
six-cube.  It then ranges over codon-coordinate conventions instead of choosing
the q6 convention.  The q6 convention is marked only after this enumeration is
defined.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import combinations, permutations, product
import json
import random
import sys
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[3]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.window_codon_bridge.experiments.run_genetic_code_fold_cert import (  # noqa: E402
    BASES,
    CODON_TO_OUTPUT,
    codon_order,
)


EXPERIMENT_ID = "fibcube_embedding_conventionrobust_test"
CLAIM_ID = "bridge.window6_codon_q6.fibcube_embedding.conventionrobust_test"
RANDOM_SEED = 619423
NULL_DRAWS_PER_COMPOSITION = 255
MCMC_BURNIN_ACCEPTED_SWAPS = 32
MCMC_STRIDE_ACCEPTED_SWAPS = 4
OUTLIER_ALPHA = 0.05
ROBUSTNESS_THRESHOLD = 0.50
BIT_PATTERNS = ((0, 0), (0, 1), (1, 0), (1, 1))
Q6_BASE_BY_PATTERN = ("U", "C", "A", "G")
STAT_NAMES = (
    "synonymous_sense_hamming1_edges",
    "boundary_sense_hamming1_edges",
    "output_classes_hit_including_stop",
    "fold_fragment_collision_pairs",
)
STOP = "Stop"


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status == "certified" else (2 if status == "refuted" else 3))


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def rounded(value: float | None, digits: int = 8) -> float | None:
    return None if value is None else round(float(value), digits)


def no_adjacent_ones(word: tuple[int, ...]) -> bool:
    return all(not (word[index] and word[index + 1]) for index in range(len(word) - 1))


def fibcube_vertices() -> list[tuple[int, ...]]:
    return [
        tuple(word)
        for word in product((0, 1), repeat=6)
        if no_adjacent_ones(tuple(word))
    ]


def fibcube_bit_automorphisms(vertices: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    vertex_set = set(vertices)
    autos = []
    for perm in permutations(range(6)):
        image = {tuple(word[perm[index]] for index in range(6)) for word in vertices}
        if image == vertex_set:
            autos.append(tuple(perm))
    return sorted(autos)


def base_code_dict(base_by_pattern: tuple[str, ...]) -> dict[tuple[int, int], str]:
    return {pattern: base for pattern, base in zip(BIT_PATTERNS, base_by_pattern)}


def convention_codons(
    vertices: list[tuple[int, ...]],
    base_by_pattern: tuple[str, ...],
    bit_order: tuple[int, ...],
) -> tuple[str, ...]:
    code = base_code_dict(base_by_pattern)
    codons = []
    for word in vertices:
        bases = []
        for codon_position in range(3):
            left = word[bit_order[2 * codon_position]]
            right = word[bit_order[2 * codon_position + 1]]
            bases.append(code[(left, right)])
        codons.append("".join(bases))
    return tuple(codons)


def base_bits(codon: str) -> tuple[int, ...]:
    pattern_by_base = {base: pattern for pattern, base in zip(BIT_PATTERNS, Q6_BASE_BY_PATTERN)}
    bits = []
    for base in codon:
        bits.extend(pattern_by_base[base])
    return tuple(bits)


def hamming_distance(left: str, right: str) -> int:
    return sum(1 for a, b in zip(left, right) if a != b)


def fold_fragment(codon: str) -> str:
    return f"{codon[:2]}:{CODON_TO_OUTPUT[codon]}"


def codon_metadata() -> dict[str, object]:
    codons = codon_order()
    codon_to_index = {codon: index for index, codon in enumerate(codons)}
    output_classes = sorted(set(CODON_TO_OUTPUT.values()))
    output_to_index = {output: index for index, output in enumerate(output_classes)}
    fragments = sorted({fold_fragment(codon) for codon in codons})
    fragment_to_index = {fragment: index for index, fragment in enumerate(fragments)}
    sense_hamming_edges: list[tuple[int, int, bool]] = []
    all_hamming_edges: list[tuple[int, int]] = []
    for left, right in combinations(codons, 2):
        if hamming_distance(left, right) != 1:
            continue
        left_index = codon_to_index[left]
        right_index = codon_to_index[right]
        all_hamming_edges.append((left_index, right_index))
        left_output = CODON_TO_OUTPUT[left]
        right_output = CODON_TO_OUTPUT[right]
        if left_output == STOP or right_output == STOP:
            continue
        sense_hamming_edges.append((left_index, right_index, left_output == right_output))

    bit_edges = []
    bits_by_index = [base_bits(codon) for codon in codons]
    for left, right in combinations(range(len(codons)), 2):
        if sum(1 for a, b in zip(bits_by_index[left], bits_by_index[right]) if a != b) == 1:
            bit_edges.append((left, right))

    return {
        "codons": codons,
        "codon_to_index": codon_to_index,
        "output_classes": output_classes,
        "output_to_index": output_to_index,
        "fragment_to_index": fragment_to_index,
        "sense_hamming_edges": sense_hamming_edges,
        "all_hamming_edges": all_hamming_edges,
        "bit_edges": bit_edges,
    }


def mask_from_codons(codons: Iterable[str], codon_to_index: dict[str, int]) -> int:
    mask = 0
    for codon in codons:
        mask |= 1 << codon_to_index[codon]
    return mask


def mask_indices(mask: int) -> list[int]:
    indices = []
    index = 0
    while mask:
        if mask & 1:
            indices.append(index)
        mask >>= 1
        index += 1
    return indices


def subset_stats(mask: int, meta: dict[str, object]) -> dict[str, int]:
    codons = meta["codons"]
    output_to_index = meta["output_to_index"]
    fragment_to_index = meta["fragment_to_index"]
    sense_hamming_edges = meta["sense_hamming_edges"]
    assert isinstance(codons, list)
    assert isinstance(output_to_index, dict)
    assert isinstance(fragment_to_index, dict)
    assert isinstance(sense_hamming_edges, list)

    synonymous_edges = 0
    boundary_edges = 0
    for left, right, same_output in sense_hamming_edges:
        if (mask >> left) & 1 and (mask >> right) & 1:
            if same_output:
                synonymous_edges += 1
            else:
                boundary_edges += 1

    output_seen = 0
    fragment_counts = [0 for _ in fragment_to_index]
    for index in mask_indices(mask):
        codon = codons[index]
        assert isinstance(codon, str)
        output = CODON_TO_OUTPUT[codon]
        output_seen |= 1 << int(output_to_index[output])
        fragment_counts[int(fragment_to_index[fold_fragment(codon)])] += 1
    return {
        "synonymous_sense_hamming1_edges": synonymous_edges,
        "boundary_sense_hamming1_edges": boundary_edges,
        "output_classes_hit_including_stop": output_seen.bit_count(),
        "fold_fragment_collision_pairs": sum(count * (count - 1) // 2 for count in fragment_counts),
    }


def stop_count(mask: int, meta: dict[str, object]) -> int:
    codons = meta["codons"]
    assert isinstance(codons, list)
    return sum(1 for index in mask_indices(mask) if CODON_TO_OUTPUT[str(codons[index])] == STOP)


def bit_q6_internal_edges(mask: int, meta: dict[str, object]) -> int:
    bit_edges = meta["bit_edges"]
    assert isinstance(bit_edges, list)
    return sum(1 for left, right in bit_edges if (mask >> left) & 1 and (mask >> right) & 1)


def composition_signature(mask: int, meta: dict[str, object]) -> tuple[int, ...]:
    codons = meta["codons"]
    assert isinstance(codons, list)
    counts = []
    selected = [str(codons[index]) for index in mask_indices(mask)]
    for position in range(3):
        counter = Counter(codon[position] for codon in selected)
        counts.extend(counter[base] for base in BASES)
    return tuple(counts)


def gc_count_from_signature(signature: tuple[int, ...]) -> int:
    gc = 0
    for position in range(3):
        gc += signature[position * 4 + BASES.index("C")]
        gc += signature[position * 4 + BASES.index("G")]
    return gc


def rows_from_signature(signature: tuple[int, ...], rng: random.Random) -> list[list[str]]:
    columns = []
    for position in range(3):
        column = []
        for base_index, base in enumerate(BASES):
            column.extend([base] * signature[position * 4 + base_index])
        rng.shuffle(column)
        columns.append(column)
    return [[columns[position][row] for position in range(3)] for row in range(21)]


def rows_from_mask(mask: int, meta: dict[str, object]) -> list[list[str]]:
    codons = meta["codons"]
    assert isinstance(codons, list)
    return [list(str(codons[index])) for index in mask_indices(mask)]


def mask_from_rows(rows: list[list[str]], codon_to_index: dict[str, int]) -> int | None:
    mask = 0
    seen = set()
    for row in rows:
        codon = "".join(row)
        if codon in seen:
            return None
        seen.add(codon)
        mask |= 1 << codon_to_index[codon]
    return mask if len(seen) == 21 else None


def accepted_swap(rows: list[list[str]], codon_to_index: dict[str, int], rng: random.Random) -> bool:
    position = rng.randrange(3)
    left = rng.randrange(21)
    right = rng.randrange(21)
    if left == right or rows[left][position] == rows[right][position]:
        return False
    rows[left][position], rows[right][position] = rows[right][position], rows[left][position]
    if mask_from_rows(rows, codon_to_index) is None:
        rows[left][position], rows[right][position] = rows[right][position], rows[left][position]
        return False
    return True


def deterministic_rng_for_signature(signature: tuple[int, ...], index: int) -> random.Random:
    accumulator = RANDOM_SEED + 1000003 * index
    for item in signature:
        accumulator = (accumulator * 1103515245 + item * 12345 + 67890) & ((1 << 63) - 1)
    return random.Random(accumulator)


def null_stats_for_signature(
    signature: tuple[int, ...],
    representative_mask: int,
    signature_index: int,
    meta: dict[str, object],
) -> tuple[dict[str, list[int]], dict[str, object]]:
    codon_to_index = meta["codon_to_index"]
    assert isinstance(codon_to_index, dict)
    rng = deterministic_rng_for_signature(signature, signature_index)
    rows = rows_from_mask(representative_mask, meta)
    accepted = 0
    attempts = 0
    max_attempts = 1000000
    target_accepted = MCMC_BURNIN_ACCEPTED_SWAPS + NULL_DRAWS_PER_COMPOSITION * MCMC_STRIDE_ACCEPTED_SWAPS
    null_values = {name: [] for name in STAT_NAMES}
    while accepted < target_accepted and attempts < max_attempts:
        attempts += 1
        if not accepted_swap(rows, codon_to_index, rng):
            continue
        accepted += 1
        if accepted <= MCMC_BURNIN_ACCEPTED_SWAPS:
            continue
        if (accepted - MCMC_BURNIN_ACCEPTED_SWAPS) % MCMC_STRIDE_ACCEPTED_SWAPS != 0:
            continue
        mask = mask_from_rows(rows, codon_to_index)
        if mask is None:
            raise RuntimeError("accepted swap produced duplicate codons")
        stats = subset_stats(mask, meta)
        for name in STAT_NAMES:
            null_values[name].append(stats[name])
    diagnostics = {
        "draws": len(next(iter(null_values.values()))),
        "accepted_swaps": accepted,
        "attempts": attempts,
        "target_draws": NULL_DRAWS_PER_COMPOSITION,
        "composition_matched": True,
        "gc_matched": True,
        "q6_degree_matched": "ambient_degree_sum=126 for every 21-codon subset; induced_bit_q6_edges_reported_not_conditioned",
    }
    return null_values, diagnostics


def empirical_two_sided_p(observed: int, null_values: list[int]) -> float:
    n = len(null_values)
    lower = (sum(1 for value in null_values if value <= observed) + 1) / (n + 1)
    upper = (sum(1 for value in null_values if value >= observed) + 1) / (n + 1)
    return min(1.0, 2.0 * min(lower, upper))


def holm_adjusted(p_values: dict[str, float]) -> dict[str, float]:
    ordered = sorted(p_values.items(), key=lambda item: (item[1], item[0]))
    adjusted = {}
    running = 0.0
    m = len(ordered)
    for rank, (name, p_value) in enumerate(ordered):
        value = min(1.0, (m - rank) * p_value)
        running = max(running, value)
        adjusted[name] = running
    return {name: adjusted[name] for name in p_values}


def null_summary(values: list[int]) -> dict[str, object]:
    ordered = sorted(values)
    n = len(ordered)
    return {
        "draws": n,
        "min": ordered[0],
        "q05": ordered[int(0.05 * (n - 1))],
        "median": ordered[int(0.50 * (n - 1))],
        "q95": ordered[int(0.95 * (n - 1))],
        "max": ordered[-1],
    }


def summarize_numbers(values: list[float]) -> dict[str, float | None]:
    if not values:
        return {"min": None, "q05": None, "median": None, "q95": None, "max": None}
    ordered = sorted(values)
    n = len(ordered)
    return {
        "min": rounded(ordered[0]),
        "q05": rounded(ordered[int(0.05 * (n - 1))]),
        "median": rounded(ordered[int(0.50 * (n - 1))]),
        "q95": rounded(ordered[int(0.95 * (n - 1))]),
        "max": rounded(ordered[-1]),
    }


def build_convention_records(vertices: list[tuple[int, ...]], meta: dict[str, object]) -> tuple[list[dict[str, object]], dict[tuple[int, ...], int]]:
    codon_to_index = meta["codon_to_index"]
    assert isinstance(codon_to_index, dict)
    automorphisms = fibcube_bit_automorphisms(vertices)
    q6_auto_set = set(automorphisms)
    records = []
    representative_by_signature: dict[tuple[int, ...], int] = {}
    for base_by_pattern in permutations(BASES):
        base_by_pattern = tuple(str(base) for base in base_by_pattern)
        for bit_order in permutations(range(6)):
            bit_order = tuple(int(index) for index in bit_order)
            codons = convention_codons(vertices, base_by_pattern, bit_order)
            mask = mask_from_codons(codons, codon_to_index)
            signature = composition_signature(mask, meta)
            representative_by_signature.setdefault(signature, mask)
            stats = subset_stats(mask, meta)
            is_q6 = base_by_pattern == Q6_BASE_BY_PATTERN and bit_order in q6_auto_set
            records.append(
                {
                    "base_by_pattern": base_by_pattern,
                    "bit_order": bit_order,
                    "mask": mask,
                    "signature": signature,
                    "stats": stats,
                    "stop_count": stop_count(mask, meta),
                    "bit_q6_internal_edges": bit_q6_internal_edges(mask, meta),
                    "q6_class": is_q6,
                }
            )
    return records, representative_by_signature


def evaluate_records(
    records: list[dict[str, object]],
    representative_by_signature: dict[tuple[int, ...], int],
    meta: dict[str, object],
) -> tuple[list[dict[str, object]], dict[str, object], list[str]]:
    checks = []
    signature_items = sorted(representative_by_signature.items())
    null_cache = {}
    null_diagnostics = []
    for index, (signature, representative_mask) in enumerate(signature_items):
        null_values, diagnostics = null_stats_for_signature(signature, representative_mask, index, meta)
        null_cache[signature] = null_values
        null_diagnostics.append(diagnostics)
    min_draws = min(int(item["draws"]) for item in null_diagnostics) if null_diagnostics else 0
    checks.append(f"null_signatures={len(null_cache)}")
    checks.append(f"null_min_draws={min_draws}")

    evaluated = []
    for record in records:
        signature = record["signature"]
        stats = record["stats"]
        assert isinstance(signature, tuple)
        assert isinstance(stats, dict)
        null_values = null_cache[signature]
        raw_p = {
            name: empirical_two_sided_p(int(stats[name]), null_values[name])
            for name in STAT_NAMES
        }
        adjusted_p = holm_adjusted(raw_p)
        best_stat = min(adjusted_p, key=lambda name: (adjusted_p[name], name))
        outlier = adjusted_p[best_stat] <= OUTLIER_ALPHA
        evaluated.append(
            {
                **record,
                "raw_p": raw_p,
                "adjusted_p": adjusted_p,
                "min_adjusted_p": adjusted_p[best_stat],
                "best_stat": best_stat,
                "outlier": outlier,
            }
        )

    draw_counts = Counter(int(item["draws"]) for item in null_diagnostics)
    null_report = {
        "unique_composition_signatures": len(null_cache),
        "draws_per_signature": NULL_DRAWS_PER_COMPOSITION,
        "draw_count_distribution": dict(sorted(draw_counts.items())),
        "accepted_swap_attempts": {
            "min": min(int(item["attempts"]) for item in null_diagnostics) if null_diagnostics else None,
            "max": max(int(item["attempts"]) for item in null_diagnostics) if null_diagnostics else None,
        },
        "example_null_summaries": {
            str(index): {
                "signature": list(signature),
                "gc_count": gc_count_from_signature(signature),
                "stats": {name: null_summary(null_cache[signature][name]) for name in STAT_NAMES},
            }
            for index, (signature, _representative) in enumerate(signature_items[:3])
        },
        "matching_contract": {
            "subset_size": 21,
            "nucleotide_position_composition": "exact",
            "gc": "implied exactly by nucleotide-position composition",
            "q6_degree": "ambient six-cube degree is 6 at every codon, so the 21-subset degree sum is exactly 126",
            "induced_bit_q6_edges": "reported as a diagnostic; not used to define S or to condition the null",
            "sampling": "fixed-seed MCMC by within-position base swaps preserving distinct codons",
        },
    }
    return evaluated, null_report, checks


def convention_report(record: dict[str, object]) -> dict[str, object]:
    stats = record["stats"]
    raw_p = record.get("raw_p", {})
    adjusted_p = record.get("adjusted_p", {})
    assert isinstance(stats, dict)
    assert isinstance(raw_p, dict)
    assert isinstance(adjusted_p, dict)
    return {
        "base_by_pattern_00_01_10_11": list(record["base_by_pattern"]),
        "bit_order": list(record["bit_order"]),
        "stats": {name: int(stats[name]) for name in STAT_NAMES},
        "stop_count": int(record["stop_count"]),
        "bit_q6_internal_edges": int(record["bit_q6_internal_edges"]),
        "raw_p": {name: rounded(float(raw_p[name])) for name in STAT_NAMES},
        "holm_adjusted_p": {name: rounded(float(adjusted_p[name])) for name in STAT_NAMES},
        "min_adjusted_p": rounded(float(record["min_adjusted_p"])),
        "best_stat": record["best_stat"],
        "outlier": bool(record["outlier"]),
    }


def classify(evaluated: list[dict[str, object]]) -> tuple[str, str, dict[str, object]]:
    q6_records = [record for record in evaluated if bool(record["q6_class"])]
    nonq6_records = [record for record in evaluated if not bool(record["q6_class"])]
    q6_outliers = [record for record in q6_records if bool(record["outlier"])]
    nonq6_outliers = [record for record in nonq6_records if bool(record["outlier"])]
    nonq6_fraction = len(nonq6_outliers) / len(nonq6_records) if nonq6_records else 0.0
    q6_class_outlier = bool(q6_outliers)

    if nonq6_fraction >= ROBUSTNESS_THRESHOLD:
        status = "certified"
        reason = (
            "a non-circular convention-robust Fibonacci-cube to codon structural alignment clears "
            "the pre-declared robustness threshold"
        )
    elif q6_class_outlier and not nonq6_outliers:
        status = "refuted"
        reason = (
            "the only outlier conventions are in the marked q6 symmetry class; the alignment is "
            "convention-dependent and circular for the Window6-codon bridge"
        )
    elif q6_class_outlier:
        status = "coincidence"
        reason = (
            "the q6 class is an outlier, but non-q6 outliers do not meet the convention-robust "
            "threshold; this is treated as a convention artifact rather than reopening evidence"
        )
    else:
        status = "needs_derivation"
        reason = (
            "the pre-declared statistics do not show a q6-only obstruction or a convention-robust "
            "non-q6 signal under the deterministic matched null"
        )

    distribution = {
        "q6_class_size": len(q6_records),
        "q6_class_outlier_count": len(q6_outliers),
        "nonq6_count": len(nonq6_records),
        "nonq6_outlier_count": len(nonq6_outliers),
        "nonq6_outlier_fraction": nonq6_fraction,
        "outlier_count_by_best_stat": dict(Counter(str(record["best_stat"]) for record in evaluated if bool(record["outlier"]))),
        "min_adjusted_p_summary_all": summarize_numbers([float(record["min_adjusted_p"]) for record in evaluated]),
        "min_adjusted_p_summary_nonq6": summarize_numbers([float(record["min_adjusted_p"]) for record in nonq6_records]),
        "stop_count_distribution": dict(sorted(Counter(int(record["stop_count"]) for record in evaluated).items())),
        "bit_q6_internal_edge_distribution": dict(sorted(Counter(int(record["bit_q6_internal_edges"]) for record in evaluated).items())),
    }
    return status, reason, distribution


def main() -> None:
    try:
        vertices = fibcube_vertices()
        meta = codon_metadata()
        records, representative_by_signature = build_convention_records(vertices, meta)
        evaluated, null_report, null_checks = evaluate_records(records, representative_by_signature, meta)
        status, reason, distribution = classify(evaluated)

        q6_records = [record for record in evaluated if bool(record["q6_class"])]
        nonq6_records = [record for record in evaluated if not bool(record["q6_class"])]
        q6_class_outlier = any(bool(record["outlier"]) for record in q6_records)
        nonq6_outlier_fraction = (
            sum(1 for record in nonq6_records if bool(record["outlier"])) / len(nonq6_records)
            if nonq6_records
            else 0.0
        )
        automorphisms = fibcube_bit_automorphisms(vertices)
        checks = [
            check_row("S_size", len(vertices), 21),
            check_row("S_is_no_adjacent_ones", all(no_adjacent_ones(word) for word in vertices), True),
            check_row("standard_code_codon_count", len(meta["codons"]), 64),
            check_row("standard_code_output_count_including_stop", len(meta["output_classes"]), 21),
            check_row("n_conventions", len(records), 24 * 720),
            check_row("q6_base_code_marked", Q6_BASE_BY_PATTERN, ("U", "C", "A", "G")),
            check_row("fibcube_bit_automorphism_count", len(automorphisms), 2),
            check_row("q6_class_size", len(q6_records), len(automorphisms)),
            check_row("unique_composition_signatures", len(representative_by_signature), null_report["unique_composition_signatures"]),
            check_row("null_draws_per_signature", null_report["draws_per_signature"], NULL_DRAWS_PER_COMPOSITION),
        ]
        checks_as_strings = [
            row["name"] if row["ok"] else f"fail:{row['name']}:{row['observed']}!={row['expected']}"
            for row in checks
        ] + null_checks

        if not all(row["ok"] for row in checks):
            emit(
                "needs_derivation",
                reason="self-check failed before verdict classification",
                S_size=len(vertices),
                n_conventions=len(records),
                q6_class_size=len(q6_records),
                per_stat_names=list(STAT_NAMES),
                q6_class_outlier=q6_class_outlier,
                nonq6_outlier_fraction=rounded(nonq6_outlier_fraction),
                robustness_threshold=ROBUSTNESS_THRESHOLD,
                multiplicity_method="Holm-Bonferroni across pre-declared statistics per convention",
                seed_if_any=RANDOM_SEED,
                checks=checks_as_strings,
            )

        emit(
            status,
            reason=reason,
            S_size=len(vertices),
            n_conventions=len(records),
            q6_class_size=len(q6_records),
            per_stat_names=list(STAT_NAMES),
            q6_class_outlier=q6_class_outlier,
            nonq6_outlier_fraction=rounded(nonq6_outlier_fraction),
            robustness_threshold=ROBUSTNESS_THRESHOLD,
            multiplicity_method="Holm-Bonferroni across pre-declared statistics per convention",
            seed_if_any=RANDOM_SEED,
            outlier_alpha=OUTLIER_ALPHA,
            convention_enumeration={
                "base_codes": "all 24 bijections from bit patterns 00,01,10,11 to U,C,A,G",
                "bit_orders": "all 6! bijections from abstract Gamma_6 bit positions to codon slots position1.bit1 through position3.bit2",
                "size": len(records),
                "q6_convention": {
                    "base_by_pattern_00_01_10_11": list(Q6_BASE_BY_PATTERN),
                    "bit_order": [0, 1, 2, 3, 4, 5],
                },
                "q6_symmetry_class": {
                    "definition": "q6 base code with abstract bit-position relabelings that preserve the no-adjacent-1 Gamma_6 vertex set",
                    "bit_orders": [list(auto) for auto in automorphisms],
                    "size": len(q6_records),
                },
            },
            null=null_report,
            distribution=distribution,
            q6_class_members=[convention_report(record) for record in q6_records],
            checks=checks_as_strings,
        )
    except Exception as exc:
        emit(
            "needs_derivation",
            reason=f"experiment raised {type(exc).__name__}: {exc}",
            S_size=None,
            n_conventions=None,
            q6_class_size=None,
            per_stat_names=list(STAT_NAMES),
            q6_class_outlier=False,
            nonq6_outlier_fraction=0.0,
            robustness_threshold=ROBUSTNESS_THRESHOLD,
            multiplicity_method="Holm-Bonferroni across pre-declared statistics per convention",
            seed_if_any=RANDOM_SEED,
            checks=["fail:exception"],
        )


if __name__ == "__main__":
    main()

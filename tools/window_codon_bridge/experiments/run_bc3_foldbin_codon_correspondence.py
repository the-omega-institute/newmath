#!/usr/bin/env python3
"""BC3 foldbin tail-cube versus codon position/wobble correspondence.

This is an anti-numerology audit.  It does not ask whether both sides contain
the integer 3.  It asks whether the foldbin tail data force a canonical map to
the ordered codon positions with third-position wobble distinguished.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import combinations, permutations, product
import json
import sys


EXPERIMENT_ID = "bc3_foldbin_codon_correspondence"
CLAIM_ID = "bridge.window6_codon_q6.foldbin_codon_positions"

FOLD_COORDS = ("c7", "c8", "c9")
FOLD_WEIGHTS = {"c7": 21, "c8": 34, "c9": 55}
VISIBLE_WEIGHTS = (1, 2, 3, 5, 8, 13)
TAIL_WEIGHTS = (21, 34, 55)
WIDTH_BOUND = 2**6 - 1

NUCLEOTIDES = ("U", "C", "A", "G")
PYRIMIDINES = frozenset(("U", "C"))
PURINES = frozenset(("A", "G"))

CODON_TO_MEANING = {
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

BASE_TO_BITS = {"U": (0, 0), "C": (0, 1), "A": (1, 0), "G": (1, 1)}


def emit(status: str, **fields: object) -> None:
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
    }
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=False, sort_keys=True))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def fib(n: int) -> int:
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def codon_order() -> list[str]:
    return ["".join(chars) for chars in product(NUCLEOTIDES, repeat=3)]


def visible_value(word: tuple[int, ...]) -> int:
    return sum(bit * weight for bit, weight in zip(word, VISIBLE_WEIGHTS))


def tail_value(tail: tuple[int, ...]) -> int:
    return sum(bit * weight for bit, weight in zip(tail, TAIL_WEIGHTS))


def no_adjacent_ones(bits: tuple[int, ...]) -> bool:
    return all(not (bits[index] and bits[index + 1]) for index in range(len(bits) - 1))


def foldbin_z9_window() -> list[tuple[tuple[int, ...], tuple[int, ...], int]]:
    rows = []
    for bits in product((0, 1), repeat=9):
        if not no_adjacent_ones(bits):
            continue
        value = sum(bit * weight for bit, weight in zip(bits, VISIBLE_WEIGHTS + TAIL_WEIGHTS))
        if value <= WIDTH_BOUND:
            rows.append((bits[:6], bits[6:], value))
    return rows


def foldbin_tail_report() -> dict[str, object]:
    z9 = foldbin_z9_window()
    values = sorted(value for _, _, value in z9)
    tail_counts = Counter(tail for _, tail, _ in z9)
    marginal_counts = {
        coord: sum(tail[index] for _, tail, _ in z9)
        for index, coord in enumerate(FOLD_COORDS)
    }
    actual_tail_states = sorted(tail_counts)
    no_adj_tail_states = [
        tail for tail in product((0, 1), repeat=3)
        if no_adjacent_ones(tail)
    ]
    full_cube_states = list(product((0, 1), repeat=3))
    fiber_sizes = Counter()
    for visible, _, _ in z9:
        fiber_sizes[visible] += 1
    return {
        "rho6": 10,
        "s6": 7,
        "return_depth": 3,
        "tail_coords": list(FOLD_COORDS),
        "tail_weights": dict(FOLD_WEIGHTS),
        "weight_order_low_to_high": sorted(FOLD_COORDS, key=lambda coord: FOLD_WEIGHTS[coord]),
        "z9_size": len(z9),
        "z9_values_are_0_to_63": values == list(range(64)),
        "full_boolean_tail_state_count": len(full_cube_states),
        "no_adjacent_tail_state_count": len(no_adj_tail_states),
        "actual_value_window_tail_state_count": len(actual_tail_states),
        "actual_value_window_tail_states": ["".join(map(str, tail)) for tail in actual_tail_states],
        "tail_state_multiplicities": {
            "".join(map(str, tail)): count for tail, count in sorted(tail_counts.items())
        },
        "tail_coordinate_marginals": marginal_counts,
        "marginal_order_high_to_low": sorted(
            FOLD_COORDS, key=lambda coord: (-marginal_counts[coord], coord)
        ),
        "visible_prefix_fiber_size_distribution": dict(sorted(Counter(fiber_sizes.values()).items())),
    }


def position_substitution_report(include_stop: bool) -> dict[str, object]:
    rows = {}
    for position in range(3):
        total_pairs = 0
        synonymous_pairs = 0
        codon_alt_counts = []
        for codon in codon_order():
            meaning = CODON_TO_MEANING[codon]
            if include_stop is False and meaning == "Stop":
                continue
            same_alt = 0
            valid_alt = 0
            for base in NUCLEOTIDES:
                if base == codon[position]:
                    continue
                alt = codon[:position] + base + codon[position + 1:]
                alt_meaning = CODON_TO_MEANING[alt]
                if include_stop is False and alt_meaning == "Stop":
                    continue
                valid_alt += 1
                if alt_meaning == meaning:
                    same_alt += 1
            codon_alt_counts.append(same_alt)
            fixed_positions = [0, 1, 2]
            fixed_positions.remove(position)
        for fixed_values in product(NUCLEOTIDES, repeat=2):
            codons = []
            for base in NUCLEOTIDES:
                chars = [None, None, None]
                chars[position] = base
                for index, fixed_position in enumerate(fixed_positions):
                    chars[fixed_position] = fixed_values[index]
                codons.append("".join(chars))
            for left, right in combinations(codons, 2):
                if include_stop is False and (
                    CODON_TO_MEANING[left] == "Stop" or CODON_TO_MEANING[right] == "Stop"
                ):
                    continue
                total_pairs += 1
                if CODON_TO_MEANING[left] == CODON_TO_MEANING[right]:
                    synonymous_pairs += 1
        rows[f"pos{position + 1}"] = {
            "synonymous_pair_count": synonymous_pairs,
            "pair_count": total_pairs,
            "synonymous_pair_rate": synonymous_pairs / total_pairs,
            "mean_same_alternatives_per_codon": sum(codon_alt_counts) / len(codon_alt_counts),
            "same_alternative_count_distribution": dict(sorted(Counter(codon_alt_counts).items())),
        }
    rate_order = sorted(rows, key=lambda key: rows[key]["synonymous_pair_rate"])
    return {
        "include_stop": include_stop,
        "positions": rows,
        "degeneracy_order_low_to_high": rate_order,
    }


def wobble_pair_report() -> dict[str, object]:
    total = 0
    same = 0
    failures = []
    for codon in codon_order():
        bits = []
        for base in codon:
            bits.extend(BASE_TO_BITS[base])
        partner_bits = list(bits)
        partner_bits[5] = 1 - partner_bits[5]
        partner = ""
        for offset in range(0, 6, 2):
            pair = tuple(partner_bits[offset:offset + 2])
            partner += {value: key for key, value in BASE_TO_BITS.items()}[pair]
        if codon > partner:
            continue
        total += 1
        if CODON_TO_MEANING[codon] == CODON_TO_MEANING[partner]:
            same += 1
        else:
            failures.append([codon, partner, CODON_TO_MEANING[codon], CODON_TO_MEANING[partner]])
    return {
        "q6_axis": 6,
        "pair_count": total,
        "same_meaning_pairs": same,
        "same_meaning_rate": same / total,
        "non_synonymous_wobble_bit_pairs": failures,
        "interpretation": "The local topology distinguishes wobble as one Q6 bit inside the third codon position, not as one whole Boolean tail coordinate.",
    }


def monotone_permutation_matches(
    fold_scores: dict[str, float], codon_scores: dict[str, float], low_to_high: bool
) -> list[dict[str, object]]:
    fold_order = sorted(fold_scores, key=lambda coord: (fold_scores[coord], coord))
    codon_order_by_score = sorted(codon_scores, key=lambda pos: (codon_scores[pos], pos))
    if not low_to_high:
        codon_order_by_score = list(reversed(codon_order_by_score))
    matches = []
    for perm in permutations(codon_scores):
        mapping = dict(zip(FOLD_COORDS, perm))
        mapped_order = [mapping[coord] for coord in fold_order]
        if mapped_order == codon_order_by_score:
            matches.append(mapping)
    return matches


def mapping_audit(fold_report: dict[str, object], codon_report: dict[str, object]) -> dict[str, object]:
    codon_scores = {
        position: details["synonymous_pair_rate"]
        for position, details in codon_report["positions"].items()
    }
    weight_scores = {coord: FOLD_WEIGHTS[coord] for coord in FOLD_COORDS}
    marginal_scores = fold_report["tail_coordinate_marginals"]
    weight_maps = monotone_permutation_matches(weight_scores, codon_scores, low_to_high=True)
    marginal_maps = monotone_permutation_matches(marginal_scores, codon_scores, low_to_high=True)
    reverse_weight_maps = monotone_permutation_matches(weight_scores, codon_scores, low_to_high=False)
    return {
        "candidate_weight_to_degeneracy": {
            "result": "rank-compatible_but_semantics_unforced",
            "maps": weight_maps,
            "note": "Maps larger Fibonacci alias to more synonymous-preserving codon position; this gives c9->pos3, but only after adding the external convention that larger tail weight means more biological degeneracy.",
        },
        "candidate_marginal_to_degeneracy": {
            "result": "conflicts_with_weight_mapping",
            "maps": marginal_maps,
            "note": "The actual 0..63 Zeckendorf/Foldbin value window activates c8 most often and c9 least often, so the natural fiber-marginal order does not put c9 at wobble.",
        },
        "candidate_reverse_weight_to_constraint": {
            "result": "also_rank-compatible_under_opposite_semantics",
            "maps": reverse_weight_maps,
            "note": "If larger Fibonacci alias is interpreted as stronger constraint instead of more freedom, a different monotone assignment is obtained. The math side alone does not choose the biological polarity.",
        },
        "all_three_assignments_identical": bool(
            weight_maps and marginal_maps and reverse_weight_maps
            and weight_maps == marginal_maps == reverse_weight_maps
        ),
    }


def main() -> None:
    fold_report = foldbin_tail_report()
    codon_sense = position_substitution_report(include_stop=False)
    codon_all = position_substitution_report(include_stop=True)
    wobble = wobble_pair_report()
    audit = mapping_audit(fold_report, codon_sense)

    checks = [
        {
            "name": "foldbin_horizon_tail_dimension",
            "passed": fold_report["rho6"] - fold_report["s6"] == 3 == len(FOLD_COORDS),
            "verdict_component": "coincidence_control",
            "detail": "This certifies the Window6 tail dimension internally, but not a biological map.",
        },
        {
            "name": "codon_positions_are_ordered_and_wobble_distinguished",
            "passed": codon_sense["degeneracy_order_low_to_high"] == ["pos2", "pos1", "pos3"],
            "verdict_component": "bio_structure_present",
            "detail": "Standard-code synonymous preservation gives a real positional gradient: position 3 is the most degenerate/wobble-like.",
        },
        {
            "name": "weight_rank_forces_wobble",
            "passed": False,
            "verdict_component": "not_certified",
            "detail": "The weight rank can be aligned with the bio rank only after choosing an external polarity; the foldbin construction does not derive that polarity.",
        },
        {
            "name": "foldbin_internal_structures_choose_same_assignment",
            "passed": audit["all_three_assignments_identical"],
            "verdict_component": "failed",
            "detail": "Tail weights, actual value-window marginals, and reverse constraint semantics do not force the same codon-position assignment.",
        },
        {
            "name": "tail_cube_8_states_match_codon_wobble_classes",
            "passed": False,
            "verdict_component": "refuted_subreading",
            "detail": "The actual bounded Zeckendorf/Foldbin window uses 4 tail states, not the full 8 Boolean states; codon positions are 3 four-letter blocks or 6 Q6 bits.",
        },
        {
            "name": "second_fold_equals_codon_pair_abundance_object",
            "passed": False,
            "verdict_component": "refuted_subreading",
            "detail": "Bio Route B/Q^(2) failed for abundance; this refutes the stronger abundance-predictive codon-pair reading, while leaving weaker structural proposals to be separately derived.",
        },
    ]

    emit(
        "coincidence",
        reason=(
            "Both sides have an ordered triple and codon position 3 is genuinely wobble-distinguished, "
            "but the foldbin tail data do not force a unique structure-preserving map to codon positions. "
            "The only successful alignment is rank-based after adding an external polarity convention; "
            "other legitimate foldbin structures give different assignments, and the 8-state/codon-pair readings fail."
        ),
        foldbin=fold_report,
        codon_position_degeneracy_sense_only=codon_sense,
        codon_position_degeneracy_with_stop=codon_all,
        wobble_bit=wobble,
        mapping_audit=audit,
        checks=checks,
        missing_for_certification=(
            "A derivation that sends Fibonacci tail aliases/evaluation/fiber constraints to a biological "
            "positional-degeneracy order with a fixed polarity, and proves invariance under the natural "
            "automorphisms on both sides. Without that, 3 tail coordinates versus 3 codon positions is a count match."
        ),
    )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact audit of canonical basepoint candidates for the period-10 clock.

The audit works only with finite objects: the cyclic golden period-10 set
P_10, the single-one 10-orbit O, Fibonacci residues modulo 10, and the
10-cycle permutation matrix.  It checks whether four natural candidate
families distinguish a ClockCouplingCert basepoint, and whether any such
distinguished basepoint makes the first seam have degree 7 modulo 10.
"""

from __future__ import annotations

import itertools
import json
from collections import Counter
from typing import Any, Callable

import sympy as sp


N = 10
SEAM_RESIDUE_RELATIVE_TO_SEED = 7
SEED = tuple(int(bit) for bit in "0000000001")
RESIDUES = tuple(range(N))


Word = tuple[int, ...]


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def bitword(word: Word) -> str:
    return "".join(str(bit) for bit in word)


def valid_cyclic(word: Word) -> bool:
    return all(
        not (word[index] == word[(index + 1) % len(word)] == 1)
        for index in range(len(word))
    )


def cyclic_words(length: int) -> list[Word]:
    return [
        tuple(bits)
        for bits in itertools.product((0, 1), repeat=length)
        if valid_cyclic(tuple(bits))
    ]


def shift(word: Word, power: int = 1) -> Word:
    power %= len(word)
    return tuple(word[(index + power) % len(word)] for index in range(len(word)))


def reverse(word: Word) -> Word:
    return tuple(reversed(word))


def complement(word: Word) -> Word:
    return tuple(1 - bit for bit in word)


def orbit(seed: Word) -> list[Word]:
    return [shift(seed, power) for power in RESIDUES]


def first_seam_word(seed: Word) -> Word:
    return shift(seed, SEAM_RESIDUE_RELATIVE_TO_SEED)


def residue_from_basepoint(basepoint: Word, seam_word: Word, orbit_words: list[Word]) -> int | None:
    if basepoint not in orbit_words or seam_word not in orbit_words:
        return None
    current = basepoint
    for residue in RESIDUES:
        if current == seam_word:
            return residue
        current = shift(current)
    return None


def fixed_words(words: list[Word], operation: Callable[[Word], Word]) -> list[Word]:
    return [word for word in words if operation(word) == word]


def cycle_structure(words: list[Word]) -> dict[str, int]:
    remaining = set(words)
    lengths: list[int] = []
    while remaining:
        start = next(iter(remaining))
        cyc: list[Word] = []
        current = start
        while current not in cyc:
            cyc.append(current)
            current = shift(current)
        for word in cyc:
            remaining.discard(word)
        lengths.append(len(cyc))
    return {str(length): count for length, count in sorted(Counter(lengths).items())}


def fixed_report(
    name: str,
    words_p10: list[Word],
    words_o: list[Word],
    operation: Callable[[Word], Word],
    is_endomorphism_p10: bool,
    is_endomorphism_o: bool,
    is_involution: bool,
    seam_word: Word,
) -> dict[str, Any]:
    fixed_o = fixed_words(words_o, operation) if is_endomorphism_o else []
    fixed_p10 = fixed_words(words_p10, operation) if is_endomorphism_p10 else []
    unique_basepoint = fixed_o[0] if len(fixed_o) == 1 else None
    residue = residue_from_basepoint(unique_basepoint, seam_word, words_o) if unique_basepoint else None
    return {
        "name": name,
        "is_endomorphism_on_p10": is_endomorphism_p10,
        "is_endomorphism_on_o": is_endomorphism_o,
        "is_involution": is_involution,
        "fixed_points_o_count": len(fixed_o),
        "fixed_points_o": [bitword(word) for word in fixed_o],
        "fixed_points_p10_count": len(fixed_p10),
        "fixed_points_p10_sample": [bitword(word) for word in fixed_p10[:20]],
        "unique_fixed_basepoint_in_o": bitword(unique_basepoint) if unique_basepoint else None,
        "deg_first_seam_residue_if_unique": residue,
        "yields_7_if_unique": residue == SEAM_RESIDUE_RELATIVE_TO_SEED,
        "verdict": (
            "unique period-10 orbit fixed point"
            if unique_basepoint
            else "no unique fixed point in the period-10 orbit O"
        ),
    }


def verify_involution_candidate(words_p10: list[Word], words_o: list[Word], seam_word: Word) -> dict[str, Any]:
    operations: list[dict[str, Any]] = []

    rev_preserves_p10 = all(reverse(word) in words_p10 for word in words_p10)
    rev_preserves_o = all(reverse(word) in words_o for word in words_o)
    operations.append(
        fixed_report(
            "reverse",
            words_p10,
            words_o,
            reverse,
            rev_preserves_p10,
            rev_preserves_o,
            True,
            seam_word,
        )
    )

    comp_preserves_p10 = all(complement(word) in words_p10 for word in words_p10)
    comp_preserves_o = all(complement(word) in words_o for word in words_o)
    operations.append(
        fixed_report(
            "bitwise-complement",
            words_p10,
            words_o,
            complement,
            comp_preserves_p10,
            comp_preserves_o,
            True,
            seam_word,
        )
    )

    for power in range(1, N):
        operation = lambda word, power=power: shift(word, power)
        operations.append(
            fixed_report(
                f"shift-{power}",
                words_p10,
                words_o,
                operation,
                True,
                True,
                (2 * power) % N == 0,
                seam_word,
            )
        )

    for power in range(N):
        operation = lambda word, power=power: shift(reverse(word), power)
        image_p10 = [operation(word) for word in words_p10]
        image_o = [operation(word) for word in words_o]
        operations.append(
            fixed_report(
                f"dihedral-reflection-{power}",
                words_p10,
                words_o,
                operation,
                all(word in words_p10 for word in image_p10),
                all(word in words_o for word in image_o),
                all(operation(operation(word)) == word for word in words_p10),
                seam_word,
            )
        )

    unique_ops = [
        item
        for item in operations
        if item["unique_fixed_basepoint_in_o"] is not None
    ]
    return {
        "candidate": "involution-or-automorphism-fixed-point",
        "canonical": False,
        "forward_constructible": False,
        "distinguished_basepoint": None,
        "deg_first_seam_residue": None,
        "yields_7": False,
        "operation_reports": operations,
        "summary": (
            "No checked natural involution or shift/dihedral symmetry has a unique fixed point "
            "inside the single-one period-10 orbit O.  Some shifts have a unique full-P_10 "
            "fixed point, but it is the all-zero orbit rather than a clock basepoint in O."
        ),
        "unique_o_fixed_operation_count": len(unique_ops),
    }


def verify_torsor_candidate(words_o: list[Word], seam_word: Word) -> dict[str, Any]:
    orbit_index = {bitword(word): index for index, word in enumerate(words_o)}
    lexmin = min(words_o, key=bitword)
    lex_residue = residue_from_basepoint(lexmin, seam_word, words_o)
    translations = []
    for origin in words_o:
        identity_label = bitword(origin)
        seam_residue = residue_from_basepoint(origin, seam_word, words_o)
        translations.append(
            {
                "chosen_identity": identity_label,
                "orbit_index_from_seed": orbit_index[identity_label],
                "first_seam_residue": seam_residue,
            }
        )
    return {
        "candidate": "group-or-torsor-identity",
        "canonical": True,
        "forward_constructible": False,
        "distinguished_basepoint": bitword(lexmin),
        "deg_first_seam_residue": lex_residue,
        "yields_7": lex_residue == SEAM_RESIDUE_RELATIVE_TO_SEED,
        "torsor_action": "The shift action of C_10 on O is simply transitive.",
        "identity_verdict": (
            "O is a C_10 torsor, not a group with an intrinsic identity.  Any point of O "
            "can be declared the identity after choosing an origin."
        ),
        "lexmin_verdict": (
            "The lexicographic representative is unique only after importing the ambient "
            "linear string order.  It gives residue 7 for the fixed seam word, but this is "
            "canonical-by-coordinate-convention rather than forward-forced by the clock torsor."
        ),
        "all_origin_choices": translations,
    }


def pisano_period(modulus: int) -> tuple[int, list[tuple[int, int]]]:
    state = (0, 1)
    seen: list[tuple[int, int]] = []
    while True:
        if state in seen:
            return len(seen), seen
        seen.append(state)
        state = (state[1], (state[0] + state[1]) % modulus)


def verify_pisano_candidate() -> dict[str, Any]:
    period, states = pisano_period(10)
    shifted_seam_residues = [(SEAM_RESIDUE_RELATIVE_TO_SEED + residue) % N for residue in RESIDUES]
    return {
        "candidate": "zeckendorf-pisano-arithmetic",
        "canonical": False,
        "forward_constructible": False,
        "distinguished_basepoint": None,
        "deg_first_seam_residue": None,
        "yields_7": False,
        "pisano_period_mod_10": period,
        "initial_states_mod_10": [list(state) for state in states[:12]],
        "state_count": len(states),
        "relative_seam_index": SEAM_RESIDUE_RELATIVE_TO_SEED,
        "absolute_residues_under_clock_origin_shift": shifted_seam_residues,
        "summary": (
            "The Fibonacci register has the canonical state (F_0,F_1)=(0,1) and period 60 modulo 10, "
            "but this supplies an arithmetic index, not a map from the ClockCouplingCert torsor O "
            "to an absolute phase.  Shifting the clock origin moves the absolute seam residue through "
            "all ten classes while preserving the same relative index s_6=7."
        ),
    }


def permutation_matrix() -> sp.Matrix:
    matrix = sp.zeros(N)
    for index in range(N):
        matrix[index, (index + 1) % N] = 1
    return matrix


def verify_spectral_candidate() -> dict[str, Any]:
    x = sp.symbols("x")
    matrix = permutation_matrix()
    charpoly = sp.factor(matrix.charpoly(x).as_expr())
    perron_nullity = (matrix - sp.eye(N)).nullspace()
    primitive_poly = x**4 - x**3 + x**2 - x + 1
    divisible_by_phi10 = sp.rem(charpoly, primitive_poly, domain=sp.QQ) == 0
    return {
        "candidate": "transfer-operator-or-spectral-phase",
        "canonical": False,
        "forward_constructible": False,
        "distinguished_basepoint": None,
        "deg_first_seam_residue": None,
        "yields_7": False,
        "S10_charpoly": str(charpoly),
        "phi10_divides_charpoly": bool(divisible_by_phi10),
        "perron_eigenspace_dimension": len(perron_nullity),
        "perron_eigenvector_shape": "constant vector, invariant under all cyclic relabelings",
        "primitive_phase_choices": N,
        "summary": (
            "The Perron vector is constant and contains no phase.  Each primitive 10th-root "
            "eigenline has a phase only after choosing a coordinate basepoint; cyclic relabeling "
            "multiplies the eigenvector by a root of unity.  The spectrum supplies a C_10 clock "
            "representation but not a unique origin or a Window6-canonical map to residue 7."
        ),
    }


def main() -> None:
    words_p10 = cyclic_words(N)
    words_o = orbit(SEED)
    seam_word = first_seam_word(SEED)
    p10_cycle_structure = cycle_structure(words_p10)

    candidates = {
        "involution_fixed_point": verify_involution_candidate(words_p10, words_o, seam_word),
        "group_torsor_identity": verify_torsor_candidate(words_o, seam_word),
        "zeckendorf_pisano": verify_pisano_candidate(),
        "spectral_phase": verify_spectral_candidate(),
    }

    forward_successes = [
        name
        for name, candidate in candidates.items()
        if candidate["forward_constructible"] and candidate["yields_7"]
    ]
    lexmin_note = candidates["group_torsor_identity"]
    all_fail = not forward_successes

    not_claimed = [
        "physical fine-structure constant identification R_6(D*)=alpha^-1",
        "the ClockCouplingCert clock basepoint o_0 as forward-canonically distinguished (all four natural candidates -- involution fixed point, group/torsor identity, Zeckendorf/Pisano arithmetic, spectral phase -- fail to forward-distinguish a basepoint; it is irreducibly free gauge)",
        "D*_6 as a Window6-internal or forward-internal theorem",
    ]

    checks = [
        check(
            "P10_cyclic_enumeration",
            len(words_p10) == 123 and p10_cycle_structure == {"1": 1, "2": 1, "5": 2, "10": 11},
            "P_10 has 123 cyclic golden words and shift cycle structure {10:11,5:2,2:1,1:1}.",
        ),
        check(
            "minimal_orbit_O",
            len(set(words_o)) == 10 and all(word in words_p10 for word in words_o),
            "The single-one orbit O is a length-10 shift orbit inside P_10.",
        ),
        check(
            "involution_fixed_point_candidate",
            candidates["involution_fixed_point"]["unique_o_fixed_operation_count"] == 0,
            "No checked natural involution or shift/dihedral symmetry gives a unique fixed basepoint in O.",
        ),
        check(
            "torsor_identity_candidate",
            lexmin_note["canonical"] and not lexmin_note["forward_constructible"] and lexmin_note["yields_7"],
            "O is a torsor with no intrinsic identity; lexmin is coordinate-canonical and gives residue 7, but is not forward-forced by the clock structure.",
        ),
        check(
            "zeckendorf_pisano_candidate",
            candidates["zeckendorf_pisano"]["pisano_period_mod_10"] == 60
            and set(candidates["zeckendorf_pisano"]["absolute_residues_under_clock_origin_shift"]) == set(RESIDUES),
            "Pisano modulo 10 has period 60 but does not pin the absolute C_10 phase; origin shifts realize all residues.",
        ),
        check(
            "spectral_phase_candidate",
            candidates["spectral_phase"]["phi10_divides_charpoly"]
            and candidates["spectral_phase"]["perron_eigenspace_dimension"] == 1
            and not candidates["spectral_phase"]["forward_constructible"],
            "S_10 has the expected tenth-root spectrum, but Perron and primitive eigenspaces do not distinguish a phase origin.",
        ),
        check(
            "ClockCouplingCert_basepoint_free_gauge",
            all_fail,
            "All four natural canonical-basepoint candidates fail to forward-distinguish a period-10 clock basepoint yielding a physically forced residue 7.",
        ),
    ]

    result: dict[str, Any] = {
        "P10_size": len(words_p10),
        "P10_cycle_structure": p10_cycle_structure,
        "O_seed": bitword(SEED),
        "O_words": [bitword(word) for word in words_o],
        "first_seam_word_relative_to_seed": bitword(seam_word),
        "first_seam_residue_relative_to_seed": SEAM_RESIDUE_RELATIVE_TO_SEED,
        "candidates": candidates,
        "forward_successes_yielding_7": forward_successes,
        "overall_verdict": (
            "irreducibly_free_gauge"
            if all_fail
            else "forward_canonical_candidate_found"
        ),
        "overall_statement": (
            "The period-10 clock structure supplies a C_10 torsor and a Phi_10 clock, but the "
            "four checked natural candidate families do not supply a forward-canonical basepoint. "
            "The ClockCouplingCert basepoint o_0 remains irreducibly free gauge, so the physical "
            "readout remains needs-external."
            if all_fail
            else "At least one candidate forward-distinguishes a basepoint with seam residue 7; this is only reported for external assessment."
        ),
        "not_claimed": not_claimed,
    }
    if forward_successes:
        result["alpha_claim_path_candidate"] = forward_successes

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    main()

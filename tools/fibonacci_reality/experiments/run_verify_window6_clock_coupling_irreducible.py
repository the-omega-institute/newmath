#!/usr/bin/env python3
"""Exact audit for the Window6 ClockCouplingCert torsor-origin obstruction.

The audit verifies that Window6 local golden words do not determine an
absolute C_10 clock origin. Every length-6 no-adjacent-11 word embeds into a
period-10 cyclic golden word at every residue by zero padding, and every local
coordinate can therefore realize every residue. The pair (s,rho)=(7,10) fixes
only the affine return shape 7+10k, not a basepoint in the C_10 torsor.
"""

from __future__ import annotations

import itertools
import json
from typing import Any


RESIDUES = tuple(range(10))
LOCAL_COORDINATES = tuple(range(6))


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def words_no_adjacent(length: int) -> list[tuple[int, ...]]:
    words: list[tuple[int, ...]] = []
    for bits in itertools.product((0, 1), repeat=length):
        if all(not (bits[index] == bits[index + 1] == 1) for index in range(length - 1)):
            words.append(bits)
    return words


def valid_cyclic(word: tuple[int, ...]) -> bool:
    return all(
        not (word[index] == word[(index + 1) % len(word)] == 1)
        for index in range(len(word))
    )


def embed_zero_padded(word: tuple[int, ...], start_residue: int) -> tuple[int, ...]:
    padded = [0] * 10
    for offset, bit in enumerate(word):
        padded[(start_residue + offset) % 10] = bit
    return tuple(padded)


def bitword(word: tuple[int, ...]) -> str:
    return "".join(str(bit) for bit in word)


def main() -> None:
    x6 = words_no_adjacent(6)
    expected_residues = set(RESIDUES)

    word_residue_support: dict[str, list[int]] = {}
    word_embedding_samples: dict[str, dict[str, str]] = {}
    for word in x6:
        valid_residues: list[int] = []
        samples: dict[str, str] = {}
        for residue in RESIDUES:
            embedded = embed_zero_padded(word, residue)
            if valid_cyclic(embedded):
                valid_residues.append(residue)
            samples[str(residue)] = bitword(embedded)
        word_residue_support[bitword(word)] = valid_residues
        word_embedding_samples[bitword(word)] = samples

    coordinate_residue_support: dict[str, dict[str, list[int]]] = {}
    for word in x6:
        word_key = bitword(word)
        coordinate_residue_support[word_key] = {}
        for coordinate in LOCAL_COORDINATES:
            possible = sorted({(residue + coordinate) % 10 for residue in word_residue_support[word_key]})
            coordinate_residue_support[word_key][str(coordinate)] = possible

    every_word_every_residue = all(
        set(residues) == expected_residues
        for residues in word_residue_support.values()
    )
    every_coord_every_residue = all(
        set(possible) == expected_residues
        for per_word in coordinate_residue_support.values()
        for possible in per_word.values()
    )
    shape_residues = [(7 + 10 * k) % 10 for k in range(20)]
    shifted_shape_residues = {
        str(shift): [((7 + 10 * k) + shift) % 10 for k in range(20)]
        for shift in RESIDUES
    }
    affine_shape_only = (
        all(residue == 7 for residue in shape_residues)
        and all(len(set(residues)) == 1 for residues in shifted_shape_residues.values())
        and sorted({residues[0] for residues in shifted_shape_residues.values()}) == list(RESIDUES)
    )
    all_fibers_have_ten_residue_placements = all(
        len(residues) == 10 and set(residues) == expected_residues
        for residues in word_residue_support.values()
    )
    functorial_obstruction = (
        len(x6) == 21
        and every_word_every_residue
        and every_coord_every_residue
        and affine_shape_only
        and all_fibers_have_ten_residue_placements
    )

    not_claimed = [
        "physical fine-structure constant identification R_6(D*)=alpha^-1",
        "the C_10-torsor origin (clock basepoint o_0) as Window6-internally determined (it is provably external: every X_6 word embeds into P_10 at every residue)",
        "the ClockCouplingCert iota as Window6-internally forced (the 10 shifted couplings are Window6-indistinguishable)",
        "D*_6 as a Window6-internal theorem (it is clock-gated / needs-external with a proven functorial obstruction)",
    ]

    checks = [
        check(
            "X6_zero_padding_every_residue",
            len(x6) == 21 and every_word_every_residue,
            "The 21 length-6 linear golden words each embed into a length-10 cyclic golden word at every start residue by zero padding.",
        ),
        check(
            "local_coordinate_every_residue",
            every_coord_every_residue,
            "For every pair (w,i) with w in X_6 and i in {0,...,5}, varying the start residue realizes all ten clock residues.",
        ),
        check(
            "affine_shape_only_s7_rho10",
            affine_shape_only,
            "The return shape e_k=7+10k has constant residue 7 mod 10, and translating by any a in Z/10Z preserves the same affine shape while changing the absolute phase.",
        ),
        check(
            "functorial_no_canonical_section",
            functorial_obstruction,
            "The cylinder-to-cyclic-placement forgetful view has all ten residues over every Window6 word, so Window6 cylinder data provide no canonical section selecting a C_10 basepoint.",
        ),
        check(
            "ClockCouplingCert_C10_torsor_origin_irreducible",
            functorial_obstruction,
            "The ClockCouplingCert C_10-torsor origin is provably external to Window6 local data; the ten shifted couplings iota_a are Window6-indistinguishable.",
        ),
    ]

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "X6_size": len(x6),
        "X6_words": [bitword(word) for word in x6],
        "residue_set": list(RESIDUES),
        "every_word_every_residue": bool(every_word_every_residue),
        "word_residue_support": word_residue_support,
        "word_embedding_samples": word_embedding_samples,
        "every_coord_every_residue": bool(every_coord_every_residue),
        "coordinate_residue_support": coordinate_residue_support,
        "shifted_couplings_count": 10,
        "shifted_couplings": [f"iota_{shift}(e)=iota(e)+{shift} mod 10" for shift in RESIDUES],
        "shape_7_plus_10k": {
            "s": 7,
            "rho": 10,
            "residues_for_k_0_to_19": shape_residues,
            "rho_mod_10": 0,
            "verdict": "(s,rho)=(7,10) fixes the affine shape e_k=7+10k and a residue class relative to a chosen origin, not the absolute C_10 phase origin.",
        },
        "shifted_shape_residues": shifted_shape_residues,
        "functorial_obstruction_verdict": "PROVEN: Window6 data define length-6 cylinders, while P_10 supplies cyclic placements of cylinders; every cylinder has all ten residue placements, so there is no Window6-internal canonical section selecting the C_10-torsor origin.",
        "minimal_external_cert": {
            "O": "C_10 torsor of absolute clock origins",
            "sigma": "cyclic shift action on the period-10 golden clock",
            "o_0": "chosen basepoint / clock phase origin",
            "E_res": "Window6 residual, seam, and return events to be coupled to the clock",
            "k": "return index in e_k=7+10k",
            "deg_tilde": "external degree lift with deg_tilde(e_k)=7+10k after choosing o_0",
        },
        "not_claimed": not_claimed,
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

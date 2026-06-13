#!/usr/bin/env python3
"""BC4 candidate audit: cyclic Window6 sectors versus codon reading-frame rotation.

The Window6 cyclic carrier has a genuine rotation-sector structure.  This
script tests the tempting biological correspondence: codon positions might
inherit that cyclic sector character under position rotation.  The standard
code is evaluated directly; a count match is not accepted as evidence.
"""
from __future__ import annotations

from collections import Counter
from itertools import product
import json
import sys


EXPERIMENT_ID = "bc4_cyclic_sector_frame_symmetry"
CLAIM_ID = "bridge.window6_codon_q6.cyclic_sector_frame_symmetry"

NUCLEOTIDES = ("U", "C", "A", "G")
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


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=False, sort_keys=True))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def codons() -> list[str]:
    return ["".join(chars) for chars in product(NUCLEOTIDES, repeat=3)]


def rotate_left(codon: str) -> str:
    return codon[1:] + codon[0]


def rotate_right(codon: str) -> str:
    return codon[-1] + codon[:-1]


def position_degeneracy_rates() -> dict[str, float]:
    rates = {}
    for position in range(3):
        total = 0
        same = 0
        for codon in codons():
            for base in NUCLEOTIDES:
                if base == codon[position]:
                    continue
                alt = codon[:position] + base + codon[position + 1:]
                total += 1
                if CODON_TO_MEANING[codon] == CODON_TO_MEANING[alt]:
                    same += 1
        rates[f"pos{position + 1}"] = same / total
    return rates


def rotation_audit(rotation) -> dict[str, object]:
    fixed_label = []
    changed_examples = []
    orbit_label_profiles = Counter()
    visited = set()
    for codon in codons():
        rotated = rotation(codon)
        if CODON_TO_MEANING[codon] == CODON_TO_MEANING[rotated]:
            fixed_label.append(codon)
        elif len(changed_examples) < 12:
            changed_examples.append([
                codon,
                rotated,
                CODON_TO_MEANING[codon],
                CODON_TO_MEANING[rotated],
            ])
        if codon not in visited:
            orbit = []
            cur = codon
            while cur not in orbit:
                orbit.append(cur)
                visited.add(cur)
                cur = rotation(cur)
            labels = tuple(sorted(Counter(CODON_TO_MEANING[item] for item in orbit).items()))
            orbit_label_profiles[labels] += 1
    return {
        "same_label_count": len(fixed_label),
        "total_codons": 64,
        "same_label_rate": len(fixed_label) / 64,
        "same_label_codons": fixed_label,
        "changed_examples": changed_examples,
        "orbit_label_profile_count": len(orbit_label_profiles),
    }


def main() -> None:
    left = rotation_audit(rotate_left)
    right = rotation_audit(rotate_right)
    rates = position_degeneracy_rates()
    position_rates_equal = len({round(value, 12) for value in rates.values()}) == 1

    emit(
        "refuted",
        claim=(
            "Window6 cyclic rotation sectors correspond to codon-position cyclic rotation "
            "as a code-label-preserving sector character."
        ),
        reason=(
            "The Window6 side has a genuine cyclic rotation sector, but the standard genetic code "
            "is not cyclic in its three positions: cyclically rotating codons usually changes the "
            "amino-acid/stop label, and position degeneracy rates are strongly unequal."
        ),
        checks=[
            {
                "name": "left_position_rotation_preserves_labels",
                "passed": left["same_label_count"] == 64,
                "same_label_count": left["same_label_count"],
                "same_label_rate": left["same_label_rate"],
            },
            {
                "name": "right_position_rotation_preserves_labels",
                "passed": right["same_label_count"] == 64,
                "same_label_count": right["same_label_count"],
                "same_label_rate": right["same_label_rate"],
            },
            {
                "name": "position_degeneracy_is_cyclically_symmetric",
                "passed": position_rates_equal,
                "rates": rates,
            },
        ],
        left_rotation=left,
        right_rotation=right,
        position_degeneracy_rates=rates,
        anti_numerology_note=(
            "A cyclic Window6 carrier and three codon positions are not enough; "
            "the sector action must preserve the biological label structure, and it does not."
        ),
    )


if __name__ == "__main__":
    main()

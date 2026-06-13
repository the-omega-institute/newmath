#!/usr/bin/env python3
"""BC1: structure-respecting forcing test for codon cardinalities.

The script evaluates whether the standard genetic code supplies a canonical
map from its box, wobble, family, or boundary structure into the width-6 or
width-5 Fibonacci cubes.  A cardinality match alone is recorded as a control,
not as a forcing certificate.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import permutations, product
import json
import sys


EXPERIMENT_ID = "bc1_cardinality_forcing"
CLAIM_ID = "bridge.window6_codon_q6.cardinality_forcing"

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

SYNONYMOUS_FAMILIES = (
    ("UUU", "UUC"), ("UUA", "UUG"), ("UCU", "UCC", "UCA", "UCG"),
    ("UAU", "UAC"), ("UGU", "UGC"), ("CUU", "CUC", "CUA", "CUG"),
    ("CCU", "CCC", "CCA", "CCG"), ("CAU", "CAC"), ("CAA", "CAG"),
    ("CGU", "CGC", "CGA", "CGG"), ("AUU", "AUC", "AUA"),
    ("ACU", "ACC", "ACA", "ACG"), ("AAU", "AAC"), ("AAA", "AAG"),
    ("AGU", "AGC"), ("AGA", "AGG"), ("GUU", "GUC", "GUA", "GUG"),
    ("GCU", "GCC", "GCA", "GCG"), ("GAU", "GAC"), ("GAA", "GAG"),
    ("GGU", "GGC", "GGA", "GGG"),
)

R_BOUNDARY = (
    "AAA", "AGA", "AGG", "AUA", "CUA", "CUC", "CUG", "CUU", "UAA",
    "UAG", "UCA", "UGA", "UUA",
)

R_MODULES = {
    "AGR": ("AGA", "AGG"),
    "AAA": ("AAA",),
    "CUN": ("CUA", "CUC", "CUG", "CUU"),
    "AUA": ("AUA",),
    "SSN": ("UCA", "UUA"),
    "stop_Trp": ("UAA", "UAG", "UGA"),
}

R_FACE_COUNT = (13, 16, 4)


def emit(status, **fields):
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
    }
    payload.update(fields)
    print(json.dumps(payload, sort_keys=True))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def codon_order():
    return ["".join(chars) for chars in product(NUCLEOTIDES, repeat=3)]


def no_adjacent_one_words(width):
    return [
        bits
        for bits in product((0, 1), repeat=width)
        if all(not (bits[i] and bits[i + 1]) for i in range(width - 1))
    ]


def hamming_distance(left, right):
    return sum(1 for a, b in zip(left, right) if a != b)


def fibonacci_cube(width):
    words = no_adjacent_one_words(width)
    adjacency = {word: [] for word in words}
    for i, left in enumerate(words):
        for right in words[i + 1:]:
            if hamming_distance(left, right) == 1:
                adjacency[left].append(right)
                adjacency[right].append(left)
    return {
        "width": width,
        "words": words,
        "count": len(words),
        "weight_counts": dict(sorted(Counter(sum(word) for word in words).items())),
        "position_one_counts": {
            str(i): sum(1 for word in words if word[i] == 1)
            for i in range(width)
        },
        "degree_counts": dict(sorted(Counter(len(neigh) for neigh in adjacency.values()).items())),
        "edge_count": sum(len(neigh) for neigh in adjacency.values()) // 2,
        "coordinate_fiber_count": width * 2,
    }


def groups_by_meaning(codons):
    groups = defaultdict(list)
    for codon in codons:
        groups[CODON_TO_MEANING[codon]].append(codon)
    return {key: tuple(value) for key, value in sorted(groups.items())}


def build_boxes():
    boxes = {}
    for first, second in product(NUCLEOTIDES, repeat=2):
        prefix = first + second
        codons = tuple(prefix + third for third in NUCLEOTIDES)
        meanings = groups_by_meaning(codons)
        box_kind = "family" if len(meanings) == 1 else "split"
        pyrimidine_codons = tuple(c for c in codons if c[2] in PYRIMIDINES)
        purine_codons = tuple(c for c in codons if c[2] in PURINES)
        boxes[prefix + "N"] = {
            "prefix": prefix,
            "codons": codons,
            "kind": box_kind,
            "meaning_groups": meanings,
            "third_position_split": {
                "Y": pyrimidine_codons,
                "R": purine_codons,
            },
        }
    return boxes


def derive_synonymous_families_from_code():
    meaning_to_codons = groups_by_meaning(codon_order())
    families = []
    for meaning, codons in meaning_to_codons.items():
        if meaning == "Stop" or len(codons) < 2:
            continue
        if meaning in ("Leu", "Arg", "Ser"):
            families.extend(split_cross_box_family(meaning, codons))
        else:
            families.append(tuple(c for c in codon_order() if c in codons))
    return tuple(families)


def split_cross_box_family(meaning, codons):
    by_box = defaultdict(list)
    for codon in codon_order():
        if codon in codons:
            by_box[codon[:2]].append(codon)
    return [tuple(value) for _, value in sorted(by_box.items()) if len(value) >= 2]


def split_box_subblocks(boxes):
    blocks = []
    for box_name, box in sorted(boxes.items()):
        if box["kind"] != "split":
            continue
        for meaning, codons in box["meaning_groups"].items():
            if meaning != "Stop" and len(codons) >= 2:
                blocks.append({
                    "box": box_name,
                    "meaning": meaning,
                    "codons": codons,
                    "third_symbols": "".join(c[2] for c in codons),
                })
    return blocks


def block_size_counts(blocks):
    return dict(sorted(Counter(len(block) for block in blocks).items()))


def list_size_counts(list_of_records):
    return dict(sorted(Counter(len(record["codons"]) for record in list_of_records).items()))


def string_keyed(counter_dict):
    return {str(key): value for key, value in counter_dict.items()}


def exact_family_sets_match(left, right):
    return {frozenset(item) for item in left} == {frozenset(item) for item in right}


def r_box_profile(boxes):
    profile = {}
    r_set = set(R_BOUNDARY)
    for box_name, box in sorted(boxes.items()):
        codons = tuple(c for c in box["codons"] if c in r_set)
        if codons:
            profile[box_name] = {
                "count": len(codons),
                "codons": codons,
                "box_kind": box["kind"],
            }
    return profile


def third_position_yr_class(codons):
    symbols = {codon[2] for codon in codons}
    if symbols <= PYRIMIDINES:
        return "Y"
    if symbols <= PURINES:
        return "R"
    return "mixed"


def wobble_alignment_report(split_blocks):
    aligned = []
    mixed = []
    for block in split_blocks:
        item = {
            "box": block["box"],
            "meaning": block["meaning"],
            "codons": block["codons"],
            "yr_class": third_position_yr_class(block["codons"]),
        }
        if item["yr_class"] == "mixed":
            mixed.append(item)
        else:
            aligned.append(item)
    return aligned, mixed


def arbitrary_encoding_control():
    bit_pairs = ((0, 0), (0, 1), (1, 0), (1, 1))
    counts = []
    r_counts = []
    all_codons = codon_order()
    for perm in permutations(bit_pairs):
        encoding = dict(zip(NUCLEOTIDES, perm))

        def image(codon):
            bits = []
            for char in codon:
                bits.extend(encoding[char])
            return tuple(bits)

        chosen = [
            codon for codon in all_codons
            if all(not (image(codon)[i] and image(codon)[i + 1]) for i in range(5))
        ]
        counts.append(len(chosen))
        r_counts.append(sum(1 for codon in R_BOUNDARY if codon in chosen))
    return {
        "encoding_count": 24,
        "no_adjacent_codon_counts": sorted(set(counts)),
        "boundary_hits": sorted(set(r_counts)),
        "all_encodings_select_21": sorted(set(counts)) == [21],
    }


def candidate_checks():
    boxes = build_boxes()
    gamma5 = fibonacci_cube(5)
    gamma6 = fibonacci_cube(6)
    derived_families = derive_synonymous_families_from_code()
    split_blocks = split_box_subblocks(boxes)
    aligned_split_blocks, mixed_split_blocks = wobble_alignment_report(split_blocks)
    family_boxes = sorted(name for name, box in boxes.items() if box["kind"] == "family")
    split_boxes = sorted(name for name, box in boxes.items() if box["kind"] == "split")
    arbitrary_control = arbitrary_encoding_control()

    family_size_counts = block_size_counts(SYNONYMOUS_FAMILIES)
    split_size_counts = list_size_counts(split_blocks)
    r_module_size_counts = dict(sorted(Counter(len(v) for v in R_MODULES.values()).items()))
    r_profile = r_box_profile(boxes)

    data_integrity = {
        "standard_code_codons": len(CODON_TO_MEANING),
        "standard_code_complete": set(CODON_TO_MEANING) == set(codon_order()),
        "families_match_code": exact_family_sets_match(SYNONYMOUS_FAMILIES, derived_families),
        "r_modules_cover_r": set().union(*(set(v) for v in R_MODULES.values())) == set(R_BOUNDARY),
        "r_modules_disjoint": sum(len(v) for v in R_MODULES.values()) == len(set(R_BOUNDARY)),
        "box_count": len(boxes),
        "family_box_count": len(family_boxes),
        "split_box_count": len(split_boxes),
        "split_box_subblock_count": len(split_blocks),
    }

    checks = [
        {
            "name": "data_integrity_standard_code",
            "passed": all(data_integrity.values()),
            "respects_biology": True,
            "respects_window": None,
            "necessity_argument": False,
            "details": data_integrity,
        },
        {
            "name": "fibonacci_cube_structure",
            "passed": gamma6["count"] == fib(8) == 21 and gamma5["count"] == fib(7) == 13,
            "respects_biology": None,
            "respects_window": True,
            "necessity_argument": True,
            "gamma6": {
                "count": gamma6["count"],
                "edge_count": gamma6["edge_count"],
                "weight_counts": string_keyed(gamma6["weight_counts"]),
                "degree_counts": string_keyed(gamma6["degree_counts"]),
                "position_one_counts": gamma6["position_one_counts"],
            },
            "gamma5": {
                "count": gamma5["count"],
                "edge_count": gamma5["edge_count"],
                "weight_counts": string_keyed(gamma5["weight_counts"]),
                "degree_counts": string_keyed(gamma5["degree_counts"]),
                "position_one_counts": gamma5["position_one_counts"],
            },
        },
        {
            "name": "families_21_to_gamma6_by_block_size_or_weight",
            "passed": False,
            "respects_biology": True,
            "respects_window": True,
            "explicit_bijection": False,
            "necessity_argument": False,
            "bio_family_size_counts": string_keyed(family_size_counts),
            "gamma6_weight_counts": string_keyed(gamma6["weight_counts"]),
            "obstruction": (
                "family block sizes have counts 12,1,8 over sizes 2,3,4, "
                "while gamma6 weights have counts 1,6,10,4 over weights 0,1,2,3"
            ),
        },
        {
            "name": "box_partition_to_gamma6_graph",
            "passed": False,
            "respects_biology": True,
            "respects_window": True,
            "explicit_bijection": False,
            "necessity_argument": False,
            "bio_box_structure": {
                "box_count": len(boxes),
                "family_boxes": family_boxes,
                "split_boxes": split_boxes,
                "family_box_count": len(family_boxes),
                "split_box_count": len(split_boxes),
            },
            "gamma6_native_structure": {
                "vertex_count": gamma6["count"],
                "edge_count": gamma6["edge_count"],
                "coordinate_fiber_count": gamma6["coordinate_fiber_count"],
                "degree_counts": string_keyed(gamma6["degree_counts"]),
            },
            "obstruction": (
                "the code uses a 16-box product by the first two codon positions, "
                "whereas gamma6 has coordinate fibers and Hamming adjacency but no "
                "native 4-by-4 box partition with a third-position wobble axis"
            ),
        },
        {
            "name": "split_box_subblocks_13_to_gamma5",
            "passed": False,
            "respects_biology": True,
            "respects_window": True,
            "explicit_bijection": False,
            "necessity_argument": False,
            "bio_object": "thirteen size-at-least-two sense subblocks inside the eight split boxes",
            "bio_subblock_size_counts": string_keyed(split_size_counts),
            "gamma5_weight_counts": string_keyed(gamma5["weight_counts"]),
            "parent_split_box_count": len(split_boxes),
            "gamma5_coordinate_fiber_count": gamma5["coordinate_fiber_count"],
            "obstruction": (
                "the split-box thirteen is a real wobble object, but its parent "
                "box structure and size profile do not match the gamma5 grading"
            ),
        },
        {
            "name": "r_boundary_13_to_gamma5",
            "passed": False,
            "respects_biology": True,
            "respects_window": True,
            "explicit_bijection": False,
            "necessity_argument": False,
            "bio_object": "boundary set R with six declared modules",
            "r_size": len(R_BOUNDARY),
            "r_face_count": list(R_FACE_COUNT),
            "r_module_size_counts": string_keyed(r_module_size_counts),
            "r_box_profile": r_profile,
            "gamma5_weight_counts": string_keyed(gamma5["weight_counts"]),
            "obstruction": (
                "R is a boundary/module object, not the split-box subblock object; "
                "its six module sizes do not supply the gamma5 weight grading or graph"
            ),
        },
        {
            "name": "purine_pyrimidine_wobble_alignment",
            "passed": False,
            "respects_biology": True,
            "respects_window": False,
            "explicit_bijection": False,
            "necessity_argument": False,
            "aligned_split_subblocks": len(aligned_split_blocks),
            "mixed_split_subblocks": mixed_split_blocks,
            "third_position_classes": {"Y": sorted(PYRIMIDINES), "R": sorted(PURINES)},
            "obstruction": (
                "purine-pyrimidine and wobble data live on the third codon position "
                "inside boxes; they do not determine the no-adjacent-one condition "
                "on six binary coordinates"
            ),
        },
        {
            "name": "arbitrary_two_bit_encoding_control",
            "passed": arbitrary_control["all_encodings_select_21"],
            "respects_biology": False,
            "respects_window": True,
            "explicit_bijection": False,
            "necessity_argument": False,
            "details": arbitrary_control,
            "obstruction": (
                "every nucleotide-to-two-bit bijection selects 21 codons because it "
                "is only a relabeling of all 64 binary words"
            ),
        },
    ]

    summary = {
        "family_count": len(SYNONYMOUS_FAMILIES),
        "boundary_count": len(R_BOUNDARY),
        "split_box_subblock_count": len(split_blocks),
        "gamma6_count": gamma6["count"],
        "gamma5_count": gamma5["count"],
        "family_box_count": len(family_boxes),
        "split_box_count": len(split_boxes),
        "certifying_checks": [
            check["name"] for check in checks
            if check.get("explicit_bijection")
            and check.get("respects_biology")
            and check.get("respects_window")
            and check.get("necessity_argument")
        ],
    }
    return checks, summary


def main():
    checks, summary = candidate_checks()
    if not checks[0]["passed"]:
        emit(
            "needs_derivation",
            checks=checks,
            summary=summary,
            note="The encoded standard-code data failed an integrity check.",
        )

    if summary["certifying_checks"]:
        emit(
            "certified",
            checks=checks,
            summary=summary,
            note="A tested candidate supplies an explicit structure-respecting map and a necessity argument.",
        )

    emit(
        "coincidence",
        checks=checks,
        summary=summary,
        note=(
            "The counts 21 and 13 match the width-6 and width-5 Fibonacci cubes, "
            "but the tested canonical biological structures do not yield a "
            "structure-respecting forcing map.  The split-box thirteen is a real "
            "wobble object; R is a separate boundary object.  Neither is forced by "
            "the Window6 horizon in this derivation."
        ),
    )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Forward enumeration for the Window6 seam-identification certificate.

The audit enumerates X_6 and the cell-owner predicates directly from the
length-six binary words. It does not read alpha, a physical origin, or any
metrological target.
"""

from __future__ import annotations

import json
from itertools import product
from typing import Any


Word = tuple[int, ...]

U1_WORDS = ["000001", "000010", "000100", "001000", "010000", "100000"]
UR_WORDS = ["100001", "100101", "101001"]
MIN_DEFECT = "100001"
MIN_DEFECT_PARENTS = ["000001", "100000"]
NOT_CLAIMED = [
    "No physical alpha, inverse-alpha readout, or metrological identification is claimed.",
    "Complete a=0 origin selection remains needs-cert.",
    "The physical identification of q_0 with this seam remains needs-external because the residual grading and D*_6 side are not certified here.",
    "ReturnFunctorCert, the 7+10k return-degree law, and the P_10-vs-edge-cokernel clock fork remain open.",
    "The P_10 torsor no-go still stands.",
]


def word_to_string(word: Word) -> str:
    return "".join(str(bit) for bit in word)


def no_adjacent_one(word: Word) -> bool:
    return all(not (word[index] and word[index + 1]) for index in range(len(word) - 1))


def cyclic_normal(word: Word) -> bool:
    return no_adjacent_one(word) and not (word[0] and word[-1])


def endpoint_collision(word: Word) -> bool:
    return no_adjacent_one(word) and bool(word[0] and word[-1])


def hamming_weight(word: Word) -> int:
    return sum(word)


def remove_one_bits(word: Word) -> list[Word]:
    parents: list[Word] = []
    for index, bit in enumerate(word):
        if bit:
            parent = list(word)
            parent[index] = 0
            parents.append(tuple(parent))
    return parents


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def main() -> None:
    all_words = list(product((0, 1), repeat=6))
    x6 = [word for word in all_words if no_adjacent_one(word)]
    u1 = [word for word in x6 if cyclic_normal(word) and hamming_weight(word) == 1]
    ur = [word for word in x6 if endpoint_collision(word)]
    ur_min_weight = min(hamming_weight(word) for word in ur)
    ur_min_defects = [word for word in ur if hamming_weight(word) == ur_min_weight]
    min_defect = ur_min_defects[0]
    parents = [
        parent
        for parent in remove_one_bits(min_defect)
        if cyclic_normal(parent) and hamming_weight(parent) == 1
    ]
    u1_strings = [word_to_string(word) for word in u1]
    ur_strings = [word_to_string(word) for word in ur]
    min_defect_string = word_to_string(min_defect)
    parent_strings = [word_to_string(word) for word in parents]
    unique_seam = (
        len(ur_min_defects) == 1
        and min_defect_string == MIN_DEFECT
        and sorted(parent_strings) == sorted(MIN_DEFECT_PARENTS)
        and all(parent in u1 for parent in parents)
    )

    checks = [
        check(
            "x6_count_21",
            len(x6) == 21,
            "The direct length-6 no-adjacent-one enumeration gives |X_6|=21=F_8.",
        ),
        check(
            "u1_cells",
            u1_strings == U1_WORDS,
            "The cyclic-normal single-excitation cell U_1 contains exactly the six visible words.",
        ),
        check(
            "ur_cells",
            ur_strings == UR_WORDS,
            "The endpoint-collision sector U_R is exactly {100001,100101,101001}.",
        ),
        check(
            "ur_min_defect_100001",
            len(ur_min_defects) == 1 and min_defect_string == MIN_DEFECT and ur_min_weight == 2,
            "The unique minimum-Hamming-weight endpoint-collision defect is 100001, with weight 2.",
        ),
        check(
            "parents_in_u1",
            sorted(parent_strings) == sorted(MIN_DEFECT_PARENTS) and all(parent in u1 for parent in parents),
            "Deleting either endpoint 1 from 100001 gives 000001 and 100000, both in U_1.",
        ),
        check(
            "unique_seam_u1_to_ur",
            unique_seam,
            "The minimal forward boundary-creation event in the cell quotient is uniquely U_1->U_R, so j_seam=e_U1-e_UR.",
        ),
    ]
    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "X_6": [word_to_string(word) for word in x6],
        "X_6_count": len(x6),
        "F_8": 21,
        "U_1": u1_strings,
        "U_R": ur_strings,
        "U_R_weight_rows": {word_to_string(word): hamming_weight(word) for word in ur},
        "min_defect": {"word": min_defect_string, "weight": ur_min_weight},
        "parents": parent_strings,
        "j_seam": "e_U1-e_UR",
        "chi_j_seam": 7,
        "closed_obligation_core": "edge-cokernel obligation A combinatorial core: SeamIdentificationCert",
        "not_claimed": NOT_CLAIMED,
        "forbidden_claims": NOT_CLAIMED,
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    main()

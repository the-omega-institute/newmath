#!/usr/bin/env python3
"""Verify the image-language count boundary for golden-mean factor maps.

For the golden-mean subshift Sigma, A_m is the finite set of admissible
length-m binary words with no adjacent 1s. A local rule f:A_m -> B gives the
length-1 image language f(A_m). The audit checks the finite count identity,
an injective count-preserving witness, a non-injective count-dropping witness,
and the higher-block unique-decipherability formulation.
"""

from __future__ import annotations

import itertools
import json
from typing import Any

from sympy import fibonacci


AUDIT_LENGTHS = tuple(range(2, 8))
WITNESS_M = 4
HIGHER_BLOCK_N_MAX = 5


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def bitword(word: tuple[int, ...]) -> str:
    return "".join(str(bit) for bit in word)


def admissible(word: tuple[int, ...]) -> bool:
    return all(
        not (word[index] == word[index + 1] == 1)
        for index in range(len(word) - 1)
    )


def words_no_adjacent(length: int) -> list[tuple[int, ...]]:
    return [
        bits
        for bits in itertools.product((0, 1), repeat=length)
        if admissible(bits)
    ]


def periodic_sigma_point(block: tuple[int, ...]) -> tuple[int, ...]:
    """Return a finite period whose bi-infinite repetition lies in Sigma."""
    if not admissible(block):
        raise ValueError("block must be golden-mean admissible")
    if block and block[0] == 1 and block[-1] == 1:
        return block + (0,)
    return block


def periodic_realizes(block: tuple[int, ...]) -> bool:
    period = periodic_sigma_point(block)
    doubled = period + period
    appears = any(
        doubled[index : index + len(block)] == block
        for index in range(len(period))
    )
    return admissible(doubled) and appears


def image_count(local_rule: dict[str, str], domain: list[tuple[int, ...]]) -> int:
    return len({local_rule[bitword(word)] for word in domain})


def injective_rule(domain: list[tuple[int, ...]]) -> dict[str, str]:
    return {bitword(word): f"label:{bitword(word)}" for word in domain}


def noninjective_rule(
    domain: list[tuple[int, ...]],
) -> tuple[dict[str, str], tuple[tuple[int, ...], tuple[int, ...]]]:
    first, second, *rest = domain
    shared = f"collision:{bitword(first)}:{bitword(second)}"
    rule = {
        bitword(first): shared,
        bitword(second): shared,
    }
    for word in rest:
        rule[bitword(word)] = f"label:{bitword(word)}"
    return rule, (first, second)


def block_labels(
    point_word: tuple[int, ...],
    m: int,
    local_rule: dict[str, str],
) -> tuple[str, ...]:
    return tuple(
        local_rule[bitword(point_word[index : index + m])]
        for index in range(len(point_word) - m + 1)
    )


def projection_injective_for_n(
    m: int,
    n: int,
    local_rule: dict[str, str],
) -> bool:
    domain = words_no_adjacent(n + m - 1)
    seen: dict[tuple[str, ...], str] = {}
    for word in domain:
        labels = block_labels(word, m, local_rule)
        key = bitword(word)
        if labels in seen and seen[labels] != key:
            return False
        seen[labels] = key
    return True


def main() -> None:
    am_counts = {str(m): len(words_no_adjacent(m)) for m in AUDIT_LENGTHS}
    fibonacci_check = {
        str(m): {
            "A_m": am_counts[str(m)],
            "F_m_plus_2": int(fibonacci(m + 2)),
            "matches": am_counts[str(m)] == int(fibonacci(m + 2)),
        }
        for m in AUDIT_LENGTHS
    }

    domains = {m: words_no_adjacent(m) for m in AUDIT_LENGTHS}
    arbitrary_image_bounds = {}
    for m, domain in domains.items():
        parity_rule = {
            bitword(word): f"parity:{sum(word) % 2}"
            for word in domain
        }
        first_symbol_rule = {
            bitword(word): f"first:{word[0]}"
            for word in domain
        }
        arbitrary_image_bounds[str(m)] = {
            "domain_count": len(domain),
            "parity_image_count": image_count(parity_rule, domain),
            "first_symbol_image_count": image_count(first_symbol_rule, domain),
            "universal_cardinality_reason": (
                "For every function f with domain A_m, f(A_m) is a quotient "
                "image of the finite set A_m, so |f(A_m)| <= |A_m|."
            ),
            "all_images_at_most_domain": (
                image_count(parity_rule, domain) <= len(domain)
                and image_count(first_symbol_rule, domain) <= len(domain)
            ),
        }

    witness_domain = domains[WITNESS_M]
    inj_rule = injective_rule(witness_domain)
    injective_image_count = image_count(inj_rule, witness_domain)

    drop_rule, (collision_u, collision_v) = noninjective_rule(witness_domain)
    noninjective_image_count = image_count(drop_rule, witness_domain)
    collision_pair = {
        "m": WITNESS_M,
        "u": bitword(collision_u),
        "v": bitword(collision_v),
        "u_admissible": admissible(collision_u),
        "v_admissible": admissible(collision_v),
        "u_periodic_sigma_witness": bitword(periodic_sigma_point(collision_u)),
        "v_periodic_sigma_witness": bitword(periodic_sigma_point(collision_v)),
        "u_realized_inside_sigma": periodic_realizes(collision_u),
        "v_realized_inside_sigma": periodic_realizes(collision_v),
        "shared_label": drop_rule[bitword(collision_u)],
    }

    all_fib_counts_match = all(item["matches"] for item in fibonacci_check.values())
    all_image_bounds_hold = all(
        item["all_images_at_most_domain"]
        for item in arbitrary_image_bounds.values()
    )
    injective_preserves = injective_image_count == len(witness_domain)
    noninjective_drops = (
        noninjective_image_count < len(witness_domain)
        and drop_rule[bitword(collision_u)] == drop_rule[bitword(collision_v)]
        and bitword(collision_u) != bitword(collision_v)
        and collision_pair["u_realized_inside_sigma"]
        and collision_pair["v_realized_inside_sigma"]
    )

    higher_block_injective = {
        str(n): projection_injective_for_n(WITNESS_M, n, inj_rule)
        for n in range(1, HIGHER_BLOCK_N_MAX + 1)
    }
    higher_block_noninjective = {
        str(n): projection_injective_for_n(WITNESS_M, n, drop_rule)
        for n in range(1, HIGHER_BLOCK_N_MAX + 1)
    }
    decipherability_ok = (
        injective_preserves
        and noninjective_drops
        and all(higher_block_injective.values())
        and higher_block_noninjective["1"] is False
    )

    lemma = {
        "L1_identity": "L_1(Phi_m(Sigma)) = f(A_m)",
        "finite_bound": "|L_1(Phi_m(Sigma))|=|f(A_m)| <= |A_m| = F_{m+2}",
        "equality_condition": "Equality holds exactly when f is injective on A_m.",
        "drop_condition": "If u != v in A_m and f(u)=f(v), then |L_1| < F_{m+2}.",
        "unique_decipherability": (
            "For length n, the image language count is preserved exactly when "
            "the block-label map pi_n:A_{n+m-1}->B^n is injective. Matching "
            "the input counts at every n is the finite unique-decipherability "
            "condition; n=1 is the first possible count-loss boundary."
        ),
        "not_about_physical_constants": True,
    }

    checks = [
        check(
            "am_count_fibonacci",
            all_fib_counts_match,
            "Enumerated |A_m| for m=2..7 matches F_{m+2}=3,5,8,13,21,34.",
        ),
        check(
            "image_count_le_fibonacci",
            all_image_bounds_hold,
            "For any local rule f:A_m -> B, the image f(A_m) is a quotient of the finite domain A_m, hence |f(A_m)|<=|A_m|=F_{m+2}; sampled rules instantiate the boundary.",
        ),
        check(
            "injective_preserves_count",
            injective_preserves,
            "The explicit injective rule word -> label:word has |L_1|=|A_m|=F_{m+2}.",
        ),
        check(
            "noninjective_drops_count",
            noninjective_drops,
            "The explicit non-injective rule merges two distinct admissible windows, both realized by periodic points in Sigma, and strictly drops |L_1|.",
        ),
        check(
            "decipherability_lemma",
            decipherability_ok,
            "The L1 equality boundary is injectivity of f on A_m; the higher-block boundary is injectivity of pi_n on A_{n+m-1}.",
        ),
    ]

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "am_counts": am_counts,
        "fibonacci_check": fibonacci_check,
        "witness_m": WITNESS_M,
        "A_m_words": [bitword(word) for word in witness_domain],
        "injective_image_count": injective_image_count,
        "noninjective_image_count": noninjective_image_count,
        "collision_pair": collision_pair,
        "image_counts": {
            "injective": {
                "L1_count": injective_image_count,
                "F_m_plus_2": int(fibonacci(WITNESS_M + 2)),
                "preserves_count": injective_preserves,
            },
            "noninjective": {
                "L1_count": noninjective_image_count,
                "F_m_plus_2": int(fibonacci(WITNESS_M + 2)),
                "drops_count": noninjective_drops,
            },
            "sampled_bounds": arbitrary_image_bounds,
        },
        "higher_block_projection_injective": {
            "injective_rule": higher_block_injective,
            "noninjective_rule": higher_block_noninjective,
        },
        "lemma": lemma,
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=True))


if __name__ == "__main__":
    main()

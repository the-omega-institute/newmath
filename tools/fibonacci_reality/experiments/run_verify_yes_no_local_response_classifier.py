#!/usr/bin/env python3
"""Finite local-response audit for yes/no logic as probe-relative change.

The audit treats a history as a finite binary word and a neighbor as a one-step
extension.  "Zero" and "nonzero" are classified only by preservation or change
of a named finite probe signature.  The checks deliberately include guards
showing that signature preservation is not raw identity and is not a literal
numeric derivative theorem.
"""

from __future__ import annotations

import itertools
import json
from typing import Any, Callable


MAX_HISTORY_LENGTH = 3
DIGITS = (0, 1)

History = tuple[int, ...]
Probe = Callable[[History], Any]


def check(name: str, passed: bool, reason: str) -> dict[str, Any]:
    return {"name": name, "passed": bool(passed), "reason": reason}


def bitword(history: History) -> str:
    return "".join(str(bit) for bit in history) if history else "empty"


def histories(max_length: int) -> list[History]:
    return [
        tuple(bits)
        for length in range(max_length + 1)
        for bits in itertools.product(DIGITS, repeat=length)
    ]


def cont(history: History, digit: int) -> History:
    return (*history, digit)


def probe_terminal_bit(history: History) -> int | None:
    return history[-1] if history else None


def probe_has_one(history: History) -> bool:
    return any(bit == 1 for bit in history)


def probe_length_parity(history: History) -> int:
    return len(history) % 2


def probe_length(history: History) -> int:
    return len(history)


def probe_word(history: History) -> str:
    return bitword(history)


PROBE_BUNDLES: dict[str, tuple[Probe, ...]] = {
    "terminal": (probe_terminal_bit,),
    "terminal_has_one": (probe_terminal_bit, probe_has_one),
    "full_word": (probe_length, probe_word),
    "parity": (probe_length_parity,),
}


def signature(bundle_name: str, history: History) -> tuple[Any, ...] | None:
    values = tuple(probe(history) for probe in PROBE_BUNDLES[bundle_name])
    if any(value is None for value in values):
        return None
    return values


def classify(bundle_name: str, history: History, digit: int) -> str:
    before = signature(bundle_name, history)
    after = signature(bundle_name, cont(history, digit))
    if before is None or after is None:
        return "Gap"
    if before == after:
        return "ZeroResp"
    return "NonzeroResp"


def count_ones(history: History) -> int:
    return sum(history)


def finite_difference_count_ones(history: History, digit: int) -> int:
    return count_ones(cont(history, digit)) - count_ones(history)


def main() -> None:
    base_histories = histories(MAX_HISTORY_LENGTH)
    neighbor_rows = [
        {
            "history": bitword(history),
            "digit": digit,
            "neighbor": bitword(cont(history, digit)),
        }
        for history in base_histories
        for digit in DIGITS
    ]

    terminal_classes = [
        classify("terminal", history, digit)
        for history in base_histories
        for digit in DIGITS
    ]
    terminal_class_counts = {
        name: terminal_classes.count(name)
        for name in ("ZeroResp", "NonzeroResp", "Gap")
    }

    preservation_examples = [
        (history, digit)
        for history in base_histories
        for digit in DIGITS
        if history and classify("terminal", history, digit) == "ZeroResp"
    ]
    separation_failures = [
        (history, digit)
        for history in base_histories
        for digit in DIGITS
        if classify("full_word", history, digit) != "NonzeroResp"
    ]
    dependence_transition = ((0,), 0)
    same_transition_terminal = classify("terminal", *dependence_transition)
    same_transition_full = classify("full_word", *dependence_transition)
    gap_examples = [
        (history, digit)
        for history in base_histories
        for digit in DIGITS
        if classify("terminal", history, digit) == "Gap"
    ]

    zero_with_numeric_change = ((1,), 1)
    nonzero_with_numeric_zero = ((1,), 0)
    zero_counterexamples = [
        (history, digit)
        for history, digit in preservation_examples
        if history != cont(history, digit)
    ]

    checks = [
        check(
            "finite_history_neighbor_table",
            len(base_histories) == 15
            and len(neighbor_rows) == 30
            and all(row["neighbor"].startswith("" if row["history"] == "empty" else row["history"]) for row in neighbor_rows),
            "Histories of length <=3 form 15 finite binary words; each has exactly two one-step extension neighbors.",
        ),
        check(
            "probe_signature_preservation",
            bool(preservation_examples)
            and terminal_class_counts == {"ZeroResp": 14, "NonzeroResp": 14, "Gap": 2},
            "For the terminal-bit probe, each nonempty history has one preserving extension and one changing extension; the empty history is a gap.",
        ),
        check(
            "probe_signature_separation",
            not separation_failures,
            "The full-word probe bundle separates every one-step extension from its source history.",
        ),
        check(
            "probe_dependence_check",
            same_transition_terminal == "ZeroResp" and same_transition_full == "NonzeroResp",
            "The transition 0 -> 00 is zero for the terminal-bit probe and nonzero for the full-word probe.",
        ),
        check(
            "gap_case_check",
            sorted((bitword(history), digit) for history, digit in gap_examples) == [("empty", 0), ("empty", 1)],
            "The terminal-bit signature is undefined at the empty history, so both first-step continuations remain Gap rather than forced yes/no.",
        ),
        check(
            "numeric_readback_sanity_check",
            classify("terminal", *zero_with_numeric_change) == "ZeroResp"
            and finite_difference_count_ones(*zero_with_numeric_change) == 1
            and classify("terminal", *nonzero_with_numeric_zero) == "NonzeroResp"
            and finite_difference_count_ones(*nonzero_with_numeric_zero) == 0,
            "Probe-signature response and numeric finite difference are distinct interfaces: terminal preservation can have count delta 1, and terminal change can have count delta 0.",
        ),
        check(
            "zero_derivative_counterexample_guard",
            bool(zero_counterexamples)
            and all(history != cont(history, digit) for history, digit in zero_counterexamples),
            "ZeroResp is not raw identity: there are nonidentical one-step extensions with preserved terminal-bit signature.",
        ),
        check(
            "yes_no_local_response_classifier",
            set(terminal_classes) == {"ZeroResp", "NonzeroResp", "Gap"}
            and terminal_class_counts["ZeroResp"] == terminal_class_counts["NonzeroResp"] == 14,
            "The finite classifier returns only ZeroResp, NonzeroResp, or Gap, with balanced zero/nonzero cases on nonempty histories for the terminal probe.",
        ),
    ]

    status = "passed" if all(item["passed"] for item in checks) else "failed"
    result = {
        "carrier": "finite binary histories of length <=3, with one-step continuations sampled to length <=4",
        "history_count": len(base_histories),
        "neighbor_count": len(neighbor_rows),
        "probe_bundles": sorted(PROBE_BUNDLES),
        "terminal_class_counts": terminal_class_counts,
        "preservation_examples": [
            {"history": bitword(history), "digit": digit, "neighbor": bitword(cont(history, digit))}
            for history, digit in preservation_examples[:8]
        ],
        "probe_dependence_witness": {
            "transition": "0 -> 00",
            "terminal": same_transition_terminal,
            "full_word": same_transition_full,
        },
        "gap_witnesses": [
            {"history": bitword(history), "digit": digit, "neighbor": bitword(cont(history, digit))}
            for history, digit in gap_examples
        ],
        "numeric_readback_witnesses": {
            "zero_response_with_count_delta_one": {
                "transition": "1 -> 11",
                "terminal_class": classify("terminal", *zero_with_numeric_change),
                "count_ones_delta": finite_difference_count_ones(*zero_with_numeric_change),
            },
            "nonzero_response_with_count_delta_zero": {
                "transition": "1 -> 10",
                "terminal_class": classify("terminal", *nonzero_with_numeric_zero),
                "count_ones_delta": finite_difference_count_ones(*nonzero_with_numeric_zero),
            },
        },
        "accepted_readback": "Yes/no is represented only as probe-relative local response: ZeroResp means finite signature preservation, NonzeroResp means finite signature change, and Gap means the named probe bundle does not decide the continuation.",
        "not_claimed": [
            "BEDC proves yes/no logic is literally real differentiation.",
            "ZeroResp proves absolute identity of histories.",
            "NonzeroResp proves absolute non-identity outside the named probe bundle.",
            "A missing certified difference proves sameness.",
            "Numeric finite difference and probe-signature response are the same interface.",
        ],
    }
    print(json.dumps({"status": status, "checks": checks, "result": result}, ensure_ascii=False))


if __name__ == "__main__":
    main()

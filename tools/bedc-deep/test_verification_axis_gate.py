#!/usr/bin/env python3
"""Regression checks for verification-axis hard rejects in paper lanes."""

from __future__ import annotations

import sys
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import burden_candidate_miner
import codex_track
from dispatch_bedc_target import BedcTarget


def test_codex_track_rejects_lean_target_close() -> None:
    target = BedcTarget(
        target_id="B-test",
        title="Closed term substitution boundary Lean target downstream coverage lemma",
        fields={},
        body="",
    )
    reason = codex_track._substance_rejection(
        target,
        {
            "content": (
                "\\begin{theorem}[Closed-term substitution boundary downstream Lean-target coverage]\n"
                "\\label{thm:closed-term-substitution-boundary-downstream-lean-target-coverage}\n"
                "For the Lean target $\\mathsf{BEDC.Derived.X.single\\_carrier\\_alignment}$, every consumer is local.\n"
                "\\end{theorem}\n"
            )
        },
    )
    assert "invalid_verification_axis_surface" in reason


def test_burden_miner_skips_verification_axis_file() -> None:
    item = {
        "file": "papers/bedc/parts/concrete_instances/example.tex",
        "theorem_like_labels": [
            {
                "label": "thm:example-lean-target-readiness",
                "title": "Example Lean target readiness",
                "env": "theorem",
            },
            {
                "label": "thm:example-formal-surface-exhaustion",
                "title": "Example formal surface exhaustion",
                "env": "theorem",
            },
        ],
    }
    original_read = burden_candidate_miner._read
    try:
        burden_candidate_miner._read = lambda _rel: (
            "The paper-side readiness surface for the Lean target "
            "$\\mathsf{BEDC.Derived.Example.single\\_carrier\\_alignment}$."
        )
        assert burden_candidate_miner._candidate_for_item(item) is None
    finally:
        burden_candidate_miner._read = original_read


if __name__ == "__main__":
    test_codex_track_rejects_lean_target_close()
    test_burden_miner_skips_verification_axis_file()
    print("test_verification_axis_gate: ok")

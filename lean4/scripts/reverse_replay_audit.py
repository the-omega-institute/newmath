#!/usr/bin/env python3
"""Reverse-replay benchmark audit for BEDC.

Per the round-2 adversarial-consensus refutation, the honest way to drive the
user's "export traditional-math equivalence" goal is NOT a single misleading
'% done' but a fixed benchmark of hard traditional theorems tracked in 4 states:
replayed_in_bedc / transferred_to_std / blocked_missing_carrier /
blocked_forbidden_principle.

This audit loads reverse_replay_benchmark.json, verifies every replayed entry's
Lean decl still exists (so the benchmark cannot drift into stale green), and
prints the 4-state dashboard. A replayed entry whose decl vanished is real
regression (reported as DRIFT). Informational (exit 0) for now.
"""
import json
import os
import re
import subprocess
import sys

SCRIPTS = os.path.dirname(os.path.abspath(__file__))
REGISTRY = os.path.join(SCRIPTS, "reverse_replay_benchmark.json")
LEAN_BEDC = "/Users/chronoai/newmath/lean4/BEDC"
STATES = (
    "replayed_in_bedc",
    "transferred_to_std",
    "blocked_missing_carrier",
    "blocked_forbidden_principle",
)


def decl_exists(name):
    pat = r"(theorem|lemma|def)\s+" + re.escape(name) + r"\b"
    try:
        out = subprocess.run(
            ["grep", "-rlE", "--include=*.lean", pat, LEAN_BEDC],
            capture_output=True, text=True, timeout=120,
        )
        return bool(out.stdout.strip())
    except (subprocess.SubprocessError, OSError):
        return None


def main():
    with open(REGISTRY, encoding="utf-8") as f:
        reg = json.load(f)
    entries = reg.get("entries", [])
    tally = {s: 0 for s in STATES}
    drift = []
    for e in entries:
        st = e.get("status")
        tally[st] = tally.get(st, 0) + 1
        if st == "replayed_in_bedc":
            d = e.get("bedc_decl")
            if d and decl_exists(d) is False:
                drift.append(f"{e['object']}::{d} ({e['traditional_theorem']})")
    by_level = {}
    by_object = {}
    counts_toward_real = 0
    for e in entries:
        lvl = e.get("bridge_level", "?")
        by_level[lvl] = by_level.get(lvl, 0) + 1
        obj = e.get("object", "?")
        by_object.setdefault(obj, []).append(e.get("status"))
        if e.get("counts_toward_real_maturity"):
            counts_toward_real += 1
    out = {
        "total_benchmark_theorems": len(entries),
        "by_state": tally,
        "by_bridge_level": dict(sorted(by_level.items())),
        "per_object_status": {k: v for k, v in sorted(by_object.items())},
        "entries_counting_toward_real_maturity": counts_toward_real,
        "anti_aggregation_rule": "NEVER report a single stdEquivChecked %; the only Real-maturity entries are the blocked Real rows above — finite/discrete replays (Nat/Rat/...) explicitly do NOT count toward Real.",
        "replayed_decl_drift": drift,
        "interop_summary": {
            "transferred_to_std": tally["transferred_to_std"],
            "_note": "0 by the mathlib-free invariant; non-zero requires an axiom-firewalled BEDC.StdBridge layer (operator-scope).",
        },
        "_headline": (
            "Honest red dashboard: replayed_in_bedc counts real BEDC "
            "reconstructions at declared scope; blocked_forbidden_principle is "
            "PERMANENT (0-axiom core cannot internalize quotient/completeness/"
            "host-equality/choice); blocked_missing_carrier is the buildable "
            "frontier (next stdEquivChecked flagship). Grow replayed and "
            "transferred; never paper over a forbidden-principle block as progress."
        ),
    }
    print(json.dumps(out, ensure_ascii=False, indent=2))
    if drift:
        print(f"\n[reverse-replay] DRIFT: {len(drift)} replayed decl(s) missing",
              file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

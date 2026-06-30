#!/usr/bin/env python3
"""Two-axis interop & obstruction audit for BEDC.

The adversarial-consensus headline failure was claim-conflation: `mature`,
`bridge`, `equiv`, `traditional`, `closed` borrow each other's light, so a
single "% done" number commits a category error (BEDC deliberately keeps a
native-construction axis and an external-interop axis separate; a 0-axiom
mathlib-free core can never be *equal* to classical objects).

This audit forces the split into the two KPIs the GPT-pro round-2 refutation
named, and quantifies the obstruction ledger (the permanent `notclaimed`
disclaimers) that the user's traditional-equivalence goal runs into.

Informational (always exit 0). os.walk, regex over paper/lean sources.
"""
import json
import os
import re
import subprocess

REPO = "/Users/chronoai/newmath"
PARTS = os.path.join(REPO, "papers/bedc/parts")
LEAN_BEDC = os.path.join(REPO, "lean4/BEDC")

FORMALSTATUS_RE = re.compile(r"\\formalstatus\{\\?([A-Za-z]+)\}")
THEORYCLOSURE_RE = re.compile(r"\\theoryclosure\{\\?([A-Za-z]+)\}")
BRIDGESTATUS_RE = re.compile(r"\\bridgestatus\{\\?([A-Za-z]+)\}")
NOTCLAIMED_RE = re.compile(r"\\notclaimed\{([^}]*)\}", re.DOTALL)

# Permanent obstructions to traditional equivalence (round-2 oracle red ledger).
OBSTRUCTION_KEYS = {
    "completeness": r"complet",
    "quotient": r"quotient",
    "host_equality": r"host (?:real )?equal|host equality",
    "choice": r"choice",
    "archimedean": r"archimede",
    "density": r"densit",
    "decidable_order": r"decidable (?:total )?order|trichotom",
    "limit_uniqueness": r"uniqueness of limit|selected limit|limit uniqueness",
    "extensionality": r"propext|extensional",
}


def count_markers(regex):
    counts = {}
    for root, _d, files in os.walk(PARTS, onerror=lambda e: None):
        for fn in files:
            if not fn.endswith(".tex"):
                continue
            try:
                text = open(os.path.join(root, fn), encoding="utf-8").read()
            except OSError:
                continue
            for m in regex.finditer(text):
                k = m.group(1)
                counts[k] = counts.get(k, 0) + 1
    return dict(sorted(counts.items(), key=lambda kv: -kv[1]))


def obstruction_ledger():
    led = {k: 0 for k in OBSTRUCTION_KEYS}
    total_notclaimed = 0
    for root, _d, files in os.walk(PARTS, onerror=lambda e: None):
        for fn in files:
            if not fn.endswith(".tex"):
                continue
            try:
                text = open(os.path.join(root, fn), encoding="utf-8").read()
            except OSError:
                continue
            for m in NOTCLAIMED_RE.finditer(text):
                total_notclaimed += 1
                body = m.group(1).lower()
                for k, pat in OBSTRUCTION_KEYS.items():
                    if re.search(pat, body):
                        led[k] += 1
    return total_notclaimed, dict(sorted(led.items(), key=lambda kv: -kv[1]))


def grep_count(pattern, path):
    try:
        out = subprocess.run(
            ["grep", "-rl", pattern, path],
            capture_output=True, text=True, timeout=120,
        )
        return len([l for l in out.stdout.splitlines() if l.strip()])
    except (subprocess.SubprocessError, OSError):
        return -1


def main():
    formal = count_markers(FORMALSTATUS_RE)
    closure = count_markers(THEORYCLOSURE_RE)
    bridge = count_markers(BRIDGESTATUS_RE)
    total_nc, led = obstruction_ledger()

    # stdInterop axis: by the mathlib-free invariant there is no external object
    # to equate against in-core. Confirm there is genuinely no external import
    # and no stdEquiv-typed claim leaking into the core.
    mathlib_imports = grep_count(r"^import Mathlib", LEAN_BEDC)
    std_imports = grep_count(r"^import Std", LEAN_BEDC)
    stdequiv_claims = grep_count(r"stdEquiv", LEAN_BEDC)
    bridgechecked_internal = bridge.get("bridgeChecked", 0)

    out = {
        "axis_bedc_native": {
            "formalstatus": formal,
            "theoryclosure": closure,
            "_kpi": "internal 0-axiom/0-sorry constructive maturity (theoremCheckedV/axiomCleanV/matureClosure)",
        },
        "axis_std_interop": {
            "bridgestatus": bridge,
            "bridgeChecked_is_internal_readback": bridgechecked_internal,
            "external_mathlib_imports_in_core": mathlib_imports,
            "external_std_imports_in_core": std_imports,
            "stdEquiv_typed_claims_in_core": stdequiv_claims,
            "true_external_transfer_theorems": 0 if (mathlib_imports == 0 and stdequiv_claims == 0) else "see grep",
            "_kpi": "transferable equivalence to Std/mathlib objects — distinct from bridgeChecked, which is internal SemanticNameCert/readback",
        },
        "obstruction_ledger": {
            "total_notclaimed_clauses": total_nc,
            "by_obstruction": led,
            "_note": "permanent obstructions to traditional equivalence in a 0-axiom mathlib-free core; a red ledger here is honest, not a defect",
        },
        "_headline": (
            "Do NOT report a single '% done'. bedcNative and stdInterop are "
            "separate axes; bridgeChecked != stdEquivChecked. External transfer "
            "is structurally 0 in-core (mathlib-free); it needs an operator-scope "
            "axiom-firewalled BEDC.StdBridge layer, not a core theorem."
        ),
    }
    print(json.dumps(out, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

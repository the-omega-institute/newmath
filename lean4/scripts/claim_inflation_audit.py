#!/usr/bin/env python3
"""Claim-inflation gate for BEDC (earned-status claim typing).

Round-2 adversarial-consensus + GPT-pro spec: any prose asserting equivalence
to a standard/traditional/classical object, a checked bridge, a formal/Lean
proof, or axiom-cleanliness must be PAID FOR by the chapter's own earned status
-- mature/bridge/equiv/traditional cannot borrow each other's light. The core
result is Rule A: external (std/mathlib) equivalence is structurally unearned in
a mathlib-free core (std_equiv_checked is always false in-core), so any
project-anchored, non-disclaimed "equivalent to the standard reals" prose is an
over-claim.

FP-avoidance (the hard part): a sentence is only checked if it carries a PROJECT
ANCHOR (BEDC/we/our/this/the formalization/Lean) -- classical-background prose
like "Classically, the reals are obtained by quotienting Cauchy sequences" is
skipped -- and DISCLAIMER context (notclaimed / "do not claim" / negation /
"terminology only") exempts it.

Default exit 0 (informational, severity-tagged). --strict makes ERROR-level
findings exit 1 (for a future hard-gate promotion; off by default per the
narrow-over-loose discipline).
"""
import argparse
import json
import os
import re
import sys

PARTS = "/Users/chronoai/newmath/papers/bedc/parts"

FORMALSTATUS_RE = re.compile(r"\\formalstatus\{\\?([A-Za-z]+)\}")
BRIDGESTATUS_RE = re.compile(r"\\bridgestatus\{\\?([A-Za-z]+)\}")
THEORYCLOSURE_RE = re.compile(r"\\theoryclosure\{\\?([A-Za-z]+)\}")
NOTCLAIMED_RE = re.compile(r"\\notclaimed\{([^}]*)\}", re.DOTALL)
DISCLAIMER_SPAN_RE = re.compile(
    r"\\(?:notclaimed|scopeclosed|upgradepath|theoryclosure|constructivestory|"
    r"falsifiablePrediction|independenceWitness)\{[^}]*\}",
    re.DOTALL,
)

# A sentence enters checking only with a project anchor (it is OUR claim).
ANCHOR_RE = re.compile(
    r"\b(?:BEDC|we|our|this\s+(?:theorem|lemma|construction|chapter|section|"
    r"result|formalization|development|encoding|definition|bridge|carrier|"
    r"package)|the\s+(?:formalization|library|development|construction|model|"
    r"encoding|carrier|namecert)|Lean)\b",
    re.IGNORECASE,
)
DISCLAIMER_RE = re.compile(
    r"\b(?:not\s+claim\w*|no\s+claim|do(?:es)?\s+not|this\s+does\s+not|"
    r"not\s+(?:intended|asserted|proved|formalized|equivalent|traditional|"
    r"standard|classical|complete|a\s+bridge|a\s+transfer)|out\s+of\s+scope|"
    r"beyond\s+(?:the\s+)?scope|future\s+work|planned|informal|sketch|"
    r"analogy\s+only|mnemonic|terminology\s+only|name\s+only|without\s+claiming|"
    r"stops?\s+short|disclaim\w*|never\s+claim\w*)\b",
    re.IGNORECASE,
)
NEG_RE = re.compile(
    r"\b(?:not|no|without|never|cannot|lacks?|does\s+not|do\s+not|is\s+not|"
    r"are\s+not|has\s+no|have\s+no|no\s+coordinate|cannot\s+replace)\b",
    re.IGNORECASE,
)
# Classical-lineage background ("Following Erdős … classical topology, …") is a
# \origin{human} reference, not a claim that the BEDC object equals it.
LINEAGE_RE = re.compile(
    r"\b(?:following|classically|in\s+the\s+(?:classical|traditional|standard)\s+"
    r"(?:presentation|literature|sense|setting)|generaliz\w+\s+the)\b",
    re.IGNORECASE,
)
CONTRAST_RE = re.compile(r"\b(?:but|however|nevertheless|yet|actually|instead)\b", re.I)

# Rule A: external standard equivalence (always unearned in-core).
A_VERB = (
    r"(?:equivalent|equiv|isomorphic|isomorphism|identif(?:y|ies|ied)\s+with|"
    r"corresponds?\s+to|agrees?\s+with|matches|recovers?|captures?|models?|"
    r"represents?|faithful(?:ly)?|conservative\s+extension|transfers?\s+to|"
    r"transports?\s+to|the\s+same\s+as|identical\s+to|coincid\w+\s+with)"
)
A_TARGET = (
    r"(?:standard|traditional|classical|usual|ordinary|textbook|mathlib|external|"
    r"host)\b[^.\n]{0,70}?\b(?:real|reals|ℝ|\\mathbb\{R\}|rational|ℚ|integer|ℤ|"
    r"complex|group|ring|field|metric\s+space|manifold|number\s+system|"
    r"Dedekind|Cauchy\s+complet\w+)"
)
A_RE = re.compile(
    r"\b" + A_VERB + r"\b[^.\n]{0,70}?\b" + A_TARGET
    + r"|\b" + A_TARGET + r"\b[^.\n]{0,40}?\b" + A_VERB + r"\b",
    re.IGNORECASE,
)
# Rule D: formal/Lean proof claimed but unearned.
D_RE = re.compile(
    r"\b(?:formalized|formalised|Lean-?checked|machine-?checked|0-?sorry\s+proof|"
    r"no-?sorry\s+proof|certified|proved\s+in\s+Lean|formal\s+proof)\b"
    r"|\b(?:proves?|established?|shows?|derives?)\b[^.\n]{0,40}?"
    r"\b(?:in\s+Lean|machine-?checked|formally\s+verified|certified)\b",
    re.IGNORECASE,
)
# Rule E: axiom-clean claimed but unearned.
E_RE = re.compile(
    r"\b(?:axiom-?clean|axiom-?free|0-?axiom|no\s+axioms?|without\s+axioms?)\b",
    re.IGNORECASE,
)


def earned(text):
    fs = FORMALSTATUS_RE.search(text)
    bs = BRIDGESTATUS_RE.search(text)
    fs = fs.group(1) if fs else None
    bs = bs.group(1) if bs else None
    return {
        "native_theorem_checked": fs in {"theoremCheckedV", "bridgeCheckedV", "axiomCleanV"},
        "axiom_clean": fs == "axiomCleanV",
        "std_equiv_checked": False,  # structurally impossible in mathlib-free core
        "formalstatus": fs,
        "bridgestatus": bs,
    }


def sentences(text):
    # Strip disclaimer macro spans so claims inside them are pre-exempt.
    spans = [(m.start(), m.end()) for m in DISCLAIMER_SPAN_RE.finditer(text)]
    for m in re.finditer(r"[^.;!?\n]{8,400}[.;!?]", text):
        s, e = m.start(), m.end()
        if any(a <= s < b for a, b in spans):
            continue
        yield m.group(0)


def exempt(sent, hit_start):
    if DISCLAIMER_RE.search(sent):
        return True
    if LINEAGE_RE.search(sent):
        return True
    # BEDC prose is disclaimer-heavy ("the carrier has no coordinate for … host
    # equality"): scan the whole sentence up to just past the hit for a negation,
    # not only the 60 chars immediately before it.
    left = sent[:hit_start + 25]
    if NEG_RE.search(left) and not CONTRAST_RE.search(left):
        return True
    return False


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--strict", action="store_true",
                    help="exit 1 if any ERROR finding (default: informational exit 0)")
    args = ap.parse_args()

    findings = []
    scanned = 0
    # Rule D dropped: `Lean-?checked` collided with the legitimate \leanchecked
    # marker macro (18013 FPs). Prose "this is Lean-checked" vs the earned marker
    # needs marker-macro exclusion + real prose context; left to a later pass.
    # Rule A is the load-bearing gate (external std-equivalence, always unearned
    # in a mathlib-free core); Rule E flags unearned axiom-clean prose.
    rules = [("A_std_equiv_unearned", A_RE, "native_theorem_checked_or_std_equiv"),
             ("E_axiom_clean_unearned", E_RE, "axiom_clean")]
    for root, _d, files in os.walk(PARTS, onerror=lambda e: None):
        for fn in files:
            if not fn.endswith(".tex"):
                continue
            path = os.path.join(root, fn)
            try:
                text = open(path, encoding="utf-8").read()
            except OSError:
                continue
            scanned += 1
            ea = earned(text)
            rel = os.path.relpath(path, PARTS)
            for sent in sentences(text):
                if not ANCHOR_RE.search(sent):
                    continue
                for rule, rx, need in rules:
                    m = rx.search(sent)
                    if not m:
                        continue
                    if exempt(sent, m.start()):
                        continue
                    if rule == "A_std_equiv_unearned" and ea["std_equiv_checked"]:
                        continue
                    if rule == "D_formal_proof_unearned" and ea["native_theorem_checked"]:
                        continue
                    if rule == "E_axiom_clean_unearned" and ea["axiom_clean"]:
                        continue
                    findings.append({
                        "rule": rule,
                        "chapter": rel,
                        "formalstatus": ea["formalstatus"],
                        "bridgestatus": ea["bridgestatus"],
                        "sentence": re.sub(r"\s+", " ", sent).strip()[:160],
                    })
                    break  # one finding per sentence
    by_rule = {}
    for f in findings:
        by_rule[f["rule"]] = by_rule.get(f["rule"], 0) + 1
    out = {
        "scope": "papers/bedc/parts/*.tex prose",
        "tex_files_scanned": scanned,
        "total_findings": len(findings),
        "by_rule": by_rule,
        "samples": findings[:30],
        "_note": (
            "Findings are project-anchored, non-disclaimed prose asserting a claim "
            "the chapter has not earned. Rule A (external std/traditional "
            "equivalence) is the load-bearing one: std_equiv_checked is always "
            "false in a mathlib-free core, so any such claim outside a disclaimer "
            "is an over-claim. Informational by default (--strict to fail on "
            "ERRORs). Refine ANCHOR/DISCLAIMER/verb lists if a FP class recurs."
        ),
    }
    print(json.dumps(out, ensure_ascii=False, indent=2))
    if args.strict and findings:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

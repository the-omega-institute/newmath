#!/usr/bin/env python3
"""Claim-inflation audit for BEDC.

The round-2 adversarial-consensus headline: the biggest quality risk is not
weak Lean code but claim-conflation -- chapter prose asserting that a BEDC
object is equivalent to the standard/classical/traditional/host counterpart
while it has not earned that status (bridgestatus != bridgeChecked), letting
mature/bridge/equiv/traditional borrow each other's light.

This flags unearned external-equivalence prose, while NOT punishing the
(legitimate, abundant) apophatic discipline: a claim inside notclaimed /
scopeclosed / upgradepath or under a negation ("does not", "without",
"refuses", "excludes") is honest scoping, not inflation.

Informational (always exit 0) -- false positives are non-fatal review items.
"""
import json
import os
import re

PARTS = "/Users/chronoai/newmath/papers/bedc/parts"

# v2: drop the bare "equality/equals" noun noise; require a genuine assertion
# verb phrase tied to a CONCRETE traditional math object, and scan only
# concrete_instances (vision/philosophy/governance essays legitimately discuss
# host/standard/equality concepts at the meta level).
EQUIV_VERB = (
    r"(?:is\s+equivalent\s+to|are\s+equivalent\s+to|isomorphic\s+to|"
    r"coincid\w+\s+with|identical\s+to|the\s+same\s+as|agrees?\s+with|"
    r"recovers?|reconstructs?\s+exactly)"
)
STD_OBJECT = (
    r"(?:standard|classical|traditional|usual|ordinary|host)\s+"
    r"(?:real|reals|rational|rationals|integer|naturals?|natural\s+number|"
    r"complex|group|ring|field|metric|topolog\w+|manifold|number\s+system)"
)
CLAIM_RE = re.compile(
    r"\b" + EQUIV_VERB + r"\b[^.\n]{0,60}?\b" + STD_OBJECT + r"\b"
    r"|\b" + STD_OBJECT + r"\b[^.\n]{0,30}?\b" + EQUIV_VERB + r"\b",
    re.IGNORECASE,
)
NEGATION_RE = re.compile(
    r"\b(?:not|no|never|cannot|without|refus\w+|exclud\w+|"
    r"does\s+not|is\s+not|are\s+not|disclaim\w*|absten\w+|"
    r"beyond\s+(?:the\s+)?scope|out\s+of\s+scope|left\s+open|future\s+work|"
    r"without\s+claiming|stops?\s+short)\b",
    re.IGNORECASE,
)
ONLY_PATH = "concrete_instances"
DISCLAIMER_SPAN_RE = re.compile(
    r"\\(?:notclaimed|scopeclosed|upgradepath|theoryclosure|constructivestory)"
    r"\{[^}]*\}",
    re.DOTALL,
)
BRIDGESTATUS_RE = re.compile(r"\\bridgestatus\{\\?([A-Za-z]+)\}")


def chapter_bridgestatus(text):
    m = BRIDGESTATUS_RE.search(text)
    return m.group(1) if m else "(absent)"


def main():
    flagged = []
    scanned = 0
    for root, _d, files in os.walk(PARTS, onerror=lambda e: None):
        for fn in files:
            if not fn.endswith(".tex"):
                continue
            path = os.path.join(root, fn)
            if ONLY_PATH not in path:
                continue
            try:
                text = open(path, encoding="utf-8").read()
            except OSError:
                continue
            scanned += 1
            bstatus = chapter_bridgestatus(text)
            if bstatus == "bridgeChecked":
                continue
            disclaimer_spans = [
                (m.start(), m.end()) for m in DISCLAIMER_SPAN_RE.finditer(text)
            ]
            for m in CLAIM_RE.finditer(text):
                pos = m.start()
                if any(s <= pos < e for s, e in disclaimer_spans):
                    continue
                window = text[max(0, pos - 110):pos + 110]
                if NEGATION_RE.search(window):
                    continue
                rel = os.path.relpath(path, PARTS)
                snippet = re.sub(r"\s+", " ", text[max(0, pos - 30):pos + 80]).strip()
                flagged.append({
                    "chapter": rel,
                    "bridgestatus": bstatus,
                    "claim": snippet,
                })
                break
    out = {
        "scope": "papers/bedc/parts (chapters with bridgestatus != bridgeChecked)",
        "tex_files_scanned": scanned,
        "flagged_chapters": len(flagged),
        "samples": flagged[:30],
        "_note": (
            "Flags prose asserting equivalence to a standard/classical/host "
            "counterpart in a chapter that has NOT earned bridgeChecked, outside "
            "any notclaimed/scopeclosed/upgradepath disclaimer and not under a "
            "negation. Informational: review each flag and refine the verb / "
            "qualifier / negation lists if a class of false positive recurs. A "
            "near-zero count confirms BEDC's notclaimed discipline holds."
        ),
    }
    print(json.dumps(out, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

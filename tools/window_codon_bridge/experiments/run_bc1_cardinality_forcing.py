#!/usr/bin/env python3
"""BC1 (head-start): is the codon-Q6 boundary cardinality FORCED by the Window6 Fibonacci horizon?

Bridge forcing conjecture BC1: |R|=13=F7 and (synonymous families)=21=F8 are NOT coincidences
but FORCED by an explicit structural map  standard-code-boundary -> width-6 Fibonacci words.

This script does the COMPUTABLE groundwork and emits an HONEST verdict:
  - Establish the Window6 Fibonacci horizon counts (no-adjacent-one binary words).
  - Establish the bio counts (21 synonymous families; |R|=13 boundary codons).
  - Test the simplest candidate structural maps (codon = 6-bit word under nucleotide=2-bit
    encodings; does the no-adjacent-one admissible set respect family / boundary structure?).
  - Verdict discipline: if only the COUNTS coincide (both Fibonacci) with no structure-respecting
    map verified -> 'coincidence' (a PROMPT for a certificate, NOT a certificate). A 'certified'
    verdict requires an explicit map + a forcing/necessity argument, which is the remaining work.

Anti-numerology: 13=F7 and 21=F8 alone are NOT evidence. Many small sets have Fibonacci sizes.
"""
from __future__ import annotations
import json, sys
from itertools import product

EXPERIMENT_ID = "bc1_cardinality_forcing"
CLAIM_ID = "bridge.window6_codon_q6.cardinality_forcing"

# BIO side fixed objects (from bio_reality window_six_codon_tiles_at_the_code_layer)
R_BOUNDARY = ["AAA", "AGA", "AGG", "AUA", "CUA", "CUC", "CUG", "CUU", "UAA", "UAG", "UCA", "UGA", "UUA"]
# 21 synonymous family blocks (Q9_FAMILIES partition of the 61 sense + stop structure)
Q9_FAMILIES = [
    ["UUU", "UUC"], ["UUA", "UUG"], ["UCU", "UCC", "UCA", "UCG"], ["UAU", "UAC"], ["UGU", "UGC"],
    ["CUU", "CUC", "CUA", "CUG"], ["CCU", "CCC", "CCA", "CCG"], ["CAU", "CAC"], ["CAA", "CAG"],
    ["CGU", "CGC", "CGA", "CGG"], ["AUU", "AUC", "AUA"], ["ACU", "ACC", "ACA", "ACG"], ["AAU", "AAC"],
    ["AAA", "AAG"], ["AGU", "AGC"], ["AGA", "AGG"], ["GUU", "GUC", "GUA", "GUG"], ["GCU", "GCC", "GCA", "GCG"],
    ["GAU", "GAC"], ["GAA", "GAG"], ["GGU", "GGC", "GGA", "GGG"],
]


def emit(status, **kw):
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, ensure_ascii=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a  # fib(1)=1,fib(2)=1,fib(7)=13,fib(8)=21


def no_adjacent_one_words(width):
    """All length-`width` binary words with no two adjacent ones."""
    out = []
    for bits in product((0, 1), repeat=width):
        if all(not (bits[i] == 1 and bits[i + 1] == 1) for i in range(width - 1)):
            out.append(bits)
    return out


def main():
    # 1. Window6 Fibonacci horizon: count of no-adjacent-one binary words
    naw6 = no_adjacent_one_words(6)
    naw5 = no_adjacent_one_words(5)
    f8, f7 = fib(8), fib(7)
    horizon_ok = (len(naw6) == f8 == 21) and (len(naw5) == f7 == 13)

    # 2. bio counts
    n_families = len(Q9_FAMILIES)
    n_R = len(R_BOUNDARY)
    counts_coincide = (n_families == len(naw6) == 21) and (n_R == len(naw5) == 13)

    # 3. candidate structural map: codon as 6-bit word, nucleotide -> 2 bits.
    # Try every nucleotide->2bit encoding (4! = 24 assignments) and check whether the
    # no-adjacent-one 6-bit codon set has size related to 21/13 or respects family blocks.
    nts = ["U", "C", "A", "G"]
    bit_pairs = [(0, 0), (0, 1), (1, 0), (1, 1)]
    from itertools import permutations
    all_codons = ["".join(c) for c in product(nts, repeat=3)]
    encoding_results = []
    best = None
    for perm in permutations(bit_pairs):
        enc = dict(zip(nts, perm))
        def word(cod):
            w = []
            for ch in cod:
                w.extend(enc[ch])
            return tuple(w)
        nadj_codons = [c for c in all_codons if all(not (word(c)[i] == 1 and word(c)[i + 1] == 1) for i in range(5))]
        k = len(nadj_codons)
        # how many R codons are no-adjacent-one under this encoding?
        r_in = sum(1 for c in R_BOUNDARY if c in nadj_codons)
        encoding_results.append({"n_noadj_codons": k, "R_in_noadj": r_in})
        if best is None or abs(k - 21) < abs(best["n_noadj_codons"] - 21):
            best = {"n_noadj_codons": k, "R_in_noadj": r_in, "encoding": {n: list(enc[n]) for n in nts}}

    # Does ANY simple encoding make the no-adjacent-one codon set size = 21 (= families)?
    any_encoding_gives_21 = any(e["n_noadj_codons"] == 21 for e in encoding_results)
    sizes_seen = sorted({e["n_noadj_codons"] for e in encoding_results})

    checks = [
        {"name": "fibonacci_horizon_counts", "passed": horizon_ok,
         "noadj_width6": len(naw6), "F8": f8, "noadj_width5": len(naw5), "F7": f7},
        {"name": "bio_counts", "passed": (n_families == 21 and n_R == 13), "n_families": n_families, "n_R": n_R},
        {"name": "counts_coincide_fibonacci", "passed": counts_coincide,
         "note": "21=F8 (families & width-6 no-adj words), 13=F7 (R & width-5 no-adj words)"},
        {"name": "structure_respecting_map_found", "passed": False,
         "any_2bit_encoding_gives_21_noadj_codons": any_encoding_gives_21,
         "noadj_codon_set_sizes_over_encodings": sizes_seen,
         "best_encoding": best,
         "note": "No structure-respecting bijection (families<->no-adj words / R<->width-5 words) has been CONSTRUCTED or PROVEN forced yet. The 2-bit codon encodings do not by themselves reproduce 21/13 as a forced structural image."},
    ]

    # Honest verdict: counts coincide (Fibonacci) but no forcing map established -> coincidence (a prompt, not a certificate)
    emit(
        "coincidence",
        checks=checks,
        remaining_derivation=[
            "Construct an EXPLICIT map standard-code synonymous structure -> width-6 no-adjacent-one (Zeckendorf) words.",
            "Decide the correct level of the map: family-level bijection (21<->21) and/or boundary R <-> width-5 words (13<->13).",
            "Give a FORCING argument: why the genetic-code degeneracy/boundary MUST have these cardinalities given the Window6 horizon, not merely that the numbers are Fibonacci.",
            "If the map respects the synonymous-block and boundary structure AND is forced -> upgrade verdict to certified; if no structural map exists, downgrade to refuted.",
        ],
        note="HEAD START ONLY. Counts coincide and are Fibonacci (21=F8 families & width-6 no-adj words; 13=F7 R & width-5 no-adj words), but per anti-numerology discipline this is a PROMPT, not a certificate. Plain 2-bit codon encodings do not reproduce 21/13 as a forced image, so the real forcing map is still to be constructed (codex). Verdict 'coincidence' = numbers match, no structural forcing yet.",
    )


if __name__ == "__main__":
    main()

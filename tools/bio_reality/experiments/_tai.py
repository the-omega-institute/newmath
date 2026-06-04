"""Modeled tAI helpers for BioReality experiments.

The functions in this module compute a bounded, copy-number based tAI contact.
They do not turn tRNA gene copy counts into measured translation efficiency.
"""

from __future__ import annotations

import math
import re
from collections import Counter


RNA_COMPLEMENT = {"A": "U", "U": "A", "C": "G", "G": "C"}

AA_ONE_TO_THREE = {
    "A": "Ala",
    "R": "Arg",
    "N": "Asn",
    "D": "Asp",
    "C": "Cys",
    "Q": "Gln",
    "E": "Glu",
    "G": "Gly",
    "H": "His",
    "I": "Ile",
    "L": "Leu",
    "K": "Lys",
    "M": "Met",
    "F": "Phe",
    "P": "Pro",
    "S": "Ser",
    "T": "Thr",
    "W": "Trp",
    "Y": "Tyr",
    "V": "Val",
}

AA_ALIASES = {
    "fMet": "Met",
    "iMet": "Met",
    "Ile2": "Ile",
}

WOBBLE_S = {
    ("G", "U"): 0.41,
    ("U", "G"): 0.68,
    ("I", "C"): 0.28,
    ("I", "A"): 0.9999,
    ("I", "U"): 0.0,
    ("L", "A"): 0.89,
}

HEADER_RE = re.compile(r"tRNA-([A-Za-z0-9]+)-([ACGTU]{3})")
FALLBACK_RE = re.compile(r"\)\s+([A-Za-z0-9]+)\s+\(([ACGTU]{3})\)")


def dna_to_rna(text: str) -> str:
    return text.upper().replace("T", "U")


def normalize_aa(label: str) -> str:
    return AA_ALIASES.get(label, label)


def parse_gtrnadb_fasta(raw_payload_text: str) -> list[dict[str, str]]:
    records = []
    for line in raw_payload_text.splitlines():
        if not line.startswith(">"):
            continue
        match = HEADER_RE.search(line) or FALLBACK_RE.search(line)
        if match is None:
            records.append(
                {
                    "header": line,
                    "aa_label": "",
                    "aa": "",
                    "anticodon": "",
                    "matched": False,
                }
            )
            continue
        aa_label = match.group(1)
        records.append(
            {
                "header": line,
                "aa_label": aa_label,
                "aa": normalize_aa(aa_label),
                "anticodon": dna_to_rna(match.group(2)),
                "matched": True,
            }
        )
    return records


def anticodon_copy_counts(records: list[dict[str, str]]) -> dict[str, int]:
    counts: Counter[str] = Counter()
    for record in records:
        anticodon = record.get("anticodon", "")
        if anticodon:
            counts[anticodon] += 1
    return dict(sorted(counts.items()))


def aa_anticodon_copy_counts(records: list[dict[str, str]]) -> dict[tuple[str, str, str], int]:
    counts: Counter[tuple[str, str, str]] = Counter()
    for record in records:
        aa = record.get("aa", "")
        anticodon = record.get("anticodon", "")
        aa_label = record.get("aa_label", "")
        if aa and anticodon:
            counts[(aa, aa_label, anticodon)] += 1
    return dict(counts)


def aa_coverage(records: list[dict[str, str]]) -> dict[str, int]:
    counts: Counter[str] = Counter()
    for record in records:
        aa = record.get("aa", "")
        if aa:
            counts[aa] += 1
    return dict(sorted(counts.items()))


def has_full_standard_aa_coverage(records: list[dict[str, str]]) -> bool:
    present = set(aa_coverage(records))
    return set(AA_ONE_TO_THREE.values()).issubset(present)


def first_two_positions_match(codon: str, anticodon: str) -> bool:
    return (
        RNA_COMPLEMENT.get(anticodon[2]) == codon[0]
        and RNA_COMPLEMENT.get(anticodon[1]) == codon[1]
    )


def effective_wobble_base(aa_label: str, anticodon: str, organism: str) -> str:
    wobble = anticodon[0]
    if aa_label == "Ile2" and anticodon == "CAU" and organism == "escherichia_coli_k12":
        return "L"
    if wobble == "A":
        return "I"
    return wobble


def wobble_penalty(wobble: str, codon_third: str) -> float | None:
    if RNA_COMPLEMENT.get(wobble) == codon_third:
        return 0.0
    return WOBBLE_S.get((wobble, codon_third))


def codon_w_values(
    *,
    organism: str,
    code: dict[str, str],
    records: list[dict[str, str]],
    codons: list[str],
) -> tuple[dict[str, float], dict[str, float], list[dict[str, object]]]:
    copy_counts = aa_anticodon_copy_counts(records)
    raw_w: dict[str, float] = {}
    contributors: list[dict[str, object]] = []
    for codon in codons:
        aa = AA_ONE_TO_THREE[code[codon]]
        total = 0.0
        codon_contributors = []
        for (record_aa, aa_label, anticodon), copy in copy_counts.items():
            if record_aa != aa:
                continue
            if not first_two_positions_match(codon, anticodon):
                continue
            wobble = effective_wobble_base(aa_label, anticodon, organism)
            penalty = wobble_penalty(wobble, codon[2])
            if penalty is None:
                continue
            contribution = (1.0 - penalty) * copy
            if contribution <= 0.0:
                continue
            total += contribution
            codon_contributors.append(
                {
                    "aa_label": aa_label,
                    "anticodon": anticodon,
                    "effective_wobble_base": wobble,
                    "copy": copy,
                    "s": penalty,
                    "contribution": contribution,
                }
            )
        raw_w[codon] = total
        if codon_contributors:
            contributors.append({"codon": codon, "contributors": codon_contributors})

    max_w = max(raw_w.values()) if raw_w else 0.0
    if max_w <= 0.0:
        raise ValueError(f"{organism} has no nonzero tAI W values")
    normalized = {codon: value / max_w for codon, value in raw_w.items()}
    nonzero = [value for value in normalized.values() if value > 0.0]
    if not nonzero:
        raise ValueError(f"{organism} has no nonzero normalized tAI values")
    fallback = math.exp(sum(math.log(value) for value in nonzero) / len(nonzero))
    w_values = {
        codon: (value if value > 0.0 else fallback)
        for codon, value in normalized.items()
    }
    return w_values, raw_w, contributors

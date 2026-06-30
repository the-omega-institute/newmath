#!/usr/bin/env python3
"""Codon-E1 frame-shift MPRA translation-dependent functional certificate.

This is intentionally stdlib-only: the daemon environment used for this
certificate has no numpy/pandas/scipy.  The codon-E1 projector construction
matches the local pure-Python experiments in this directory.  Yeast CSC is
computed from the in-repo S. cerevisiae half-life/CDS tables by the published
CSC definition, namely per-codon Pearson correlation between codon frequency
and mRNA half-life across genes (Presnyak et al. 2015 / Coller lineage).
"""
from __future__ import annotations

from collections import defaultdict
from itertools import product
import hashlib
import json
import math
from pathlib import Path
import random
import sys


EXPERIMENT_ID = "codon_e1_frameshift_mpra_tcausal"
CLAIM_ID = "bridge.genetic_code.codon_e1_frameshift_mpra_translation_dependent_function"

BASES = ("U", "C", "A", "G")
DINUCLEOTIDES = tuple(a + b for a in BASES for b in BASES)
N_NULL = 100000
N_BOOTSTRAP = 10000
TOL = 1.0e-12
MGS_TOL = 1.0e-10
ESTIMABILITY_MIN_NORM_FRAC = 1.0e-6
NULL_SEED = "codon_e1_frameshift_mpra_tcausal.synonymous_v_star_permutation"
BOOTSTRAP_SEED = "codon_e1_frameshift_mpra_tcausal.two_stage_cluster_bootstrap"
CSC_GATE_NULL_SEED = "codon_e1_frameshift_mpra_tcausal.csc_gate_synonymous_permutation"

BASE_CONTROL_NAMES = [
    "csc_pair_inframe",
    "csc_pair_frameshift",
    "tai_pair_inframe",
    "tai_pair_frameshift",
    "log1p_barcodes_inframe",
    "log1p_barcodes_frameshift",
    "log1p_min_barcodes",
    "baseline_inframe_gc_fraction",
    "baseline_frameshift_gc_fraction",
    "baseline_inframe_gc3_fraction",
    "baseline_frameshift_gc3_fraction",
]
GC_CONTROL_NAMES = [
    "pair_gc_fraction",
    "pair_gc3_fraction",
    *[f"dinucleotide_{dinuc}_count" for dinuc in DINUCLEOTIDES],
]

CODON_TO_AA = {
    "UUU": "F", "UUC": "F", "UUA": "L", "UUG": "L",
    "UCU": "S", "UCC": "S", "UCA": "S", "UCG": "S",
    "UAU": "Y", "UAC": "Y", "UAA": "*", "UAG": "*",
    "UGU": "C", "UGC": "C", "UGA": "*", "UGG": "W",
    "CUU": "L", "CUC": "L", "CUA": "L", "CUG": "L",
    "CCU": "P", "CCC": "P", "CCA": "P", "CCG": "P",
    "CAU": "H", "CAC": "H", "CAA": "Q", "CAG": "Q",
    "CGU": "R", "CGC": "R", "CGA": "R", "CGG": "R",
    "AUU": "I", "AUC": "I", "AUA": "I", "AUG": "M",
    "ACU": "T", "ACC": "T", "ACA": "T", "ACG": "T",
    "AAU": "N", "AAC": "N", "AAA": "K", "AAG": "K",
    "AGU": "S", "AGC": "S", "AGA": "R", "AGG": "R",
    "GUU": "V", "GUC": "V", "GUA": "V", "GUG": "V",
    "GCU": "A", "GCC": "A", "GCA": "A", "GCG": "A",
    "GAU": "D", "GAC": "D", "GAA": "E", "GAG": "E",
    "GGU": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}

AA_ONE_TO_THREE = {
    "A": "Ala", "R": "Arg", "N": "Asn", "D": "Asp", "C": "Cys",
    "Q": "Gln", "E": "Glu", "G": "Gly", "H": "His", "I": "Ile",
    "L": "Leu", "K": "Lys", "M": "Met", "F": "Phe", "P": "Pro",
    "S": "Ser", "T": "Thr", "W": "Trp", "Y": "Tyr", "V": "Val",
}

RNA_COMPLEMENT = {"A": "U", "U": "A", "C": "G", "G": "C"}
WOBBLE_S = {
    ("G", "U"): 0.41,
    ("U", "G"): 0.68,
    ("I", "C"): 0.28,
    ("I", "A"): 0.9999,
    ("I", "U"): 0.0,
    ("L", "A"): 0.89,
}


def repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def round_float(value: float | None, digits: int = 12) -> float | None:
    if value is None:
        return None
    if not math.isfinite(value):
        return None
    rounded = round(value, digits)
    return 0.0 if rounded == -0.0 else rounded


def emit(status: str, **fields: object) -> None:
    payload = {"status": status}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":"), allow_nan=False))
    if status in {"certified", "coincidence"}:
        sys.exit(0)
    if status == "refuted":
        sys.exit(2)
    sys.exit(3)


def stable_seed(text: str) -> int:
    return int.from_bytes(hashlib.sha256(text.encode("utf-8")).digest()[:16], "big")


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def percentile(values: list[float], q: float) -> float:
    ordered = sorted(values)
    if not ordered:
        return math.nan
    pos = (len(ordered) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return ordered[lo]
    return ordered[lo] * (hi - pos) + ordered[hi] * (pos - lo)


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def vector_norm(vector: list[float]) -> float:
    return math.sqrt(dot(vector, vector))


def weighted_dot(left: list[float], right: list[float], weights: list[float]) -> float:
    return sum(w * a * b for a, b, w in zip(left, right, weights))


def weighted_norm(vector: list[float], weights: list[float]) -> float:
    return math.sqrt(max(0.0, weighted_dot(vector, vector, weights)))


def weighted_corr(left: list[float], right: list[float], weights: list[float]) -> float:
    ln = weighted_norm(left, weights)
    rn = weighted_norm(right, weights)
    if ln <= TOL or rn <= TOL:
        return math.nan
    return weighted_dot(left, right, weights) / (ln * rn)


def codon_order() -> list[str]:
    return ["".join(parts) for parts in product(BASES, repeat=3)]


def sense_codon_order() -> list[str]:
    return [codon for codon in codon_order() if CODON_TO_AA[codon] != "*"]


def families_by_aa(codons: list[str]) -> dict[str, list[str]]:
    families: dict[str, list[str]] = defaultdict(list)
    for codon in codons:
        families[CODON_TO_AA[codon]].append(codon)
    return dict(families)


def modified_gram_schmidt(columns: list[list[float]], tol: float) -> list[list[float]]:
    basis: list[list[float]] = []
    for column in columns:
        working = column[:]
        for q in basis:
            coeff = dot(q, working)
            if coeff:
                for idx, q_value in enumerate(q):
                    working[idx] -= coeff * q_value
        norm = vector_norm(working)
        if norm <= tol:
            continue
        basis.append([value / norm for value in working])
    return basis


def base_orthonormal_characters() -> list[dict[str, float]]:
    return [
        {base: 0.5 for base in BASES},
        {"U": 1.0 / math.sqrt(2.0), "C": -1.0 / math.sqrt(2.0), "A": 0.0, "G": 0.0},
        {"U": 1.0 / math.sqrt(6.0), "C": 1.0 / math.sqrt(6.0), "A": -2.0 / math.sqrt(6.0), "G": 0.0},
        {"U": 1.0 / math.sqrt(12.0), "C": 1.0 / math.sqrt(12.0), "A": 1.0 / math.sqrt(12.0), "G": -3.0 / math.sqrt(12.0)},
    ]


def e1_character_basis(full_codons: list[str]) -> list[list[float]]:
    base_chars = base_orthonormal_characters()
    columns: list[list[float]] = []
    for labels in product(range(4), repeat=3):
        if sum(label != 0 for label in labels) != 1:
            continue
        columns.append(
            [
                base_chars[labels[0]][codon[0]]
                * base_chars[labels[1]][codon[1]]
                * base_chars[labels[2]][codon[2]]
                for codon in full_codons
            ]
        )
    return columns


def project_syn(vector: list[float], families: dict[str, list[str]], index: dict[str, int]) -> list[float]:
    result = vector[:]
    for family_codons in families.values():
        family_mean = sum(vector[index[codon]] for codon in family_codons) / len(family_codons)
        for codon in family_codons:
            result[index[codon]] -= family_mean
    return result


def build_b1_basis(
    full_codons: list[str],
    sense_codons: list[str],
    families: dict[str, list[str]],
    sense_index: dict[str, int],
) -> list[list[float]]:
    full_index = {codon: idx for idx, codon in enumerate(full_codons)}
    columns: list[list[float]] = []
    for full_column in e1_character_basis(full_codons):
        restricted = [full_column[full_index[codon]] for codon in sense_codons]
        columns.append(project_syn(restricted, families, sense_index))
    return modified_gram_schmidt(columns, MGS_TOL)


def project_basis(vector: list[float], q_basis: list[list[float]]) -> list[float]:
    out = [0.0 for _ in vector]
    for q in q_basis:
        coeff = dot(vector, q)
        if coeff:
            for idx, q_value in enumerate(q):
                out[idx] += coeff * q_value
    return out


def organism_name(entry: dict[str, object]) -> str:
    for key in ("assembly_organism_name", "organism", "organism_slug"):
        value = entry.get(key)
        if isinstance(value, str) and value:
            return value
    return ""


def organism_genus(entry: dict[str, object]) -> str:
    value = entry.get("genus")
    if isinstance(value, str) and value:
        return value.lower()
    name = organism_name(entry).strip()
    return name.split()[0].lower() if name else "unknown"


def is_scerevisiae(entry: dict[str, object]) -> bool:
    text = " ".join(str(entry.get(key, "")) for key in ("organism", "assembly_organism_name", "organism_slug")).lower()
    return "saccharomyces cerevisiae" in text or "saccharomyces_cerevisiae" in text


def load_panel_organisms() -> list[dict[str, object]]:
    base = repo_root() / "tools" / "window_codon_bridge" / "synced"
    organisms: list[dict[str, object]] = []
    for filename in ("codon_e1_heldout_panel.json", "codon_e1_transport_panel.json"):
        with (base / filename).open("r", encoding="utf-8") as handle:
            data = json.load(handle)
        for entry in data["organisms"]:
            item = dict(entry)
            item["_panel_file"] = filename
            organisms.append(item)
    return organisms


def organism_residual(
    entry: dict[str, object],
    sense_codons: list[str],
    families: dict[str, list[str]],
    sense_index: dict[str, int],
) -> list[float] | None:
    counts = entry.get("codon_counts_rna")
    if not isinstance(counts, dict):
        return None
    total_value = entry.get("total_sense_codons", entry.get("total_sense"))
    total = int(total_value) if total_value is not None else sum(int(counts.get(codon, 0)) for codon in sense_codons)
    if total <= 0:
        return None
    raw = [float(counts[codon]) / total for codon in sense_codons]
    return project_syn(raw, families, sense_index)


def build_v_star(
    sense_codons: list[str],
    families: dict[str, list[str]],
    sense_index: dict[str, int],
    q_basis: list[list[float]],
) -> tuple[dict[str, float], dict[str, object]]:
    by_genus: dict[str, list[list[float]]] = defaultdict(list)
    excluded_scerevisiae = []
    used_organisms = []
    for entry in load_panel_organisms():
        if is_scerevisiae(entry):
            excluded_scerevisiae.append(organism_name(entry))
            continue
        residual = organism_residual(entry, sense_codons, families, sense_index)
        if residual is None:
            continue
        projected = project_basis(residual, q_basis)
        norm = vector_norm(projected)
        if norm <= TOL:
            continue
        normalized = [value / norm for value in projected]
        by_genus[organism_genus(entry)].append(normalized)
        used_organisms.append(organism_name(entry))

    genus_vectors: list[list[float]] = []
    for genus in sorted(by_genus):
        vectors = by_genus[genus]
        genus_vectors.append([sum(vector[idx] for vector in vectors) / len(vectors) for idx in range(len(sense_codons))])
    if not genus_vectors:
        raise ValueError("v_star undefined: no usable non-yeast organisms")
    consensus = [sum(vector[idx] for vector in genus_vectors) / len(genus_vectors) for idx in range(len(sense_codons))]
    consensus = project_basis(consensus, q_basis)
    norm = vector_norm(consensus)
    if norm <= TOL:
        raise ValueError("v_star undefined: consensus E1 vector has zero norm")
    consensus = [value / norm for value in consensus]

    reference = "AAA" if "AAA" in sense_index else sense_codons[0]
    if consensus[sense_index[reference]] < 0.0:
        consensus = [-value for value in consensus]

    return (
        {codon: consensus[sense_index[codon]] for codon in sense_codons},
        {
            "n_non_yeast_organisms": len(used_organisms),
            "n_genus_weighted_groups": len(genus_vectors),
            "excluded_scerevisiae_entries": excluded_scerevisiae,
            "reference_sign_codon": reference,
            "rank_B1": len(q_basis),
        },
    )


def translate_pair(codon_a: str, codon_b: str) -> str:
    return CODON_TO_AA[codon_a] + CODON_TO_AA[codon_b]


def frameshift_codons(codon_a: str, codon_b: str) -> tuple[str, str]:
    seq = codon_a + codon_b + codon_a[:2]
    return seq[1:4], seq[4:7]


def pair_score(codon_a: str, codon_b: str, values: dict[str, float]) -> float:
    return 0.5 * (values[codon_a] + values[codon_b])


def pair_score_frameshift(codon_a: str, codon_b: str, values: dict[str, float]) -> float:
    f1, f2 = frameshift_codons(codon_a, codon_b)
    return 0.5 * (values[f1] + values[f2])


def gc_fraction(codons: tuple[str, str]) -> float:
    seq = "".join(codons)
    return sum(base in {"G", "C"} for base in seq) / len(seq)


def third_gc_fraction(codons: tuple[str, str]) -> float:
    return sum(codon[2] in {"G", "C"} for codon in codons) / len(codons)


def dinucleotide_counts(codons: tuple[str, str]) -> list[float]:
    seq = "".join(codons)
    counts = {dinuc: 0.0 for dinuc in DINUCLEOTIDES}
    for idx in range(len(seq) - 1):
        counts[seq[idx : idx + 2]] += 1.0
    return [counts[dinuc] for dinuc in DINUCLEOTIDES]


def gc_control_values(codons: tuple[str, str]) -> list[float]:
    return [
        gc_fraction(codons),
        third_gc_fraction(codons),
        *dinucleotide_counts(codons),
    ]


def load_reporter_rows(v_star: dict[str, float], csc: dict[str, float], tai: dict[str, float]) -> list[dict[str, object]]:
    path = repo_root() / "tools" / "window_codon_bridge" / "synced" / "chen2023_codon_pair_mrna_effects.json"
    with path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)

    rows: list[dict[str, object]] = []
    for key, value in data.items():
        if key.startswith("_"):
            continue
        if not isinstance(value, dict):
            continue
        y_in = value.get("y_inframe")
        y_fs = value.get("y_frameshift")
        if y_in is None or y_fs is None:
            continue
        codon_a, codon_b = key.split("_")
        if CODON_TO_AA.get(codon_a) == "*" or CODON_TO_AA.get(codon_b) == "*":
            continue
        fs_a, fs_b = frameshift_codons(codon_a, codon_b)
        if CODON_TO_AA.get(fs_a) == "*" or CODON_TO_AA.get(fs_b) == "*":
            continue
        n_in = int(value.get("n_barcodes_inframe", 0))
        n_fs = int(value.get("n_barcodes_frameshift", 0))
        weight = float(max(1, min(n_in, n_fs)))
        rows.append(
            {
                "key": key,
                "codons": (codon_a, codon_b),
                "fs_codons": (fs_a, fs_b),
                "delta_y": float(y_in) - float(y_fs),
                "s": pair_score(codon_a, codon_b, v_star),
                "csc_pair": pair_score(codon_a, codon_b, csc),
                "weight": weight,
                "strata": translate_pair(codon_a, codon_b),
                "fixed_groups": (
                    "in:" + translate_pair(codon_a, codon_b),
                    "fs:" + translate_pair(fs_a, fs_b),
                ),
                "base_controls": [
                    pair_score(codon_a, codon_b, csc),
                    pair_score_frameshift(codon_a, codon_b, csc),
                    pair_score(codon_a, codon_b, tai),
                    pair_score_frameshift(codon_a, codon_b, tai),
                    math.log1p(n_in),
                    math.log1p(n_fs),
                    math.log1p(min(n_in, n_fs)),
                    gc_fraction((codon_a, codon_b)),
                    gc_fraction((fs_a, fs_b)),
                    third_gc_fraction((codon_a, codon_b)),
                    third_gc_fraction((fs_a, fs_b)),
                ],
                "gc_controls": gc_control_values((codon_a, codon_b)),
            }
        )
    return rows


def weighted_demean_by_group(values: list[float], weights: list[float], groups: list[str]) -> list[float]:
    totals: dict[str, float] = defaultdict(float)
    wtotals: dict[str, float] = defaultdict(float)
    for value, weight, group in zip(values, weights, groups):
        totals[group] += weight * value
        wtotals[group] += weight
    means = {group: totals[group] / wtotals[group] for group in totals if wtotals[group] > 0.0}
    return [value - means[group] for value, group in zip(values, groups)]


def weighted_orthonormalize_columns(columns: list[list[float]], weights: list[float]) -> list[list[float]]:
    basis: list[list[float]] = []
    for column in columns:
        working = column[:]
        for q in basis:
            coeff = weighted_dot(working, q, weights)
            if coeff:
                for idx, q_value in enumerate(q):
                    working[idx] -= coeff * q_value
        norm = weighted_norm(working, weights)
        if norm <= 1.0e-9:
            continue
        basis.append([value / norm for value in working])
    return basis


def row_control_values(row: dict[str, object], include_gc_controls: bool) -> list[float]:
    values = list(row["base_controls"])  # type: ignore[arg-type]
    if include_gc_controls:
        values.extend(row["gc_controls"])  # type: ignore[arg-type]
    return [float(value) for value in values]


def residualizer(
    rows: list[dict[str, object]],
    indices: list[int] | None = None,
    include_gc_controls: bool = False,
    excluded_control_names: set[str] | None = None,
):
    if indices is None:
        selected = list(range(len(rows)))
    else:
        selected = indices
    weights = [float(rows[idx]["weight"]) for idx in selected]
    fixed_groups_by_axis = [
        [str(rows[idx]["fixed_groups"][axis]) for idx in selected]  # type: ignore[index]
        for axis in range(2)
    ]
    names = BASE_CONTROL_NAMES + (GC_CONTROL_NAMES if include_gc_controls else [])
    excluded = excluded_control_names or set()
    selected_controls = [row_control_values(rows[idx], include_gc_controls) for idx in selected]
    raw_control_columns = [
        [
            control_values[ctrl]
            for control_values in selected_controls
        ]
        for ctrl, name in enumerate(names)
        if name not in excluded
    ]

    def absorb_fixed(vector: list[float]) -> list[float]:
        out = vector[:]
        for groups in fixed_groups_by_axis:
            out = weighted_demean_by_group(out, weights, groups)
        return out

    control_columns = [absorb_fixed(column) for column in raw_control_columns]
    q_controls = weighted_orthonormalize_columns(control_columns, weights)

    def apply(vector: list[float]) -> list[float]:
        out = absorb_fixed(vector)
        for q in q_controls:
            coeff = weighted_dot(out, q, weights)
            if coeff:
                for idx, q_value in enumerate(q):
                    out[idx] -= coeff * q_value
        return out

    return apply, weights, len(q_controls)


def pearson(left: list[float], right: list[float]) -> float:
    if len(left) != len(right) or len(left) < 3:
        return math.nan
    lm = mean(left)
    rm = mean(right)
    lc = [value - lm for value in left]
    rc = [value - rm for value in right]
    denom = vector_norm(lc) * vector_norm(rc)
    if denom <= TOL:
        return math.nan
    return dot(lc, rc) / denom


def load_csc_values(sense_codons: list[str]) -> tuple[dict[str, float], dict[str, object]]:
    base = repo_root() / "tools" / "bio_reality" / "data"
    with (base / "mrna_half_life_saccharomyces_cerevisiae_neymotin.json").open("r", encoding="utf-8") as handle:
        half_life_data = json.load(handle)
    with (base / "cds_ordered_sequences_saccharomyces_cerevisiae.json").open("r", encoding="utf-8") as handle:
        cds_data = json.load(handle)

    half_life_by_gene = {
        str(record["Syst"]).upper(): float(record["thalf"])
        for record in half_life_data["records"]
        if float(record.get("thalf", 0.0)) > 0.0
    }
    rows: list[tuple[float, dict[str, float]]] = []
    for record in cds_data["cds"]:
        gene_id = str(record["gene_id"]).upper()
        if gene_id not in half_life_by_gene:
            continue
        codons = [str(codon).replace("T", "U") for codon in record["codons"]]
        sense = [codon for codon in codons if codon in CODON_TO_AA and CODON_TO_AA[codon] != "*"]
        if len(sense) < 30:
            continue
        counts: dict[str, int] = defaultdict(int)
        for codon in sense:
            counts[codon] += 1
        total = float(len(sense))
        freqs = {codon: counts.get(codon, 0) / total for codon in sense_codons}
        rows.append((math.log(half_life_by_gene[gene_id]), freqs))

    if len(rows) < 100:
        raise ValueError("cannot compute yeast CSC: too few joined half-life/CDS rows")
    half_lives = [row[0] for row in rows]
    csc = {codon: pearson([freqs[codon] for _, freqs in rows], half_lives) for codon in sense_codons}
    if any(not math.isfinite(value) for value in csc.values()):
        raise ValueError("cannot compute yeast CSC: nonfinite codon correlation")
    return csc, {"source": "Neymotin2014_half_life_plus_RefSeq_CDS_Presnyak_CSC_definition", "n_joined_genes": len(rows)}


def parse_trna_records(raw_payload_text: str) -> list[dict[str, str]]:
    records = []
    for line in raw_payload_text.splitlines():
        if not line.startswith(">"):
            continue
        aa = ""
        anticodon = ""
        marker = "_tRNA-"
        if marker in line:
            suffix = line.split(marker, 1)[1]
            parts = suffix.split("-", 2)
            if len(parts) >= 2:
                aa = parts[0]
                anticodon = parts[1].upper().replace("T", "U")
        if not aa or not anticodon:
            tokens = line.replace("(", " ").replace(")", " ").split()
            for idx in range(len(tokens) - 1):
                if tokens[idx] in set(AA_ONE_TO_THREE.values()) and len(tokens[idx + 1]) == 3:
                    aa = tokens[idx]
                    anticodon = tokens[idx + 1].upper().replace("T", "U")
                    break
        if aa and anticodon:
            records.append({"aa": aa, "anticodon": anticodon})
    return records


def first_two_positions_match(codon: str, anticodon: str) -> bool:
    return RNA_COMPLEMENT.get(anticodon[2]) == codon[0] and RNA_COMPLEMENT.get(anticodon[1]) == codon[1]


def wobble_penalty(wobble: str, codon_third: str) -> float | None:
    if RNA_COMPLEMENT.get(wobble) == codon_third:
        return 0.0
    return WOBBLE_S.get((wobble, codon_third))


def load_tai_values(sense_codons: list[str]) -> tuple[dict[str, float], dict[str, object]]:
    path = repo_root() / "tools" / "bio_reality" / "data" / "gtrnadb_trna_all_copy_saccharomyces_cerevisiae.json"
    with path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    records = parse_trna_records(str(payload["raw_payload_text"]))
    copy_counts: dict[tuple[str, str], int] = defaultdict(int)
    for record in records:
        copy_counts[(record["aa"], record["anticodon"])] += 1

    raw_w: dict[str, float] = {}
    for codon in sense_codons:
        aa = AA_ONE_TO_THREE[CODON_TO_AA[codon]]
        total = 0.0
        for (record_aa, anticodon), copy in copy_counts.items():
            if record_aa != aa or not first_two_positions_match(codon, anticodon):
                continue
            wobble = "I" if anticodon[0] == "A" else anticodon[0]
            penalty = wobble_penalty(wobble, codon[2])
            if penalty is None:
                continue
            contribution = (1.0 - penalty) * copy
            if contribution > 0.0:
                total += contribution
        raw_w[codon] = total
    max_w = max(raw_w.values())
    if max_w <= 0.0:
        raise ValueError("cannot compute yeast tAI: no nonzero W values")
    normalized = {codon: value / max_w for codon, value in raw_w.items()}
    nonzero = [value for value in normalized.values() if value > 0.0]
    fallback = math.exp(sum(math.log(value) for value in nonzero) / len(nonzero))
    tai = {codon: (value if value > 0.0 else fallback) for codon, value in normalized.items()}
    return tai, {"source": "GtRNAdb_Scere3_copy_counts_dos_Reis_wobble_weights", "n_trna_records": len(records)}


def family_permutation(families: dict[str, list[str]], rng: random.Random) -> dict[str, str]:
    permutation: dict[str, str] = {}
    for family_codons in families.values():
        shuffled = family_codons[:]
        rng.shuffle(shuffled)
        for source, target in zip(family_codons, shuffled):
            permutation[source] = target
    return permutation


def permuted_values(values: dict[str, float], permutation: dict[str, str]) -> dict[str, float]:
    return {target: values[source] for source, target in permutation.items()}


def feature_columns(
    rows: list[dict[str, object]],
    sense_codons: list[str],
    sense_index: dict[str, int],
) -> list[list[float]]:
    columns = [[0.0 for _ in rows] for _ in sense_codons]
    for row_idx, row in enumerate(rows):
        codon_a, codon_b = row["codons"]  # type: ignore[misc]
        columns[sense_index[codon_a]][row_idx] += 0.5
        columns[sense_index[codon_b]][row_idx] += 0.5
    return columns


def residual_feature_quadratic(
    rows: list[dict[str, object]],
    sense_codons: list[str],
    sense_index: dict[str, int],
    apply_resid,
    delta_resid: list[float],
    weights: list[float],
) -> tuple[list[float], list[list[float]], float]:
    residual_features = [apply_resid(column) for column in feature_columns(rows, sense_codons, sense_index)]
    h = [weighted_dot(delta_resid, column, weights) for column in residual_features]
    gram: list[list[float]] = []
    for left in residual_features:
        gram.append([weighted_dot(left, right, weights) for right in residual_features])
    delta_norm = weighted_norm(delta_resid, weights)
    return h, gram, delta_norm


def vector_from_values(values: dict[str, float], sense_codons: list[str]) -> list[float]:
    return [values[codon] for codon in sense_codons]


def corr_from_feature_quadratic(
    values_vector: list[float],
    h: list[float],
    gram: list[list[float]],
    delta_norm: float,
) -> float:
    numerator = dot(values_vector, h)
    norm_sq = 0.0
    for i, vi in enumerate(values_vector):
        if vi == 0.0:
            continue
        row = gram[i]
        norm_sq += vi * sum(row[j] * values_vector[j] for j in range(len(values_vector)))
    denom = delta_norm * math.sqrt(max(0.0, norm_sq))
    if denom <= TOL:
        return math.nan
    return numerator / denom


def permuted_vector(values_vector: list[float], permutation_indices: list[int]) -> list[float]:
    out = [0.0 for _ in values_vector]
    for source_idx, target_idx in enumerate(permutation_indices):
        out[target_idx] = values_vector[source_idx]
    return out


def family_permutation_indices(
    families: dict[str, list[str]],
    sense_index: dict[str, int],
    rng: random.Random,
) -> list[int]:
    indices = list(range(len(sense_index)))
    for family_codons in families.values():
        shuffled = family_codons[:]
        rng.shuffle(shuffled)
        for source, target in zip(family_codons, shuffled):
            indices[sense_index[source]] = sense_index[target]
    return indices


def two_sided_family_perm_p(
    observed: float,
    values: dict[str, float],
    families: dict[str, list[str]],
    sense_codons: list[str],
    sense_index: dict[str, int],
    h: list[float],
    gram: list[list[float]],
    delta_norm: float,
    n_null: int,
    seed: str,
) -> float:
    rng = random.Random(stable_seed(seed))
    values_vector = vector_from_values(values, sense_codons)
    ge = 0
    observed_abs = abs(observed)
    for _ in range(n_null):
        p_vector = permuted_vector(values_vector, family_permutation_indices(families, sense_index, rng))
        t_perm = corr_from_feature_quadratic(p_vector, h, gram, delta_norm)
        if math.isfinite(t_perm) and abs(t_perm) >= observed_abs:
            ge += 1
    return (1 + ge) / (1 + n_null)


def one_sided_family_perm_p(
    observed: float,
    values: dict[str, float],
    families: dict[str, list[str]],
    sense_codons: list[str],
    sense_index: dict[str, int],
    h: list[float],
    gram: list[list[float]],
    delta_norm: float,
    n_null: int,
    seed: str,
) -> float:
    rng = random.Random(stable_seed(seed))
    values_vector = vector_from_values(values, sense_codons)
    ge = 0
    for _ in range(n_null):
        p_vector = permuted_vector(values_vector, family_permutation_indices(families, sense_index, rng))
        t_perm = corr_from_feature_quadratic(p_vector, h, gram, delta_norm)
        if math.isfinite(t_perm) and t_perm >= observed:
            ge += 1
    return (1 + ge) / (1 + n_null)


def bootstrap_ci95(
    rows: list[dict[str, object]],
    delta_resid: list[float],
    score_resid: list[float],
    weights: list[float],
    seed: str,
) -> tuple[float, float]:
    by_strata: dict[str, list[int]] = defaultdict(list)
    for idx, row in enumerate(rows):
        by_strata[str(row["strata"])].append(idx)
    strata = sorted(by_strata)
    rng = random.Random(stable_seed(seed))
    values: list[float] = []
    for _ in range(N_BOOTSTRAP):
        indices: list[int] = []
        for _ in range(len(strata)):
            stratum = rng.choice(strata)
            members = by_strata[stratum]
            for _ in range(len(members)):
                indices.append(rng.choice(members))
        if len(set(str(rows[idx]["strata"]) for idx in indices)) < 3:
            continue
        b_delta = [delta_resid[idx] for idx in indices]
        b_score = [score_resid[idx] for idx in indices]
        b_weights = [weights[idx] for idx in indices]
        corr = weighted_corr(b_delta, b_score, b_weights)
        if math.isfinite(corr):
            values.append(corr)
    return percentile(values, 0.025), percentile(values, 0.975)


def statistic_for_controls(
    rows: list[dict[str, object]],
    v_star: dict[str, float],
    families: dict[str, list[str]],
    sense_codons: list[str],
    sense_index: dict[str, int],
    include_gc_controls: bool,
    seed_suffix: str,
) -> dict[str, object]:
    apply_resid, weights, n_control_rank = residualizer(rows, include_gc_controls=include_gc_controls)
    delta = [float(row["delta_y"]) for row in rows]
    score = [float(row["s"]) for row in rows]
    delta_resid = apply_resid(delta)
    score_resid = apply_resid(score)
    score_raw_norm = weighted_norm(score, weights)
    score_resid_norm = weighted_norm(score_resid, weights)
    s_norm_frac = score_resid_norm / score_raw_norm if score_raw_norm > TOL else math.nan
    t_causal = weighted_corr(delta_resid, score_resid, weights)
    h, gram, delta_norm = residual_feature_quadratic(rows, sense_codons, sense_index, apply_resid, delta_resid, weights)
    if not math.isfinite(t_causal) or not math.isfinite(s_norm_frac) or s_norm_frac <= ESTIMABILITY_MIN_NORM_FRAC:
        p_two = math.nan
        ci_low = math.nan
        ci_high = math.nan
    else:
        p_two = two_sided_family_perm_p(
            t_causal,
            v_star,
            families,
            sense_codons,
            sense_index,
            h,
            gram,
            delta_norm,
            N_NULL,
            f"{NULL_SEED}.{seed_suffix}.two_sided",
        )
        ci_low, ci_high = bootstrap_ci95(
            rows,
            delta_resid,
            score_resid,
            weights,
            f"{BOOTSTRAP_SEED}.{seed_suffix}",
        )
    return {
        "T_causal": t_causal,
        "p_two": p_two,
        "bootstrap_ci_low": ci_low,
        "bootstrap_ci_high": ci_high,
        "s_residual_frac": s_norm_frac,
        "n_control_rank": n_control_rank,
    }


def csc_gate(
    rows: list[dict[str, object]],
    csc: dict[str, float],
    families: dict[str, list[str]],
    sense_codons: list[str],
    sense_index: dict[str, int],
) -> tuple[bool, float, float]:
    # Test CSC itself against the same frame/peptide/precision/composition/tAI
    # pipeline, excluding the CSC columns that would otherwise absorb the
    # positive-control score by construction.
    apply_resid, weights, _ = residualizer(
        rows,
        include_gc_controls=True,
        excluded_control_names={"csc_pair_inframe", "csc_pair_frameshift"},
    )
    delta_resid = apply_resid([float(row["delta_y"]) for row in rows])
    h, gram, delta_norm = residual_feature_quadratic(rows, sense_codons, sense_index, apply_resid, delta_resid, weights)
    score = [float(row["csc_pair"]) for row in rows]
    score_resid = apply_resid(score)
    corr = weighted_corr(delta_resid, score_resid, weights)
    if not math.isfinite(corr):
        return False, corr, math.nan
    # The assay readout is y_inframe - y_frameshift. Optimal/stabilizing codons
    # are expected to make this contrast less negative, hence positive CSC slope.
    p = one_sided_family_perm_p(
        corr,
        csc,
        families,
        sense_codons,
        sense_index,
        h,
        gram,
        delta_norm,
        min(N_NULL, 20000),
        CSC_GATE_NULL_SEED,
    )
    return corr > 0.0 and p <= 0.01, corr, p


def main() -> None:
    default_payload = {
        "T_causal": None,
        "p_two_without_gc": None,
        "p_two_with_gc": None,
        "abs_T": None,
        "bootstrap_ci_low": None,
        "bootstrap_ci_high": None,
        "csc_gate_passed": False,
        "csc_control_corr": None,
        "n_codon_pairs": 0,
        "s_residual_frac_without_gc": None,
        "s_residual_frac_with_gc": None,
        "gc_controls_added": GC_CONTROL_NAMES,
        "v_star_excludes_scerevisiae": False,
        "reason": "statistic did not run",
    }
    try:
        full_codons = codon_order()
        sense_codons = sense_codon_order()
        sense_index = {codon: idx for idx, codon in enumerate(sense_codons)}
        families = families_by_aa(sense_codons)
        q_basis = build_b1_basis(full_codons, sense_codons, families, sense_index)

        v_star, v_meta = build_v_star(sense_codons, families, sense_index, q_basis)
        csc, csc_meta = load_csc_values(sense_codons)
        tai, tai_meta = load_tai_values(sense_codons)
        rows = load_reporter_rows(v_star, csc, tai)
        if len(rows) < 100:
            raise ValueError("too few codon pairs after non-null and stop filters")

        without_gc = statistic_for_controls(
            rows,
            v_star,
            families,
            sense_codons,
            sense_index,
            include_gc_controls=False,
            seed_suffix="without_gc",
        )
        with_gc = statistic_for_controls(
            rows,
            v_star,
            families,
            sense_codons,
            sense_index,
            include_gc_controls=True,
            seed_suffix="with_gc",
        )

        csc_passed, csc_corr, csc_p = csc_gate(
            rows,
            csc,
            families,
            sense_codons,
            sense_index,
        )

        t_without = float(without_gc["T_causal"])
        t_with = float(with_gc["T_causal"])
        p_without = float(without_gc["p_two"])
        p_with = float(with_gc["p_two"])
        ci_low = float(with_gc["bootstrap_ci_low"])
        ci_high = float(with_gc["bootstrap_ci_high"])
        s_frac_without = float(without_gc["s_residual_frac"])
        s_frac_with = float(with_gc["s_residual_frac"])
        with_gc_estimable = (
            math.isfinite(t_with)
            and math.isfinite(s_frac_with)
            and s_frac_with > ESTIMABILITY_MIN_NORM_FRAC
        )
        with_gc_significant = (
            math.isfinite(p_with)
            and p_with <= 0.01
            and math.isfinite(ci_low)
            and math.isfinite(ci_high)
            and (ci_low > 0.0 or ci_high < 0.0)
        )
        if not csc_passed:
            status = "needs_derivation"
            reason = "CSC positive-control gate failed under the augmented control matrix, so the reporter contrast is non-resolving."
        elif not with_gc_estimable:
            status = "needs_derivation"
            reason = "The codon-E1 pair score is absorbed by the augmented GC3+dinucleotide control matrix."
        elif with_gc_significant:
            status = "needs_derivation"
            reason = (
                "A sign-invariant codon-E1 association survives GC3+dinucleotide controls; exact Delta-MFE "
                "control is still missing, so this is an escalation target rather than a certificate."
            )
        else:
            status = "coincidence"
            reason = (
                "The apparent codon-E1 association collapses after GC3+dinucleotide sequence controls; "
                "the reporter result is consistent with a GC/RNA-folding composition confound, not a "
                "GC-orthogonal translation-dependent codon-E1 effect."
            )

        emit(
            status,
            T_causal=round_float(t_with),
            T_causal_without_gc=round_float(t_without),
            p_two_without_gc=round_float(p_without),
            p_two_with_gc=round_float(p_with),
            abs_T=round_float(abs(t_with)),
            abs_T_without_gc=round_float(abs(t_without)),
            bootstrap_ci_low=round_float(ci_low),
            bootstrap_ci_high=round_float(ci_high),
            bootstrap_ci_low_without_gc=round_float(float(without_gc["bootstrap_ci_low"])),
            bootstrap_ci_high_without_gc=round_float(float(without_gc["bootstrap_ci_high"])),
            csc_gate_passed=bool(csc_passed),
            csc_control_corr=round_float(csc_corr),
            csc_control_p=round_float(csc_p),
            n_codon_pairs=len(rows),
            s_residual_frac_without_gc=round_float(s_frac_without),
            s_residual_frac_with_gc=round_float(s_frac_with),
            gc_controls_added=GC_CONTROL_NAMES,
            v_star_excludes_scerevisiae=bool(v_meta["excluded_scerevisiae_entries"]),
            v_star_n_non_yeast_organisms=v_meta["n_non_yeast_organisms"],
            v_star_n_genus_weighted_groups=v_meta["n_genus_weighted_groups"],
            v_star_reference_sign_codon=v_meta["reference_sign_codon"],
            rank_B1=v_meta["rank_B1"],
            n_control_rank_without_gc=without_gc["n_control_rank"],
            n_control_rank_with_gc=with_gc["n_control_rank"],
            csc_source=csc_meta,
            tai_source=tai_meta,
            experiment_id=EXPERIMENT_ID,
            claim_id=CLAIM_ID,
            n_null=N_NULL,
            n_bootstrap=N_BOOTSTRAP,
            reason=reason,
        )
    except Exception as exc:
        emit(
            "needs_derivation",
            **{
                **default_payload,
                "reason": f"{type(exc).__name__}: {exc}",
                "experiment_id": EXPERIMENT_ID,
                "claim_id": CLAIM_ID,
            },
        )


if __name__ == "__main__":
    main()

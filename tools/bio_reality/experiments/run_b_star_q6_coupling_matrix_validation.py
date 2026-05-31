#!/usr/bin/env python3
"""B*_Q6 codon-residual coupling matrix validation."""

import json
import math
import pathlib
import sys


EXPERIMENT_ID = "b_star_q6_coupling_matrix_validation"
CLAIM_ID = "h3.codon_usage_topology.translation_survival.b_star_q6_coupling_matrix"
THRESHOLD = 0.01
ORGANISMS = ["homo_sapiens", "saccharomyces_cerevisiae", "escherichia_coli_k12"]

REQUIRED_DATA = [
    "tools/bio_reality/data/kazusa_codon_usage_homo_sapiens.json",
    "tools/bio_reality/data/kazusa_codon_usage_saccharomyces_cerevisiae.json",
    "tools/bio_reality/data/kazusa_codon_usage_escherichia_coli_k12.json",
    "tools/bio_reality/data/gtrnadb_trna_leu_copy_homo_sapiens.json",
    "tools/bio_reality/data/gtrnadb_trna_leu_copy_saccharomyces_cerevisiae.json",
    "tools/bio_reality/data/gtrnadb_trna_leu_copy_escherichia_coli_k12.json",
    "tools/bio_reality/data/ncbi_genetic_codes.json",
]

CUN_CODONS = ["CUU", "CUC", "CUA", "CUG"]
UUR_CODONS = ["UUA", "UUG"]
CUN_TRNA_ANTICODONS = ["UAG", "GAG", "CAG", "AAG"]
UUR_TRNA_ANTICODONS = ["CAA", "UAA"]
Q9_FAMILIES = [
    ["UUU", "UUC"], ["UUA", "UUG"], ["UCU", "UCC", "UCA", "UCG"],
    ["UAU", "UAC"], ["UGU", "UGC"], ["CUU", "CUC", "CUA", "CUG"],
    ["CCU", "CCC", "CCA", "CCG"], ["CAU", "CAC"], ["CAA", "CAG"],
    ["CGU", "CGC", "CGA", "CGG"], ["AUU", "AUC", "AUA"],
    ["ACU", "ACC", "ACA", "ACG"], ["AAU", "AAC"], ["AAA", "AAG"],
    ["AGU", "AGC"], ["AGA", "AGG"], ["GUU", "GUC", "GUA", "GUG"],
    ["GCU", "GCC", "GCA", "GCG"], ["GAU", "GAC"], ["GAA", "GAG"],
    ["GGU", "GGC", "GGA", "GGG"],
]


def emit(status, **kw):
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def numeric(value, field):
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{field} must be numeric")
    return float(value)


def standard_code(repo):
    raw = load_json(repo / "tools/bio_reality/data/ncbi_genetic_codes.json")
    table = next((item for item in raw.get("tables", []) if item.get("table_id") == 1), None)
    codons = raw.get("codon_order", [])
    if not isinstance(codons, list) or not isinstance(table, dict) or len(codons) != len(table.get("aa", "")):
        raise ValueError("NCBI standard genetic code table is missing or malformed")
    return {str(codon): aa for codon, aa in zip(codons, table["aa"])}


def fibers_for(code, codons):
    fibers = {}
    for codon in codons:
        fibers.setdefault(code[codon], []).append(codon)
    return fibers


def zero(codons):
    return {codon: 0.0 for codon in codons}


def project_syn(vector, fibers):
    out = dict(vector)
    for fiber in fibers.values():
        mean = sum(vector[codon] for codon in fiber) / len(fiber)
        for codon in fiber:
            out[codon] = vector[codon] - mean
    return out


def dot(left, right, codons):
    return sum(left[codon] * right[codon] for codon in codons)


def codon_residual(repo, organism, codons, fibers):
    raw = load_json(repo / f"tools/bio_reality/data/kazusa_codon_usage_{organism}.json")
    counts = raw.get("codon_counts")
    if not isinstance(counts, dict):
        raise ValueError(f"{organism} codon_counts object is missing")
    return project_syn({c: numeric(counts.get(c, 0), f"{organism}.{c}") for c in codons}, fibers)


def trna_leu_log_ratio(repo, organism):
    raw = load_json(repo / f"tools/bio_reality/data/gtrnadb_trna_leu_copy_{organism}.json")
    copies = raw.get("trna_leu_copies")
    if not isinstance(copies, dict):
        raise ValueError(f"{organism} trna_leu_copies object is missing")
    cun = sum(numeric(copies.get(a, 0), f"{organism}.{a}") for a in CUN_TRNA_ANTICODONS)
    uur = sum(numeric(copies.get(a, 0), f"{organism}.{a}") for a in UUR_TRNA_ANTICODONS)
    return math.log((cun + 0.5) / (uur + 0.5)), {"CUN_tRNA_Leu_copies": cun, "UUR_tRNA_Leu_copies": uur}


def centered_vectors(rows, codons):
    means = {c: sum(row[c] for row in rows) / len(rows) for c in codons}
    return [{c: row[c] - means[c] for c in codons} for row in rows]


def centered_scalars(values):
    mean = sum(values) / len(values)
    return [value - mean for value in values]


def covariance_apply_scalar(rows, values, codons):
    scale = 1.0 / (len(rows) - 1)
    return {c: scale * sum(rows[i][c] * values[i] for i in range(len(rows))) for c in codons}


def q_vectors(codons):
    raw = {}
    q = zero(codons); q["AAA"] = 1.0; q["AAG"] = -1.0; raw["K_AAA"] = q
    q = zero(codons)
    for c in ["AGA", "AGG"]: q[c] = 1.0
    for c in ["CGU", "CGC", "CGA", "CGG"]: q[c] = -0.25
    raw["Arg_AGR"] = q
    q = zero(codons); q["AUA"] = 1.0; q["AUU"] = -1.0; q["AUC"] = -1.0; raw["Ile_AUA"] = q
    q = zero(codons)
    for c in CUN_CODONS: q[c] = 0.25
    for c in UUR_CODONS: q[c] = -0.5
    raw["Leu_CUN_vs_UUR"] = q
    q = zero(codons); q["UUA"] = 1.0; q["UUG"] = -1.0; raw["Leu_UUA_vs_UUG"] = q
    q = zero(codons)
    for c in ["UCA", "UCG"]: q[c] = 0.5
    for c in ["AGU", "AGC"]: q[c] = -0.5
    raw["Ser_UCR_vs_AGY"] = q
    q = zero(codons); q["UCA"] = 1.0; q["UCG"] = -1.0; raw["Ser_UCA_vs_UCG"] = q
    q = zero(codons)
    for c in ["ACA", "ACG"]: q[c] = 0.5
    for c in ["ACU", "ACC"]: q[c] = -0.5
    raw["Thr_ACR_vs_ACY"] = q
    q = zero(codons)
    for family in Q9_FAMILIES:
        q[family[0]] += 1.0
        q[family[-1]] -= 1.0
    raw["f3_stress"] = q
    return raw


def cannot_claim():
    return [
        "This coupling matrix does not assert S_ij survival; true survival requires ribo-seq, stAI, or protein-abundance readouts under controls.",
        "This codon-count and tRNA-copy proxy contact does not assert ribosome-mediated translation realization.",
        "This result does not assert protein folding, structural order, physical admissibility, biological function, or pathway evidence.",
        "This three-organism finite-row statistic does not assert a universal biological law or population-level estimate.",
        "This result does not interpret the sign of any A_ij entry as universal directionality.",
        "This computation keeps the amino-acid composition quotient explicit through the P_tau synonymous projection.",
    ]


def main():
    repo = pathlib.Path(__file__).resolve().parents[3]
    missing = [path for path in REQUIRED_DATA if not (repo / path).exists()]
    if missing:
        emit("needs_data", missing_required_data=missing, reason="required coupling-matrix data not present")
    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        usage_rows, readouts, organisms = [], [], {}
        for organism in ORGANISMS:
            usage_rows.append(codon_residual(repo, organism, codons, fibers))
            readout, summary = trna_leu_log_ratio(repo, organism)
            readouts.append(readout)
            organisms[organism] = {**summary, "log_CUN_over_UUR_tRNA_Leu": readout}

        sigma_readout = covariance_apply_scalar(centered_vectors(usage_rows, codons), centered_scalars(readouts), codons)
        projected_q = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        matrix = {name: {"tRNA_Leu_CUN_vs_UUR_proxy": dot(vector, sigma_readout, codons)} for name, vector in projected_q.items()}
        entries = [
            {"q": name, "readout": readout, "A_ij": value}
            for name, row in matrix.items()
            for readout, value in row.items()
            if abs(value) > THRESHOLD
        ]
        max_abs = max(abs(value) for row in matrix.values() for value in row.values())
        syn_ok = all(abs(sum(vector[c] for c in fiber)) < 1e-8 for vector in projected_q.values() for fiber in fibers.values())
        checks = [
            {"name": "cross_organism_data_loaded", "passed": len(usage_rows) == 3 and len(readouts) == 3, "actual": ORGANISMS, "expected": "3 organisms x codon counts x tRNA-Leu copies"},
            {"name": "b_star_q6_synonymous_residuals_computed", "passed": len(projected_q) == 9 and syn_ok, "actual": sorted(projected_q), "expected": "9 q_i projected to V_syn"},
            {"name": "coupling_matrix_at_least_one_above_threshold", "passed": len(entries) >= 1, "actual": {"max_abs_A_ij": max_abs, "nonzero_entries": len(entries)}, "expected": {"coupling_threshold": THRESHOLD, "min_nonzero_entries": 1}},
            {"name": "no_survival_claim_without_translation_readout", "passed": True, "actual": cannot_claim()[:2], "expected": "coupling is not promoted to survival without ribo-seq, stAI, or proteomics"},
            {"name": "no_cross_layer_promotion_to_function_or_structure", "passed": True, "actual": cannot_claim()[2:], "expected": "no function, structure, universality, directionality, or population promotion"},
        ]
        emit("passed" if all(c["passed"] for c in checks) else "failed", checks=checks, result={
            "claimed_layer": "codon_usage_topology",
            "codon_count_space": len(codons),
            "organisms": organisms,
            "coupling_threshold": THRESHOLD,
            "coupling_matrix": matrix,
            "entries_above_threshold": entries,
            "break_condition": "null if all 9 q_i have |A_ij| < 0.01 against the proxy readout",
            "break_condition_met": len(entries) == 0,
            "proxy_readout": "tRNA-Leu CUN-vs-UUR log-copy spectrum; true tAI/stAI and translation readouts are not present",
            "cannot_claim": cannot_claim(),
            "future_required_data_for_survival": ["tAI or stAI weights main dataset", "ribo-seq translation efficiency readouts", "proteomics protein-abundance readouts"],
        })
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable required data")


if __name__ == "__main__":
    main()

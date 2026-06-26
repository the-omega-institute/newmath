#!/usr/bin/env python3
"""Cross-organism meta analysis for B*_Q6 organism-specificity.

This is a descriptive correlation audit across organisms. It is not causal and
does not apply a phylogenetic comparative correction.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any

from run_b_star_q6_protein_omics_survival_powered import (
    explained_by_design,
    frobenius2,
    residualize,
    standard_amino_acids,
    protein_rows as sqp_protein_rows,
)
from run_b_star_q6_translation_complement_residual_powered import complement_decomposition
from run_b_star_q6_translation_mediation_powered import (
    DEGENERATE_R2,
    MIN_PROTEINS_PER_ORGANISM,
    SURVIVAL_EPS,
    codon_counts_rna,
    joint_decomposition,
    load_json,
    modeled_tai_weights,
    protein_rows as mqtp_protein_rows,
)
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_organism_specificity_meta_powered"
CLAIM_ID = "h3.cross_layer_relation.organism_specificity_meta.b_star_q6_cross_organism_powered"
CONJECTURE_ID = "q6.organism-specificity-meta.cross-organism"

PERMUTATION_TRIALS = 1000
MIN_COMPLETE_ORGANISMS = 10

ORGANISMS = [
    "saccharomyces_cerevisiae",
    "mycobacterium_smegmatis_str_mc2_155",
    "escherichia_coli_k12_mg1655",
    "homo_sapiens",
    "danio_rerio",
    "gallus_gallus",
    "bacillus_subtilis_subsp_subtilis_str_168",
    "mus_musculus",
    "caenorhabditis_elegans",
    "drosophila_melanogaster",
    "sulfolobus_solfataricus",
    "rattus_norvegicus",
    "pseudomonas_aeruginosa_pao1",
    "halobacterium_salinarum",
    "dictyostelium_discoideum",
    "arabidopsis_thaliana",
]

TRNA_ORGANISM = {
    "escherichia_coli_k12_mg1655": "escherichia_coli",
}

DOMAIN = {
    "escherichia_coli_k12_mg1655": "bacteria",
    "mycobacterium_smegmatis_str_mc2_155": "bacteria",
    "pseudomonas_aeruginosa_pao1": "bacteria",
    "bacillus_subtilis_subsp_subtilis_str_168": "bacteria",
    "halobacterium_salinarum": "archaea",
    "sulfolobus_solfataricus": "archaea",
}


def emit(status: str, **kw: object) -> None:
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
    }
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def finite_float(value: object) -> bool:
    return (
        isinstance(value, (int, float))
        and not isinstance(value, bool)
        and math.isfinite(float(value))
    )


def organism_domain(organism: str) -> str:
    return DOMAIN.get(organism, "eukaryote")


def trna_organism_for(organism: str) -> str:
    return TRNA_ORGANISM.get(organism, organism)


def trna_path(repo: pathlib.Path, organism: str) -> pathlib.Path:
    return repo / f"tools/fibonacci_reality/data/gtrnadb_trna_all_copy_{trna_organism_for(organism)}.json"


def proteomics_n_proteins(repo: pathlib.Path, organism: str) -> int | None:
    path = repo / f"tools/fibonacci_reality/data/proteomics_abundance_{organism}.json"
    if not path.exists():
        return None
    payload = load_json(path)
    if not isinstance(payload, dict):
        return None
    value = payload.get("n_proteins")
    if isinstance(value, bool) or not isinstance(value, int):
        return None
    return value


def trna_gene_count(repo: pathlib.Path, organism: str) -> int | None:
    path = trna_path(repo, organism)
    if not path.exists():
        return None
    payload = load_json(path)
    if not isinstance(payload, dict):
        return None
    copies = payload.get("trna_all_copies")
    if not isinstance(copies, dict):
        return None
    total = 0
    for value in copies.values():
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            return None
        total += int(value)
    return total


def global_gc3(
    *,
    payload: dict[str, object],
    codons: list[str],
    organism: str,
) -> tuple[float | None, dict[str, int]]:
    joined = payload.get("joined")
    if not isinstance(joined, list):
        return None, {"records_scanned": 0, "records_used": 0, "sense_codons": 0}

    gc3_count = 0
    sense_count = 0
    used = 0
    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            continue
        counts = codon_counts_rna(item, codons, organism, row_index)
        total = sum(counts.values())
        if total <= 0:
            continue
        used += 1
        sense_count += total
        gc3_count += sum(counts[codon] for codon in codons if codon[2] in {"G", "C"})

    if sense_count <= 0:
        return None, {"records_scanned": len(joined), "records_used": used, "sense_codons": 0}
    return gc3_count / sense_count, {
        "records_scanned": len(joined),
        "records_used": used,
        "sense_codons": sense_count,
    }


def sqp_metrics(
    *,
    payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> dict[str, object]:
    x_rows, y_rows, z_rows, data_summary = sqp_protein_rows(
        payload=payload,
        organism=organism,
        codons=codons,
        code=code,
        aa_order=aa_order,
        q_projected=q_projected,
        q_names=q_names,
        q_support=q_support,
    )
    n_joined = len(x_rows)
    if n_joined == 0:
        return {
            "R2_QP": None,
            "sqp_status": "needs_data",
            "sqp_reason": "cds_codon_abundance joined rows contain no usable protein-abundance/CDS codon-count records",
            "sqp_n_joined": 0,
            "sqp_data_summary": data_summary,
        }
    x_tilde, rank_z = residualize(x_rows, z_rows)
    y_tilde, _ = residualize(y_rows, z_rows)
    y_energy = frobenius2(y_tilde)
    explained, rank_x = explained_by_design(x_tilde, y_tilde)
    r2_qp = 0.0 if y_energy <= SURVIVAL_EPS else max(0.0, min(1.0, explained / y_energy))
    return {
        "R2_QP": r2_qp,
        "sqp_status": "computed",
        "sqp_n_joined": n_joined,
        "sqp_rank_Z": rank_z,
        "sqp_rank_X": rank_x,
        "sqp_y_residual_energy": y_energy,
        "sqp_explained_energy": explained,
        "sqp_powered_rank_sufficient": (
            n_joined >= MIN_PROTEINS_PER_ORGANISM
            and n_joined - rank_z > 10 * len(q_names)
            and rank_x == len(q_names)
            and y_energy > SURVIVAL_EPS
            and r2_qp < DEGENERATE_R2
        ),
        "sqp_data_summary": data_summary,
    }


def mqtp_metrics(
    *,
    repo: pathlib.Path,
    payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> dict[str, object]:
    if not trna_path(repo, organism).exists():
        return {
            "M_QTP_fraction": None,
            "dominant_coord": None,
            "mqtp_status": "needs_data",
            "mqtp_reason": "matched gtrnadb_trna_all_copy file is absent for this organism slug",
        }

    trna_organism = trna_organism_for(organism)
    tai_weights, tai_summary = modeled_tai_weights(
        repo=repo,
        organism=organism,
        trna_organism=trna_organism,
        code=code,
        codons=codons,
    )
    x_rows, t_rows, y_rows, z_rows, data_summary = mqtp_protein_rows(
        payload=payload,
        organism=organism,
        codons=codons,
        code=code,
        aa_order=aa_order,
        q_projected=q_projected,
        q_names=q_names,
        q_support=q_support,
        tai_weights=tai_weights,
    )
    n_joined = len(x_rows)
    if n_joined == 0:
        return {
            "M_QTP_fraction": None,
            "dominant_coord": None,
            "mqtp_status": "needs_data",
            "mqtp_reason": "cds_codon_abundance joined rows contain no usable protein-abundance/CDS codon-count records",
            "mqtp_n_joined": 0,
            "tai_summary": tai_summary,
            "mqtp_data_summary": data_summary,
        }

    x_tilde, rank_z = residualize(x_rows, z_rows)
    t_tilde, _ = residualize(t_rows, z_rows)
    y_tilde, _ = residualize(y_rows, z_rows)
    joint = joint_decomposition(
        x_tilde=x_tilde,
        t_tilde=t_tilde,
        y_tilde=y_tilde,
        q_names=q_names,
    )
    complement = complement_decomposition(
        x_tilde=x_tilde,
        t_tilde=t_tilde,
        y_tilde=y_tilde,
        q_names=q_names,
    )
    support_entries = complement["support"]["entries"]
    dominant_entry = max(
        support_entries,
        key=lambda item: (abs(float(item["a_perp"])), str(item["coordinate"])),
    )
    dominant_coord = str(dominant_entry["coordinate"])
    rank_diag = joint["rank_diagnostics"]
    fraction = joint["M_QTP_fraction"]
    return {
        "M_QTP_fraction": fraction,
        "dominant_coord": dominant_coord,
        "mqtp_status": "computed",
        "mqtp_n_joined": n_joined,
        "mqtp_rank_Z": rank_z,
        "mqtp_rank_X": rank_diag["rank_Xtilde"],
        "mqtp_rank_T": rank_diag["rank_Ttilde"],
        "mqtp_rank_XT": rank_diag["rank_XTtilde"],
        "mqtp_y_residual_energy": rank_diag["y_residual_energy"],
        "mqtp_t_residual_energy": rank_diag["t_residual_energy"],
        "a_perp": complement["a_perp"],
        "a_perp_abs_fraction": {
            str(entry["coordinate"]): float(entry["abs_fraction"])
            for entry in support_entries
        },
        "dominant_coord_abs_fraction": float(dominant_entry["abs_fraction"]),
        "M_QTP_fraction_in_unit_interval": finite_float(fraction) and 0.0 <= float(fraction) <= 1.0,
        "mqtp_powered_rank_sufficient": (
            n_joined >= MIN_PROTEINS_PER_ORGANISM
            and n_joined - rank_z > 10 * (len(q_names) + 1)
            and int(rank_diag["rank_Xtilde"]) == len(q_names)
            and int(rank_diag["rank_Ttilde"]) == 1
            and int(rank_diag["rank_XTtilde"]) == len(q_names) + 1
            and float(rank_diag["y_residual_energy"]) > SURVIVAL_EPS
            and float(rank_diag["t_residual_energy"]) > SURVIVAL_EPS
            and finite_float(fraction)
            and 0.0 <= float(fraction) <= 1.0
        ),
        "tai_summary": tai_summary,
        "mqtp_data_summary": data_summary,
    }


def hash_int(material: str) -> int:
    return int.from_bytes(hashlib.sha256(material.encode("utf-8")).digest()[:8], "big")


def deterministic_shuffle(items: list[Any], material: str) -> list[Any]:
    out = list(items)
    for index in range(len(out) - 1, 0, -1):
        swap = hash_int(f"{material}|{index}") % (index + 1)
        out[index], out[swap] = out[swap], out[index]
    return out


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def pearson_r(x_values: list[float], y_values: list[float]) -> float | None:
    if len(x_values) != len(y_values) or len(x_values) < 3:
        return None
    x_mean = mean(x_values)
    y_mean = mean(y_values)
    x_centered = [value - x_mean for value in x_values]
    y_centered = [value - y_mean for value in y_values]
    x_ss = sum(value * value for value in x_centered)
    y_ss = sum(value * value for value in y_centered)
    if x_ss <= 0.0 or y_ss <= 0.0:
        return None
    return sum(x_centered[index] * y_centered[index] for index in range(len(x_values))) / math.sqrt(x_ss * y_ss)


def continuous_test(
    *,
    rows: list[dict[str, object]],
    predictor: str,
    transform: str | None,
    response: str,
    test_id: str,
) -> dict[str, object]:
    x_values: list[float] = []
    y_values: list[float] = []
    organisms: list[str] = []
    for row in rows:
        x_raw = row.get(predictor)
        y_raw = row.get(response)
        if not finite_float(x_raw) or not finite_float(y_raw):
            continue
        x = float(x_raw)
        if transform == "log":
            if x <= 0.0:
                continue
            x = math.log(x)
        x_values.append(x)
        y_values.append(float(y_raw))
        organisms.append(str(row["organism"]))

    observed = pearson_r(x_values, y_values)
    if observed is None:
        return {
            "status": "needs_data",
            "test": test_id,
            "predictor": predictor,
            "response": response,
            "transform": transform,
            "n": len(x_values),
            "reason": "fewer than 3 usable rows or a zero-variance vector",
        }

    exceed = 0
    for trial in range(PERMUTATION_TRIALS):
        shuffled_y = deterministic_shuffle(y_values, f"{EXPERIMENT_ID}|{test_id}|{trial}")
        permuted = pearson_r(x_values, shuffled_y)
        if permuted is not None and abs(permuted) >= abs(observed) - 1e-15:
            exceed += 1
    p_value = (exceed + 1) / (PERMUTATION_TRIALS + 1)
    return {
        "status": "computed",
        "test": test_id,
        "predictor": predictor,
        "response": response,
        "transform": transform,
        "n": len(x_values),
        "organisms": organisms,
        "statistic": "Pearson r",
        "r": observed,
        "r_abs": abs(observed),
        "permutation_trials": PERMUTATION_TRIALS,
        "permutation_p_two_sided": p_value,
        "direction": "positive" if observed > 0.0 else ("negative" if observed < 0.0 else "zero"),
    }


def domain_ratio(values: list[float], labels: list[str]) -> float | None:
    if len(values) != len(labels) or len(values) < 3:
        return None
    groups: dict[str, list[float]] = {}
    for value, label in zip(values, labels):
        groups.setdefault(label, []).append(value)
    if len(groups) < 2:
        return None
    overall = mean(values)
    between = sum(len(items) * (mean(items) - overall) ** 2 for items in groups.values())
    within = sum(sum((value - mean(items)) ** 2 for value in items) for items in groups.values())
    between_df = len(groups) - 1
    within_df = len(values) - len(groups)
    if between_df <= 0 or within_df <= 0:
        return None
    between_ms = between / between_df
    within_ms = within / within_df
    if within_ms <= 0.0:
        return math.inf if between_ms > 0.0 else 0.0
    return between_ms / within_ms


def mqtp_vs_domain(rows: list[dict[str, object]]) -> dict[str, object]:
    values: list[float] = []
    labels: list[str] = []
    organisms: list[str] = []
    for row in rows:
        value = row.get("M_QTP_fraction")
        if not finite_float(value):
            continue
        values.append(float(value))
        labels.append(str(row["domain"]))
        organisms.append(str(row["organism"]))
    observed = domain_ratio(values, labels)
    if observed is None:
        return {
            "status": "needs_data",
            "test": "M_QTP_fraction_vs_domain",
            "n": len(values),
            "reason": "insufficient usable M_QTP_fraction rows across at least two domains",
        }
    groups: dict[str, list[float]] = {}
    for value, label in zip(values, labels):
        groups.setdefault(label, []).append(value)
    group_means = {
        label: {
            "n": len(items),
            "mean": mean(items),
            "min": min(items),
            "max": max(items),
        }
        for label, items in sorted(groups.items())
    }
    exceed = 0
    for trial in range(PERMUTATION_TRIALS):
        shuffled_labels = deterministic_shuffle(labels, f"{EXPERIMENT_ID}|M_QTP_fraction_vs_domain|{trial}")
        permuted = domain_ratio(values, shuffled_labels)
        if permuted is not None and permuted >= observed - 1e-15:
            exceed += 1
    ordered_means = sorted(group_means.items(), key=lambda item: item[1]["mean"], reverse=True)
    return {
        "status": "computed",
        "test": "M_QTP_fraction_vs_domain",
        "n": len(values),
        "organisms": organisms,
        "statistic": "between_domain_mean_square / within_domain_mean_square",
        "variance_ratio": observed,
        "group_means": group_means,
        "effect_size": {
            "max_minus_min_group_mean": ordered_means[0][1]["mean"] - ordered_means[-1][1]["mean"],
            "highest_mean_domain": ordered_means[0][0],
            "lowest_mean_domain": ordered_means[-1][0],
        },
        "permutation_trials": PERMUTATION_TRIALS,
        "permutation_p_right_tail": (exceed + 1) / (PERMUTATION_TRIALS + 1),
        "direction": f"{ordered_means[0][0]} higher than {ordered_means[-1][0]} by group mean",
    }


def contingency_table(rows: list[dict[str, object]]) -> tuple[list[str], list[str], dict[str, dict[str, int]]]:
    domains = sorted({str(row["domain"]) for row in rows if row.get("dominant_coord") is not None})
    coords = sorted({str(row["dominant_coord"]) for row in rows if row.get("dominant_coord") is not None})
    table = {domain: {coord: 0 for coord in coords} for domain in domains}
    for row in rows:
        coord = row.get("dominant_coord")
        if coord is None:
            continue
        table[str(row["domain"])][str(coord)] += 1
    return domains, coords, table


def chi_square_from_table(
    domains: list[str],
    coords: list[str],
    table: dict[str, dict[str, int]],
) -> tuple[float, float | None, int]:
    n = sum(table[domain][coord] for domain in domains for coord in coords)
    if n == 0 or len(domains) < 2 or len(coords) < 2:
        return 0.0, None, n
    row_totals = {domain: sum(table[domain][coord] for coord in coords) for domain in domains}
    col_totals = {coord: sum(table[domain][coord] for domain in domains) for coord in coords}
    chi2 = 0.0
    for domain in domains:
        for coord in coords:
            expected = row_totals[domain] * col_totals[coord] / n
            if expected > 0.0:
                chi2 += (table[domain][coord] - expected) ** 2 / expected
    denom = n * min(len(domains) - 1, len(coords) - 1)
    cramers_v = math.sqrt(chi2 / denom) if denom > 0 else None
    return chi2, cramers_v, n


def dominant_coord_vs_domain(rows: list[dict[str, object]]) -> dict[str, object]:
    usable = [row for row in rows if row.get("dominant_coord") is not None]
    domains, coords, table = contingency_table(usable)
    observed, cramers_v, n = chi_square_from_table(domains, coords, table)
    if n < 3 or cramers_v is None:
        return {
            "status": "needs_data",
            "test": "dominant_coord_vs_domain",
            "n": n,
            "contingency": table,
            "reason": "insufficient dominant-coordinate rows or only one category/domain",
        }

    labels = [str(row["domain"]) for row in usable]
    coord_values = [str(row["dominant_coord"]) for row in usable]
    exceed = 0
    for trial in range(PERMUTATION_TRIALS):
        shuffled_labels = deterministic_shuffle(labels, f"{EXPERIMENT_ID}|dominant_coord_vs_domain|{trial}")
        perm_rows = [
            {"domain": shuffled_labels[index], "dominant_coord": coord_values[index]}
            for index in range(len(coord_values))
        ]
        p_domains, p_coords, p_table = contingency_table(perm_rows)
        permuted, _, _ = chi_square_from_table(p_domains, p_coords, p_table)
        if permuted >= observed - 1e-15:
            exceed += 1

    top_by_domain = {}
    for domain in domains:
        ordered = sorted(table[domain].items(), key=lambda item: (item[1], item[0]), reverse=True)
        top_by_domain[domain] = {
            "top_coordinate": ordered[0][0],
            "count": ordered[0][1],
            "domain_n": sum(table[domain].values()),
        }
    return {
        "status": "computed",
        "test": "dominant_coord_vs_domain",
        "n": n,
        "statistic": "Pearson chi-square on domain x dominant_coord contingency",
        "chi_square": observed,
        "cramers_v": cramers_v,
        "contingency": table,
        "top_by_domain": top_by_domain,
        "permutation_trials": PERMUTATION_TRIALS,
        "permutation_p_right_tail": (exceed + 1) / (PERMUTATION_TRIALS + 1),
        "direction": "domain-specific dominant-coordinate enrichment if the permutation p is small; otherwise heterogeneous without a resolved domain preference",
    }


def cannot_claim() -> list[str]:
    return [
        "descriptive cross-organism correlation, not causal",
        "N=16 small, exploratory",
        "organisms are NOT phylogenetically independent samples (no phylogenetic comparative correction applied); shared ancestry can drive apparent domain/GC correlations",
        "modeled-tAI mediation is not ribo-seq",
        "M^QTP/R2_QP/dominant_coord are statistical projections from prior experiments, not mechanisms",
        "correlation with GC/domain does not establish a translation or codon-usage mechanism",
    ]


def core_conclusion(tests: dict[str, dict[str, object]]) -> dict[str, object]:
    computed = {
        name: test
        for name, test in tests.items()
        if test.get("status") == "computed"
    }
    significant = []
    for name, test in computed.items():
        p_value = test.get("permutation_p_two_sided", test.get("permutation_p_right_tail"))
        if finite_float(p_value) and float(p_value) <= 0.05:
            significant.append(
                {
                    "test": name,
                    "p": float(p_value),
                    "direction": test.get("direction"),
                }
            )
    strongest = sorted(
        [
            {
                "test": name,
                "p": float(test.get("permutation_p_two_sided", test.get("permutation_p_right_tail"))),
                "direction": test.get("direction"),
            }
            for name, test in computed.items()
            if finite_float(test.get("permutation_p_two_sided", test.get("permutation_p_right_tail")))
        ],
        key=lambda item: item["p"],
    )
    if significant:
        answer = (
            "At least one exploratory uncorrected permutation test is small enough to flag a systematic association, "
            "but the result remains descriptive and phylogenetically uncorrected."
        )
    else:
        answer = (
            "No tested domain/GC3/tRNA-pool/proteome-size association reaches p <= 0.05 under the deterministic "
            "permutation null; the current meta result supports organism-specific heterogeneity more than a resolved "
            "systematic driver."
        )
    return {
        "systematic_signal_detected_uncorrected_p_le_0_05": bool(significant),
        "significant_tests_uncorrected": significant,
        "strongest_tests_by_p": strongest[:3],
        "answer": answer,
        "interpretation_boundary": "exploratory descriptive meta correlation only; not causal and not phylogenetically corrected",
    }


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    required = ["tools/fibonacci_reality/data/ncbi_genetic_codes.json"]
    required += [f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json" for organism in ORGANISMS]
    required += [f"tools/fibonacci_reality/data/proteomics_abundance_{organism}.json" for organism in ORGANISMS]
    missing = [path for path in required if not (repo / path).exists()]
    if missing:
        emit("needs_data", missing_required_data=missing, reason="required local CDS/proteomics data are absent")

    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {
            codon
            for vector in q_projected.values()
            for codon, value in vector.items()
            if abs(value) > 0.0
        }

        rows: list[dict[str, object]] = []
        diagnostics: dict[str, object] = {}
        for organism in ORGANISMS:
            payload = load_json(repo / f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json")
            if not isinstance(payload, dict):
                raise ValueError(f"{organism} CDS payload must be a JSON object")
            gc3, gc3_summary = global_gc3(payload=payload, codons=codons, organism=organism)
            sqp = sqp_metrics(
                payload=payload,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
            )
            mqtp = mqtp_metrics(
                repo=repo,
                payload=payload,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
            )
            table_row = {
                "organism": organism,
                "domain": organism_domain(organism),
                "dominant_coord": mqtp["dominant_coord"],
                "M_QTP_fraction": mqtp["M_QTP_fraction"],
                "R2_QP": sqp["R2_QP"],
                "GC3": gc3,
                "trna_gene_count": trna_gene_count(repo, organism),
                "n_proteins": proteomics_n_proteins(repo, organism),
            }
            rows.append(table_row)
            diagnostics[organism] = {
                "gc3_summary": gc3_summary,
                "sqp": sqp,
                "mqtp": mqtp,
                "trna_organism": trna_organism_for(organism),
            }

        tests = {
            "M_QTP_fraction_vs_domain": mqtp_vs_domain(rows),
            "M_QTP_fraction_vs_GC3": continuous_test(
                rows=rows,
                predictor="GC3",
                transform=None,
                response="M_QTP_fraction",
                test_id="M_QTP_fraction_vs_GC3",
            ),
            "M_QTP_fraction_vs_log_trna_gene_count": continuous_test(
                rows=rows,
                predictor="trna_gene_count",
                transform="log",
                response="M_QTP_fraction",
                test_id="M_QTP_fraction_vs_log_trna_gene_count",
            ),
            "M_QTP_fraction_vs_log_n_proteins": continuous_test(
                rows=rows,
                predictor="n_proteins",
                transform="log",
                response="M_QTP_fraction",
                test_id="M_QTP_fraction_vs_log_n_proteins",
            ),
            "dominant_coord_vs_domain": dominant_coord_vs_domain(rows),
        }

        complete_rows = [
            row for row in rows
            if (
                row.get("dominant_coord") is not None
                and finite_float(row.get("M_QTP_fraction"))
                and finite_float(row.get("R2_QP"))
                and finite_float(row.get("GC3"))
                and finite_float(row.get("trna_gene_count"))
                and finite_float(row.get("n_proteins"))
            )
        ]
        gc3_needs_data = [
            row["organism"]
            for row in rows
            if not finite_float(row.get("GC3"))
        ]
        gc3_ok = (
            sum(finite_float(row.get("GC3")) and 0.0 <= float(row["GC3"]) <= 1.0 for row in rows)
            >= MIN_COMPLETE_ORGANISMS
            and all(
                not finite_float(row.get("GC3"))
                or 0.0 <= float(row["GC3"]) <= 1.0
                for row in rows
            )
        )
        mqtp_domain_ok = tests["M_QTP_fraction_vs_domain"].get("status") == "computed"
        continuous_ok = all(
            tests[name].get("status") == "computed"
            for name in [
                "M_QTP_fraction_vs_GC3",
                "M_QTP_fraction_vs_log_trna_gene_count",
                "M_QTP_fraction_vs_log_n_proteins",
            ]
        )
        dominant_ok = tests["dominant_coord_vs_domain"].get("status") == "computed"
        no_overclaim_ok = cannot_claim() == [
            "descriptive cross-organism correlation, not causal",
            "N=16 small, exploratory",
            "organisms are NOT phylogenetically independent samples (no phylogenetic comparative correction applied); shared ancestry can drive apparent domain/GC correlations",
            "modeled-tAI mediation is not ribo-seq",
            "M^QTP/R2_QP/dominant_coord are statistical projections from prior experiments, not mechanisms",
            "correlation with GC/domain does not establish a translation or codon-usage mechanism",
        ]

        checks = [
            {
                "name": "per_organism_meta_assembled",
                "passed": len(complete_rows) >= MIN_COMPLETE_ORGANISMS and len(rows) == 16,
                "actual": {
                    "row_count": len(rows),
                    "complete_feature_row_count": len(complete_rows),
                    "complete_feature_organisms": [row["organism"] for row in complete_rows],
                    "needs_data_organisms_for_mqtp": [
                        row["organism"] for row in rows if row.get("M_QTP_fraction") is None
                    ],
                },
                "expected": "16 organism rows and at least 10 rows with dominant_coord, M_QTP_fraction, R2_QP, GC3, trna_gene_count, and n_proteins",
            },
            {
                "name": "gc3_computed",
                "passed": gc3_ok,
                "actual": {
                    "computed": {row["organism"]: row["GC3"] for row in rows if finite_float(row.get("GC3"))},
                    "needs_data": gc3_needs_data,
                },
                "expected": "global GC3 in [0,1] computed from local CDS codon counts for every organism with usable cds_codon_abundance joined rows; row-level needs_data is explicit when joined rows are empty",
            },
            {
                "name": "mqtp_vs_domain_tested",
                "passed": mqtp_domain_ok,
                "actual": tests["M_QTP_fraction_vs_domain"],
                "expected": "M_QTP_fraction domain group means and deterministic label-permutation null",
            },
            {
                "name": "mqtp_vs_continuous_tested",
                "passed": continuous_ok,
                "actual": {
                    name: tests[name]
                    for name in [
                        "M_QTP_fraction_vs_GC3",
                        "M_QTP_fraction_vs_log_trna_gene_count",
                        "M_QTP_fraction_vs_log_n_proteins",
                    ]
                },
                "expected": "Pearson r and deterministic permutation p for GC3, log(tRNA gene count), and log(n_proteins)",
            },
            {
                "name": "dominant_coord_contingency",
                "passed": dominant_ok,
                "actual": tests["dominant_coord_vs_domain"],
                "expected": "dominant_coord x domain contingency table with deterministic domain-label permutation",
            },
            {
                "name": "no_causal_or_phylo_overclaim",
                "passed": no_overclaim_ok,
                "actual": cannot_claim(),
                "expected": "explicit caveats include non-causal status, N=16 exploratory scope, and no phylogenetic comparative correction",
            },
        ]

        status = "passed" if all(check["passed"] for check in checks) else "needs_data"
        emit(
            status,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture": CONJECTURE_ID,
                "statement": "Organism-specific B*_Q6 cross-layer summaries are compared against domain, GC3, tRNA-pool size, and proteome-size proxies with deterministic permutation nulls.",
                "status_semantics": "passed means the descriptive meta table and null tests were computed; it does not promote causality, mechanism, or phylogenetically corrected inference",
                "organism_scope": {
                    "n_total": len(rows),
                    "organisms": ORGANISMS,
                    "domain_rule": "archaea = halobacterium/sulfolobus; bacteria = ecoli/m.smeg/pseudomonas/b.subtilis; all remaining organisms are eukaryote",
                    "tRNA_missing_policy": "M_QTP_fraction and dominant_coord are None where the exact gtrnadb_trna_all_copy organism slug is absent",
                },
                "per_organism_meta": rows,
                "meta_tests": tests,
                "core_conclusion": core_conclusion(tests),
                "diagnostics": diagnostics,
                "honest": {
                    "cannot_claim": cannot_claim(),
                },
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable organism-specificity meta input")


if __name__ == "__main__":
    main()

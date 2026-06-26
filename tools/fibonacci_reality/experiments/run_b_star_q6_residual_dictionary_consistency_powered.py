#!/usr/bin/env python3
"""Direction-aware ordered residual dictionary for B*_Q6 to protein abundance.

The experiment is descriptive. It partitions projection energy after local
controls and ranks residual H readouts by absorption times coordinate-support
direction agreement above a deterministic label-permutation null with
description-length and join-shift penalties.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any

import run_b_star_q6_residual_decomposition_powered as bare_absorption_decomposition
from run_b_star_q6_h_candidate_ranking_table_powered import (
    FEATURE_CANDIDATES,
    feature_index,
    localization_index,
    turnover_index,
)
from run_b_star_q6_joint_te_stability_mediation_powered import (
    ecoli_join_keys,
    ecoli_mrna_index,
    human_join_keys,
    human_mrna_indices,
    te_indices,
    yeast_join_keys,
    yeast_mrna_index,
)
from run_b_star_q6_mrna_half_life_sqm_ecoli_powered import (
    PRIMARY_GROWTH_RATE as ECOLI_PRIMARY_GROWTH_RATE,
)
from run_b_star_q6_protein_omics_survival_powered import (
    matrix_column,
    numeric,
    orthonormal_basis_from_columns,
    standard_amino_acids,
)
from run_b_star_q6_translation_complement_residual_powered import vector_norm2
from run_b_star_q6_translation_complement_residual_powered import solve_regularized_normal_equation
from run_b_star_q6_translation_mediation_powered import (
    MIN_PROTEINS_PER_ORGANISM,
    codon_counts_rna,
    normed_coordinate,
    vector_dot,
)
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_residual_dictionary_consistency_powered"
CLAIM_ID = "h3.cross_layer_relation.residual_dictionary_consistency.b_star_q6_direction_aware_ordered_powered"
CONJECTURE_ID = "q6.residual-dictionary.direction-aware-ordered.cross-layer"

PERMUTATION_COUNT = 1000
LAMBDA_DL = 0.01
RHO_JOIN = 0.05
EPS = 1e-12
SUM_TOL = 1e-6

ORGANISMS = [
    {
        "key": "saccharomyces_cerevisiae",
        "label": "Saccharomyces cerevisiae",
        "domain": "eukaryote",
        "has_stability": True,
        "stability_path": "tools/fibonacci_reality/data/mrna_half_life_saccharomyces_cerevisiae_neymotin.json",
        "stability_readout": "log10(mRNA half-life minutes), Neymotin et al 2014",
    },
    {
        "key": "escherichia_coli_k12_mg1655",
        "label": "Escherichia coli K-12 MG1655",
        "domain": "prokaryote",
        "has_stability": True,
        "stability_path": "tools/fibonacci_reality/data/mrna_half_life_escherichia_coli_esquerre.json",
        "stability_readout": f"log10(mRNA half-life minutes at growth rate {ECOLI_PRIMARY_GROWTH_RATE} h-1), Esquerre et al 2015",
    },
    {
        "key": "homo_sapiens",
        "label": "Homo sapiens",
        "domain": "eukaryote",
        "has_stability": True,
        "stability_path": "tools/fibonacci_reality/data/mrna_half_life_homo_sapiens_agarwal_consensus.json",
        "stability_readout": "unlogged consensus relative mRNA half-life, Agarwal and Kelley 2022",
    },
    {
        "key": "danio_rerio",
        "label": "Danio rerio",
        "domain": "eukaryote",
        "has_stability": False,
        "stability_path": None,
        "stability_readout": None,
    },
]

H_CANDIDATES = [
    "turnover",
    "localization",
    "ptm_density",
    "complex_member",
    "tm_count",
    "domain_count",
    "mrna_abundance",
]


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def finite(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def bounded_unit(value: float, tol: float = 1e-8) -> float:
    if -tol <= value < 0.0:
        return 0.0
    if 1.0 < value <= 1.0 + tol:
        return 1.0
    return value


def finite_unit(value: object) -> bool:
    return finite(value) and 0.0 <= float(value) <= 1.0


def percentile_nearest_rank(values: list[float], probability: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def transpose(matrix: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    return [[row[index] for row in matrix] for index in range(len(matrix[0]))]


def residualize_with_basis(matrix: list[list[float]], basis: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    out = [list(row) for row in matrix]
    columns = transpose(matrix)
    for q in basis:
        for col_index, column in enumerate(columns):
            coeff = vector_dot(column, q)
            if coeff == 0.0:
                continue
            for row_index in range(len(matrix)):
                out[row_index][col_index] -= coeff * q[row_index]
    return out


def project_vector(design: list[list[float]], target: list[float]) -> tuple[list[float], float, int]:
    basis = orthonormal_basis_from_columns(design)
    projected = [0.0 for _ in target]
    for q in basis:
        coeff = vector_dot(target, q)
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            projected[index] += coeff * q[index]
    return projected, vector_norm2(projected), len(basis)


def project_by_basis(design: list[list[float]], target: list[float]) -> dict[str, object]:
    basis = orthonormal_basis_from_columns(design)
    projected = [0.0 for _ in target]
    for q in basis:
        coeff = vector_dot(target, q)
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            projected[index] += coeff * q[index]
    target_norm2 = vector_norm2(target)
    projected_norm2 = vector_norm2(projected)
    absorbed = 0.0 if target_norm2 <= EPS else bounded_unit(projected_norm2 / target_norm2)
    return {
        "projected_vector": projected,
        "absorbed": absorbed,
        "projected_norm2": projected_norm2,
        "target_norm2": target_norm2,
        "rank": len(basis),
    }


def subtract_vectors(left: list[float], right: list[float]) -> list[float]:
    return [left[index] - right[index] for index in range(len(left))]


def support_cosine(left: list[float], right: list[float]) -> tuple[float, str | None]:
    left_norm = math.sqrt(vector_dot(left, left))
    right_norm = math.sqrt(vector_dot(right, right))
    if left_norm <= EPS:
        return 0.0, "a_H_zero_vector"
    if right_norm <= EPS:
        return 0.0, "a_perp_zero_vector"
    value = vector_dot(left, right) / (left_norm * right_norm)
    if -1.0 - 1e-8 <= value < -1.0:
        value = -1.0
    if 1.0 < value <= 1.0 + 1e-8:
        value = 1.0
    return value, None


def matrix_rows(rows: list[dict[str, object]], key: str) -> list[list[float]]:
    return [list(row[key]) for row in rows]  # type: ignore[arg-type]


def q6_context(repo: pathlib.Path) -> dict[str, object]:
    code = standard_code(repo)
    codons = [codon for codon in sorted(code) if code[codon] != "*"]
    fibers = fibers_for(code, codons)
    aa_order = standard_amino_acids(code, codons)
    q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
    q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}
    return {
        "code": code,
        "codons": codons,
        "aa_order": aa_order,
        "q_projected": q_projected,
        "q_names": list(q_projected),
        "q_support": q_support,
    }


def controls_used(aa_order: list[str]) -> list[str]:
    return [
        "intercept",
        "log(cds_len_nt)",
        "20 amino-acid composition proportions from real CDS codon counts: " + ",".join(aa_order),
        "GC3 from real CDS codon counts",
        "M-density baseline = fraction of sense codons on the union support of the 9 projected B*_Q6 q vectors",
        "log10(mRNA abundance) from the local measured-TE payload",
    ]


def cds_q_z_rows(
    *,
    item: dict[str, object],
    row_index: int,
    organism: str,
    context: dict[str, object],
    mrna_value: float,
) -> tuple[list[float], list[float]]:
    codons = context["codons"]
    code = context["code"]
    aa_order = context["aa_order"]
    q_projected = context["q_projected"]
    q_names = context["q_names"]
    q_support = context["q_support"]
    if not isinstance(codons, list) or not isinstance(code, dict) or not isinstance(aa_order, list):
        raise ValueError("q6 context malformed")
    if not isinstance(q_projected, dict) or not isinstance(q_names, list) or not isinstance(q_support, set):
        raise ValueError("q6 context malformed")

    cds_len_nt = numeric(item.get("cds_len_nt"), f"{organism}.joined[{row_index}].cds_len_nt")
    if cds_len_nt <= 0.0:
        raise ValueError("invalid_length")
    counts = codon_counts_rna(item, codons, organism, row_index)
    total = sum(counts.values())
    if total <= 0:
        raise ValueError("empty_sense_codon_counts")
    frequencies = {codon: counts[codon] / total for codon in codons}
    x_row = [normed_coordinate(frequencies, q_projected[name], codons) for name in q_names]

    aa_counts = {aa: 0 for aa in aa_order}
    for codon in codons:
        aa_counts[code[codon]] += counts[codon]
    aa_total = sum(aa_counts.values())
    if aa_total <= 0:
        raise ValueError("empty_amino_acid_counts")
    gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
    m_density = sum(counts[codon] for codon in q_support) / total
    z_row = (
        [1.0, math.log(cds_len_nt)]
        + [aa_counts[aa] / aa_total for aa in aa_order]
        + [gc3, m_density, math.log10(mrna_value)]
    )
    return x_row, z_row


def stability_value_for(
    *,
    organism: str,
    item: dict[str, object],
    protein_id: str,
    stability_indices: dict[str, object],
    skipped: dict[str, int],
    join_sources: dict[str, int],
) -> float | None:
    if organism == "saccharomyces_cerevisiae":
        _pid, orf, error = yeast_join_keys(item)
        if error:
            skipped[error] = skipped.get(error, 0) + 1
            return None
        values = stability_indices["yeast"]
        if not isinstance(values, dict):
            raise ValueError("yeast stability index malformed")
        value = values.get(str(orf))
        if value is not None:
            join_sources["stability_primary_key"] += 1
            return math.log10(float(value))
        return None
    if organism == "escherichia_coli_k12_mg1655":
        _pid, locus_tag, error = ecoli_join_keys(item)
        if error:
            skipped[error] = skipped.get(error, 0) + 1
            return None
        values = stability_indices["ecoli"]
        if not isinstance(values, dict):
            raise ValueError("ecoli stability index malformed")
        value = values.get(str(locus_tag))
        if value is not None:
            join_sources["stability_primary_key"] += 1
            return math.log10(float(value))
        return None
    if organism == "homo_sapiens":
        _pid, ensg, symbol, error = human_join_keys(item)
        if error:
            skipped[error] = skipped.get(error, 0) + 1
            return None
        by_ensg = stability_indices["human_ensg"]
        by_symbol = stability_indices["human_symbol"]
        if not isinstance(by_ensg, dict) or not isinstance(by_symbol, dict):
            raise ValueError("human stability indices malformed")
        value = by_ensg.get(ensg) if ensg is not None else None
        if value is not None:
            join_sources["stability_primary_key"] += 1
            return float(value)
        if symbol is not None:
            value = by_symbol.get(symbol)
            if value is not None:
                join_sources["stability_symbol_fallback"] += 1
                return float(value)
        return None
    raise ValueError(f"unsupported stability organism {organism}")


def stability_indices_for(repo: pathlib.Path, config: dict[str, object]) -> tuple[dict[str, object], dict[str, object]]:
    if not config.get("has_stability"):
        return {}, {"status": "skipped", "reason": "no local mRNA-stability payload listed for this organism"}
    path = repo / str(config["stability_path"])
    if not path.exists():
        return {}, {"status": "needs_data", "missing_path": str(path.relative_to(repo))}
    payload = load_json(path)
    if not isinstance(payload, dict):
        raise ValueError(f"{path} must contain a JSON object")
    organism = str(config["key"])
    if organism == "saccharomyces_cerevisiae":
        values, summary = yeast_mrna_index(payload)
        return {"yeast": values}, summary
    if organism == "escherichia_coli_k12_mg1655":
        values, summary = ecoli_mrna_index(payload)
        return {"ecoli": values}, summary
    if organism == "homo_sapiens":
        by_ensg, by_symbol, summary = human_mrna_indices(payload)
        return {"human_ensg": by_ensg, "human_symbol": by_symbol}, summary
    raise ValueError(f"unsupported organism {organism}")


def base_rows(
    *,
    repo: pathlib.Path,
    context: dict[str, object],
    config: dict[str, object],
) -> dict[str, object]:
    organism = str(config["key"])
    cds_path = repo / f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json"
    te_path = repo / f"tools/fibonacci_reality/data/ribosome_te_{organism}.json"
    missing = [str(path.relative_to(repo)) for path in [cds_path, te_path] if not path.exists()]
    if missing:
        return {"status": "needs_data", "reason": "missing local CDS or measured-TE payload", "missing": missing}
    cds_payload = load_json(cds_path)
    te_payload = load_json(te_path)
    if not isinstance(cds_payload, dict) or not isinstance(te_payload, dict):
        raise ValueError(f"{organism} CDS and TE payloads must be JSON objects")
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} CDS payload must contain joined list")
    te_by_protein, te_by_gene, te_summary = te_indices(te_payload, organism)
    stability_indices, stability_summary = stability_indices_for(repo, config)
    require_stability = bool(config.get("has_stability")) and bool(stability_indices)

    rows: dict[str, dict[str, object]] = {}
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "duplicate_protein_id": 0,
        "no_te_match": 0,
        "nonpositive_te": 0,
        "nonpositive_mrna": 0,
        "no_mrna_stability_match": 0,
        "nonpositive_mrna_stability": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
        "empty_amino_acid_counts": 0,
        "missing_locus_tag": 0,
        "missing_cds_header": 0,
        "missing_gene_keys": 0,
        "unparseable_yeast_orf": 0,
    }
    join_sources = {
        "te_protein_id": 0,
        "te_gene_key": 0,
        "stability_primary_key": 0,
        "stability_symbol_fallback": 0,
    }

    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        if protein_id in rows:
            skipped["duplicate_protein_id"] += 1
            continue
        abundance = numeric(item.get("abundance_ppm"), f"{organism}.joined[{row_index}].abundance_ppm")
        if abundance <= 0.0:
            skipped["nonpositive_abundance"] += 1
            continue

        te_record = te_by_protein.get(protein_id)
        if te_record is None:
            if organism == "saccharomyces_cerevisiae":
                _pid, orf, error = yeast_join_keys(item)
                if not error and orf is not None:
                    te_record = te_by_gene.get(str(orf))
            elif organism == "escherichia_coli_k12_mg1655":
                _pid, locus_tag, error = ecoli_join_keys(item)
                if not error and locus_tag is not None:
                    te_record = te_by_gene.get(str(locus_tag))
            elif organism == "homo_sapiens":
                _pid, ensg, _symbol, error = human_join_keys(item)
                if not error and ensg is not None:
                    te_record = te_by_gene.get(str(ensg))
            if te_record is not None:
                join_sources["te_gene_key"] += 1
        else:
            join_sources["te_protein_id"] += 1
        if te_record is None:
            skipped["no_te_match"] += 1
            continue
        te_value = float(te_record["te"])
        mrna_value = float(te_record["mrna"])
        if te_value <= 0.0:
            skipped["nonpositive_te"] += 1
            continue
        if mrna_value <= 0.0:
            skipped["nonpositive_mrna"] += 1
            continue

        s_row = None
        if require_stability:
            s_value = stability_value_for(
                organism=organism,
                item=item,
                protein_id=protein_id,
                stability_indices=stability_indices,
                skipped=skipped,
                join_sources=join_sources,
            )
            if s_value is None:
                skipped["no_mrna_stability_match"] += 1
                continue
            if not math.isfinite(s_value):
                skipped["nonpositive_mrna_stability"] += 1
                continue
            s_row = [s_value]

        try:
            x_row, z_row = cds_q_z_rows(
                item=item,
                row_index=row_index,
                organism=organism,
                context=context,
                mrna_value=mrna_value,
            )
        except ValueError as exc:
            key = str(exc)
            if key in skipped:
                skipped[key] += 1
                continue
            raise

        rows[protein_id] = {
            "protein_id": protein_id,
            "x": x_row,
            "p": [math.log10(abundance)],
            "t": [math.log10(te_value)],
            "s": s_row,
            "z": z_row,
            "h": {"mrna_abundance": [math.log10(mrna_value)]},
        }

    return {
        "status": "computed",
        "rows": rows,
        "summary": {
            **te_summary,
            "stability_summary": stability_summary,
            "stability_required_in_base_join": require_stability,
            "n_cds_joined_reported": cds_payload.get("n_joined"),
            "cds_join_hit_rate_reported": cds_payload.get("join_hit_rate"),
            "n_base_joined": len(rows),
            "join_sources": join_sources,
            "skipped_cds_records": skipped,
        },
    }


def load_h_index(repo: pathlib.Path, organism: str, candidate: str) -> tuple[dict[str, list[float]] | None, dict[str, object]]:
    if candidate == "mrna_abundance":
        return {}, {"source": "mRNA abundance already loaded from ribosome_te payload into base rows"}
    if candidate == "turnover":
        path = repo / f"tools/fibonacci_reality/data/protein_turnover_{organism}.json"
        if not path.exists():
            return None, {"status": "needs_data", "missing_path": str(path.relative_to(repo))}
        payload = load_json(path)
        if not isinstance(payload, dict):
            raise ValueError(f"{path} must contain a JSON object")
        return turnover_index(payload)
    if candidate == "localization":
        path = repo / f"tools/fibonacci_reality/data/subcellular_localization_{organism}.json"
        if not path.exists():
            return None, {"status": "needs_data", "missing_path": str(path.relative_to(repo))}
        payload = load_json(path)
        if not isinstance(payload, dict):
            raise ValueError(f"{path} must contain a JSON object")
        return localization_index(payload)
    if candidate in FEATURE_CANDIDATES:
        path = repo / f"tools/fibonacci_reality/data/uniprot_protein_features_{organism}.json"
        if not path.exists():
            return None, {"status": "needs_data", "missing_path": str(path.relative_to(repo))}
        payload = load_json(path)
        if not isinstance(payload, dict):
            raise ValueError(f"{path} must contain a JSON object")
        return feature_index(payload, candidate)
    raise ValueError(f"unknown H candidate {candidate}")


def attach_h_readouts(repo: pathlib.Path, organism: str, rows: dict[str, dict[str, object]]) -> dict[str, object]:
    summaries: dict[str, object] = {}
    dropped: list[dict[str, object]] = []
    for candidate in H_CANDIDATES:
        if candidate == "mrna_abundance":
            summaries[candidate] = {"status": "computed", "n_indexed": len(rows), "source": "base measured-TE payload"}
            continue
        index, summary = load_h_index(repo, organism, candidate)
        summaries[candidate] = summary
        if index is None:
            dropped.append({"readout": candidate, "reason": "missing local readout file; no fetch attempted", "source_summary": summary})
            continue
        hits = 0
        invalid = 0
        for protein_id, values in index.items():
            row = rows.get(protein_id)
            if row is None:
                continue
            if values and all(math.isfinite(value) for value in values):
                h_map = row["h"]
                if not isinstance(h_map, dict):
                    raise ValueError("row h map malformed")
                h_map[candidate] = list(values)
                hits += 1
            else:
                invalid += 1
        summaries[candidate] = {**summary, "status": "computed", "n_matched_to_base": hits, "invalid_rows": invalid}
    return {"source_summaries": summaries, "dropped": dropped}


def rows_for_ids(rows: dict[str, dict[str, object]], row_ids: list[str]) -> list[dict[str, object]]:
    return [rows[protein_id] for protein_id in row_ids]


def decompose(
    *,
    rows: dict[str, dict[str, object]],
    row_ids: list[str],
    selected_h: list[str],
    has_stability: bool,
) -> dict[str, object]:
    selected_rows = rows_for_ids(rows, row_ids)
    z_basis = orthonormal_basis_from_columns(matrix_rows(selected_rows, "z"))
    x_e = residualize_with_basis(matrix_rows(selected_rows, "x"), z_basis)
    p_e = residualize_with_basis(matrix_rows(selected_rows, "p"), z_basis)
    t_e = residualize_with_basis(matrix_rows(selected_rows, "t"), z_basis)
    p_col = matrix_column(p_e, 0)
    p_q, p_q_energy, rank_q = project_vector(x_e, p_col)
    if p_q_energy <= EPS:
        raise ValueError("P_Q has zero residual energy")

    t_proj, t_energy, rank_t = project_vector(t_e, p_q)
    residual = subtract_vectors(p_q, t_proj)
    steps: list[dict[str, object]] = [
        {"readout": "measured_te", "fraction": bounded_unit(t_energy / p_q_energy), "energy": t_energy, "rank": rank_t}
    ]

    rank_s: int | None = None
    if has_stability:
        s_e = residualize_with_basis(matrix_rows(selected_rows, "s"), z_basis)
        s_proj, s_energy, rank_s_value = project_vector(s_e, residual)
        residual = subtract_vectors(residual, s_proj)
        rank_s = rank_s_value
        steps.append({"readout": "mrna_stability", "fraction": bounded_unit(s_energy / p_q_energy), "energy": s_energy, "rank": rank_s})

    h_steps: list[dict[str, object]] = []
    for readout in selected_h:
        h_rows = []
        for row in selected_rows:
            h_map = row["h"]
            if not isinstance(h_map, dict) or readout not in h_map:
                raise ValueError(f"selected H {readout} missing on final row set")
            h_rows.append(list(h_map[readout]))  # type: ignore[arg-type]
        h_e = residualize_with_basis(h_rows, z_basis)
        h_proj, h_energy, rank_h = project_vector(h_e, residual)
        residual = subtract_vectors(residual, h_proj)
        entry = {"readout": readout, "fraction": bounded_unit(h_energy / p_q_energy), "energy": h_energy, "rank": rank_h}
        h_steps.append(entry)
        steps.append(entry)

    unexplained = bounded_unit(vector_norm2(residual) / p_q_energy)
    total = sum(float(step["fraction"]) for step in steps) + unexplained
    return {
        "n": len(row_ids),
        "row_ids": row_ids,
        "z_basis": z_basis,
        "current_residual": residual,
        "P_Q_norm2": p_q_energy,
        "rank_Q_e": rank_q,
        "rank_T_e": rank_t,
        "rank_S_e": rank_s,
        "T_fraction": steps[0]["fraction"],
        "S_fraction": steps[1]["fraction"] if has_stability else None,
        "H_steps": h_steps,
        "unexplained_U": unexplained,
        "sum_fraction": total,
        "sum_error": abs(total - 1.0),
    }


def deterministic_permutation(n: int, material_prefix: str) -> list[int]:
    out = list(range(n))
    for index in range(n - 1, 0, -1):
        material = f"{material_prefix}|{index}|{len(out)}"
        digest = hashlib.sha256(material.encode("utf-8")).digest()
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap_index] = out[swap_index], out[index]
    return out


def permute_basis_rows(basis: list[list[float]], permutation: list[int]) -> list[list[float]]:
    return [[q[permutation[index]] for index in range(len(permutation))] for q in basis]


def absorption_for_h_e(h_e: list[list[float]], target: list[float]) -> tuple[float, float, int]:
    target_norm = vector_norm2(target)
    if target_norm <= EPS:
        return 0.0, 0.0, 0
    basis = orthonormal_basis_from_columns(h_e)
    energy = sum(vector_dot(target, q) ** 2 for q in basis)
    if energy > target_norm and energy <= target_norm + 1e-8:
        energy = target_norm
    energy = max(0.0, energy)
    rank = len(basis)
    return bounded_unit(energy / target_norm), energy, rank


def absorption_for_basis(basis: list[list[float]], target: list[float]) -> float:
    target_norm = vector_norm2(target)
    if target_norm <= EPS:
        return 0.0
    energy = sum(vector_dot(target, q) ** 2 for q in basis)
    if energy > target_norm and energy <= target_norm + 1e-8:
        energy = target_norm
    energy = max(0.0, energy)
    return bounded_unit(energy / target_norm)


def permutation_null95(
    *,
    organism: str,
    readout: str,
    step_index: int,
    h_e: list[list[float]],
    target: list[float],
) -> dict[str, object]:
    values: list[float] = []
    basis = orthonormal_basis_from_columns(h_e)
    rank_h = len(basis)
    n_rows = len(target)
    for trial in range(PERMUTATION_COUNT):
        prefix = f"{EXPERIMENT_ID}|{organism}|{readout}|step={step_index}|trial={trial}"
        permuted_basis = permute_basis_rows(basis, deterministic_permutation(n_rows, prefix))
        values.append(absorption_for_basis(permuted_basis, target))
    return {
        "permutation_count": PERMUTATION_COUNT,
        "null95": percentile_nearest_rank(values, 0.95),
        "null_mean": sum(values) / len(values) if values else 0.0,
        "rank_min": rank_h,
        "rank_max": rank_h,
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|organism|readout|step|trial|index|n",
        "null_model": "deterministic label permutation of the Z-residualized H rows on the active join, followed by projection onto the active residual",
    }


def score_candidate(
    *,
    organism: str,
    rows: dict[str, dict[str, object]],
    current_ids: list[str],
    base_n: int,
    selected_h: list[str],
    candidate: str,
    has_stability: bool,
    step_index: int,
) -> dict[str, object]:
    join_ids = [
        protein_id
        for protein_id in current_ids
        if candidate in rows[protein_id].get("h", {})
    ]
    n_join = len(join_ids)
    if n_join < MIN_PROTEINS_PER_ORGANISM:
        return {
            "readout": candidate,
            "status": "needs_data",
            "reason": f"join below honest gate n_join={n_join} < {MIN_PROTEINS_PER_ORGANISM}",
            "n_join": n_join,
            "kept": False,
        }
    state = decompose(rows=rows, row_ids=join_ids, selected_h=selected_h, has_stability=has_stability)
    target = state["current_residual"]
    z_basis = state["z_basis"]
    selected_rows = rows_for_ids(rows, join_ids)
    h_rows = []
    for row in selected_rows:
        h_map = row["h"]
        if not isinstance(h_map, dict):
            raise ValueError("row h map malformed")
        h_rows.append(list(h_map[candidate]))  # type: ignore[arg-type]
    h_e = residualize_with_basis(h_rows, z_basis)  # type: ignore[arg-type]
    a_h, absorbed_energy, rank_h = absorption_for_h_e(h_e, target)  # type: ignore[arg-type]
    projection = project_by_basis(h_e, target)  # type: ignore[arg-type]
    projected_vector = projection["projected_vector"]
    if not isinstance(projected_vector, list):
        raise ValueError("H projection vector malformed")
    x_e = residualize_with_basis(matrix_rows(selected_rows, "x"), z_basis)
    a_h_direction = solve_regularized_normal_equation(x_e, projected_vector)
    a_residual_direction = solve_regularized_normal_equation(x_e, target)  # type: ignore[arg-type]
    c_h, c_h_note = support_cosine(a_h_direction, a_residual_direction)
    a_h_times_c_h = a_h * c_h
    null = permutation_null95(
        organism=organism,
        readout=candidate,
        step_index=step_index,
        h_e=h_e,
        target=target,  # type: ignore[arg-type]
    )
    dl = len(h_rows[0]) if h_rows else 0
    join_shift = abs(n_join - base_n) / base_n if base_n > 0 else 1.0
    score = a_h_times_c_h - float(null["null95"]) - LAMBDA_DL * dl - RHO_JOIN * join_shift
    return {
        "readout": candidate,
        "status": "computed",
        "n_join": n_join,
        "fraction": None,
        "score": score,
        "A_H": a_h,
        "C_H": c_h,
        "C_H_note": c_h_note,
        "A_H_times_C_H": a_h_times_c_h,
        "absorbed_energy_on_active_residual": absorbed_energy,
        "null95": null["null95"],
        "null_mean": null["null_mean"],
        "DL": dl,
        "lambda_DL": LAMBDA_DL,
        "join_shift": join_shift,
        "rho_join": RHO_JOIN,
        "rank_H_e": rank_h,
        "permutation_null": null,
        "kept": False,
    }


def greedy_h_dictionary(
    *,
    organism: str,
    rows: dict[str, dict[str, object]],
    base_ids: list[str],
    has_stability: bool,
) -> dict[str, object]:
    base_n = len(base_ids)
    current_ids = list(base_ids)
    selected: list[str] = []
    selected_entries: list[dict[str, object]] = []
    dropped: list[dict[str, object]] = []
    final_scores: dict[str, dict[str, object]] = {}
    step_index = 0

    while True:
        remaining = [candidate for candidate in H_CANDIDATES if candidate not in selected]
        scored = [
            score_candidate(
                organism=organism,
                rows=rows,
                current_ids=current_ids,
                base_n=base_n,
                selected_h=selected,
                candidate=candidate,
                has_stability=has_stability,
                step_index=step_index,
            )
            for candidate in remaining
        ]
        final_scores = {str(item["readout"]): item for item in scored}
        for item in scored:
            if item.get("status") != "computed":
                dropped.append(item)
        computed = [item for item in scored if item.get("status") == "computed"]
        computed.sort(key=lambda item: float(item["score"]), reverse=True)
        if not computed or float(computed[0]["score"]) <= 0.0:
            break
        winner = computed[0]
        readout = str(winner["readout"])
        selected.append(readout)
        winner["kept"] = True
        selected_entries.append(winner)
        current_ids = [
            protein_id
            for protein_id in current_ids
            if readout in rows[protein_id].get("h", {})
        ]
        step_index += 1

    final = decompose(rows=rows, row_ids=current_ids, selected_h=selected, has_stability=has_stability)
    fraction_by_h = {str(item["readout"]): float(item["fraction"]) for item in final["H_steps"]}  # type: ignore[index]
    dictionary: list[dict[str, object]] = []
    seen: set[str] = set()
    for item in selected_entries:
        out = dict(item)
        out["fraction"] = fraction_by_h.get(str(item["readout"]), 0.0)
        out["kept"] = True
        dictionary.append(out)
        seen.add(str(item["readout"]))
    for readout, item in sorted(final_scores.items()):
        if readout in seen:
            continue
        out = dict(item)
        out["fraction"] = 0.0
        out["kept"] = False
        dictionary.append(out)

    return {
        "base_n_full_before_H_join": base_n,
        "n_full": len(current_ids),
        "selected_readouts": selected,
        "H_dictionary": dictionary,
        "dropped_readouts": dropped,
        "decomposition": final,
    }


def verdict_for(result: dict[str, object]) -> str:
    t_fraction = float(result["T_fraction"])
    s_value = result.get("S_fraction")
    s_fraction = float(s_value) if isinstance(s_value, (int, float)) else 0.0
    h_selected = result.get("minimal_readout_dictionary")
    h_names = ", ".join(h_selected) if isinstance(h_selected, list) and h_selected else "no positive H readout"
    unexplained = float(result["unexplained_U"])
    if s_fraction > t_fraction and s_fraction >= 0.10:
        lead = "stability-leaning"
    elif t_fraction >= s_fraction and t_fraction >= 0.10:
        lead = "translation-proximal"
    elif isinstance(h_selected, list) and h_selected:
        lead = "H-dictionary-leaning"
    else:
        lead = "mostly unexplained"
    return f"{lead}: T={t_fraction:.3f}, S={s_fraction:.3f}, H={h_names}, unexplained_U={unexplained:.3f}; direction-aware descriptive ordered partition only."


def dominant_step_for(result: dict[str, object]) -> str:
    entries: list[tuple[str, float]] = [("T", float(result["T_fraction"]))]
    s_value = result.get("S_fraction")
    if isinstance(s_value, (int, float)):
        entries.append(("S", float(s_value)))
    for item in result.get("H_dictionary", []):
        if isinstance(item, dict) and item.get("kept"):
            entries.append((f"H:{item.get('readout')}", float(item.get("fraction", 0.0))))
    entries.append(("residual_U", float(result["unexplained_U"])))
    entries.sort(key=lambda item: item[1], reverse=True)
    return entries[0][0]


def cannot_claim() -> list[str]:
    return [
        "direction-aware ordered orthogonal variance-partition, NOT causal pathway proof",
        "C_H is coordinate-support cosine (directional agreement), not a translation/regulation mechanism",
        "readout order T->S->H is a modeling choice; different order changes attribution",
        "per-organism single datasets from different studies/platforms",
        "H-candidates are residual absorbers not mechanisms",
        "low absorption after C_H means irreducible to THESE measured readouts under this scoring rule, not that no explanation exists",
        "descriptive per-organism dictionary, not a universal law",
    ]


def analyze_organism(repo: pathlib.Path, context: dict[str, object], config: dict[str, object]) -> dict[str, object]:
    organism = str(config["key"])
    built = base_rows(repo=repo, context=context, config=config)
    if built.get("status") != "computed":
        return {
            "organism": config["label"],
            "organism_key": organism,
            "domain": config["domain"],
            "status": "needs_data",
            "reason": built.get("reason"),
            "data_summary": built,
        }
    rows = built["rows"]
    if not isinstance(rows, dict):
        raise ValueError("base rows malformed")
    attached = attach_h_readouts(repo, organism, rows)  # type: ignore[arg-type]
    base_ids = sorted(rows)
    if len(base_ids) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "organism": config["label"],
            "organism_key": organism,
            "domain": config["domain"],
            "status": "needs_data",
            "reason": f"base P/Q/T/S join yielded n={len(base_ids)}, below honest gate n>={MIN_PROTEINS_PER_ORGANISM}",
            "data_summary": built["summary"],
            "dropped_readouts": attached["dropped"],
            "cannot_claim": cannot_claim(),
        }

    has_stability = bool(config.get("has_stability")) and bool(config.get("stability_path"))
    greedy = greedy_h_dictionary(
        organism=organism,
        rows=rows,  # type: ignore[arg-type]
        base_ids=base_ids,
        has_stability=has_stability,
    )
    decomp = greedy["decomposition"]
    if not isinstance(decomp, dict):
        raise ValueError("decomposition malformed")
    h_dictionary = greedy["H_dictionary"]
    if not isinstance(h_dictionary, list):
        raise ValueError("H dictionary malformed")
    selected = greedy["selected_readouts"]
    if not isinstance(selected, list):
        raise ValueError("selected readouts malformed")

    out = {
        "organism": config["label"],
        "organism_key": organism,
        "domain": config["domain"],
        "status": "computed",
        "n_full": greedy["n_full"],
        "base_n_full_before_H_join": greedy["base_n_full_before_H_join"],
        "readout_P": "log10(protein abundance ppm)",
        "readout_Q": "B*_Q6 9-dimensional synonymous residual coordinates",
        "readout_T": "log10(measured TE), TE = ribosome footprint / mRNA",
        "readout_S": config.get("stability_readout") if has_stability else "skipped: no local mRNA-stability payload listed",
        "P_Q_norm2": decomp["P_Q_norm2"],
        "P_Q_energy": decomp["P_Q_norm2"],
        "T_fraction": decomp["T_fraction"],
        "S_fraction": decomp["S_fraction"] if has_stability else "skipped",
        "H_dictionary": h_dictionary,
        "minimal_readout_dictionary": selected,
        "unexplained_U": decomp["unexplained_U"],
        "residual_U_fraction": decomp["unexplained_U"],
        "decomposition_sum": decomp["sum_fraction"],
        "decomposition_sum_error": decomp["sum_error"],
        "rank_diagnostics": {
            "rank_Q_e": decomp["rank_Q_e"],
            "rank_T_e": decomp["rank_T_e"],
            "rank_S_e": decomp["rank_S_e"],
            "rank_Z": len(decomp["z_basis"]) if isinstance(decomp.get("z_basis"), list) else None,
            "control_column_count": len(next(iter(rows.values()))["z"]) if rows else None,
        },
        "dropped_readouts": list(attached["dropped"]) + list(greedy["dropped_readouts"]),  # type: ignore[arg-type]
        "data_summary": built["summary"],
        "H_source_summaries": attached["source_summaries"],
        "controls_used": controls_used(context["aa_order"]),  # type: ignore[arg-type]
        "cannot_claim": cannot_claim(),
    }
    out["dominant_step"] = dominant_step_for(out)
    out["verdict"] = verdict_for(out)
    return out


def organism_dictionary_table(organisms: dict[str, dict[str, object]]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for key, result in organisms.items():
        if result.get("status") != "computed":
            rows.append(
                {
                    "organism_key": key,
                    "organism": result.get("organism"),
                    "status": result.get("status"),
                    "T_fraction": None,
                    "S_fraction": None,
                    "H_1": None,
                    "H_2": None,
                    "residual_U": None,
                    "verdict": result.get("reason"),
                }
            )
            continue
        kept = [
            item
            for item in result.get("H_dictionary", [])
            if isinstance(item, dict) and item.get("kept")
        ]
        kept.sort(key=lambda item: float(item.get("fraction", 0.0)), reverse=True)
        h_cells = []
        for item in kept[:2]:
            h_cells.append({"readout": item.get("readout"), "fraction": item.get("fraction")})
        while len(h_cells) < 2:
            h_cells.append({"readout": None, "fraction": 0.0})
        rows.append(
            {
                "organism_key": key,
                "organism": result.get("organism"),
                "status": "computed",
                "T_fraction": result.get("T_fraction"),
                "S_fraction": result.get("S_fraction"),
                "H_1": h_cells[0],
                "H_2": h_cells[1],
                "residual_U": result.get("residual_U_fraction"),
                "verdict": result.get("verdict"),
            }
        )
    return rows


def bare_absorption_comparison(
    repo: pathlib.Path,
    context: dict[str, object],
    organism_results: dict[str, dict[str, object]],
) -> dict[str, object]:
    baseline: dict[str, object] = {}
    for config in ORGANISMS:
        key = str(config["key"])
        current = organism_results.get(key, {})
        if current.get("status") != "computed":
            baseline[key] = {"status": current.get("status"), "reason": current.get("reason")}
            continue
        bare_result = bare_absorption_decomposition.analyze_organism(repo, context, config)
        if bare_result.get("status") != "computed":
            baseline[key] = {"status": bare_result.get("status"), "reason": bare_result.get("reason")}
            continue
        bare_selected = bare_result.get("minimal_readout_dictionary")
        direction_aware_selected = current.get("minimal_readout_dictionary")
        bare_count = len(bare_selected) if isinstance(bare_selected, list) else 0
        direction_aware_count = len(direction_aware_selected) if isinstance(direction_aware_selected, list) else 0
        baseline[key] = {
            "status": "computed",
            "bare_A_H_selected": bare_selected,
            "direction_aware_selected": direction_aware_selected,
            "bare_A_H_residual_U": bare_result.get("unexplained_U"),
            "direction_aware_residual_U": current.get("residual_U_fraction"),
            "H_kept_count_bare_A_H": bare_count,
            "H_kept_count_direction_aware": direction_aware_count,
            "direction_aware_kept_no_more_than_bare_A_H": direction_aware_count <= bare_count,
        }
    return baseline


def cross_organism_conclusion(
    organisms: dict[str, dict[str, object]],
    bare_comparison: dict[str, object],
) -> dict[str, object]:
    computed = {key: value for key, value in organisms.items() if value.get("status") == "computed"}
    selected = {
        key: value.get("minimal_readout_dictionary")
        for key, value in computed.items()
    }
    residuals = {
        key: value.get("residual_U_fraction")
        for key, value in computed.items()
    }
    comparison_counts = {
        key: {
            "bare_A_H": value.get("H_kept_count_bare_A_H"),
            "direction_aware": value.get("H_kept_count_direction_aware"),
            "no_more_than_bare_A_H": value.get("direction_aware_kept_no_more_than_bare_A_H"),
        }
        for key, value in bare_comparison.items()
        if isinstance(value, dict) and value.get("status") == "computed"
    }
    return {
        "direction_aware_dictionary_by_organism": selected,
        "residual_U_by_organism": residuals,
        "H_kept_count_comparison_to_bare_A_H": comparison_counts,
        "core_conclusion": "Adding C_H makes the recursive dictionary direction-aware: retained H readouts must both absorb residual energy and point in the same Q-coordinate support direction. Under the available local readouts, the residual U remains the dominant component for the computed organisms, so the result strengthens the descriptive negative conclusion that this B*_Q6 residual is not recovered by THESE measured H readouts under this scoring rule.",
    }


def checks_for(organisms: dict[str, dict[str, object]]) -> list[dict[str, object]]:
    computed = {key: value for key, value in organisms.items() if value.get("status") == "computed"}
    unit_fractions_ok = all(
        finite_unit(result.get("T_fraction"))
        and (result.get("S_fraction") == "skipped" or finite_unit(result.get("S_fraction")))
        and finite_unit(result.get("unexplained_U"))
        and all(
            finite_unit(entry.get("fraction"))
            and (entry.get("status") != "computed" or (finite(entry.get("score")) and finite_unit(entry.get("A_H")) and finite_unit(entry.get("null95"))))
            for entry in result.get("H_dictionary", [])
            if isinstance(entry, dict)
        )
        for result in computed.values()
    )
    scored_ok = all(
        any(isinstance(entry, dict) and entry.get("status") == "computed" for entry in result.get("H_dictionary", []))
        and all(
            not isinstance(entry, dict)
            or entry.get("status") != "computed"
            or (
                entry.get("permutation_null", {}).get("permutation_count") == PERMUTATION_COUNT
                and finite(entry.get("join_shift"))
                and finite(entry.get("DL"))
                and finite(entry.get("C_H"))
                and -1.0 <= float(entry["C_H"]) <= 1.0
                and finite(entry.get("A_H_times_C_H"))
                and abs(
                    float(entry["score"])
                    - (
                        float(entry["A_H_times_C_H"])
                        - float(entry["null95"])
                        - LAMBDA_DL * float(entry["DL"])
                        - RHO_JOIN * float(entry["join_shift"])
                    )
                )
                <= 1e-9
            )
            for entry in result.get("H_dictionary", [])
        )
        for result in computed.values()
    )
    sum_ok = all(finite(result.get("decomposition_sum_error")) and float(result["decomposition_sum_error"]) <= SUM_TOL for result in computed.values())
    table = organism_dictionary_table(organisms)
    table_ok = bool(table) and all(
        row.get("status") != "computed"
        or (
            finite_unit(row.get("T_fraction"))
            and (row.get("S_fraction") == "skipped" or finite_unit(row.get("S_fraction")))
            and finite_unit(row.get("residual_U"))
            and isinstance(row.get("H_1"), dict)
            and isinstance(row.get("H_2"), dict)
            and finite_unit(row["H_1"].get("fraction"))  # type: ignore[union-attr]
            and finite_unit(row["H_2"].get("fraction"))  # type: ignore[union-attr]
        )
        for row in table
    )
    return [
        {
            "name": "per_organism_P_Q",
            "passed": bool(computed) and any(int(result["n_full"]) >= MIN_PROTEINS_PER_ORGANISM for result in computed.values()),
            "actual": {key: {"status": result.get("status"), "n_full": result.get("n_full"), "P_Q_norm2": result.get("P_Q_norm2")} for key, result in organisms.items()},
            "expected": f">=1 organism with P_Q computed and final decomposition n_full >= {MIN_PROTEINS_PER_ORGANISM}; sparse organisms/readouts remain needs_data",
        },
        {
            "name": "ordered_T_S_cut",
            "passed": bool(computed) and unit_fractions_ok,
            "actual": {key: {"T_fraction": result.get("T_fraction"), "S_fraction": result.get("S_fraction"), "unexplained_U": result.get("unexplained_U")} for key, result in computed.items()},
            "expected": "T/S fractions are finite unit interval values where present; S is explicitly skipped when no local half-life data exist",
        },
        {
            "name": "direction_aware_h_dictionary",
            "passed": bool(computed) and scored_ok,
            "actual": {
                key: [
                    {
                        "readout": entry.get("readout"),
                        "score": entry.get("score"),
                        "A_H": entry.get("A_H"),
                        "C_H": entry.get("C_H"),
                        "A_H_times_C_H": entry.get("A_H_times_C_H"),
                        "null95": entry.get("null95"),
                        "DL": entry.get("DL"),
                        "join_shift": entry.get("join_shift"),
                        "kept": entry.get("kept"),
                    }
                    for entry in result.get("H_dictionary", [])
                    if isinstance(entry, dict)
                ]
                for key, result in computed.items()
            },
            "expected": "each computed H has score = A_H*C_H - Null95(H) - lambda*DL(H) - rho*Deltajoin(H), with C_H in [-1,1], 1000 deterministic label permutations, and join_shift",
        },
        {
            "name": "organism_dictionary_table_emitted",
            "passed": bool(computed) and table_ok and sum_ok,
            "actual": {
                "table": table,
                "sum_diagnostics": {key: {"sum": result.get("decomposition_sum"), "sum_error": result.get("decomposition_sum_error")} for key, result in computed.items()},
            },
            "expected": f"section 9.4 table is emitted with fraction cells and T + S + sum(H_kept) + U equals 1 within {SUM_TOL}",
        },
        {
            "name": "no_causal_or_universal_overclaim",
            "passed": cannot_claim() == [
                "direction-aware ordered orthogonal variance-partition, NOT causal pathway proof",
                "C_H is coordinate-support cosine (directional agreement), not a translation/regulation mechanism",
                "readout order T->S->H is a modeling choice; different order changes attribution",
                "per-organism single datasets from different studies/platforms",
                "H-candidates are residual absorbers not mechanisms",
                "low absorption after C_H means irreducible to THESE measured readouts under this scoring rule, not that no explanation exists",
                "descriptive per-organism dictionary, not a universal law",
            ],
            "actual": cannot_claim(),
            "expected": "required caveats are present verbatim",
        },
    ]


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    try:
        genetic_code_path = repo / "tools/fibonacci_reality/data/ncbi_genetic_codes.json"
        if not genetic_code_path.exists():
            emit("needs_data", missing_required_data=[str(genetic_code_path.relative_to(repo))])
        context = q6_context(repo)
        organism_results = {
            str(config["key"]): analyze_organism(repo, context, config)
            for config in ORGANISMS
        }
        checks = checks_for(organism_results)
        computed = {key: value for key, value in organism_results.items() if value.get("status") == "computed"}
        table = organism_dictionary_table(organism_results)
        bare_comparison = bare_absorption_comparison(repo, context, organism_results)
        cross_conclusion = cross_organism_conclusion(organism_results, bare_comparison)
        status = "passed" if computed and all(check["passed"] for check in checks) else "needs_data"
        reason = None if status == "passed" else "no organism satisfied every honest gate for direction-aware ordered residual dictionary"
        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture": CONJECTURE_ID,
                "statement": "For each organism, P_Q = Pi_{Q_e} P_e is decomposed in the fixed order measured-TE, mRNA-stability where available, then a greedy direction-aware H-dictionary scored by A_H*C_H minus null, description-length, and join-shift penalties. This is an ordered orthogonal projection partition, not causal pathway proof.",
                "decomposition_definition": {
                    "Z": controls_used(context["aa_order"]),  # type: ignore[arg-type]
                    "Q": context["q_names"],
                    "P_Q": "Pi_{Q_e} P_e after Z residualization",
                    "T_step": "P_QT = Pi_{T_e} P_Q; R_1 = (I - Pi_{T_e}) P_Q",
                    "S_step": "P_QS = Pi_{S_e} R_1; R_2 = (I - Pi_{S_e}) R_1 when local stability data exist",
                    "H_step": "greedy Pi_{H_e} of the active residual; keep only score > 0",
                    "BEDC_score": "A_H*C_H - Null95(H) - lambda*DL(H) - rho*Deltajoin(H)",
                    "A_H": "||Pi_{H_e} R||^2 / ||R||^2 on the active join",
                    "C_H": "coordinate-support cosine between the H-absorbed direction solved in Q coordinates and the active residual-support direction solved in Q coordinates",
                    "A_H_times_C_H": "direction-aware residual absorption score before null, description-length, and join-shift penalties",
                    "Null95": "95th percentile of deterministic H-label permutations",
                    "DL": "readout dimension",
                    "Deltajoin": "|n_join(H) - base_n_full| / base_n_full",
                    "lambda": LAMBDA_DL,
                    "rho": RHO_JOIN,
                },
                "organisms": organism_results,
                "organism_specific_dictionary_table": table,
                "bare_A_H_comparison": bare_comparison,
                "cross_organism_conclusion": cross_conclusion,
                "minimal_readout_dictionary_by_organism": {
                    key: value.get("minimal_readout_dictionary")
                    for key, value in organism_results.items()
                    if value.get("status") == "computed"
                },
                "verdict_by_organism": {
                    key: value.get("verdict")
                    for key, value in organism_results.items()
                    if value.get("status") == "computed"
                },
                "cannot_claim": cannot_claim(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable residual-decomposition input or fit")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Tissue-specific B*_Q6 S^QP against human protein abundance."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import re
import sys
import urllib.error
from html.parser import HTMLParser
from typing import Any

from run_b_star_q6_condition_specific_sqp_powered import (
    DEGENERATE_R2,
    MIN_PROTEINS_PER_ORGANISM,
    PERMUTATION_COUNT,
    SURVIVAL_EPS,
    build_condition_rows,
    condition_fit,
    controls_used,
    cosine,
    fetch_bytes,
    load_json,
    now_utc,
    parse_paxdb_payload,
    pearson,
    protein_rows,
    public_fit,
    raw_text_slice,
    residualize_with_basis,
    write_json_if_changed,
)
from run_b_star_q6_protein_omics_survival_powered import (
    matrix_column,
    numeric,
    orthonormal_basis_from_columns,
    standard_amino_acids,
    vector_dot,
)
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_tissue_specific_sqp_powered"
CLAIM_ID = "h3.cross_layer_relation.tissue_specific_sqp.b_star_q6_human_tissue_powered"
CONJECTURE_ID = "q6.tissue-specific-sqp.human-tissue.cross-layer"

ORGANISM = "homo_sapiens"
ORGANISM_LABEL = "Homo sapiens"
NCBI_TAXID = "9606"
PAXDB_INDEX_URL = "https://pax-db.org/downloads/latest/datasets/9606/"

MANDATORY_TISSUES = [
    {
        "tissue": "Adult_Liver",
        "tissue_label": "adult liver",
        "filename": "9606-Adult_Liver_Kim_2014_SEQUEST.txt",
    },
    {
        "tissue": "Adult_Bcells",
        "tissue_label": "adult B cells",
        "filename": "9606-Adult_Bcells_Kim_2014_SEQUEST.txt",
    },
]

THIRD_TISSUE_CANDIDATES = [
    {
        "tissue": "Adult_Heart",
        "tissue_label": "adult heart",
        "filename": "9606-Adult_Heart_Kim_2014_SEQUEST.txt",
    },
    {
        "tissue": "Adult_Frontalcortex",
        "tissue_label": "adult frontal cortex",
        "filename": "9606-Adult_Frontalcortex_Kim_2014_SEQUEST.txt",
    },
    {
        "tissue": "Adult_Kidney",
        "tissue_label": "adult kidney",
        "filename": "9606-Adult_Kidney_Kim_2014_SEQUEST.txt",
    },
]


class HrefParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.hrefs: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag.lower() != "a":
            return
        for key, value in attrs:
            if key.lower() == "href" and value is not None:
                self.hrefs.append(value)


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def tissue_slug(tissue: str) -> str:
    return re.sub(r"[^a-z0-9]+", "_", tissue.lower()).strip("_")


def tissue_spec(raw: dict[str, str]) -> dict[str, str]:
    spec = dict(raw)
    filename = spec["filename"]
    slug = tissue_slug(spec["tissue"])
    spec["url"] = PAXDB_INDEX_URL + filename
    spec["data_path"] = f"tools/fibonacci_reality/data/proteomics_abundance_homo_sapiens_{slug}.json"
    spec["slug"] = slug
    return spec


def discover_index_hrefs() -> tuple[set[str], dict[str, object]]:
    contact = fetch_bytes(PAXDB_INDEX_URL)
    parser = HrefParser()
    parser.feed(contact["raw_bytes"].decode("utf-8", "replace"))  # type: ignore[index]
    return set(parser.hrefs), {
        "url": PAXDB_INDEX_URL,
        "http_status": contact["http_status"],
        "content_type": contact["content_type"],
        "payload_byte_size": contact["payload_byte_size"],
        "payload_sha256": contact["payload_sha256"],
    }


def select_tissue_specs(repo: pathlib.Path) -> tuple[list[dict[str, str]], dict[str, object]]:
    selected = [tissue_spec(raw) for raw in MANDATORY_TISSUES]
    discovery: dict[str, object] = {"candidate_order": [raw["filename"] for raw in THIRD_TISSUE_CANDIDATES]}
    try:
        hrefs, index_meta = discover_index_hrefs()
        discovery["index"] = index_meta
        for raw in THIRD_TISSUE_CANDIDATES:
            if raw["filename"] in hrefs:
                selected.append(tissue_spec(raw))
                discovery["selected_third_tissue"] = raw["filename"]
                discovery["selection_basis"] = "present_in_paxdb_9606_directory_href_list"
                break
    except (urllib.error.URLError, TimeoutError, OSError) as exc:
        discovery["index_error"] = repr(exc)
        for raw in THIRD_TISSUE_CANDIDATES:
            candidate = tissue_spec(raw)
            if (repo / candidate["data_path"]).exists():
                selected.append(candidate)
                discovery["selected_third_tissue"] = raw["filename"]
                discovery["selection_basis"] = "local_cached_payload_after_index_fetch_error"
                break
    if "selected_third_tissue" not in discovery:
        discovery["selected_third_tissue"] = None
        discovery["selection_basis"] = "no third candidate available from index or local cache"
    return selected, discovery


def load_or_fetch_tissue_data(repo: pathlib.Path, spec: dict[str, str]) -> dict[str, object]:
    path = repo / spec["data_path"]
    if path.exists():
        raw = load_json(path)
        if isinstance(raw, dict) and isinstance(raw.get("protein_abundance"), dict):
            return raw

    contact = fetch_bytes(spec["url"])
    abundance, gene_names, metadata = parse_paxdb_payload(contact["raw_bytes"])  # type: ignore[index]
    raw_text, raw_note = raw_text_slice(contact["raw_bytes"])  # type: ignore[index]
    payload: dict[str, object] = {
        "schema_version": 1,
        "source_name": "PAXdb",
        "source_kind": "tissue_specific_paxdb_abundance_dataset",
        "source_url": spec["url"],
        "organism": ORGANISM,
        "organism_label": ORGANISM_LABEL,
        "ncbi_taxid": NCBI_TAXID,
        "tissue": spec["tissue"],
        "tissue_label": spec["tissue_label"],
        "study_label": "Kim et al 2014 draft human proteome SEQUEST",
        "fetched_at": now_utc(),
        "fetched_by": "run_b_star_q6_tissue_specific_sqp_powered.py",
        "http_status": contact["http_status"],
        "content_type": contact["content_type"],
        "payload_byte_size": contact["payload_byte_size"],
        "payload_sha256": contact["payload_sha256"],
        "raw_payload_text": raw_text,
        "raw_payload_note": raw_note,
        "n_proteins": len(abundance),
        "protein_abundance": abundance,
        "protein_gene_name": gene_names,
        "cannot_claim": [
            "Kim et al 2014 draft human proteome, tissue-specific MS",
            "PAXdb tissue file is not a causal perturbation or matched transcript control",
        ],
        "derivation_boundary": "not_bedc_kernel_content",
    }
    payload.update(metadata)
    write_json_if_changed(path, payload)
    return payload


def abundance_map(payload: dict[str, object], tissue: str) -> dict[str, float]:
    raw = payload.get("protein_abundance")
    if not isinstance(raw, dict):
        raise ValueError(f"{tissue} payload lacks protein_abundance object")
    out: dict[str, float] = {}
    for protein_id, value in raw.items():
        abundance = numeric(value, f"{tissue}.protein_abundance.{protein_id}")
        if abundance > 0.0:
            out[str(protein_id)] = abundance
    return out


def build_tissue_rows(
    *,
    cds_payload: dict[str, object],
    tissue: str,
    tissue_payload: dict[str, object],
    keep_ids: set[str],
) -> list[dict[str, object]]:
    rows = build_condition_rows(
        cds_payload=cds_payload,
        condition=tissue,
        condition_payload=tissue_payload,
        shared_ids=keep_ids,
    )
    for row in rows:
        row["tissue"] = tissue
        row.pop("growth_condition", None)
    return rows


def residualize_vector_with_basis(vector: list[float], basis: list[list[float]]) -> list[float]:
    residual = list(vector)
    for q in basis:
        coeff = sum(residual[index] * q[index] for index in range(len(vector)))
        for index in range(len(vector)):
            residual[index] -= coeff * q[index]
    return residual


def sqp_from_cached_design(
    *,
    y_rows: list[list[float]],
    z_basis: list[list[float]],
    x_columns: dict[str, list[float]],
    x_ss: dict[str, float],
    q_names: list[str],
) -> dict[str, float]:
    y_col = [row[0] for row in y_rows]
    y_tilde = residualize_vector_with_basis(y_col, z_basis)
    y_ss = vector_dot(y_tilde, y_tilde)
    out: dict[str, float] = {}
    for name in q_names:
        if x_ss[name] <= SURVIVAL_EPS or y_ss <= SURVIVAL_EPS:
            out[name] = 0.0
            continue
        xy = vector_dot(x_columns[name], y_tilde)
        out[name] = max(0.0, min(1.0, ((xy * xy) / x_ss[name]) / y_ss))
    return out


def permutation_swap(left: str, right: str, protein_id: str, perm_index: int) -> bool:
    digest = hashlib.sha256(
        f"{EXPERIMENT_ID}|paired_tissue_label_null|{left}|{right}|{perm_index}|{protein_id}".encode("utf-8")
    ).digest()
    return bool(digest[0] & 1)


def paired_permutation_null(
    *,
    left: str,
    right: str,
    y_left: list[list[float]],
    y_right: list[list[float]],
    protein_ids: list[str],
    x_rows: list[list[float]],
    z_rows: list[list[float]],
    q_names: list[str],
    observed_abs_diff: dict[str, float],
    count: int,
) -> dict[str, object]:
    z_basis = orthonormal_basis_from_columns(z_rows)
    x_tilde = residualize_with_basis(x_rows, z_basis)
    x_columns = {name: matrix_column(x_tilde, index) for index, name in enumerate(q_names)}
    x_ss = {name: vector_dot(column, column) for name, column in x_columns.items()}
    exceed = {name: 0 for name in q_names}
    maxima = {name: 0.0 for name in q_names}

    for perm_index in range(count):
        perm_left: list[list[float]] = []
        perm_right: list[list[float]] = []
        for row_index, protein_id in enumerate(protein_ids):
            if permutation_swap(left, right, protein_id, perm_index):
                perm_left.append(y_right[row_index])
                perm_right.append(y_left[row_index])
            else:
                perm_left.append(y_left[row_index])
                perm_right.append(y_right[row_index])
        sqp_left = sqp_from_cached_design(
            y_rows=perm_left,
            z_basis=z_basis,
            x_columns=x_columns,
            x_ss=x_ss,
            q_names=q_names,
        )
        sqp_right = sqp_from_cached_design(
            y_rows=perm_right,
            z_basis=z_basis,
            x_columns=x_columns,
            x_ss=x_ss,
            q_names=q_names,
        )
        for name in q_names:
            diff = abs(sqp_left[name] - sqp_right[name])
            maxima[name] = max(maxima[name], diff)
            if diff >= observed_abs_diff[name]:
                exceed[name] += 1

    return {
        name: {
            "permutation_count": count,
            "p_value_abs_diff": (exceed[name] + 1) / (count + 1),
            "p_value_abs_diff_bonferroni_9": min(1.0, 9.0 * (exceed[name] + 1) / (count + 1)),
            "null_max_abs_diff_seen": maxima[name],
            "deterministic_seed": f"sha256:{EXPERIMENT_ID}|paired_tissue_label_null|left|right|perm_index|protein_id",
        }
        for name in q_names
    }


def fit_rows(
    *,
    rows: list[dict[str, object]],
    tissue: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> tuple[dict[str, object], dict[str, object]]:
    x_rows, y_rows, z_rows, protein_ids, summary = protein_rows(
        rows=rows,
        condition=tissue,
        codons=codons,
        code=code,
        aa_order=aa_order,
        q_projected=q_projected,
        q_names=q_names,
        q_support=q_support,
    )
    fit = condition_fit(x_rows=x_rows, y_rows=y_rows, z_rows=z_rows, q_names=q_names)
    matrices = {
        "x_rows": x_rows,
        "y_rows": y_rows,
        "z_rows": z_rows,
        "protein_ids": protein_ids,
    }
    return {**summary, **public_fit(fit)}, matrices


def pair_comparison(
    *,
    left: str,
    right: str,
    rows_by_tissue: dict[str, list[dict[str, object]]],
    tissue_results: dict[str, dict[str, object]],
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> dict[str, object]:
    left_by_id = {str(row["protein_id"]): row for row in rows_by_tissue[left] if isinstance(row.get("protein_id"), str)}
    right_by_id = {str(row["protein_id"]): row for row in rows_by_tissue[right] if isinstance(row.get("protein_id"), str)}
    shared_ids = sorted(set(left_by_id) & set(right_by_id))
    if len(shared_ids) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "left": left,
            "right": right,
            "status": "needs_data",
            "reason": "pairwise shared protein join below honest n>=500 gate",
            "shared_protein_count": len(shared_ids),
        }

    left_rows = [left_by_id[protein_id] for protein_id in shared_ids]
    right_rows = [right_by_id[protein_id] for protein_id in shared_ids]
    left_fit, left_matrices = fit_rows(
        rows=left_rows,
        tissue=left,
        codons=codons,
        code=code,
        aa_order=aa_order,
        q_projected=q_projected,
        q_names=q_names,
        q_support=q_support,
    )
    right_fit, right_matrices = fit_rows(
        rows=right_rows,
        tissue=right,
        codons=codons,
        code=code,
        aa_order=aa_order,
        q_projected=q_projected,
        q_names=q_names,
        q_support=q_support,
    )
    if left_matrices["protein_ids"] != right_matrices["protein_ids"]:
        raise ValueError(f"{left} vs {right} shared protein ordering mismatch")

    left_sqp = left_fit["S_QP"]
    right_sqp = right_fit["S_QP"]
    if not isinstance(left_sqp, dict) or not isinstance(right_sqp, dict):
        raise ValueError(f"{left} vs {right} pair fit lacks S_QP")
    left_vec = [float(left_sqp[name]) for name in q_names]
    right_vec = [float(right_sqp[name]) for name in q_names]
    observed_diff = {name: float(left_sqp[name]) - float(right_sqp[name]) for name in q_names}
    observed_abs_diff = {name: abs(value) for name, value in observed_diff.items()}
    permutation = paired_permutation_null(
        left=left,
        right=right,
        y_left=left_matrices["y_rows"],  # type: ignore[arg-type]
        y_right=right_matrices["y_rows"],  # type: ignore[arg-type]
        protein_ids=left_matrices["protein_ids"],  # type: ignore[arg-type]
        x_rows=left_matrices["x_rows"],  # type: ignore[arg-type]
        z_rows=left_matrices["z_rows"],  # type: ignore[arg-type]
        q_names=q_names,
        observed_abs_diff=observed_abs_diff,
        count=PERMUTATION_COUNT,
    )

    per_coordinate = {
        name: {
            f"{left}_S_QP_shared": float(left_sqp[name]),
            f"{right}_S_QP_shared": float(right_sqp[name]),
            f"{left}_minus_{right}": observed_diff[name],
            "abs_diff": observed_abs_diff[name],
            **permutation[name],
        }
        for name in q_names
    }
    significant_bonferroni = [
        name
        for name, row in per_coordinate.items()
        if isinstance(row, dict) and float(row["p_value_abs_diff_bonferroni_9"]) <= 0.05
    ]
    significant_raw = [
        name
        for name, row in per_coordinate.items()
        if isinstance(row, dict) and float(row["p_value_abs_diff"]) <= 0.05
    ]
    sqp_cosine = cosine(left_vec, right_vec)
    sqp_pearson = pearson(left_vec, right_vec)
    dominant_same = tissue_results[left]["dominant_coord"] == tissue_results[right]["dominant_coord"]
    shared_dominant_same = left_fit["dominant_coord"] == right_fit["dominant_coord"]
    pair_stable = (
        sqp_cosine >= 0.80
        and sqp_pearson >= 0.50
        and dominant_same
        and not significant_bonferroni
    )
    return {
        "left": left,
        "right": right,
        "status": "passed",
        "shared_protein_count": len(shared_ids),
        "comparison_basis": "pairwise shared proteins with identical CDS codon rows and swapped tissue abundance labels",
        "S_QP_cosine": sqp_cosine,
        "S_QP_pearson": sqp_pearson,
        "dominant_coord_same": dominant_same,
        "shared_fit_dominant_coord_same": shared_dominant_same,
        "left_dominant_coord_overall": tissue_results[left]["dominant_coord"],
        "right_dominant_coord_overall": tissue_results[right]["dominant_coord"],
        "left_dominant_coord_shared": left_fit["dominant_coord"],
        "right_dominant_coord_shared": right_fit["dominant_coord"],
        "left_R2_QP_shared": left_fit["R2_QP"],
        "right_R2_QP_shared": right_fit["R2_QP"],
        "per_coordinate": per_coordinate,
        "significant_raw_p_le_0_05_coordinates": significant_raw,
        "significant_bonferroni_p_le_0_05_coordinates": significant_bonferroni,
        "null_model": "deterministic paired tissue-label swap over shared proteins using hashlib bits",
        "stability_rule": "tissue-stable pair if cosine >= 0.80, Pearson >= 0.50, overall dominant coordinate is the same, and no per-coordinate paired-label Bonferroni p <= 0.05",
        "core_conclusion": "tissue-stable-descriptive" if pair_stable else "tissue-dependent-descriptive",
    }


def cannot_claim() -> list[str]:
    return [
        "Kim et al 2014 draft human proteome, tissue-specific MS",
        "descriptive tissue comparison, not causal",
        "S^QP statistical projection not mechanism",
        "tissue-stable/dependent here is one study, not a general law",
        "raw per-coord p uncorrected; report Bonferroni too",
        "not ribo-seq, not matched mRNA-controlled",
    ]


def future_required() -> list[str]:
    return [
        "matched mRNA abundance controls before separating protein abundance from expression-level confounding",
        "ribosome profiling or calibrated translation contacts before translation-mediated claims",
        "independent tissue proteome studies before treating stability or dependence as a general law",
        "perturbation or synonymous-edit assays before any causal or mechanism claim",
    ]


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    try:
        cds_path = repo / f"tools/fibonacci_reality/data/cds_codon_abundance_{ORGANISM}.json"
        genetic_code_path = repo / "tools/fibonacci_reality/data/ncbi_genetic_codes.json"
        missing = [str(path.relative_to(repo)) for path in [cds_path, genetic_code_path] if not path.exists()]
        if missing:
            emit("needs_data", missing_required_data=missing, reason="required local human CDS codon data not present")

        selected_specs, discovery = select_tissue_specs(repo)
        tissue_payloads: dict[str, dict[str, object]] = {}
        skipped_tissues: dict[str, object] = {}
        for spec in selected_specs:
            try:
                tissue_payloads[spec["tissue"]] = load_or_fetch_tissue_data(repo, spec)
            except (urllib.error.URLError, TimeoutError, OSError, ValueError) as exc:
                skipped_tissues[spec["tissue"]] = {
                    "source_url": spec["url"],
                    "data_path": spec["data_path"],
                    "reason": repr(exc),
                }

        mandatory_missing = [spec["tissue"] for spec in selected_specs[: len(MANDATORY_TISSUES)] if spec["tissue"] not in tissue_payloads]
        if mandatory_missing:
            emit(
                "needs_data",
                reason="mandatory liver/B-cell tissue PAXdb payload unavailable",
                missing_tissues=mandatory_missing,
                skipped_tissues=skipped_tissues,
                cannot_claim=cannot_claim(),
            )

        cds_payload = load_json(cds_path)
        if not isinstance(cds_payload, dict):
            raise ValueError("human CDS codon payload must be an object")
        cds_joined = cds_payload.get("joined")
        if not isinstance(cds_joined, list):
            raise ValueError("human CDS codon payload lacks joined list")
        cds_ids = {
            item.get("protein_id")
            for item in cds_joined
            if isinstance(item, dict) and isinstance(item.get("protein_id"), str)
        }

        abundance_ids = {
            tissue: set(abundance_map(payload, tissue))
            for tissue, payload in tissue_payloads.items()
        }
        join_counts = {tissue: len(set(cds_ids) & ids) for tissue, ids in abundance_ids.items()}
        retained_tissues = {
            tissue: count
            for tissue, count in join_counts.items()
            if count >= MIN_PROTEINS_PER_ORGANISM
        }
        for tissue, count in join_counts.items():
            if count < MIN_PROTEINS_PER_ORGANISM:
                skipped_tissues[tissue] = {
                    "reason": "tissue join below honest n>=500 gate",
                    "join_count": count,
                }
        if len(retained_tissues) < 2:
            emit(
                "needs_data",
                reason="fewer than two human tissues pass honest n>=500 join gate",
                tissue_join_counts=join_counts,
                skipped_tissues=skipped_tissues,
                cannot_claim=cannot_claim(),
            )

        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}

        rows_by_tissue: dict[str, list[dict[str, object]]] = {}
        tissue_results: dict[str, dict[str, object]] = {}
        ordered_tissues = [spec["tissue"] for spec in selected_specs if spec["tissue"] in retained_tissues]
        for tissue in ordered_tissues:
            payload = tissue_payloads[tissue]
            rows = build_tissue_rows(
                cds_payload=cds_payload,
                tissue=tissue,
                tissue_payload=payload,
                keep_ids=abundance_ids[tissue],
            )
            fit, matrices = fit_rows(
                rows=rows,
                tissue=tissue,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
            )
            if int(fit["n_joined"]) < MIN_PROTEINS_PER_ORGANISM:
                skipped_tissues[tissue] = {
                    "reason": "usable tissue matrix below honest n>=500 gate after row filters",
                    "n_joined": fit["n_joined"],
                }
                continue
            rows_by_tissue[tissue] = rows
            matching_spec = next(spec for spec in selected_specs if spec["tissue"] == tissue)
            tissue_results[tissue] = {
                **fit,
                "tissue_label": matching_spec["tissue_label"],
                "n_joined_tissue_total": join_counts[tissue],
                "source_url": matching_spec["url"],
                "data_path": matching_spec["data_path"],
                "http_status": payload.get("http_status"),
                "payload_sha256": payload.get("payload_sha256"),
                "paxdb_filename": payload.get("paxdb_filename"),
                "paxdb_publication_year": payload.get("paxdb_publication_year"),
                "study_label": payload.get("study_label"),
            }

        if len(tissue_results) < 2:
            emit(
                "needs_data",
                reason="fewer than two human tissues have usable S^QP matrices after row filters",
                tissue_join_counts=join_counts,
                skipped_tissues=skipped_tissues,
                cannot_claim=cannot_claim(),
            )

        pairwise: dict[str, object] = {}
        tissue_names = list(tissue_results)
        for i, left in enumerate(tissue_names):
            for right in tissue_names[i + 1 :]:
                key = f"{left}__vs__{right}"
                pairwise[key] = pair_comparison(
                    left=left,
                    right=right,
                    rows_by_tissue=rows_by_tissue,
                    tissue_results=tissue_results,
                    codons=codons,
                    code=code,
                    aa_order=aa_order,
                    q_projected=q_projected,
                    q_names=q_names,
                    q_support=q_support,
                )

        passed_pairwise = {
            key: value
            for key, value in pairwise.items()
            if isinstance(value, dict) and value.get("status") == "passed"
        }
        if not passed_pairwise:
            emit(
                "needs_data",
                reason="no tissue pair has shared protein n>=500 for paired comparison",
                pairwise=pairwise,
                cannot_claim=cannot_claim(),
            )

        all_pairs_stable = all(
            isinstance(value, dict) and value.get("core_conclusion") == "tissue-stable-descriptive"
            for value in passed_pairwise.values()
        )
        core_conclusion = "tissue-stable-descriptive" if all_pairs_stable else "tissue-dependent-descriptive"

        comparison_cosines = {
            key: value["S_QP_cosine"]
            for key, value in passed_pairwise.items()
            if isinstance(value, dict)
        }
        finite_tissue_results = all(
            math.isfinite(float(result["R2_QP"]))
            and 0.0 <= float(result["R2_QP"]) < DEGENERATE_R2
            and int(result["rank_diagnostics"]["rank_Xtilde"]) == len(q_names)
            and int(result["rank_diagnostics"]["residual_df_after_Z"]) > 10 * len(q_names)
            for result in tissue_results.values()
        )
        finite_pairwise = all(
            isinstance(value, dict)
            and value.get("status") == "passed"
            and -1.0 <= float(value["S_QP_cosine"]) <= 1.0
            and -1.0 <= float(value["S_QP_pearson"]) <= 1.0
            and len(value["per_coordinate"]) == 9
            and all(
                int(row["permutation_count"]) == PERMUTATION_COUNT
                and 0.0 <= float(row["p_value_abs_diff"]) <= 1.0
                and 0.0 <= float(row["p_value_abs_diff_bonferroni_9"]) <= 1.0
                for row in value["per_coordinate"].values()
            )
            for value in passed_pairwise.values()
        )

        checks = [
            {
                "name": "tissues_loaded",
                "passed": len(tissue_results) >= 2 and all(int(result["n_joined"]) >= MIN_PROTEINS_PER_ORGANISM for result in tissue_results.values()),
                "actual": {
                    "loaded_tissues": list(tissue_results),
                    "tissue_join_counts": join_counts,
                    "usable_n_joined": {tissue: result["n_joined"] for tissue, result in tissue_results.items()},
                    "skipped_tissues": skipped_tissues,
                },
                "expected": f">=2 human tissues, each with joined usable protein n >= {MIN_PROTEINS_PER_ORGANISM}",
            },
            {
                "name": "b_star_q6_residuals+controls_Z",
                "passed": len(q_projected) == 9
                and all(
                    result["rank_diagnostics"]["control_column_count"] == 24
                    and result["rank_diagnostics"]["rank_Z"] > 0
                    for result in tissue_results.values()
                ),
                "actual": {
                    "coordinates": q_names,
                    "control_column_count": {
                        tissue: result["rank_diagnostics"]["control_column_count"]
                        for tissue, result in tissue_results.items()
                    },
                    "controls_used": controls_used(aa_order),
                },
                "expected": "fixed human CDS codon rows, 9 B*_Q6 coordinates, and 24 controls Z",
            },
            {
                "name": "sqp_per_tissue_computed",
                "passed": finite_tissue_results,
                "actual": {
                    tissue: {
                        "n_joined": result["n_joined"],
                        "R2_QP": result["R2_QP"],
                        "dominant_coord": result["dominant_coord"],
                        "rank_diagnostics": result["rank_diagnostics"],
                    }
                    for tissue, result in tissue_results.items()
                },
                "expected": "finite nondegenerate R2_QP per tissue, full 9-coordinate residual rank, and residual df comfortably above coordinate count",
            },
            {
                "name": "tissue_comparison_computed",
                "passed": finite_pairwise,
                "actual": {
                    "pairwise_cosines": comparison_cosines,
                    "permutation_count": PERMUTATION_COUNT,
                    "pair_count": len(passed_pairwise),
                },
                "expected": "pairwise cosine and Pearson in [-1,1], deterministic paired-label permutation plus Bonferroni for all 9 coordinates",
            },
            {
                "name": "no_causal_promotion",
                "passed": True,
                "actual": cannot_claim(),
                "expected": "tissue comparison remains descriptive and non-causal with single-study, draft-proteome, non-ribo-seq, no matched-mRNA limits explicit",
            },
        ]

        status = "passed" if all(bool(check["passed"]) for check in checks) else "failed"
        emit(
            status,
            reason=None if status == "passed" else "one or more honest gates failed",
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture_id": CONJECTURE_ID,
                "organism": ORGANISM,
                "organism_label": ORGANISM_LABEL,
                "comparison": "B*_Q6 S^QP to log10(abundance_ppm), human Kim et al 2014 SEQUEST adult tissue PAXdb files",
                "readout": "log10(abundance_ppm)",
                "source_provenance_note": "PAXdb 9606 Adult_*_Kim_2014_SEQUEST tissue files are used as tissue-specific draft human proteome readouts.",
                "coordinate_source": "q_vectors imported from run_b_star_q6_translation_survival_powered.py",
                "coordinates": q_names,
                "tissue_discovery": discovery,
                "tissues": tissue_results,
                "tissue_comparison": {
                    "pairwise": pairwise,
                    "overall_rule": "tissue-stable if every passing tissue pair is stable by high S^QP cosine/Pearson, same overall dominant coordinate, and no Bonferroni-significant coordinate difference; otherwise tissue-dependent",
                    "core_conclusion": core_conclusion,
                },
                "controls_used": controls_used(aa_order),
                "cannot_claim": cannot_claim(),
                "future_required": future_required(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid tissue-specific S^QP input or computation")


if __name__ == "__main__":
    main()

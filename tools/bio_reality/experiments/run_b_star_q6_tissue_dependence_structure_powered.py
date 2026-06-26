#!/usr/bin/env python3
"""Functional-class structure test for human tissue-specific B*_Q6 S^QP."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import re
import sys
import urllib.error
from typing import Any

from run_b_star_q6_condition_specific_sqp_powered import (
    DEGENERATE_R2,
    MIN_PROTEINS_PER_ORGANISM,
    PERMUTATION_COUNT,
    build_condition_rows,
    condition_fit,
    controls_used,
    cosine,
    fetch_bytes,
    load_json,
    now_utc,
    parse_paxdb_payload,
    protein_rows,
    public_fit,
    raw_text_slice,
    write_json_if_changed,
)
from run_b_star_q6_protein_omics_survival_powered import (
    numeric,
    standard_amino_acids,
)
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_tissue_dependence_structure_powered"
CLAIM_ID = "h3.cross_layer_relation.tissue_dependence_structure.b_star_q6_functional_class_powered"
CONJECTURE_ID = "q6.tissue-dependence-structure.functional-class.cross-layer"

ORGANISM = "homo_sapiens"
ORGANISM_LABEL = "Homo sapiens"
NCBI_TAXID = "9606"
PAXDB_DATASET_URL = "https://pax-db.org/downloads/latest/datasets/9606/"
MIN_TISSUES_FOR_STRUCTURE = 8

TISSUES = [
    {"tissue": "Adult_Bcells", "short_name": "Bcells", "tissue_label": "adult B cells", "functional_class": "immune"},
    {"tissue": "Adult_CD4Tcells", "short_name": "CD4Tcells", "tissue_label": "adult CD4 T cells", "functional_class": "immune"},
    {"tissue": "Adult_CD8Tcells", "short_name": "CD8Tcells", "tissue_label": "adult CD8 T cells", "functional_class": "immune"},
    {"tissue": "Adult_NKcells", "short_name": "NKcells", "tissue_label": "adult NK cells", "functional_class": "immune"},
    {"tissue": "Adult_Monocytes", "short_name": "Monocytes", "tissue_label": "adult monocytes", "functional_class": "immune"},
    {"tissue": "Adult_Liver", "short_name": "Liver", "tissue_label": "adult liver", "functional_class": "metabolic"},
    {"tissue": "Adult_Kidney", "short_name": "Kidney", "tissue_label": "adult kidney", "functional_class": "metabolic"},
    {"tissue": "Adult_Pancreas", "short_name": "Pancreas", "tissue_label": "adult pancreas", "functional_class": "metabolic"},
    {"tissue": "Adult_Frontalcortex", "short_name": "Frontalcortex", "tissue_label": "adult frontal cortex", "functional_class": "neural"},
    {"tissue": "Adult_Retina", "short_name": "Retina", "tissue_label": "adult retina", "functional_class": "neural"},
    {"tissue": "Adult_Colon", "short_name": "Colon", "tissue_label": "adult colon", "functional_class": "epithelial_or_other"},
    {"tissue": "Adult_Lung", "short_name": "Lung", "tissue_label": "adult lung", "functional_class": "epithelial_or_other"},
    {"tissue": "Adult_Heart", "short_name": "Heart", "tissue_label": "adult heart", "functional_class": "epithelial_or_other"},
]


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def tissue_slug(tissue: str) -> str:
    return re.sub(r"[^a-z0-9]+", "_", tissue.lower()).strip("_")


def tissue_spec(raw: dict[str, str]) -> dict[str, str]:
    spec = dict(raw)
    filename = f"9606-{spec['tissue']}_Kim_2014_SEQUEST.txt"
    slug = tissue_slug(spec["tissue"])
    spec["filename"] = filename
    spec["url"] = PAXDB_DATASET_URL + filename
    spec["slug"] = slug
    spec["data_path"] = f"tools/bio_reality/data/proteomics_abundance_homo_sapiens_{slug}.json"
    return spec


def cannot_claim() -> list[str]:
    return [
        "Kim 2014 draft proteome 单研究",
        "功能分类(免疫/代谢/神经/上皮)是人为先验标签,非数据驱动",
        "descriptive clustering, not causal",
        "S^QP statistical projection not mechanism",
        "tissue-structure here one study not general law",
        "not ribo-seq/not mRNA-controlled",
    ]


def future_required() -> list[str]:
    return [
        "independent tissue proteome studies before treating functional-class structure as general",
        "matched mRNA abundance controls before separating abundance from expression-level confounding",
        "ribo-seq or direct translation measurements before translation-mechanism claims",
        "data-driven tissue-class discovery before replacing the hand-coded functional prior",
    ]


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
        "functional_class_prior": spec["functional_class"],
        "study_label": "Kim et al 2014 draft human proteome SEQUEST",
        "fetched_at": now_utc(),
        "fetched_by": "run_b_star_q6_tissue_dependence_structure_powered.py",
        "http_status": contact["http_status"],
        "content_type": contact["content_type"],
        "payload_byte_size": contact["payload_byte_size"],
        "payload_sha256": contact["payload_sha256"],
        "raw_payload_text": raw_text,
        "raw_payload_note": raw_note,
        "n_proteins": len(abundance),
        "protein_abundance": abundance,
        "protein_gene_name": gene_names,
        "cannot_claim": cannot_claim(),
        "derivation_boundary": "not_bedc_kernel_content",
    }
    payload.update(metadata)
    write_json_if_changed(path, payload)
    return payload


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
) -> dict[str, object]:
    x_rows, y_rows, z_rows, _protein_ids, summary = protein_rows(
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
    return {**summary, **public_fit(fit)}


def sqp_vector(result: dict[str, object], q_names: list[str]) -> list[float]:
    raw = result.get("S_QP")
    if not isinstance(raw, dict):
        raise ValueError("tissue result lacks S_QP object")
    return [float(raw[name]) for name in q_names]


def cosine_matrix(tissue_names: list[str], tissue_results: dict[str, dict[str, object]], q_names: list[str]) -> dict[str, dict[str, float]]:
    vectors = {tissue: sqp_vector(tissue_results[tissue], q_names) for tissue in tissue_names}
    return {
        left: {
            right: 1.0 if left == right else cosine(vectors[left], vectors[right])
            for right in tissue_names
        }
        for left in tissue_names
    }


def pair_values(
    tissue_names: list[str],
    classes_by_tissue: dict[str, str],
    matrix: dict[str, dict[str, float]],
) -> tuple[list[float], list[float]]:
    within: list[float] = []
    between: list[float] = []
    for i, left in enumerate(tissue_names):
        for right in tissue_names[i + 1 :]:
            value = matrix[left][right]
            if classes_by_tissue[left] == classes_by_tissue[right]:
                within.append(value)
            else:
                between.append(value)
    return within, between


def mean(values: list[float]) -> float:
    if not values:
        return 0.0
    return sum(values) / len(values)


def deterministic_permuted_labels(labels: list[str], perm_index: int) -> list[str]:
    out = list(labels)
    for index in range(len(out) - 1, 0, -1):
        digest = hashlib.sha256(f"{EXPERIMENT_ID}|functional_class_label_null|{perm_index}|{index}".encode("utf-8")).digest()
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        out[index], out[swap_index] = out[swap_index], out[index]
    return out


def class_structure_test(
    *,
    tissue_names: list[str],
    classes_by_tissue: dict[str, str],
    matrix: dict[str, dict[str, float]],
    permutation_count: int,
) -> dict[str, object]:
    observed_within, observed_between = pair_values(tissue_names, classes_by_tissue, matrix)
    observed_within_mean = mean(observed_within)
    observed_between_mean = mean(observed_between)
    observed_delta = observed_within_mean - observed_between_mean

    labels = [classes_by_tissue[tissue] for tissue in tissue_names]
    exceed = 0
    max_delta = -math.inf
    min_delta = math.inf
    null_sum = 0.0
    for perm_index in range(permutation_count):
        permuted = deterministic_permuted_labels(labels, perm_index)
        permuted_classes = dict(zip(tissue_names, permuted))
        null_within, null_between = pair_values(tissue_names, permuted_classes, matrix)
        null_delta = mean(null_within) - mean(null_between)
        null_sum += null_delta
        max_delta = max(max_delta, null_delta)
        min_delta = min(min_delta, null_delta)
        if null_delta >= observed_delta:
            exceed += 1

    p_value = (exceed + 1) / (permutation_count + 1)
    return {
        "observed_within_class_mean_cosine": observed_within_mean,
        "observed_between_class_mean_cosine": observed_between_mean,
        "observed_within_minus_between": observed_delta,
        "within_pair_count": len(observed_within),
        "between_pair_count": len(observed_between),
        "permutation_count": permutation_count,
        "p_value_one_sided_within_greater": p_value,
        "null_mean_delta": null_sum / permutation_count if permutation_count else 0.0,
        "null_min_delta_seen": min_delta,
        "null_max_delta_seen": max_delta,
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|functional_class_label_null|perm_index|index",
        "class_size_preserving": True,
        "test_interpretation": "descriptive functional-class prior test; small p supports within-class S^QP similarity above label-shuffle null",
    }


def dominant_coord_contingency(
    tissue_names: list[str],
    classes_by_tissue: dict[str, str],
    tissue_results: dict[str, dict[str, object]],
) -> dict[str, object]:
    classes = sorted(set(classes_by_tissue.values()))
    coords = sorted({str(tissue_results[tissue]["dominant_coord"]) for tissue in tissue_names})
    by_coord = {coord: {klass: 0 for klass in classes} for coord in coords}
    by_class = {klass: {coord: 0 for coord in coords} for klass in classes}
    tissue_dominants: dict[str, str] = {}
    for tissue in tissue_names:
        klass = classes_by_tissue[tissue]
        coord = str(tissue_results[tissue]["dominant_coord"])
        by_coord[coord][klass] += 1
        by_class[klass][coord] += 1
        tissue_dominants[tissue] = coord
    return {
        "dominant_coord_by_tissue": tissue_dominants,
        "dominant_coord_x_class": by_coord,
        "class_x_dominant_coord": by_class,
        "note": "counts only; no causal or mechanistic inference from dominant-coordinate concentration",
    }


def conclusion_from_test(test: dict[str, object]) -> str:
    delta = float(test["observed_within_minus_between"])
    p_value = float(test["p_value_one_sided_within_greater"])
    if delta > 0.0 and p_value <= 0.05:
        return "functional-class-structured-descriptive"
    return "idiosyncratic-or-not-functional-class-structured-descriptive"


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    try:
        cds_path = repo / f"tools/bio_reality/data/cds_codon_abundance_{ORGANISM}.json"
        genetic_code_path = repo / "tools/bio_reality/data/ncbi_genetic_codes.json"
        missing = [str(path.relative_to(repo)) for path in [cds_path, genetic_code_path] if not path.exists()]
        if missing:
            emit("needs_data", missing_required_data=missing, reason="required local human CDS codon data not present")

        specs = [tissue_spec(raw) for raw in TISSUES]
        tissue_payloads: dict[str, dict[str, object]] = {}
        skipped_tissues: dict[str, object] = {}
        for spec in specs:
            try:
                tissue_payloads[spec["tissue"]] = load_or_fetch_tissue_data(repo, spec)
            except (urllib.error.URLError, TimeoutError, OSError, ValueError) as exc:
                skipped_tissues[spec["tissue"]] = {
                    "source_url": spec["url"],
                    "data_path": spec["data_path"],
                    "functional_class": spec["functional_class"],
                    "reason": repr(exc),
                }

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

        abundance_ids = {tissue: set(abundance_map(payload, tissue)) for tissue, payload in tissue_payloads.items()}
        join_counts = {tissue: len(set(cds_ids) & ids) for tissue, ids in abundance_ids.items()}
        retained_tissues = {tissue: count for tissue, count in join_counts.items() if count >= MIN_PROTEINS_PER_ORGANISM}
        for tissue, count in join_counts.items():
            if count < MIN_PROTEINS_PER_ORGANISM:
                skipped_tissues[tissue] = {
                    "reason": "tissue join below honest n>=500 gate",
                    "join_count": count,
                }

        if len(retained_tissues) < MIN_TISSUES_FOR_STRUCTURE:
            emit(
                "needs_data",
                reason="fewer than eight human tissues pass honest n>=500 join gate",
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

        tissue_results: dict[str, dict[str, object]] = {}
        ordered_tissues = [spec["tissue"] for spec in specs if spec["tissue"] in retained_tissues]
        classes_by_tissue = {spec["tissue"]: spec["functional_class"] for spec in specs if spec["tissue"] in retained_tissues}
        specs_by_tissue = {spec["tissue"]: spec for spec in specs}

        for tissue in ordered_tissues:
            payload = tissue_payloads[tissue]
            rows = build_tissue_rows(
                cds_payload=cds_payload,
                tissue=tissue,
                tissue_payload=payload,
                keep_ids=abundance_ids[tissue],
            )
            fit = fit_rows(
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
            spec = specs_by_tissue[tissue]
            tissue_results[tissue] = {
                **fit,
                "short_name": spec["short_name"],
                "tissue_label": spec["tissue_label"],
                "functional_class_prior": spec["functional_class"],
                "n_joined_tissue_total": join_counts[tissue],
                "source_url": spec["url"],
                "data_path": spec["data_path"],
                "http_status": payload.get("http_status"),
                "payload_sha256": payload.get("payload_sha256"),
                "paxdb_filename": payload.get("paxdb_filename"),
                "paxdb_publication_year": payload.get("paxdb_publication_year"),
                "study_label": payload.get("study_label"),
            }

        if len(tissue_results) < MIN_TISSUES_FOR_STRUCTURE:
            emit(
                "needs_data",
                reason="fewer than eight human tissues have usable S^QP matrices after row filters",
                tissue_join_counts=join_counts,
                skipped_tissues=skipped_tissues,
                cannot_claim=cannot_claim(),
            )

        tissue_names = list(tissue_results)
        matrix = cosine_matrix(tissue_names, tissue_results, q_names)
        class_test = class_structure_test(
            tissue_names=tissue_names,
            classes_by_tissue=classes_by_tissue,
            matrix=matrix,
            permutation_count=PERMUTATION_COUNT,
        )
        contingency = dominant_coord_contingency(tissue_names, classes_by_tissue, tissue_results)
        core_conclusion = conclusion_from_test(class_test)

        finite_tissue_results = all(
            math.isfinite(float(result["R2_QP"]))
            and 0.0 <= float(result["R2_QP"]) < DEGENERATE_R2
            and int(result["rank_diagnostics"]["rank_Xtilde"]) == len(q_names)
            and int(result["rank_diagnostics"]["residual_df_after_Z"]) > 10 * len(q_names)
            for result in tissue_results.values()
        )
        finite_matrix = (
            set(matrix) == set(tissue_names)
            and all(set(row) == set(tissue_names) for row in matrix.values())
            and all(-1.0 <= float(matrix[left][right]) <= 1.0 for left in tissue_names for right in tissue_names)
            and all(abs(float(matrix[left][right]) - float(matrix[right][left])) <= 1e-12 for left in tissue_names for right in tissue_names)
            and all(abs(float(matrix[tissue][tissue]) - 1.0) <= 1e-12 for tissue in tissue_names)
        )
        class_test_ok = (
            int(class_test["permutation_count"]) == PERMUTATION_COUNT
            and int(class_test["within_pair_count"]) > 0
            and int(class_test["between_pair_count"]) > 0
            and 0.0 <= float(class_test["p_value_one_sided_within_greater"]) <= 1.0
        )

        checks = [
            {
                "name": "tissues_loaded",
                "passed": len(tissue_results) >= MIN_TISSUES_FOR_STRUCTURE
                and all(int(result["n_joined"]) >= MIN_PROTEINS_PER_ORGANISM for result in tissue_results.values()),
                "actual": {
                    "loaded_tissue_count": len(tissue_results),
                    "loaded_tissues": tissue_names,
                    "tissue_join_counts": join_counts,
                    "usable_n_joined": {tissue: result["n_joined"] for tissue, result in tissue_results.items()},
                    "skipped_tissues": skipped_tissues,
                },
                "expected": f">={MIN_TISSUES_FOR_STRUCTURE} human tissues, each with joined usable protein n >= {MIN_PROTEINS_PER_ORGANISM}",
            },
            {
                "name": "b_star_q6_residuals+Z",
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
                "name": "per_tissue_sqp_computed",
                "passed": finite_tissue_results,
                "actual": {
                    tissue: {
                        "n_joined": result["n_joined"],
                        "R2_QP": result["R2_QP"],
                        "dominant_coord": result["dominant_coord"],
                        "functional_class_prior": result["functional_class_prior"],
                        "rank_diagnostics": result["rank_diagnostics"],
                    }
                    for tissue, result in tissue_results.items()
                },
                "expected": "finite nondegenerate S^QP per tissue, full 9-coordinate residual rank, and residual df comfortably above coordinate count",
            },
            {
                "name": "cosine_matrix_computed",
                "passed": finite_matrix,
                "actual": {
                    "tissue_count": len(tissue_names),
                    "pair_count": len(tissue_names) * (len(tissue_names) - 1) // 2,
                },
                "expected": "symmetric tissue x tissue S^QP cosine matrix with unit diagonal and finite entries in [-1,1]",
            },
            {
                "name": "within_vs_between_class_tested",
                "passed": class_test_ok,
                "actual": class_test,
                "expected": "class-size-preserving deterministic permutation of hand-coded functional-class labels",
            },
            {
                "name": "no_causal_promotion",
                "passed": True,
                "actual": cannot_claim(),
                "expected": "single-study, prior-label, descriptive, non-causal, non-ribo-seq, no matched-mRNA limits explicit",
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
                "functional_class_prior": classes_by_tissue,
                "tissues": tissue_results,
                "tissue_x_tissue_S_QP_cosine": matrix,
                "within_vs_between_functional_class": class_test,
                "dominant_coord_contingency": contingency,
                "core_conclusion": core_conclusion,
                "controls_used": controls_used(aa_order),
                "cannot_claim": cannot_claim(),
                "future_required": future_required(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid tissue-dependence structure input or computation")


if __name__ == "__main__":
    main()

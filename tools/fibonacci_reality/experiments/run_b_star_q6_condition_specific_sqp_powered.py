#!/usr/bin/env python3
"""Condition-specific B*_Q6 S^{QP} against yeast protein abundance."""

from __future__ import annotations

import datetime as _dt
import hashlib
import json
import math
import pathlib
import sys
import urllib.error
import urllib.request
from typing import Any

from run_b_star_q6_protein_omics_survival_powered import (
    DEGENERATE_R2,
    MIN_PROTEINS_PER_ORGANISM,
    SURVIVAL_EPS,
    codon_counts_rna,
    controls_used,
    explained_by_design,
    matrix_column,
    normed_coordinate,
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


EXPERIMENT_ID = "b_star_q6_condition_specific_sqp_powered"
CLAIM_ID = "h3.cross_layer_relation.condition_specific_sqp.b_star_q6_growth_condition_powered"
CONJECTURE_ID = "q6.condition-specific-sqp.growth-condition.cross-layer"

ORGANISM = "saccharomyces_cerevisiae"
ORGANISM_LABEL = "Saccharomyces cerevisiae"
NCBI_TAXID = "4932"
PERMUTATION_COUNT = 1000
RAW_TEXT_LIMIT_BYTES = 1024 * 1024
USER_AGENT = "fibonacci-reality-condition-sqp/1.0"
RANK_TOL = 1e-10
RIDGE_EPS = 1e-12

CONDITIONS = {
    "YEPD": {
        "medium_label": "YEPD rich medium",
        "url": "https://pax-db.org/downloads/latest/datasets/4932/4932-Newman_et_al_yeast_data_YEPD.txt",
        "data_path": "tools/fibonacci_reality/data/proteomics_abundance_saccharomyces_cerevisiae_yepd.json",
    },
    "SD": {
        "medium_label": "SD minimal medium",
        "url": "https://pax-db.org/downloads/latest/datasets/4932/4932-Newman_et_al_yeast_data_SD.txt",
        "data_path": "tools/fibonacci_reality/data/proteomics_abundance_saccharomyces_cerevisiae_sd.json",
    },
}


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def now_utc() -> str:
    return _dt.datetime.now(_dt.UTC).replace(microsecond=0).isoformat()


def decode_text(raw: bytes) -> str:
    return raw.decode("utf-8", "replace")


def raw_text_slice(raw: bytes) -> tuple[str, str]:
    if len(raw) <= RAW_TEXT_LIMIT_BYTES:
        return decode_text(raw), "full_raw_payload"
    prefix = raw[:RAW_TEXT_LIMIT_BYTES]
    return decode_text(prefix), f"deterministic_prefix_{RAW_TEXT_LIMIT_BYTES}_bytes"


def fetch_bytes(url: str) -> dict[str, object]:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=60) as response:
        body = response.read()
        return {
            "url": url,
            "http_status": int(response.status),
            "content_type": response.headers.get("content-type"),
            "payload_byte_size": len(body),
            "payload_sha256": hashlib.sha256(body).hexdigest(),
            "raw_bytes": body,
        }


def parse_paxdb_payload(raw: bytes) -> tuple[dict[str, float], dict[str, str], dict[str, object]]:
    text = decode_text(raw)
    abundance: dict[str, float] = {}
    gene_names: dict[str, str] = {}
    metadata: dict[str, object] = {}
    header_seen = False

    for line in text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("#"):
            no_hash = stripped.lstrip("#").strip()
            header_columns = no_hash.split()
            if header_columns[:3] == ["gene_name", "string_external_id", "abundance"]:
                header_seen = True
            if ":" in no_hash:
                key, value = no_hash.split(":", 1)
                key = key.strip()
                value = value.strip()
                if key in {
                    "id",
                    "name",
                    "score",
                    "description",
                    "organ",
                    "integrated",
                    "coverage",
                    "link",
                    "publication_year",
                    "filename",
                }:
                    metadata[f"paxdb_{key}"] = coerce_metadata_value(key, value)
            continue

        parts = stripped.split()
        if len(parts) < 3:
            continue
        gene_name, string_external_id, abundance_text = parts[:3]
        try:
            value = float(abundance_text)
        except ValueError:
            continue
        if value <= 0.0:
            continue
        protein_id = string_external_id or gene_name
        if protein_id:
            abundance[protein_id] = value
            gene_names[protein_id] = gene_name

    if not header_seen:
        raise ValueError("PAXdb abundance header not found")
    if not abundance:
        raise ValueError("no positive PAXdb abundance rows parsed")
    return abundance, gene_names, metadata


def coerce_metadata_value(key: str, value: str) -> object:
    if key == "integrated":
        return value.lower() == "true"
    if key in {"coverage", "publication_year"}:
        try:
            return int(value)
        except ValueError:
            return value
    if key == "score":
        try:
            return float(value)
        except ValueError:
            return value
    return value


def write_json_if_changed(path: pathlib.Path, payload: dict[str, object]) -> None:
    text = json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    if path.exists() and path.read_text(encoding="utf-8") == text:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def load_or_fetch_condition_data(repo: pathlib.Path, condition: str, spec: dict[str, str]) -> dict[str, object]:
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
        "source_kind": "condition_specific_paxdb_abundance_dataset",
        "source_url": spec["url"],
        "organism": ORGANISM,
        "organism_label": ORGANISM_LABEL,
        "ncbi_taxid": NCBI_TAXID,
        "growth_condition": condition,
        "medium_label": spec["medium_label"],
        "fetched_at": now_utc(),
        "fetched_by": "run_b_star_q6_condition_specific_sqp_powered.py",
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
            "condition-specific GFP abundance readout only; not integrated abundance",
            "PAXdb metadata is the source of publication-year and filename provenance",
        ],
        "derivation_boundary": "not_bedc_kernel_content",
    }
    payload.update(metadata)
    write_json_if_changed(path, payload)
    return payload


def abundance_map(payload: dict[str, object], condition: str) -> dict[str, float]:
    raw = payload.get("protein_abundance")
    if not isinstance(raw, dict):
        raise ValueError(f"{condition} payload lacks protein_abundance object")
    out: dict[str, float] = {}
    for protein_id, value in raw.items():
        abundance = numeric(value, f"{condition}.protein_abundance.{protein_id}")
        if abundance > 0.0:
            out[str(protein_id)] = abundance
    return out


def gene_name_map(payload: dict[str, object]) -> dict[str, str]:
    raw = payload.get("protein_gene_name")
    if not isinstance(raw, dict):
        return {}
    return {str(key): str(value) for key, value in raw.items()}


def build_condition_rows(
    *,
    cds_payload: dict[str, object],
    condition: str,
    condition_payload: dict[str, object],
    shared_ids: set[str],
) -> list[dict[str, object]]:
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError("yeast CDS payload must contain joined list")

    abundances = abundance_map(condition_payload, condition)
    gene_names = gene_name_map(condition_payload)
    rows: list[dict[str, object]] = []
    seen: set[str] = set()
    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str):
            raise ValueError(f"CDS joined row {row_index} lacks string protein_id")
        if protein_id not in shared_ids or protein_id in seen:
            continue
        if protein_id not in abundances:
            continue
        copied = dict(item)
        copied["abundance_ppm"] = abundances[protein_id]
        copied["paxdb_gene_name"] = gene_names.get(protein_id, item.get("paxdb_gene_name"))
        copied["growth_condition"] = condition
        rows.append(copied)
        seen.add(protein_id)
    return rows


def protein_rows(
    *,
    rows: list[dict[str, object]],
    condition: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> tuple[list[list[float]], list[list[float]], list[list[float]], list[str], dict[str, object]]:
    x_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    protein_ids: list[str] = []
    skipped = {
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }

    for row_index, item in enumerate(rows):
        abundance = numeric(item.get("abundance_ppm"), f"{condition}.rows[{row_index}].abundance_ppm")
        if abundance <= 0.0:
            skipped["nonpositive_abundance"] += 1
            continue
        cds_len_nt = numeric(item.get("cds_len_nt"), f"{condition}.rows[{row_index}].cds_len_nt")
        if cds_len_nt <= 0.0:
            skipped["invalid_length"] += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str):
            raise ValueError(f"{condition}.rows[{row_index}] lacks protein_id")

        counts = codon_counts_rna(item, codons, condition, row_index)
        total = sum(counts.values())
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue

        frequencies = {codon: counts[codon] / total for codon in codons}
        x_rows.append([normed_coordinate(frequencies, q_projected[name], codons) for name in q_names])
        y_rows.append([math.log10(abundance)])
        protein_ids.append(protein_id)

        aa_counts = {aa: 0 for aa in aa_order}
        for codon in codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        if aa_total <= 0:
            raise ValueError(f"{condition}.rows[{row_index}] has no amino-acid counts")

        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
        m_density = sum(counts[codon] for codon in q_support) / total
        z_rows.append(
            [1.0, math.log(cds_len_nt)]
            + [aa_counts[aa] / aa_total for aa in aa_order]
            + [gc3, m_density]
        )

    summary = {
        "n_joined": len(x_rows),
        "skipped_records": skipped,
    }
    return x_rows, y_rows, z_rows, protein_ids, summary


def project_with_basis(matrix: list[list[float]], basis: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    out = [[0.0 for _ in matrix[0]] for _ in matrix]
    columns = [[row[index] for row in matrix] for index in range(len(matrix[0]))]
    for q in basis:
        for col_index, column in enumerate(columns):
            coeff = vector_dot(column, q)
            for row_index in range(len(matrix)):
                out[row_index][col_index] += coeff * q[row_index]
    return out


def residualize_with_basis(matrix: list[list[float]], basis: list[list[float]]) -> list[list[float]]:
    projected = project_with_basis(matrix, basis)
    return [
        [matrix[row][col] - projected[row][col] for col in range(len(matrix[row]))]
        for row in range(len(matrix))
    ]


def gram_matrix(design: list[list[float]]) -> list[list[float]]:
    if not design:
        return []
    width = len(design[0])
    gram = [[0.0 for _ in range(width)] for _ in range(width)]
    for row in design:
        for i in range(width):
            for j in range(width):
                gram[i][j] += row[i] * row[j]
    return gram


def crossprod_vector(design: list[list[float]], response: list[float]) -> list[float]:
    if not design:
        return []
    width = len(design[0])
    out = [0.0 for _ in range(width)]
    for row, value in zip(design, response):
        for index in range(width):
            out[index] += row[index] * value
    return out


def solve_linear_system(matrix: list[list[float]], rhs: list[float], tol: float = RANK_TOL) -> list[float]:
    n = len(rhs)
    aug = [list(matrix[row]) + [rhs[row]] for row in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= tol:
            raise ValueError("normal-equation solve is rank deficient after ridge")
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        scale = aug[col][col]
        for item in range(col, n + 1):
            aug[col][item] /= scale
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor == 0.0:
                continue
            for item in range(col, n + 1):
                aug[row][item] -= factor * aug[col][item]
    return [aug[row][n] for row in range(n)]


def solve_regularized_normal_equation(
    design: list[list[float]],
    response: list[float],
    ridge: float = RIDGE_EPS,
) -> list[float]:
    gram = gram_matrix(design)
    rhs = crossprod_vector(design, response)
    for index in range(len(gram)):
        gram[index][index] += ridge
    return solve_linear_system(gram, rhs)


def condition_fit(
    *,
    x_rows: list[list[float]],
    y_rows: list[list[float]],
    z_rows: list[list[float]],
    q_names: list[str],
    z_basis: list[list[float]] | None = None,
    x_tilde_cached: list[list[float]] | None = None,
) -> dict[str, object]:
    if z_basis is None:
        z_basis = orthonormal_basis_from_columns(z_rows)
    x_tilde = x_tilde_cached if x_tilde_cached is not None else residualize_with_basis(x_rows, z_basis)
    y_tilde = residualize_with_basis(y_rows, z_basis)
    y_col = matrix_column(y_tilde, 0)
    y_ss = vector_dot(y_col, y_col)
    explained, rank_xtilde = explained_by_design(x_tilde, y_tilde)
    r2_qp = 0.0 if y_ss <= SURVIVAL_EPS else max(0.0, min(1.0, explained / y_ss))
    a_perp = dict(zip(q_names, solve_regularized_normal_equation(x_tilde, y_col)))

    sqp: dict[str, float] = {}
    raw_improvement: dict[str, float] = {}
    for index, q_name in enumerate(q_names):
        x_col = matrix_column(x_tilde, index)
        x_ss = vector_dot(x_col, x_col)
        if x_ss <= SURVIVAL_EPS or y_ss <= SURVIVAL_EPS:
            improvement = 0.0
            partial = 0.0
        else:
            xy = vector_dot(x_col, y_col)
            improvement = (xy * xy) / x_ss
            partial = max(0.0, min(1.0, improvement / y_ss))
        sqp[q_name] = partial
        raw_improvement[q_name] = improvement

    dominant_coord = max(q_names, key=lambda name: abs(a_perp[name]))
    return {
        "R2_QP": r2_qp,
        "S_QP": sqp,
        "a_perp": a_perp,
        "dominant_coord": dominant_coord,
        "raw_sse_improvement": raw_improvement,
        "rank_diagnostics": {
            "rank_Z": len(z_basis),
            "rank_Xtilde": rank_xtilde,
            "residual_df_after_Z": len(x_rows) - len(z_basis),
            "control_column_count": len(z_rows[0]) if z_rows else 0,
            "q_coordinate_count": len(q_names),
            "y_residual_energy": y_ss,
            "explained_energy": explained,
            "degenerate_R2_threshold": DEGENERATE_R2,
        },
        "_x_tilde": x_tilde,
        "_z_basis": z_basis,
    }


def public_fit(fit: dict[str, object]) -> dict[str, object]:
    return {key: value for key, value in fit.items() if not key.startswith("_")}


def cosine(left: list[float], right: list[float]) -> float:
    left_norm = math.sqrt(sum(value * value for value in left))
    right_norm = math.sqrt(sum(value * value for value in right))
    if left_norm <= SURVIVAL_EPS or right_norm <= SURVIVAL_EPS:
        return 0.0
    return max(-1.0, min(1.0, sum(left[i] * right[i] for i in range(len(left))) / (left_norm * right_norm)))


def pearson(left: list[float], right: list[float]) -> float:
    if len(left) != len(right) or len(left) < 2:
        return 0.0
    left_mean = sum(left) / len(left)
    right_mean = sum(right) / len(right)
    left_centered = [value - left_mean for value in left]
    right_centered = [value - right_mean for value in right]
    return cosine(left_centered, right_centered)


def permutation_swap(protein_id: str, perm_index: int) -> bool:
    digest = hashlib.sha256(f"{EXPERIMENT_ID}|paired_label_null|{perm_index}|{protein_id}".encode("utf-8")).digest()
    return bool(digest[0] & 1)


def paired_permutation_null(
    *,
    y_yepd: list[list[float]],
    y_sd: list[list[float]],
    protein_ids: list[str],
    x_rows: list[list[float]],
    z_rows: list[list[float]],
    q_names: list[str],
    observed_abs_diff: dict[str, float],
    count: int,
) -> dict[str, object]:
    z_basis = orthonormal_basis_from_columns(z_rows)
    x_tilde = residualize_with_basis(x_rows, z_basis)
    exceed = {name: 0 for name in q_names}
    maxima = {name: 0.0 for name in q_names}

    for perm_index in range(count):
        perm_yepd: list[list[float]] = []
        perm_sd: list[list[float]] = []
        for row_index, protein_id in enumerate(protein_ids):
            if permutation_swap(protein_id, perm_index):
                perm_yepd.append(y_sd[row_index])
                perm_sd.append(y_yepd[row_index])
            else:
                perm_yepd.append(y_yepd[row_index])
                perm_sd.append(y_sd[row_index])
        fit_y = condition_fit(
            x_rows=x_rows,
            y_rows=perm_yepd,
            z_rows=z_rows,
            q_names=q_names,
            z_basis=z_basis,
            x_tilde_cached=x_tilde,
        )
        fit_s = condition_fit(
            x_rows=x_rows,
            y_rows=perm_sd,
            z_rows=z_rows,
            q_names=q_names,
            z_basis=z_basis,
            x_tilde_cached=x_tilde,
        )
        sqp_y = fit_y["S_QP"]
        sqp_s = fit_s["S_QP"]
        if not isinstance(sqp_y, dict) or not isinstance(sqp_s, dict):
            raise ValueError("internal permutation fit lacks S_QP")
        for name in q_names:
            diff = abs(float(sqp_y[name]) - float(sqp_s[name]))
            maxima[name] = max(maxima[name], diff)
            if diff >= observed_abs_diff[name]:
                exceed[name] += 1

    return {
        name: {
            "permutation_count": count,
            "p_value_abs_diff": (exceed[name] + 1) / (count + 1),
            "null_max_abs_diff_seen": maxima[name],
            "deterministic_seed": f"sha256:{EXPERIMENT_ID}|paired_label_null|perm_index|protein_id",
        }
        for name in q_names
    }


def cannot_claim() -> list[str]:
    return [
        "single study (Newman et al 2009) GFP-based yeast abundance, two growth conditions",
        "descriptive condition comparison, not causal",
        "S^QP is statistical projection not mechanism",
        "condition-stable/dependent here is one organism one study, not a general law",
        "not ribo-seq, not matched mRNA-controlled",
    ]


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    try:
        cds_path = repo / f"tools/fibonacci_reality/data/cds_codon_abundance_{ORGANISM}.json"
        genetic_code_path = repo / "tools/fibonacci_reality/data/ncbi_genetic_codes.json"
        missing = [str(path.relative_to(repo)) for path in [cds_path, genetic_code_path] if not path.exists()]
        if missing:
            emit("needs_data", missing_required_data=missing, reason="required local yeast CDS codon data not present")

        condition_payloads: dict[str, dict[str, object]] = {}
        try:
            for condition, spec in CONDITIONS.items():
                condition_payloads[condition] = load_or_fetch_condition_data(repo, condition, spec)
        except (urllib.error.URLError, TimeoutError, OSError) as exc:
            emit("needs_data", missing_required_data=[spec["data_path"] for spec in CONDITIONS.values()], reason=repr(exc))

        cds_payload = load_json(cds_path)
        if not isinstance(cds_payload, dict):
            raise ValueError("yeast CDS codon payload must be an object")

        abundance_ids = {
            condition: set(abundance_map(payload, condition))
            for condition, payload in condition_payloads.items()
        }
        cds_joined = cds_payload.get("joined")
        if not isinstance(cds_joined, list):
            raise ValueError("yeast CDS codon payload lacks joined list")
        cds_ids = {
            item.get("protein_id")
            for item in cds_joined
            if isinstance(item, dict) and isinstance(item.get("protein_id"), str)
        }
        shared_ids = set(cds_ids) & abundance_ids["YEPD"] & abundance_ids["SD"]
        total_join = {
            condition: len(set(cds_ids) & ids)
            for condition, ids in abundance_ids.items()
        }
        if any(n < MIN_PROTEINS_PER_ORGANISM for n in total_join.values()) or len(shared_ids) < MIN_PROTEINS_PER_ORGANISM:
            emit(
                "needs_data",
                reason="condition-specific yeast join below honest n>=500 gate",
                condition_join_counts=total_join,
                shared_join_count=len(shared_ids),
                cannot_claim=cannot_claim(),
            )

        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}

        condition_rows = {
            condition: build_condition_rows(
                cds_payload=cds_payload,
                condition=condition,
                condition_payload=payload,
                shared_ids=shared_ids,
            )
            for condition, payload in condition_payloads.items()
        }
        condition_matrices: dict[str, dict[str, object]] = {}
        condition_results: dict[str, dict[str, object]] = {}
        ordered_protein_ids: list[str] | None = None

        for condition in ["YEPD", "SD"]:
            x_rows, y_rows, z_rows, protein_ids, summary = protein_rows(
                rows=condition_rows[condition],
                condition=condition,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
            )
            if ordered_protein_ids is None:
                ordered_protein_ids = protein_ids
            elif ordered_protein_ids != protein_ids:
                raise ValueError("condition shared-protein ordering mismatch")
            fit = condition_fit(x_rows=x_rows, y_rows=y_rows, z_rows=z_rows, q_names=q_names)
            condition_matrices[condition] = {
                "x_rows": x_rows,
                "y_rows": y_rows,
                "z_rows": z_rows,
                "protein_ids": protein_ids,
            }
            condition_results[condition] = {
                **summary,
                "n_joined_condition_total": total_join[condition],
                "n_shared_used": len(protein_ids),
                "medium_label": CONDITIONS[condition]["medium_label"],
                "source_url": CONDITIONS[condition]["url"],
                "payload_sha256": condition_payloads[condition].get("payload_sha256"),
                "paxdb_filename": condition_payloads[condition].get("paxdb_filename"),
                "paxdb_publication_year": condition_payloads[condition].get("paxdb_publication_year"),
                **public_fit(fit),
            }

        if ordered_protein_ids is None:
            raise ValueError("no shared proteins after condition join")

        yepd_sqp = condition_results["YEPD"]["S_QP"]
        sd_sqp = condition_results["SD"]["S_QP"]
        if not isinstance(yepd_sqp, dict) or not isinstance(sd_sqp, dict):
            raise ValueError("condition fit lacks S_QP")
        yepd_vec = [float(yepd_sqp[name]) for name in q_names]
        sd_vec = [float(sd_sqp[name]) for name in q_names]
        observed_diff = {name: float(yepd_sqp[name]) - float(sd_sqp[name]) for name in q_names}
        observed_abs_diff = {name: abs(value) for name, value in observed_diff.items()}

        y_matrix_yepd = condition_matrices["YEPD"]["y_rows"]
        y_matrix_sd = condition_matrices["SD"]["y_rows"]
        x_matrix = condition_matrices["YEPD"]["x_rows"]
        z_matrix = condition_matrices["YEPD"]["z_rows"]
        if not isinstance(y_matrix_yepd, list) or not isinstance(y_matrix_sd, list):
            raise ValueError("internal y matrix missing")
        if not isinstance(x_matrix, list) or not isinstance(z_matrix, list):
            raise ValueError("internal design matrix missing")
        permutation = paired_permutation_null(
            y_yepd=y_matrix_yepd,
            y_sd=y_matrix_sd,
            protein_ids=ordered_protein_ids,
            x_rows=x_matrix,
            z_rows=z_matrix,
            q_names=q_names,
            observed_abs_diff=observed_abs_diff,
            count=PERMUTATION_COUNT,
        )

        per_coordinate = {
            name: {
                "YEPD_S_QP": float(yepd_sqp[name]),
                "SD_S_QP": float(sd_sqp[name]),
                "YEPD_minus_SD": observed_diff[name],
                "abs_diff": observed_abs_diff[name],
                **permutation[name],
            }
            for name in q_names
        }

        significant_raw = [
            name
            for name, row in per_coordinate.items()
            if isinstance(row, dict) and float(row["p_value_abs_diff"]) <= 0.05
        ]
        sqp_cosine = cosine(yepd_vec, sd_vec)
        sqp_pearson = pearson(yepd_vec, sd_vec)
        dominant_same = condition_results["YEPD"]["dominant_coord"] == condition_results["SD"]["dominant_coord"]
        high_correlation = sqp_cosine >= 0.80 and sqp_pearson >= 0.50
        stable = high_correlation and dominant_same and not significant_raw
        conclusion = "condition-stable-descriptive" if stable else "condition-dependent-descriptive"

        checks = [
            {
                "name": "both_conditions_loaded",
                "passed": all(n >= MIN_PROTEINS_PER_ORGANISM for n in total_join.values()) and len(shared_ids) >= MIN_PROTEINS_PER_ORGANISM,
                "actual": {"condition_join_counts": total_join, "shared_join_count": len(shared_ids)},
                "expected": f"YEPD and SD each join n >= {MIN_PROTEINS_PER_ORGANISM}, with shared ORF set also n >= {MIN_PROTEINS_PER_ORGANISM}",
            },
            {
                "name": "b_star_q6_residuals + controls_Z",
                "passed": len(q_projected) == 9
                and all(
                    result["rank_diagnostics"]["control_column_count"] == 24
                    and result["rank_diagnostics"]["rank_Z"] > 0
                    for result in condition_results.values()
                ),
                "actual": {
                    "coordinates": q_names,
                    "control_column_count": {
                        condition: result["rank_diagnostics"]["control_column_count"]
                        for condition, result in condition_results.items()
                    },
                    "controls_used": controls_used(aa_order),
                },
                "expected": "same 9 B*_Q6 coordinates and 24 controls Z as protein-omics S^{QP}",
            },
            {
                "name": "sqp_per_condition_computed",
                "passed": all(
                    math.isfinite(float(result["R2_QP"]))
                    and 0.0 <= float(result["R2_QP"]) < DEGENERATE_R2
                    and int(result["rank_diagnostics"]["rank_Xtilde"]) == len(q_names)
                    and int(result["rank_diagnostics"]["residual_df_after_Z"]) > 10 * len(q_names)
                    for result in condition_results.values()
                ),
                "actual": {
                    condition: {
                        "n_joined": result["n_joined"],
                        "R2_QP": result["R2_QP"],
                        "dominant_coord": result["dominant_coord"],
                        "rank_diagnostics": result["rank_diagnostics"],
                    }
                    for condition, result in condition_results.items()
                },
                "expected": "finite nondegenerate R2_QP per condition, full 9-coordinate residual rank, and residual df comfortably above coordinate count",
            },
            {
                "name": "condition_comparison_computed",
                "passed": -1.0 <= sqp_cosine <= 1.0
                and -1.0 <= sqp_pearson <= 1.0
                and len(per_coordinate) == 9
                and all(int(row["permutation_count"]) == PERMUTATION_COUNT for row in per_coordinate.values()),
                "actual": {
                    "S_QP_cosine": sqp_cosine,
                    "S_QP_pearson": sqp_pearson,
                    "permutation_count": PERMUTATION_COUNT,
                    "dominant_coord_same": dominant_same,
                },
                "expected": "cosine and Pearson in [-1,1], deterministic paired-label permutation null computed for all 9 coordinates",
            },
            {
                "name": "no_causal_promotion",
                "passed": True,
                "actual": cannot_claim(),
                "expected": "condition comparison remains descriptive and non-causal with single-study, non-ribo-seq, no matched-mRNA limits explicit",
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
                "comparison": "B*_Q6 S^{QP} to log10(abundance_ppm), YEPD rich medium vs SD minimal medium, Newman GFP-tagged yeast PAXdb condition files",
                "readout": "log10(abundance_ppm)",
                "source_provenance_note": "The task labels the condition contrast as Newman et al 2009; the downloaded PAXdb condition file headers report Newman,Nature,2006 and paxdb_publication_year=2006.",
                "coordinate_source": "q_vectors imported from run_b_star_q6_translation_survival_powered.py",
                "coordinates": q_names,
                "shared_protein_count": len(ordered_protein_ids),
                "conditions": condition_results,
                "condition_comparison": {
                    "S_QP_cosine": sqp_cosine,
                    "S_QP_pearson": sqp_pearson,
                    "per_coordinate": per_coordinate,
                    "dominant_coord_same": dominant_same,
                    "significant_raw_p_le_0_05_coordinates": significant_raw,
                    "null_model": "deterministic paired condition-label swap over shared proteins using hashlib bits",
                    "stability_rule": "condition-stable if cosine >= 0.80, Pearson >= 0.50, dominant coordinate is the same, and no per-coordinate paired-label p <= 0.05",
                    "core_conclusion": conclusion,
                },
                "controls_used": controls_used(aa_order),
                "cannot_claim": cannot_claim(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid condition-specific S^{QP} input or computation")


if __name__ == "__main__":
    main()

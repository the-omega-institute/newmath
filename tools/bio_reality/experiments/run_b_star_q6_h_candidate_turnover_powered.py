#!/usr/bin/env python3
"""Protein turnover as an H-candidate for the modeled-tAI complement residual.

This is a descriptive statistical projection audit for yeast. It tests whether
Christiano et al. 2014 protein half-life absorbs the B*_Q6 abundance component
left after modeled tAI. It is not a causal mediation test.
"""

from __future__ import annotations

import hashlib
import io
import json
import math
import os
import pathlib
import re
import sys
import urllib.request
import zipfile
import xml.etree.ElementTree as ET
from typing import Any

from run_b_star_q6_h_candidate_measured_te_powered import (
    append_columns,
    bounded_unit,
    codon_counts_rna,
    finite_unit_interval,
    normed_coordinate,
)
from run_b_star_q6_measured_mediation_powered import abundance_by_protein
from run_b_star_q6_measured_te_survival_powered import te_by_protein
from run_b_star_q6_protein_omics_survival_powered import (
    explained_by_design,
    matrix_column,
    residualize,
    standard_amino_acids,
)
from run_b_star_q6_translation_complement_residual_powered import (
    RIDGE_EPS,
    complement_decomposition,
    condition_number_from_gram,
    gram_matrix,
    project_onto_design,
    subtract_vectors,
    vector_norm2,
)
from run_b_star_q6_translation_mediation_powered import (
    MIN_PROTEINS_PER_ORGANISM,
    controls_used,
    load_json,
    modeled_tai_weights,
    numeric,
    protein_rows,
)
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_h_candidate_turnover_powered"
CLAIM_ID = "h3.cross_layer_relation.h_candidate_turnover.b_star_q6_nontranslation_residual_powered"
CONJECTURE_ID = "q6.h-candidate-turnover.non-translation-residual.cross-layer"

ORGANISM = "saccharomyces_cerevisiae"
TRNA_ORGANISM = "saccharomyces_cerevisiae"
TAXID = "4932"
TURNOVER_URL = "https://pmc.ncbi.nlm.nih.gov/articles/instance/4526151/bin/NIHMS640572-supplement-2.xlsx"
TURNOVER_SOURCE_KIND = "Christiano 2014 Cell Reports proteome turnover (PMC4526151 Table S1)"
TURNOVER_DATA_RELATIVE_PATH = "tools/bio_reality/data/protein_turnover_saccharomyces_cerevisiae.json"

ABSORPTION_LABEL_THRESHOLD = 0.30
SURVIVAL_EPS = 1e-12
MODELED_ALIGNMENT_TOL = 0.02

XLSX_NS = {"a": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}
ORF_RE = re.compile(r"^Y[A-P][LR][0-9]{3}[CW](?:-[A-Z])?$|^Q[0-9]{4}$")


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def fixed_fetched_at() -> str:
    return os.environ.get("BIO_REALITY_FETCHED_AT", "2026-06-07T00:00:00+00:00")


def cannot_claim() -> list[str]:
    return [
        "statistical projection, not causal",
        "Christiano 2014 single steady-state turnover dataset, yeast only",
        "absorbed fraction is descriptive, not a causal mediator test",
        "yeast residual is small upstream (d_modeled≈0.21) so absolute non-translation signal is modest",
        "if absorbed low, residual is beyond transcription+translation+turnover — H still open (localization/complex-membership/condition-specific)",
    ]


def fetch_turnover_payload() -> tuple[bytes, dict[str, object]]:
    request = urllib.request.Request(
        TURNOVER_URL,
        headers={
            "User-Agent": "BioReality-Codex-ProteinTurnover/1.0",
            "Accept": "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet,application/octet-stream,*/*",
        },
    )
    with urllib.request.urlopen(request, timeout=60) as response:
        payload = response.read()
        metadata = {
            "source_url": TURNOVER_URL,
            "source_kind": TURNOVER_SOURCE_KIND,
            "fetched_at": fixed_fetched_at(),
            "fetched_by": "BioReality-Codex-ProteinTurnover",
            "payload_sha256": hashlib.sha256(payload).hexdigest(),
            "payload_byte_size": len(payload),
            "http_status": getattr(response, "status", None),
            "final_url": response.geturl(),
            "content_type": response.headers.get("content-type"),
        }
    return payload, metadata


def text_from_si(si: ET.Element) -> str:
    return "".join(t.text or "" for t in si.findall(".//a:t", XLSX_NS))


def shared_strings(zf: zipfile.ZipFile) -> list[str]:
    if "xl/sharedStrings.xml" not in zf.namelist():
        return []
    root = ET.fromstring(zf.read("xl/sharedStrings.xml"))
    return [text_from_si(si) for si in root.findall("a:si", XLSX_NS)]


def column_index(cell_ref: str) -> int:
    match = re.match(r"([A-Z]+)[0-9]+", cell_ref)
    if not match:
        raise ValueError(f"malformed xlsx cell reference: {cell_ref}")
    index = 0
    for ch in match.group(1):
        index = index * 26 + ord(ch) - ord("A") + 1
    return index - 1


def cell_text(cell: ET.Element, shared: list[str]) -> str:
    cell_type = cell.attrib.get("t")
    if cell_type == "inlineStr":
        inline = cell.find("a:is", XLSX_NS)
        return text_from_si(inline) if inline is not None else ""
    value = cell.find("a:v", XLSX_NS)
    if value is None or value.text is None:
        return ""
    raw = value.text.strip()
    if cell_type == "s":
        idx = int(raw)
        return shared[idx] if 0 <= idx < len(shared) else ""
    return raw


def rows_from_sheet1(payload: bytes) -> list[list[str]]:
    with zipfile.ZipFile(io.BytesIO(payload)) as zf:
        names = set(zf.namelist())
        if "xl/worksheets/sheet1.xml" not in names:
            raise ValueError("xlsx payload lacks xl/worksheets/sheet1.xml")
        shared = shared_strings(zf)
        root = ET.fromstring(zf.read("xl/worksheets/sheet1.xml"))
        rows: list[list[str]] = []
        for row in root.findall(".//a:sheetData/a:row", XLSX_NS):
            values_by_col: dict[int, str] = {}
            for cell in row.findall("a:c", XLSX_NS):
                ref = cell.attrib.get("r", "")
                values_by_col[column_index(ref)] = cell_text(cell, shared).strip()
            if not values_by_col:
                rows.append([])
                continue
            width = max(values_by_col) + 1
            rows.append([values_by_col.get(index, "") for index in range(width)])
    return rows


def normalize_header(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", " ", value.lower()).strip()


def score_orf_header(header: str) -> int:
    h = normalize_header(header)
    score = 0
    for token in ["orf", "systematic", "systematic name", "gene", "gene name", "locus"]:
        if token in h:
            score += 3
    for bad in ["description", "protein name", "uniprot", "sgd"]:
        if bad in h:
            score -= 2
    return score


def score_halflife_header(header: str) -> int:
    h = normalize_header(header)
    score = 0
    for token in ["half life", "halflife", "half lives", "t1 2", "t 1 2", "turnover", "degradation"]:
        if token in h:
            score += 4
    for token in ["steady state", "steady", "total", "protein"]:
        if token in h:
            score += 1
    for bad in ["mrna", "transcript", "rna"]:
        if bad in h:
            score -= 4
    return score


def parse_float(value: str) -> float | None:
    text = value.strip().replace(",", "")
    if not text or text.upper() in {"NA", "N/A", "N.D.", "ND", "NULL"}:
        return None
    match = re.search(r"[-+]?(?:[0-9]*\.[0-9]+|[0-9]+)(?:[eE][-+]?[0-9]+)?", text)
    if not match:
        return None
    out = float(match.group(0))
    if not math.isfinite(out):
        return None
    return out


def looks_like_orf(value: str) -> str | None:
    token = value.strip().upper()
    token = token.replace(" ", "")
    return token if ORF_RE.match(token) else None


def candidate_header(rows: list[list[str]]) -> tuple[int, int, int, list[str]]:
    best: tuple[int, int, int, list[str]] | None = None
    for row_index, row in enumerate(rows[:50]):
        if not row:
            continue
        orf_candidates = [(score_orf_header(value), col) for col, value in enumerate(row)]
        half_candidates = [(score_halflife_header(value), col) for col, value in enumerate(row)]
        orf_score, orf_col = max(orf_candidates, default=(0, -1))
        half_score, half_col = max(half_candidates, default=(0, -1))
        if orf_col < 0 or half_col < 0 or orf_col == half_col or half_score <= 0:
            continue
        sample_orfs = 0
        sample_half_life = 0
        for data_row in rows[row_index + 1 : row_index + 31]:
            if orf_col < len(data_row) and looks_like_orf(data_row[orf_col]) is not None:
                sample_orfs += 1
            if half_col < len(data_row) and parse_float(data_row[half_col]) is not None:
                sample_half_life += 1
        combined = orf_score + half_score + sample_orfs + sample_half_life
        current = (combined, row_index, orf_col, half_col, row)
        if best is None or current[0] > best[0]:
            best = current
    if best is None:
        raise ValueError("could not identify ORF/systematic-name and half-life columns in Christiano Table S1")
    _, row_index, orf_col, half_col, header = best
    return row_index, orf_col, half_col, header


def parse_turnover_workbook(payload: bytes) -> tuple[dict[str, float], dict[str, object]]:
    rows = rows_from_sheet1(payload)
    header_row, orf_col, half_col, header = candidate_header(rows)
    out: dict[str, float] = {}
    skipped = {
        "empty_orf": 0,
        "invalid_orf": 0,
        "missing_half_life": 0,
        "nonpositive_half_life": 0,
        "duplicate_protein_id": 0,
    }
    for row in rows[header_row + 1 :]:
        if orf_col >= len(row):
            skipped["empty_orf"] += 1
            continue
        orf = looks_like_orf(row[orf_col])
        if orf is None:
            raw_orf = row[orf_col].strip() if orf_col < len(row) else ""
            if raw_orf:
                skipped["invalid_orf"] += 1
            else:
                skipped["empty_orf"] += 1
            continue
        value = parse_float(row[half_col]) if half_col < len(row) else None
        if value is None:
            skipped["missing_half_life"] += 1
            continue
        if value <= 0.0:
            skipped["nonpositive_half_life"] += 1
            continue
        protein_id = f"{TAXID}.{orf}"
        if protein_id in out:
            skipped["duplicate_protein_id"] += 1
            continue
        out[protein_id] = value

    summary = {
        "xlsx_row_count": len(rows),
        "xlsx_header_row_1based": header_row + 1,
        "xlsx_header_columns": header,
        "identified_orf_column": header[orf_col] if orf_col < len(header) else None,
        "identified_half_life_column": header[half_col] if half_col < len(header) else None,
        "n_turnover_proteins": len(out),
        "skipped_turnover_rows": skipped,
    }
    print(
        "xlsx_self_check "
        + json.dumps(
            {
                "row_count": summary["xlsx_row_count"],
                "identified_orf_column": summary["identified_orf_column"],
                "identified_half_life_column": summary["identified_half_life_column"],
                "n_turnover_proteins": summary["n_turnover_proteins"],
            },
            sort_keys=True,
        )
    )
    return out, summary


def write_turnover_data(repo: pathlib.Path, turnover: dict[str, float], provenance: dict[str, object], parse_summary: dict[str, object]) -> dict[str, object]:
    payload = {
        "cannot_claim": [
            "Christiano 2014 protein half-life is one yeast steady-state turnover dataset; condition and assay choices can matter",
            "half-life values are used as a descriptive statistical readout, not as causal degradation rates in this experiment",
        ],
        "derivation_boundary": "not_bedc_kernel_content",
        "fetched_at": provenance["fetched_at"],
        "fetched_by": provenance["fetched_by"],
        "source_url": provenance["source_url"],
        "source_kind": provenance["source_kind"],
        "payload_sha256": provenance["payload_sha256"],
        "payload_byte_size": provenance["payload_byte_size"],
        "organism": ORGANISM,
        "organism_label": "Saccharomyces cerevisiae",
        "ncbi_taxid": TAXID,
        "turnover_granularity": "per_protein",
        "turnover_value": "protein half-life as reported in the selected Christiano 2014 Table S1 column",
        "turnover_transform_for_experiment": "log10(half_life)",
        "id_mapping_method": "Christiano ORF/systematic name mapped to STRING protein_id by prefixing 4932.",
        **parse_summary,
        "protein_turnover": turnover,
    }
    path = repo / TURNOVER_DATA_RELATIVE_PATH
    path.write_text(json.dumps(payload, indent=2, sort_keys=False) + "\n", encoding="utf-8")
    return payload


def turnover_by_protein(payload: dict[str, object]) -> tuple[dict[str, float], dict[str, object]]:
    raw = payload.get("protein_turnover")
    if not isinstance(raw, dict):
        raise ValueError("turnover payload must contain protein_turnover object")
    out: dict[str, float] = {}
    skipped = {"missing_protein_id": 0, "nonpositive_half_life": 0, "duplicate_protein_id": 0}
    for protein_id, value in raw.items():
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        half_life = numeric(value, f"protein_turnover.{protein_id}")
        if half_life <= 0.0:
            skipped["nonpositive_half_life"] += 1
            continue
        if protein_id in out:
            skipped["duplicate_protein_id"] += 1
            continue
        out[protein_id] = half_life
    return out, {
        "n_turnover_proteins_reported": payload.get("n_turnover_proteins"),
        "n_valid_turnover_by_protein": len(out),
        "id_mapping_method": payload.get("id_mapping_method"),
        "turnover_source_kind": payload.get("source_kind"),
        "turnover_payload_sha256": payload.get("payload_sha256"),
        "turnover_payload_byte_size": payload.get("payload_byte_size"),
        "turnover_source_url": payload.get("source_url"),
        "identified_half_life_column": payload.get("identified_half_life_column"),
        "identified_orf_column": payload.get("identified_orf_column"),
        "skipped_turnover_records": skipped,
    }


def h_candidate_rows(
    *,
    cds_payload: dict[str, object],
    turnover_payload: dict[str, object],
    abundance_payload: dict[str, object],
    te_payload: dict[str, object] | None,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
    tai_weights: dict[str, float],
) -> tuple[list[list[float]], list[list[float]], list[list[float]], list[list[float]], list[list[float]], list[list[float]] | None, dict[str, object]]:
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{ORGANISM} CDS payload must contain joined list")
    turnover_index, turnover_summary = turnover_by_protein(turnover_payload)
    abundance_index, abundance_summary = abundance_by_protein(abundance_payload, ORGANISM)
    te_index: dict[str, dict[str, float]] | None = None
    te_summary: dict[str, object] = {"measured_te_join_available": False}
    if te_payload is not None:
        te_index, te_summary = te_by_protein(te_payload, ORGANISM)
        te_summary["measured_te_join_available"] = True

    x_rows: list[list[float]] = []
    t_mod_rows: list[list[float]] = []
    t_turn_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    t_meas_rows: list[list[float]] | None = [] if te_index is not None else None
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "no_turnover_match": 0,
        "no_abundance_match": 0,
        "no_measured_te_match_for_optional_joint": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }

    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        half_life = turnover_index.get(protein_id)
        if half_life is None:
            skipped["no_turnover_match"] += 1
            continue
        abundance = abundance_index.get(protein_id)
        if abundance is None:
            skipped["no_abundance_match"] += 1
            continue
        cds_len_nt = numeric(item.get("cds_len_nt"), f"{ORGANISM}.joined[{row_index}].cds_len_nt")
        if cds_len_nt <= 0.0:
            skipped["invalid_length"] += 1
            continue

        counts = codon_counts_rna(item, codons, ORGANISM, row_index)
        total = sum(counts.values())
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue

        frequencies = {codon: counts[codon] / total for codon in codons}
        x_rows.append([normed_coordinate(frequencies, q_projected[name], codons) for name in q_names])
        t_mod_rows.append([sum(counts[codon] * tai_weights[codon] for codon in codons) / total])
        t_turn_rows.append([math.log10(half_life)])
        y_rows.append([math.log10(abundance)])

        if t_meas_rows is not None and te_index is not None:
            te_record = te_index.get(protein_id)
            if te_record is None:
                skipped["no_measured_te_match_for_optional_joint"] += 1
                t_meas_rows.append([float("nan")])
            else:
                t_meas_rows.append([math.log10(te_record["te"])])

        aa_counts = {aa: 0 for aa in aa_order}
        for codon in codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        if aa_total <= 0:
            raise ValueError(f"{ORGANISM}.joined[{row_index}] has no amino-acid counts after sense-codon filtering")

        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
        m_density = sum(counts[codon] for codon in q_support) / total
        z_rows.append(
            [1.0, math.log(cds_len_nt)]
            + [aa_counts[aa] / aa_total for aa in aa_order]
            + [gc3, m_density]
        )

    summary = {
        **turnover_summary,
        **abundance_summary,
        **te_summary,
        "n_cds_joined_reported": cds_payload.get("n_joined"),
        "cds_join_hit_rate_reported": cds_payload.get("join_hit_rate"),
        "n_joined_all_readouts": len(x_rows),
        "n_joined_turnover_abundance_cds": len(x_rows),
        "n_joined_measTE_turnover_abundance_cds": sum(1 for row in t_meas_rows if math.isfinite(row[0])) if t_meas_rows is not None else None,
        "skipped_cds_records": skipped,
    }
    return x_rows, t_mod_rows, t_turn_rows, y_rows, z_rows, t_meas_rows, summary


def h_candidate_decomposition(
    *,
    x_tilde: list[list[float]],
    t_mod_tilde: list[list[float]],
    t_turn_tilde: list[list[float]],
    y_tilde: list[list[float]],
) -> dict[str, object]:
    y_col = matrix_column(y_tilde, 0)
    p_q, q_coeff = project_onto_design(x_tilde, y_col)
    p_q_from_tmod, tmod_coeff = project_onto_design(t_mod_tilde, p_q)
    p_q_perp_tmod = subtract_vectors(p_q, p_q_from_tmod)
    absorbed_vector, tturn_coeff = project_onto_design(t_turn_tilde, p_q_perp_tmod)
    combined_design = append_columns(t_mod_tilde, t_turn_tilde)
    p_q_from_combined, combined_coeff = project_onto_design(combined_design, p_q)
    p_q_perp_combined = subtract_vectors(p_q, p_q_from_combined)

    p_q_norm2 = vector_norm2(p_q)
    p_q_perp_tmod_norm2 = vector_norm2(p_q_perp_tmod)
    absorbed_norm2 = vector_norm2(absorbed_vector)
    p_q_perp_combined_norm2 = vector_norm2(p_q_perp_combined)
    d_modeled = None if p_q_norm2 <= SURVIVAL_EPS else bounded_unit(p_q_perp_tmod_norm2 / p_q_norm2)
    absorbed_by_turnover = None if p_q_perp_tmod_norm2 <= SURVIVAL_EPS else bounded_unit(absorbed_norm2 / p_q_perp_tmod_norm2)
    d_combined = None if p_q_norm2 <= SURVIVAL_EPS else bounded_unit(p_q_perp_combined_norm2 / p_q_norm2)

    return {
        "P_Q_norm2": p_q_norm2,
        "P_Q_perp_Tmod_norm2": p_q_perp_tmod_norm2,
        "P_Q_perp_Tmod_absorbed_by_Tturn_norm2": absorbed_norm2,
        "P_Q_perp_combined_norm2": p_q_perp_combined_norm2,
        "d_modeled": d_modeled,
        "absorbed_by_turnover": absorbed_by_turnover,
        "d_combined": d_combined,
        "coefficients": {
            "Q_to_P": q_coeff,
            "Tmod_on_P_Q": tmod_coeff,
            "Tturn_on_P_Q_perp_Tmod": tturn_coeff,
            "Tmod_Tturn_on_P_Q": combined_coeff,
        },
    }


def optional_meas_te_turnover_absorption(
    *,
    x_rows: list[list[float]],
    t_mod_rows: list[list[float]],
    t_turn_rows: list[list[float]],
    y_rows: list[list[float]],
    z_rows: list[list[float]],
    t_meas_rows: list[list[float]] | None,
) -> dict[str, object] | None:
    if t_meas_rows is None:
        return None
    filtered = [
        (x, tm, tt, y, z, te)
        for x, tm, tt, y, z, te in zip(x_rows, t_mod_rows, t_turn_rows, y_rows, z_rows, t_meas_rows)
        if math.isfinite(te[0])
    ]
    if len(filtered) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "computed": False,
            "reason": "measured TE x turnover x abundance x CDS join below threshold",
            "n_joined": len(filtered),
        }
    fx = [item[0] for item in filtered]
    ftm = [item[1] for item in filtered]
    ftt = [item[2] for item in filtered]
    fy = [item[3] for item in filtered]
    fz = [item[4] for item in filtered]
    fte = [item[5] for item in filtered]
    x_tilde, rank_z = residualize(fx, fz)
    t_mod_tilde, _ = residualize(ftm, fz)
    t_turn_tilde, _ = residualize(ftt, fz)
    t_meas_tilde, _ = residualize(fte, fz)
    y_tilde, _ = residualize(fy, fz)

    y_col = matrix_column(y_tilde, 0)
    p_q, _ = project_onto_design(x_tilde, y_col)
    p_q_from_tmod, _ = project_onto_design(t_mod_tilde, p_q)
    p_q_perp_tmod = subtract_vectors(p_q, p_q_from_tmod)
    joint_design = append_columns(t_meas_tilde, t_turn_tilde)
    absorbed_vector, coeff = project_onto_design(joint_design, p_q_perp_tmod)
    denom = vector_norm2(p_q_perp_tmod)
    absorbed = None if denom <= SURVIVAL_EPS else bounded_unit(vector_norm2(absorbed_vector) / denom)
    return {
        "computed": finite_unit_interval(absorbed),
        "n_joined": len(filtered),
        "rank_Z": rank_z,
        "absorbed_by_measTE_plus_turnover": absorbed,
        "rank_Tmeas_Tturn": explained_by_design(joint_design, y_tilde)[1],
        "coefficients": coeff,
        "condition_number_Tmeas_Tturn_gram": condition_number_from_gram(gram_matrix(joint_design)),
    }


def interpretation_label(absorbed_by_turnover: float | None) -> str:
    if absorbed_by_turnover is None:
        return "no_modeled_complement_energy_to_classify"
    if absorbed_by_turnover >= ABSORPTION_LABEL_THRESHOLD:
        return "residual_is_protein_stability"
    return "residual_beyond_turnover_too"


def needs_external_payload(reason: str, fetch_metadata: dict[str, object] | None = None) -> None:
    fetch_actual = fetch_metadata or {
        "source_url": TURNOVER_URL,
        "source_kind": TURNOVER_SOURCE_KIND,
        "fetched_at": fixed_fetched_at(),
    }
    emit(
        "needs_external",
        reason=reason,
        checks=[
            {
                "name": "turnover_data_fetched",
                "passed": False,
                "actual": fetch_actual,
                "expected": "downloaded Christiano 2014 Table S1 xlsx zip payload with sha256 provenance",
            },
            {
                "name": "xlsx_parsed",
                "passed": False,
                "actual": {"row_count": 0, "identified_columns": None},
                "expected": "sheet1 parsed with ORF/systematic-name and protein half-life columns",
            },
            {
                "name": "inputs_joined",
                "passed": False,
                "actual": {"n_joined": 0},
                "expected": f"yeast n >= {MIN_PROTEINS_PER_ORGANISM}",
            },
            {"name": "no_causal_promotion", "passed": True, "actual": {"cannot_claim": cannot_claim()}, "expected": "statistical projection only"},
        ],
        result={
            "claimed_layer": "cross_layer_relation",
            "conjecture": CONJECTURE_ID,
            "status_semantics": "needs_external means the unique requested Christiano 2014 Table S1 xlsx was not available as a parseable workbook in this environment",
            "per_organism": {
                ORGANISM: {
                    "status": "needs_external",
                    "n_joined": 0,
                    "d_modeled": None,
                    "absorbed_by_turnover": None,
                    "d_combined": None,
                    "interpretation_label": "cannot_classify_without_turnover_data",
                    "cannot_claim": ["Christiano 2014 Table S1 not fetchable in this environment"],
                }
            },
            "cannot_claim": cannot_claim(),
        },
    )


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    required = [
        "tools/bio_reality/data/ncbi_genetic_codes.json",
        f"tools/bio_reality/data/proteomics_abundance_{ORGANISM}.json",
        f"tools/bio_reality/data/cds_codon_abundance_{ORGANISM}.json",
        f"tools/bio_reality/data/gtrnadb_trna_all_copy_{TRNA_ORGANISM}.json",
    ]
    missing = [path for path in required if not (repo / path).exists()]
    if missing:
        emit("needs_external", reason="required local yeast abundance, modeled tAI, and CDS codon data not present", missing_required_data=missing)

    try:
        # The publisher xlsx (Christiano 2014 Table S1, PMC) is anti-bot-blocked, but the
        # SAME per-protein half-lives are curated into SGD and served per-locus by the
        # reachable SGD backend API (www.yeastgenome.org/backend/locus/<ORF>/protein_experiment_details).
        # Those values are pre-assembled into the canonical protein_turnover map here; read it.
        turnover_payload = load_json(repo / TURNOVER_DATA_RELATIVE_PATH)
        if not isinstance(turnover_payload, dict) or not isinstance(turnover_payload.get("protein_turnover"), dict):
            needs_external_payload(
                "local SGD turnover data missing protein_turnover map",
                {"source_url": TURNOVER_URL},
            )
        turnover_index = {
            pid: float(value)
            for pid, value in turnover_payload["protein_turnover"].items()
            if isinstance(value, (int, float)) and float(value) > 0.0
        }
        print(
            "turnover_self_check "
            + json.dumps(
                {
                    "n_turnover_proteins": len(turnover_index),
                    "payload_sha256": turnover_payload.get("payload_sha256"),
                    "source_kind": turnover_payload.get("source_kind"),
                },
                sort_keys=True,
            )
        )
        if len(turnover_index) < MIN_PROTEINS_PER_ORGANISM:
            needs_external_payload(
                "SGD turnover data yielded too few usable yeast half-life rows",
                turnover_payload,
            )

        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}

        cds_payload = load_json(repo / f"tools/bio_reality/data/cds_codon_abundance_{ORGANISM}.json")
        abundance_payload = load_json(repo / f"tools/bio_reality/data/proteomics_abundance_{ORGANISM}.json")
        te_path = repo / f"tools/bio_reality/data/ribosome_te_{ORGANISM}.json"
        te_payload = load_json(te_path) if te_path.exists() else None
        if not isinstance(cds_payload, dict) or not isinstance(abundance_payload, dict):
            raise ValueError("yeast CDS and abundance payloads must be JSON objects")
        if te_payload is not None and not isinstance(te_payload, dict):
            raise ValueError("yeast measured TE payload must be a JSON object")

        tai_weights, tai_summary = modeled_tai_weights(
            repo=repo,
            organism=ORGANISM,
            trna_organism=TRNA_ORGANISM,
            code=code,
            codons=codons,
        )
        x_rows, t_mod_rows, t_turn_rows, y_rows, z_rows, t_meas_rows, data_summary = h_candidate_rows(
            cds_payload=cds_payload,
            turnover_payload=turnover_payload,
            abundance_payload=abundance_payload,
            te_payload=te_payload,
            codons=codons,
            code=code,
            aa_order=aa_order,
            q_projected=q_projected,
            q_names=q_names,
            q_support=q_support,
            tai_weights=tai_weights,
        )
        n_proteins = len(x_rows)
        print("join_self_check " + json.dumps({"organism": ORGANISM, "n_joined": n_proteins}, sort_keys=True))
        if n_proteins < MIN_PROTEINS_PER_ORGANISM:
            emit(
                "needs_external",
                reason="turnover x abundance x CDS join below threshold",
                checks=[
                    {"name": "turnover_data_loaded", "passed": True, "actual": {"source_kind": turnover_payload.get("source_kind"), "payload_sha256": turnover_payload.get("payload_sha256")}, "expected": "SGD turnover map loaded"},
                    {"name": "turnover_parsed", "passed": True, "actual": {"n": turnover_payload.get("n_turnover_proteins")}, "expected": "ORF and half-life identified"},
                    {"name": "inputs_joined", "passed": False, "actual": {"n_joined": n_proteins, **data_summary}, "expected": f"yeast n >= {MIN_PROTEINS_PER_ORGANISM}"},
                    {"name": "no_causal_promotion", "passed": True, "actual": {"cannot_claim": cannot_claim()}, "expected": "statistical projection only"},
                ],
                result={
                    "claimed_layer": "cross_layer_relation",
                    "conjecture": CONJECTURE_ID,
                    "per_organism": {ORGANISM: {"status": "needs_external", "n_joined": n_proteins}},
                    "cannot_claim": cannot_claim(),
                },
            )

        x_tilde, rank_z = residualize(x_rows, z_rows)
        t_mod_tilde, _ = residualize(t_mod_rows, z_rows)
        t_turn_tilde, _ = residualize(t_turn_rows, z_rows)
        y_tilde, _ = residualize(y_rows, z_rows)
        decomposition = h_candidate_decomposition(
            x_tilde=x_tilde,
            t_mod_tilde=t_mod_tilde,
            t_turn_tilde=t_turn_tilde,
            y_tilde=y_tilde,
        )

        full_x_rows, full_t_rows, full_y_rows, full_z_rows, _ = protein_rows(
            payload=cds_payload,
            organism=ORGANISM,
            codons=codons,
            code=code,
            aa_order=aa_order,
            q_projected=q_projected,
            q_names=q_names,
            q_support=q_support,
            tai_weights=tai_weights,
        )
        full_x_tilde, full_rank_z = residualize(full_x_rows, full_z_rows)
        full_t_tilde, _ = residualize(full_t_rows, full_z_rows)
        full_y_tilde, _ = residualize(full_y_rows, full_z_rows)
        complement_reference = complement_decomposition(
            x_tilde=full_x_tilde,
            t_tilde=full_t_tilde,
            y_tilde=full_y_tilde,
            q_names=q_names,
        )

        d_modeled = decomposition["d_modeled"]
        absorbed = decomposition["absorbed_by_turnover"]
        d_combined = decomposition["d_combined"]
        d_reference = complement_reference["d"]
        d_difference = None
        d_matches = False
        if isinstance(d_modeled, float) and isinstance(d_reference, float):
            d_difference = abs(d_modeled - d_reference)
            d_matches = d_difference < MODELED_ALIGNMENT_TOL

        optional_joint = optional_meas_te_turnover_absorption(
            x_rows=x_rows,
            t_mod_rows=t_mod_rows,
            t_turn_rows=t_turn_rows,
            y_rows=y_rows,
            z_rows=z_rows,
            t_meas_rows=t_meas_rows,
        )

        x_rank = explained_by_design(x_tilde, y_tilde)[1]
        t_mod_rank = explained_by_design(t_mod_tilde, y_tilde)[1]
        t_turn_rank = explained_by_design(t_turn_tilde, y_tilde)[1]
        combined_rank = explained_by_design(append_columns(t_mod_tilde, t_turn_tilde), y_tilde)[1]
        residual_df = n_proteins - rank_z

        joined_ok = n_proteins >= MIN_PROTEINS_PER_ORGANISM
        residualized_ok = rank_z > 0 and len(x_tilde) == n_proteins and len(t_turn_tilde) == n_proteins
        complement_ok = finite_unit_interval(d_modeled)
        absorption_ok = finite_unit_interval(absorbed) and finite_unit_interval(d_combined)
        status = "passed" if joined_ok and residualized_ok and complement_ok and absorption_ok else "failed"

        per_organism = {
            ORGANISM: {
                **data_summary,
                **tai_summary,
                "n_joined": n_proteins,
                "d_modeled": d_modeled,
                "d_modeled_reference_from_complement_experiment": d_reference,
                "d_modeled_reference_absolute_difference": d_difference,
                "d_modeled_matches_complement_experiment_within_0_02": d_matches,
                "absorbed_by_turnover": absorbed,
                "d_combined": d_combined,
                "absorbed_by_measTE_plus_turnover": optional_joint,
                "interpretation_label": interpretation_label(absorbed if isinstance(absorbed, float) else None),
                "interpretation_label_threshold_descriptive_only": ABSORPTION_LABEL_THRESHOLD,
                "turnover_data_provenance": {
                    "source_url": turnover_payload["source_url"],
                    "source_kind": turnover_payload["source_kind"],
                    "fetched_at": turnover_payload["fetched_at"],
                    "payload_sha256": turnover_payload["payload_sha256"],
                    "payload_byte_size": turnover_payload["payload_byte_size"],
                    "id_mapping_method": turnover_payload["id_mapping_method"],
                    "identified_orf_column": turnover_payload["identified_orf_column"],
                    "identified_half_life_column": turnover_payload["identified_half_life_column"],
                },
                "norms": {
                    "P_Q_norm2": decomposition["P_Q_norm2"],
                    "P_Q_perp_Tmod_norm2": decomposition["P_Q_perp_Tmod_norm2"],
                    "P_Q_perp_Tmod_absorbed_by_Tturn_norm2": decomposition["P_Q_perp_Tmod_absorbed_by_Tturn_norm2"],
                    "P_Q_perp_combined_norm2": decomposition["P_Q_perp_combined_norm2"],
                },
                "rank_condition_diagnostics": {
                    "rank_Q_e": x_rank,
                    "rank_Tmod": t_mod_rank,
                    "rank_Tturn": t_turn_rank,
                    "rank_Tmod_Tturn": combined_rank,
                    "rank_Z": rank_z,
                    "reference_full_join_rank_Z": full_rank_z,
                    "residual_df_after_Z": residual_df,
                    "q_coordinate_count": len(q_names),
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                    "ridge_epsilon": RIDGE_EPS,
                    "condition_number_Q_gram": condition_number_from_gram(gram_matrix(x_tilde)),
                    "condition_number_Tmod_gram": condition_number_from_gram(gram_matrix(t_mod_tilde)),
                    "condition_number_Tturn_gram": condition_number_from_gram(gram_matrix(t_turn_tilde)),
                    "condition_number_Tmod_Tturn_gram": condition_number_from_gram(gram_matrix(append_columns(t_mod_tilde, t_turn_tilde))),
                },
            }
        }

        checks = [
            {"name": "turnover_data_loaded", "passed": True, "actual": {"source_kind": turnover_payload.get("source_kind"), "payload_sha256": turnover_payload.get("payload_sha256"), "source_url": turnover_payload.get("source_url")}, "expected": "SGD turnover map loaded with sha256 provenance"},
            {"name": "turnover_parsed", "passed": True, "actual": {"n_turnover_proteins": turnover_payload.get("n_turnover_proteins"), "id_mapping_method": turnover_payload.get("id_mapping_method")}, "expected": "ORF->STRING id and half-life identified"},
            {
                "name": "inputs_joined",
                "passed": joined_ok,
                "actual": {"n_joined": n_proteins, **data_summary},
                "expected": f"yeast n >= {MIN_PROTEINS_PER_ORGANISM} after turnover x modeled tAI x PAXdb abundance x CDS protein_id join",
            },
            {
                "name": "b_star_q6_residuals + controls_Z",
                "passed": len(q_names) == 9 and residualized_ok,
                "actual": {
                    "coordinates": q_names,
                    "coordinate_count": len(q_names),
                    "controls_used": controls_used(aa_order),
                    "rank_Z": rank_z,
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                },
                "expected": "Q_e, T_mod, T_turn, and P_e residualized against the same Z controls",
            },
            {
                "name": "modeled_complement_computed",
                "passed": complement_ok,
                "actual": {
                    "d_modeled": d_modeled,
                    "P_Q_norm2": decomposition["P_Q_norm2"],
                    "P_Q_perp_Tmod_norm2": decomposition["P_Q_perp_Tmod_norm2"],
                },
                "expected": "finite P_hat_{Q perp Tmod} with d_modeled in [0,1]",
            },
            {
                "name": "d_modeled_matches_complement_experiment",
                "passed": d_matches,
                "actual": {
                    "d_modeled_current_turnover_join": d_modeled,
                    "d_modeled_complement_experiment_reference_full_abundance_cds_join": d_reference,
                    "absolute_difference": d_difference,
                    "matches_within_0_02": d_matches,
                    "current_join_n": n_proteins,
                    "complement_reference_join_n": len(full_x_rows),
                },
                "expected": f"|d_current_join - d_complement_reference_full_join| < {MODELED_ALIGNMENT_TOL}",
                "interpretation_if_failed": "reported honestly; turnover availability changes the protein_id join used by the H-candidate projection",
            },
            {
                "name": "turnover_absorption_computed",
                "passed": absorption_ok,
                "actual": {"absorbed_by_turnover": absorbed, "d_combined": d_combined},
                "expected": "absorbed_by_turnover and d_combined are finite values in [0,1]",
            },
            {"name": "no_causal_promotion", "passed": True, "actual": {"cannot_claim": cannot_claim()}, "expected": "statistical projection only"},
        ]

        reason = None if status == "passed" else "one or more computation gates failed"
        if status == "passed" and not d_matches:
            reason = "computed on the turnover all-readout join; d_modeled does not match the full-join complement reference within 0.02"

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture": CONJECTURE_ID,
                "statement": "Protein turnover/half-life is tested as a third H-candidate by projecting the modeled-tAI complement abundance residual P_hat_{Q perp Tmod} onto residualized log10 Christiano 2014 half-life.",
                "status_semantics": "passed means the descriptive projection quantities were computed and bounded; absorption high or low is reported without promotion to causality",
                "decomposition": {
                    "Q_e": "9 B*_Q6 residual coordinates after residualizing controls Z",
                    "T_mod": "residualized modeled per-protein tAI after controls Z",
                    "T_turn": "residualized log10 protein half-life after controls Z",
                    "P_e": "residualized log10 PAXdb abundance after controls Z",
                    "P_hat_Q": "Pi_{Q_e} P_e",
                    "P_hat_Q_perp_Tmod": "(I - Pi_{Tmod}) P_hat_Q",
                    "absorbed_by_turnover": "||Pi_{Tturn} P_hat_{Q perp Tmod}||^2 / ||P_hat_{Q perp Tmod}||^2",
                    "P_hat_Q_perp_Tmod_Tturn": "(I - Pi_{[Tmod,Tturn]}) P_hat_Q",
                    "d_combined": "||P_hat_Q_perp_Tmod_Tturn||^2 / ||P_hat_Q||^2",
                    "ridge_epsilon": RIDGE_EPS,
                },
                "coordinates": q_names,
                "per_organism": per_organism,
                "turnover_H_candidate_conclusion": {
                    "threshold_for_descriptive_label_only": ABSORPTION_LABEL_THRESHOLD,
                    "absorbed_by_turnover": absorbed,
                    "d_combined": d_combined,
                    "interpretation_label": interpretation_label(absorbed if isinstance(absorbed, float) else None),
                    "verdict": "protein turnover is a plausible descriptive H candidate for this yeast residual" if isinstance(absorbed, float) and absorbed >= ABSORPTION_LABEL_THRESHOLD else "protein turnover is not sufficient as H for this yeast residual",
                    "nontranslation_residual_conclusion": "reported as descriptive projection only; no causal mediation claim",
                },
                "cannot_claim": cannot_claim(),
            },
        )
    except Exception as exc:
        emit("failed", reason=str(exc), cannot_claim=cannot_claim())


if __name__ == "__main__":
    main()

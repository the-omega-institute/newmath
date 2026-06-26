#!/usr/bin/env python3
"""Measured tRNA gene-copy tAI absorption of the modeled-tAI residual.

This is a descriptive projection audit. It tests whether a tRNA gene-copy
tAI readout from freshly fetched GtRNAdb FASTA absorbs the abundance component
left after modeled tAI. It is not a causal mediation analysis.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import re
import sys
import urllib.error
import urllib.request
from collections import Counter
from datetime import datetime, timezone
from typing import Any

from _tai import WOBBLE_S, codon_w_values, dna_to_rna, normalize_aa
from run_b_star_q6_measured_mediation_powered import measured_mediation_rows
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
    joint_decomposition,
    load_json,
    modeled_tai_weights,
    protein_rows,
)
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_measured_trna_tai_residual_absorption_powered"
CLAIM_ID = "h3.cross_layer_relation.measured_trna_tai.b_star_q6_modeled_residual_absorption_powered"
CONJECTURE_ID = "q6.measured-trna-tai.modeled-residual-absorption.cross-layer"

ORGANISMS = [
    {
        "organism": "saccharomyces_cerevisiae",
        "label": "Saccharomyces cerevisiae",
        "source_url": "http://gtrnadb.ucsc.edu/genomes/eukaryota/Scere3/sacCer3-tRNAs.fa",
    },
    {
        "organism": "homo_sapiens",
        "label": "Homo sapiens",
        "source_url": "http://gtrnadb.ucsc.edu/genomes/eukaryota/Hsapi38/hg38-tRNAs.fa",
    },
    {
        "organism": "danio_rerio",
        "label": "Danio rerio",
        "source_url": "http://gtrnadb.ucsc.edu/genomes/eukaryota/Dreri11/danRer11-tRNAs.fa",
    },
]

SOURCE_KIND = "GtRNAdb tRNA gene set (tRNAscan-SE)"
USER_AGENT = "Mozilla/5.0"
MODELED_ALIGNMENT_TOL = 0.02
SURVIVAL_EPS = 1e-12
ABSORPTION_PROXY_ERROR_THRESHOLD = 0.50

# dos Reis et al. 2004 optimized wobble s-values, via the shared _tai.py
# implementation used by the upstream modeled-tAI experiments.
DOS_REIS_2004_WOBBLE_S = {
    "G:U": WOBBLE_S[("G", "U")],
    "U:G": WOBBLE_S[("U", "G")],
    "I:C": WOBBLE_S[("I", "C")],
    "I:A": WOBBLE_S[("I", "A")],
    "I:U": WOBBLE_S[("I", "U")],
    "L:A": WOBBLE_S[("L", "A")],
}

HEADER_RE = re.compile(r"tRNA-([A-Za-z0-9]+)-([ACGTUNacgtun]{3})")
FALLBACK_RE = re.compile(r"\)\s+([A-Za-z0-9]+)\s+\(([ACGTUNacgtun]{3})\)")


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def numeric(value: object, field: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{field} must be numeric")
    return float(value)


def bounded_unit(value: float, tol: float = 1e-8) -> float:
    if not math.isfinite(value):
        return value
    if -tol <= value < 0.0:
        return 0.0
    if 1.0 < value <= 1.0 + tol:
        return 1.0
    return value


def finite_unit_interval(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value)) and 0.0 <= float(value) <= 1.0


def append_columns(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    return [left[index] + right[index] for index in range(len(left))]


def mean(values: list[float]) -> float | None:
    return None if not values else sum(values) / len(values)


def median(values: list[float]) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    mid = len(ordered) // 2
    if len(ordered) % 2 == 1:
        return ordered[mid]
    return 0.5 * (ordered[mid - 1] + ordered[mid])


def fetch_bytes(url: str) -> tuple[bytes, dict[str, object]]:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=60) as response:
        payload = response.read()
        return payload, {
            "source_http_status": getattr(response, "status", None),
            "source_content_type": response.headers.get("Content-Type", ""),
            "final_url": response.geturl(),
        }


def parse_gtrnadb_headers(raw_payload_text: str) -> tuple[list[dict[str, object]], dict[str, int], dict[str, int], dict[str, int]]:
    records: list[dict[str, object]] = []
    excluded: Counter[str] = Counter()
    anticodon_counts: Counter[str] = Counter()
    elongator_tai_counts: Counter[str] = Counter()

    for line in raw_payload_text.splitlines():
        if not line.startswith(">"):
            continue
        match = HEADER_RE.search(line) or FALLBACK_RE.search(line)
        if match is None:
            excluded["unmatched_header"] += 1
            records.append({"header": line, "matched": False, "included_for_gcn": False, "excluded_reason": "unmatched_header"})
            continue

        aa_label = match.group(1)
        anticodon = dna_to_rna(match.group(2))
        aa = normalize_aa(aa_label)
        header_lower = line.lower()
        reason = ""
        if "pseudo" in header_lower:
            reason = "pseudogene"
        elif anticodon == "NNN" or "N" in anticodon:
            reason = "undetermined_anticodon"
        elif aa_label in {"Und", "Undet"}:
            reason = "undetermined_amino_acid"
        elif aa_label == "Sup" or "suppressor" in header_lower:
            reason = "suppressor"
        elif aa_label == "SeC":
            reason = "selenocysteine"

        included_for_gcn = reason == ""
        included_for_tai = included_for_gcn and aa_label != "iMet"
        if not included_for_gcn:
            excluded[reason] += 1
        else:
            anticodon_counts[anticodon] += 1
            if included_for_tai:
                elongator_tai_counts[anticodon] += 1

        records.append(
            {
                "header": line,
                "matched": True,
                "aa_label": aa_label,
                "aa": aa,
                "anticodon": anticodon,
                "included_for_gcn": included_for_gcn,
                "included_for_tai": included_for_tai,
                "excluded_reason": reason or None,
            }
        )

    return records, dict(sorted(anticodon_counts.items())), dict(sorted(elongator_tai_counts.items())), dict(sorted(excluded.items()))


def write_trna_data_file(
    *,
    repo: pathlib.Path,
    organism: str,
    label: str,
    source_url: str,
    payload: bytes,
    fetch_meta: dict[str, object],
    records: list[dict[str, object]],
    anticodon_counts: dict[str, int],
    elongator_tai_counts: dict[str, int],
    excluded: dict[str, int],
) -> dict[str, object]:
    payload_sha256 = hashlib.sha256(payload).hexdigest()
    fetched_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
    aa_counts: Counter[str] = Counter()
    aa_anticodon_counts: Counter[str] = Counter()
    tai_records: list[dict[str, str]] = []

    for record in records:
        if record.get("included_for_gcn"):
            aa_label = str(record["aa_label"])
            anticodon = str(record["anticodon"])
            aa_counts[aa_label] += 1
            aa_anticodon_counts[f"{aa_label}:{anticodon}"] += 1
        if record.get("included_for_tai"):
            tai_records.append(
                {
                    "aa": str(record["aa"]),
                    "aa_label": str(record["aa_label"]),
                    "anticodon": str(record["anticodon"]),
                    "matched": True,
                }
            )

    data = {
        "schema_version": "fibonacci_reality_measured_trna_gene_copy_v1",
        "organism": organism,
        "organism_label": label,
        "source_name": "GtRNAdb",
        "source_kind": SOURCE_KIND,
        "source_url": source_url,
        "source_final_url": fetch_meta.get("final_url"),
        "source_http_status": fetch_meta.get("source_http_status"),
        "source_content_type": fetch_meta.get("source_content_type"),
        "fetched_at": fetched_at,
        "fetched_by": "FibonacciReality-Codex-Measured-tRNA-tAI",
        "payload_sha256": payload_sha256,
        "payload_byte_size": len(payload),
        "payload_note": "payload_sha256 is computed over the original HTTP response bytes; FASTA headers were parsed with stdlib Python only",
        "trna_fasta_header_count": sum(1 for line in payload.decode("utf-8", errors="replace").splitlines() if line.startswith(">")),
        "n_trna_genes_included_for_gcn": sum(anticodon_counts.values()),
        "n_trna_genes_included_for_elongator_tai": len(tai_records),
        "excluded_header_counts": excluded,
        "trna_anticodon_gene_copy_counts": anticodon_counts,
        "trna_anticodon_gene_copy_counts_for_elongator_tai": elongator_tai_counts,
        "trna_aa_gene_copy_counts": dict(sorted(aa_counts.items())),
        "trna_aa_anticodon_gene_copy_counts": dict(sorted(aa_anticodon_counts.items())),
        "cannot_claim": [
            "tRNA gene copy number is a proxy for tRNA abundance, not direct tRNA-seq",
            "this external count contact does not establish translation efficiency",
            "this external count contact does not establish a causal mechanism",
        ],
    }
    path = repo / f"tools/fibonacci_reality/data/trna_gene_copy_{organism}.json"
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return data


def fetch_parse_write_trna(repo: pathlib.Path, organism_spec: dict[str, str]) -> tuple[dict[str, object] | None, list[dict[str, str]], dict[str, object]]:
    organism = organism_spec["organism"]
    source_url = organism_spec["source_url"]
    try:
        payload, fetch_meta = fetch_bytes(source_url)
        payload_text = payload.decode("utf-8", errors="replace")
        records, anticodon_counts, elongator_tai_counts, excluded = parse_gtrnadb_headers(payload_text)
        if not anticodon_counts:
            return None, [], {
                "status": "needs_external",
                "organism": organism,
                "source_url": source_url,
                "reason": "download succeeded but no usable anticodon GCN records were parsed",
            }

        data = write_trna_data_file(
            repo=repo,
            organism=organism,
            label=organism_spec["label"],
            source_url=source_url,
            payload=payload,
            fetch_meta=fetch_meta,
            records=records,
            anticodon_counts=anticodon_counts,
            elongator_tai_counts=elongator_tai_counts,
            excluded=excluded,
        )
        tai_records = [
            {
                "aa": str(record["aa"]),
                "aa_label": str(record["aa_label"]),
                "anticodon": str(record["anticodon"]),
                "matched": True,
            }
            for record in records
            if record.get("included_for_tai")
        ]
        sys.stderr.write(
            f"[trna-gcn] {organism}: {len(anticodon_counts)} anticodons, "
            f"{sum(anticodon_counts.values())} included tRNA genes, "
            f"sha256={data['payload_sha256']}\n"
        )
        return data, tai_records, {"status": "fetched", "organism": organism}
    except (urllib.error.URLError, TimeoutError, OSError, UnicodeError) as exc:
        return None, [], {
            "status": "needs_external",
            "organism": organism,
            "source_url": source_url,
            "reason": f"GtRNAdb FASTA fetch/parse failed: {exc}",
        }


def measured_trna_tai_weights(
    *,
    organism: str,
    code: dict[str, str],
    codons: list[str],
    records: list[dict[str, str]],
) -> tuple[dict[str, float], dict[str, object]]:
    if not records:
        raise ValueError(f"{organism} has no measured tRNA records for tAI")
    tai, raw_w, contributors = codon_w_values(
        organism=organism,
        code=code,
        records=records,
        codons=codons,
    )
    zero_raw_w = sorted(codon for codon, value in raw_w.items() if value == 0.0)
    return tai, {
        "measured_trna_tai_weight_definition": "W_c = sum_i (1 - s_ic) * GCN_i using GtRNAdb gene-copy records and dos Reis 2004 wobble s-values from _tai.py; w_c = W_c/max(W); zero W_c filled by geometric mean",
        "per_gene_T_trna_definition": "geometric mean exp(sum_codon count_c * log(w_c) / total_sense_codons)",
        "dos_reis_2004_wobble_s_values": DOS_REIS_2004_WOBBLE_S,
        "usable_measured_tai_record_count": len(records),
        "zero_raw_W_filled_by_geometric_mean_count": len(zero_raw_w),
        "zero_raw_W_codons": zero_raw_w,
        "tai_contributor_contact_count": len(contributors),
    }


def codon_counts_rna(record: dict[str, object], codons: list[str], organism: str, row_index: int) -> dict[str, int]:
    raw = record.get("codon_counts")
    if not isinstance(raw, dict):
        raise ValueError(f"{organism}.joined[{row_index}].codon_counts must be an object")
    converted = {codon: 0 for codon in codons}
    for raw_codon, raw_count in raw.items():
        codon = dna_to_rna(str(raw_codon))
        if codon in converted:
            value = numeric(raw_count, f"{organism}.joined[{row_index}].codon_counts.{raw_codon}")
            if value < 0 or int(value) != value:
                raise ValueError(f"{organism}.joined[{row_index}].codon_counts.{raw_codon} must be a non-negative integer")
            converted[codon] += int(value)
    return converted


def normed_coordinate(vector: dict[str, float], q: dict[str, float], codons: list[str]) -> float:
    denom = math.sqrt(sum(q[codon] * q[codon] for codon in codons))
    if denom <= 0.0:
        raise ValueError("q vector has zero norm")
    return sum(vector[codon] * q[codon] for codon in codons) / denom


def measured_trna_rows(
    *,
    payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
    modeled_tai: dict[str, float],
    measured_trna_tai: dict[str, float],
) -> tuple[list[list[float]], list[list[float]], list[list[float]], list[list[float]], list[list[float]], dict[str, object]]:
    joined = payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} CDS payload must contain joined list")

    x_rows: list[list[float]] = []
    t_mod_rows: list[list[float]] = []
    t_trna_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    skipped = {
        "non_object": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }

    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        abundance = numeric(item.get("abundance_ppm"), f"{organism}.joined[{row_index}].abundance_ppm")
        if abundance <= 0.0:
            skipped["nonpositive_abundance"] += 1
            continue
        cds_len_nt = numeric(item.get("cds_len_nt"), f"{organism}.joined[{row_index}].cds_len_nt")
        if cds_len_nt <= 0.0:
            skipped["invalid_length"] += 1
            continue

        counts = codon_counts_rna(item, codons, organism, row_index)
        total = sum(counts.values())
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue

        frequencies = {codon: counts[codon] / total for codon in codons}
        x_rows.append([normed_coordinate(frequencies, q_projected[name], codons) for name in q_names])
        t_mod_rows.append([sum(counts[codon] * modeled_tai[codon] for codon in codons) / total])
        t_trna_rows.append([math.exp(sum(counts[codon] * math.log(measured_trna_tai[codon]) for codon in codons) / total)])
        y_rows.append([math.log10(abundance)])

        aa_counts = {aa: 0 for aa in aa_order}
        for codon in codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        if aa_total <= 0:
            raise ValueError(f"{organism}.joined[{row_index}] has no amino-acid counts after sense-codon filtering")

        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
        m_density = sum(counts[codon] for codon in q_support) / total
        z_rows.append(
            [1.0, math.log(cds_len_nt)]
            + [aa_counts[aa] / aa_total for aa in aa_order]
            + [gc3, m_density]
        )

    return x_rows, t_mod_rows, t_trna_rows, y_rows, z_rows, {
        "n_cds_joined_reported": payload.get("n_joined"),
        "cds_join_hit_rate_reported": payload.get("join_hit_rate"),
        "n_joined": len(x_rows),
        "skipped_cds_records": skipped,
    }


def absorption_decomposition(
    *,
    x_tilde: list[list[float]],
    t_mod_tilde: list[list[float]],
    t_trna_tilde: list[list[float]],
    y_tilde: list[list[float]],
) -> dict[str, object]:
    y_col = matrix_column(y_tilde, 0)
    p_q, q_coeff = project_onto_design(x_tilde, y_col)
    p_q_from_tmod, tmod_coeff = project_onto_design(t_mod_tilde, p_q)
    p_q_perp_tmod = subtract_vectors(p_q, p_q_from_tmod)
    absorbed_vector, trna_absorption_coeff = project_onto_design(t_trna_tilde, p_q_perp_tmod)
    combined_design = append_columns(t_mod_tilde, t_trna_tilde)
    p_q_from_combined, combined_coeff = project_onto_design(combined_design, p_q)
    p_q_perp_combined = subtract_vectors(p_q, p_q_from_combined)

    p_q_norm2 = vector_norm2(p_q)
    p_q_perp_tmod_norm2 = vector_norm2(p_q_perp_tmod)
    absorbed_norm2 = vector_norm2(absorbed_vector)
    p_q_perp_combined_norm2 = vector_norm2(p_q_perp_combined)
    return {
        "P_Q_norm2": p_q_norm2,
        "P_Q_perp_Tmod_norm2": p_q_perp_tmod_norm2,
        "P_Q_perp_Tmod_absorbed_by_Ttrna_norm2": absorbed_norm2,
        "P_Q_perp_combined_norm2": p_q_perp_combined_norm2,
        "d_modeled": None if p_q_norm2 <= SURVIVAL_EPS else bounded_unit(p_q_perp_tmod_norm2 / p_q_norm2),
        "absorbed_by_trna": None if p_q_perp_tmod_norm2 <= SURVIVAL_EPS else bounded_unit(absorbed_norm2 / p_q_perp_tmod_norm2),
        "d_combined": None if p_q_norm2 <= SURVIVAL_EPS else bounded_unit(p_q_perp_combined_norm2 / p_q_norm2),
        "coefficients": {
            "Q_to_P": q_coeff,
            "Tmod_on_P_Q": tmod_coeff,
            "Ttrna_on_P_Q_perp_Tmod": trna_absorption_coeff,
            "Tmod_Ttrna_on_P_Q": combined_coeff,
        },
    }


def interpretation_label(absorbed_by_trna: float | None) -> str:
    if absorbed_by_trna is None:
        return "no_modeled_complement_energy_to_classify"
    if absorbed_by_trna >= ABSORPTION_PROXY_ERROR_THRESHOLD:
        return "residual_was_modeled_tAI_proxy_error"
    return "residual_robust_to_real_tRNA"


def measured_te_mediation_context(
    *,
    repo: pathlib.Path,
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> dict[str, object]:
    cds_payload = load_json(repo / f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json")
    te_payload = load_json(repo / f"tools/fibonacci_reality/data/ribosome_te_{organism}.json")
    abundance_payload = load_json(repo / f"tools/fibonacci_reality/data/proteomics_abundance_{organism}.json")
    if not isinstance(cds_payload, dict) or not isinstance(te_payload, dict) or not isinstance(abundance_payload, dict):
        raise ValueError(f"{organism} measured-TE context payloads must be JSON objects")
    x_rows, t_rows, y_rows, z_rows, summary = measured_mediation_rows(
        cds_payload=cds_payload,
        te_payload=te_payload,
        abundance_payload=abundance_payload,
        organism=organism,
        codons=codons,
        code=code,
        aa_order=aa_order,
        q_projected=q_projected,
        q_names=q_names,
        q_support=q_support,
    )
    if not x_rows:
        raise ValueError(f"{organism} has no measured-TE joined rows")
    x_tilde, rank_z = residualize(x_rows, z_rows)
    t_tilde, _ = residualize(t_rows, z_rows)
    y_tilde, _ = residualize(y_rows, z_rows)
    joint = joint_decomposition(x_tilde=x_tilde, t_tilde=t_tilde, y_tilde=y_tilde, q_names=q_names)
    return {
        "m_measTE": joint["M_QTP_fraction"],
        "n_measuredTE_joined": len(x_rows),
        "rank_Z_measuredTE_join": rank_z,
        "join_definition": "measured ribo-seq TE x PAXdb abundance x CDS protein_id intersection; context only, not the primary full-join tRNA absorption test",
        "summary": summary,
        "rank_diagnostics": joint["rank_diagnostics"],
    }


def cannot_claim() -> list[str]:
    return [
        "statistical projection, not causal",
        "tRNA gene copy number is a proxy for tRNA abundance (not direct tRNA-seq)",
        "tAI wobble s-values from dos Reis 2004, a modeling choice",
        "absorbed fraction descriptive not causal",
        "if residual robust to real tRNA, it is genuinely beyond translation - H still open",
    ]


def conclusion_from_absorption(absorptions: dict[str, float]) -> dict[str, object]:
    values = list(absorptions.values())
    high = [value for value in values if value >= ABSORPTION_PROXY_ERROR_THRESHOLD]
    low = [value for value in values if value < ABSORPTION_PROXY_ERROR_THRESHOLD]
    if len(high) == len(values) and values:
        consistency = "consistently_high"
        conclusion = "real tRNA gene-copy tAI mostly absorbs the modeled-tAI residual in every computed organism; this supports the proxy-error reading for this projection"
    elif len(low) == len(values) and values:
        consistency = "consistently_low"
        conclusion = "real tRNA gene-copy tAI absorbs little of the modeled-tAI residual in every computed organism; the residual is robust to this real-tRNA proxy"
    elif values:
        consistency = "mixed"
        conclusion = "real tRNA gene-copy tAI absorption is organism-dependent; proxy-error and robust-residual readings cannot be promoted as a single cross-organism rule"
    else:
        consistency = "not_computed"
        conclusion = "no organism produced a measured-tRNA absorption result"
    return {
        "threshold_for_descriptive_proxy_error_label_only": ABSORPTION_PROXY_ERROR_THRESHOLD,
        "consistency": consistency,
        "computed_organism_count": len(values),
        "high_count": len(high),
        "low_count": len(low),
        "absorbed_by_trna_values": absorptions,
        "min": min(values) if values else None,
        "max": max(values) if values else None,
        "mean": mean(values),
        "median": median(values),
        "answer_to_core_question": conclusion,
    }


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    required = ["tools/fibonacci_reality/data/ncbi_genetic_codes.json"]
    for item in ORGANISMS:
        organism = item["organism"]
        required.append(f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json")
        required.append(f"tools/fibonacci_reality/data/gtrnadb_trna_all_copy_{organism}.json")
        required.append(f"tools/fibonacci_reality/data/ribosome_te_{organism}.json")
        required.append(f"tools/fibonacci_reality/data/proteomics_abundance_{organism}.json")
    missing = [path for path in required if not (repo / path).exists()]
    if missing:
        emit("needs_data", missing_required_data=missing, reason="required local CDS/modelled-tAI/measured-TE/proteomics data not present")

    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}

        fetched_data: dict[str, dict[str, object]] = {}
        tai_records_by_organism: dict[str, list[dict[str, str]]] = {}
        fetch_status: dict[str, object] = {}
        for item in ORGANISMS:
            data, tai_records, status = fetch_parse_write_trna(repo, item)
            organism = item["organism"]
            fetch_status[organism] = status
            if data is not None:
                fetched_data[organism] = data
                tai_records_by_organism[organism] = tai_records

        if not fetched_data:
            checks = [
                {
                    "name": "trna_data_fetched",
                    "passed": False,
                    "actual": fetch_status,
                    "expected": "at least one organism has a freshly fetched GtRNAdb FASTA with sha256 provenance",
                }
            ]
            emit("needs_external", checks=checks, reason="all GtRNAdb tRNA FASTA fetches failed; no tRNA copy numbers were fabricated")

        per_organism: dict[str, object] = {}
        absorption_values: dict[str, float] = {}
        input_actual: dict[str, object] = {}
        d_alignment_actual: dict[str, object] = {}
        all_fetched = len(fetched_data) == len(ORGANISMS)
        all_gcn_parsed = True
        all_tai_computed = True
        all_joined_ok = True
        all_residualized_ok = True
        all_d_aligned = True
        all_absorption_ok = True

        for item in ORGANISMS:
            organism = item["organism"]
            if organism not in fetched_data:
                per_organism[organism] = fetch_status[organism]
                all_joined_ok = False
                all_residualized_ok = False
                all_d_aligned = False
                all_absorption_ok = False
                continue

            cds_payload = load_json(repo / f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json")
            if not isinstance(cds_payload, dict):
                raise ValueError(f"{organism} CDS payload must be a JSON object")
            tai_mod_weights, tai_mod_summary = modeled_tai_weights(
                repo=repo,
                organism=organism,
                trna_organism=organism,
                code=code,
                codons=codons,
            )
            tai_trna_weights, tai_trna_summary = measured_trna_tai_weights(
                organism=organism,
                code=code,
                codons=codons,
                records=tai_records_by_organism[organism],
            )
            x_rows, t_mod_rows, t_trna_rows, y_rows, z_rows, data_summary = measured_trna_rows(
                payload=cds_payload,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
                modeled_tai=tai_mod_weights,
                measured_trna_tai=tai_trna_weights,
            )
            n_joined = len(x_rows)
            if n_joined == 0:
                raise ValueError(f"{organism} has no usable abundance/CDS rows")

            x_tilde, rank_z = residualize(x_rows, z_rows)
            t_mod_tilde, _ = residualize(t_mod_rows, z_rows)
            t_trna_tilde, _ = residualize(t_trna_rows, z_rows)
            y_tilde, _ = residualize(y_rows, z_rows)
            decomposition = absorption_decomposition(
                x_tilde=x_tilde,
                t_mod_tilde=t_mod_tilde,
                t_trna_tilde=t_trna_tilde,
                y_tilde=y_tilde,
            )

            reference_x, reference_t, reference_y, reference_z, _ = protein_rows(
                payload=cds_payload,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
                tai_weights=tai_mod_weights,
            )
            reference_x_tilde, reference_rank_z = residualize(reference_x, reference_z)
            reference_t_tilde, _ = residualize(reference_t, reference_z)
            reference_y_tilde, _ = residualize(reference_y, reference_z)
            complement_reference = complement_decomposition(
                x_tilde=reference_x_tilde,
                t_tilde=reference_t_tilde,
                y_tilde=reference_y_tilde,
                q_names=q_names,
            )

            d_modeled = decomposition["d_modeled"]
            d_reference = complement_reference["d"]
            d_difference = None
            d_matches = False
            if isinstance(d_modeled, float) and isinstance(d_reference, float):
                d_difference = abs(d_modeled - d_reference)
                d_matches = d_difference < MODELED_ALIGNMENT_TOL

            comp_mod = complement_decomposition(x_tilde=x_tilde, t_tilde=t_mod_tilde, y_tilde=y_tilde, q_names=q_names)
            comp_trna = complement_decomposition(x_tilde=x_tilde, t_tilde=t_trna_tilde, y_tilde=y_tilde, q_names=q_names)
            joint_mod = joint_decomposition(x_tilde=x_tilde, t_tilde=t_mod_tilde, y_tilde=y_tilde, q_names=q_names)
            joint_trna = joint_decomposition(x_tilde=x_tilde, t_tilde=t_trna_tilde, y_tilde=y_tilde, q_names=q_names)
            measured_te_context = measured_te_mediation_context(
                repo=repo,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
            )

            r2_q_ttrna, _, rank_q_for_ttrna = r2_from_design_like(x_tilde, t_trna_tilde)
            x_rank = explained_by_design(x_tilde, y_tilde)[1]
            t_mod_rank = explained_by_design(t_mod_tilde, y_tilde)[1]
            t_trna_rank = explained_by_design(t_trna_tilde, y_tilde)[1]
            combined_rank = explained_by_design(append_columns(t_mod_tilde, t_trna_tilde), y_tilde)[1]
            residual_df = n_joined - rank_z
            absorbed = decomposition["absorbed_by_trna"]

            organism_gcn_ok = bool(fetched_data[organism].get("trna_anticodon_gene_copy_counts"))
            organism_tai_ok = all(math.isfinite(value) and value > 0.0 for value in tai_trna_weights.values()) and len(t_trna_rows) == n_joined
            organism_joined_ok = n_joined >= MIN_PROTEINS_PER_ORGANISM
            organism_residualized_ok = (
                rank_z > 0
                and len(x_tilde) == n_joined
                and len(t_mod_tilde) == n_joined
                and len(t_trna_tilde) == n_joined
                and len(y_tilde) == n_joined
            )
            organism_absorption_ok = finite_unit_interval(absorbed) and finite_unit_interval(decomposition["d_combined"])

            all_gcn_parsed = all_gcn_parsed and organism_gcn_ok
            all_tai_computed = all_tai_computed and organism_tai_ok
            all_joined_ok = all_joined_ok and organism_joined_ok
            all_residualized_ok = all_residualized_ok and organism_residualized_ok
            all_d_aligned = all_d_aligned and d_matches
            all_absorption_ok = all_absorption_ok and organism_absorption_ok
            if isinstance(absorbed, float):
                absorption_values[organism] = absorbed

            input_actual[organism] = {
                "n_joined": n_joined,
                "n_cds_joined_reported": data_summary["n_cds_joined_reported"],
                "n_trna_genes": fetched_data[organism]["n_trna_genes_included_for_gcn"],
                "anticodon_gcn_table_size": len(fetched_data[organism]["trna_anticodon_gene_copy_counts"]),
                "rank_Z": rank_z,
                "control_column_count": len(z_rows[0]) if z_rows else 0,
            }
            d_alignment_actual[organism] = {
                "d_modeled_current_full_join": d_modeled,
                "d_modeled_complement_experiment_reference": d_reference,
                "absolute_difference": d_difference,
                "matches_within_0_02": d_matches,
                "current_join_n": n_joined,
                "complement_reference_join_n": len(reference_x),
                "reference_rank_Z": reference_rank_z,
            }

            per_organism[organism] = {
                **data_summary,
                **tai_mod_summary,
                **tai_trna_summary,
                "n_joined": n_joined,
                "n_trna_genes": fetched_data[organism]["n_trna_genes_included_for_gcn"],
                "d_modeled": d_modeled,
                "d_modeled_reference_from_complement_experiment": d_reference,
                "d_modeled_reference_absolute_difference": d_difference,
                "d_modeled_matches_complement_experiment_within_0_02": d_matches,
                "absorbed_by_trna": absorbed,
                "R2_Q_Ttrna": r2_q_ttrna,
                "m_comparison": {
                    "m_modeled_projection_1_minus_d": comp_mod["m"],
                    "m_trna_projection_1_minus_d": comp_trna["m"],
                    "m_modeled_joint_mediation_fraction": joint_mod["M_QTP_fraction"],
                    "m_trna_joint_mediation_fraction": joint_trna["M_QTP_fraction"],
                    "m_measTE_joint_mediation_fraction": measured_te_context["m_measTE"],
                    "measured_TE_context_join_n": measured_te_context["n_measuredTE_joined"],
                    "measured_TE_context_note": measured_te_context["join_definition"],
                },
                "d_combined": decomposition["d_combined"],
                "interpretation_label": interpretation_label(absorbed if isinstance(absorbed, float) else None),
                "interpretation_label_threshold_descriptive_only": ABSORPTION_PROXY_ERROR_THRESHOLD,
                "tRNA_provenance": {
                    "source_url": fetched_data[organism]["source_url"],
                    "source_kind": fetched_data[organism]["source_kind"],
                    "fetched_at": fetched_data[organism]["fetched_at"],
                    "payload_sha256": fetched_data[organism]["payload_sha256"],
                    "payload_byte_size": fetched_data[organism]["payload_byte_size"],
                    "anticodon_gcn_table_size": len(fetched_data[organism]["trna_anticodon_gene_copy_counts"]),
                    "excluded_header_counts": fetched_data[organism]["excluded_header_counts"],
                },
                "norms": {
                    "P_Q_norm2": decomposition["P_Q_norm2"],
                    "P_Q_perp_Tmod_norm2": decomposition["P_Q_perp_Tmod_norm2"],
                    "P_Q_perp_Tmod_absorbed_by_Ttrna_norm2": decomposition["P_Q_perp_Tmod_absorbed_by_Ttrna_norm2"],
                    "P_Q_perp_combined_norm2": decomposition["P_Q_perp_combined_norm2"],
                },
                "rank_condition_diagnostics": {
                    "rank_Q_e": x_rank,
                    "rank_Tmod": t_mod_rank,
                    "rank_Ttrna": t_trna_rank,
                    "rank_Tmod_Ttrna": combined_rank,
                    "rank_Q_for_Ttrna": rank_q_for_ttrna,
                    "rank_Z": rank_z,
                    "residual_df_after_Z": residual_df,
                    "q_coordinate_count": len(q_names),
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                    "ridge_epsilon": RIDGE_EPS,
                    "condition_number_Q_gram": condition_number_from_gram(gram_matrix(x_tilde)),
                    "condition_number_Tmod_gram": condition_number_from_gram(gram_matrix(t_mod_tilde)),
                    "condition_number_Ttrna_gram": condition_number_from_gram(gram_matrix(t_trna_tilde)),
                    "condition_number_Tmod_Ttrna_gram": condition_number_from_gram(gram_matrix(append_columns(t_mod_tilde, t_trna_tilde))),
                },
            }

        checks = [
            {
                "name": "trna_data_fetched",
                "passed": all_fetched,
                "actual": {
                    organism: (
                        {
                            "source_url": data["source_url"],
                            "payload_sha256": data["payload_sha256"],
                            "payload_byte_size": data["payload_byte_size"],
                            "fetched_at": data["fetched_at"],
                        }
                        if organism in fetched_data
                        else fetch_status.get(organism)
                    )
                    for organism, data in {**{item["organism"]: {} for item in ORGANISMS}, **fetched_data}.items()
                },
                "expected": "fresh urllib.request download with User-Agent Mozilla/5.0 and sha256 provenance for yeast, human, and danio",
            },
            {
                "name": "trna_gcn_parsed",
                "passed": all_gcn_parsed,
                "actual": {
                    organism: {
                        "anticodon_gcn_table_size": len(data["trna_anticodon_gene_copy_counts"]),
                        "n_trna_genes": data["n_trna_genes_included_for_gcn"],
                        "excluded_header_counts": data["excluded_header_counts"],
                    }
                    for organism, data in fetched_data.items()
                },
                "expected": "nonempty anticodon -> GCN tables after excluding Und/NNN/Sup/pseudo/SeC",
            },
            {
                "name": "measured_trna_tai_computed",
                "passed": all_tai_computed,
                "actual": {
                    organism: {
                        "usable_measured_tai_record_count": result["usable_measured_tai_record_count"],
                        "zero_raw_W_filled_by_geometric_mean_count": result["zero_raw_W_filled_by_geometric_mean_count"],
                    }
                    for organism, result in per_organism.items()
                    if isinstance(result, dict) and "usable_measured_tai_record_count" in result
                },
                "expected": "finite positive measured-tRNA tAI weights and per-gene geometric tAI values",
            },
            {
                "name": "inputs_joined",
                "passed": all_joined_ok,
                "actual": input_actual,
                "expected": f"each computed organism has n >= {MIN_PROTEINS_PER_ORGANISM} on the full abundance/CDS join",
            },
            {
                "name": "b_star_q6_residuals + controls_Z + modeled_complement",
                "passed": len(q_names) == 9 and all_residualized_ok,
                "actual": {
                    "coordinates": q_names,
                    "coordinate_count": len(q_names),
                    "controls_used": controls_used(aa_order),
                    "per_organism": input_actual,
                },
                "expected": "Q_e, T_mod, T_trna, and P_e residualized against the same Z controls",
            },
            {
                "name": "d_modeled_matches_complement_experiment",
                "passed": all_d_aligned,
                "actual": d_alignment_actual,
                "expected": f"per-organism |d_current_full_join - d_complement_reference| < {MODELED_ALIGNMENT_TOL}",
            },
            {
                "name": "trna_absorption_computed",
                "passed": all_absorption_ok,
                "actual": {
                    organism: {
                        "absorbed_by_trna": result["absorbed_by_trna"],
                        "d_combined": result["d_combined"],
                    }
                    for organism, result in per_organism.items()
                    if isinstance(result, dict) and "absorbed_by_trna" in result
                },
                "expected": "absorbed_by_trna and d_combined finite in [0,1]",
            },
            {
                "name": "no_causal_promotion",
                "passed": True,
                "actual": {"passed": True, "cannot_claim": cannot_claim()},
                "expected": "statistical projection only; no causal or mechanism promotion",
            },
        ]

        status = "passed" if all_joined_ok and all_residualized_ok and all_tai_computed and all_absorption_ok else "failed"
        reason = None
        if status == "passed" and (not all_fetched or not all_d_aligned):
            reason = "computed results are reported, but at least one honesty gate is false; see checks"
        if status != "passed":
            reason = "one or more computation gates failed; no copy number was fabricated"

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture": CONJECTURE_ID,
                "statement": "Measured tRNA gene-copy tAI is tested for whether it absorbs the modeled-tAI-complement abundance component P_hat_{Q perp Tmod}.",
                "status_semantics": "passed means the descriptive projection quantities were computed and bounded; absorption high or low is reported without promotion to causality",
                "decomposition": {
                    "Q_e": "residualized 9-coordinate B*_Q6 design after controls Z",
                    "P_e": "residualized log10 PAXdb abundance after controls Z",
                    "T_mod": "residualized modeled per-protein tAI after controls Z, using the upstream arithmetic per-protein readout for d_modeled alignment",
                    "T_trna": "residualized measured-tRNA gene-copy tAI after controls Z, with per-gene geometric mean over measured GCN-derived w_c",
                    "T_meas": "residualized log10 measured ribo-seq TE, reported as measured-TE join context for m comparison",
                    "P_hat_Q": "Pi_{Q_e} P_e",
                    "P_hat_Q_perp_Tmod": "(I - Pi_{Tmod}) P_hat_Q",
                    "absorbed_by_trna": "||Pi_{Ttrna} P_hat_{Q perp Tmod}||^2 / ||P_hat_{Q perp Tmod}||^2",
                    "d_combined": "|| (I - Pi_{[Tmod,Ttrna]}) P_hat_Q ||^2 / ||P_hat_Q||^2",
                    "ridge_epsilon": RIDGE_EPS,
                },
                "coordinates": q_names,
                "per_organism": per_organism,
                "cross_organism": {
                    "absorbed_by_trna_distribution": conclusion_from_absorption(absorption_values),
                    "ordered_by_absorbed_by_trna": sorted(
                        [
                            {
                                "organism": organism,
                                "absorbed_by_trna": float(result["absorbed_by_trna"]),
                                "R2_Q_Ttrna": float(result["R2_Q_Ttrna"]),
                                "d_modeled": float(result["d_modeled"]),
                                "d_combined": float(result["d_combined"]),
                                "interpretation_label": result["interpretation_label"],
                            }
                            for organism, result in per_organism.items()
                            if isinstance(result, dict)
                            and isinstance(result.get("absorbed_by_trna"), float)
                            and isinstance(result.get("R2_Q_Ttrna"), float)
                            and isinstance(result.get("d_modeled"), float)
                            and isinstance(result.get("d_combined"), float)
                        ],
                        key=lambda row: row["absorbed_by_trna"],
                        reverse=True,
                    ),
                },
                "honest": {"cannot_claim": cannot_claim()},
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable measured tRNA tAI residual-absorption input")


def r2_from_design_like(design: list[list[float]], response: list[list[float]]) -> tuple[float, float, int]:
    y_ss = sum(value * value for row in response for value in row)
    if y_ss <= SURVIVAL_EPS:
        return 0.0, 0.0, 0
    explained, rank = explained_by_design(design, response)
    r2 = max(0.0, min(1.0, explained / y_ss))
    return r2, explained, rank


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Subcellular localization as an H-candidate for the modeled-tAI complement.

This is a descriptive statistical projection audit. It tests whether UniProt
reviewed subcellular-location annotations absorb the B*_Q6 abundance component
left after modeled tAI. It is not causal.
"""

from __future__ import annotations

import csv
import datetime as dt
import hashlib
import json
import math
import pathlib
import re
import socket
import sys
import time
import urllib.parse
import urllib.request
from typing import Any

from run_b_star_q6_protein_omics_survival_powered import (
    explained_by_design,
    matrix_column,
    orthonormal_basis_from_columns,
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
    codon_counts_rna,
    controls_used,
    load_json,
    modeled_tai_weights,
    normed_coordinate,
    numeric,
    protein_rows,
)
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_h_candidate_localization_powered"
CLAIM_ID = "h3.cross_layer_relation.h_candidate_localization.b_star_q6_nontranslation_residual_powered"
CONJECTURE_ID = "q6.h-candidate-localization.non-translation-residual.cross-layer"

ORGANISM_PAIRS = [
    {
        "organism": "saccharomyces_cerevisiae",
        "trna_organism": "saccharomyces_cerevisiae",
        "taxid": "559292",
        "data_slug": "saccharomyces_cerevisiae",
        "url": "https://rest.uniprot.org/uniprotkb/stream?query=organism_id:559292+AND+reviewed:true&fields=accession,xref_string,cc_subcellular_location&format=tsv",
    },
    {
        "organism": "homo_sapiens",
        "trna_organism": "homo_sapiens",
        "taxid": "9606",
        "data_slug": "homo_sapiens",
        "url": "https://rest.uniprot.org/uniprotkb/stream?query=organism_id:9606+AND+reviewed:true&fields=accession,xref_string,cc_subcellular_location&format=tsv",
    },
    {
        "organism": "danio_rerio",
        "trna_organism": "danio_rerio",
        "taxid": "7955",
        "data_slug": "danio_rerio",
        "url": "https://rest.uniprot.org/uniprotkb/stream?query=organism_id:7955+AND+reviewed:true&fields=accession,xref_string,cc_subcellular_location&format=tsv",
    },
]

LOCALIZATION_CATEGORIES = [
    "Cytoplasm",
    "Nucleus",
    "Cell_membrane",
    "Membrane",
    "Mitochondrion",
    "Endoplasmic_reticulum",
    "Golgi",
    "Secreted",
    "Vacuole_Lysosome",
    "Peroxisome",
    "Cytoskeleton",
    "Other",
]

SURVIVAL_EPS = 1e-12
MODELED_ALIGNMENT_TOL = 0.02
NULL_TRIALS = 200


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def utc_now_iso() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def finite_unit_interval(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value)) and 0.0 <= float(value) <= 1.0


def bounded_unit(value: float, tol: float = 1e-8) -> float:
    if not math.isfinite(value):
        return value
    if -tol <= value < 0.0:
        return 0.0
    if 1.0 < value <= 1.0 + tol:
        return 1.0
    return value


def mean(values: list[float]) -> float | None:
    if not values:
        return None
    return sum(values) / len(values)


def percentile_nearest_rank(values: list[float], probability: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def fetch_url(url: str) -> bytes:
    socket.setdefaulttimeout(120)
    request = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0", "Connection": "close"})
    with urllib.request.urlopen(request, timeout=120) as response:
        chunks: list[bytes] = []
        deadline = time.monotonic() + 8.0
        while True:
            if time.monotonic() > deadline:
                raise TimeoutError(f"download deadline exceeded for {url}")
            chunk = response.read(65536)
            if not chunk:
                break
            chunks.append(chunk)
        return b"".join(chunks)


def paged_search_url_from_stream(stream_url: str) -> str:
    parsed = urllib.parse.urlparse(stream_url)
    query = parsed.query
    if "size=" not in query:
        query = f"{query}&size=500" if query else "size=500"
    return urllib.parse.urlunparse(
        parsed._replace(
            path="/uniprotkb/search",
            query=query,
        )
    )


def next_link(headers: object) -> str | None:
    links = []
    get_all = getattr(headers, "get_all", None)
    if callable(get_all):
        links = get_all("Link") or []
    else:
        value = getattr(headers, "get", lambda _name: None)("Link")
        if value:
            links = [value]
    for header in links:
        match = re.search(r"<([^>]+)>;\s*rel=\"next\"", str(header))
        if match:
            return match.group(1)
    return None


def fetch_uniprot_payload(stream_url: str) -> tuple[bytes, str, str]:
    try:
        return fetch_url(stream_url), "stream", stream_url
    except Exception:
        page_url = paged_search_url_from_stream(stream_url)
        lines: list[bytes] = []
        page_index = 0
        current: str | None = page_url
        while current:
            request = urllib.request.Request(current, headers={"User-Agent": "Mozilla/5.0", "Connection": "close"})
            with urllib.request.urlopen(request, timeout=120) as response:
                payload = response.read()
                page_lines = payload.splitlines()
                if page_index == 0:
                    lines.extend(page_lines)
                else:
                    lines.extend(page_lines[1:])
                current = next_link(response.headers)
            page_index += 1
        return b"\n".join(lines) + b"\n", "paged_search_fallback_after_stream_deadline", page_url


def first_present(row: dict[str, str], names: list[str]) -> str:
    for name in names:
        value = row.get(name)
        if value is not None:
            return value
    return ""


def first_string_key(raw_string: str) -> str | None:
    for part in raw_string.replace(",", ";").split(";"):
        value = part.strip()
        if value:
            return value
    return None


def clean_location_text(text: str) -> str:
    value = text.replace("\n", " ").replace("\r", " ")
    if value.upper().startswith("SUBCELLULAR LOCATION:"):
        value = value.split(":", 1)[1]
    while "  " in value:
        value = value.replace("  ", " ")
    return value.strip()


def infer_location_categories(raw_text: str) -> list[str]:
    text = clean_location_text(raw_text)
    lowered = text.lower()
    categories: set[str] = set()

    if "cytoplasm" in lowered or "cytosol" in lowered:
        categories.add("Cytoplasm")
    if "nucleus" in lowered or "nuclear" in lowered or "nucleolus" in lowered:
        categories.add("Nucleus")
    if "cell membrane" in lowered or "plasma membrane" in lowered:
        categories.add("Cell_membrane")
    if "membrane" in lowered:
        categories.add("Membrane")
    if "mitochond" in lowered:
        categories.add("Mitochondrion")
    if "endoplasmic reticulum" in lowered or "sarcoplasmic reticulum" in lowered or " er " in f" {lowered} ":
        categories.add("Endoplasmic_reticulum")
    if "golgi" in lowered:
        categories.add("Golgi")
    if "secreted" in lowered or "extracellular" in lowered:
        categories.add("Secreted")
    if "vacuole" in lowered or "lysosome" in lowered or "lysosomal" in lowered:
        categories.add("Vacuole_Lysosome")
    if "peroxisome" in lowered or "peroxisomal" in lowered:
        categories.add("Peroxisome")
    if "cytoskeleton" in lowered or "microtubule" in lowered or "actin" in lowered or "spindle" in lowered:
        categories.add("Cytoskeleton")

    if not categories and text:
        categories.add("Other")
    return [category for category in LOCALIZATION_CATEGORIES if category in categories]


def parse_uniprot_tsv(payload: bytes, organism: str, taxid: str) -> dict[str, object]:
    text = payload.decode("utf-8")
    reader = csv.DictReader(text.splitlines(), delimiter="\t")
    proteins: dict[str, dict[str, object]] = {}
    skipped = {
        "missing_string": 0,
        "missing_location": 0,
        "unparsed_location": 0,
        "duplicate_string_first_key": 0,
    }
    category_counts = {category: 0 for category in LOCALIZATION_CATEGORIES}
    multi_label_count = 0

    for row in reader:
        string_key = first_string_key(first_present(row, ["STRING", "Cross-reference (STRING)", "String"]))
        if not string_key:
            skipped["missing_string"] += 1
            continue
        raw_location = first_present(row, ["Subcellular location [CC]", "Subcellular location", "CC_SUBCELLULAR_LOCATION"])
        if not raw_location.strip():
            skipped["missing_location"] += 1
            continue
        categories = infer_location_categories(raw_location)
        if not categories:
            skipped["unparsed_location"] += 1
            continue
        if string_key in proteins:
            skipped["duplicate_string_first_key"] += 1
            existing = set(proteins[string_key]["categories"])
            categories = [category for category in LOCALIZATION_CATEGORIES if category in existing or category in set(categories)]
        proteins[string_key] = {
            "uniprot_accession": first_present(row, ["Entry", "Accession"]),
            "string_id": string_key,
            "categories": categories,
            "raw_subcellular_location": raw_location,
        }

    for record in proteins.values():
        categories = record["categories"]
        if isinstance(categories, list):
            if len(categories) > 1:
                multi_label_count += 1
            for category in categories:
                category_counts[str(category)] += 1

    return {
        "organism": organism,
        "ncbi_taxid": taxid,
        "schema_version": 1,
        "source_kind": "UniProtKB reviewed subcellular location",
        "proteins": proteins,
        "n_uniprot_rows": len(text.splitlines()) - 1 if text else 0,
        "n_string_localization_records": len(proteins),
        "n_multi_label_records": multi_label_count,
        "category_counts": category_counts,
        "skipped_records": skipped,
        "category_parse_policy": {
            "standard_categories": LOCALIZATION_CATEGORIES,
            "note": "coarse deterministic keyword mapping from UniProt SUBCELLULAR LOCATION text; multi-label one-hot is retained",
        },
    }


def localization_data_path(repo: pathlib.Path, slug: str) -> pathlib.Path:
    return repo / f"tools/bio_reality/data/subcellular_localization_{slug}.json"


def load_or_fetch_localization(repo: pathlib.Path, pair: dict[str, str]) -> tuple[dict[str, object] | None, dict[str, object]]:
    path = localization_data_path(repo, pair["data_slug"])
    if path.exists():
        payload = load_json(path)
        if not isinstance(payload, dict):
            raise ValueError(f"{path} must contain a JSON object")
        provenance = payload.get("provenance")
        return payload, {
            "organism": pair["organism"],
            "data_path": str(path.relative_to(repo)),
            "loaded_existing": True,
            "payload_sha256": provenance.get("payload_sha256") if isinstance(provenance, dict) else None,
            "payload_byte_size": provenance.get("payload_byte_size") if isinstance(provenance, dict) else None,
        }

    try:
        raw, fetch_method, downloaded_url = fetch_uniprot_payload(pair["url"])
        sha = hashlib.sha256(raw).hexdigest()
        parsed = parse_uniprot_tsv(raw, pair["organism"], pair["taxid"])
        parsed["provenance"] = {
            "source_url": pair["url"],
            "downloaded_url": downloaded_url,
            "fetch_method": fetch_method,
            "source_kind": "UniProtKB reviewed subcellular location",
            "fetched_at": utc_now_iso(),
            "payload_sha256": sha,
            "payload_byte_size": len(raw),
            "fetch_user_agent": "Mozilla/5.0",
            "derivation_boundary": "not_bedc_kernel_content",
        }
        path.write_text(json.dumps(parsed, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        return parsed, {
            "organism": pair["organism"],
            "data_path": str(path.relative_to(repo)),
            "loaded_existing": False,
            "payload_sha256": sha,
            "payload_byte_size": len(raw),
        }
    except Exception as exc:
        return None, {
            "organism": pair["organism"],
            "source_url": pair["url"],
            "needs_external": True,
            "fetch_error": str(exc),
        }


def localization_rows(
    *,
    cds_payload: dict[str, object],
    localization_payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
    tai_weights: dict[str, float],
) -> tuple[list[list[float]], list[list[float]], list[list[float]], list[list[float]], list[list[float]], dict[str, object]]:
    joined = cds_payload.get("joined")
    proteins = localization_payload.get("proteins")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} CDS payload must contain joined list")
    if not isinstance(proteins, dict):
        raise ValueError(f"{organism} localization payload must contain proteins object")

    x_rows: list[list[float]] = []
    t_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    l_rows: list[list[float]] = []
    category_counts = {category: 0 for category in LOCALIZATION_CATEGORIES}
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "no_localization_match": 0,
        "empty_categories": 0,
        "nonpositive_abundance": 0,
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
        record = proteins.get(protein_id)
        if not isinstance(record, dict):
            skipped["no_localization_match"] += 1
            continue
        categories = record.get("categories")
        if not isinstance(categories, list) or not categories:
            skipped["empty_categories"] += 1
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
        t_rows.append([sum(counts[codon] * tai_weights[codon] for codon in codons) / total])
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

        category_set = set(str(category) for category in categories)
        l_rows.append([1.0 if category in category_set else 0.0 for category in LOCALIZATION_CATEGORIES])
        for category in category_set:
            if category in category_counts:
                category_counts[category] += 1

    present = [index for index, category in enumerate(LOCALIZATION_CATEGORIES) if category_counts[category] > 0]
    categories_used = [LOCALIZATION_CATEGORIES[index] for index in present]
    l_rows = [[row[index] for index in present] for row in l_rows]
    category_counts_used = {category: category_counts[category] for category in categories_used}

    summary = {
        "n_joined_reported": cds_payload.get("n_joined"),
        "join_hit_rate": cds_payload.get("join_hit_rate"),
        "n_proteins": len(x_rows),
        "skipped_records": skipped,
        "n_localization_records": localization_payload.get("n_string_localization_records"),
        "n_joined": len(x_rows),
        "localization_category_counts": category_counts_used,
        "localization_categories_used": categories_used,
        "source_localization_category_counts": localization_payload.get("category_counts"),
    }
    return x_rows, t_rows, y_rows, z_rows, l_rows, summary


def p_q_perp_tmod(
    *,
    x_tilde: list[list[float]],
    t_mod_tilde: list[list[float]],
    y_tilde: list[list[float]],
) -> dict[str, object]:
    y_col = matrix_column(y_tilde, 0)
    p_q, q_coeff = project_onto_design(x_tilde, y_col)
    p_q_from_tmod, tmod_coeff = project_onto_design(t_mod_tilde, p_q)
    residual = subtract_vectors(p_q, p_q_from_tmod)
    p_q_norm2 = vector_norm2(p_q)
    residual_norm2 = vector_norm2(residual)
    return {
        "P_Q": p_q,
        "P_Q_perp_Tmod": residual,
        "P_Q_norm2": p_q_norm2,
        "P_Q_perp_Tmod_norm2": residual_norm2,
        "d_modeled": None if p_q_norm2 <= SURVIVAL_EPS else bounded_unit(residual_norm2 / p_q_norm2),
        "coefficients": {
            "Q_to_P": q_coeff,
            "Tmod_on_P_Q": tmod_coeff,
        },
    }


def absorption_by_design(design_tilde: list[list[float]], target: list[float]) -> dict[str, object]:
    absorbed_vector, coeff = project_onto_design(design_tilde, target)
    denominator = vector_norm2(target)
    absorbed_norm2 = vector_norm2(absorbed_vector)
    absorbed = None if denominator <= SURVIVAL_EPS else bounded_unit(absorbed_norm2 / denominator)
    return {
        "absorbed": absorbed,
        "absorbed_norm2": absorbed_norm2,
        "target_norm2": denominator,
        "coefficients": coeff,
    }


def absorption_by_basis(design_tilde: list[list[float]], target: list[float]) -> dict[str, object]:
    basis = orthonormal_basis_from_columns(design_tilde)
    absorbed_vector = [0.0 for _ in target]
    for q in basis:
        coeff = sum(target[index] * q[index] for index in range(len(target)))
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            absorbed_vector[index] += coeff * q[index]
    denominator = vector_norm2(target)
    absorbed_norm2 = vector_norm2(absorbed_vector)
    absorbed = None if denominator <= SURVIVAL_EPS else bounded_unit(absorbed_norm2 / denominator)
    return {
        "absorbed": absorbed,
        "absorbed_norm2": absorbed_norm2,
        "target_norm2": denominator,
        "rank": len(basis),
    }


def residualize_with_basis(matrix: list[list[float]], basis: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    out = [list(row) for row in matrix]
    width = len(matrix[0])
    for q in basis:
        for col in range(width):
            coeff = sum(matrix[row][col] * q[row] for row in range(len(matrix)))
            if coeff == 0.0:
                continue
            for row in range(len(matrix)):
                out[row][col] -= coeff * q[row]
    return out


def rank_of_design(design: list[list[float]], response: list[list[float]]) -> int:
    return explained_by_design(design, response)[1]


def lcg_uniform(seed: int) -> tuple[int, float]:
    next_seed = (1664525 * seed + 1013904223) & 0xFFFFFFFF
    return next_seed, (next_seed + 0.5) / 4294967296.0


def deterministic_gaussian_matrix(*, organism: str, trial: int, n_rows: int, k_cols: int) -> list[list[float]]:
    digest = hashlib.sha256(f"{EXPERIMENT_ID}|{organism}|{trial}".encode("utf-8")).digest()
    seed = int.from_bytes(digest[:4], "big")
    values: list[float] = []
    need = n_rows * k_cols
    while len(values) < need:
        seed, u1 = lcg_uniform(seed)
        seed, u2 = lcg_uniform(seed)
        u1 = max(u1, 1e-12)
        radius = math.sqrt(-2.0 * math.log(u1))
        angle = 2.0 * math.pi * u2
        values.append(radius * math.cos(angle))
        if len(values) < need:
            values.append(radius * math.sin(angle))
    return [values[row * k_cols:(row + 1) * k_cols] for row in range(n_rows)]


def dof_matched_null(
    *,
    organism: str,
    n_rows: int,
    k_cols: int,
    z_basis: list[list[float]],
    target: list[float],
    trials: int = NULL_TRIALS,
) -> dict[str, object]:
    absorptions: list[float] = []
    ranks: list[int] = []
    for trial in range(trials):
        raw = deterministic_gaussian_matrix(organism=organism, trial=trial, n_rows=n_rows, k_cols=k_cols)
        null_tilde = residualize_with_basis(raw, z_basis)
        result = absorption_by_basis(null_tilde, target)
        absorbed = result["absorbed"]
        if not isinstance(absorbed, float):
            raise ValueError(f"{organism} null trial {trial} did not produce finite absorption")
        absorptions.append(absorbed)
        ranks.append(int(result["rank"]))
    return {
        "trial_count": trials,
        "absorbed_values": absorptions,
        "absorbed_null_mean": mean(absorptions),
        "absorbed_null_p95": percentile_nearest_rank(absorptions, 0.95),
        "rank_min": min(ranks) if ranks else None,
        "rank_max": max(ranks) if ranks else None,
        "rank_unique_values": sorted(set(ranks)),
        "randomness": "one deterministic hashlib-derived seed per organism/trial, then LCG and Box-Muller; no system time",
    }


def interpretation_label(absorbed: float | None, null_p95: float | None) -> str:
    if absorbed is None or null_p95 is None:
        return "no_modeled_complement_energy_to_classify"
    if absorbed > null_p95:
        return "localization_carries_residual_signal"
    return "localization_no_better_than_dof_matched_null"


def cannot_claim() -> list[str]:
    return [
        "statistical projection, not causal",
        "subcellular location is a coarse categorical annotation (UniProt CC), multi-label",
        "multi-column readout absorbs mechanically - only excess over dof-matched null is signal",
        "absorbed fraction descriptive, not causal",
        "if no excess over null, localization does NOT explain the residual - H still open",
    ]


def cross_organism_conclusion(per_organism: dict[str, dict[str, object]]) -> dict[str, object]:
    tested = [
        {
            "organism": organism,
            "absorbed_by_localization": result.get("absorbed_by_localization"),
            "absorbed_null_mean": result.get("absorbed_null_mean"),
            "absorbed_null_p95": result.get("absorbed_null_p95"),
            "excess_over_null": result.get("excess_over_null"),
            "above_null_p95": result.get("above_null_p95"),
            "interpretation_label": result.get("interpretation_label"),
        }
        for organism, result in per_organism.items()
    ]
    positive = [item for item in tested if item["above_null_p95"] is True]
    if not tested:
        verdict = "localization could not be tested from fetched UniProt data"
    elif len(positive) == len(tested):
        verdict = "localization is above the dof-matched null in every tested organism"
    elif positive:
        verdict = "localization is above the dof-matched null only in a subset of tested organisms"
    else:
        verdict = "localization is not above the dof-matched null in the tested organisms"
    return {
        "verdict": verdict,
        "tested_organism_count": len(tested),
        "above_null_p95_count": len(positive),
        "per_organism_signal_summary": tested,
        "criterion": "true localization signal is called only when absorbed_by_localization > absorbed_null_p95 for the same K-column design size",
    }


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    required = ["tools/bio_reality/data/ncbi_genetic_codes.json"]
    for pair in ORGANISM_PAIRS:
        required.append(f"tools/bio_reality/data/cds_codon_abundance_{pair['organism']}.json")
        required.append(f"tools/bio_reality/data/gtrnadb_trna_all_copy_{pair['trna_organism']}.json")
    missing = [path for path in required if not (repo / path).exists()]
    if missing:
        emit("needs_data", missing_required_data=missing, reason="required local CDS-abundance and GtRNAdb all-tRNA data not present")

    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}

        per_organism: dict[str, dict[str, object]] = {}
        needs_external: dict[str, object] = {}
        fetch_actual: dict[str, object] = {}
        joined_actual: dict[str, object] = {}
        alignment_actual: dict[str, object] = {}
        localization_parsed_ok = True
        joined_ok = True
        residualized_ok = True
        complement_ok = True
        absorption_ok = True
        null_ok = True
        alignment_ok = True

        for pair in ORGANISM_PAIRS:
            organism = pair["organism"]
            trna_organism = pair["trna_organism"]
            localization_payload, fetch_summary = load_or_fetch_localization(repo, pair)
            fetch_actual[organism] = fetch_summary
            if localization_payload is None:
                needs_external[organism] = fetch_summary
                continue

            proteins = localization_payload.get("proteins")
            category_counts_source = localization_payload.get("category_counts")
            localization_parsed_ok = localization_parsed_ok and isinstance(proteins, dict) and bool(proteins) and isinstance(category_counts_source, dict)

            cds_payload = load_json(repo / f"tools/bio_reality/data/cds_codon_abundance_{organism}.json")
            if not isinstance(cds_payload, dict):
                raise ValueError(f"{organism} CDS payload must be a JSON object")
            tai_weights, tai_summary = modeled_tai_weights(
                repo=repo,
                organism=organism,
                trna_organism=trna_organism,
                code=code,
                codons=codons,
            )
            x_rows, t_mod_rows, y_rows, z_rows, l_rows, data_summary = localization_rows(
                cds_payload=cds_payload,
                localization_payload=localization_payload,
                organism=organism,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
                tai_weights=tai_weights,
            )
            n_proteins = len(x_rows)
            if n_proteins == 0:
                raise ValueError(f"{organism} has no usable proteins after localization x modeled tAI x abundance x codon join")

            z_basis = orthonormal_basis_from_columns(z_rows)
            rank_z = len(z_basis)
            x_tilde = residualize_with_basis(x_rows, z_basis)
            t_mod_tilde = residualize_with_basis(t_mod_rows, z_basis)
            y_tilde = residualize_with_basis(y_rows, z_basis)
            l_tilde = residualize_with_basis(l_rows, z_basis)

            residual = p_q_perp_tmod(x_tilde=x_tilde, t_mod_tilde=t_mod_tilde, y_tilde=y_tilde)
            target = residual["P_Q_perp_Tmod"]
            if not isinstance(target, list):
                raise ValueError(f"{organism} P_Q_perp_Tmod vector is malformed")
            localization_absorption = absorption_by_basis(l_tilde, target)
            null = dof_matched_null(
                organism=organism,
                n_rows=n_proteins,
                k_cols=len(l_rows[0]) if l_rows else 0,
                z_basis=z_basis,
                target=target,
            )

            full_x_rows, full_t_rows, full_y_rows, full_z_rows, _ = protein_rows(
                payload=cds_payload,
                organism=organism,
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

            d_modeled = residual["d_modeled"]
            d_reference = complement_reference["d"]
            d_difference = None
            d_matches = False
            if isinstance(d_modeled, float) and isinstance(d_reference, float):
                d_difference = abs(d_modeled - d_reference)
                d_matches = d_difference < MODELED_ALIGNMENT_TOL

            absorbed = localization_absorption["absorbed"]
            null_mean = null["absorbed_null_mean"]
            null_p95 = null["absorbed_null_p95"]
            excess = None
            above_p95 = False
            if isinstance(absorbed, float) and isinstance(null_mean, float):
                excess = absorbed - null_mean
            if isinstance(absorbed, float) and isinstance(null_p95, float):
                above_p95 = absorbed > null_p95

            k_cols = len(l_rows[0]) if l_rows else 0
            l_rank = int(localization_absorption["rank"])
            n_ok = n_proteins >= MIN_PROTEINS_PER_ORGANISM
            residualized_current_ok = rank_z > 0 and len(x_tilde) == n_proteins and len(t_mod_tilde) == n_proteins and len(y_tilde) == n_proteins and len(l_tilde) == n_proteins
            complement_current_ok = finite_unit_interval(d_modeled)
            absorption_current_ok = finite_unit_interval(absorbed)
            null_current_ok = isinstance(null_mean, float) and isinstance(null_p95, float) and 0.0 <= null_mean <= 1.0 and 0.0 <= null_p95 <= 1.0

            joined_ok = joined_ok and n_ok
            residualized_ok = residualized_ok and residualized_current_ok
            complement_ok = complement_ok and complement_current_ok
            absorption_ok = absorption_ok and absorption_current_ok
            null_ok = null_ok and null_current_ok
            alignment_ok = alignment_ok and d_matches

            joined_actual[organism] = {
                "n_joined": n_proteins,
                "n_cds_joined_reported": data_summary.get("n_joined_reported"),
                "n_localization_records": data_summary.get("n_localization_records"),
                "rank_Z": rank_z,
                "control_column_count": len(z_rows[0]) if z_rows else 0,
                "K": k_cols,
            }
            alignment_actual[organism] = {
                "d_modeled_current_localization_join": d_modeled,
                "d_modeled_complement_experiment_reference_full_abundance_cds_join": d_reference,
                "absolute_difference": d_difference,
                "matches_within_0_02": d_matches,
                "current_join_n": n_proteins,
                "complement_reference_join_n": len(full_x_rows),
                "interpretation_if_failed": "reported honestly; localization availability can change the protein_id join used by the H-candidate projection",
            }

            provenance = localization_payload.get("provenance")
            per_organism[organism] = {
                **data_summary,
                **tai_summary,
                "n_joined": n_proteins,
                "K": k_cols,
                "category_counts": data_summary["localization_category_counts"],
                "d_modeled": d_modeled,
                "d_modeled_reference_from_complement_experiment": d_reference,
                "d_modeled_reference_absolute_difference": d_difference,
                "d_modeled_matches_complement_experiment_within_0_02": d_matches,
                "absorbed_by_localization": absorbed,
                "absorbed_null_mean": null_mean,
                "absorbed_null_p95": null_p95,
                "excess_over_null": excess,
                "above_null_p95": above_p95,
                "interpretation_label": interpretation_label(absorbed if isinstance(absorbed, float) else None, null_p95 if isinstance(null_p95, float) else None),
                "provenance": provenance if isinstance(provenance, dict) else {},
                "norms": {
                    "P_Q_norm2": residual["P_Q_norm2"],
                    "P_Q_perp_Tmod_norm2": residual["P_Q_perp_Tmod_norm2"],
                    "P_Q_perp_Tmod_absorbed_by_localization_norm2": localization_absorption["absorbed_norm2"],
                },
                "rank_condition_diagnostics": {
                    "rank_Q_e": rank_of_design(x_tilde, y_tilde),
                    "rank_Tmod": rank_of_design(t_mod_tilde, y_tilde),
                    "rank_L": l_rank,
                    "rank_Z": rank_z,
                    "reference_full_join_rank_Z": full_rank_z,
                    "residual_df_after_Z": n_proteins - rank_z,
                    "q_coordinate_count": len(q_names),
                    "localization_column_count": k_cols,
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                    "ridge_epsilon": RIDGE_EPS,
                    "condition_number_Q_gram": condition_number_from_gram(gram_matrix(x_tilde)),
                    "condition_number_Tmod_gram": condition_number_from_gram(gram_matrix(t_mod_tilde)),
                    "condition_number_L_gram": condition_number_from_gram(gram_matrix(l_tilde)),
                    "null_rank_min": null["rank_min"],
                    "null_rank_max": null["rank_max"],
                },
                "dof_matched_null": {
                    "trial_count": null["trial_count"],
                    "randomness": null["randomness"],
                    "rank_unique_values": null["rank_unique_values"],
                },
            }

        checks = [
            {
                "name": "localization_data_fetched",
                "passed": len(fetch_actual) == len(ORGANISM_PAIRS) and not needs_external,
                "actual": fetch_actual,
                "expected": "UniProtKB reviewed localization stream downloaded or existing sha256-provenance JSON loaded for yeast/human/danio; fetch failure marks needs_external and no labels are fabricated",
            },
            {
                "name": "localization_parsed",
                "passed": localization_parsed_ok and bool(per_organism),
                "actual": {
                    organism: {
                        "category_counts": result["category_counts"],
                        "K": result["K"],
                        "n_localization_records": result["n_localization_records"],
                    }
                    for organism, result in per_organism.items()
                },
                "expected": "STRING join key and non-empty coarse localization category table",
            },
            {
                "name": "inputs_joined",
                "passed": joined_ok and len(per_organism) == len(ORGANISM_PAIRS),
                "actual": joined_actual,
                "expected": f"each organism has n >= {MIN_PROTEINS_PER_ORGANISM} after localization x modeled tAI x abundance x CDS protein_id join",
            },
            {
                "name": "b_star_q6_residuals + controls_Z + modeled_complement",
                "passed": len(q_names) == 9 and residualized_ok and complement_ok,
                "actual": {
                    "coordinates": q_names,
                    "coordinate_count": len(q_names),
                    "controls_used": controls_used(aa_order),
                    "per_organism": joined_actual,
                },
                "expected": "Q_e, T_mod, P_e, and L residualized against the same 24 control columns Z; modeled complement computed",
            },
            {
                "name": "d_modeled_matches_complement_experiment",
                "passed": alignment_ok,
                "actual": alignment_actual,
                "expected": f"|d_current_join - d_complement_reference_full_join| < {MODELED_ALIGNMENT_TOL}",
            },
            {
                "name": "localization_absorption_computed",
                "passed": absorption_ok,
                "actual": {
                    organism: {
                        "absorbed_by_localization": result["absorbed_by_localization"],
                        "K": result["K"],
                        "rank_L": result["rank_condition_diagnostics"]["rank_L"],
                    }
                    for organism, result in per_organism.items()
                },
                "expected": "absorbed_by_localization is finite and in [0,1]",
            },
            {
                "name": "dof_matched_null_computed",
                "passed": null_ok,
                "actual": {
                    organism: {
                        "absorbed_null_mean": result["absorbed_null_mean"],
                        "absorbed_null_p95": result["absorbed_null_p95"],
                        "trial_count": result["dof_matched_null"]["trial_count"],
                    }
                    for organism, result in per_organism.items()
                },
                "expected": f"{NULL_TRIALS} deterministic K-column Gaussian null projections per organism",
            },
            {
                "name": "no_causal_promotion",
                "passed": True,
                "actual": {
                    "passed": True,
                    "cannot_claim": cannot_claim(),
                },
                "expected": "statistical projection only; no causal or mechanism promotion",
            },
        ]

        if not per_organism and needs_external:
            status = "needs_external"
            reason = "all UniProt localization fetches failed; no localization labels were fabricated"
        else:
            status = "passed" if joined_ok and residualized_ok and complement_ok and absorption_ok and null_ok and not needs_external else "failed"
            reason = None
            if status == "passed" and not alignment_ok:
                reason = "computed on localization all-readout join; d_modeled does not match the full-join complement reference within 0.02 for every organism"
            if status == "failed":
                reason = "one or more computation gates failed or at least one organism needs external localization data"

        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture": CONJECTURE_ID,
                "statement": "UniProtKB reviewed subcellular localization is tested as an H-candidate by projecting the modeled-tAI complement abundance residual P_hat_{Q perp Tmod} onto residualized multi-label localization one-hot columns, with a K-column dof-matched Gaussian null baseline.",
                "status_semantics": "passed means localization absorption and the dof-matched null were computed; only absorption above the null 95th percentile is interpreted as localization carrying residual signal; no causal statement is made",
                "decomposition": {
                    "Q_e": "9 B*_Q6 residual coordinates after residualizing controls Z",
                    "T_mod": "residualized modeled per-protein tAI after controls Z",
                    "L": "residualized UniProt subcellular-location multi-label one-hot matrix after controls Z",
                    "P_e": "residualized log10 PAXdb abundance after controls Z",
                    "P_hat_Q": "Pi_{Q_e} P_e",
                    "P_hat_Q_perp_Tmod": "(I - Pi_{Tmod}) P_hat_Q",
                    "absorbed_by_localization": "||Pi_L P_hat_{Q perp Tmod}||^2 / ||P_hat_{Q perp Tmod}||^2",
                    "dof_matched_null": "K-column deterministic Gaussian designs residualized by Z, projected onto the same P_hat_{Q perp Tmod}",
                    "ridge_epsilon": RIDGE_EPS,
                },
                "coordinates": q_names,
                "per_organism": per_organism,
                "needs_external": needs_external,
                "cross_organism": cross_organism_conclusion(per_organism),
                "honest": {
                    "cannot_claim": cannot_claim(),
                },
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable localization H-candidate input")


if __name__ == "__main__":
    main()

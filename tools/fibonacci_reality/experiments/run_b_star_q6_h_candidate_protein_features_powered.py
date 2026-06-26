#!/usr/bin/env python3
"""UniProt protein features as H-candidates for the modeled-tAI complement.

This is a descriptive statistical projection audit. It tests whether fetchable
UniProt reviewed protein feature annotations absorb the B*_Q6 abundance
component left after modeled tAI. It is not causal.
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

from run_b_star_q6_h_candidate_localization_powered import (
    MODELED_ALIGNMENT_TOL,
    NULL_TRIALS,
    bounded_unit,
    dof_matched_null,
    finite_unit_interval,
    first_present,
    first_string_key,
    p_q_perp_tmod,
    percentile_nearest_rank,
    rank_of_design,
    residualize_with_basis,
)
from run_b_star_q6_protein_omics_survival_powered import (
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


EXPERIMENT_ID = "b_star_q6_h_candidate_protein_features_powered"
CLAIM_ID = "h3.cross_layer_relation.h_candidate_protein_features.b_star_q6_nontranslation_residual_powered"
CONJECTURE_ID = "q6.h-candidate-protein-features.non-translation-residual.cross-layer"

ORGANISM_PAIRS = [
    {
        "organism": "saccharomyces_cerevisiae",
        "trna_organism": "saccharomyces_cerevisiae",
        "taxid": "559292",
        "data_slug": "saccharomyces_cerevisiae",
        "url": "https://rest.uniprot.org/uniprotkb/search?query=organism_id%3A559292%20AND%20reviewed%3Atrue&fields=accession%2Cxref_string%2Cft_mod_res%2Cft_domain%2Cft_transmem%2Ccc_subunit%2Clength&format=tsv&size=500",
    },
    {
        "organism": "homo_sapiens",
        "trna_organism": "homo_sapiens",
        "taxid": "9606",
        "data_slug": "homo_sapiens",
        "url": "https://rest.uniprot.org/uniprotkb/search?query=organism_id%3A9606%20AND%20reviewed%3Atrue&fields=accession%2Cxref_string%2Cft_mod_res%2Cft_domain%2Cft_transmem%2Ccc_subunit%2Clength&format=tsv&size=500",
    },
    {
        "organism": "danio_rerio",
        "trna_organism": "danio_rerio",
        "taxid": "7955",
        "data_slug": "danio_rerio",
        "url": "https://rest.uniprot.org/uniprotkb/search?query=organism_id%3A7955%20AND%20reviewed%3Atrue&fields=accession%2Cxref_string%2Cft_mod_res%2Cft_domain%2Cft_transmem%2Ccc_subunit%2Clength&format=tsv&size=500",
    },
]

CANDIDATES = ["ptm_density", "domain_count", "tm_count", "complex_member"]
BONFERRONI_ALPHA = 0.05
TOTAL_TESTS = len(ORGANISM_PAIRS) * len(CANDIDATES)
BONFERRONI_PROBABILITY = 1.0 - BONFERRONI_ALPHA / TOTAL_TESTS
SURVIVAL_EPS = 1e-12
COMPLEX_PATTERNS = ["complex", "component of", "omplex", "heteromer", "homodimer", "oligomer"]
STARTED_AT = dt.datetime.now(dt.timezone.utc).isoformat()


def emit(status: str, **kw: object) -> None:
    checks = kw.pop("checks", [])
    result = kw.pop("result", None)
    if result is None:
        result = kw
    elif kw and isinstance(result, dict):
        result = {**result, **kw}
    payload = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "status": status,
        "checks": checks if isinstance(checks, list) else [],
        "result": result if isinstance(result, dict) else {"value": result},
        "started_at": STARTED_AT,
        "completed_at": dt.datetime.now(dt.timezone.utc).isoformat(),
    }
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def utc_now_iso() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def mean(values: list[float]) -> float | None:
    if not values:
        return None
    return sum(values) / len(values)


def fetch_url(url: str) -> bytes:
    socket.setdefaulttimeout(240)
    request = urllib.request.Request(
        url,
        headers={
            "User-Agent": "FibonacciReality-Codex-UniProtProteinFeatures/1.0",
            "Connection": "close",
        },
    )
    with urllib.request.urlopen(request, timeout=240) as response:
        chunks: list[bytes] = []
        deadline = time.monotonic() + 180.0
        while True:
            if time.monotonic() > deadline:
                raise TimeoutError(f"download deadline exceeded for {url}")
            chunk = response.read(65536)
            if not chunk:
                break
            chunks.append(chunk)
        return b"".join(chunks)


def paged_search_url_from_url(url: str) -> str:
    parsed = urllib.parse.urlparse(url)
    query = parsed.query
    if "size=" not in query:
        query = f"{query}&size=500" if query else "size=500"
    return urllib.parse.urlunparse(parsed._replace(path="/uniprotkb/search", query=query))


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


def fetch_uniprot_payload(source_url: str) -> tuple[bytes, str, str]:
    page_url = paged_search_url_from_url(source_url)
    lines: list[bytes] = []
    page_index = 0
    current: str | None = page_url
    try:
        while current:
            request = urllib.request.Request(
                current,
                headers={
                    "User-Agent": "FibonacciReality-Codex-UniProtProteinFeatures/1.0",
                    "Connection": "close",
                },
            )
            with urllib.request.urlopen(request, timeout=240) as response:
                payload = response.read()
                page_lines = payload.splitlines()
                if page_index == 0:
                    lines.extend(page_lines)
                else:
                    lines.extend(page_lines[1:])
                current = next_link(response.headers)
            page_index += 1
        return b"\n".join(lines) + b"\n", "paged_search", page_url
    except Exception:
        stream_url = page_url.replace("/uniprotkb/search?", "/uniprotkb/stream?").replace("&size=500", "")
        return fetch_url(stream_url), "stream_fallback_after_paged_search_failure", stream_url


def parse_float(value: str) -> float | None:
    text = value.strip().replace(",", "")
    if not text or text.upper() in {"NA", "N/A", "NULL"}:
        return None
    try:
        out = float(text)
    except ValueError:
        return None
    return out if math.isfinite(out) else None


def count_feature_mentions(text: str, token: str) -> int:
    if not text.strip():
        return 0
    return text.upper().count(token.upper())


def complex_member_from_subunit(text: str) -> int:
    lowered = text.lower()
    return 1 if any(pattern in lowered for pattern in COMPLEX_PATTERNS) else 0


def distribution_summary(values: list[float]) -> dict[str, object]:
    if not values:
        return {"n": 0}
    ordered = sorted(values)
    return {
        "n": len(values),
        "min": ordered[0],
        "mean": mean(values),
        "median": percentile_nearest_rank(values, 0.5),
        "p95": percentile_nearest_rank(values, 0.95),
        "max": ordered[-1],
        "nonzero_count": sum(1 for value in values if value != 0.0),
    }


def parse_uniprot_tsv(payload: bytes, organism: str, taxid: str) -> dict[str, object]:
    text = payload.decode("utf-8")
    reader = csv.DictReader(text.splitlines(), delimiter="\t")
    proteins: dict[str, dict[str, object]] = {}
    skipped = {
        "missing_string": 0,
        "missing_or_invalid_length": 0,
        "duplicate_string_first_key": 0,
    }

    for row in reader:
        string_key = first_string_key(first_present(row, ["STRING", "Cross-reference (STRING)", "String"]))
        if not string_key:
            skipped["missing_string"] += 1
            continue
        length = parse_float(first_present(row, ["Length", "length"]))
        if length is None or length <= 0.0:
            skipped["missing_or_invalid_length"] += 1
            continue

        mod_res = first_present(row, ["Modified residue", "Modified residue [FT]", "FT_MOD_RES", "MOD_RES"])
        domain = first_present(row, ["Domain [FT]", "Domain", "FT_DOMAIN", "DOMAIN"])
        transmem = first_present(row, ["Transmembrane", "Transmembrane [FT]", "FT_TRANSMEM", "TRANSMEM"])
        subunit = first_present(row, ["Subunit structure [CC]", "Subunit", "CC_SUBUNIT", "Subunit structure"])

        features = {
            "ptm_density": count_feature_mentions(mod_res, "MOD_RES") / length,
            "domain_count": float(count_feature_mentions(domain, "DOMAIN")),
            "tm_count": float(count_feature_mentions(transmem, "TRANSMEM")),
            "complex_member": float(complex_member_from_subunit(subunit)),
        }

        if string_key in proteins:
            skipped["duplicate_string_first_key"] += 1
            old = proteins[string_key]
            old_features = old.get("features")
            if isinstance(old_features, dict):
                features = {
                    "ptm_density": max(float(old_features.get("ptm_density", 0.0)), features["ptm_density"]),
                    "domain_count": max(float(old_features.get("domain_count", 0.0)), features["domain_count"]),
                    "tm_count": max(float(old_features.get("tm_count", 0.0)), features["tm_count"]),
                    "complex_member": max(float(old_features.get("complex_member", 0.0)), features["complex_member"]),
                }

        proteins[string_key] = {
            "uniprot_accession": first_present(row, ["Entry", "Accession"]),
            "string_id": string_key,
            "length": length,
            "features": features,
            "raw_feature_counts": {
                "mod_res_count": int(round(features["ptm_density"] * length)),
                "domain_count": int(features["domain_count"]),
                "tm_count": int(features["tm_count"]),
                "complex_member": int(features["complex_member"]),
            },
        }

    values_by_candidate = {name: [] for name in CANDIDATES}
    for record in proteins.values():
        features = record.get("features")
        if isinstance(features, dict):
            for name in CANDIDATES:
                value = features.get(name)
                if isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value)):
                    values_by_candidate[name].append(float(value))

    return {
        "organism": organism,
        "ncbi_taxid": taxid,
        "schema_version": 1,
        "source_kind": "UniProtKB reviewed protein features",
        "proteins": proteins,
        "n_uniprot_rows": len(text.splitlines()) - 1 if text else 0,
        "n_string_feature_records": len(proteins),
        "feature_distribution_summary": {name: distribution_summary(values) for name, values in values_by_candidate.items()},
        "skipped_records": skipped,
        "feature_parse_policy": {
            "ptm_density": "count of MOD_RES feature mentions divided by UniProt length",
            "domain_count": "count of DOMAIN feature mentions",
            "tm_count": "count of TRANSMEM feature mentions",
            "complex_member": "1 when UniProt SUBUNIT text contains complex/component/heteromer/homodimer/oligomer keyword, else 0",
            "note": "coarse fetchable annotations only; absent annotation is encoded as zero, not as biological absence",
        },
    }


def protein_feature_data_path(repo: pathlib.Path, slug: str) -> pathlib.Path:
    return repo / f"tools/fibonacci_reality/data/uniprot_protein_features_{slug}.json"


def load_or_fetch_protein_features(repo: pathlib.Path, pair: dict[str, str]) -> tuple[dict[str, object] | None, dict[str, object]]:
    path = protein_feature_data_path(repo, pair["data_slug"])
    # Cache hit: a valid local payload (with a recorded sha256) is authoritative.
    # UniProt reviewed features are stable, so re-downloading on every run only
    # rewrites fetched_at on byte-identical data (commit churn) and re-loads UniProt.
    # Loading the cache also avoids the delete-on-fetch-error hazard below, where a
    # transient network blip during a rerun would wipe otherwise-good cached data.
    if path.exists():
        try:
            cached = json.loads(path.read_text(encoding="utf-8"))
            provenance = cached.get("provenance", {})
            cached_sha = provenance.get("payload_sha256")
            if cached_sha:
                return cached, {
                    "organism": pair["organism"],
                    "data_path": str(path.relative_to(repo)),
                    "loaded_existing": True,
                    "payload_sha256": cached_sha,
                    "payload_byte_size": provenance.get("payload_byte_size"),
                    "fetch_method": "cache",
                    "source_url": pair["url"],
                    "downloaded_url": provenance.get("downloaded_url"),
                }
        except Exception:
            pass  # corrupt cache → fall through to a real fetch
    try:
        raw, fetch_method, downloaded_url = fetch_uniprot_payload(pair["url"])
        sha = hashlib.sha256(raw).hexdigest()
        parsed = parse_uniprot_tsv(raw, pair["organism"], pair["taxid"])
        parsed["provenance"] = {
            "source_url": pair["url"],
            "downloaded_url": downloaded_url,
            "fetch_method": fetch_method,
            "source_kind": "UniProtKB reviewed protein features",
            "fetched_at": utc_now_iso(),
            "payload_sha256": sha,
            "payload_byte_size": len(raw),
            "fetch_user_agent": "FibonacciReality-Codex-UniProtProteinFeatures/1.0",
            "derivation_boundary": "not_bedc_kernel_content",
        }
        path.write_text(json.dumps(parsed, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        return parsed, {
            "organism": pair["organism"],
            "data_path": str(path.relative_to(repo)),
            "loaded_existing": False,
            "payload_sha256": sha,
            "payload_byte_size": len(raw),
            "fetch_method": fetch_method,
            "source_url": pair["url"],
            "downloaded_url": downloaded_url,
        }
    except Exception as exc:
        if path.exists():
            path.unlink()
        return None, {
            "organism": pair["organism"],
            "source_url": pair["url"],
            "needs_external": True,
            "fetch_error": str(exc),
        }


def feature_rows(
    *,
    cds_payload: dict[str, object],
    feature_payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
    tai_weights: dict[str, float],
) -> tuple[list[list[float]], list[list[float]], list[list[float]], list[list[float]], dict[str, list[list[float]]], dict[str, object]]:
    joined = cds_payload.get("joined")
    proteins = feature_payload.get("proteins")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} CDS payload must contain joined list")
    if not isinstance(proteins, dict):
        raise ValueError(f"{organism} feature payload must contain proteins object")

    x_rows: list[list[float]] = []
    t_rows: list[list[float]] = []
    y_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    h_rows = {name: [] for name in CANDIDATES}
    values_by_candidate = {name: [] for name in CANDIDATES}
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "no_feature_match": 0,
        "missing_features": 0,
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
            skipped["no_feature_match"] += 1
            continue
        features = record.get("features")
        if not isinstance(features, dict) or not all(name in features for name in CANDIDATES):
            skipped["missing_features"] += 1
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

        for name in CANDIDATES:
            value = float(features[name])
            h_rows[name].append([value])
            values_by_candidate[name].append(value)

    summary = {
        "n_joined_reported": cds_payload.get("n_joined"),
        "join_hit_rate": cds_payload.get("join_hit_rate"),
        "n_proteins": len(x_rows),
        "skipped_records": skipped,
        "n_feature_records": feature_payload.get("n_string_feature_records"),
        "n_joined": len(x_rows),
        "feature_distribution_summary_joined": {name: distribution_summary(values) for name, values in values_by_candidate.items()},
        "source_feature_distribution_summary": feature_payload.get("feature_distribution_summary"),
    }
    return x_rows, t_rows, y_rows, z_rows, h_rows, summary


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


def candidate_label(absorbed: float | None, threshold: float | None) -> str:
    if absorbed is None or threshold is None:
        return "no_modeled_complement_energy_to_classify"
    if absorbed > threshold:
        return "candidate_exceeds_bonferroni_dof_null"
    return "candidate_not_above_bonferroni_dof_null"


def cannot_claim() -> list[str]:
    return [
        "statistical projection, not causal",
        "UniProt features are sparse/coarse annotations",
        "multi-candidate competition: Bonferroni-corrected, only excess over dof-matched null counts",
        "absorbed fraction descriptive, not mechanism",
        "if no candidate exceeds Bonferroni, the non-translation residual remains UNEXPLAINED by these fetchable features — H still open (turnover/degradation likely, data-blocked)",
    ]


def cross_organism_conclusion(per_organism: dict[str, dict[str, object]]) -> dict[str, object]:
    by_candidate: dict[str, dict[str, object]] = {}
    winners: dict[str, object] = {}
    for name in CANDIDATES:
        entries = []
        for organism, result in per_organism.items():
            candidates = result.get("candidates")
            if not isinstance(candidates, dict):
                continue
            candidate = candidates.get(name)
            if not isinstance(candidate, dict):
                continue
            entries.append(
                {
                    "organism": organism,
                    "absorbed": candidate.get("absorbed_c"),
                    "bonferroni_threshold": candidate.get("bonferroni_threshold"),
                    "exceeds_bonferroni": candidate.get("exceeds_bonferroni"),
                    "K_c": candidate.get("K_c"),
                }
            )
        positive = [entry for entry in entries if entry.get("exceeds_bonferroni") is True]
        by_candidate[name] = {
            "tested_organism_count": len(entries),
            "exceeds_bonferroni_count": len(positive),
            "consistent_excess_all_tested": bool(entries) and len(positive) == len(entries),
            "per_organism": entries,
        }
    for organism, result in per_organism.items():
        winners[organism] = result.get("H_star")

    any_winner = any(value for value in winners.values())
    stable = [name for name, summary in by_candidate.items() if summary["consistent_excess_all_tested"] is True]
    if stable:
        verdict = "at least one fetchable UniProt protein feature candidate consistently exceeds Bonferroni in all tested organisms"
    elif any_winner:
        verdict = "some fetchable UniProt protein feature candidates exceed Bonferroni in isolated organisms, but no candidate is stable across yeast/human/danio"
    else:
        verdict = "no fetchable UniProt protein feature candidate wins the Bonferroni dof-null competition; residual remains unexplained by these features"
    return {
        "verdict": verdict,
        "candidate_consistency": by_candidate,
        "H_star_by_organism": winners,
        "stable_H_candidates": stable,
        "criterion": "a candidate counts only when absorbed_c exceeds its dof-matched null nearest-rank quantile at 1 - 0.05/(organisms*candidates)",
    }


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    required = ["tools/fibonacci_reality/data/ncbi_genetic_codes.json"]
    for pair in ORGANISM_PAIRS:
        required.append(f"tools/fibonacci_reality/data/cds_codon_abundance_{pair['organism']}.json")
        required.append(f"tools/fibonacci_reality/data/gtrnadb_trna_all_copy_{pair['trna_organism']}.json")
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
        parsed_ok = True
        joined_ok = True
        residualized_ok = True
        complement_ok = True
        absorption_ok = True
        null_ok = True
        alignment_ok = True

        for pair in ORGANISM_PAIRS:
            organism = pair["organism"]
            trna_organism = pair["trna_organism"]
            feature_payload, fetch_summary = load_or_fetch_protein_features(repo, pair)
            fetch_actual[organism] = fetch_summary
            if feature_payload is None:
                needs_external[organism] = fetch_summary
                continue

            proteins = feature_payload.get("proteins")
            source_distribution = feature_payload.get("feature_distribution_summary")
            parsed_ok = parsed_ok and isinstance(proteins, dict) and bool(proteins) and isinstance(source_distribution, dict)

            cds_payload = load_json(repo / f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json")
            if not isinstance(cds_payload, dict):
                raise ValueError(f"{organism} CDS payload must be a JSON object")
            tai_weights, tai_summary = modeled_tai_weights(
                repo=repo,
                organism=organism,
                trna_organism=trna_organism,
                code=code,
                codons=codons,
            )
            x_rows, t_mod_rows, y_rows, z_rows, h_rows, data_summary = feature_rows(
                cds_payload=cds_payload,
                feature_payload=feature_payload,
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
                raise ValueError(f"{organism} has no usable proteins after feature x modeled tAI x abundance x codon join")

            z_basis = orthonormal_basis_from_columns(z_rows)
            rank_z = len(z_basis)
            x_tilde = residualize_with_basis(x_rows, z_basis)
            t_mod_tilde = residualize_with_basis(t_mod_rows, z_basis)
            y_tilde = residualize_with_basis(y_rows, z_basis)

            residual = p_q_perp_tmod(x_tilde=x_tilde, t_mod_tilde=t_mod_tilde, y_tilde=y_tilde)
            target = residual["P_Q_perp_Tmod"]
            if not isinstance(target, list):
                raise ValueError(f"{organism} P_Q_perp_Tmod vector is malformed")

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

            candidates: dict[str, dict[str, object]] = {}
            for candidate_name in CANDIDATES:
                h_tilde = residualize_with_basis(h_rows[candidate_name], z_basis)
                absorption = absorption_by_design(h_tilde, target)
                null = dof_matched_null(
                    organism=f"{organism}|{candidate_name}",
                    n_rows=n_proteins,
                    k_cols=1,
                    z_basis=z_basis,
                    target=target,
                )
                absorbed = absorption["absorbed"]
                null_values = null["absorbed_values"]
                if not isinstance(null_values, list):
                    raise ValueError(f"{organism} {candidate_name} null values malformed")
                null_float_values = [float(value) for value in null_values]
                threshold = percentile_nearest_rank(null_float_values, BONFERRONI_PROBABILITY)
                null_mean = null["absorbed_null_mean"]
                null_p95 = null["absorbed_null_p95"]
                exceeds = bool(isinstance(absorbed, float) and isinstance(threshold, float) and absorbed > threshold)
                candidates[candidate_name] = {
                    "absorbed_c": absorbed,
                    "null_mean": null_mean,
                    "null_p95": null_p95,
                    "bonferroni_threshold": threshold,
                    "bonferroni_probability": BONFERRONI_PROBABILITY,
                    "exceeds_bonferroni": exceeds,
                    "K_c": 1,
                    "DL": 1,
                    "rank_H_c": rank_of_design(h_tilde, y_tilde),
                    "condition_number_H_c_gram": condition_number_from_gram(gram_matrix(h_tilde)),
                    "absorbed_norm2": absorption["absorbed_norm2"],
                    "target_norm2": absorption["target_norm2"],
                    "excess_over_null_mean": absorbed - null_mean if isinstance(absorbed, float) and isinstance(null_mean, float) else None,
                    "interpretation_label": candidate_label(absorbed if isinstance(absorbed, float) else None, threshold if isinstance(threshold, float) else None),
                    "dof_matched_null": {
                        "trial_count": null["trial_count"],
                        "randomness": null["randomness"],
                        "rank_unique_values": null["rank_unique_values"],
                    },
                }

            winners = [
                {"candidate": name, "absorbed_c": value["absorbed_c"], "K_c": value["K_c"]}
                for name, value in candidates.items()
                if value.get("exceeds_bonferroni") is True and isinstance(value.get("absorbed_c"), float)
            ]
            winners.sort(key=lambda item: float(item["absorbed_c"]), reverse=True)
            h_star = winners[0] if winners else None

            n_ok = n_proteins >= MIN_PROTEINS_PER_ORGANISM
            residualized_current_ok = rank_z > 0 and len(x_tilde) == n_proteins and len(t_mod_tilde) == n_proteins and len(y_tilde) == n_proteins
            complement_current_ok = finite_unit_interval(d_modeled)
            absorption_current_ok = all(finite_unit_interval(candidate.get("absorbed_c")) for candidate in candidates.values())
            null_current_ok = all(
                isinstance(candidate.get("null_mean"), float)
                and isinstance(candidate.get("null_p95"), float)
                and isinstance(candidate.get("bonferroni_threshold"), float)
                and 0.0 <= float(candidate["null_mean"]) <= 1.0
                and 0.0 <= float(candidate["null_p95"]) <= 1.0
                and 0.0 <= float(candidate["bonferroni_threshold"]) <= 1.0
                for candidate in candidates.values()
            )

            joined_ok = joined_ok and n_ok
            residualized_ok = residualized_ok and residualized_current_ok
            complement_ok = complement_ok and complement_current_ok
            absorption_ok = absorption_ok and absorption_current_ok
            null_ok = null_ok and null_current_ok
            alignment_ok = alignment_ok and d_matches

            joined_actual[organism] = {
                "n_joined": n_proteins,
                "n_cds_joined_reported": data_summary.get("n_joined_reported"),
                "n_feature_records": data_summary.get("n_feature_records"),
                "rank_Z": rank_z,
                "control_column_count": len(z_rows[0]) if z_rows else 0,
                "candidate_count": len(candidates),
                "K_by_candidate": {name: candidate["K_c"] for name, candidate in candidates.items()},
            }
            alignment_actual[organism] = {
                "d_modeled_current_feature_join": d_modeled,
                "d_modeled_complement_experiment_reference_full_abundance_cds_join": d_reference,
                "absolute_difference": d_difference,
                "matches_within_0_02": d_matches,
                "current_join_n": n_proteins,
                "complement_reference_join_n": len(full_x_rows),
                "interpretation_if_failed": "reported honestly; feature availability can change the protein_id join used by the H-candidate projection",
            }

            provenance = feature_payload.get("provenance")
            per_organism[organism] = {
                **data_summary,
                **tai_summary,
                "n_joined": n_proteins,
                "d_modeled": d_modeled,
                "d_modeled_reference_from_complement_experiment": d_reference,
                "d_modeled_reference_absolute_difference": d_difference,
                "d_modeled_matches_complement_experiment_within_0_02": d_matches,
                "candidates": candidates,
                "H_star": h_star,
                "bonferroni": {
                    "alpha_familywise": BONFERRONI_ALPHA,
                    "total_tests": TOTAL_TESTS,
                    "probability": BONFERRONI_PROBABILITY,
                    "threshold_policy": "nearest-rank quantile of this candidate's dof-matched null at 1 - 0.05/(organisms*candidates)",
                },
                "provenance": provenance if isinstance(provenance, dict) else {},
                "norms": {
                    "P_Q_norm2": residual["P_Q_norm2"],
                    "P_Q_perp_Tmod_norm2": residual["P_Q_perp_Tmod_norm2"],
                },
                "rank_condition_diagnostics": {
                    "rank_Q_e": rank_of_design(x_tilde, y_tilde),
                    "rank_Tmod": rank_of_design(t_mod_tilde, y_tilde),
                    "rank_Z": rank_z,
                    "reference_full_join_rank_Z": full_rank_z,
                    "residual_df_after_Z": n_proteins - rank_z,
                    "q_coordinate_count": len(q_names),
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                    "ridge_epsilon": RIDGE_EPS,
                    "condition_number_Q_gram": condition_number_from_gram(gram_matrix(x_tilde)),
                    "condition_number_Tmod_gram": condition_number_from_gram(gram_matrix(t_mod_tilde)),
                },
            }

        checks = [
            {
                "name": "uniprot_features_fetched",
                "passed": len(fetch_actual) == len(ORGANISM_PAIRS) and not needs_external,
                "actual": fetch_actual,
                "expected": "UniProtKB reviewed protein-feature TSV truly downloaded with sha256 provenance for yeast/human/danio; fetch failure marks needs_external and no feature values are fabricated",
            },
            {
                "name": "features_parsed",
                "passed": parsed_ok and bool(per_organism),
                "actual": {
                    organism: {
                        "source_feature_distribution_summary": result["source_feature_distribution_summary"],
                        "joined_feature_distribution_summary": result["feature_distribution_summary_joined"],
                        "n_feature_records": result["n_feature_records"],
                    }
                    for organism, result in per_organism.items()
                },
                "expected": "four candidate readouts present with non-empty STRING-keyed feature table",
            },
            {
                "name": "inputs_joined",
                "passed": joined_ok and len(per_organism) == len(ORGANISM_PAIRS),
                "actual": joined_actual,
                "expected": f"each organism has n >= {MIN_PROTEINS_PER_ORGANISM} after UniProt feature x modeled tAI x abundance x CDS protein_id join",
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
                "expected": "Q_e, T_mod, P_e, and H_c residualized against the same 24 control columns Z; modeled complement computed",
            },
            {
                "name": "d_modeled_matches_complement_experiment",
                "passed": alignment_ok,
                "actual": alignment_actual,
                "expected": f"|d_current_join - d_complement_reference_full_join| < {MODELED_ALIGNMENT_TOL}",
            },
            {
                "name": "per_candidate_absorption_computed",
                "passed": absorption_ok,
                "actual": {
                    organism: {
                        name: {
                            "absorbed_c": candidate["absorbed_c"],
                            "K_c": candidate["K_c"],
                            "rank_H_c": candidate["rank_H_c"],
                        }
                        for name, candidate in result["candidates"].items()
                    }
                    for organism, result in per_organism.items()
                },
                "expected": "absorbed_c is finite and in [0,1] for every candidate and organism",
            },
            {
                "name": "dof_null_and_bonferroni_computed",
                "passed": null_ok,
                "actual": {
                    organism: {
                        name: {
                            "null_mean": candidate["null_mean"],
                            "null_p95": candidate["null_p95"],
                            "bonferroni_threshold": candidate["bonferroni_threshold"],
                            "exceeds_bonferroni": candidate["exceeds_bonferroni"],
                            "trial_count": candidate["dof_matched_null"]["trial_count"],
                        }
                        for name, candidate in result["candidates"].items()
                    }
                    for organism, result in per_organism.items()
                },
                "expected": f"{NULL_TRIALS} deterministic 1-column Gaussian null projections per candidate; Bonferroni threshold uses probability {BONFERRONI_PROBABILITY}",
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
            reason = "all UniProt feature fetches failed; no protein feature values were fabricated"
        else:
            status = "passed" if joined_ok and residualized_ok and complement_ok and absorption_ok and null_ok and not needs_external else "failed"
            reason = None
            if not alignment_ok:
                reason = "computed on feature all-readout join, but at least one organism's d_modeled does not match the full-join complement reference within 0.02; sparse reviewed-UniProt/STRING coverage changes the residual target and prevents a stable cross-organism H claim"
            if status == "failed":
                reason = reason or "one or more computation gates failed or at least one organism needs external UniProt feature data"

        emit(
            status,
            checks=checks,
            result={
                "statement": {
                    "conjecture_id": CONJECTURE_ID,
                    "claimed_layer": "cross_layer_relation",
                    "statement": "UniProtKB reviewed protein features are tested as H-candidates by projecting the modeled-tAI complement abundance residual P_hat_{Q perp Tmod} onto residualized one-column feature readouts, with per-candidate dof-matched Gaussian nulls and Bonferroni correction over organism x candidate tests.",
                    "candidate_readouts": CANDIDATES,
                    "competition": "H* = argmax_H [absorbed_c - lambda*DL(H)] among candidates exceeding Bonferroni; DL(H)=K_c=1 for all tested candidates, so winners are ranked by absorbed_c",
                },
                "status_semantics": "passed means the descriptive projection quantities were computed and bounded; sparse feature coverage and unstable cross-organism candidates are reported without promotion to causality, mechanism, or stable H closure",
                "per_organism": per_organism,
                "cross_organism": cross_organism_conclusion(per_organism),
                "cannot_claim": cannot_claim(),
                "needs_external": needs_external,
                "reason": reason,
            },
        )
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable UniProt protein-feature H-candidate input")


if __name__ == "__main__":
    main()

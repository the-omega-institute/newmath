#!/usr/bin/env python3
"""Fetch probe for codon-E1 expression-selection orientation data.

Only numeric PaxDB abundance rows that match a concrete RefSeq CDS are counted.
The probe does not infer missing identifiers; STRING aliases and exact protein
sequence matches are used only as deterministic joins.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from datetime import datetime, timezone
import gzip
import hashlib
import json
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any

import _e1_trna_fetch_probe as ncbi


EXPERIMENT_ID = "codon_e1_expression_selection_fetch_probe"
CLAIM_ID = "bridge.genetic_code.codon_e1_expression_selection_orientation"
USER_AGENT = "codon-e1-expression-selection-orientation"
PAXDB_ROOT = "https://pax-db.org/downloads/6.0/datasets/paxdb-abundance-files-v6.0"
STRING_ROOT = "https://stringdb-downloads.org/download"
MIN_MATCHED_GENES = 800
MIN_SENSE_CODONS = 200_000
MIN_SPECIES = 5
NCBI_DELAY_SECONDS = 0.34

ANCHOR_ASSEMBLY_ACCESSIONS = (
    "GCF_000005845.2",
    "GCF_000195955.2",
    "GCF_000009045.1",
    "GCF_000006765.1",
    "GCF_000195995.1",
    "GCF_000008865.2",
    "GCF_000007305.1",
    "GCF_000008265.1",
    "GCF_000091665.1",
    "GCF_000006945.2",
    "GCF_000013425.1",
    "GCF_000006745.1",
    "GCF_000008725.1",
    "GCF_000011965.2",
    "GCF_000196095.1",
    "GCF_000008525.1",
    "GCF_000009725.1",
    "GCF_000006905.1",
    "GCF_000009425.1",
    "GCF_000006885.1",
    "GCF_000008805.1",
    "GCF_000007125.1",
    "GCF_000195815.1",
)

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[2]
PANEL_CACHE_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "codon_e1_expression_selection_orientation_panel.json"
)
PROBE_CACHE_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "codon_e1_expression_selection_fetch_probe.json"
)


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def fetch_bytes(url: str, timeout: int = 90, attempts: int = 3) -> tuple[bytes, dict[str, object]]:
    last_error = ""
    for attempt in range(1, attempts + 1):
        req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(req, timeout=timeout) as response:
                payload = response.read()
                return payload, {
                    "url": url,
                    "reachable": True,
                    "http_status": int(getattr(response, "status", 200)),
                    "byte_size": len(payload),
                    "sha256": hashlib.sha256(payload).hexdigest(),
                    "attempts": attempt,
                }
        except urllib.error.HTTPError as exc:
            last_error = f"HTTPError:{exc.code}"
            if exc.code not in {429, 500, 502, 503, 504}:
                break
        except urllib.error.URLError as exc:
            last_error = f"URLError:{exc.reason}"
        except TimeoutError:
            last_error = "TimeoutError"
        except Exception as exc:  # pragma: no cover - network surface
            last_error = f"{type(exc).__name__}:{exc}"
        time.sleep(0.5 * attempt)
    return b"", {"url": url, "reachable": False, "blocked": True, "error": last_error or "fetch_failed"}


def fetch_text(url: str, timeout: int = 90, attempts: int = 3) -> tuple[str, dict[str, object]]:
    payload, contact = fetch_bytes(url, timeout=timeout, attempts=attempts)
    if not payload:
        return "", contact
    return payload.decode("utf-8", "replace"), contact


def fetch_gzip_text(url: str, timeout: int = 120, attempts: int = 3) -> tuple[str, dict[str, object]]:
    payload, contact = fetch_bytes(url, timeout=timeout, attempts=attempts)
    if not payload:
        return "", contact
    try:
        text = gzip.decompress(payload).decode("utf-8", "replace")
    except Exception as exc:
        contact["decompress_error"] = f"{type(exc).__name__}:{exc}"
        return "", contact
    contact["decompressed_chars"] = len(text)
    return text, contact


def paxdb_species_index() -> tuple[set[str], dict[str, object]]:
    html, contact = fetch_text(f"{PAXDB_ROOT}/", timeout=45)
    taxids = set(re.findall(r'href="(\d+)/"', html))
    contact["n_species_dirs"] = len(taxids)
    return taxids, contact


def parse_paxdb_abundance(text: str) -> tuple[list[dict[str, object]], dict[str, object]]:
    rows: list[dict[str, object]] = []
    meta: dict[str, object] = {}
    header: list[str] | None = None
    for line in text.splitlines():
        if not line:
            continue
        if line.startswith("#"):
            if ":" in line:
                key, value = line[1:].split(":", 1)
                meta[key.strip()] = value.strip()
            continue
        parts = line.split("\t")
        if header is None:
            header = [part.strip() for part in parts]
            continue
        if len(parts) < 3:
            continue
        try:
            abundance = float(parts[2])
        except ValueError:
            continue
        rows.append(
            {
                "gene_name": parts[0].strip(),
                "string_external_id": parts[1].strip(),
                "abundance_ppm": abundance,
            }
        )
    meta["n_abundance_rows"] = len(rows)
    return rows, meta


def fetch_paxdb_integrated(taxid: str) -> tuple[list[dict[str, object]], dict[str, object]]:
    url = f"{PAXDB_ROOT}/{taxid}/{taxid}-WHOLE_ORGANISM-integrated.txt"
    text, contact = fetch_text(url, timeout=60)
    if not text:
        return [], contact
    rows, meta = parse_paxdb_abundance(text)
    return rows, {**contact, **meta}


def parse_fasta_records(text: str) -> list[tuple[str, str]]:
    return ncbi.parse_fasta_records(text)


def bracket_attrs(header: str) -> dict[str, list[str]]:
    attrs: dict[str, list[str]] = defaultdict(list)
    for key, value in re.findall(r"\[([^=\]]+)=([^\]]*)\]", header):
        attrs[key].append(value)
    return dict(attrs)


def parse_db_xrefs(values: list[str]) -> list[str]:
    out: list[str] = []
    for value in values:
        for item in value.split(","):
            token = item.strip()
            if not token:
                continue
            out.append(token)
            if ":" in token:
                out.append(token.split(":", 1)[1])
    return out


def normalize_key(value: object) -> str:
    text = str(value or "").strip().lower()
    text = re.sub(r"^string:", "", text)
    return text


def codon_count_record(seq: str) -> tuple[dict[str, int] | None, dict[str, object]]:
    seq = re.sub(r"[^A-Za-z]", "", seq).upper()
    stop_codons = {codon.replace("U", "T") for codon, aa in ncbi.CODON_TO_AA.items() if aa == "*"}
    if len(seq) < 3 or len(seq) % 3 != 0:
        return None, {"skip": "length"}
    if any(base not in ncbi.BASES_DNA for base in seq):
        return None, {"skip": "ambiguous"}
    codons = [seq[offset : offset + 3] for offset in range(0, len(seq), 3)]
    if codons and codons[-1] in stop_codons:
        codons = codons[:-1]
    if any(codon in stop_codons for codon in codons):
        return None, {"skip": "internal_stop"}
    counts = {codon: 0 for codon in ncbi.sense_codon_order_rna()}
    for codon_dna in codons:
        codon = codon_dna.replace("T", "U")
        if codon in counts:
            counts[codon] += 1
    total = sum(counts.values())
    if total <= 0:
        return None, {"skip": "empty"}
    gc3 = sum(value for codon, value in counts.items() if codon[2] in {"G", "C"}) / total
    gc12 = (
        sum(value * ((codon[0] in {"G", "C"}) + (codon[1] in {"G", "C"})) for codon, value in counts.items())
        / (2.0 * total)
    )
    return counts, {"length_codons": total, "gc3": gc3, "gc12": gc12}


def parse_cds_records(cds_text: str) -> tuple[list[dict[str, object]], dict[str, object]]:
    records: list[dict[str, object]] = []
    skip_counts: Counter[str] = Counter()
    seen_primary: Counter[str] = Counter()
    for header, seq in parse_fasta_records(cds_text):
        attrs = bracket_attrs(header)
        counts, meta = codon_count_record(seq)
        if counts is None:
            skip_counts[str(meta.get("skip", "unknown"))] += 1
            continue
        first_token = header.split()[0]
        replicon = first_token
        if "_cds_" in first_token:
            replicon = first_token.split("_cds_", 1)[0].replace("lcl|", "")
        aliases: set[str] = set()
        for key in ("gene", "locus_tag", "protein_id"):
            for value in attrs.get(key, []):
                aliases.add(value)
        aliases.update(parse_db_xrefs(attrs.get("db_xref", [])))
        primary = next(iter(attrs.get("protein_id", [])), first_token)
        seen_primary[primary] += 1
        records.append(
            {
                "record_id": primary,
                "gene": next(iter(attrs.get("gene", [])), ""),
                "locus_tag": next(iter(attrs.get("locus_tag", [])), ""),
                "protein_id": next(iter(attrs.get("protein_id", [])), ""),
                "replicon": replicon,
                "aliases": sorted({alias for alias in aliases if alias}),
                "codon_counts_rna": {codon: int(value) for codon, value in counts.items() if value},
                **meta,
            }
        )
    return records, {
        "n_cds_records": len(parse_fasta_records(cds_text)),
        "n_accepted_cds": len(records),
        "skip_counts": dict(sorted(skip_counts.items())),
        "duplicate_primary_ids": sum(count - 1 for count in seen_primary.values() if count > 1),
    }


def parse_gff_tables_and_trna(gff_text: str, gbff_text: str = "") -> tuple[int | None, dict[str, int], dict[str, object]]:
    trna_counts, trna_meta = ncbi.parse_gff_trna_and_tables(gff_text) if gff_text else ({}, {})
    table_counts = trna_meta.get("transl_table_counts", {}) if isinstance(trna_meta, dict) else {}
    if (not table_counts or int(trna_meta.get("n_trna_with_anticodon", 0)) == 0) and gbff_text:
        gbff_trna, gbff_meta = ncbi.parse_genbank_trna_anticodons(gbff_text)
        gbff_tables = ncbi.parse_genbank_transl_tables(gbff_text)
        if int(gbff_meta.get("n_trna_with_anticodon", 0)) > 0:
            trna_counts = gbff_trna
            trna_meta = {**gbff_meta, "source": "genomic.gbff.gz", "transl_table_counts": gbff_tables}
            table_counts = gbff_tables
    observed = sorted(int(key) for key in table_counts) if table_counts else []
    table = observed[0] if len(observed) == 1 and observed[0] in {1, 11} else None
    return table, {str(k): int(v) for k, v in trna_counts.items()}, trna_meta


def parse_string_aliases(text: str) -> dict[str, list[str]]:
    aliases: dict[str, list[str]] = defaultdict(list)
    for line in text.splitlines():
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        string_id = parts[0].strip()
        alias = parts[1].strip()
        if string_id and alias:
            aliases[string_id].append(alias)
    return dict(aliases)


def fetch_string_aliases(taxid: str) -> tuple[dict[str, list[str]], dict[str, object]]:
    url = f"{STRING_ROOT}/protein.aliases.v12.0/{taxid}.protein.aliases.v12.0.txt.gz"
    text, contact = fetch_gzip_text(url, timeout=120, attempts=2)
    if not text:
        return {}, contact
    aliases = parse_string_aliases(text)
    contact["n_string_ids"] = len(aliases)
    return aliases, contact


def parse_protein_fasta_hashes(text: str) -> dict[str, str]:
    hashes: dict[str, str] = {}
    for header, seq in parse_fasta_records(text):
        protein_id = header.split()[0]
        if protein_id:
            hashes[protein_id] = hashlib.sha256(seq.encode("ascii", "ignore")).hexdigest()
    return hashes


def fetch_string_sequence_hashes(taxid: str) -> tuple[dict[str, str], dict[str, object]]:
    url = f"{STRING_ROOT}/protein.sequences.v12.0/{taxid}.protein.sequences.v12.0.fa.gz"
    text, contact = fetch_gzip_text(url, timeout=120, attempts=2)
    if not text:
        return {}, contact
    hashes = parse_protein_fasta_hashes(text)
    contact["n_string_sequences"] = len(hashes)
    return hashes, contact


def build_cds_key_index(cds_records: list[dict[str, object]]) -> dict[str, list[int]]:
    index: dict[str, list[int]] = defaultdict(list)
    for idx, rec in enumerate(cds_records):
        for key in [rec.get("record_id"), rec.get("gene"), rec.get("locus_tag"), rec.get("protein_id"), *rec.get("aliases", [])]:
            norm = normalize_key(key)
            if norm:
                index[norm].append(idx)
    return dict(index)


def unique_lookup(index: dict[str, list[int]], keys: list[str]) -> tuple[int | None, str | None, bool]:
    hits: dict[int, str] = {}
    for key in keys:
        norm = normalize_key(key)
        if not norm:
            continue
        for idx in index.get(norm, []):
            hits.setdefault(idx, norm)
    if len(hits) == 1:
        idx, key = next(iter(hits.items()))
        return idx, key, False
    return None, None, len(hits) > 1


def abundance_keys(row: dict[str, object], string_aliases: dict[str, list[str]]) -> list[str]:
    string_id = str(row.get("string_external_id", "")).strip()
    suffix = string_id.split(".", 1)[1] if "." in string_id else string_id
    keys = [string_id, suffix, str(row.get("gene_name", ""))]
    keys.extend(string_aliases.get(string_id, []))
    return [key for key in keys if key]


def match_abundance_to_cds(
    abundance_rows: list[dict[str, object]],
    cds_records: list[dict[str, object]],
    string_aliases: dict[str, list[str]],
    string_hashes: dict[str, str],
    protein_hashes: dict[str, str],
) -> tuple[list[dict[str, object]], dict[str, object]]:
    index = build_cds_key_index(cds_records)
    protein_hash_to_cds: dict[str, list[int]] = defaultdict(list)
    for idx, rec in enumerate(cds_records):
        protein_id = str(rec.get("protein_id") or rec.get("record_id") or "")
        if protein_id in protein_hashes:
            protein_hash_to_cds[protein_hashes[protein_id]].append(idx)

    matched: list[dict[str, object]] = []
    used_cds: set[int] = set()
    method_counts: Counter[str] = Counter()
    ambiguous = 0
    unmatched = 0
    duplicate_cds = 0
    for row in abundance_rows:
        idx, key, is_ambiguous = unique_lookup(index, abundance_keys(row, string_aliases))
        method = "direct_alias"
        if idx is None and not is_ambiguous:
            string_id = str(row.get("string_external_id", "")).strip()
            seq_hash = string_hashes.get(string_id)
            candidates = protein_hash_to_cds.get(seq_hash or "", [])
            if len(candidates) == 1:
                idx = candidates[0]
                key = "protein_sequence_sha256"
                method = "exact_protein_sequence"
            elif len(candidates) > 1:
                is_ambiguous = True
        if idx is None:
            if is_ambiguous:
                ambiguous += 1
            else:
                unmatched += 1
            continue
        if idx in used_cds:
            duplicate_cds += 1
            continue
        used_cds.add(idx)
        rec = cds_records[idx]
        method_counts[method] += 1
        matched.append(
            {
                "abundance_ppm": float(row["abundance_ppm"]),
                "paxdb_gene_name": row.get("gene_name"),
                "string_external_id": row.get("string_external_id"),
                "match_key": key,
                "match_method": method,
                "record_id": rec["record_id"],
                "gene": rec.get("gene"),
                "locus_tag": rec.get("locus_tag"),
                "protein_id": rec.get("protein_id"),
                "replicon": rec.get("replicon"),
                "length_codons": rec["length_codons"],
                "gc3": rec["gc3"],
                "gc12": rec["gc12"],
                "codon_counts_rna": rec["codon_counts_rna"],
            }
        )
    total_codons = sum(int(row["length_codons"]) for row in matched)
    return matched, {
        "n_abundance_rows": len(abundance_rows),
        "n_cds_records": len(cds_records),
        "n_matched_genes": len(matched),
        "total_sense_codons": total_codons,
        "unmatched_abundance_rows": unmatched,
        "ambiguous_abundance_rows": ambiguous,
        "duplicate_cds_matches": duplicate_cds,
        "match_method_counts": dict(sorted(method_counts.items())),
    }


def fetch_species_payload(summary: dict[str, object], paxdb_taxids: set[str]) -> dict[str, object]:
    taxid = str(summary.get("taxid", ""))
    if taxid not in paxdb_taxids:
        return {**summary, "ok_expr": False, "reason": "taxid_not_in_paxdb_v6_directory"}

    abundance_rows, paxdb_contact = fetch_paxdb_integrated(taxid)
    if not abundance_rows:
        return {**summary, "ok_expr": False, "reason": "paxdb_integrated_unavailable", "paxdb_contact": paxdb_contact}

    ftp_path = str(summary["ftp_path_refseq"])
    gff_text, gff_contact = ncbi.fetch_assembly_file(ftp_path, "genomic.gff.gz")
    cds_text, cds_contact = ncbi.fetch_assembly_file(ftp_path, "cds_from_genomic.fna.gz")
    protein_text, protein_contact = ncbi.fetch_assembly_file(ftp_path, "protein.faa.gz")
    gbff_text = ""
    gbff_contact: dict[str, object] = {"reachable": False, "skipped": True}
    need_gbff = False
    if gff_text:
        gff_trna_counts, gff_trna_meta = ncbi.parse_gff_trna_and_tables(gff_text)
        need_gbff = int(gff_trna_meta.get("n_trna_with_anticodon", 0)) == 0 or not gff_trna_meta.get("transl_table_counts")
        if gff_trna_counts:
            del gff_trna_counts
    if not gff_text or need_gbff:
        gbff_text, gbff_contact = ncbi.fetch_assembly_file(ftp_path, "genomic.gbff.gz")
    table, trna_counts, trna_meta = parse_gff_tables_and_trna(gff_text, gbff_text)
    cds_records, cds_meta = parse_cds_records(cds_text) if cds_text else ([], {"n_accepted_cds": 0})
    protein_hashes = parse_protein_fasta_hashes(protein_text) if protein_text else {}

    string_aliases, string_alias_contact = fetch_string_aliases(taxid)
    string_hashes: dict[str, str] = {}
    string_seq_contact: dict[str, object] = {"skipped": True}
    matched, match_meta = match_abundance_to_cds(abundance_rows, cds_records, string_aliases, string_hashes, protein_hashes)
    if int(match_meta["n_matched_genes"]) < MIN_MATCHED_GENES:
        string_hashes, string_seq_contact = fetch_string_sequence_hashes(taxid)
        matched, match_meta = match_abundance_to_cds(abundance_rows, cds_records, string_aliases, string_hashes, protein_hashes)

    ok = (
        table in {1, 11}
        and int(match_meta["n_matched_genes"]) >= MIN_MATCHED_GENES
        and int(match_meta["total_sense_codons"]) >= MIN_SENSE_CODONS
        and int(trna_meta.get("n_trna_with_anticodon", 0)) > 0
    )
    reason = "usable" if ok else "below_matched_gene_or_codon_threshold"
    if table not in {1, 11}:
        reason = "unsupported_or_mixed_translation_table"
    elif int(trna_meta.get("n_trna_with_anticodon", 0)) <= 0:
        reason = "missing_trna_anticodon_counts"
    return {
        **summary,
        "ok_expr": bool(ok),
        "reason": reason,
        "transl_table": table,
        "paxdb_contact": paxdb_contact,
        "gff_contact": gff_contact,
        "gbff_contact": gbff_contact,
        "cds_contact": cds_contact,
        "protein_contact": protein_contact,
        "string_alias_contact": string_alias_contact,
        "string_sequence_contact": string_seq_contact,
        "cds_meta": cds_meta,
        "trna_meta": trna_meta,
        "trna_anticodon_counts_rna": trna_counts,
        "match_meta": match_meta,
        "matched_genes": matched,
    }


def compact_attempt(row: dict[str, object]) -> dict[str, object]:
    match_meta = row.get("match_meta", {}) if isinstance(row.get("match_meta"), dict) else {}
    return {
        "assembly_accession": row.get("assembly_accession"),
        "organism": row.get("organism"),
        "species_name": row.get("species_name"),
        "genus": row.get("genus"),
        "taxid": row.get("taxid"),
        "ok_expr": row.get("ok_expr"),
        "reason": row.get("reason"),
        "transl_table": row.get("transl_table"),
        "n_abundance_rows": match_meta.get("n_abundance_rows"),
        "n_cds_records": match_meta.get("n_cds_records"),
        "n_matched_genes": match_meta.get("n_matched_genes"),
        "total_sense_codons": match_meta.get("total_sense_codons"),
        "match_method_counts": match_meta.get("match_method_counts"),
        "n_trna_with_anticodon": row.get("trna_meta", {}).get("n_trna_with_anticodon") if isinstance(row.get("trna_meta"), dict) else None,
    }


def candidate_summaries(retmax: int = 260) -> tuple[list[dict[str, object]], dict[str, object]]:
    anchor_ids, anchor_contact = ncbi.assembly_ids_for_accessions(ANCHOR_ASSEMBLY_ACCESSIONS)
    ids, search_contact = ncbi.assembly_search_ids(retmax=retmax)
    summaries, summary_contact = ncbi.assembly_summaries(list(dict.fromkeys(anchor_ids + ids)))
    by_taxid: dict[str, dict[str, object]] = {}
    for row in summaries:
        taxid = str(row.get("taxid") or "")
        if taxid and taxid not in by_taxid and row.get("assembly_status") == "Complete Genome":
            by_taxid[taxid] = row
    return list(by_taxid.values()), {
        "anchor_accession_search": anchor_contact,
        "assembly_search": search_contact,
        "assembly_summary": summary_contact,
    }


def build_fetch_probe(force_refresh: bool = True, min_species: int = MIN_SPECIES) -> dict[str, object]:
    if PROBE_CACHE_PATH.exists() and PANEL_CACHE_PATH.exists() and not force_refresh:
        return json.loads(PROBE_CACHE_PATH.read_text(encoding="utf-8"))

    paxdb_taxids, paxdb_index_contact = paxdb_species_index()
    summaries, source_status = candidate_summaries(retmax=260)
    attempts: list[dict[str, object]] = []
    usable: list[dict[str, object]] = []
    seen_genera: set[str] = set()
    for summary in summaries:
        if len(attempts) >= 40 and len(usable) >= min_species:
            break
        if str(summary.get("taxid", "")) not in paxdb_taxids:
            continue
        genus = str(summary.get("genus") or "")
        if genus in seen_genera:
            continue
        row = fetch_species_payload(summary, paxdb_taxids)
        attempts.append(row)
        if row.get("ok_expr"):
            seen_genera.add(genus)
            usable.append(row)
        if len(usable) >= min_species:
            break
        time.sleep(NCBI_DELAY_SECONDS)

    panel = {
        "generated_at": now_iso(),
        "provenance": {
            "paxdb": "PaxDB v6 WHOLE_ORGANISM integrated abundance files",
            "cds": "NCBI RefSeq cds_from_genomic.fna.gz",
            "trna": "NCBI genomic.gff.gz tRNA anticodon annotations with GBFF fallback",
            "string_aliases": "STRING protein.aliases.v12.0",
            "string_sequences": "STRING protein.sequences.v12.0 exact protein sequence fallback",
            "not_window6": True,
            "not_causal_proof": True,
            "b1_expression_leakage": "B1 is built only from the frozen standard-code H(3,4) first-order characters plus sense restriction and synonymous mean removal.",
        },
        "sense_codon_order_rna": ncbi.sense_codon_order_rna(),
        "filters": {
            "min_matched_genes_per_species": MIN_MATCHED_GENES,
            "min_sense_codons_per_species": MIN_SENSE_CODONS,
            "min_species": min_species,
            "translation_tables_allowed": [1, 11],
            "paxdb_dataset": "WHOLE_ORGANISM-integrated",
            "one_species_per_genus": True,
        },
        "organisms": [
            {
                "assembly_accession": row["assembly_accession"],
                "organism": row["organism"],
                "species_name": row["species_name"],
                "genus": row["genus"],
                "taxid": row["taxid"],
                "transl_table": row["transl_table"],
                "ftp_path_refseq": row["ftp_path_refseq"],
                "match_meta": row["match_meta"],
                "cds_meta": row["cds_meta"],
                "trna_meta": row["trna_meta"],
                "trna_anticodon_counts_rna": row["trna_anticodon_counts_rna"],
                "matched_genes": row["matched_genes"],
            }
            for row in usable
        ],
        "n_species": len(usable),
        "n_genera": len({str(row["genus"]) for row in usable}),
        "n_matched_genes_total": sum(int(row["match_meta"]["n_matched_genes"]) for row in usable),
        "n_sense_codons_total": sum(int(row["match_meta"]["total_sense_codons"]) for row in usable),
        "cache_path": str(PANEL_CACHE_PATH),
    }
    final = {
        "generated_at": now_iso(),
        "status": "fetchable" if len(usable) >= min_species else "needs_external",
        "reason": (
            "PaxDB abundance rows matched RefSeq CDS records above the preregistered thresholds"
            if len(usable) >= min_species
            else "yield audit found too few species with >=800 abundance-CDS matches and >=200k sense codons"
        ),
        "source_status": {**source_status, "paxdb_species_index": paxdb_index_contact},
        "fetchability_rule": panel["filters"],
        "attempts": [compact_attempt(row) for row in attempts],
        "usable_species": [compact_attempt(row) for row in usable],
        "n_usable": len(usable),
        "n_usable_genera": panel["n_genera"],
        "n_matched_genes_total": panel["n_matched_genes_total"],
        "n_sense_codons_total": panel["n_sense_codons_total"],
        "panel_cache_path": str(PANEL_CACHE_PATH),
        "probe_cache_path": str(PROBE_CACHE_PATH),
    }
    PROBE_CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    PROBE_CACHE_PATH.write_text(json.dumps(final, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    PANEL_CACHE_PATH.write_text(json.dumps(panel, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return final


def main() -> None:
    panel = build_fetch_probe(force_refresh=True)
    for row in panel["attempts"]:
        print(json.dumps({"source": "paxdb_refseq_expression_join", **row}, ensure_ascii=True, sort_keys=True))
    final = {
        "status": panel["status"],
        "reason": panel["reason"],
        "fetch_probe": {
            "n_usable": panel["n_usable"],
            "n_usable_genera": panel["n_usable_genera"],
            "n_matched_genes_total": panel["n_matched_genes_total"],
            "n_sense_codons_total": panel["n_sense_codons_total"],
            "usable_species": panel["usable_species"],
            "attempts": panel["attempts"],
            "panel_cache_path": panel["panel_cache_path"],
            "probe_cache_path": panel["probe_cache_path"],
        },
    }
    print(json.dumps(final, ensure_ascii=True, sort_keys=True, separators=(",", ":")))
    sys.exit(0 if panel["status"] == "fetchable" else 3)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Fetch probe for codon-E1/tRNA decoding-supply data.

Only numeric CDS codon counts and numeric tRNA anticodon copy counts are usable.
The probe is biology-internal: it is not Window6 forcing and it does not claim
causal closure.
"""
from __future__ import annotations

from collections import Counter
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
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any


BASES_RNA = ("U", "C", "A", "G")
BASES_DNA = ("T", "C", "A", "G")
NCBI_DELAY_SECONDS = 0.34
USER_AGENT = "codon-e1-trna-decoding-supply-orientation"
MIN_PROBE_GENOMES = 6
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
)

EXPERIMENT_DIR = Path(__file__).resolve().parent
REPO_ROOT = EXPERIMENT_DIR.parents[2]
PROBE_CACHE_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "codon_e1_trna_decoding_supply_fetch_probe.json"
)

CODON_TO_AA = {
    "UUU": "F", "UUC": "F", "UUA": "L", "UUG": "L",
    "UCU": "S", "UCC": "S", "UCA": "S", "UCG": "S",
    "UAU": "Y", "UAC": "Y", "UAA": "*", "UAG": "*",
    "UGU": "C", "UGC": "C", "UGA": "*", "UGG": "W",
    "CUU": "L", "CUC": "L", "CUA": "L", "CUG": "L",
    "CCU": "P", "CCC": "P", "CCA": "P", "CCG": "P",
    "CAU": "H", "CAC": "H", "CAA": "Q", "CAG": "Q",
    "CGU": "R", "CGC": "R", "CGA": "R", "CGG": "R",
    "AUU": "I", "AUC": "I", "AUA": "I", "AUG": "M",
    "ACU": "T", "ACC": "T", "ACA": "T", "ACG": "T",
    "AAU": "N", "AAC": "N", "AAA": "K", "AAG": "K",
    "AGU": "S", "AGC": "S", "AGA": "R", "AGG": "R",
    "GUU": "V", "GUC": "V", "GUA": "V", "GUG": "V",
    "GCU": "A", "GCC": "A", "GCA": "A", "GCG": "A",
    "GAU": "D", "GAC": "D", "GAA": "E", "GAG": "E",
    "GGU": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}

AA3_TO_1 = {
    "Ala": "A", "Arg": "R", "Asn": "N", "Asp": "D", "Cys": "C",
    "Gln": "Q", "Glu": "E", "Gly": "G", "His": "H", "Ile": "I",
    "Leu": "L", "Lys": "K", "Met": "M", "Phe": "F", "Pro": "P",
    "Ser": "S", "Thr": "T", "Trp": "W", "Tyr": "Y", "Val": "V",
}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def codon_order_rna() -> list[str]:
    return ["".join(parts) for parts in __import__("itertools").product(BASES_RNA, repeat=3)]


def sense_codon_order_rna() -> list[str]:
    return [codon for codon in codon_order_rna() if CODON_TO_AA[codon] != "*"]


def genus_from_species(species: str, organism: str) -> str:
    source = species or organism
    token = re.sub(r"[^A-Za-z].*$", "", source.strip())
    return token.lower() if token else "unknown"


def fetch_bytes(url: str, timeout: int = 60, attempts: int = 3) -> tuple[bytes, dict[str, object]]:
    last_error = ""
    for attempt in range(1, attempts + 1):
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
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
        time.sleep(NCBI_DELAY_SECONDS * attempt * 2.0)
    return b"", {"url": url, "reachable": False, "blocked": True, "error": last_error or "fetch_failed"}


def fetch_text(url: str, timeout: int = 60, attempts: int = 3) -> tuple[str, dict[str, object]]:
    payload, contact = fetch_bytes(url, timeout=timeout, attempts=attempts)
    if not payload:
        return "", contact
    return payload.decode("utf-8", "replace"), contact


def ncbi_url(endpoint: str, params: dict[str, object]) -> str:
    return f"https://eutils.ncbi.nlm.nih.gov/entrez/eutils/{endpoint}.fcgi?{urllib.parse.urlencode(params)}"


def assembly_search_ids(retmax: int = 80) -> tuple[list[str], dict[str, object]]:
    term = '((Bacteria[Organism] OR Archaea[Organism]) AND "Complete Genome"[Assembly Status])'
    url = ncbi_url("esearch", {"db": "assembly", "term": term, "retmax": retmax, "sort": "organism"})
    text, contact = fetch_text(url, timeout=45)
    if not text:
        return [], contact
    try:
        root = ET.fromstring(text)
    except ET.ParseError as exc:
        contact["parse_error"] = str(exc)
        return [], contact
    ids = [node.text for node in root.findall(".//Id") if node.text]
    contact["count"] = root.findtext("Count")
    contact["n_ids"] = len(ids)
    time.sleep(NCBI_DELAY_SECONDS)
    return ids, contact


def assembly_ids_for_accessions(accessions: tuple[str, ...]) -> tuple[list[str], dict[str, object]]:
    ids: list[str] = []
    contacts: list[dict[str, object]] = []
    for accession in accessions:
        url = ncbi_url("esearch", {"db": "assembly", "term": accession, "retmax": 3})
        text, contact = fetch_text(url, timeout=45)
        contact["assembly_accession_query"] = accession
        contacts.append(contact)
        if text:
            try:
                root = ET.fromstring(text)
                ids.extend(node.text for node in root.findall(".//Id") if node.text)
            except ET.ParseError as exc:
                contact["parse_error"] = str(exc)
        time.sleep(NCBI_DELAY_SECONDS)
    return ids, {
        "reachable": any(item.get("reachable") for item in contacts),
        "blocked": not any(item.get("reachable") for item in contacts),
        "n_ids": len(ids),
        "contacts": contacts,
    }


def assembly_summaries(ids: list[str]) -> tuple[list[dict[str, object]], dict[str, object]]:
    if not ids:
        return [], {"reachable": False, "blocked": True, "error": "no_assembly_ids"}
    rows: list[dict[str, object]] = []
    contacts: list[dict[str, object]] = []
    for offset in range(0, len(ids), 20):
        batch = ids[offset : offset + 20]
        url = ncbi_url("esummary", {"db": "assembly", "id": ",".join(batch), "report": "full"})
        text, contact = fetch_text(url, timeout=90)
        contacts.append(contact)
        if not text:
            continue
        try:
            root = ET.fromstring(text)
        except ET.ParseError as exc:
            contact["parse_error"] = str(exc)
            continue
        for node in root.findall(".//DocumentSummary"):
            ftp = node.findtext("FtpPath_RefSeq") or ""
            accession = node.findtext("AssemblyAccession") or ""
            organism = node.findtext("Organism") or ""
            species = node.findtext("SpeciesName") or organism
            status = node.findtext("AssemblyStatus") or ""
            taxid = node.findtext("Taxid") or ""
            if not ftp or not accession.startswith("GCF_"):
                continue
            rows.append(
                {
                    "assembly_accession": accession,
                    "assembly_name": node.findtext("AssemblyName") or "",
                    "assembly_status": status,
                    "organism": organism,
                    "species_name": species,
                    "genus": genus_from_species(species, organism),
                    "taxid": taxid,
                    "ftp_path_refseq": ftp,
                }
            )
        time.sleep(NCBI_DELAY_SECONDS)
    contact = {
        "reachable": any(item.get("reachable") for item in contacts),
        "blocked": not any(item.get("reachable") for item in contacts),
        "n_batches": len(contacts),
        "n_summaries": len(rows),
        "contacts": contacts,
    }
    return rows, contact


def https_ftp_path(ftp_path: str) -> str:
    if ftp_path.startswith("ftp://"):
        return "https://" + ftp_path[len("ftp://") :]
    return ftp_path


def fetch_assembly_file(ftp_path: str, suffix: str) -> tuple[str, dict[str, object]]:
    base = https_ftp_path(ftp_path).rstrip("/")
    name = base.rsplit("/", 1)[-1]
    url = f"{base}/{name}_{suffix}"
    payload, contact = fetch_bytes(url, timeout=90)
    time.sleep(NCBI_DELAY_SECONDS)
    if not payload:
        return "", contact
    try:
        text = gzip.decompress(payload).decode("utf-8", "replace")
    except Exception as exc:
        contact["decompress_error"] = f"{type(exc).__name__}:{exc}"
        return "", contact
    contact["decompressed_chars"] = len(text)
    return text, contact


def parse_fasta_records(text: str) -> list[tuple[str, str]]:
    records: list[tuple[str, str]] = []
    header = ""
    chunks: list[str] = []
    for line in text.splitlines():
        if line.startswith(">"):
            if header:
                records.append((header, "".join(chunks).upper()))
            header = line[1:].strip()
            chunks = []
        else:
            chunks.append(re.sub(r"[^A-Za-z]", "", line))
    if header:
        records.append((header, "".join(chunks).upper()))
    return records


def count_cds_codons(text: str) -> tuple[dict[str, int], dict[str, object]]:
    counts = {codon: 0 for codon in sense_codon_order_rna()}
    n_records = 0
    n_accepted = 0
    skipped_length = 0
    skipped_ambiguous = 0
    skipped_internal_stop = 0
    stop_codons = {codon.replace("U", "T") for codon, aa in CODON_TO_AA.items() if aa == "*"}
    for _header, seq in parse_fasta_records(text):
        n_records += 1
        if len(seq) < 3 or len(seq) % 3 != 0:
            skipped_length += 1
            continue
        if any(base not in BASES_DNA for base in seq):
            skipped_ambiguous += 1
            continue
        codons = [seq[offset : offset + 3] for offset in range(0, len(seq), 3)]
        if codons and codons[-1] in stop_codons:
            codons = codons[:-1]
        if any(codon in stop_codons for codon in codons):
            skipped_internal_stop += 1
            continue
        n_accepted += 1
        for codon_dna in codons:
            codon = codon_dna.replace("T", "U")
            if codon in counts:
                counts[codon] += 1
    meta = {
        "n_cds_records": n_records,
        "n_complete_cds": n_accepted,
        "skipped_length": skipped_length,
        "skipped_ambiguous": skipped_ambiguous,
        "skipped_internal_stop": skipped_internal_stop,
        "total_sense_codons": int(sum(counts.values())),
    }
    return counts, meta


def parse_gff_attributes(raw: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for part in raw.split(";"):
        if not part:
            continue
        if "=" not in part:
            continue
        key, value = part.split("=", 1)
        result[urllib.parse.unquote(key)] = urllib.parse.unquote(value)
    return result


def normalize_anticodon(raw: str) -> str | None:
    seq = raw.strip().upper().replace("T", "U")
    seq = re.sub(r"[^ACGUI]", "", seq)
    return seq if len(seq) == 3 else None


def parse_anticodon_from_attrs(attrs: dict[str, str]) -> tuple[str | None, str | None]:
    joined = ";".join(f"{key}={value}" for key, value in attrs.items())
    seq_match = re.search(r"seq:([A-Za-z]+)", joined)
    if seq_match:
        seq = normalize_anticodon(seq_match.group(1))
        aa_match = re.search(r"aa:([A-Za-z]+)", joined)
        aa = aa_match.group(1).title()[:3] if aa_match else None
        if seq:
            return seq, aa
    note = attrs.get("Note", "") + ";" + attrs.get("product", "")
    note_match = re.search(r"tRNA-(?:initiator\s+)?([A-Za-z]{3})\(([A-Za-z]+)\)", note)
    if note_match:
        seq = normalize_anticodon(note_match.group(2))
        if seq:
            return seq, note_match.group(1).title()
    any_match = re.search(r"\(([ACGTUIacgtui]{3})\)", joined)
    if any_match:
        seq = normalize_anticodon(any_match.group(1))
        if seq:
            return seq, None
    return None, None


def parse_gff_trna_and_tables(text: str) -> tuple[dict[str, int], dict[str, object]]:
    anticodon_counts: Counter[str] = Counter()
    aa_counts: Counter[str] = Counter()
    transl_tables: Counter[str] = Counter()
    n_trna_features = 0
    n_trna_with_anticodon = 0
    ignored_nonstandard_aa = 0
    for line in text.splitlines():
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) < 9:
            continue
        feature = fields[2]
        attrs = parse_gff_attributes(fields[8])
        if feature == "CDS" and "transl_table" in attrs:
            transl_tables[str(attrs["transl_table"])] += 1
        if feature != "tRNA":
            continue
        n_trna_features += 1
        anticodon, aa3 = parse_anticodon_from_attrs(attrs)
        if not anticodon:
            continue
        if aa3 and aa3 not in AA3_TO_1:
            ignored_nonstandard_aa += 1
            continue
        n_trna_with_anticodon += 1
        anticodon_counts[anticodon] += 1
        if aa3:
            aa_counts[AA3_TO_1[aa3]] += 1
    meta = {
        "n_trna_features": n_trna_features,
        "n_trna_with_anticodon": n_trna_with_anticodon,
        "ignored_nonstandard_aa": ignored_nonstandard_aa,
        "transl_table_counts": dict(sorted(transl_tables.items(), key=lambda item: int(item[0]))),
        "n_anticodon_classes": len(anticodon_counts),
        "aa_counts": dict(sorted(aa_counts.items())),
    }
    return dict(sorted(anticodon_counts.items())), meta


def parse_genbank_trna_anticodons(text: str) -> tuple[dict[str, int], dict[str, object]]:
    anticodon_counts: Counter[str] = Counter()
    aa_counts: Counter[str] = Counter()
    n_trna_features = 0
    n_trna_with_anticodon = 0
    blocks = re.findall(r"^     tRNA\s+.*?(?=^     \S|\Z)", text, flags=re.MULTILINE | re.DOTALL)
    for block in blocks:
        n_trna_features += 1
        aa3: str | None = None
        seq: str | None = None
        anticodon_match = re.search(r"/anticodon=\([^\)]*aa:([A-Za-z]+),seq:([A-Za-z]+)\)", block)
        if anticodon_match:
            aa3 = anticodon_match.group(1).title()[:3]
            seq = normalize_anticodon(anticodon_match.group(2))
        if not seq:
            note_match = re.search(r"anticodon\s+([A-Za-z]{3})", block, flags=re.IGNORECASE)
            if note_match:
                seq = normalize_anticodon(note_match.group(1))
        if not aa3:
            product_match = re.search(r"/product=\"tRNA-([A-Za-z]{3})", block)
            if product_match:
                aa3 = product_match.group(1).title()
        if not seq:
            product_match = re.search(r"/product=\"tRNA-(?:initiator\s+)?[A-Za-z]{3}\(([A-Za-z]{3})\)\"", block)
            if product_match:
                seq = normalize_anticodon(product_match.group(1))
        if not seq:
            continue
        if aa3 and aa3 not in AA3_TO_1:
            continue
        n_trna_with_anticodon += 1
        anticodon_counts[seq] += 1
        if aa3:
            aa_counts[AA3_TO_1[aa3]] += 1
    meta = {
        "n_trna_features": n_trna_features,
        "n_trna_with_anticodon": n_trna_with_anticodon,
        "n_anticodon_classes": len(anticodon_counts),
        "aa_counts": dict(sorted(aa_counts.items())),
    }
    return dict(sorted(anticodon_counts.items())), meta


def parse_genbank_transl_tables(text: str) -> dict[str, int]:
    counts: Counter[str] = Counter()
    blocks = re.findall(r"^     CDS\s+.*?(?=^     \S|\Z)", text, flags=re.MULTILINE | re.DOTALL)
    for block in blocks:
        match = re.search(r"/transl_table=(\d+)", block)
        if match:
            counts[match.group(1)] += 1
    return dict(sorted(counts.items(), key=lambda item: int(item[0])))


def sample_counts(counts: dict[str, int], keys: list[str] | None = None, limit: int = 10) -> dict[str, int]:
    if keys is None:
        keys = sorted(counts, key=lambda key: (-counts[key], key))[:limit]
    return {key: int(counts.get(key, 0)) for key in keys[:limit]}


def fetch_assembly_payload(summary: dict[str, object]) -> dict[str, object]:
    ftp_path = str(summary["ftp_path_refseq"])
    gff_text, gff_contact = fetch_assembly_file(ftp_path, "genomic.gff.gz")
    cds_text, cds_contact = fetch_assembly_file(ftp_path, "cds_from_genomic.fna.gz")
    trna_counts, trna_meta = parse_gff_trna_and_tables(gff_text) if gff_text else ({}, {})
    gbff_text = ""
    gbff_contact: dict[str, object] = {"reachable": False, "skipped": True}
    gbff_trna_counts: dict[str, int] = {}
    gbff_trna_meta: dict[str, object] = {}
    gff_table_counts = trna_meta.get("transl_table_counts", {}) if isinstance(trna_meta, dict) else {}
    if int(trna_meta.get("n_trna_with_anticodon", 0)) == 0 or not gff_table_counts:
        gbff_text, gbff_contact = fetch_assembly_file(ftp_path, "genomic.gbff.gz")
        gbff_trna_counts, gbff_trna_meta = parse_genbank_trna_anticodons(gbff_text) if gbff_text else ({}, {})
        if int(gbff_trna_meta.get("n_trna_with_anticodon", 0)) > 0:
            trna_counts = gbff_trna_counts
            trna_meta = {**gbff_trna_meta, "source": "genomic.gbff.gz"}
    else:
        trna_meta = {**trna_meta, "source": "genomic.gff.gz"}
    codon_counts, cds_meta = count_cds_codons(cds_text) if cds_text else ({}, {})
    table_counts = trna_meta.get("transl_table_counts", {}) if isinstance(trna_meta, dict) else {}
    if not table_counts and gbff_text:
        table_counts = parse_genbank_transl_tables(gbff_text)
        trna_meta = {**trna_meta, "transl_table_counts": table_counts}
    observed_tables = sorted(int(key) for key in table_counts) if table_counts else []
    ok_tables = len(observed_tables) == 1 and observed_tables[0] in {1, 11}
    ok = (
        bool(gff_contact.get("reachable"))
        and bool(cds_contact.get("reachable"))
        and ok_tables
        and int(cds_meta.get("n_complete_cds", 0)) >= 300
        and int(cds_meta.get("total_sense_codons", 0)) > 0
        and int(trna_meta.get("n_trna_with_anticodon", 0)) > 0
    )
    return {
        **summary,
        "reachable": bool(gff_contact.get("reachable")) and bool(cds_contact.get("reachable")),
        "blocked": not (bool(gff_contact.get("reachable")) and bool(cds_contact.get("reachable"))),
        "ok_numeric": bool(ok),
        "transl_table": observed_tables[0] if ok_tables else None,
        "gff_contact": gff_contact,
        "gbff_contact": gbff_contact,
        "cds_contact": cds_contact,
        "cds_meta": cds_meta,
        "trna_meta": trna_meta,
        "gff_trna_meta": parse_gff_trna_and_tables(gff_text)[1] if gff_text else {},
        "gbff_trna_meta": gbff_trna_meta,
        "codon_counts_rna": codon_counts,
        "trna_anticodon_counts_rna": trna_counts,
        "sample_codon_counts": sample_counts(codon_counts, sense_codon_order_rna()[:10]),
        "sample_trna_anticodon_counts": sample_counts(trna_counts),
    }


def candidate_summaries(retmax: int = 160) -> tuple[list[dict[str, object]], dict[str, object]]:
    anchor_ids, anchor_contact = assembly_ids_for_accessions(ANCHOR_ASSEMBLY_ACCESSIONS)
    ids, search_contact = assembly_search_ids(retmax=retmax)
    summaries, summary_contact = assembly_summaries(list(dict.fromkeys(anchor_ids + ids)))
    by_genus: dict[str, dict[str, object]] = {}
    for row in summaries:
        genus = str(row.get("genus") or "")
        if genus and genus not in by_genus and row.get("assembly_status") == "Complete Genome":
            by_genus[genus] = row
    return list(by_genus.values()), {
        "anchor_accession_search": anchor_contact,
        "assembly_search": search_contact,
        "assembly_summary": summary_contact,
    }


def build_fetch_probe(force_refresh: bool = True, min_genomes: int = MIN_PROBE_GENOMES) -> dict[str, object]:
    summaries, source_status = candidate_summaries(retmax=160)
    attempts: list[dict[str, object]] = []
    usable: list[dict[str, object]] = []
    for summary in summaries:
        row = fetch_assembly_payload(summary)
        attempts.append(row)
        if row["ok_numeric"]:
            usable.append(row)
        if len(usable) >= min_genomes and len(attempts) >= min_genomes:
            break
    panel = {
        "generated_at": now_iso(),
        "status": "fetchable" if len(usable) >= min_genomes else "needs_external",
        "reason": (
            "RefSeq assembly FTP yielded numeric CDS codon counts and tRNA anticodon copy counts"
            if len(usable) >= min_genomes
            else "fewer than the required complete RefSeq genomes yielded both numeric CDS codon counts and tRNA anticodon copy counts"
        ),
        "source_status": source_status,
        "fetchability_rule": {
            "min_probe_genomes": min_genomes,
            "assembly_level": "Complete Genome",
            "transl_table_allowed": [1, 11],
            "min_complete_cds": 300,
            "numeric_cds_counts_required": True,
            "numeric_trna_anticodon_counts_required": True,
            "not_window6": True,
            "not_causal_closure": True,
        },
        "attempts": attempts,
        "usable_assemblies": [
            {
                "assembly_accession": row["assembly_accession"],
                "organism": row["organism"],
                "species_name": row["species_name"],
                "genus": row["genus"],
                "transl_table": row["transl_table"],
                "n_complete_cds": row["cds_meta"]["n_complete_cds"],
                "total_sense_codons": row["cds_meta"]["total_sense_codons"],
                "n_trna_with_anticodon": row["trna_meta"]["n_trna_with_anticodon"],
                "sample_codon_counts": row["sample_codon_counts"],
                "sample_trna_anticodon_counts": row["sample_trna_anticodon_counts"],
            }
            for row in usable
        ],
        "n_usable": len(usable),
        "n_usable_genera": len({str(row["genus"]) for row in usable}),
        "cache_path": str(PROBE_CACHE_PATH),
    }
    PROBE_CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    PROBE_CACHE_PATH.write_text(json.dumps(panel, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return panel


def compact_attempt(row: dict[str, object]) -> dict[str, object]:
    return {
        "assembly_accession": row.get("assembly_accession"),
        "organism": row.get("organism"),
        "genus": row.get("genus"),
        "reachable": row.get("reachable"),
        "blocked": row.get("blocked"),
        "ok_numeric": row.get("ok_numeric"),
        "transl_table": row.get("transl_table"),
        "n_complete_cds": row.get("cds_meta", {}).get("n_complete_cds") if isinstance(row.get("cds_meta"), dict) else None,
        "total_sense_codons": row.get("cds_meta", {}).get("total_sense_codons") if isinstance(row.get("cds_meta"), dict) else None,
        "n_trna_with_anticodon": row.get("trna_meta", {}).get("n_trna_with_anticodon") if isinstance(row.get("trna_meta"), dict) else None,
        "sample_codon_counts": row.get("sample_codon_counts"),
        "sample_trna_anticodon_counts": row.get("sample_trna_anticodon_counts"),
    }


def main() -> None:
    panel = build_fetch_probe(force_refresh=True)
    for row in panel["attempts"]:
        assert isinstance(row, dict)
        print(json.dumps({"source": "refseq_assembly_ftp", **compact_attempt(row)}, ensure_ascii=True, sort_keys=True))
    final = {
        "status": panel["status"],
        "reason": panel["reason"],
        "fetch_probe": {
            "n_usable": panel["n_usable"],
            "n_usable_genera": panel["n_usable_genera"],
            "cache_path": panel["cache_path"],
            "usable_assemblies": panel["usable_assemblies"],
            "source_status": panel["source_status"],
        },
    }
    print(json.dumps(final, ensure_ascii=True, sort_keys=True, separators=(",", ":")))
    sys.exit(0 if panel["status"] == "fetchable" else 3)


if __name__ == "__main__":
    main()

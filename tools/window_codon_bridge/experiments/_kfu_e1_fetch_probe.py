#!/usr/bin/env python3
"""Fetch probe for codon-E1 known-force-union irreducibility data."""
from __future__ import annotations

from collections import Counter
from datetime import datetime, timezone
import gzip
import hashlib
import json
import os
import re
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any

import _e1_trna_fetch_probe as trna_probe
import _mut_e1_fetch_probe as code_probe


EXPERIMENT_ID = "codon_e1_known_force_union_fetch_probe"
USER_AGENT = "codon-e1-known-force-union-irreducibility"
NCBI_DELAY_SECONDS = 0.34
MIN_HEG_GENES = 20
BACTERIA_FLOOR = 12
ARCHAEA_FLOOR = 12
EUKARYOTA_FLOOR = 8
GENOME_FETCH_TIMEOUT = int(os.environ.get("CODON_E1_KFU_GENOME_TIMEOUT", "20"))
SUMMARY_FETCH_TIMEOUT = int(os.environ.get("CODON_E1_KFU_SUMMARY_TIMEOUT", "12"))
FETCH_DEADLINE_SECONDS = float(os.environ.get("CODON_E1_KFU_FETCH_DEADLINE", "900"))
MAX_SUPPLY_ATTEMPTS = int(os.environ.get("CODON_E1_KFU_MAX_SUPPLY_ATTEMPTS", "30"))
MAX_ARCHAEA_ATTEMPTS = int(os.environ.get("CODON_E1_KFU_MAX_ARCHAEA_ATTEMPTS", "24"))
MAX_EUK_ATTEMPTS = int(os.environ.get("CODON_E1_KFU_MAX_EUK_ATTEMPTS", "8"))

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[2]
PANEL_CACHE_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "codon_e1_known_force_union_panel.json"
)
GENOME_CACHE_DIR = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "codon_e1_known_force_union_genomes"
)
SUPPLY_PANEL_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "codon_e1_trna_decoding_supply_orientation_panel.json"
)

EUKARYOTA_ROSTER = (
    ("GCF_000146045.2", "Saccharomyces cerevisiae", "saccharomyces"),
    ("GCF_000002945.1", "Schizosaccharomyces pombe", "schizosaccharomyces"),
    ("GCF_000182965.3", "Candida albicans", "candida"),
    ("GCF_000002525.2", "Yarrowia lipolytica", "yarrowia"),
    ("GCF_000002515.2", "Kluyveromyces lactis", "kluyveromyces"),
    ("GCF_000091025.4", "Ashbya gossypii", "ashbya"),
    ("GCF_000004695.1", "Dictyostelium discoideum", "dictyostelium"),
    ("GCF_000002765.6", "Plasmodium falciparum", "plasmodium"),
    ("GCF_000002595.2", "Chlamydomonas reinhardtii", "chlamydomonas"),
    ("GCF_000149405.2", "Thalassiosira pseudonana", "thalassiosira"),
)

ARCHAEA_ROSTER = (
    ("GCF_000007305.1", "Pyrococcus furiosus DSM 3638", "pyrococcus"),
    ("GCF_000091665.1", "Methanocaldococcus jannaschii DSM 2661", "methanocaldococcus"),
    ("GCF_000008265.1", "Picrophilus oshimae DSM 9789", "picrophilus"),
    ("GCF_000012285.1", "Sulfolobus acidocaldarius DSM 639", "sulfolobus"),
    ("GCF_000007005.1", "Sulfolobus solfataricus P2", "sulfolobus"),
    ("GCF_000006805.1", "Halobacterium salinarum NRC-1", "halobacterium"),
    ("GCF_000025685.1", "Haloferax volcanii DS2", "haloferax"),
    ("GCF_000009965.1", "Thermococcus kodakarensis KOD1", "thermococcus"),
    ("GCF_000008665.1", "Archaeoglobus fulgidus DSM 4304", "archaeoglobus"),
    ("GCF_000011585.1", "Methanococcus maripaludis S2", "methanococcus"),
    ("GCF_000007225.1", "Pyrobaculum aerophilum str. IM2", "pyrobaculum"),
    ("GCF_000011125.1", "Aeropyrum pernix K1", "aeropyrum"),
    ("GCF_000007345.1", "Methanosarcina acetivorans C2A", "methanosarcina"),
    ("GCF_000007065.1", "Methanosarcina mazei Go1", "methanosarcina"),
    ("GCF_000016525.1", "Methanobrevibacter smithii ATCC 35061", "methanobrevibacter"),
    ("GCF_000008085.1", "Nanoarchaeum equitans Kin4-M", "nanoarchaeum"),
    ("GCF_000012545.1", "Thermoplasma acidophilum DSM 1728", "thermoplasma"),
    ("GCF_000024265.1", "Ferroplasma acidarmanus fer1", "ferroplasma"),
    ("GCF_000018465.1", "Methanospirillum hungatei JF-1", "methanospirillum"),
    ("GCF_000015225.1", "Methanococcoides burtonii DSM 6242", "methanococcoides"),
)

ARCHAEA_HINTS = {
    "pyrococcus",
    "picrophilus",
    "methanocaldococcus",
    "methanococcus",
    "halobacterium",
    "sulfolobus",
    "thermococcus",
    "archaeoglobus",
    "haloferax",
    "pyrobaculum",
    "aeropyrum",
    "methanosarcina",
    "methanobrevibacter",
    "nanoarchaeum",
    "thermoplasma",
    "ferroplasma",
    "methanospirillum",
    "methanococcoides",
}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def codon_order_rna() -> list[str]:
    return code_probe.codon_order_rna()


def sense_codon_order_rna() -> list[str]:
    return code_probe.sense_codon_order_rna()


def zero_counts() -> dict[str, int]:
    return {codon: 0 for codon in sense_codon_order_rna()}


def fetch_bytes(url: str, timeout: int = 90, attempts: int = 3) -> tuple[bytes, dict[str, object]]:
    last_error = "fetch_failed"
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
        except Exception as exc:  # pragma: no cover - network boundary
            last_error = f"{type(exc).__name__}:{exc}"
        time.sleep(NCBI_DELAY_SECONDS * attempt * 2.0)
    return b"", {"url": url, "reachable": False, "blocked": True, "error": last_error, "attempts": attempts}


def fetch_text(url: str, timeout: int = 90, attempts: int = 3) -> tuple[str, dict[str, object]]:
    payload, contact = fetch_bytes(url, timeout=timeout, attempts=attempts)
    if not payload:
        return "", contact
    return payload.decode("utf-8", "replace"), contact


def ncbi_url(endpoint: str, params: dict[str, object]) -> str:
    return f"https://eutils.ncbi.nlm.nih.gov/entrez/eutils/{endpoint}.fcgi?{urllib.parse.urlencode(params)}"


def https_ftp_path(ftp_path: str) -> str:
    if ftp_path.startswith("ftp://"):
        return "https://" + ftp_path[len("ftp://") :]
    return ftp_path


def deadline_expired(deadline: float | None) -> bool:
    return deadline is not None and time.monotonic() >= deadline


def assembly_summary_for_accession(accession: str, deadline: float | None = None) -> tuple[dict[str, object] | None, dict[str, object]]:
    if deadline_expired(deadline):
        return None, {"error": "fetch_deadline_exceeded_before_summary"}
    search_url = ncbi_url("esearch", {"db": "assembly", "term": accession, "retmax": 1})
    text, search_contact = fetch_text(search_url, timeout=SUMMARY_FETCH_TIMEOUT, attempts=1)
    if not text:
        return None, {"search": search_contact, "error": "assembly_search_failed"}
    try:
        root = ET.fromstring(text)
    except ET.ParseError as exc:
        return None, {"search": search_contact, "parse_error": str(exc)}
    assembly_id = root.findtext(".//Id")
    if not assembly_id:
        return None, {"search": search_contact, "error": "assembly_id_not_found"}
    time.sleep(NCBI_DELAY_SECONDS)
    if deadline_expired(deadline):
        return None, {"search": search_contact, "error": "fetch_deadline_exceeded_before_summary_detail"}
    summary_url = ncbi_url("esummary", {"db": "assembly", "id": assembly_id, "report": "full"})
    text, summary_contact = fetch_text(summary_url, timeout=SUMMARY_FETCH_TIMEOUT, attempts=1)
    if not text:
        return None, {"search": search_contact, "summary": summary_contact, "error": "assembly_summary_failed"}
    try:
        root = ET.fromstring(text)
    except ET.ParseError as exc:
        return None, {"search": search_contact, "summary": summary_contact, "parse_error": str(exc)}
    node = root.find(".//DocumentSummary")
    if node is None:
        return None, {"search": search_contact, "summary": summary_contact, "error": "document_summary_not_found"}
    ftp = node.findtext("FtpPath_RefSeq") or node.findtext("FtpPath_GenBank") or ""
    if not ftp:
        return None, {"search": search_contact, "summary": summary_contact, "error": "assembly_ftp_not_found"}
    row = {
        "assembly_accession": node.findtext("AssemblyAccession") or accession,
        "organism": node.findtext("Organism") or "",
        "species_name": node.findtext("SpeciesName") or node.findtext("Organism") or "",
        "taxid": node.findtext("Taxid") or "",
        "ftp_path_refseq": ftp,
    }
    return row, {"search": search_contact, "summary": summary_contact}


def assembly_summary_for_search_term(term: str, deadline: float | None = None) -> tuple[dict[str, object] | None, dict[str, object]]:
    if deadline_expired(deadline):
        return None, {"error": "fetch_deadline_exceeded_before_summary"}
    search_url = ncbi_url("esearch", {"db": "assembly", "term": term, "retmax": 8})
    text, search_contact = fetch_text(search_url, timeout=SUMMARY_FETCH_TIMEOUT, attempts=1)
    if not text:
        return None, {"search": search_contact, "error": "assembly_search_failed"}
    try:
        root = ET.fromstring(text)
    except ET.ParseError as exc:
        return None, {"search": search_contact, "parse_error": str(exc)}
    assembly_ids = [node.text for node in root.findall(".//Id") if node.text]
    if not assembly_ids:
        return None, {"search": search_contact, "error": "assembly_id_not_found"}
    time.sleep(NCBI_DELAY_SECONDS)
    if deadline_expired(deadline):
        return None, {"search": search_contact, "error": "fetch_deadline_exceeded_before_summary_detail"}
    summary_url = ncbi_url("esummary", {"db": "assembly", "id": ",".join(assembly_ids), "report": "full"})
    text, summary_contact = fetch_text(summary_url, timeout=SUMMARY_FETCH_TIMEOUT, attempts=1)
    if not text:
        return None, {"search": search_contact, "summary": summary_contact, "error": "assembly_summary_failed"}
    try:
        root = ET.fromstring(text)
    except ET.ParseError as exc:
        return None, {"search": search_contact, "summary": summary_contact, "parse_error": str(exc)}
    candidates = []
    for node in root.findall(".//DocumentSummary"):
        ftp = node.findtext("FtpPath_RefSeq") or node.findtext("FtpPath_GenBank") or ""
        if not ftp:
            continue
        status = (node.findtext("AssemblyStatus") or "").lower()
        category = (node.findtext("RefSeq_category") or "").lower()
        score = 0
        if "complete" in status:
            score += 4
        if category in {"reference genome", "representative genome"}:
            score += 2
        if node.findtext("FtpPath_RefSeq"):
            score += 1
        candidates.append(
            (
                score,
                {
                    "assembly_accession": node.findtext("AssemblyAccession") or "",
                    "organism": node.findtext("Organism") or "",
                    "species_name": node.findtext("SpeciesName") or node.findtext("Organism") or "",
                    "taxid": node.findtext("Taxid") or "",
                    "ftp_path_refseq": ftp,
                },
            )
        )
    if not candidates:
        return None, {"search": search_contact, "summary": summary_contact, "error": "assembly_ftp_not_found"}
    candidates.sort(key=lambda item: item[0], reverse=True)
    return candidates[0][1], {"search": search_contact, "summary": summary_contact, "fallback_term": term}


def assembly_summary_for_roster_entry(accession: str, organism: str, deadline: float | None = None) -> tuple[dict[str, object] | None, dict[str, object]]:
    summary, contact = assembly_summary_for_accession(accession, deadline=deadline)
    if summary is not None:
        return summary, contact
    genus_species = " ".join(organism.split()[:2])
    fallback_term = f'{genus_species}[Organism] AND latest[filter]'
    fallback, fallback_contact = assembly_summary_for_search_term(fallback_term, deadline=deadline)
    return fallback, {"accession_contact": contact, "fallback_contact": fallback_contact}


def cached_assembly_file(ftp_path: str, suffix: str, cache_key: str, deadline: float | None = None) -> tuple[str, dict[str, object]]:
    base = https_ftp_path(ftp_path).rstrip("/")
    name = base.rsplit("/", 1)[-1]
    url = f"{base}/{name}_{suffix}"
    GENOME_CACHE_DIR.mkdir(parents=True, exist_ok=True)
    safe_key = re.sub(r"[^A-Za-z0-9_.-]+", "_", cache_key)
    gz_path = GENOME_CACHE_DIR / f"{safe_key}_{suffix}"
    if gz_path.exists() and gz_path.stat().st_size > 0:
        payload = gz_path.read_bytes()
        source = {
            "url": url,
            "reachable": True,
            "on_disk_cache_hit": True,
            "byte_size": len(payload),
            "sha256": hashlib.sha256(payload).hexdigest(),
        }
    else:
        if deadline_expired(deadline):
            return "", {"url": url, "reachable": False, "blocked": True, "error": "fetch_deadline_exceeded", "cache_path": str(gz_path)}
        payload, source = fetch_bytes(url, timeout=GENOME_FETCH_TIMEOUT, attempts=1)
        time.sleep(NCBI_DELAY_SECONDS)
        if not payload:
            return "", source
        gz_path.write_bytes(payload)
        source = {**source, "on_disk_cache_hit": False, "cache_path": str(gz_path)}
    try:
        if suffix.endswith(".gz"):
            text = gzip.decompress(payload).decode("utf-8", "replace")
        else:
            text = payload.decode("utf-8", "replace")
    except Exception as exc:
        return "", {**source, "decompress_error": f"{type(exc).__name__}:{exc}"}
    return text, {**source, "decompressed_chars": len(text), "cache_path": str(gz_path)}


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


def heg_header(header: str) -> bool:
    lower = header.lower()
    if any(token in lower for token in ("hypothetical", "pseudogene", "pseudo=", "partial=true")):
        return False
    patterns = (
        r"ribosomal protein",
        r"elongation factor (?:tu|g|ts|ef-?tu|ef-?g|ef-?ts)\b",
        r"\bef-tu\b",
        r"\bef-g\b",
        r"\bef-ts\b",
        r"translation initiation factor",
        r"\binitiation factor\b",
        r"peptide chain release factor",
        r"ribosome recycling factor",
        r"\brelease factor\b",
    )
    return any(re.search(pattern, lower) for pattern in patterns)


def count_cds_fasta(text: str, heg_only: bool = False) -> tuple[dict[str, int], dict[str, object]]:
    counts = zero_counts()
    stop_codons = {codon.replace("U", "T") for codon, aa in code_probe.CODON_TO_AA.items() if aa == "*"}
    n_records = 0
    n_accepted = 0
    n_heg_records = 0
    skipped = Counter()
    for header, seq in parse_fasta_records(text):
        n_records += 1
        is_heg = heg_header(header)
        if heg_only and not is_heg:
            continue
        if is_heg:
            n_heg_records += 1
        if len(seq) < 3 or len(seq) % 3 != 0:
            skipped["bad_length"] += 1
            continue
        if any(base not in trna_probe.BASES_DNA for base in seq):
            skipped["ambiguous"] += 1
            continue
        codons = [seq[offset : offset + 3] for offset in range(0, len(seq), 3)]
        if codons and codons[-1] in stop_codons:
            codons = codons[:-1]
        if any(codon in stop_codons for codon in codons):
            skipped["internal_stop"] += 1
            continue
        n_accepted += 1
        for codon_dna in codons:
            codon = codon_dna.replace("T", "U")
            if codon in counts:
                counts[codon] += 1
    return counts, {
        "n_cds_records": n_records,
        "n_complete_cds": n_accepted,
        "n_heg_records": n_heg_records,
        "total_sense_codons": int(sum(counts.values())),
        "skipped": dict(sorted(skipped.items())),
        "heg_rule": "annotation product/header ribosomal proteins plus translation factors, excluding pseudo/hypothetical",
    }


def domain_for_supply_row(row: dict[str, object]) -> str:
    genus = str(row.get("genus") or "").lower()
    organism = str(row.get("organism") or "").lower()
    if genus in ARCHAEA_HINTS or "archaea" in organism or "euryarchae" in organism:
        return "Archaea"
    return "Bacteria"


def row_has_numeric_counts(row: dict[str, object]) -> bool:
    sense = sense_codon_order_rna()
    codon_counts = row.get("codon_counts_rna")
    trna_counts = row.get("trna_anticodon_counts_rna")
    if not isinstance(codon_counts, dict) or not isinstance(trna_counts, dict):
        return False
    return sum(int(codon_counts.get(codon, 0)) for codon in sense) > 0 and sum(int(v) for v in trna_counts.values()) > 0


def build_supply_rows(max_rows: int = MAX_SUPPLY_ATTEMPTS, deadline: float | None = None) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    if not SUPPLY_PANEL_PATH.exists():
        return [], [{"source": str(SUPPLY_PANEL_PATH), "error": "supply_panel_missing"}]
    payload = json.loads(SUPPLY_PANEL_PATH.read_text(encoding="utf-8"))
    attempts: list[dict[str, object]] = []
    usable: list[dict[str, object]] = []
    for base_row in payload.get("organisms", [])[:max_rows]:
        if deadline_expired(deadline):
            attempts.append({"source": str(SUPPLY_PANEL_PATH), "ok": False, "error": "fetch_deadline_exceeded"})
            break
        if not isinstance(base_row, dict) or not row_has_numeric_counts(base_row):
            continue
        accession = str(base_row.get("assembly_accession") or "")
        ftp_path = str(base_row.get("ftp_path_refseq") or "")
        cds_text, cds_contact = cached_assembly_file(ftp_path, "cds_from_genomic.fna.gz", accession, deadline=deadline) if ftp_path else ("", {})
        gbff_text, gbff_contact = cached_assembly_file(ftp_path, "genomic.gbff.gz", accession, deadline=deadline) if ftp_path else ("", {})
        all_counts, all_meta = count_cds_fasta(cds_text, heg_only=False) if cds_text else (zero_counts(), {})
        heg_counts, heg_meta = count_cds_fasta(cds_text, heg_only=True) if cds_text else (zero_counts(), {})
        trna_counts, trna_meta = trna_probe.parse_genbank_trna_anticodons(gbff_text) if gbff_text else ({}, {})
        row = {
            "organism": base_row.get("organism"),
            "genus": str(base_row.get("genus") or "").lower(),
            "domain": domain_for_supply_row(base_row),
            "assembly_accession": accession,
            "taxid": base_row.get("taxid"),
            "transl_table": int(base_row.get("transl_table") or 11),
            "codon_counts_rna": all_counts,
            "all_codon_counts_rna": all_counts,
            "trna_anticodon_counts_rna": {str(k): int(v) for k, v in trna_counts.items()},
            "heg_codon_counts_rna": heg_counts,
            "cds_meta": all_meta,
            "heg_meta": heg_meta,
            "trna_meta": trna_meta,
            "annotation_contacts": {"cds_from_genomic": cds_contact, "genomic_gbff": gbff_contact},
        }
        ok = (
            sum(all_counts.values()) > 0
            and sum(int(v) for v in trna_counts.values()) > 0
            and int(heg_meta.get("n_heg_records", 0)) >= MIN_HEG_GENES
        )
        attempts.append(
            {
                "assembly_accession": accession,
                "organism": row["organism"],
                "genus": row["genus"],
                "domain": row["domain"],
                "n_cds_records": all_meta.get("n_cds_records"),
                "n_trna_with_anticodon": trna_meta.get("n_trna_with_anticodon"),
                "n_heg_records": heg_meta.get("n_heg_records"),
                "total_heg_sense_codons": heg_meta.get("total_sense_codons"),
                "ok": ok,
            }
        )
        if ok:
            usable.append(row)
    return usable, attempts


def build_refseq_roster_rows(
    roster: tuple[tuple[str, str, str], ...],
    domain: str,
    transl_table: int,
    max_rows: int,
    deadline: float | None = None,
) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    usable: list[dict[str, object]] = []
    attempts: list[dict[str, object]] = []
    seen_genera: set[str] = set()
    for accession, organism_hint, genus_hint in roster[:max_rows]:
        if deadline_expired(deadline):
            attempts.append({"assembly_accession": accession, "organism": organism_hint, "genus": genus_hint, "ok": False, "error": "fetch_deadline_exceeded"})
            break
        summary, summary_contact = assembly_summary_for_roster_entry(accession, organism_hint, deadline=deadline)
        if summary is None:
            attempts.append({"assembly_accession": accession, "organism": organism_hint, "genus": genus_hint, "domain": domain, "ok": False, "contact": summary_contact})
            continue
        genus = genus_hint.lower()
        if genus in seen_genera:
            attempts.append({"assembly_accession": accession, "organism": summary.get("organism") or organism_hint, "genus": genus, "domain": domain, "ok": False, "error": "duplicate_genus"})
            continue
        ftp_path = str(summary["ftp_path_refseq"])
        cache_key = str(summary.get("assembly_accession") or accession)
        cds_text, cds_contact = cached_assembly_file(ftp_path, "cds_from_genomic.fna.gz", cache_key, deadline=deadline)
        gbff_text, gbff_contact = cached_assembly_file(ftp_path, "genomic.gbff.gz", cache_key, deadline=deadline)
        all_counts, all_meta = count_cds_fasta(cds_text, heg_only=False) if cds_text else (zero_counts(), {})
        heg_counts, heg_meta = count_cds_fasta(cds_text, heg_only=True) if cds_text else (zero_counts(), {})
        trna_counts, trna_meta = trna_probe.parse_genbank_trna_anticodons(gbff_text) if gbff_text else ({}, {})
        ok = (
            sum(all_counts.values()) > 0
            and sum(int(v) for v in trna_counts.values()) > 0
            and int(heg_meta.get("n_heg_records", 0)) >= MIN_HEG_GENES
        )
        attempts.append(
            {
                "assembly_accession": summary.get("assembly_accession") or accession,
                "organism": summary.get("organism") or organism_hint,
                "genus": genus,
                "domain": domain,
                "n_cds_records": all_meta.get("n_cds_records"),
                "n_trna_with_anticodon": trna_meta.get("n_trna_with_anticodon"),
                "n_heg_records": heg_meta.get("n_heg_records"),
                "ok": ok,
                "summary_contact": summary_contact,
                "cds_contact": {k: cds_contact.get(k) for k in ("reachable", "on_disk_cache_hit", "byte_size", "error")},
                "gbff_contact": {k: gbff_contact.get(k) for k in ("reachable", "on_disk_cache_hit", "byte_size", "error")},
            }
        )
        if not ok:
            continue
        seen_genera.add(genus)
        usable.append(
            {
                "organism": summary.get("organism") or organism_hint,
                "genus": genus,
                "domain": domain,
                "assembly_accession": summary.get("assembly_accession") or accession,
                "taxid": summary.get("taxid"),
                "transl_table": transl_table,
                "codon_counts_rna": all_counts,
                "all_codon_counts_rna": all_counts,
                "trna_anticodon_counts_rna": {str(k): int(v) for k, v in trna_counts.items()},
                "heg_codon_counts_rna": heg_counts,
                "cds_meta": all_meta,
                "heg_meta": heg_meta,
                "trna_meta": trna_meta,
                "annotation_contacts": {"summary": summary_contact, "cds_from_genomic": cds_contact, "genomic_gbff": gbff_contact},
            }
        )
    return usable, attempts


def build_eukaryota_rows(deadline: float | None = None) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    usable: list[dict[str, object]] = []
    attempts: list[dict[str, object]] = []
    for accession, organism_hint, genus_hint in EUKARYOTA_ROSTER[:MAX_EUK_ATTEMPTS]:
        if deadline_expired(deadline):
            attempts.append({"assembly_accession": accession, "organism": organism_hint, "genus": genus_hint, "ok": False, "error": "fetch_deadline_exceeded"})
            break
        summary, summary_contact = assembly_summary_for_accession(accession, deadline=deadline)
        if summary is None:
            attempts.append({"assembly_accession": accession, "organism": organism_hint, "genus": genus_hint, "ok": False, "contact": summary_contact})
            continue
        ftp_path = str(summary["ftp_path_refseq"])
        cds_text, cds_contact = cached_assembly_file(ftp_path, "cds_from_genomic.fna.gz", accession, deadline=deadline)
        gbff_text, gbff_contact = cached_assembly_file(ftp_path, "genomic.gbff.gz", accession, deadline=deadline)
        all_counts, all_meta = count_cds_fasta(cds_text, heg_only=False) if cds_text else (zero_counts(), {})
        heg_counts, heg_meta = count_cds_fasta(cds_text, heg_only=True) if cds_text else (zero_counts(), {})
        trna_counts, trna_meta = trna_probe.parse_genbank_trna_anticodons(gbff_text) if gbff_text else ({}, {})
        ok = (
            sum(all_counts.values()) > 0
            and sum(int(v) for v in trna_counts.values()) > 0
            and int(heg_meta.get("n_heg_records", 0)) >= MIN_HEG_GENES
        )
        attempts.append(
            {
                "assembly_accession": accession,
                "organism": summary.get("organism") or organism_hint,
                "genus": genus_hint,
                "domain": "Eukaryota",
                "n_cds_records": all_meta.get("n_cds_records"),
                "n_trna_with_anticodon": trna_meta.get("n_trna_with_anticodon"),
                "n_heg_records": heg_meta.get("n_heg_records"),
                "ok": ok,
                "summary_contact": summary_contact,
                "cds_contact": {k: cds_contact.get(k) for k in ("reachable", "on_disk_cache_hit", "byte_size", "error")},
                "gbff_contact": {k: gbff_contact.get(k) for k in ("reachable", "on_disk_cache_hit", "byte_size", "error")},
            }
        )
        if not ok:
            continue
        usable.append(
            {
                "organism": summary.get("organism") or organism_hint,
                "genus": genus_hint,
                "domain": "Eukaryota",
                "assembly_accession": summary.get("assembly_accession") or accession,
                "taxid": summary.get("taxid"),
                "transl_table": 1,
                "codon_counts_rna": all_counts,
                "all_codon_counts_rna": all_counts,
                "trna_anticodon_counts_rna": {str(k): int(v) for k, v in trna_counts.items()},
                "heg_codon_counts_rna": heg_counts,
                "cds_meta": all_meta,
                "heg_meta": heg_meta,
                "trna_meta": trna_meta,
                "annotation_contacts": {"summary": summary_contact, "cds_from_genomic": cds_contact, "genomic_gbff": gbff_contact},
            }
        )
    return usable, attempts


def domain_counts(rows: list[dict[str, object]]) -> dict[str, int]:
    out: dict[str, set[str]] = {}
    for row in rows:
        out.setdefault(str(row["domain"]), set()).add(str(row["genus"]))
    return {domain: len(genera) for domain, genera in sorted(out.items())}


def domain_floors() -> dict[str, int]:
    return {"Bacteria": BACTERIA_FLOOR, "Archaea": ARCHAEA_FLOOR, "Eukaryota": EUKARYOTA_FLOOR}


def qualified_domains(n_genera_domain: dict[str, int]) -> list[str]:
    floors = domain_floors()
    return [domain for domain in ("Bacteria", "Archaea", "Eukaryota") if int(n_genera_domain.get(domain, 0)) >= floors[domain]]


def compact_rows(rows: list[dict[str, object]]) -> list[dict[str, object]]:
    return [
        {
            "organism": row.get("organism"),
            "genus": row.get("genus"),
            "domain": row.get("domain"),
            "assembly_accession": row.get("assembly_accession"),
            "transl_table": row.get("transl_table"),
            "n_trna_anticodons": len(row.get("trna_anticodon_counts_rna", {})),
            "n_heg_records": row.get("heg_meta", {}).get("n_heg_records") if isinstance(row.get("heg_meta"), dict) else None,
            "total_sense_codons": sum(int(v) for v in dict(row.get("all_codon_counts_rna", {})).values()),
        }
        for row in rows
    ]


def build_panel(force_refresh: bool = False) -> dict[str, object]:
    if PANEL_CACHE_PATH.exists() and not force_refresh:
        cached = json.loads(PANEL_CACHE_PATH.read_text(encoding="utf-8"))
        if "rows" in cached and cached.get("status") == "ok" and len(cached.get("qualified_domains", [])) >= 2:
            return cached
    deadline = time.monotonic() + FETCH_DEADLINE_SECONDS if FETCH_DEADLINE_SECONDS > 0 else None
    supply_rows, supply_attempts = build_supply_rows(deadline=deadline)
    archaea_rows, archaea_attempts = build_refseq_roster_rows(ARCHAEA_ROSTER, "Archaea", 11, MAX_ARCHAEA_ATTEMPTS, deadline=deadline)
    euk_rows, euk_attempts = build_eukaryota_rows(deadline=deadline)
    keyed_rows: dict[tuple[str, str], dict[str, object]] = {}
    for row in supply_rows + archaea_rows + euk_rows:
        keyed_rows[(str(row.get("domain")), str(row.get("genus")))] = row
    rows = list(keyed_rows.values())
    n_genera_domain = domain_counts(rows)
    qualified = qualified_domains(n_genera_domain)
    status = "ok" if len(qualified) >= 2 else "needs_external"
    if len(qualified) >= 3:
        scope = "three-domain"
    elif status == "ok":
        scope = "two-domain"
    else:
        scope = "insufficient-domain-power"
    panel = {
        "status": status,
        "generated_at": now_iso(),
        "experiment_id": EXPERIMENT_ID,
        "cache_path": str(PANEL_CACHE_PATH),
        "genome_cache_dir": str(GENOME_CACHE_DIR),
        "scope": scope,
        "qualified_domains": qualified,
        "floors": {**domain_floors(), "heg_genes_per_organism": MIN_HEG_GENES},
        "fetch_limits": {
            "deadline_seconds": FETCH_DEADLINE_SECONDS,
            "genome_timeout_seconds": GENOME_FETCH_TIMEOUT,
            "summary_timeout_seconds": SUMMARY_FETCH_TIMEOUT,
            "max_supply_attempts": MAX_SUPPLY_ATTEMPTS,
            "max_archaea_attempts": MAX_ARCHAEA_ATTEMPTS,
            "max_eukaryota_attempts": MAX_EUK_ATTEMPTS,
        },
        "n_genera_domain": n_genera_domain,
        "n_rows": len(rows),
        "rows_compact": compact_rows(rows),
        "attempts": {"supply_panel": supply_attempts, "archaea_roster": archaea_attempts, "eukaryota_roster": euk_attempts},
        "provenance": {
            "bacteria_archaea_source": str(SUPPLY_PANEL_PATH),
            "archaea_roster": [{"assembly_accession": a, "organism": o, "genus": g} for a, o, g in ARCHAEA_ROSTER],
            "eukaryota_roster": [{"assembly_accession": a, "organism": o, "genus": g} for a, o, g in EUKARYOTA_ROSTER],
            "per_organism_requirements": ["CDS codon counts", "annotation tRNA anticodon counts", "annotation HEG set >=20 genes"],
            "not_window6": True,
            "not_causal_closure": True,
        },
        "sense_codon_order_rna": sense_codon_order_rna(),
        "rows": rows,
    }
    PANEL_CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    PANEL_CACHE_PATH.write_text(json.dumps(panel, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return panel


def compact_panel(panel: dict[str, object]) -> dict[str, object]:
    return {
        "status": panel.get("status"),
        "scope": panel.get("scope"),
        "qualified_domains": panel.get("qualified_domains"),
        "n_rows": panel.get("n_rows"),
        "n_genera_domain": panel.get("n_genera_domain"),
        "floors": panel.get("floors"),
        "cache_path": panel.get("cache_path"),
        "genome_cache_dir": panel.get("genome_cache_dir"),
        "rows_compact": panel.get("rows_compact"),
    }


if __name__ == "__main__":
    payload = build_panel(force_refresh="--force" in __import__("sys").argv)
    print(json.dumps(compact_panel(payload), ensure_ascii=True, sort_keys=True, separators=(",", ":")))

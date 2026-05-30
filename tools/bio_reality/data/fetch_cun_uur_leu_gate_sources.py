#!/usr/bin/env python3
"""Fetch curated codon-usage and tRNA-Leu contacts for the CUN/UUR gate."""
from __future__ import annotations

import hashlib
import json
import re
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DATA_DIR = Path(__file__).resolve().parent
MANIFEST_DIR = DATA_DIR / "manifests"
USER_AGENT = "BioReality-data-fetcher/1.0"
MAX_BYTES = 100 * 1024 * 1024
CLAIM_ID = "h3.translation_realization.cross_organism.cun_uur_leu_gate"
ALLOWED_MANIFEST_SOURCE_NAMES = {
    "ncbi",
    "uniprot",
    "ensembl",
    "gtrnadb",
    "ena",
    "arxiv",
    "biorxiv",
    "wikipedia",
    "wikidata",
    "github",
    "other",
}

STANDARD_CODE = {
    "UUU": "F",
    "UUC": "F",
    "UUA": "L",
    "UUG": "L",
    "UCU": "S",
    "UCC": "S",
    "UCA": "S",
    "UCG": "S",
    "UAU": "Y",
    "UAC": "Y",
    "UAA": "*",
    "UAG": "*",
    "UGU": "C",
    "UGC": "C",
    "UGA": "*",
    "UGG": "W",
    "CUU": "L",
    "CUC": "L",
    "CUA": "L",
    "CUG": "L",
    "CCU": "P",
    "CCC": "P",
    "CCA": "P",
    "CCG": "P",
    "CAU": "H",
    "CAC": "H",
    "CAA": "Q",
    "CAG": "Q",
    "CGU": "R",
    "CGC": "R",
    "CGA": "R",
    "CGG": "R",
    "AUU": "I",
    "AUC": "I",
    "AUA": "I",
    "AUG": "M",
    "ACU": "T",
    "ACC": "T",
    "ACA": "T",
    "ACG": "T",
    "AAU": "N",
    "AAC": "N",
    "AAA": "K",
    "AAG": "K",
    "AGU": "S",
    "AGC": "S",
    "AGA": "R",
    "AGG": "R",
    "GUU": "V",
    "GUC": "V",
    "GUA": "V",
    "GUG": "V",
    "GCU": "A",
    "GCC": "A",
    "GCA": "A",
    "GCG": "A",
    "GAU": "D",
    "GAC": "D",
    "GAA": "E",
    "GAG": "E",
    "GGU": "G",
    "GGC": "G",
    "GGA": "G",
    "GGG": "G",
}

KAZUSA_SOURCES = [
    {
        "organism": "homo_sapiens",
        "species": "9606",
        "label": "Homo sapiens",
        "basename": "kazusa_codon_usage_homo_sapiens",
    },
    {
        "organism": "saccharomyces_cerevisiae",
        "species": "4932",
        "label": "Saccharomyces cerevisiae",
        "basename": "kazusa_codon_usage_saccharomyces_cerevisiae",
    },
    {
        "organism": "escherichia_coli_k12",
        "species": "83333",
        "label": "Escherichia coli K12",
        "basename": "kazusa_codon_usage_escherichia_coli_k12",
    },
]

GTRNADB_SOURCES = [
    {
        "organism": "homo_sapiens",
        "accession_or_id": "Hsapi38/hg38-tRNAs.fa",
        "label": "Homo sapiens hg38",
        "basename": "gtrnadb_trna_leu_copy_homo_sapiens",
        "url": "https://gtrnadb.ucsc.edu/genomes/eukaryota/Hsapi38/hg38-tRNAs.fa",
    },
    {
        "organism": "saccharomyces_cerevisiae",
        "accession_or_id": "Scere3/sacCer3-tRNAs.fa",
        "label": "Saccharomyces cerevisiae sacCer3",
        "basename": "gtrnadb_trna_leu_copy_saccharomyces_cerevisiae",
        "url": "https://gtrnadb.ucsc.edu/genomes/eukaryota/Scere3/sacCer3-tRNAs.fa",
    },
    {
        "organism": "escherichia_coli_k12",
        "accession_or_id": "Esch_coli_K_12_MG1655/eschColi_K_12_MG1655-tRNAs.fa",
        "label": "Escherichia coli str. K-12 substr. MG1655",
        "basename": "gtrnadb_trna_leu_copy_escherichia_coli_k12",
        "url": "https://gtrnadb.ucsc.edu/genomes/bacteria/Esch_coli_K_12_MG1655/eschColi_K_12_MG1655-tRNAs.fa",
    },
]


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def fetch_bytes(url: str) -> tuple[bytes, str]:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=60) as response:
        content_length = response.headers.get("Content-Length")
        if content_length is not None and int(content_length) > MAX_BYTES:
            raise RuntimeError(f"response too large before read: {content_length} bytes")
        payload = response.read(MAX_BYTES + 1)
        if len(payload) > MAX_BYTES:
            raise RuntimeError("response exceeds 100 MB")
        return payload, str(response.headers.get("Content-Type") or "server did not provide Content-Type")


def write_manifest(
    basename: str,
    *,
    payload: bytes,
    content_type: str,
    url: str,
    source_name: str,
    accession_or_id: str,
    license_or_terms: str,
) -> None:
    if source_name not in ALLOWED_MANIFEST_SOURCE_NAMES:
        raise ValueError(f"manifest source_name is not allowed: {source_name}")
    MANIFEST_DIR.mkdir(parents=True, exist_ok=True)
    manifest = {
        "fetched_at": now_iso(),
        "source_url": url,
        "source_name": source_name,
        "accession_or_id": accession_or_id,
        "sha256": hashlib.sha256(payload).hexdigest(),
        "byte_size": len(payload),
        "content_type": content_type,
        "fetched_by": "bio-data-fetcher",
        "intended_claim_id": CLAIM_ID,
        "license_or_terms": license_or_terms,
    }
    (MANIFEST_DIR / f"{basename}.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def kazusa_url(species: str) -> str:
    return f"https://www.kazusa.or.jp/codon/cgi-bin/showcodon.cgi?species={species}&style=N"


def parse_kazusa(payload: bytes) -> dict[str, Any]:
    text = payload.decode("iso-8859-1")
    if "<TITLE>Not found</TITLE>" in text:
        raise ValueError("Kazusa record not found")
    codon_counts = {
        match.group(1): int(match.group(2))
        for match in re.finditer(r"\b([UCAG]{3})\s+[0-9.]+\(\s*([0-9]+)\)", text)
    }
    if len(codon_counts) != 64:
        raise ValueError(f"expected 64 Kazusa codons, got {len(codon_counts)}")
    amino_acid_counts: dict[str, int] = {}
    stop_counts: dict[str, int] = {}
    for codon, count in codon_counts.items():
        aa = STANDARD_CODE[codon]
        if aa == "*":
            stop_counts[codon] = count
        else:
            amino_acid_counts[aa] = amino_acid_counts.get(aa, 0) + count
    return {
        "codon_counts": codon_counts,
        "amino_acid_counts": dict(sorted(amino_acid_counts.items())),
        "stop_codon_counts": stop_counts,
        "raw_payload_text": text,
        "payload_note": "raw_payload_text preserves the Kazusa HTML response; manifest sha256 is computed over the original HTTP response bytes",
        "cannot_claim": [
            "The Kazusa codon-usage contact does not establish protein structure.",
            "The Kazusa codon-usage contact does not establish biological function.",
            "The Kazusa codon-usage contact does not establish physical admissibility.",
            "The Kazusa codon-usage contact does not establish a global biological law.",
        ],
    }


def parse_gtrnadb_fasta(payload: bytes) -> dict[str, Any]:
    text = payload.decode("utf-8")
    copies: dict[str, int] = {}
    total_leu = 0
    for line in text.splitlines():
        if not line.startswith(">"):
            continue
        match = re.search(r"\bLeu\s+\(([UCAGT]{3})\)", line)
        if not match:
            continue
        anticodon = match.group(1).replace("T", "U")
        copies[anticodon] = copies.get(anticodon, 0) + 1
        total_leu += 1
    if total_leu == 0:
        raise ValueError("no Leu tRNA headers found in GtRNAdb FASTA")
    return {
        "trna_leu_copies": dict(sorted(copies.items())),
        "total_trna_leu_copies": total_leu,
        "raw_payload_text": text,
        "payload_note": "raw_payload_text preserves the GtRNAdb FASTA response; manifest sha256 is computed over the original HTTP response bytes",
        "cannot_claim": [
            "The GtRNAdb tRNA gene-copy contact does not establish protein structure.",
            "The GtRNAdb tRNA gene-copy contact does not establish biological function.",
            "The GtRNAdb tRNA gene-copy contact does not establish physical admissibility.",
            "The GtRNAdb tRNA gene-copy contact does not establish a global biological law.",
        ],
    }


def write_json(basename: str, record: dict[str, Any]) -> Path:
    path = DATA_DIR / f"{basename}.json"
    path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return path


def fetch_kazusa(source: dict[str, str]) -> str:
    url = kazusa_url(source["species"])
    payload, content_type = fetch_bytes(url)
    record = parse_kazusa(payload)
    record.update(
        {
            "source_name": "kazusa",
            "source_url": url,
            "organism": source["organism"],
            "organism_label": source["label"],
            "accession_or_id": source["species"],
            "fetched_by": "bio-data-fetcher",
            "intended_claim_id": CLAIM_ID,
        }
    )
    path = write_json(source["basename"], record)
    write_manifest(
        source["basename"],
        payload=payload,
        content_type=content_type,
        url=url,
        source_name="other",
        accession_or_id=source["species"],
        license_or_terms="Kazusa Codon Usage Database public codon-usage table; use subject to Kazusa database terms and citation guidance.",
    )
    return str(path.relative_to(DATA_DIR.parents[2]))


def fetch_gtrnadb(source: dict[str, str]) -> str:
    payload, content_type = fetch_bytes(source["url"])
    record = parse_gtrnadb_fasta(payload)
    record.update(
        {
            "source_name": "gtrnadb",
            "source_url": source["url"],
            "organism": source["organism"],
            "organism_label": source["label"],
            "accession_or_id": source["accession_or_id"],
            "fetched_by": "bio-data-fetcher",
            "intended_claim_id": CLAIM_ID,
        }
    )
    path = write_json(source["basename"], record)
    write_manifest(
        source["basename"],
        payload=payload,
        content_type=content_type,
        url=source["url"],
        source_name="gtrnadb",
        accession_or_id=source["accession_or_id"],
        license_or_terms="GtRNAdb public genomic tRNA predictions; use subject to GtRNAdb/UCSC database terms and citation guidance.",
    )
    return str(path.relative_to(DATA_DIR.parents[2]))


def main() -> int:
    written = []
    for source in KAZUSA_SOURCES:
        written.append(fetch_kazusa(source))
    for source in GTRNADB_SOURCES:
        written.append(fetch_gtrnadb(source))
    print(json.dumps({"written": written}, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

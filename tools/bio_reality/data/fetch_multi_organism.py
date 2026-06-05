#!/usr/bin/env python3
"""Fetch multi-organism tRNA gene-copy and codon-usage contacts."""
from __future__ import annotations

import hashlib
import html
import json
import re
import string
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DATA_DIR = Path(__file__).resolve().parent
USER_AGENT = "BioReality-data-fetcher/1.0"
MAX_BYTES = 100 * 1024 * 1024
TARGET_SUCCESS = 40
MAX_CANDIDATES = 260

GTRNADB_SPECIES_INDEX_URL = "https://gtrnadb.ucsc.edu/js/species.json"
GTRNADB_DOMAIN_PATH = {"e": "eukaryota", "a": "archaea", "b": "bacteria"}
KAZUSA_LETTER_URL = "https://www.kazusa.or.jp/codon/{letter}.html"
KAZUSA_CODON_URL = "https://www.kazusa.or.jp/codon/cgi-bin/showcodon.cgi?species={taxid}&style=N"

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


class FetchFailure(Exception):
    pass


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def fetch_bytes(url: str) -> tuple[bytes, str, int]:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(request, timeout=60) as response:
            status = int(getattr(response, "status", 200))
            content_length = response.headers.get("Content-Length")
            if content_length is not None and int(content_length) > MAX_BYTES:
                raise FetchFailure(f"response too large before read: {content_length} bytes")
            payload = response.read(MAX_BYTES + 1)
            if len(payload) > MAX_BYTES:
                raise FetchFailure("response exceeds 100 MB")
            if status != 200:
                raise FetchFailure(f"HTTP status {status}")
            if not payload:
                raise FetchFailure("empty HTTP payload")
            return payload, str(response.headers.get("Content-Type") or ""), status
    except urllib.error.HTTPError as exc:
        raise FetchFailure(f"HTTP status {exc.code}") from exc
    except urllib.error.URLError as exc:
        raise FetchFailure(f"URL error: {exc.reason}") from exc


def decode_text(payload: bytes, encoding: str) -> str:
    return payload.decode(encoding, "replace")


def slugify(label: str) -> str:
    value = label.lower()
    value = re.sub(r"\([^)]*\)", " ", value)
    value = re.sub(r"[^a-z0-9]+", "_", value)
    value = re.sub(r"_+", "_", value).strip("_")
    return value[:90] or "organism"


def normalized_label(label: str) -> str:
    value = html.unescape(label).lower().replace("_", " ")
    value = re.sub(r"\([^)]*\)", " ", value)
    value = re.sub(
        r"\b(str\.?|strain|substr\.?|subsp\.?|serovar|biovar|pv\.?|var\.?|f\.?|sp\.)\b",
        " ",
        value,
    )
    value = re.sub(r"[^a-z0-9]+", " ", value)
    return re.sub(r"\s+", " ", value).strip()


def binomial(label: str) -> str:
    parts = normalized_label(label).split()
    return " ".join(parts[:2]) if len(parts) >= 2 else normalized_label(label)


def gtrnadb_fasta_url(entry: dict[str, str]) -> str:
    domain = GTRNADB_DOMAIN_PATH[entry["d"]]
    genome_id = urllib.parse.quote(entry["i"], safe="")
    prefix = urllib.parse.quote(entry["f"], safe="")
    return f"https://gtrnadb.ucsc.edu/genomes/{domain}/{genome_id}/{prefix}-tRNAs.fa"


def load_gtrnadb_species() -> tuple[list[dict[str, str]], dict[str, Any]]:
    payload, content_type, status = fetch_bytes(GTRNADB_SPECIES_INDEX_URL)
    records = json.loads(decode_text(payload, "utf-8"))
    if not isinstance(records, list) or not records:
        raise FetchFailure("GtRNAdb species.json did not parse as a non-empty list")
    species = []
    for record in records:
        if not all(key in record for key in ("d", "i", "n", "f")):
            continue
        if record["d"] not in GTRNADB_DOMAIN_PATH:
            continue
        species.append(
            {
                "domain_code": str(record["d"]),
                "genome_id": str(record["i"]),
                "label": str(record["n"]),
                "prefix": str(record["f"]),
                "url": gtrnadb_fasta_url(record),
            }
        )
    index_contact = {
        "source_url": GTRNADB_SPECIES_INDEX_URL,
        "content_type": content_type,
        "http_status": status,
        "payload_sha256": hashlib.sha256(payload).hexdigest(),
        "raw_payload_text": decode_text(payload, "utf-8"),
        "byte_size": len(payload),
        "fetched_at": now_iso(),
    }
    return species, index_contact


def parse_kazusa_letter(payload: bytes, letter: str) -> list[dict[str, Any]]:
    text = decode_text(payload, "iso-8859-1")
    records = []
    pattern = re.compile(
        r'showcodon\.cgi\?species=([0-9]+).*?<I>(.*?)</I>\s*\[([^\]]+)\]:\s*([0-9]+)',
        re.IGNORECASE | re.DOTALL,
    )
    for match in pattern.finditer(text):
        label = html.unescape(re.sub(r"<.*?>", "", match.group(2))).strip()
        records.append(
            {
                "taxid": match.group(1),
                "label": label,
                "division": match.group(3),
                "cds_records": int(match.group(4)),
                "letter": letter,
            }
        )
    return records


def load_kazusa_index() -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    records: list[dict[str, Any]] = []
    contacts: list[dict[str, Any]] = []
    for letter in string.ascii_uppercase:
        url = KAZUSA_LETTER_URL.format(letter=letter)
        payload, content_type, status = fetch_bytes(url)
        records.extend(parse_kazusa_letter(payload, letter))
        contacts.append(
            {
                "letter": letter,
                "source_url": url,
                "content_type": content_type,
                "http_status": status,
                "payload_sha256": hashlib.sha256(payload).hexdigest(),
                "raw_payload_text": decode_text(payload, "iso-8859-1"),
                "byte_size": len(payload),
                "fetched_at": now_iso(),
            }
        )
    if not records:
        raise FetchFailure("Kazusa A-Z index produced zero species records")
    return records, contacts


def choose_kazusa_by_normalized_label(records: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    by_label: dict[str, dict[str, Any]] = {}
    for record in records:
        key = normalized_label(record["label"])
        if not key:
            continue
        previous = by_label.get(key)
        if previous is None or record["cds_records"] > previous["cds_records"]:
            by_label[key] = record
    return by_label


def build_candidates(
    gtrnadb_species: list[dict[str, str]], kazusa_records: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    kazusa_by_label = choose_kazusa_by_normalized_label(kazusa_records)
    candidates = []
    used_slugs: set[str] = set()
    for gtrna in gtrnadb_species:
        key = normalized_label(gtrna["label"])
        kazusa = kazusa_by_label.get(key)
        if kazusa is None:
            continue
        slug_base = slugify(kazusa["label"])
        slug = slug_base
        suffix = 2
        while slug in used_slugs:
            slug = f"{slug_base}_{suffix}"
            suffix += 1
        used_slugs.add(slug)
        candidates.append(
            {
                "organism": slug,
                "match_kind": "exact_normalized_label",
                "match_key": key,
                "binomial": binomial(kazusa["label"]),
                "organism_label": kazusa["label"],
                "gtrnadb_label": gtrna["label"],
                "kazusa_label": kazusa["label"],
                "kazusa_taxid": kazusa["taxid"],
                "kazusa_division": kazusa["division"],
                "kazusa_cds_records": kazusa["cds_records"],
                "gtrnadb_domain_code": gtrna["domain_code"],
                "gtrnadb_domain": GTRNADB_DOMAIN_PATH[gtrna["domain_code"]],
                "gtrnadb_genome_id": gtrna["genome_id"],
                "gtrnadb_prefix": gtrna["prefix"],
                "gtrnadb_fasta_url": gtrna["url"],
                "accession_or_id": f"{gtrna['genome_id']}/{gtrna['prefix']}-tRNAs.fa",
            }
        )

    def rank(candidate: dict[str, Any]) -> tuple[int, int, str]:
        domain_rank = {"b": 0, "a": 1, "e": 2}.get(candidate["gtrnadb_domain_code"], 9)
        return (-candidate["kazusa_cds_records"], domain_rank, candidate["organism"])

    return sorted(candidates, key=rank)


def parse_gtrnadb_all_trna(payload: bytes) -> dict[str, Any]:
    text = decode_text(payload, "utf-8")
    copies: dict[str, int] = {}
    total = 0
    header_count = 0
    for line in text.splitlines():
        if not line.startswith(">"):
            continue
        header_count += 1
        match = re.search(r"\b(?:[A-Za-z0-9]+|Undet)\s+\(([UCAGT]{3}|NNN)\)", line)
        if not match:
            continue
        anticodon = match.group(1).replace("T", "U")
        if anticodon == "NNN":
            continue
        copies[anticodon] = copies.get(anticodon, 0) + 1
        total += 1
    if header_count == 0:
        raise ValueError("GtRNAdb FASTA contains no headers")
    if total == 0:
        raise ValueError("GtRNAdb FASTA contains no parseable non-NNN anticodon headers")
    return {
        "trna_all_copies": dict(sorted(copies.items())),
        "total_trna_all_copies": total,
        "trna_fasta_header_count": header_count,
        "raw_payload_text": text,
        "payload_note": "raw_payload_text preserves the GtRNAdb FASTA response; payload_sha256 is computed over the original HTTP response bytes",
    }


def parse_kazusa_codon_usage(payload: bytes) -> dict[str, Any]:
    text = decode_text(payload, "iso-8859-1")
    if "<TITLE>Not found</TITLE>" in text:
        raise ValueError("Kazusa record not found")
    codon_counts = {
        match.group(1): int(match.group(2))
        for match in re.finditer(r"\b([UCAG]{3})\s+[0-9.]+\(\s*([0-9]+)\)", text)
    }
    if len(codon_counts) != 64:
        raise ValueError(f"expected 64 Kazusa codons, got {len(codon_counts)}")
    amino_acid_counts: dict[str, int] = {}
    stop_codon_counts: dict[str, int] = {}
    for codon, count in codon_counts.items():
        amino_acid = STANDARD_CODE[codon]
        if amino_acid == "*":
            stop_codon_counts[codon] = count
        else:
            amino_acid_counts[amino_acid] = amino_acid_counts.get(amino_acid, 0) + count
    return {
        "codon_counts": dict(sorted(codon_counts.items())),
        "amino_acid_counts": dict(sorted(amino_acid_counts.items())),
        "stop_codon_counts": dict(sorted(stop_codon_counts.items())),
        "raw_payload_text": text,
        "payload_note": "raw_payload_text preserves the Kazusa HTML response; payload_sha256 is computed over the original HTTP response bytes",
    }


def write_json(path: Path, record: dict[str, Any]) -> None:
    path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def base_contact(candidate: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema_version": "bio_reality_curated_external_contact_v1",
        "organism": candidate["organism"],
        "organism_label": candidate["organism_label"],
        "match_kind": candidate["match_kind"],
        "match_key": candidate["match_key"],
        "fetched_by": "bio-data-fetcher",
        "fetched_at": now_iso(),
        "derivation_boundary": "not_bedc_kernel_content",
        "cannot_claim": [
            "This external count contact does not establish translation or protein synthesis outcomes.",
            "This external count contact does not establish protein structure.",
            "This external count contact does not establish biological function.",
            "This external count contact does not establish physical admissibility.",
            "This external count contact does not establish a global biological law.",
        ],
    }


def fetch_candidate(candidate: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    trna_payload, trna_content_type, trna_status = fetch_bytes(candidate["gtrnadb_fasta_url"])
    trna_parsed = parse_gtrnadb_all_trna(trna_payload)
    codon_url = KAZUSA_CODON_URL.format(taxid=candidate["kazusa_taxid"])
    codon_payload, codon_content_type, codon_status = fetch_bytes(codon_url)
    codon_parsed = parse_kazusa_codon_usage(codon_payload)

    trna_record = {
        **base_contact(candidate),
        **trna_parsed,
        "accession_or_id": candidate["accession_or_id"],
        "source_kind": "gtrnadb_full_trna_gene_copy",
        "source_name": "gtrnadb",
        "source_url": candidate["gtrnadb_fasta_url"],
        "source_content_type": trna_content_type,
        "source_http_status": trna_status,
        "payload_sha256": hashlib.sha256(trna_payload).hexdigest(),
        "payload_byte_size": len(trna_payload),
        "gtrnadb_domain": candidate["gtrnadb_domain"],
        "gtrnadb_genome_id": candidate["gtrnadb_genome_id"],
        "gtrnadb_prefix": candidate["gtrnadb_prefix"],
        "gtrnadb_label": candidate["gtrnadb_label"],
        "reality_contact_scope": "external_curated_full_trna_gene_copy_counts_only",
    }
    codon_record = {
        **base_contact(candidate),
        **codon_parsed,
        "accession_or_id": candidate["kazusa_taxid"],
        "source_kind": "kazusa_codon_usage_counts",
        "source_name": "kazusa",
        "source_url": codon_url,
        "source_content_type": codon_content_type,
        "source_http_status": codon_status,
        "payload_sha256": hashlib.sha256(codon_payload).hexdigest(),
        "payload_byte_size": len(codon_payload),
        "kazusa_taxid": candidate["kazusa_taxid"],
        "kazusa_division": candidate["kazusa_division"],
        "kazusa_cds_records": candidate["kazusa_cds_records"],
        "kazusa_label": candidate["kazusa_label"],
        "reality_contact_scope": "external_curated_codon_usage_counts_only",
    }
    return trna_record, codon_record


def cleanup_previous_outputs() -> None:
    for pattern in (
        "gtrnadb_trna_all_copy_*.json",
        "codon_usage_*.json",
        "multi_organism_campaign_manifest.json",
    ):
        for path in DATA_DIR.glob(pattern):
            path.unlink()


def main() -> int:
    cleanup_previous_outputs()
    failures: list[dict[str, Any]] = []
    successes: list[dict[str, Any]] = []
    trna_samples: list[dict[str, Any]] = []

    try:
        gtrnadb_species, gtrnadb_index_contact = load_gtrnadb_species()
    except Exception as exc:
        manifest = {
            "schema_version": "bio_reality_multi_organism_campaign_manifest_v1",
            "fetched_by": "bio-data-fetcher",
            "fetched_at": now_iso(),
            "success_count": 0,
            "failure_count": 1,
            "target_success_count": TARGET_SUCCESS,
            "successes": [],
            "failures": [{"stage": "gtrnadb_index", "reason": str(exc)}],
            "derivation_boundary": "not_bedc_kernel_content",
        }
        write_json(DATA_DIR / "multi_organism_campaign_manifest.json", manifest)
        print(json.dumps(manifest, indent=2, sort_keys=True))
        return 0

    try:
        kazusa_records, kazusa_index_contacts = load_kazusa_index()
    except Exception as exc:
        manifest = {
            "schema_version": "bio_reality_multi_organism_campaign_manifest_v1",
            "fetched_by": "bio-data-fetcher",
            "fetched_at": now_iso(),
            "success_count": 0,
            "failure_count": 1,
            "target_success_count": TARGET_SUCCESS,
            "gtrnadb_species_index_contact": gtrnadb_index_contact,
            "successes": [],
            "failures": [{"stage": "kazusa_index", "reason": str(exc)}],
            "derivation_boundary": "not_bedc_kernel_content",
        }
        write_json(DATA_DIR / "multi_organism_campaign_manifest.json", manifest)
        print(json.dumps(manifest, indent=2, sort_keys=True))
        return 0

    candidates = build_candidates(gtrnadb_species, kazusa_records)
    for candidate in candidates[:MAX_CANDIDATES]:
        if len(successes) >= TARGET_SUCCESS:
            break
        trna_path = DATA_DIR / f"gtrnadb_trna_all_copy_{candidate['organism']}.json"
        codon_path = DATA_DIR / f"codon_usage_{candidate['organism']}.json"
        try:
            trna_record, codon_record = fetch_candidate(candidate)
        except Exception as exc:
            failures.append(
                {
                    "organism": candidate["organism"],
                    "organism_label": candidate["organism_label"],
                    "gtrnadb_fasta_url": candidate["gtrnadb_fasta_url"],
                    "kazusa_taxid": candidate["kazusa_taxid"],
                    "stage": "paired_fetch_or_parse",
                    "reason": str(exc),
                }
            )
            continue
        write_json(trna_path, trna_record)
        write_json(codon_path, codon_record)
        successes.append(
            {
                "organism": candidate["organism"],
                "organism_label": candidate["organism_label"],
                "accession_or_id": candidate["accession_or_id"],
                "gtrnadb_fasta_url": candidate["gtrnadb_fasta_url"],
                "kazusa_taxid": candidate["kazusa_taxid"],
                "kazusa_url": KAZUSA_CODON_URL.format(taxid=candidate["kazusa_taxid"]),
                "trna_file": str(trna_path.relative_to(DATA_DIR.parent.parent.parent)),
                "codon_usage_file": str(codon_path.relative_to(DATA_DIR.parent.parent.parent)),
                "trna_payload_sha256": trna_record["payload_sha256"],
                "codon_payload_sha256": codon_record["payload_sha256"],
                "total_trna_all_copies": trna_record["total_trna_all_copies"],
                "total_codon_counts": sum(codon_record["codon_counts"].values()),
                "match_kind": candidate["match_kind"],
                "match_key": candidate["match_key"],
            }
        )
        if len(trna_samples) < 3:
            trna_samples.append(
                {
                    "organism": candidate["organism"],
                    "organism_label": candidate["organism_label"],
                    "top_anticodon_copies": sorted(
                        trna_record["trna_all_copies"].items(), key=lambda item: (-item[1], item[0])
                    )[:10],
                }
            )

    manifest = {
        "schema_version": "bio_reality_multi_organism_campaign_manifest_v1",
        "fetched_by": "bio-data-fetcher",
        "fetched_at": now_iso(),
        "target_success_count": TARGET_SUCCESS,
        "success_count": len(successes),
        "failure_count": len(failures),
        "candidate_count": len(candidates),
        "attempted_candidate_count": min(len(candidates), MAX_CANDIDATES),
        "selection_policy": "Exact normalized GtRNAdb species label to Kazusa species label; failed paired fetches/parses are skipped without replacement by fabricated values.",
        "raw_payload_policy": "Every successful tRNA and codon-usage JSON embeds the original HTTP response text in raw_payload_text and records sha256 over the original response bytes.",
        "gtrnadb_species_index_contact": gtrnadb_index_contact,
        "kazusa_letter_index_contacts": kazusa_index_contacts,
        "successes": successes,
        "failures": failures,
        "sample_anticodon_copy_summaries": trna_samples,
        "derivation_boundary": "not_bedc_kernel_content",
        "cannot_claim": [
            "The campaign does not claim translation or protein realization.",
            "The campaign does not claim biological function.",
            "The campaign does not claim any BEDC kernel content.",
        ],
    }
    write_json(DATA_DIR / "multi_organism_campaign_manifest.json", manifest)

    print(
        json.dumps(
            {
                "success_count": len(successes),
                "failure_count": len(failures),
                "sample_anticodon_copy_summaries": trna_samples,
                "manifest": "tools/bio_reality/data/multi_organism_campaign_manifest.json",
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

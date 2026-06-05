#!/usr/bin/env python3
"""Fetch real CDS FASTA and PAXdb abundance, then join by exact identifiers."""

from __future__ import annotations

import gzip
import hashlib
import json
import re
import urllib.request
import base64
from datetime import datetime, timezone
from pathlib import Path


DATA_DIR = Path(__file__).resolve().parent
USER_AGENT = "BioReality-Codex-CDS-Codon/1.0"
RAW_SLICE_BYTES = 1024

CODONS = [
    a + b + c
    for a in "ACGT"
    for b in "ACGT"
    for c in "ACGT"
]

ORGANISMS = [
    {
        "organism": "escherichia_coli_k12_mg1655",
        "organism_label": "Escherichia coli str. K-12 substr. MG1655",
        "ncbi_taxid": "511145",
        "paxdb_url": "https://pax-db.org/downloads/latest/datasets/511145/511145-WHOLE_ORGANISM-integrated.txt",
        "cds_url": "https://ftp.ncbi.nlm.nih.gov/genomes/all/GCF/000/005/845/GCF_000005845.2_ASM584v2/GCF_000005845.2_ASM584v2_cds_from_genomic.fna.gz",
        "cds_source_name": "NCBI RefSeq GCF_000005845.2 ASM584v2 cds_from_genomic",
        "join_method": "PAXdb external id after taxid prefix is matched exactly to unique NCBI CDS header identifiers, primarily locus_tag b-numbers.",
    },
    {
        "organism": "saccharomyces_cerevisiae",
        "organism_label": "Saccharomyces cerevisiae S288C",
        "ncbi_taxid": "4932",
        "paxdb_url": "https://pax-db.org/downloads/latest/datasets/4932/4932-WHOLE_ORGANISM-integrated.txt",
        "cds_url": "https://ftp.ncbi.nlm.nih.gov/genomes/all/GCF/000/146/045/GCF_000146045.2_R64/GCF_000146045.2_R64_cds_from_genomic.fna.gz",
        "cds_source_name": "NCBI RefSeq GCF_000146045.2 R64 cds_from_genomic",
        "join_method": "PAXdb external id after taxid prefix is matched exactly to unique NCBI CDS header identifiers, primarily systematic locus tags such as YGR192C.",
    },
    {
        "organism": "mycobacterium_smegmatis_str_mc2_155",
        "organism_label": "Mycobacterium smegmatis str. MC2 155",
        "ncbi_taxid": "246196",
        "paxdb_url": "https://pax-db.org/downloads/latest/datasets/246196/246196-WHOLE_ORGANISM-integrated.txt",
        "cds_url": "https://ftp.ncbi.nlm.nih.gov/genomes/all/GCA/000/015/005/GCA_000015005.1_ASM1500v1/GCA_000015005.1_ASM1500v1_cds_from_genomic.fna.gz",
        "cds_source_name": "NCBI GenBank GCA_000015005.1 ASM1500v1 cds_from_genomic",
        "join_method": "PAXdb external id after taxid prefix is matched exactly to unique NCBI GenBank CDS header identifiers, primarily MSMEG locus tags.",
    },
]


def fetch_bytes(url: str) -> bytes:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=120) as response:
        return response.read()


def sha256_hex(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def raw_prefix_b64(payload: bytes) -> str:
    return base64.b64encode(payload[:RAW_SLICE_BYTES]).decode("ascii")


def parse_bracket_fields(header: str) -> dict[str, list[str]]:
    fields: dict[str, list[str]] = {}
    for key, value in re.findall(r"\[([^=\]]+)=([^\]]*)\]", header):
        fields.setdefault(key, []).append(value)
    return fields


def normalize_seq(seq: str) -> str:
    return re.sub(r"[^A-Za-z]", "", seq).upper()


def parse_fasta(text: str) -> list[dict[str, object]]:
    records: list[dict[str, object]] = []
    header: str | None = None
    chunks: list[str] = []
    for line in text.splitlines():
        if line.startswith(">"):
            if header is not None:
                records.append({"header": header, "seq": normalize_seq("".join(chunks))})
            header = line[1:].strip()
            chunks = []
        else:
            chunks.append(line.strip())
    if header is not None:
        records.append({"header": header, "seq": normalize_seq("".join(chunks))})
    return records


def header_identifiers(header: str) -> set[str]:
    fields = parse_bracket_fields(header)
    identifiers: set[str] = set()
    first_token = header.split(None, 1)[0]
    identifiers.add(first_token)
    for key in ("locus_tag", "gene", "protein_id"):
        for value in fields.get(key, []):
            identifiers.add(value)
    for value in fields.get("db_xref", []):
        identifiers.add(value)
        if ":" in value:
            identifiers.add(value.split(":", 1)[1])
    if "_cds_" in first_token:
        tail = first_token.split("_cds_", 1)[1]
        if "_" in tail:
            identifiers.add(tail.rsplit("_", 1)[0])
    return {x for x in identifiers if x}


def count_codons(seq: str) -> tuple[dict[str, int], int]:
    counts = {codon: 0 for codon in CODONS}
    usable = 0
    for index in range(0, len(seq) - 2, 3):
        codon = seq[index : index + 3]
        if len(codon) != 3:
            continue
        if all(base in "ACGT" for base in codon):
            counts[codon] += 1
            usable += 1
    return counts, usable


def parse_paxdb(payload: bytes, taxid: str) -> tuple[list[dict[str, object]], dict[str, str]]:
    text = payload.decode("utf-8", "replace")
    metadata: dict[str, str] = {}
    rows: list[dict[str, object]] = []
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if line.startswith("#"):
            if ":" in line:
                key, value = line[1:].split(":", 1)
                metadata[key.strip()] = value.strip()
            continue
        parts = line.split("\t")
        if len(parts) < 3:
            continue
        gene_name, protein_id, abundance = parts[:3]
        if not protein_id.startswith(taxid + "."):
            continue
        try:
            abundance_ppm = float(abundance)
        except ValueError:
            continue
        rows.append(
            {
                "gene_name": gene_name,
                "protein_id": protein_id,
                "ext_id": protein_id.split(".", 1)[1],
                "abundance_ppm": abundance_ppm,
            }
        )
    return rows, metadata


def unique_identifier_index(cds_records: list[dict[str, object]]) -> tuple[dict[str, dict[str, object]], dict[str, int]]:
    buckets: dict[str, list[dict[str, object]]] = {}
    for record in cds_records:
        for identifier in header_identifiers(str(record["header"])):
            buckets.setdefault(identifier, []).append(record)
    unique = {identifier: records[0] for identifier, records in buckets.items() if len(records) == 1}
    multiplicities = {identifier: len(records) for identifier, records in buckets.items()}
    return unique, multiplicities


def join_records(
    abundance_rows: list[dict[str, object]],
    cds_unique: dict[str, dict[str, object]],
) -> tuple[list[dict[str, object]], dict[str, int]]:
    joined: list[dict[str, object]] = []
    match_sources = {"ext_id": 0, "gene_name": 0}
    for row in abundance_rows:
        candidates = [
            ("ext_id", str(row["ext_id"])),
            ("gene_name", str(row["gene_name"])),
        ]
        match_kind = ""
        cds_record: dict[str, object] | None = None
        for candidate_kind, candidate_id in candidates:
            if candidate_id in cds_unique:
                match_kind = candidate_kind
                cds_record = cds_unique[candidate_id]
                break
        if cds_record is None:
            continue
        seq = str(cds_record["seq"])
        counts, usable_codons = count_codons(seq)
        match_sources[match_kind] += 1
        joined.append(
            {
                "protein_id": row["protein_id"],
                "paxdb_gene_name": row["gene_name"],
                "abundance_ppm": row["abundance_ppm"],
                "cds_match_id": str(row["ext_id"] if match_kind == "ext_id" else row["gene_name"]),
                "cds_match_kind": match_kind,
                "cds_header": cds_record["header"],
                "codon_counts": counts,
                "codon_count_total": usable_codons,
                "cds_len_nt": len(seq),
                "starts_atg": seq.startswith("ATG"),
                "len_mod3_ok": len(seq) % 3 == 0,
            }
        )
    return joined, match_sources


def build_organism(config: dict[str, str]) -> tuple[dict[str, object] | None, dict[str, object]]:
    started = datetime.now(timezone.utc).isoformat()
    try:
        paxdb_raw = fetch_bytes(config["paxdb_url"])
        cds_raw_gz = fetch_bytes(config["cds_url"])
        cds_text = gzip.decompress(cds_raw_gz).decode("utf-8", "replace")
        abundance_rows, paxdb_metadata = parse_paxdb(paxdb_raw, config["ncbi_taxid"])
        cds_records = parse_fasta(cds_text)
        cds_unique, multiplicities = unique_identifier_index(cds_records)
        joined, match_sources = join_records(abundance_rows, cds_unique)
        n_abundance = len(abundance_rows)
        n_joined = len(joined)
        hit_rate = n_joined / n_abundance if n_abundance else 0.0
        output = {
            "schema_version": 1,
            "organism": config["organism"],
            "organism_label": config["organism_label"],
            "ncbi_taxid": config["ncbi_taxid"],
            "source_kind": "ncbi_refseq_or_genbank_cds + paxdb_join",
            "source_name": "NCBI CDS FASTA joined to PAXdb protein abundance",
            "cds_source_name": config["cds_source_name"],
            "cds_source_url": config["cds_url"],
            "cds_payload_sha256": sha256_hex(cds_raw_gz),
            "cds_payload_byte_size": len(cds_raw_gz),
            "cds_payload_raw_prefix_base64": raw_prefix_b64(cds_raw_gz),
            "cds_payload_raw_prefix_byte_count": min(RAW_SLICE_BYTES, len(cds_raw_gz)),
            "cds_payload_decompressed_prefix_text": cds_text[:RAW_SLICE_BYTES],
            "cds_payload_note": "full_raw_gzip_payload_sha256 plus deterministic raw gzip prefix slice; decompressed FASTA parsed deterministically",
            "paxdb_source_url": config["paxdb_url"],
            "paxdb_payload_sha256": sha256_hex(paxdb_raw),
            "paxdb_payload_byte_size": len(paxdb_raw),
            "paxdb_payload_raw_prefix_text": paxdb_raw[:RAW_SLICE_BYTES].decode("utf-8", "replace"),
            "paxdb_payload_raw_prefix_byte_count": min(RAW_SLICE_BYTES, len(paxdb_raw)),
            "paxdb_payload_note": "full_raw_payload_sha256 plus deterministic raw text prefix slice",
            "paxdb_name": paxdb_metadata.get("name"),
            "paxdb_filename": paxdb_metadata.get("filename"),
            "join_method": config["join_method"],
            "join_policy": "Only exact unique identifier matches are accepted. Unmatched and ambiguous proteins are discarded.",
            "join_match_sources": match_sources,
            "n_cds_records": len(cds_records),
            "n_unique_cds_identifiers": len(cds_unique),
            "n_abundance_proteins": n_abundance,
            "n_joined": n_joined,
            "join_hit_rate": hit_rate,
            "fetched_at": started,
            "fetched_by": USER_AGENT,
            "joined": joined,
            "cannot_claim": [
                "measured abundance + real CDS codon; 非 translation rate; 非 mechanism",
                "PAXdb abundance does not by itself establish ribosome occupancy, elongation speed, folding, function, phenotype, or fitness.",
                "The join is identifier-level evidence only; proteins without exact unique CDS identifiers are discarded.",
            ],
            "derivation_boundary": "not_bedc_kernel_content",
        }
        manifest_row = {
            "organism": config["organism"],
            "organism_label": config["organism_label"],
            "ncbi_taxid": config["ncbi_taxid"],
            "status": "success",
            "n_abundance_proteins": n_abundance,
            "n_joined": n_joined,
            "join_hit_rate": hit_rate,
            "usable_for_powered_per_protein_s_qp": hit_rate > 0.3 and n_joined >= 1000,
            "cds_source_url": config["cds_url"],
            "cds_payload_sha256": sha256_hex(cds_raw_gz),
            "paxdb_source_url": config["paxdb_url"],
            "paxdb_payload_sha256": sha256_hex(paxdb_raw),
            "output_file": f"tools/bio_reality/data/cds_codon_abundance_{config['organism']}.json",
            "join_method": config["join_method"],
            "join_match_sources": match_sources,
            "n_cds_records": len(cds_records),
            "n_unique_cds_identifiers": len(cds_unique),
            "ambiguous_identifier_count": sum(1 for n in multiplicities.values() if n > 1),
        }
        return output, manifest_row
    except Exception as exc:
        return None, {
            "organism": config["organism"],
            "organism_label": config["organism_label"],
            "ncbi_taxid": config["ncbi_taxid"],
            "status": "failed",
            "reason": f"{type(exc).__name__}: {exc}",
            "cds_source_url": config["cds_url"],
            "paxdb_source_url": config["paxdb_url"],
        }


def assert_output_integrity(output: dict[str, object]) -> None:
    joined = output["joined"]
    if not isinstance(joined, list):
        raise AssertionError("joined is not a list")
    if int(output["n_joined"]) != len(joined):
        raise AssertionError("n_joined does not equal len(joined)")
    for row in joined:
        if not isinstance(row, dict):
            raise AssertionError("joined row is not an object")
        counts = row["codon_counts"]
        if not isinstance(counts, dict):
            raise AssertionError("codon_counts is not an object")
        total = sum(int(value) for value in counts.values())
        if total != int(row["codon_count_total"]):
            raise AssertionError("codon count total mismatch")
        if total > int(row["cds_len_nt"]) // 3:
            raise AssertionError("codon count total exceeds CDS length floor")


def main() -> int:
    successes: list[dict[str, object]] = []
    failures: list[dict[str, object]] = []
    manifest_rows: list[dict[str, object]] = []
    for config in ORGANISMS:
        output, row = build_organism(config)
        manifest_rows.append(row)
        if output is None:
            failures.append(row)
            continue
        assert_output_integrity(output)
        output_path = DATA_DIR / f"cds_codon_abundance_{config['organism']}.json"
        output_path.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
        successes.append(row)
    usable = [
        {"organism": row["organism"], "n_joined": row["n_joined"]}
        for row in successes
        if row.get("usable_for_powered_per_protein_s_qp")
    ]
    manifest = {
        "schema_version": 1,
        "source_name": "per-protein CDS codon composition joined to PAXdb abundance",
        "source_kind": "real_http_fetch_only",
        "raw_payload_policy": "Each PAXdb abundance payload and each CDS FASTA gzip payload was fetched by HTTP and recorded by full raw payload sha256.",
        "fetched_at": datetime.now(timezone.utc).isoformat(),
        "fetched_by": USER_AGENT,
        "target_relation": "powered per-protein S^QP input table",
        "organism_count": len(ORGANISMS),
        "success_count": len(successes),
        "failure_count": len(failures),
        "successes": successes,
        "failures": failures,
        "organisms": manifest_rows,
        "total_joined_proteins": sum(int(row["n_joined"]) for row in successes),
        "usable_powered_per_protein_s_qp": usable,
        "cannot_claim": [
            "measured abundance + real CDS codon; 非 translation rate; 非 mechanism",
            "No organism is retained without a true HTTP-fetched CDS payload and true HTTP-fetched PAXdb payload.",
            "No protein is retained without an exact unique identifier join between PAXdb and CDS FASTA.",
        ],
        "derivation_boundary": "not_bedc_kernel_content",
    }
    (DATA_DIR / "cds_codon_campaign_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps({"success_count": len(successes), "failure_count": len(failures), "usable": usable}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

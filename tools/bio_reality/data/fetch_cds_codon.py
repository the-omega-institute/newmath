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

TARGET_ORGANISMS = [
    {
        "organism": "homo_sapiens",
        "organism_label": "Homo sapiens",
        "ncbi_taxid": "9606",
        "cds_url": "https://ftp.ensembl.org/pub/current_fasta/homo_sapiens/cds/Homo_sapiens.GRCh38.cds.all.fa.gz",
        "cds_source_name": "Ensembl Homo_sapiens GRCh38 current cds.all",
        "gtf_url": "https://ftp.ensembl.org/pub/current_gtf/homo_sapiens/Homo_sapiens.GRCh38.115.gtf.gz",
        "gtf_source_name": "Ensembl Homo_sapiens GRCh38 release 115 GTF",
        "join_method": "PAXdb external id after taxid prefix is matched exactly to Ensembl protein_id from the HTTP-fetched Ensembl GTF; each protein keeps the longest CDS among mapped transcripts.",
    },
    {
        "organism": "arabidopsis_thaliana",
        "organism_label": "Arabidopsis thaliana",
        "ncbi_taxid": "3702",
        "cds_url": "https://ftp.ensemblgenomes.ebi.ac.uk/pub/plants/current/fasta/arabidopsis_thaliana/cds/Arabidopsis_thaliana.TAIR10.cds.all.fa.gz",
        "cds_source_name": "EnsemblPlants Arabidopsis_thaliana TAIR10 current cds.all",
        "gtf_url": "https://ftp.ensemblgenomes.ebi.ac.uk/pub/plants/current/gtf/arabidopsis_thaliana/Arabidopsis_thaliana.TAIR10.62.gtf.gz",
        "gtf_source_name": "EnsemblPlants Arabidopsis_thaliana TAIR10 release 62 GTF",
        "join_method": "PAXdb external id after taxid prefix is matched exactly to identifiers present in the HTTP-fetched EnsemblPlants CDS FASTA and GTF; each matched protein keeps the longest CDS among mapped transcripts.",
    },
    {
        "organism": "danio_rerio",
        "organism_label": "Danio rerio",
        "ncbi_taxid": "7955",
        "cds_url": "https://ftp.ensembl.org/pub/current_fasta/danio_rerio/cds/Danio_rerio.GRCz11.cds.all.fa.gz",
        "cds_source_name": "Ensembl Danio_rerio GRCz11 current cds.all",
        "gtf_url": "https://ftp.ensembl.org/pub/current_gtf/danio_rerio/Danio_rerio.GRCz11.115.gtf.gz",
        "gtf_source_name": "Ensembl Danio_rerio GRCz11 release 115 GTF",
        "join_method": "PAXdb external id after taxid prefix is matched exactly to Ensembl protein_id from the HTTP-fetched Ensembl GTF; each protein keeps the longest CDS among mapped transcripts.",
    },
    {
        "organism": "gallus_gallus",
        "organism_label": "Gallus gallus",
        "ncbi_taxid": "9031",
        "cds_url": "https://ftp.ensembl.org/pub/release-106/fasta/gallus_gallus/cds/Gallus_gallus.GRCg6a.cds.all.fa.gz",
        "cds_source_name": "Ensembl Gallus_gallus GRCg6a release 106 cds.all",
        "gtf_url": "https://ftp.ensembl.org/pub/release-106/gtf/gallus_gallus/Gallus_gallus.GRCg6a.106.gtf.gz",
        "gtf_source_name": "Ensembl Gallus_gallus GRCg6a release 106 GTF",
        "join_method": "PAXdb external id after taxid prefix is matched exactly to Ensembl protein_id from the HTTP-fetched Ensembl release 106 GTF; each protein keeps the longest CDS among mapped transcripts.",
    },
    {
        "organism": "pseudomonas_aeruginosa_pao1",
        "organism_label": "Pseudomonas aeruginosa PAO1",
        "ncbi_taxid": "208964",
        "cds_url": "https://ftp.ncbi.nlm.nih.gov/genomes/all/GCF/000/006/765/GCF_000006765.1_ASM676v1/GCF_000006765.1_ASM676v1_cds_from_genomic.fna.gz",
        "cds_source_name": "NCBI RefSeq GCF_000006765.1 ASM676v1 cds_from_genomic",
        "join_method": "PAXdb external id after taxid prefix is matched exactly to unique NCBI CDS header identifiers, primarily PA locus tags.",
    },
    {
        "organism": "bacillus_subtilis_subsp_subtilis_str_168",
        "organism_label": "Bacillus subtilis subsp. subtilis str. 168",
        "ncbi_taxid": "224308",
        "cds_url": "https://ftp.ncbi.nlm.nih.gov/genomes/all/GCF/000/009/045/GCF_000009045.1_ASM904v1/GCF_000009045.1_ASM904v1_cds_from_genomic.fna.gz",
        "cds_source_name": "NCBI RefSeq GCF_000009045.1 ASM904v1 cds_from_genomic",
        "join_method": "PAXdb external id after taxid prefix is matched exactly to unique NCBI CDS header identifiers, primarily BSU locus tags.",
    },
    {
        "organism": "mus_musculus",
        "organism_label": "Mus musculus",
        "ncbi_taxid": "10090",
        "cds_url": "https://ftp.ensembl.org/pub/release-115/fasta/mus_musculus/cds/Mus_musculus.GRCm39.cds.all.fa.gz",
        "cds_source_name": "Ensembl Mus_musculus GRCm39 release 115 cds.all",
        "gtf_url": "https://ftp.ensembl.org/pub/release-115/gtf/mus_musculus/Mus_musculus.GRCm39.115.gtf.gz",
        "gtf_source_name": "Ensembl Mus_musculus GRCm39 release 115 GTF",
        "join_method": "PAXdb external id after taxid prefix is matched exactly to Ensembl protein_id from the HTTP-fetched Ensembl GTF; each protein keeps the longest CDS among mapped transcripts.",
    },
    {
        "organism": "caenorhabditis_elegans",
        "organism_label": "Caenorhabditis elegans",
        "ncbi_taxid": "6239",
        "cds_url": "https://ftp.ensembl.org/pub/release-115/fasta/caenorhabditis_elegans/cds/Caenorhabditis_elegans.WBcel235.cds.all.fa.gz",
        "cds_source_name": "Ensembl Caenorhabditis_elegans WBcel235 release 115 cds.all",
        "gtf_url": "https://ftp.ensembl.org/pub/release-115/gtf/caenorhabditis_elegans/Caenorhabditis_elegans.WBcel235.115.gtf.gz",
        "gtf_source_name": "Ensembl Caenorhabditis_elegans WBcel235 release 115 GTF",
        "join_method": "PAXdb external id after taxid prefix is matched exactly to Ensembl protein_id from the HTTP-fetched Ensembl GTF; each protein keeps the longest CDS among mapped transcripts.",
    },
    {
        "organism": "drosophila_melanogaster",
        "organism_label": "Drosophila melanogaster",
        "ncbi_taxid": "7227",
        "cds_url": "https://ftp.ensembl.org/pub/release-115/fasta/drosophila_melanogaster/cds/Drosophila_melanogaster.BDGP6.54.cds.all.fa.gz",
        "cds_source_name": "Ensembl Drosophila_melanogaster BDGP6.54 release 115 cds.all",
        "gtf_url": "https://ftp.ensembl.org/pub/release-115/gtf/drosophila_melanogaster/Drosophila_melanogaster.BDGP6.54.115.gtf.gz",
        "gtf_source_name": "Ensembl Drosophila_melanogaster BDGP6.54 release 115 GTF",
        "join_method": "PAXdb external id after taxid prefix is matched exactly to Ensembl protein_id from the HTTP-fetched Ensembl GTF; each protein keeps the longest CDS among mapped transcripts.",
    },
    {
        "organism": "halobacterium_salinarum",
        "organism_label": "Halobacterium salinarum NRC-1",
        "ncbi_taxid": "64091",
        "cds_url": "https://ftp.ncbi.nlm.nih.gov/genomes/all/GCA/000/006/805/GCA_000006805.1_ASM680v1/GCA_000006805.1_ASM680v1_cds_from_genomic.fna.gz",
        "cds_source_name": "NCBI GenBank GCA_000006805.1 ASM680v1 cds_from_genomic",
        "join_method": "PAXdb external id after taxid prefix is matched exactly to unique NCBI GenBank CDS header identifiers, primarily original VNG locus tags.",
    },
    {
        "organism": "sulfolobus_solfataricus",
        "organism_label": "Sulfolobus solfataricus P2",
        "ncbi_taxid": "273057",
        "cds_url": "https://ftp.ncbi.nlm.nih.gov/genomes/all/GCA/000/007/005/GCA_000007005.1_ASM700v1/GCA_000007005.1_ASM700v1_cds_from_genomic.fna.gz",
        "cds_source_name": "NCBI GenBank GCA_000007005.1 ASM700v1 cds_from_genomic",
        "join_method": "PAXdb external id after taxid prefix is matched exactly to unique NCBI GenBank CDS header identifiers, primarily original SSO locus tags.",
    },
    {
        "organism": "dictyostelium_discoideum",
        "organism_label": "Dictyostelium discoideum",
        "ncbi_taxid": "44689",
        "cds_url": "https://ftp.ensemblgenomes.ebi.ac.uk/pub/protists/current/fasta/dictyostelium_discoideum/cds/Dictyostelium_discoideum.dicty_2.7.cds.all.fa.gz",
        "cds_source_name": "EnsemblProtists Dictyostelium_discoideum dicty_2.7 current cds.all",
        "gtf_url": "https://ftp.ensemblgenomes.ebi.ac.uk/pub/protists/current/gtf/dictyostelium_discoideum/Dictyostelium_discoideum.dicty_2.7.63.gtf.gz",
        "gtf_source_name": "EnsemblProtists Dictyostelium_discoideum dicty_2.7 release 63 GTF",
        "uniprot_mapping_url": "https://rest.uniprot.org/uniprotkb/stream?query=organism_id%3A44689&format=tsv&fields=accession%2Cgene_primary%2Cxref_dictybase%2Cxref_refseq%2Cxref_embl",
        "uniprot_mapping_source_name": "UniProtKB organism_id:44689 accession cross-references",
        "join_method": "PAXdb external id after taxid prefix is mapped by HTTP-fetched UniProtKB accession cross-references to explicit dictyBase/RefSeq/EMBL identifiers present in EnsemblProtists CDS FASTA/GTF; accession mappings resolving to multiple distinct CDS records are discarded.",
    },
    {
        "organism": "rattus_norvegicus",
        "organism_label": "Rattus norvegicus",
        "ncbi_taxid": "10116",
        "cds_url": "https://ftp.ensembl.org/pub/release-115/fasta/rattus_norvegicus/cds/Rattus_norvegicus.GRCr8.cds.all.fa.gz",
        "cds_source_name": "Ensembl Rattus_norvegicus GRCr8 release 115 cds.all",
        "gtf_url": "https://ftp.ensembl.org/pub/release-115/gtf/rattus_norvegicus/Rattus_norvegicus.GRCr8.115.gtf.gz",
        "gtf_source_name": "Ensembl Rattus_norvegicus GRCr8 release 115 GTF",
        "join_method": "PAXdb external id after taxid prefix is matched exactly to Ensembl protein_id from the HTTP-fetched Ensembl GTF; each protein keeps the longest CDS among mapped transcripts.",
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


def parse_colon_fields(header: str) -> dict[str, list[str]]:
    fields: dict[str, list[str]] = {}
    for token in header.split():
        if ":" not in token:
            continue
        key, value = token.split(":", 1)
        if key in {"chromosome", "scaffold", "primary_assembly", "description"}:
            continue
        fields.setdefault(key, []).append(value)
    return fields


def strip_version(identifier: str) -> str:
    if re.search(r"\.[0-9]+$", identifier):
        return identifier.rsplit(".", 1)[0]
    return identifier


def parse_gtf_attributes(attributes: str) -> dict[str, list[str]]:
    fields: dict[str, list[str]] = {}
    for key, value in re.findall(r'([A-Za-z_][A-Za-z0-9_]*) "([^"]*)"', attributes):
        fields.setdefault(key, []).append(value)
    return fields


def parse_gtf_transcript_to_identifiers(text: str) -> dict[str, set[str]]:
    mapping: dict[str, set[str]] = {}
    for raw_line in text.splitlines():
        if not raw_line or raw_line.startswith("#"):
            continue
        parts = raw_line.split("\t")
        if len(parts) != 9 or parts[2] != "CDS":
            continue
        fields = parse_gtf_attributes(parts[8])
        transcript_ids = fields.get("transcript_id", [])
        if not transcript_ids:
            continue
        identifiers: set[str] = set()
        for key in ("protein_id", "ccds_id", "exon_id", "gene_id", "gene_name", "transcript_name"):
            for value in fields.get(key, []):
                identifiers.add(value)
                identifiers.add(strip_version(value))
        for transcript_id in transcript_ids:
            for key in (transcript_id, strip_version(transcript_id)):
                mapping.setdefault(key, set()).update(x for x in identifiers if x)
    return mapping


def parse_uniprot_identifier_mapping(text: str) -> dict[str, set[str]]:
    mapping: dict[str, set[str]] = {}
    lines = text.splitlines()
    if not lines:
        return mapping
    headers = lines[0].split("\t")
    try:
        accession_index = headers.index("Entry")
    except ValueError:
        return mapping
    for line in lines[1:]:
        if not line.strip():
            continue
        parts = line.split("\t")
        if accession_index >= len(parts):
            continue
        accession = parts[accession_index].strip()
        if not accession:
            continue
        identifiers: set[str] = set()
        for value in parts[1:]:
            for item in re.split(r"[;\s]+", value):
                item = item.strip()
                if not item:
                    continue
                identifiers.add(item)
                identifiers.add(strip_version(item))
        if identifiers:
            mapping.setdefault(accession, set()).update(identifiers)
    return mapping


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
    colon_fields = parse_colon_fields(header)
    identifiers: set[str] = set()
    first_token = header.split(None, 1)[0]
    identifiers.add(first_token)
    identifiers.add(strip_version(first_token))
    for key in ("locus_tag", "gene", "protein_id"):
        for value in fields.get(key, []):
            identifiers.add(value)
            identifiers.add(strip_version(value))
            if re.fullmatch(r"[A-Za-z]+_[0-9]+", value):
                identifiers.add(value.replace("_", ""))
    for key in ("gene", "gene_symbol"):
        for value in colon_fields.get(key, []):
            identifiers.add(value)
            identifiers.add(strip_version(value))
    for value in fields.get("db_xref", []):
        for component in value.split(","):
            identifiers.add(component)
            if ":" in component:
                identifiers.add(component.split(":", 1)[1])
    if "_cds_" in first_token:
        tail = first_token.split("_cds_", 1)[1]
        if "_" in tail:
            identifiers.add(tail.rsplit("_", 1)[0])
    return {x for x in identifiers if x}


def transcript_identifier(header: str) -> str:
    return header.split(None, 1)[0]


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


def longest_identifier_index(
    cds_records: list[dict[str, object]],
    gtf_mapping: dict[str, set[str]] | None = None,
) -> tuple[dict[str, dict[str, object]], dict[str, int]]:
    buckets: dict[str, list[dict[str, object]]] = {}
    for record in cds_records:
        identifiers = set(header_identifiers(str(record["header"])))
        if gtf_mapping is not None:
            transcript_id = transcript_identifier(str(record["header"]))
            identifiers.update(gtf_mapping.get(transcript_id, set()))
            identifiers.update(gtf_mapping.get(strip_version(transcript_id), set()))
        for identifier in identifiers:
            buckets.setdefault(identifier, []).append(record)
    selected: dict[str, dict[str, object]] = {}
    multiplicities: dict[str, int] = {}
    for identifier, records in buckets.items():
        multiplicities[identifier] = len(records)
        selected[identifier] = max(records, key=lambda record: len(str(record["seq"])))
    return selected, multiplicities


def abundance_rows_from_local_file(config: dict[str, str]) -> tuple[list[dict[str, object]], dict[str, object], bytes]:
    path = DATA_DIR / f"proteomics_abundance_{config['organism']}.json"
    data = json.loads(path.read_text())
    protein_abundance = data.get("protein_abundance", {})
    if not isinstance(protein_abundance, dict):
        raise ValueError(f"{path} has no protein_abundance object")
    rows: list[dict[str, object]] = []
    taxid = config["ncbi_taxid"]
    for protein_id, abundance_ppm in protein_abundance.items():
        if not str(protein_id).startswith(taxid + "."):
            continue
        rows.append(
            {
                "gene_name": "",
                "protein_id": protein_id,
                "ext_id": str(protein_id).split(".", 1)[1],
                "abundance_ppm": abundance_ppm,
            }
        )
    raw_text = str(data.get("raw_payload_text", ""))
    raw_payload = raw_text.encode("utf-8")
    expected_sha = data.get("payload_sha256")
    if expected_sha and sha256_hex(raw_payload) != expected_sha:
        raise ValueError(f"{path} raw_payload_text sha256 does not match payload_sha256")
    return rows, data, raw_payload


def join_records(
    abundance_rows: list[dict[str, object]],
    cds_unique: dict[str, dict[str, object]],
) -> tuple[list[dict[str, object]], dict[str, int]]:
    joined: list[dict[str, object]] = []
    match_sources = {"ext_id": 0, "gene_name": 0, "mapped_id": 0}
    for row in abundance_rows:
        candidates = [
            ("ext_id", str(row["ext_id"])),
            ("gene_name", str(row["gene_name"])),
        ]
        for mapped_id in row.get("cds_candidate_ids", []):
            candidates.append(("mapped_id", str(mapped_id)))
        match_kind = ""
        match_id = ""
        cds_record: dict[str, object] | None = None
        candidate_matches: dict[str, tuple[str, str, dict[str, object]]] = {}
        for candidate_kind, candidate_id in candidates:
            if candidate_id in cds_unique:
                record = cds_unique[candidate_id]
                candidate_matches[str(record["header"])] = (candidate_kind, candidate_id, record)
        if len(candidate_matches) == 1:
            match_kind, match_id, cds_record = next(iter(candidate_matches.values()))
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
                "cds_match_id": match_id,
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


def build_target_organism(config: dict[str, str]) -> tuple[dict[str, object] | None, dict[str, object]]:
    started = datetime.now(timezone.utc).isoformat()
    try:
        cds_raw_gz = fetch_bytes(config["cds_url"])
        cds_text = gzip.decompress(cds_raw_gz).decode("utf-8", "replace")
        abundance_rows, abundance_metadata, paxdb_raw = abundance_rows_from_local_file(config)
        cds_records = parse_fasta(cds_text)
        gtf_mapping: dict[str, set[str]] | None = None
        gtf_raw_gz: bytes | None = None
        gtf_text = ""
        uniprot_mapping: dict[str, set[str]] | None = None
        uniprot_raw: bytes | None = None
        uniprot_text = ""
        if config.get("gtf_url"):
            gtf_raw_gz = fetch_bytes(config["gtf_url"])
            gtf_text = gzip.decompress(gtf_raw_gz).decode("utf-8", "replace")
            gtf_mapping = parse_gtf_transcript_to_identifiers(gtf_text)
            cds_index, multiplicities = longest_identifier_index(cds_records, gtf_mapping)
            index_policy = "longest_cds_per_identifier"
        else:
            cds_index, multiplicities = unique_identifier_index(cds_records)
            index_policy = "unique_identifier_only"
        if config.get("uniprot_mapping_url"):
            uniprot_raw = fetch_bytes(config["uniprot_mapping_url"])
            uniprot_text = uniprot_raw.decode("utf-8", "replace")
            uniprot_mapping = parse_uniprot_identifier_mapping(uniprot_text)
            for row in abundance_rows:
                candidates = sorted(uniprot_mapping.get(str(row["ext_id"]), set()))
                if candidates:
                    row["cds_candidate_ids"] = candidates
        joined, match_sources = join_records(abundance_rows, cds_index)
        n_abundance = len(abundance_rows)
        n_joined = len(joined)
        hit_rate = n_joined / n_abundance if n_abundance else 0.0
        output = {
            "schema_version": 1,
            "organism": config["organism"],
            "organism_label": config["organism_label"],
            "ncbi_taxid": config["ncbi_taxid"],
            "source_kind": "ensembl_or_ncbi_cds + local_verified_paxdb_join",
            "source_name": "HTTP-fetched CDS FASTA joined to locally archived PAXdb protein abundance",
            "cds_source_name": config["cds_source_name"],
            "cds_source_url": config["cds_url"],
            "cds_payload_sha256": sha256_hex(cds_raw_gz),
            "cds_payload_byte_size": len(cds_raw_gz),
            "cds_payload_raw_prefix_base64": raw_prefix_b64(cds_raw_gz),
            "cds_payload_raw_prefix_byte_count": min(RAW_SLICE_BYTES, len(cds_raw_gz)),
            "cds_payload_decompressed_prefix_text": cds_text[:RAW_SLICE_BYTES],
            "cds_payload_note": "full_raw_gzip_payload_sha256 plus deterministic raw gzip prefix slice; decompressed FASTA parsed deterministically",
            "paxdb_source_url": str(abundance_metadata.get("source_url", "")),
            "paxdb_payload_sha256": str(abundance_metadata.get("payload_sha256", sha256_hex(paxdb_raw))),
            "paxdb_payload_byte_size": int(abundance_metadata.get("payload_byte_size", len(paxdb_raw))),
            "paxdb_payload_raw_prefix_text": paxdb_raw[:RAW_SLICE_BYTES].decode("utf-8", "replace"),
            "paxdb_payload_raw_prefix_byte_count": min(RAW_SLICE_BYTES, len(paxdb_raw)),
            "paxdb_payload_note": "local proteomics_abundance raw_payload_text sha256 checked against its archived payload_sha256",
            "paxdb_name": abundance_metadata.get("paxdb_name"),
            "paxdb_filename": abundance_metadata.get("paxdb_filename"),
            "join_method": config["join_method"],
            "join_policy": "Only exact identifier matches present in fetched CDS/GTF payloads are accepted. Unmatched proteins are discarded.",
            "join_index_policy": index_policy,
            "join_match_sources": match_sources,
            "n_cds_records": len(cds_records),
            "n_unique_cds_identifiers": len(cds_index),
            "n_abundance_proteins": n_abundance,
            "n_joined": n_joined,
            "join_hit_rate": hit_rate,
            "fetched_at": started,
            "fetched_by": USER_AGENT,
            "joined": joined,
            "cannot_claim": [
                "measured abundance + real CDS codon; 非 translation rate; 非 mechanism",
                "PAXdb abundance does not by itself establish ribosome occupancy, elongation speed, folding, function, phenotype, or fitness.",
                "The join is identifier-level evidence only; proteins without exact CDS identifiers are discarded.",
            ],
            "derivation_boundary": "not_bedc_kernel_content",
        }
        if gtf_raw_gz is not None:
            output.update(
                {
                    "id_mapping_source_name": config["gtf_source_name"],
                    "id_mapping_source_url": config["gtf_url"],
                    "id_mapping_payload_sha256": sha256_hex(gtf_raw_gz),
                    "id_mapping_payload_byte_size": len(gtf_raw_gz),
                    "id_mapping_payload_raw_prefix_base64": raw_prefix_b64(gtf_raw_gz),
                    "id_mapping_payload_raw_prefix_byte_count": min(RAW_SLICE_BYTES, len(gtf_raw_gz)),
                    "id_mapping_payload_decompressed_prefix_text": gtf_text[:RAW_SLICE_BYTES],
                    "id_mapping_payload_note": "full_raw_gzip_payload_sha256 for GTF used only to map transcript_id to protein_id and other explicit attributes",
                    "n_id_mapping_transcripts": len(gtf_mapping or {}),
                }
            )
        if uniprot_raw is not None:
            output.update(
                {
                    "secondary_id_mapping_source_name": config["uniprot_mapping_source_name"],
                    "secondary_id_mapping_source_url": config["uniprot_mapping_url"],
                    "secondary_id_mapping_payload_sha256": sha256_hex(uniprot_raw),
                    "secondary_id_mapping_payload_byte_size": len(uniprot_raw),
                    "secondary_id_mapping_payload_raw_prefix_text": uniprot_text[:RAW_SLICE_BYTES],
                    "secondary_id_mapping_payload_raw_prefix_byte_count": min(RAW_SLICE_BYTES, len(uniprot_raw)),
                    "secondary_id_mapping_payload_note": "full raw TSV payload sha256 for UniProt accession cross-references used only to map PAXdb accessions to explicit CDS/GTF identifiers",
                    "n_secondary_id_mapping_accessions": len(uniprot_mapping or {}),
                }
            )
        manifest_row = {
            "organism": config["organism"],
            "organism_label": config["organism_label"],
            "ncbi_taxid": config["ncbi_taxid"],
            "status": "success",
            "n_abundance_proteins": n_abundance,
            "n_joined": n_joined,
            "join_hit_rate": hit_rate,
            "usable_for_powered_per_protein_s_qp": hit_rate > 0.2 and n_joined >= 1000,
            "cds_source_url": config["cds_url"],
            "cds_payload_sha256": sha256_hex(cds_raw_gz),
            "paxdb_source_url": str(abundance_metadata.get("source_url", "")),
            "paxdb_payload_sha256": str(abundance_metadata.get("payload_sha256", sha256_hex(paxdb_raw))),
            "output_file": f"tools/bio_reality/data/cds_codon_abundance_{config['organism']}.json",
            "join_method": config["join_method"],
            "join_match_sources": match_sources,
            "join_index_policy": index_policy,
            "n_cds_records": len(cds_records),
            "n_unique_cds_identifiers": len(cds_index),
            "ambiguous_identifier_count": sum(1 for n in multiplicities.values() if n > 1),
        }
        if gtf_raw_gz is not None:
            manifest_row.update(
                {
                    "id_mapping_source_url": config["gtf_url"],
                    "id_mapping_payload_sha256": sha256_hex(gtf_raw_gz),
                    "n_id_mapping_transcripts": len(gtf_mapping or {}),
                }
            )
        if uniprot_raw is not None:
            manifest_row.update(
                {
                    "secondary_id_mapping_source_url": config["uniprot_mapping_url"],
                    "secondary_id_mapping_payload_sha256": sha256_hex(uniprot_raw),
                    "n_secondary_id_mapping_accessions": len(uniprot_mapping or {}),
                }
            )
        return output, manifest_row
    except Exception as exc:
        return None, {
            "organism": config["organism"],
            "organism_label": config["organism_label"],
            "ncbi_taxid": config["ncbi_taxid"],
            "status": "failed",
            "reason": f"{type(exc).__name__}: {exc}",
            "cds_source_url": config["cds_url"],
            "id_mapping_source_url": config.get("gtf_url"),
        }


def load_existing_manifest_rows() -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    manifest_path = DATA_DIR / "cds_codon_campaign_manifest.json"
    if not manifest_path.exists():
        return [], []
    manifest = json.loads(manifest_path.read_text())
    successes = [row for row in manifest.get("successes", []) if isinstance(row, dict)]
    failures = [row for row in manifest.get("failures", []) if isinstance(row, dict)]
    return successes, failures


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
    existing_successes, existing_failures = load_existing_manifest_rows()
    rows_by_organism = {
        str(row.get("organism")): row
        for row in existing_successes + existing_failures
    }
    for config in TARGET_ORGANISMS:
        output, row = build_target_organism(config)
        rows_by_organism[config["organism"]] = row
        if output is None:
            continue
        assert_output_integrity(output)
        output_path = DATA_DIR / f"cds_codon_abundance_{config['organism']}.json"
        output_path.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    manifest_rows = list(rows_by_organism.values())
    successes = [row for row in manifest_rows if row.get("status") == "success"]
    failures = [row for row in manifest_rows if row.get("status") == "failed"]
    usable = [
        {"organism": row["organism"], "n_joined": row["n_joined"]}
        for row in successes
        if row.get("usable_for_powered_per_protein_s_qp")
    ]
    manifest = {
        "schema_version": 1,
        "source_name": "per-protein CDS codon composition joined to PAXdb abundance",
        "source_kind": "real_http_fetch_only",
        "raw_payload_policy": "Each CDS FASTA gzip payload was fetched by HTTP and recorded by full raw payload sha256. Ensembl GTF mapping payloads, where used, were also fetched by HTTP and sha256 archived. PAXdb abundance payloads are locally archived proteomics_abundance raw payloads checked by sha256.",
        "fetched_at": datetime.now(timezone.utc).isoformat(),
        "fetched_by": USER_AGENT,
        "target_relation": "powered per-protein S^QP input table",
        "organism_count": len(manifest_rows),
        "success_count": len(successes),
        "failure_count": len(failures),
        "successes": successes,
        "failures": failures,
        "organisms": manifest_rows,
        "total_joined_proteins": sum(int(row["n_joined"]) for row in successes),
        "usable_powered_per_protein_s_qp": usable,
        "cannot_claim": [
            "measured abundance + real CDS codon; 非 translation rate; 非 mechanism",
            "No newly attempted organism is retained without a true HTTP-fetched CDS payload.",
            "No protein is retained without an exact identifier join between PAXdb and CDS FASTA/GTF evidence.",
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

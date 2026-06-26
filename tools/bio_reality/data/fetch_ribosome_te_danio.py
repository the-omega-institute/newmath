#!/usr/bin/env python3
"""Fetch danio rerio measured ribosome-profiling translation efficiency data."""

from __future__ import annotations

import gzip
import hashlib
import json
import math
import re
import urllib.request
from datetime import datetime, timezone
from pathlib import Path


DATA_DIR = Path(__file__).resolve().parent
USER_AGENT = "BioReality-Codex-RiboTE"
DERIVATION_BOUNDARY = "not_bedc_kernel_content"
STUDY = "GSE53693"
RPFDB_BASE = "https://sysbio.gzzoc.com/rpfdb"

DANIO_URLS = {
    "translation_efficiency_cds": f"{RPFDB_BASE}/data/TranslationEff/D.rerio_{STUDY}_TE_CDS.txt.gz",
    "riboseq_rawcount": f"{RPFDB_BASE}/data/Rawcount/D.rerio_{STUDY}_rawcount.metatable.gz",
    "rnaseq_rawcount": f"{RPFDB_BASE}/data/Rawcount_RNAseq/D.rerio_{STUDY}_rawcount.metatable.gz",
}

CANNOT_CLAIM = [
    "measured TE from one zebrafish ribo-seq dataset; condition-specific and not causal",
    "RPFdb processed CDS TE is used as a direct measured TE readout, not as a universal danio rerio translation-efficiency constant",
    "the Ribo-seq and RNA-seq rawcount columns are retained as positive support measurements and are not claimed to reproduce RPFdb's internal normalization",
    "gene-level Ensembl IDs are mapped to one longest-CDS ENSDARP representative; unmapped genes and non-positive measurements are discarded",
    "this dataset does not by itself identify a mechanism, developmental universal, or vertebrate-wide law",
]


def fetch_payload(url: str) -> bytes:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=180) as response:
        return response.read()


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def combined_payload_sha(payloads: dict[str, bytes]) -> str:
    h = hashlib.sha256()
    for key in sorted(payloads):
        h.update(key.encode("utf-8"))
        h.update(b"\0")
        h.update(hashlib.sha256(payloads[key]).hexdigest().encode("ascii"))
        h.update(b"\0")
    return h.hexdigest()


def payload_archive(payloads: dict[str, bytes], urls: dict[str, str]) -> dict[str, dict[str, object]]:
    archive = {}
    for key in sorted(payloads):
        archive[key] = {
            "source_url": urls[key],
            "payload_sha256": sha256_hex(payloads[key]),
            "payload_byte_size": len(payloads[key]),
        }
    return archive


def mean_positive_values(parts: list[str]) -> float | None:
    values = []
    for raw in parts:
        if raw in {"", "NA", "NaN", "nan"}:
            continue
        try:
            value = float(raw)
        except ValueError:
            continue
        if math.isfinite(value) and value > 0.0:
            values.append(value)
    if not values:
        return None
    return sum(values) / float(len(values))


def parse_mean_positive_table(raw_gz: bytes, expected_first_header: str) -> dict[str, float]:
    text = gzip.decompress(raw_gz).decode("utf-8", "replace")
    lines = text.splitlines()
    if not lines:
        raise ValueError("empty RPFdb table")
    header = lines[0].rstrip("\t").split("\t")
    if not header or header[0] != expected_first_header:
        raise ValueError(f"unexpected RPFdb header: {header[:3]!r}")
    rows: dict[str, float] = {}
    for line in lines[1:]:
        if not line.strip():
            continue
        parts = line.rstrip("\t").split("\t")
        if len(parts) < 2:
            continue
        gene_key = parts[0].split(".", 1)[0]
        if not gene_key.startswith("ENSDARG"):
            continue
        value = mean_positive_values(parts[1:])
        if value is None:
            continue
        rows[gene_key] = value
    return rows


def load_danio_cds_representatives() -> tuple[dict[str, dict[str, object]], int]:
    with (DATA_DIR / "cds_codon_abundance_danio_rerio.json").open("r", encoding="utf-8") as f:
        payload = json.load(f)
    joined = payload["joined"]
    representatives: dict[str, dict[str, object]] = {}
    for row in joined:
        header = str(row.get("cds_header", ""))
        match = re.search(r"gene:(ENSDARG[0-9]+)(?:\.[0-9]+)?", header)
        if not match:
            continue
        gene_key = match.group(1)
        current = representatives.get(gene_key)
        if current is None:
            representatives[gene_key] = row
            continue
        current_len = int(current.get("cds_len_nt", 0))
        row_len = int(row.get("cds_len_nt", 0))
        if (row_len, str(row.get("protein_id", ""))) > (current_len, str(current.get("protein_id", ""))):
            representatives[gene_key] = row
    return representatives, len(joined)


def build_danio() -> dict[str, object]:
    payloads = {key: fetch_payload(url) for key, url in DANIO_URLS.items()}
    te_by_gene = parse_mean_positive_table(payloads["translation_efficiency_cds"], "Gene_ID")
    footprint_by_gene = parse_mean_positive_table(payloads["riboseq_rawcount"], "Gene_ID")
    mrna_by_gene = parse_mean_positive_table(payloads["rnaseq_rawcount"], "Geneid")
    representatives, universe_n = load_danio_cds_representatives()

    genes = []
    for gene_key in sorted(te_by_gene):
        te = te_by_gene[gene_key]
        if not math.isfinite(te) or te <= 0.0:
            continue
        row = representatives.get(gene_key)
        if row is None:
            continue
        footprint = footprint_by_gene.get(gene_key)
        if footprint is None or footprint <= 0.0:
            continue
        mrna = mrna_by_gene.get(gene_key)
        if mrna is None or mrna <= 0.0:
            continue
        genes.append(
            {
                "protein_id": row["protein_id"],
                "gene_key": gene_key,
                "te": float(te),
                "footprint": float(footprint),
                "mrna": float(mrna),
            }
        )

    return {
        "organism": "danio_rerio",
        "ncbi_taxid": 7955,
        "source_kind": "RPFdb processed CDS translation-efficiency table with matched Ribo-seq and RNA-seq rawcount support",
        "source_url": DANIO_URLS["translation_efficiency_cds"],
        "source_urls": [DANIO_URLS[key] for key in sorted(DANIO_URLS)],
        "study_ref": "RPFdb processed Danio rerio GSE53693, Bazzini et al. 2014 EMBO Journal, identification of small ORFs in vertebrates using ribosome footprinting and evolutionary conservation",
        "payload_sha256": combined_payload_sha(payloads),
        "payload_sha256_by_url": payload_archive(payloads, DANIO_URLS),
        "te_definition": "direct positive RPFdb CDS translation-efficiency value from D.rerio_GSE53693_TE_CDS.txt.gz, averaged across positive TE columns for each Ensembl gene; footprint and mRNA fields are mean positive rawcounts from the matched Ribo-seq and RNA-seq RPFdb rawcount tables for the same study and gene",
        "id_mapping_method": "RPFdb Ensembl gene IDs are stripped of version suffix and matched exactly to the gene:ENSDARG field in the existing BioReality Danio rerio Ensembl CDS headers; when multiple CDS records share one Ensembl gene, the longest CDS representative protein_id is emitted; all unmapped or non-positive genes are skipped.",
        "n_genes_with_te": len(genes),
        "join_hit_rate": len(genes) / float(universe_n) if universe_n else 0.0,
        "join_universe_n": universe_n,
        "genes": genes,
        "cannot_claim": CANNOT_CLAIM,
        "derivation_boundary": DERIVATION_BOUNDARY,
    }


def assert_result(result: dict[str, object]) -> None:
    genes = result["genes"]
    if not isinstance(genes, list):
        raise AssertionError("genes must be a list")
    if result["n_genes_with_te"] != len(genes):
        raise AssertionError("n_genes_with_te mismatch")
    seen = set()
    for gene in genes:
        if gene["protein_id"] in seen:
            raise AssertionError(f"duplicate protein_id: {gene['protein_id']}")
        seen.add(gene["protein_id"])
        for key in ("te", "footprint", "mrna"):
            value = gene[key]
            if not isinstance(value, float) or not math.isfinite(value) or value <= 0.0:
                raise AssertionError(f"bad {key} value: {gene!r}")


def write_json(filename: str, data: dict[str, object]) -> None:
    with (DATA_DIR / filename).open("w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")


def main() -> None:
    result = build_danio()
    result["fetched_at"] = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    result["fetched_by"] = USER_AGENT
    assert_result(result)
    write_json("ribosome_te_danio_rerio.json", result)
    print(
        result["organism"],
        "n=",
        result["n_genes_with_te"],
        "hit_rate=",
        f"{result['join_hit_rate']:.6f}",
        "sha=",
        result["payload_sha256"],
    )


if __name__ == "__main__":
    main()

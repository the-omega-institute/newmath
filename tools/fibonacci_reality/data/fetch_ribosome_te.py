#!/usr/bin/env python3
"""Fetch measured ribosome-profiling translation efficiency data.

Only processed public payloads are used.  A gene is emitted only when both
footprint and mRNA measurements are present and join exactly to the existing
FibonacciReality protein_id universe.
"""

from __future__ import annotations

import gzip
import hashlib
import json
import math
import re
import urllib.request
from array import array
from datetime import datetime, timezone
from pathlib import Path


DATA_DIR = Path(__file__).resolve().parent
USER_AGENT = "FibonacciReality-Codex-RiboTE"
DERIVATION_BOUNDARY = "not_bedc_kernel_content"
CANNOT_CLAIM = [
    "measured TE from one/few ribo-seq datasets; condition-specific; still not causal",
]


YEAST_URLS = {
    "footprint_rep1": "https://ftp.ncbi.nlm.nih.gov/geo/samples/GSM346nnn/GSM346111/suppl/GSM346111_fp_rich1_quant.txt.gz",
    "footprint_rep2": "https://ftp.ncbi.nlm.nih.gov/geo/samples/GSM346nnn/GSM346114/suppl/GSM346114_fp_rich1_quant.txt.gz",
    "mrna_rep1": "https://ftp.ncbi.nlm.nih.gov/geo/samples/GSM346nnn/GSM346117/suppl/GSM346117_mrna_rich1_quant.txt.gz",
    "mrna_rep2": "https://ftp.ncbi.nlm.nih.gov/geo/samples/GSM346nnn/GSM346118/suppl/GSM346118_mrna_rich2_quant.txt.gz",
    "readme": "https://ftp.ncbi.nlm.nih.gov/geo/samples/GSM346nnn/GSM346111/suppl/GSM346111_readMe.txt.gz",
}

ECOLI_URLS = {
    "footprint_forward": "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE53nnn/GSE53767/suppl/GSE53767_fp_rdm_pooled_f.wig.gz",
    "footprint_reverse": "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE53nnn/GSE53767/suppl/GSE53767_fp_rdm_pooled_r.wig.gz",
    "mrna_forward": "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE53nnn/GSE53767/suppl/GSE53767_mrna-rdm-pooled_f.wig.gz",
    "mrna_reverse": "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE53nnn/GSE53767/suppl/GSE53767_mrna-rdm-pooled_r.wig.gz",
    "family_soft": "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE53nnn/GSE53767/soft/GSE53767_family.soft.gz",
}


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


def load_join_universe(filename: str) -> list[dict[str, object]]:
    with (DATA_DIR / filename).open("r", encoding="utf-8") as f:
        data = json.load(f)
    return list(data["joined"])


def parse_yeast_quant(raw_gz: bytes) -> dict[str, dict[str, float]]:
    text = gzip.decompress(raw_gz).decode("utf-8", "replace")
    rows: dict[str, dict[str, float]] = {}
    lines = text.splitlines()
    if not lines or lines[0].split("\t")[:6] != ["yorf", "norm", "dens", "count", "len", "total"]:
        raise ValueError("unexpected yeast quant header")
    for line in lines[1:]:
        if not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) < 6:
            continue
        feature = parts[0]
        rows[feature] = {
            "norm": float(parts[1]),
            "dens": float(parts[2]),
            "count": float(parts[3]),
            "length_nt": float(parts[4]),
            "total_cds_aligned_reads": float(parts[5]),
        }
    return rows


def mean_present(values: list[float]) -> float | None:
    if not values:
        return None
    return sum(values) / float(len(values))


def build_yeast() -> dict[str, object]:
    payloads = {key: fetch_payload(url) for key, url in YEAST_URLS.items()}
    fp_tables = [
        parse_yeast_quant(payloads["footprint_rep1"]),
        parse_yeast_quant(payloads["footprint_rep2"]),
    ]
    mrna_tables = [
        parse_yeast_quant(payloads["mrna_rep1"]),
        parse_yeast_quant(payloads["mrna_rep2"]),
    ]

    universe = load_join_universe("cds_codon_abundance_saccharomyces_cerevisiae.json")
    genes = []
    for row in universe:
        gene_key = str(row["cds_match_id"])
        footprint = mean_present([table[gene_key]["norm"] for table in fp_tables if gene_key in table])
        mrna = mean_present([table[gene_key]["norm"] for table in mrna_tables if gene_key in table])
        if footprint is None or mrna is None or footprint <= 0.0 or mrna <= 0.0:
            continue
        te = footprint / mrna
        if not math.isfinite(te) or te <= 0.0:
            continue
        genes.append(
            {
                "protein_id": row["protein_id"],
                "gene_key": gene_key,
                "te": te,
                "footprint": footprint,
                "mrna": mrna,
            }
        )

    return {
        "organism": "saccharomyces_cerevisiae",
        "ncbi_taxid": 4932,
        "source_kind": "GEO processed per-feature ribosome-profiling quantification",
        "source_url": "https://www.ncbi.nlm.nih.gov/geo/query/acc.cgi?acc=GSE13750",
        "source_urls": [YEAST_URLS[key] for key in sorted(YEAST_URLS)],
        "study_ref": "Ingolia et al. 2009 Science, GSE13750, BY4741 mid-exponential rich medium footprint and mRNA quant files",
        "payload_sha256": combined_payload_sha(payloads),
        "payload_sha256_by_url": payload_archive(payloads, YEAST_URLS),
        "te_definition": "mean footprint normalized read density rpkM across two rich-medium replicates divided by mean mRNA normalized read density rpkM across two rich-medium replicates; quant readMe defines column 2 as normalized read density [rpkM]",
        "id_mapping_method": "Exact join from FibonacciReality protein_id suffix 4932.<systematic_ORF> to GEO quant feature name; UTR/intron features are ignored because only exact ORF feature names are accepted.",
        "n_genes_with_te": len(genes),
        "join_hit_rate": len(genes) / float(len(universe)) if universe else 0.0,
        "join_universe_n": len(universe),
        "genes": genes,
        "cannot_claim": CANNOT_CLAIM,
        "derivation_boundary": DERIVATION_BOUNDARY,
    }


def parse_ecoli_location(cds_header: str) -> tuple[int, int, str] | None:
    m = re.search(r"\[location=([^\]]+)\]", cds_header)
    if not m:
        return None
    loc = m.group(1)
    strand = "reverse" if loc.startswith("complement(") else "forward"
    nums = [int(x) for x in re.findall(r"\d+", loc)]
    if len(nums) < 2:
        return None
    start = min(nums)
    end = max(nums)
    if start <= 0 or end < start:
        return None
    return start, end, strand


def load_wig_prefix(raw_gz: bytes, genome_size: int) -> array:
    coverage = array("d", [0.0]) * (genome_size + 2)
    text = gzip.decompress(raw_gz).decode("utf-8", "replace")
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith(("#", "track", "variableStep", "fixedStep")):
            continue
        parts = line.split()
        if len(parts) < 2:
            continue
        pos = int(parts[0])
        if 1 <= pos <= genome_size:
            coverage[pos] = float(parts[1])
    running = 0.0
    for i in range(1, genome_size + 1):
        running += coverage[i]
        coverage[i] = running
    return coverage


def interval_mean(prefix: array, start: int, end: int) -> float:
    return (prefix[end] - prefix[start - 1]) / float(end - start + 1)


def build_ecoli() -> dict[str, object]:
    payloads = {key: fetch_payload(url) for key, url in ECOLI_URLS.items()}
    genome_size = 4641652
    fp_forward = load_wig_prefix(payloads["footprint_forward"], genome_size)
    fp_reverse = load_wig_prefix(payloads["footprint_reverse"], genome_size)
    mrna_forward = load_wig_prefix(payloads["mrna_forward"], genome_size)
    mrna_reverse = load_wig_prefix(payloads["mrna_reverse"], genome_size)

    universe = load_join_universe("cds_codon_abundance_escherichia_coli_k12_mg1655.json")
    genes = []
    for row in universe:
        loc = parse_ecoli_location(str(row["cds_header"]))
        if loc is None:
            continue
        start, end, strand = loc
        if end > genome_size:
            continue
        if strand == "forward":
            footprint = interval_mean(fp_forward, start, end)
            mrna = interval_mean(mrna_forward, start, end)
        else:
            footprint = interval_mean(fp_reverse, start, end)
            mrna = interval_mean(mrna_reverse, start, end)
        if footprint <= 0.0 or mrna <= 0.0:
            continue
        te = footprint / mrna
        if not math.isfinite(te) or te <= 0.0:
            continue
        genes.append(
            {
                "protein_id": row["protein_id"],
                "gene_key": row["cds_match_id"],
                "te": te,
                "footprint": footprint,
                "mrna": mrna,
            }
        )

    return {
        "organism": "escherichia_coli_k12_mg1655",
        "ncbi_taxid": 511145,
        "source_kind": "GEO processed pooled ribosome-profiling wiggle coverage",
        "source_url": "https://www.ncbi.nlm.nih.gov/geo/query/acc.cgi?acc=GSE53767",
        "source_urls": [ECOLI_URLS[key] for key in sorted(ECOLI_URLS)],
        "study_ref": "Li, Burkhardt, Gross, and Weissman 2014 Cell, GSE53767, random-fragment control pooled footprint and mRNA wig files",
        "payload_sha256": combined_payload_sha(payloads),
        "payload_sha256_by_url": payload_archive(payloads, ECOLI_URLS),
        "te_definition": "mean CDS footprint wiggle coverage on the annotated coding strand divided by mean CDS mRNA wiggle coverage on the same strand; CDS intervals and b-number joins come from the existing RefSeq NC_000913.3 FibonacciReality CDS file",
        "id_mapping_method": "Exact join from FibonacciReality protein_id suffix 511145.<b-number> to RefSeq CDS locus_tag b-number; coverage is summed over the matching CDS genomic interval and strand.",
        "n_genes_with_te": len(genes),
        "join_hit_rate": len(genes) / float(len(universe)) if universe else 0.0,
        "join_universe_n": len(universe),
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
    for gene in genes:
        te = gene["te"]
        if not isinstance(te, float) or not math.isfinite(te) or te <= 0.0:
            raise AssertionError(f"bad TE value: {gene!r}")
        for key in ("footprint", "mrna"):
            value = gene[key]
            if not isinstance(value, float) or not math.isfinite(value) or value <= 0.0:
                raise AssertionError(f"bad {key} value: {gene!r}")


def write_json(filename: str, data: dict[str, object]) -> None:
    with (DATA_DIR / filename).open("w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")


def main() -> None:
    fetched_at = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    successes = []
    failures = []
    results = []
    for slug, builder, filename in [
        ("saccharomyces_cerevisiae", build_yeast, "ribosome_te_saccharomyces_cerevisiae.json"),
        ("escherichia_coli_k12_mg1655", build_ecoli, "ribosome_te_escherichia_coli_k12_mg1655.json"),
    ]:
        try:
            result = builder()
            result["fetched_at"] = fetched_at
            result["fetched_by"] = USER_AGENT
            assert_result(result)
            write_json(filename, result)
            successes.append(
                {
                    "organism": slug,
                    "ncbi_taxid": result["ncbi_taxid"],
                    "n_genes_with_te": result["n_genes_with_te"],
                    "join_hit_rate": result["join_hit_rate"],
                    "source_kind": result["source_kind"],
                    "source_url": result["source_url"],
                    "source_urls": result["source_urls"],
                    "study_ref": result["study_ref"],
                    "payload_sha256": result["payload_sha256"],
                    "output_file": filename,
                }
            )
            results.append(result)
        except Exception as exc:
            failures.append({"organism": slug, "error": repr(exc)})

    manifest = {
        "campaign": "ribosome_te_measured",
        "fetched_at": fetched_at,
        "fetched_by": USER_AGENT,
        "derivation_boundary": DERIVATION_BOUNDARY,
        "policy": "Only real HTTP-fetched processed ribosome-profiling payloads are used; genes with missing or non-positive footprint/mRNA measurements are skipped.",
        "success_count": len(successes),
        "failure_count": len(failures),
        "organisms": successes,
        "failures": failures,
        "cannot_claim": CANNOT_CLAIM,
    }
    write_json("ribosome_te_campaign_manifest.json", manifest)

    for result in results:
        print(
            result["organism"],
            "n=",
            result["n_genes_with_te"],
            "hit_rate=",
            f"{result['join_hit_rate']:.6f}",
            "sha=",
            result["payload_sha256"],
        )
    for failure in failures:
        print("FAIL", failure["organism"], failure["error"])


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""抓取 Ingolia yeast ribo-seq chr_best 比对并构建逐密码子 A-site 占据窗口。"""

from __future__ import annotations

import gzip
import hashlib
import json
import math
import urllib.error
import urllib.parse
import urllib.request
from collections import defaultdict
from datetime import datetime, timezone
from io import BytesIO
from pathlib import Path


DATA_DIR = Path(__file__).resolve().parent
USER_AGENT = "BioReality-Codex-RiboPositional/1.0"
ORGANISM = "saccharomyces_cerevisiae"
HEAD_CODONS = 200
TAIL_CODONS = 60
A_SITE_OFFSET_NT = 15
BIN_SIZE = 1000

GFF_URL = (
    "https://ftp.ensembl.org/pub/release-110/gff3/saccharomyces_cerevisiae/"
    "Saccharomyces_cerevisiae.R64-1-1.110.gff3.gz"
)
README_URL = (
    "https://ftp.ncbi.nlm.nih.gov/geo/samples/GSM346nnn/GSM346111/suppl/"
    "GSM346111_readMe.txt.gz"
)
FOOTPRINT_URLS = {
    "footprint_rich_rep1": (
        "https://ftp.ncbi.nlm.nih.gov/geo/samples/GSM346nnn/GSM346111/suppl/"
        "GSM346111_fp_rich1_chr_best.txt.gz"
    ),
    "footprint_rich_rep2": (
        "https://ftp.ncbi.nlm.nih.gov/geo/samples/GSM346nnn/GSM346114/suppl/"
        "GSM346114_fp_rich2_chr_best.txt.gz"
    ),
}
OPTIONAL_PROBE_URLS = {
    "footprint_rich_rep2_rich1_name_probe": (
        "https://ftp.ncbi.nlm.nih.gov/geo/samples/GSM346nnn/GSM346114/suppl/"
        "GSM346114_fp_rich1_chr_best.txt.gz"
    ),
}

CANNOT_CLAIM = [
    "A-site offset=+15nt 是酵母 ribo-seq 的标准近似；没有按 read length 或实验条件重估 P-site/A-site offset。",
    "footprint 密度/占据不等于真实 dwell time 或 elongation rate 的因果测量。",
    "chr_best 比对文件只给出最佳比对坐标；多重定位、长度歧义和注释差异会限制映射覆盖率。",
    "本文件只保留每个基因 5 prime 前 200 codon 与 3 prime 后 60 codon 窗口，不保存全长占据。",
    "两个 rich-medium footprint replicate 取逐 codon 平均；没有建模 batch effect、mRNA abundance 或表达条件差异。",
]


def fetch_bytes(url: str, timeout: int = 240) -> bytes:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return response.read()


def probe_url(url: str) -> dict[str, object]:
    request = urllib.request.Request(url, method="HEAD", headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(request, timeout=90) as response:
            return {
                "status": "available",
                "http_status": response.status,
                "content_length": response.headers.get("Content-Length"),
            }
    except urllib.error.HTTPError as exc:
        return {"status": "unavailable", "http_status": exc.code, "reason": str(exc)}
    except urllib.error.URLError as exc:
        return {"status": "unavailable", "reason": str(exc)}


def sha256_hex(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def gz_text_lines(raw_gz: bytes):
    with gzip.GzipFile(fileobj=BytesIO(raw_gz)) as gz:
        for raw_line in gz:
            yield raw_line.decode("utf-8", "replace").rstrip("\n")


def parse_attrs(attr_text: str) -> dict[str, str]:
    attrs = {}
    for field in attr_text.split(";"):
        if not field or "=" not in field:
            continue
        key, value = field.split("=", 1)
        attrs[key] = urllib.parse.unquote(value)
    return attrs


def normalize_chrom(name: str) -> str:
    chrom = name.strip()
    if chrom.startswith("chr"):
        chrom = chrom[3:]
    mito_names = {"M", "MT", "Mt", "mito", "Mitochondrion", "Mitochondria"}
    if chrom in mito_names:
        return "Mito"
    return chrom


def load_ordered_cds() -> dict[str, dict[str, object]]:
    path = DATA_DIR / "cds_ordered_sequences_saccharomyces_cerevisiae.json"
    with path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    rows = data["cds"]
    return {str(row["gene_id"]): row for row in rows}


def parse_gff_cds(raw_gz: bytes, ordered: dict[str, dict[str, object]]) -> tuple[dict[str, dict[str, object]], dict[str, int]]:
    genes: dict[str, dict[str, object]] = {}
    stats = defaultdict(int)
    ordered_ids = set(ordered)
    for line in gz_text_lines(raw_gz):
        stats["gff_lines_total"] += 1
        if not line or line.startswith("#"):
            stats["gff_comment_or_blank_lines"] += 1
            continue
        parts = line.split("\t")
        if len(parts) != 9:
            stats["malformed_gff_lines"] += 1
            continue
        stats["gff_feature_lines"] += 1
        seqid, _source, feature, start_s, end_s, _score, strand, phase, attrs_s = parts
        if feature not in {"gene", "mRNA", "CDS"}:
            continue
        stats["feature_" + feature] += 1
        if feature != "CDS":
            continue
        attrs = parse_attrs(attrs_s)
        gene_id = attrs.get("protein_id") or attrs.get("gene_id") or attrs.get("ID", "").replace("CDS:", "")
        if not gene_id:
            stats["cds_without_gene_id"] += 1
            continue
        if gene_id not in ordered_ids:
            stats["cds_not_in_ordered_cds"] += 1
            continue
        start = int(start_s)
        end = int(end_s)
        if start > end:
            start, end = end, start
        gene = genes.setdefault(
            gene_id,
            {
                "gene_id": gene_id,
                "chrom": normalize_chrom(seqid),
                "strand": strand,
                "segments": [],
                "n_codons": int(ordered[gene_id]["n_codons"]),
            },
        )
        if gene["chrom"] != normalize_chrom(seqid) or gene["strand"] != strand:
            stats["cds_inconsistent_gene_records"] += 1
            continue
        gene["segments"].append((start, end, phase))
        stats["cds_kept"] += 1

    for gene in genes.values():
        segments = list(gene["segments"])
        if gene["strand"] == "+":
            segments.sort(key=lambda item: item[0])
        else:
            segments.sort(key=lambda item: item[0], reverse=True)
        annotated_nt = sum(end - start + 1 for start, end, _phase in segments)
        gene["segments"] = segments
        gene["annotated_nt"] = annotated_nt
        if annotated_nt != int(gene["n_codons"]) * 3:
            stats["cds_length_mismatch_ordered_cds"] += 1
    stats["genes_with_cds_in_ordered_universe"] = len(genes)
    stats["ordered_cds_gene_universe"] = len(ordered)
    return genes, dict(sorted(stats.items()))


def build_interval_index(genes: dict[str, dict[str, object]]) -> dict[tuple[str, str, int], list[tuple[int, int, str, int]]]:
    index: dict[tuple[str, str, int], list[tuple[int, int, str, int]]] = defaultdict(list)
    for gene_id, gene in genes.items():
        chrom = str(gene["chrom"])
        strand = str(gene["strand"])
        offset = 0
        for start, end, _phase in gene["segments"]:
            first_bin = start // BIN_SIZE
            last_bin = end // BIN_SIZE
            for bin_id in range(first_bin, last_bin + 1):
                index[(chrom, strand, bin_id)].append((start, end, gene_id, offset))
            offset += end - start + 1
    return index


def find_codon_hits(
    index: dict[tuple[str, str, int], list[tuple[int, int, str, int]]],
    genes: dict[str, dict[str, object]],
    chrom: str,
    strand: str,
    pos: int,
) -> list[tuple[str, int]]:
    hits = []
    for start, end, gene_id, offset in index.get((chrom, strand, pos // BIN_SIZE), []):
        if not (start <= pos <= end):
            continue
        gene = genes[gene_id]
        if strand == "+":
            nt_offset = offset + (pos - start)
        else:
            nt_offset = offset + (end - pos)
        codon_index = nt_offset // 3
        if 0 <= codon_index < int(gene["n_codons"]):
            hits.append((gene_id, codon_index))
    return hits


def empty_occupancy_arrays(genes: dict[str, dict[str, object]]) -> dict[str, list[float]]:
    return {gene_id: [0.0] * int(gene["n_codons"]) for gene_id, gene in genes.items()}


def parse_chr_best_into_occupancy(
    raw_gz: bytes,
    url: str,
    index: dict[tuple[str, str, int], list[tuple[int, int, str, int]]],
    genes: dict[str, dict[str, object]],
) -> tuple[dict[str, list[float]], dict[str, object]]:
    occupancy = empty_occupancy_arrays(genes)
    stats = defaultdict(int)
    chrom_seen = defaultdict(int)
    chrom_mapped = defaultdict(int)
    for line in gz_text_lines(raw_gz):
        if not line:
            continue
        if line.startswith("#"):
            stats["comment_lines"] += 1
            continue
        parts = line.split("\t")
        if len(parts) != 8:
            stats["malformed_chr_best_lines"] += 1
            continue
        _tag, tag_count_s, _score_s, chrom_s, start_s, end_s, align_len_s, _ambiguity_s = parts
        try:
            tag_count = int(tag_count_s)
            ref_start = int(start_s)
            ref_end = int(end_s)
            align_len = int(align_len_s)
        except ValueError:
            stats["non_numeric_chr_best_lines"] += 1
            continue
        if tag_count <= 0:
            stats["non_positive_tag_count_lines"] += 1
            continue
        chrom = normalize_chrom(chrom_s)
        chrom_seen[chrom] += tag_count
        stats["footprint_records_total"] += 1
        stats["footprint_tag_count_total"] += tag_count
        stats["aligned_nt_total"] += align_len

        if ref_start <= ref_end:
            strand = "+"
            a_site = ref_start + A_SITE_OFFSET_NT
        else:
            strand = "-"
            a_site = ref_start - A_SITE_OFFSET_NT
        if a_site < min(ref_start, ref_end) or a_site > max(ref_start, ref_end):
            stats["a_site_outside_reported_alignment_span"] += 1

        hits = find_codon_hits(index, genes, chrom, strand, a_site)
        if not hits:
            stats["footprint_records_unmapped"] += 1
            stats["footprint_tag_count_unmapped"] += tag_count
            continue
        stats["footprint_records_mapped"] += 1
        stats["footprint_tag_count_mapped"] += tag_count
        if len(hits) > 1:
            stats["footprint_records_multi_cds"] += 1
            stats["footprint_tag_count_multi_cds"] += tag_count
        chrom_mapped[chrom] += tag_count
        for gene_id, codon_index in hits:
            occupancy[gene_id][codon_index] += float(tag_count)
            stats["gene_codon_assignments"] += 1
    total = stats["footprint_tag_count_total"]
    mapped = stats["footprint_tag_count_mapped"]
    rec_total = stats["footprint_records_total"]
    rec_mapped = stats["footprint_records_mapped"]
    stats["mapping_coverage_weighted"] = mapped / float(total) if total else 0.0
    stats["mapping_coverage_records"] = rec_mapped / float(rec_total) if rec_total else 0.0
    stats["source_url"] = url
    stats["chrom_tag_count_seen_top"] = dict(sorted(chrom_seen.items(), key=lambda item: (-item[1], item[0]))[:20])
    stats["chrom_tag_count_mapped_top"] = dict(sorted(chrom_mapped.items(), key=lambda item: (-item[1], item[0]))[:20])
    return occupancy, dict(stats)


def combine_replicates(
    replicate_occupancies: dict[str, dict[str, list[float]]],
    genes: dict[str, dict[str, object]],
) -> dict[str, list[float]]:
    combined = {}
    n_reps = len(replicate_occupancies)
    for gene_id, gene in genes.items():
        n_codons = int(gene["n_codons"])
        values = [0.0] * n_codons
        for occupancy in replicate_occupancies.values():
            row = occupancy[gene_id]
            for index, value in enumerate(row):
                values[index] += value
        if n_reps:
            values = [value / float(n_reps) for value in values]
        combined[gene_id] = values
    return combined


def rounded_window(values: list[float], start: int, end: int) -> list[float]:
    return [round(value, 6) for value in values[start:end]]


def gene_payloads(combined: dict[str, list[float]], genes: dict[str, dict[str, object]]) -> dict[str, dict[str, object]]:
    payload = {}
    for gene_id in sorted(combined):
        raw = combined[gene_id]
        total = sum(raw)
        if total <= 0.0:
            continue
        n_codons = int(genes[gene_id]["n_codons"])
        mean_raw = total / float(n_codons) if n_codons else 0.0
        if mean_raw > 0.0 and math.isfinite(mean_raw):
            rel = [value / mean_raw for value in raw]
        else:
            rel = [0.0] * len(raw)
        head_end = min(HEAD_CODONS, n_codons)
        tail_start = max(0, n_codons - TAIL_CODONS)
        payload[gene_id] = {
            "n_codons": n_codons,
            "chrom": genes[gene_id]["chrom"],
            "strand": genes[gene_id]["strand"],
            "mean_raw_occupancy": round(mean_raw, 6),
            "raw_occupancy_5prime": rounded_window(raw, 0, head_end),
            "raw_occupancy_3prime": rounded_window(raw, tail_start, n_codons),
            "rel_occupancy_5prime": rounded_window(rel, 0, head_end),
            "rel_occupancy_3prime": rounded_window(rel, tail_start, n_codons),
        }
    return payload


def compact_json_dump(path: Path, data: object) -> None:
    with path.open("w", encoding="utf-8") as handle:
        json.dump(data, handle, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        handle.write("\n")


def build_payload() -> dict[str, object]:
    fetched_at = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    fetch_status: dict[str, dict[str, object]] = {}
    payloads: dict[str, bytes] = {}

    for label, url in {"readme": README_URL, "gff3": GFF_URL, **FOOTPRINT_URLS}.items():
        try:
            payloads[label] = fetch_bytes(url)
            fetch_status[url] = {
                "status": "fetched",
                "label": label,
                "payload_byte_size": len(payloads[label]),
                "sha256": sha256_hex(payloads[label]),
            }
        except Exception as exc:
            fetch_status[url] = {"status": "failed", "label": label, "reason": repr(exc)}
            if label in {"gff3", "footprint_rich_rep1"}:
                raise

    for label, url in OPTIONAL_PROBE_URLS.items():
        fetch_status[url] = {"label": label, **probe_url(url)}

    ordered = load_ordered_cds()
    genes, gff_stats = parse_gff_cds(payloads["gff3"], ordered)
    index = build_interval_index(genes)

    replicate_occupancies = {}
    replicate_stats = {}
    for label, url in FOOTPRINT_URLS.items():
        if label not in payloads:
            continue
        occupancy, stats = parse_chr_best_into_occupancy(payloads[label], url, index, genes)
        replicate_occupancies[label] = occupancy
        replicate_stats[label] = stats

    combined = combine_replicates(replicate_occupancies, genes)
    genes_payload = gene_payloads(combined, genes)

    total_tags = sum(int(stats.get("footprint_tag_count_total", 0)) for stats in replicate_stats.values())
    mapped_tags = sum(int(stats.get("footprint_tag_count_mapped", 0)) for stats in replicate_stats.values())
    total_records = sum(int(stats.get("footprint_records_total", 0)) for stats in replicate_stats.values())
    mapped_records = sum(int(stats.get("footprint_records_mapped", 0)) for stats in replicate_stats.values())
    weighted_cov = mapped_tags / float(total_tags) if total_tags else 0.0
    record_cov = mapped_records / float(total_records) if total_records else 0.0

    source_urls = [README_URL, GFF_URL] + [FOOTPRINT_URLS[key] for key in sorted(FOOTPRINT_URLS)]
    sha_by_url = {
        README_URL: sha256_hex(payloads["readme"]),
        GFF_URL: sha256_hex(payloads["gff3"]),
    }
    for label, url in FOOTPRINT_URLS.items():
        if label in payloads:
            sha_by_url[url] = sha256_hex(payloads[label])
    record_count_by_url = {
        README_URL: sum(1 for _line in gz_text_lines(payloads["readme"])),
        GFF_URL: int(gff_stats.get("gff_feature_lines", 0)),
    }
    for label, url in FOOTPRINT_URLS.items():
        if label in replicate_stats:
            record_count_by_url[url] = int(replicate_stats[label].get("footprint_records_total", 0))

    return {
        "organism": ORGANISM,
        "source_urls": source_urls,
        "sha256_by_url": sha_by_url,
        "source_record_count_by_url": record_count_by_url,
        "payload_byte_size_by_url": {
            url: int(fetch_status[url]["payload_byte_size"])
            for url in source_urls
            if fetch_status.get(url, {}).get("status") == "fetched"
        },
        "fetch_status": fetch_status,
        "fetch_date": fetched_at[:10],
        "fetched_at": fetched_at,
        "fetched_by": USER_AGENT,
        "a_site_offset_nt": A_SITE_OFFSET_NT,
        "a_site_method": "+15nt from 5' end, strand-aware, yeast standard; chr_best reverse alignments have start>end so reverse-strand A-site uses ref_start-15",
        "gff_source": "Ensembl R64-1-1 release-110",
        "chr_best_source": "GSE13750 Ingolia et al. 2009 Saccharomyces cerevisiae rich-medium footprint chr_best alignments",
        "chromosome_name_reconciliation": "chr_best reference names strip leading chr, e.g. chrII -> II; mitochondrial aliases map to Mito.",
        "gene_id_mapping": "Ensembl CDS protein_id/systematic ORF IDs are joined exactly to cds_ordered_sequences_saccharomyces_cerevisiae.json gene_id values.",
        "n_genes_mapped": len(genes_payload),
        "n_footprints_used": mapped_tags,
        "n_footprint_records_used": mapped_records,
        "n_footprint_tag_count_total": total_tags,
        "n_footprint_records_total": total_records,
        "mapping_coverage": (
            f"{weighted_cov:.6f} weighted tag-count footprint A-sites in CDS "
            f"({mapped_tags}/{total_tags}); record coverage {record_cov:.6f} ({mapped_records}/{total_records})"
        ),
        "mapping_coverage_weighted": weighted_cov,
        "mapping_coverage_records": record_cov,
        "replicates_used": sorted(replicate_occupancies),
        "combine_method": "mean",
        "head_codons_retained": HEAD_CODONS,
        "tail_codons_retained": TAIL_CODONS,
        "gff_parse_stats": gff_stats,
        "replicate_mapping_stats": replicate_stats,
        "genes": genes_payload,
        "cannot_claim": CANNOT_CLAIM,
    }


def main() -> None:
    output_path = DATA_DIR / "riboseq_positional_occupancy_saccharomyces_cerevisiae.json"
    payload = build_payload()
    compact_json_dump(output_path, payload)
    with output_path.open("r", encoding="utf-8") as handle:
        json.load(handle)
    print(
        "wrote",
        output_path,
        "genes",
        payload["n_genes_mapped"],
        "coverage",
        payload["mapping_coverage"],
    )


if __name__ == "__main__":
    main()

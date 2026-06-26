#!/usr/bin/env python3
"""Fetch ordered CDS codon sequences and derived positional codon profiles."""

from __future__ import annotations

import gzip
import hashlib
import json
import math
import re
import urllib.error
import urllib.request
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path


DATA_DIR = Path(__file__).resolve().parent
USER_AGENT = "BioReality-Codex-Ordered-CDS/1.0"
MAX_ORDERED_JSON_BYTES = 50 * 1024 * 1024
HEAD_CODONS = 200
TAIL_CODONS = 60

ORDERED_CANNOT_CLAIM = [
    "有序密码子序列 != 翻译速率/核糖体占据/折叠/功能/适应度。",
    "CDS FASTA 只给出参考注释序列；不证明任一条件下的表达量、翻译效率或因果机制。",
    "过滤后的 CDS 集合排除了长度非 3 倍数、含非 ACGT 碱基或短于 30 codon 的记录。",
]

PROFILE_CANNOT_CLAIM = [
    "位置频率 != 核糖体停顿/翻译效率；这里只是序列内禀统计。",
    "同义家族频率不区分表达条件、mRNA abundance、ribo-seq footprint、蛋白丰度或适应度。",
    "5 prime 与 3 prime 对齐 profile 是聚合统计；不能推出单基因因果边界响应。",
]

TE_CANNOT_CLAIM = [
    "ribo-seq translation-efficiency 是公开处理表的再计算；条件特异，不是普适翻译规律。",
    "TE 数值不单独证明密码子位置响应、核糖体停顿机制、蛋白折叠、功能或适应度。",
    "只保留 footprint 与 mRNA 均存在且为正值的基因；缺失基因不能解释为 TE 为零。",
]

ORGANISMS = [
    {
        "organism": "saccharomyces_cerevisiae",
        "organism_label": "Saccharomyces cerevisiae S288C",
        "ncbi_taxid": "4932",
        "release": "NCBI RefSeq GCF_000146045.2_R64",
        "source_url": "https://ftp.ncbi.nlm.nih.gov/genomes/all/GCF/000/146/045/GCF_000146045.2_R64/GCF_000146045.2_R64_cds_from_genomic.fna.gz",
    },
    {
        "organism": "escherichia_coli_k12_mg1655",
        "organism_label": "Escherichia coli str. K-12 substr. MG1655",
        "ncbi_taxid": "511145",
        "release": "NCBI RefSeq GCF_000005845.2_ASM584v2",
        "source_url": "https://ftp.ncbi.nlm.nih.gov/genomes/all/GCF/000/005/845/GCF_000005845.2_ASM584v2/GCF_000005845.2_ASM584v2_cds_from_genomic.fna.gz",
    },
]

YEAST_TE_URLS = {
    "footprint_rep1": "https://ftp.ncbi.nlm.nih.gov/geo/samples/GSM346nnn/GSM346111/suppl/GSM346111_fp_rich1_quant.txt.gz",
    "footprint_rep2": "https://ftp.ncbi.nlm.nih.gov/geo/samples/GSM346nnn/GSM346114/suppl/GSM346114_fp_rich1_quant.txt.gz",
    "mrna_rep1": "https://ftp.ncbi.nlm.nih.gov/geo/samples/GSM346nnn/GSM346117/suppl/GSM346117_mrna_rich1_quant.txt.gz",
    "mrna_rep2": "https://ftp.ncbi.nlm.nih.gov/geo/samples/GSM346nnn/GSM346118/suppl/GSM346118_mrna_rich2_quant.txt.gz",
    "readme": "https://ftp.ncbi.nlm.nih.gov/geo/samples/GSM346nnn/GSM346111/suppl/GSM346111_readMe.txt.gz",
}

# 每个 family 的 codon 顺序就是 profile 中 ratio_by_codon 的坐标顺序。
SYNONYMOUS_FAMILIES = {
    "K_AAA_vs_AAG": ["AAA", "AAG"],
    "N_AAC_vs_AAT": ["AAC", "AAT"],
    "Q_CAA_vs_CAG": ["CAA", "CAG"],
    "E_GAA_vs_GAG": ["GAA", "GAG"],
    "D_GAC_vs_GAT": ["GAC", "GAT"],
    "H_CAC_vs_CAT": ["CAC", "CAT"],
    "Y_TAC_vs_TAT": ["TAC", "TAT"],
    "C_TGC_vs_TGT": ["TGC", "TGT"],
    "F_TTC_vs_TTT": ["TTC", "TTT"],
    "I_AUA_vs_AUC_AUU": ["ATA", "ATC", "ATT"],
    "R_AGR_vs_CGN": ["AGA", "AGG", "CGA", "CGC", "CGG", "CGT"],
    "L_CUN_vs_UUR": ["CTA", "CTC", "CTG", "CTT", "TTA", "TTG"],
    "S_UCR_vs_AGY": ["TCA", "TCC", "TCG", "TCT", "AGC", "AGT"],
    "T_ACR_vs_ACY": ["ACA", "ACC", "ACG", "ACT"],
    "A_GCR": ["GCA", "GCC", "GCG", "GCT"],
    "G_GGR": ["GGA", "GGC", "GGG", "GGT"],
    "P_CCR": ["CCA", "CCC", "CCG", "CCT"],
    "V_GUR": ["GTA", "GTC", "GTG", "GTT"],
}


def fetch_bytes(url: str, timeout: int = 180) -> bytes:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return response.read()


def sha256_hex(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def combined_sha256(payloads: dict[str, bytes]) -> str:
    digest = hashlib.sha256()
    for key in sorted(payloads):
        digest.update(key.encode("utf-8"))
        digest.update(b"\0")
        digest.update(sha256_hex(payloads[key]).encode("ascii"))
        digest.update(b"\0")
    return digest.hexdigest()


def normalize_seq(seq: str) -> str:
    return re.sub(r"[^A-Za-z]", "", seq).upper()


def parse_fasta(text: str) -> list[tuple[str, str]]:
    records: list[tuple[str, str]] = []
    header: str | None = None
    chunks: list[str] = []
    for line in text.splitlines():
        if line.startswith(">"):
            if header is not None:
                records.append((header, normalize_seq("".join(chunks))))
            header = line[1:].strip()
            chunks = []
        else:
            chunks.append(line.strip())
    if header is not None:
        records.append((header, normalize_seq("".join(chunks))))
    return records


def strip_version(identifier: str) -> str:
    if re.search(r"\.[0-9]+$", identifier):
        return identifier.rsplit(".", 1)[0]
    return identifier


def first_bracket_value(header: str, key: str) -> str | None:
    match = re.search(r"\[" + re.escape(key) + r"=([^\]]*)\]", header)
    if match:
        return match.group(1)
    return None


def gene_id_from_header(header: str) -> str:
    # NCBI RefSeq headers expose stable locus_tag values; fall back through common identifiers.
    for key in ("locus_tag", "gene", "protein_id"):
        value = first_bracket_value(header, key)
        if value:
            return strip_version(value)
    first_token = header.split(None, 1)[0]
    if "_cds_" in first_token:
        tail = first_token.split("_cds_", 1)[1]
        if "_" in tail:
            return strip_version(tail.rsplit("_", 1)[0])
    return strip_version(first_token)


def codons_from_seq(seq: str) -> list[str]:
    return [seq[index : index + 3] for index in range(0, len(seq), 3)]


def ordered_record(header: str, seq: str) -> tuple[dict[str, object] | None, str | None]:
    if len(seq) % 3 != 0:
        return None, "length_not_multiple_of_3"
    if re.search(r"[^ACGT]", seq):
        return None, "non_acgt_base"
    codons = codons_from_seq(seq)
    if len(codons) < 30:
        return None, "shorter_than_30_codons"
    return (
        {
            "gene_id": gene_id_from_header(header),
            "length_nt": len(seq),
            "n_codons": len(codons),
            "codons": codons,
        },
        None,
    )


def ordered_payload_from_records(
    config: dict[str, str],
    cds: list[dict[str, object]],
    raw_gz: bytes,
    fetched_at: str,
    skipped_by_reason: dict[str, int],
    truncation: str,
) -> dict[str, object]:
    payload = {
        "schema_version": 1,
        "organism": config["organism"],
        "organism_label": config["organism_label"],
        "ncbi_taxid": config["ncbi_taxid"],
        "source_name": config["release"] + " cds_from_genomic.fna.gz",
        "source_url": config["source_url"],
        "fetch_date": fetched_at[:10],
        "fetched_at": fetched_at,
        "fetched_by": USER_AGENT,
        "sha256": sha256_hex(raw_gz),
        "sha256_of_source": sha256_hex(raw_gz),
        "source_payload_byte_size": len(raw_gz),
        "n_cds": len(cds),
        "n_records": len(cds),
        "n_skipped": sum(skipped_by_reason.values()),
        "skipped_by_reason": dict(sorted(skipped_by_reason.items())),
        "release": config["release"],
        "truncation": truncation,
        "head_codons_retained": HEAD_CODONS if truncation != "none" else None,
        "tail_codons_retained": TAIL_CODONS if truncation != "none" else None,
        "cannot_claim": ORDERED_CANNOT_CLAIM,
        "cds": cds,
    }
    if truncation == "none":
        payload.pop("head_codons_retained")
        payload.pop("tail_codons_retained")
    return payload


def compact_json_bytes(data: object) -> bytes:
    return json.dumps(data, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")


def maybe_truncate_ordered_payload(
    config: dict[str, str],
    full_cds: list[dict[str, object]],
    raw_gz: bytes,
    fetched_at: str,
    skipped_by_reason: dict[str, int],
) -> tuple[dict[str, object], bytes]:
    full_payload = ordered_payload_from_records(config, full_cds, raw_gz, fetched_at, skipped_by_reason, "none")
    encoded = compact_json_bytes(full_payload)
    if len(encoded) <= MAX_ORDERED_JSON_BYTES:
        return full_payload, encoded

    windowed = []
    for record in full_cds:
        codons = list(record["codons"])
        compact_record = dict(record)
        compact_record["codons_5prime_head"] = codons[:HEAD_CODONS]
        compact_record["codons_3prime_tail"] = codons[-TAIL_CODONS:]
        compact_record.pop("codons")
        windowed.append(compact_record)
    window_payload = ordered_payload_from_records(
        config,
        windowed,
        raw_gz,
        fetched_at,
        skipped_by_reason,
        "head200_tail60",
    )
    encoded = compact_json_bytes(window_payload)
    return window_payload, encoded


def profile_for_family(
    cds: list[dict[str, object]],
    codon_set: list[str],
    limit: int,
    from_tail: bool,
) -> list[dict[str, object]]:
    rows = []
    codon_lookup = set(codon_set)
    for pos in range(limit):
        counts = {codon: 0 for codon in codon_set}
        denominator = 0
        for record in cds:
            codons = record["codons"]
            codon_index = len(codons) - 1 - pos if from_tail else pos
            if codon_index < 0 or codon_index >= len(codons):
                continue
            codon = codons[codon_index]
            if codon in codon_lookup:
                counts[codon] += 1
                denominator += 1
        rows.append(
            {
                "position": -pos - 1 if from_tail else pos,
                "n_family_codons": denominator,
                "ratio_by_codon": {
                    codon: (counts[codon] / denominator if denominator else None)
                    for codon in codon_set
                },
            }
        )
    return rows


def build_positional_profile(
    config: dict[str, str],
    full_cds: list[dict[str, object]],
    ordered_filename: str,
    ordered_sha256: str,
    cds_source_url: str,
    cds_source_sha256: str,
    fetched_at: str,
) -> dict[str, object]:
    align_5prime = {}
    align_3prime = {}
    for family, codons in SYNONYMOUS_FAMILIES.items():
        align_5prime[family] = profile_for_family(full_cds, codons, HEAD_CODONS, False)
        align_3prime[family] = profile_for_family(full_cds, codons, TAIL_CODONS, True)
    return {
        "schema_version": 1,
        "organism": config["organism"],
        "organism_label": config["organism_label"],
        "source": "derived from " + ordered_filename,
        "source_url": cds_source_url,
        "sha256": ordered_sha256,
        "source_sha256": ordered_sha256,
        "sha256_of_ordered_cds_source": cds_source_sha256,
        "fetch_date": fetched_at[:10],
        "fetched_at": fetched_at,
        "fetched_by": USER_AGENT,
        "align_5prime_window_codons": HEAD_CODONS,
        "align_3prime_window_codons": TAIL_CODONS,
        "profile_definition": "For each aligned position and synonymous family, ratio_by_codon is count(codon at position) divided by count(any codon from that family at that position).",
        "family_definitions": SYNONYMOUS_FAMILIES,
        "align_5prime": align_5prime,
        "align_3prime": align_3prime,
        "n_cds_used": len(full_cds),
        "n_records": len(full_cds),
        "cannot_claim": PROFILE_CANNOT_CLAIM,
    }


def parse_yeast_quant(raw_gz: bytes) -> dict[str, dict[str, float]]:
    text = gzip.decompress(raw_gz).decode("utf-8", "replace")
    lines = text.splitlines()
    if not lines:
        raise ValueError("empty GEO quant table")
    expected = ["yorf", "norm", "dens", "count", "len", "total"]
    if lines[0].split("\t")[:6] != expected:
        raise ValueError("unexpected GEO yeast quant header: " + lines[0][:120])
    rows: dict[str, dict[str, float]] = {}
    for line in lines[1:]:
        if not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) < 6:
            continue
        try:
            rows[parts[0]] = {
                "norm": float(parts[1]),
                "dens": float(parts[2]),
                "count": float(parts[3]),
                "length_nt": float(parts[4]),
                "total_cds_aligned_reads": float(parts[5]),
            }
        except ValueError:
            continue
    return rows


def mean(values: list[float]) -> float | None:
    if not values:
        return None
    return sum(values) / float(len(values))


def build_yeast_te(fetched_at: str, valid_cds_gene_ids: set[str]) -> dict[str, object]:
    attempted_urls = [YEAST_TE_URLS[key] for key in sorted(YEAST_TE_URLS)]
    try:
        payloads = {key: fetch_bytes(url) for key, url in YEAST_TE_URLS.items()}
        footprint_tables = [
            parse_yeast_quant(payloads["footprint_rep1"]),
            parse_yeast_quant(payloads["footprint_rep2"]),
        ]
        mrna_tables = [
            parse_yeast_quant(payloads["mrna_rep1"]),
            parse_yeast_quant(payloads["mrna_rep2"]),
        ]
    except (urllib.error.URLError, TimeoutError, OSError, ValueError) as exc:
        return {
            "schema_version": 1,
            "organism": "saccharomyces_cerevisiae",
            "fetch_status": "blocked",
            "reason": repr(exc),
            "attempted_urls": attempted_urls,
            "fetch_date": fetched_at[:10],
            "fetched_at": fetched_at,
            "fetched_by": USER_AGENT,
            "cannot_claim": TE_CANNOT_CLAIM,
        }

    gene_names = sorted(set().union(*(table.keys() for table in footprint_tables + mrna_tables)))
    genes = []
    for gene_name in gene_names:
        if gene_name not in valid_cds_gene_ids:
            continue
        footprint = mean([table[gene_name]["norm"] for table in footprint_tables if gene_name in table])
        mrna = mean([table[gene_name]["norm"] for table in mrna_tables if gene_name in table])
        if footprint is None or mrna is None or footprint <= 0.0 or mrna <= 0.0:
            continue
        te = footprint / mrna
        if not math.isfinite(te) or te <= 0.0:
            continue
        genes.append(
            {
                "gene_id": gene_name,
                "translation_efficiency": te,
                "footprint_norm_mean": footprint,
                "mrna_norm_mean": mrna,
            }
        )

    return {
        "schema_version": 1,
        "organism": "saccharomyces_cerevisiae",
        "organism_label": "Saccharomyces cerevisiae S288C",
        "ncbi_taxid": "4932",
        "fetch_status": "fetched",
        "source_kind": "GEO processed per-feature ribosome-profiling quantification",
        "source_url": "https://www.ncbi.nlm.nih.gov/geo/query/acc.cgi?acc=GSE13750",
        "source_urls": attempted_urls,
        "study_ref": "Ingolia et al. 2009 Science, GSE13750, rich-medium footprint and mRNA quant files",
        "fetch_date": fetched_at[:10],
        "fetched_at": fetched_at,
        "fetched_by": USER_AGENT,
        "sha256": combined_sha256(payloads),
        "sha256_of_source": combined_sha256(payloads),
        "sha256_by_url": {
            key: {
                "source_url": YEAST_TE_URLS[key],
                "sha256": sha256_hex(payloads[key]),
                "payload_byte_size": len(payloads[key]),
            }
            for key in sorted(payloads)
        },
        "n_records": len(genes),
        "n_source_features": len(gene_names),
        "te_definition": "mean footprint normalized read density across two rich-medium replicates divided by mean mRNA normalized read density across two rich-medium replicates.",
        "id_filter_method": "Only GEO feature names exactly matching gene_id values in cds_ordered_sequences_saccharomyces_cerevisiae.json are retained; rRNA, tRNA, UTR, intron, and other non-CDS features are discarded unless they also appear as CDS gene_id values.",
        "genes": genes,
        "cannot_claim": TE_CANNOT_CLAIM,
    }


def write_bytes(path: Path, payload: bytes) -> str:
    path.write_bytes(payload + b"\n")
    return sha256_hex(payload + b"\n")


def write_json(path: Path, data: object) -> str:
    payload = compact_json_bytes(data)
    return write_bytes(path, payload)


def build_ordered_for_organism(config: dict[str, str], fetched_at: str) -> dict[str, object]:
    raw_gz = fetch_bytes(config["source_url"])
    text = gzip.decompress(raw_gz).decode("utf-8", "replace")
    records = parse_fasta(text)
    full_cds = []
    skipped_by_reason: dict[str, int] = defaultdict(int)
    for header, seq in records:
        record, reason = ordered_record(header, seq)
        if record is None:
            skipped_by_reason[str(reason)] += 1
            continue
        full_cds.append(record)

    ordered_payload, ordered_encoded = maybe_truncate_ordered_payload(
        config,
        full_cds,
        raw_gz,
        fetched_at,
        skipped_by_reason,
    )
    ordered_filename = f"cds_ordered_sequences_{config['organism']}.json"
    ordered_path = DATA_DIR / ordered_filename
    ordered_sha = write_bytes(ordered_path, ordered_encoded)

    profile = build_positional_profile(
        config,
        full_cds,
        ordered_filename,
        ordered_sha,
        config["source_url"],
        sha256_hex(raw_gz),
        fetched_at,
    )
    profile_filename = f"cds_positional_codon_profile_{config['organism']}.json"
    profile_path = DATA_DIR / profile_filename
    profile_sha = write_json(profile_path, profile)

    return {
        "organism": config["organism"],
        "n_cds": len(full_cds),
        "n_skipped": sum(skipped_by_reason.values()),
        "truncation": ordered_payload["truncation"],
        "ordered_file": ordered_filename,
        "ordered_size": ordered_path.stat().st_size,
        "ordered_sha256": ordered_sha,
        "profile_file": profile_filename,
        "profile_size": profile_path.stat().st_size,
        "profile_sha256": profile_sha,
        "profile_families": sorted(SYNONYMOUS_FAMILIES),
        "gene_ids": sorted(str(record["gene_id"]) for record in full_cds),
    }


def main() -> None:
    fetched_at = datetime.now(timezone.utc).replace(microsecond=0).isoformat()
    summaries = [build_ordered_for_organism(config, fetched_at) for config in ORGANISMS]
    yeast_gene_ids = set()
    for summary in summaries:
        if summary["organism"] == "saccharomyces_cerevisiae":
            yeast_gene_ids = set(str(gene_id) for gene_id in summary["gene_ids"])
    te = build_yeast_te(fetched_at, yeast_gene_ids)
    te_path = DATA_DIR / "riboseq_translation_efficiency_saccharomyces_cerevisiae.json"
    te_sha = write_json(te_path, te)
    for summary in summaries:
        print(
            summary["organism"],
            "n_cds=",
            summary["n_cds"],
            "n_skipped=",
            summary["n_skipped"],
            "truncation=",
            summary["truncation"],
            "ordered_size=",
            summary["ordered_size"],
            "profile_size=",
            summary["profile_size"],
        )
    print(
        "saccharomyces_cerevisiae_te",
        "status=",
        te.get("fetch_status"),
        "n_records=",
        te.get("n_records", 0),
        "sha256=",
        te_sha,
    )


if __name__ == "__main__":
    main()

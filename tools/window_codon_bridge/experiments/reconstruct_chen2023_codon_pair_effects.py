#!/usr/bin/env python3
"""
Reconstruct Chen/Park/Subramaniam 8xdicodon mRNA effects from raw SRA.

This script mirrors the relevant parts of rasilab/chen_2023:

* linkage experiments:
  analysis/barcodeseq/{8xdicodon_linkage,frameshifted_8xdicodon_linkage}
  scripts/run_analysis.smk and scripts/filter_barcodes.ipynb
* expression experiments:
  analysis/barcodeseq/{wt_mrna_grna,wt_frameshifted_mrna_grna}/scripts/run_analysis.smk
* aggregation/thresholds:
  wt_mrna_grna/scripts/plot_dipeptide_effects.ipynb and
  wt_hel2_no_glucose_mrna_grna/scripts/plot_translation_effects.ipynb

Requirements: Python stdlib, curl, gzip-compatible zcat/gzcat, bowtie2, bowtie2-build.
The script downloads one FASTQ at a time, streams it, and deletes it immediately.
"""

from __future__ import annotations

import csv
import gzip
import json
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from statistics import median
from typing import Iterable
from io import TextIOWrapper
from urllib.parse import quote
from urllib.request import urlopen


ROOT = Path(__file__).resolve().parents[3]
CHEN_REPO = Path(os.environ.get("CHEN2023_REPO", "/tmp/chen_2023"))
WORK = Path(os.environ.get("CHEN2023_WORK", "/tmp/chen2023_reconstruct_work"))
OUT_JSON = ROOT / "tools/window_codon_bridge/synced/chen2023_codon_pair_mrna_effects.json"
REUSE_CACHE = os.environ.get("CHEN2023_REUSE_CACHE", "1") != "0"

BARCODE_READS_CUTOFF = 10
INSERT_READS_CUTOFF = 500
N_BARCODES_CUTOFF = 4


SAMPLES = {
    "inframe_linkage": {
        "srr": "SRR24783016",
        "sample_id": "yeast_cyto_linkage",
        "annotation": CHEN_REPO / "analysis/barcodeseq/8xdicodon_linkage/annotations/sample_annotations.csv",
        "insert_annotation": CHEN_REPO / "analysis/barcodeseq/8xdicodon_linkage/annotations/dicodon_yeast.csv",
        "fastq_member": 0,
    },
    "inframe_mrna": {
        "srr": "SRR24651717",
        "sample_name": "wt_mrna",
        "annotation": CHEN_REPO / "analysis/barcodeseq/wt_mrna_grna/annotations/sample_annotations.csv",
        "fastq_member": 0,
    },
    "inframe_gdna": {
        "srr": "SRR24651716",
        "sample_name": "wt_gdna",
        "annotation": CHEN_REPO / "analysis/barcodeseq/wt_mrna_grna/annotations/sample_annotations.csv",
        "fastq_member": 0,
    },
    "frameshift_linkage": {
        "srr": "SRR25184715",
        "sample_id": "107p3",
        "annotation": CHEN_REPO / "analysis/barcodeseq/frameshifted_8xdicodon_linkage/annotations/sample_annotations.csv",
        "insert_annotation": CHEN_REPO / "analysis/barcodeseq/frameshifted_8xdicodon_linkage/annotations/insert_annotations.csv",
        "fastq_member": 0,
    },
    "frameshift_mrna": {
        "srr": "SRR25204980",
        "sample_name": "mrna_cyto",
        "annotation": CHEN_REPO / "analysis/barcodeseq/wt_frameshifted_mrna_grna/annotations/sample_annotations.csv",
        "fastq_member": 0,
    },
    "frameshift_grna": {
        "srr": "SRR25204979",
        "sample_name": "grna_cyto",
        "annotation": CHEN_REPO / "analysis/barcodeseq/wt_frameshifted_mrna_grna/annotations/sample_annotations.csv",
        "fastq_member": 0,
    },
}


GENETIC_CODE = {
    "TTT": "F", "TTC": "F", "TTA": "L", "TTG": "L",
    "TCT": "S", "TCC": "S", "TCA": "S", "TCG": "S",
    "TAT": "Y", "TAC": "Y", "TAA": "*", "TAG": "*",
    "TGT": "C", "TGC": "C", "TGA": "*", "TGG": "W",
    "CTT": "L", "CTC": "L", "CTA": "L", "CTG": "L",
    "CCT": "P", "CCC": "P", "CCA": "P", "CCG": "P",
    "CAT": "H", "CAC": "H", "CAA": "Q", "CAG": "Q",
    "CGT": "R", "CGC": "R", "CGA": "R", "CGG": "R",
    "ATT": "I", "ATC": "I", "ATA": "I", "ATG": "M",
    "ACT": "T", "ACC": "T", "ACA": "T", "ACG": "T",
    "AAT": "N", "AAC": "N", "AAA": "K", "AAG": "K",
    "AGT": "S", "AGC": "S", "AGA": "R", "AGG": "R",
    "GTT": "V", "GTC": "V", "GTA": "V", "GTG": "V",
    "GCT": "A", "GCC": "A", "GCA": "A", "GCG": "A",
    "GAT": "D", "GAC": "D", "GAA": "E", "GAG": "E",
    "GGT": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}


@dataclass(frozen=True)
class ReadSpec:
    barcode_start: int
    barcode_length: int
    insert_start: int | None = None
    insert_length: int | None = None


def run(cmd: list[str], *, cwd: Path | None = None, stdout=None, stderr=None) -> None:
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=cwd, check=True, stdout=stdout, stderr=stderr)


def require_tools() -> None:
    missing = [tool for tool in ["curl", "bowtie2", "bowtie2-build"] if shutil.which(tool) is None]
    if shutil.which("zcat") is None and shutil.which("gzcat") is None:
        missing.append("zcat-or-gzcat")
    if missing:
        raise SystemExit("needs_external: missing required tool(s): " + ", ".join(missing))
    if not CHEN_REPO.exists():
        raise SystemExit(f"needs_external: Chen repo not found at {CHEN_REPO}; clone rasilab/chen_2023 there")


def read_annotation(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as f:
        lines = [line for line in f if not line.startswith("#")]
    return list(csv.DictReader(lines))


def read_spec(annotation: Path, *, sample_id: str | None = None, sample_name: str | None = None) -> ReadSpec:
    rows = read_annotation(annotation)
    matches = []
    for row in rows:
        if sample_id is not None and row.get("sample_id") == sample_id:
            matches.append(row)
        if sample_name is not None and row.get("sample_name") == sample_name:
            matches.append(row)
    if len(matches) != 1:
        raise RuntimeError(f"expected one annotation match in {annotation}, got {len(matches)}")
    row = matches[0]
    return ReadSpec(
        barcode_start=int(row["barcode_start"]),
        barcode_length=int(row["barcode_length"]),
        insert_start=int(row["insert_start"]) if row.get("insert_start") else None,
        insert_length=int(row["insert_length"]) if row.get("insert_length") else None,
    )


def dna_to_rna(seq: str) -> str:
    return seq.replace("T", "U")


def translate_dicodon(dicodon: str) -> str:
    return GENETIC_CODE[dicodon[:3]] + GENETIC_CODE[dicodon[3:6]]


def canonical_dicodon_from_insert(insert: str, *, frameshift: bool) -> str | None:
    if frameshift:
        m = re.search(r"GAACAATTCTTCACCCTTAGACAT([ACGT]{48})CGCGTAGTCCGGGACGTCGTACGG$", insert)
        if not m:
            return None
        repeated = m.group(1)
    else:
        repeated = insert
    if len(repeated) != 48:
        return None
    unit = repeated[:6]
    if unit * 8 != repeated:
        return None
    return unit


def load_insert_annotations(path: Path, *, frameshift: bool) -> tuple[dict[str, int], dict[int, str], dict[str, int]]:
    seq_to_insert: dict[str, int] = {}
    insert_to_dicodon: dict[int, str] = {}
    dicodon_to_insert: dict[str, int] = {}
    with path.open(newline="") as f:
        for row in csv.DictReader(f):
            insert_num = int(row["insert_num"])
            insert = row["insert"].strip().upper()
            seq_to_insert[insert] = insert_num
            if insert_num <= 4095:
                dicodon = canonical_dicodon_from_insert(insert, frameshift=frameshift)
                if dicodon is not None:
                    insert_to_dicodon[insert_num] = dicodon
                    dicodon_to_insert[dicodon] = insert_num
    if len(insert_to_dicodon) != 4096:
        raise RuntimeError(f"{path}: expected 4096 dicodon inserts, got {len(insert_to_dicodon)}")
    return seq_to_insert, insert_to_dicodon, dicodon_to_insert


def ena_fastq_urls(srr: str) -> list[tuple[str, int | None]]:
    url = (
        "https://www.ebi.ac.uk/ena/portal/api/filereport?"
        f"accession={quote(srr)}&result=read_run&fields=fastq_ftp,fastq_bytes,read_count&format=tsv"
    )
    with urlopen(url, timeout=60) as fh:
        text = fh.read().decode()
    lines = [line for line in text.splitlines() if line.strip()]
    if len(lines) < 2:
        raise RuntimeError(f"ENA filereport returned no data for {srr}: {text[:200]}")
    header = lines[0].split("\t")
    vals = lines[1].split("\t")
    row = dict(zip(header, vals))
    ftp_field = row.get("fastq_ftp", "")
    bytes_field = row.get("fastq_bytes", "")
    if "ftp.sra.ebi.ac.uk" not in ftp_field:
        m = re.search(r"ftp\.sra\.ebi\.ac\.uk\S+", lines[1])
        if not m:
            raise RuntimeError(f"could not parse fastq_ftp for {srr}: {lines[1]}")
        ftp_field = m.group(0)
    ftp_parts = ftp_field.split(";")
    byte_parts = bytes_field.split(";") if bytes_field else []
    out = []
    for i, ftp in enumerate(ftp_parts):
        ftp = ftp.strip()
        if not ftp:
            continue
        nbytes = int(byte_parts[i]) if i < len(byte_parts) and byte_parts[i].isdigit() else None
        out.append(("https://" + ftp, nbytes))
    if not out:
        raise RuntimeError(f"no FASTQ URLs for {srr}")
    return out


def ena_run_read_count(srr: str) -> int | None:
    url = (
        "https://www.ebi.ac.uk/ena/portal/api/filereport?"
        f"accession={quote(srr)}&result=read_run&fields=read_count&format=tsv"
    )
    with urlopen(url, timeout=60) as fh:
        text = fh.read().decode()
    lines = [line for line in text.splitlines() if line.strip()]
    if len(lines) < 2:
        return None
    vals = lines[1].split("\t")
    for val in reversed(vals):
        if val.isdigit():
            return int(val)
    return None


def load_cached_counts(path: Path) -> tuple[Counter[str], int, dict[str, object]]:
    counts: Counter[str] = Counter()
    n_reads = 0
    with path.open(newline="") as f:
        for row in csv.DictReader(f):
            count = int(row["counts"])
            counts[row["barcode"]] = count
            n_reads += count
    return counts, n_reads, {
        "path": str(path),
        "unique_barcodes": len(counts),
        "reused_cached_csv": True,
    }


def load_cached_filtered_linkage(path: Path) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    with path.open(newline="") as f:
        for row in csv.DictReader(f):
            rows.append(
                {
                    "insert_num": int(row["insert_num"]),
                    "barcode_num": int(row["barcode_num"]),
                    "barcode": row["barcode"],
                    "linkage_count": int(row["linkage_count"]),
                }
            )
    return rows


def download_fastq(srr: str, member: int) -> Path:
    urls = ena_fastq_urls(srr)
    if member >= len(urls):
        raise RuntimeError(f"{srr}: requested FASTQ member {member}, only {len(urls)} available")
    url, expected_bytes = urls[member]
    dest = WORK / "fastq" / Path(url).name
    dest.parent.mkdir(parents=True, exist_ok=True)
    tmp = dest.with_suffix(dest.suffix + ".part")
    if dest.exists() and expected_bytes is not None and dest.stat().st_size == expected_bytes:
        return dest
    if tmp.exists():
        tmp.unlink()
    run(["curl", "-L", "--fail", "--retry", "5", "--retry-delay", "5", "-o", str(tmp), url])
    if expected_bytes is not None and tmp.stat().st_size != expected_bytes:
        raise RuntimeError(f"{srr}: downloaded {tmp.stat().st_size} bytes, expected {expected_bytes}")
    tmp.rename(dest)
    return dest


def gzip_line_iter(path: Path) -> Iterable[str]:
    with gzip.open(path, "rt", encoding="ascii", errors="strict") as f:
        for line in f:
            yield line.rstrip("\n")


def remote_fastq_sequence_iter(url: str) -> Iterable[str]:
    """Stream sequence lines from a remote gzipped FASTQ without writing it to disk."""
    proc = subprocess.Popen(
        ["curl", "-L", "--fail", "--retry", "5", "--retry-delay", "5", "-s", url],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert proc.stdout is not None
    try:
        with gzip.GzipFile(fileobj=proc.stdout, mode="rb") as gz:
            text = TextIOWrapper(gz, encoding="ascii", errors="strict")
            for i, line in enumerate(text, 1):
                if i % 4 == 2:
                    yield line.rstrip("\n")
    finally:
        if proc.stdout:
            proc.stdout.close()
        stderr = proc.stderr.read().decode(errors="replace") if proc.stderr else ""
        rc = proc.wait()
        if rc != 0:
            raise RuntimeError(f"curl stream failed for {url} with exit {rc}: {stderr[:500]}")


def count_expression_barcodes(sample_key: str) -> tuple[Counter[str], int, dict[str, object]]:
    cfg = SAMPLES[sample_key]
    spec = read_spec(cfg["annotation"], sample_name=cfg["sample_name"])
    if spec.barcode_start != 1 or spec.barcode_length != 24:
        raise RuntimeError(f"{sample_key}: unexpected barcode spec {spec}")
    counts_path = WORK / "counts" / f"{sample_key}_barcode_counts.csv"
    if REUSE_CACHE and counts_path.exists():
        return load_cached_counts(counts_path)
    fastq = download_fastq(cfg["srr"], int(cfg["fastq_member"]))
    counts: Counter[str] = Counter()
    n_reads = 0
    try:
        for i, line in enumerate(gzip_line_iter(fastq), 1):
            if i % 4 == 2:
                bc = line[spec.barcode_start - 1 : spec.barcode_start - 1 + spec.barcode_length]
                counts[bc] += 1
                n_reads += 1
    finally:
        fastq.unlink(missing_ok=True)
    counts_path.parent.mkdir(parents=True, exist_ok=True)
    with counts_path.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["barcode", "counts"])
        for bc, count in counts.most_common():
            w.writerow([bc, count])
    return counts, n_reads, {"path": str(counts_path), "unique_barcodes": len(counts)}


def load_cached_annotated_linkage(path: Path) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    with path.open(newline="") as f:
        for i, row in enumerate(csv.DictReader(f), 1):
            rows.append(
                {
                    "barcode_num": int(row.get("barcode_num") or i),
                    "insert_num": int(row["insert_num"]),
                    "barcode": row["barcode"],
                    "read_count": int(row.get("read_count") or row["count"]),
                }
            )
    return rows


def count_linkage_insert_barcodes(
    sample_key: str, seq_to_insert: dict[str, int]
) -> tuple[list[dict[str, object]], int, dict[str, object]]:
    cfg = SAMPLES[sample_key]
    spec = read_spec(cfg["annotation"], sample_id=cfg["sample_id"])
    if spec.barcode_start != 1 or spec.barcode_length != 24:
        raise RuntimeError(f"{sample_key}: unexpected barcode spec {spec}")
    if spec.insert_start is None or spec.insert_length is None:
        raise RuntimeError(f"{sample_key}: missing insert spec")
    annotated_path = WORK / "linkage" / f"{sample_key}_annotated_insert_barcode_counts.csv"
    if REUSE_CACHE and annotated_path.exists():
        rows = load_cached_annotated_linkage(annotated_path)
        n_reads = ena_run_read_count(str(cfg["srr"]))
        return rows, int(n_reads) if n_reads is not None else 0, {
            "annotated_path": str(annotated_path),
            "annotated_pairs": len(rows),
            "reads_with_N": None,
            "reused_cached_csv": True,
            "n_reads_source": "ENA read_count",
        }
    pair_counts: Counter[tuple[str, str]] = Counter()
    n_reads = 0
    n_with_n = 0
    urls = ena_fastq_urls(str(cfg["srr"]))
    used_streaming_pair = False
    if len(urls) > 1:
        # The in-frame linkage Snakemake annotation says the SRA files are
        # concatenated, with insert_start=61 for 60 nt R1 reads. ENA exposes
        # the same run as paired FASTQ, so concatenate the R1/R2 sequence lines
        # in memory and then apply the original 1-based substr coordinates.
        used_streaming_pair = True
        iter1 = remote_fastq_sequence_iter(urls[0][0])
        iter2 = remote_fastq_sequence_iter(urls[1][0])
        for line1, line2 in zip(iter1, iter2):
            line = line1 + line2
            insert = line[spec.insert_start - 1 : spec.insert_start - 1 + spec.insert_length]
            barcode = line[spec.barcode_start - 1 : spec.barcode_start - 1 + spec.barcode_length]
            n_reads += 1
            if "N" in insert or "N" in barcode:
                n_with_n += 1
                continue
            if insert in seq_to_insert:
                pair_counts[(insert, barcode)] += 1
    else:
        fastq = download_fastq(cfg["srr"], int(cfg["fastq_member"]))
        try:
            for i, line in enumerate(gzip_line_iter(fastq), 1):
                if i % 4 == 2:
                    insert = line[spec.insert_start - 1 : spec.insert_start - 1 + spec.insert_length]
                    barcode = line[spec.barcode_start - 1 : spec.barcode_start - 1 + spec.barcode_length]
                    n_reads += 1
                    if "N" in insert or "N" in barcode:
                        n_with_n += 1
                        continue
                    if insert in seq_to_insert:
                        pair_counts[(insert, barcode)] += 1
        finally:
            fastq.unlink(missing_ok=True)

    rows = []
    for barcode_num, ((insert, barcode), count) in enumerate(pair_counts.most_common(), 1):
        rows.append(
            {
                "barcode_num": barcode_num,
                "insert_num": seq_to_insert[insert],
                "barcode": barcode,
                "read_count": count,
            }
        )
    annotated_path.parent.mkdir(parents=True, exist_ok=True)
    with annotated_path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["barcode_num", "insert_num", "barcode", "count"])
        w.writeheader()
        for row in rows:
            w.writerow(
                {
                    "barcode_num": row["barcode_num"],
                    "insert_num": row["insert_num"],
                    "barcode": row["barcode"],
                    "count": row["read_count"],
                }
            )
    return rows, n_reads, {
        "annotated_path": str(annotated_path),
        "annotated_pairs": len(rows),
        "reads_with_N": n_with_n,
        "paired_fastq_sequence_lines_concatenated": used_streaming_pair,
    }


def write_barcode_fasta(rows: list[dict[str, object]], sample_key: str) -> Path:
    fasta = WORK / "linkage" / f"{sample_key}_reference_barcode1.fasta"
    with fasta.open("w") as f:
        for row in rows:
            if int(row["read_count"]) >= 1:
                f.write(f">{row['barcode_num']}\n{row['barcode']}\n")
    return fasta


def bowtie_self_align(fasta: Path, sample_key: str) -> Path:
    prefix = WORK / "linkage" / f"{sample_key}_reference_barcode1"
    sam = WORK / "linkage" / f"{sample_key}_alignment_barcode1.sam"
    for p in prefix.parent.glob(prefix.name + ".*.bt2"):
        p.unlink()
    run(["bowtie2-build", str(fasta), str(prefix)], stdout=subprocess.DEVNULL)
    with sam.open("w") as out, (WORK / "linkage" / f"{sample_key}_bowtie2.log").open("w") as err:
        run(
            [
                "bowtie2",
                "-L",
                "19",
                "-N",
                "1",
                "--all",
                "--norc",
                "--no-unal",
                "-f",
                "-x",
                str(prefix),
                "-U",
                str(fasta),
            ],
            stdout=out,
            stderr=err,
        )
    return sam


def parse_sam_pairs(sam: Path) -> Iterable[tuple[int, int]]:
    with sam.open() as f:
        for line in f:
            if line.startswith("@"):
                continue
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 3:
                continue
            qname = int(parts[0])
            rname = int(parts[2])
            yield rname, qname


def filter_linkage_rows(rows: list[dict[str, object]], sample_key: str) -> tuple[list[dict[str, object]], dict[str, int | str]]:
    filtered_path = WORK / "linkage" / f"{sample_key}_filtered_barcodes.csv"
    if REUSE_CACHE and filtered_path.exists():
        out = load_cached_filtered_linkage(filtered_path)
        return out, {
            "filtered_path": str(filtered_path),
            "filtered_barcodes": len(out),
            "reused_cached_csv": True,
        }
    # Reproduce filter_barcodes.ipynb:
    # many_to_one_barcode_combinations: any identical barcode observed with >1 insert-barcode row.
    by_barcode: defaultdict[str, list[int]] = defaultdict(list)
    row_by_num: dict[int, dict[str, object]] = {}
    for row in rows:
        n = int(row["barcode_num"])
        by_barcode[str(row["barcode"])].append(n)
        row_by_num[n] = row
    many_to_one = {n for nums in by_barcode.values() if len(nums) > 1 for n in nums}

    fasta = write_barcode_fasta(rows, sample_key)
    sam = bowtie_self_align(fasta, sample_key)

    exclude: set[int] = set()
    n_nonself_alignments = 0
    for rname, qname in parse_sam_pairs(sam):
        if rname == qname:
            continue
        n_nonself_alignments += 1
        rrow = row_by_num.get(rname)
        qrow = row_by_num.get(qname)
        if rrow is None or qrow is None:
            continue
        qinsert = int(qrow["insert_num"])
        rinsert = int(rrow["insert_num"])
        qcount = int(qrow["read_count"])
        rcount = int(rrow["read_count"])
        # filter(!(qinsert == rinsert & qcount > rcount))
        if not (qinsert == rinsert and qcount > rcount):
            exclude.add(qname)

    filtered = []
    for row in rows:
        n = int(row["barcode_num"])
        if n in exclude or n in many_to_one:
            continue
        filtered.append(dict(row))
    filtered.sort(key=lambda r: int(r["read_count"]), reverse=True)
    out = []
    for i, row in enumerate(filtered, 1):
        out.append(
            {
                "insert_num": int(row["insert_num"]),
                "barcode_num": i,
                "barcode": str(row["barcode"]),
                "linkage_count": int(row["read_count"]),
            }
        )
    with filtered_path.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["insert_num", "barcode_num", "barcode", "linkage_count"])
        w.writeheader()
        w.writerows(out)
    return out, {
        "filtered_path": str(filtered_path),
        "excluded_homologous_or_collision": len(exclude),
        "excluded_many_to_one": len(many_to_one),
        "nonself_bowtie2_alignments": n_nonself_alignments,
        "filtered_barcodes": len(out),
    }


def aggregate_effects(
    linkage_rows: list[dict[str, object]],
    mrna_counts: Counter[str],
    gdna_counts: Counter[str],
    insert_to_dicodon: dict[int, str],
    *,
    mrna_label: str,
    gdna_label: str,
) -> tuple[dict[str, dict[str, object]], dict[str, object]]:
    barcode_to_link = {str(row["barcode"]): row for row in linkage_rows}
    per_insert_sample: defaultdict[tuple[int, str], dict[str, int]] = defaultdict(lambda: {"count": 0, "n_barcodes": 0})

    for sample_label, counts in [(mrna_label, mrna_counts), (gdna_label, gdna_counts)]:
        for barcode, count in counts.items():
            row = barcode_to_link.get(barcode)
            if row is None:
                continue
            if count < BARCODE_READS_CUTOFF:
                continue
            insert_num = int(row["insert_num"])
            if insert_num > 4095:
                continue
            cell = per_insert_sample[(insert_num, sample_label)]
            cell["count"] += int(count)
            cell["n_barcodes"] += 1

    raw_lfc: dict[int, dict[str, object]] = {}
    for insert_num in range(4096):
        m = per_insert_sample.get((insert_num, mrna_label))
        g = per_insert_sample.get((insert_num, gdna_label))
        if not m or not g:
            continue
        if m["count"] < INSERT_READS_CUTOFF or g["count"] < INSERT_READS_CUTOFF:
            continue
        if m["n_barcodes"] < N_BARCODES_CUTOFF or g["n_barcodes"] < N_BARCODES_CUTOFF:
            continue
        raw_lfc[insert_num] = {
            "lfc": math.log2(m["count"]) - math.log2(g["count"]),
            "count_mrna": m["count"],
            "count_gdna": g["count"],
            "n_barcodes_mrna": m["n_barcodes"],
            "n_barcodes_gdna": g["n_barcodes"],
            "n_barcodes": min(m["n_barcodes"], g["n_barcodes"]),
        }

    if not raw_lfc:
        raise RuntimeError("no inserts passed aggregation thresholds")
    med = median([float(v["lfc"]) for v in raw_lfc.values()])
    result: dict[str, dict[str, object]] = {}
    for insert_num, vals in raw_lfc.items():
        dicodon = insert_to_dicodon[insert_num]
        key = dna_to_rna(dicodon[:3]) + "_" + dna_to_rna(dicodon[3:6])
        result[key] = {
            "y": float(vals["lfc"]) - med,
            **vals,
        }
    return result, {
        "median_norm_constant": med,
        "n_codon_pairs_recovered": len(result),
        "sum_linked_mrna_counts_passing_barcode_cutoff": sum(
            v["count"] for (insert, sample), v in per_insert_sample.items() if sample == mrna_label and insert <= 4095
        ),
        "sum_linked_gdna_counts_passing_barcode_cutoff": sum(
            v["count"] for (insert, sample), v in per_insert_sample.items() if sample == gdna_label and insert <= 4095
        ),
    }


def summarize_dipeptides(table: dict[str, dict[str, object]]) -> dict[str, dict[str, object]]:
    groups: defaultdict[str, list[tuple[str, dict[str, object]]]] = defaultdict(list)
    for key, row in table.items():
        dna_key = key.replace("U", "T").replace("_", "")
        diaa = translate_dicodon(dna_key)
        if "*" not in diaa:
            groups[diaa].append((key, row))
    out = {}
    for diaa, rows in groups.items():
        vals = [float(r["y"]) for _, r in rows]
        out[diaa] = {
            "mean_y": sum(vals) / len(vals),
            "min_y": min(vals),
            "n": len(vals),
            "bottom_codon_pair": min(rows, key=lambda kv: float(kv[1]["y"]))[0],
        }
    return out


def validation_gate(inframe: dict[str, dict[str, object]], frameshift: dict[str, dict[str, object]]) -> dict[str, object]:
    in_diaa = summarize_dipeptides(inframe)
    fs_diaa = summarize_dipeptides(frameshift)
    # The repository README reports proline-glycine/proline-aspartic acid
    # repeats and combinations of positively charged and bulky residues as
    # mRNA-destabilizing signals. The translation-effect notebooks separately
    # plot GP and LA in the original versus -1 frameshifted library.
    ranked = sorted(in_diaa.items(), key=lambda kv: kv[1]["mean_y"])
    rank = {diaa: i + 1 for i, (diaa, _) in enumerate(ranked)}
    bottom = [diaa for diaa, _ in ranked[:30]]
    reported_proline = ["PG", "PD"]
    charged_bulky = ["KR", "RK", "RR", "KK", "KW", "WK", "RW", "WR"]
    highlighted_controls = ["GP", "LA"]
    required = reported_proline + charged_bulky + highlighted_controls
    checks = {}
    for diaa in required:
        if diaa not in in_diaa:
            raise RuntimeError(f"validation failed: missing in-frame dipeptide {diaa}")
        fs_mean = fs_diaa.get(diaa, {}).get("mean_y")
        checks[diaa] = {
            "inframe_mean_y": in_diaa[diaa]["mean_y"],
            "inframe_min_y": in_diaa[diaa]["min_y"],
            "inframe_bottom_codon_pair": in_diaa[diaa]["bottom_codon_pair"],
            "frameshift_mean_y": fs_mean,
            "frameshift_min_y": fs_diaa.get(diaa, {}).get("min_y"),
            "frameshift_minus_inframe_mean_y": None if fs_mean is None else fs_mean - in_diaa[diaa]["mean_y"],
            "inframe_rank_by_mean_y": rank[diaa],
            "in_bottom_30_dipeptides": diaa in bottom,
        }

    proline_pass = [
        diaa
        for diaa in reported_proline
        if checks[diaa]["inframe_mean_y"] < -0.75
        and checks[diaa]["in_bottom_30_dipeptides"]
        and checks[diaa]["frameshift_minus_inframe_mean_y"] is not None
        and checks[diaa]["frameshift_minus_inframe_mean_y"] > 0.75
    ]
    if len(proline_pass) != len(reported_proline):
        raise RuntimeError(
            "validation failed: README-reported PG/PD dipeptides are not strongly low and frameshift-relieved "
            + json.dumps(checks, sort_keys=True)
        )

    charged_bulky_pass = [
        diaa
        for diaa in charged_bulky
        if checks[diaa]["inframe_mean_y"] < -1.0
        and checks[diaa]["frameshift_minus_inframe_mean_y"] is not None
        and checks[diaa]["frameshift_minus_inframe_mean_y"] > 0.75
    ]
    if len(charged_bulky_pass) < 6:
        raise RuntimeError(
            "validation failed: positively charged/bulky dipeptide signal is not recovered "
            + json.dumps(checks, sort_keys=True)
        )

    for diaa in highlighted_controls:
        fs = checks[diaa]["frameshift_mean_y"]
        delta = checks[diaa]["frameshift_minus_inframe_mean_y"]
        if fs is None or delta is None or delta <= 0.5:
            raise RuntimeError(
                f"validation failed: frameshift did not relieve notebook-highlighted {diaa}: "
                + json.dumps(checks[diaa], sort_keys=True)
            )

    return {
        "bottom_30_inframe_dipeptides_by_mean_y": bottom,
        "reported_proline_dipeptides": reported_proline,
        "charged_bulky_dipeptides_checked": charged_bulky,
        "notebook_highlighted_controls": highlighted_controls,
        "checks": checks,
    }


def get_peak_tmp_usage_gib() -> float | None:
    usage_file = WORK / "peak_du_bytes.txt"
    if usage_file.exists():
        try:
            return int(usage_file.read_text().strip()) / (1024**3)
        except Exception:
            return None
    return None


def update_peak_usage() -> None:
    total = 0
    for p in WORK.rglob("*"):
        if p.is_file():
            total += p.stat().st_size
    usage_file = WORK / "peak_du_bytes.txt"
    prev = int(usage_file.read_text()) if usage_file.exists() else 0
    if total > prev:
        usage_file.write_text(str(total))


def main() -> None:
    require_tools()
    WORK.mkdir(parents=True, exist_ok=True)
    provenance: dict[str, object] = {
        "chen_2023_repo": str(CHEN_REPO),
        "thresholds": {
            "barcode_reads_cutoff": BARCODE_READS_CUTOFF,
            "insert_reads_cutoff": INSERT_READS_CUTOFF,
            "n_barcodes_cutoff": N_BARCODES_CUTOFF,
        },
        "srrs": {k: v["srr"] for k, v in SAMPLES.items()},
        "start_time_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }

    inf_seq_to_insert, inf_insert_to_dicodon, _ = load_insert_annotations(
        SAMPLES["inframe_linkage"]["insert_annotation"], frameshift=False
    )
    fs_seq_to_insert, fs_insert_to_dicodon, _ = load_insert_annotations(
        SAMPLES["frameshift_linkage"]["insert_annotation"], frameshift=True
    )

    print("Counting and filtering in-frame linkage", flush=True)
    inf_link_raw, inf_link_reads, inf_link_meta = count_linkage_insert_barcodes("inframe_linkage", inf_seq_to_insert)
    update_peak_usage()
    inf_link, inf_filter_meta = filter_linkage_rows(inf_link_raw, "inframe_linkage")
    update_peak_usage()

    print("Counting and filtering frameshift linkage", flush=True)
    fs_link_raw, fs_link_reads, fs_link_meta = count_linkage_insert_barcodes("frameshift_linkage", fs_seq_to_insert)
    update_peak_usage()
    fs_link, fs_filter_meta = filter_linkage_rows(fs_link_raw, "frameshift_linkage")
    update_peak_usage()

    print("Counting expression barcodes", flush=True)
    inf_mrna_counts, inf_mrna_reads, inf_mrna_meta = count_expression_barcodes("inframe_mrna")
    update_peak_usage()
    inf_gdna_counts, inf_gdna_reads, inf_gdna_meta = count_expression_barcodes("inframe_gdna")
    update_peak_usage()
    fs_mrna_counts, fs_mrna_reads, fs_mrna_meta = count_expression_barcodes("frameshift_mrna")
    update_peak_usage()
    fs_grna_counts, fs_grna_reads, fs_grna_meta = count_expression_barcodes("frameshift_grna")
    update_peak_usage()

    print("Aggregating effects", flush=True)
    inf_effects, inf_agg_meta = aggregate_effects(
        inf_link, inf_mrna_counts, inf_gdna_counts, inf_insert_to_dicodon, mrna_label="wt_mrna", gdna_label="wt_gdna"
    )
    fs_effects, fs_agg_meta = aggregate_effects(
        fs_link, fs_mrna_counts, fs_grna_counts, fs_insert_to_dicodon, mrna_label="mrna_cyto", gdna_label="grna_cyto"
    )

    print("Running validation gate", flush=True)
    validation = validation_gate(inf_effects, fs_effects)

    all_keys = [
        dna_to_rna(a) + "_" + dna_to_rna(b)
        for a in sorted(GENETIC_CODE)
        for b in sorted(GENETIC_CODE)
    ]
    out: dict[str, object] = {}
    for key in all_keys:
        inf = inf_effects.get(key)
        fs = fs_effects.get(key)
        out[key] = {
            "y_inframe": None if inf is None else inf["y"],
            "y_frameshift": None if fs is None else fs["y"],
            "n_barcodes_inframe": 0 if inf is None else int(inf["n_barcodes"]),
            "n_barcodes_frameshift": 0 if fs is None else int(fs["n_barcodes"]),
        }

    provenance.update(
        {
            "n_reads": {
                "inframe_linkage": inf_link_reads,
                "inframe_mrna": inf_mrna_reads,
                "inframe_gdna": inf_gdna_reads,
                "frameshift_linkage": fs_link_reads,
                "frameshift_mrna": fs_mrna_reads,
                "frameshift_grna": fs_grna_reads,
            },
            "linkage": {
                "inframe": {**inf_link_meta, **inf_filter_meta},
                "frameshift": {**fs_link_meta, **fs_filter_meta},
            },
            "expression_counting": {
                "inframe_mrna": inf_mrna_meta,
                "inframe_gdna": inf_gdna_meta,
                "frameshift_mrna": fs_mrna_meta,
                "frameshift_grna": fs_grna_meta,
            },
            "aggregation": {
                "inframe": inf_agg_meta,
                "frameshift": fs_agg_meta,
            },
            "validation_gate": validation,
            "n_codon_pairs_total": 4096,
            "peak_workdir_usage_gib": get_peak_tmp_usage_gib(),
            "end_time_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        }
    )
    out["_provenance"] = provenance
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    tmp = OUT_JSON.with_suffix(".json.tmp")
    with tmp.open("w") as f:
        json.dump(out, f, indent=2, sort_keys=True)
        f.write("\n")
    tmp.rename(OUT_JSON)
    print(json.dumps(provenance, indent=2, sort_keys=True), flush=True)
    print(f"Wrote {OUT_JSON}", flush=True)


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as e:
        raise SystemExit(f"needs_external: command failed with exit {e.returncode}: {' '.join(e.cmd)}")

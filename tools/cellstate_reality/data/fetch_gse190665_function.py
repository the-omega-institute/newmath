#!/usr/bin/env python3
"""抓取小鼠体内部分重编程 function marker 输入。"""

from __future__ import annotations

import csv
import gzip
import json
import math
import re
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


OUT_DIR = Path(__file__).resolve().parent
CURATED_PATH = OUT_DIR / "gse190665_function_signature_inputs.json"
SCAN_MANIFEST_PATH = OUT_DIR / "k_f_invivo_scan_manifest.json"
CONTACT_ID = "k-f.gse190665-invivo-mouse"
GEO_ROOT = "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE190nnn"
USER_AGENT = "cellstate-reality-fetch"
MARKERS = {
    "senescence": ["Cdkn2a", "Cdkn1a", "Trp53", "Glb1", "Serpine1"],
    "sasp_inflammation": ["Il6", "Il1a", "Il1b", "Cxcl1", "Cxcl2", "Mmp3", "Mmp12", "Tnf", "Ccl2"],
}
FALLBACK_MARKER_ENSEMBL = {
    "Cdkn2a": "ENSMUSG00000044303",
    "Cdkn1a": "ENSMUSG00000023067",
    "Trp53": "ENSMUSG00000059552",
    "Glb1": "ENSMUSG00000045594",
    "Serpine1": "ENSMUSG00000037411",
    "Il6": "ENSMUSG00000025746",
    "Il1a": "ENSMUSG00000027399",
    "Il1b": "ENSMUSG00000027398",
    "Cxcl1": "ENSMUSG00000029380",
    "Cxcl2": "ENSMUSG00000058427",
    "Mmp3": "ENSMUSG00000043613",
    "Mmp12": "ENSMUSG00000049723",
    "Tnf": "ENSMUSG00000024401",
    "Ccl2": "ENSMUSG00000035385",
}
RNA_SUBSERIES = {
    "GSE190983": {
        "counts_file": "GSE190983_count.tsv.gz",
        "duration": "7-month cyclic dox induction",
        "age_at_endpoint_months": 22,
        "treatment_selector": {"prefix": None, "treated": "4F", "control": "Control"},
        "n_threshold": 3,
    },
    "GSE190984": {
        "counts_file": "GSE190984_count.tsv.gz",
        "duration": "1-month cyclic dox induction",
        "age_at_endpoint_months": 26,
        "treatment_selector": {"prefix": "Old", "treated": "dox-treated", "control": "non-dox"},
        "n_threshold": 3,
    },
    "GSE190985": {
        "counts_file": "GSE190985_counts.tsv.gz",
        "duration": "10-month cyclic dox induction",
        "age_at_endpoint_months": 22,
        "treatment_selector": {"prefix": "4F", "treated": "dox-treated", "control": "non-dox"},
        "n_threshold": 3,
    },
}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def url_text(url: str) -> str:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=30) as response:
        raw = response.read()
    return raw.decode("utf-8", errors="replace")


def download(url: str, path: Path) -> None:
    if path.exists() and path.stat().st_size > 0:
        return
    part_path = path.with_suffix(path.suffix + ".part")
    part_path.unlink(missing_ok=True)
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=300) as response, part_path.open("wb") as handle:
        while True:
            chunk = response.read(1024 * 1024)
            if not chunk:
                break
            handle.write(chunk)
    part_path.replace(path)


def dir_files(url: str) -> list[dict[str, str]]:
    html = url_text(url)
    rows: list[dict[str, str]] = []
    pattern = re.compile(r'<a href="([^"]+)">([^<]+)</a>\s+([0-9A-Za-z :.-]+)?\s+([0-9.]+[KMG]?|-)?')
    for href, name, modified, size in pattern.findall(html):
        if name == "Parent Directory":
            continue
        rows.append({"name": name, "href": href, "last_modified": modified.strip(), "size": size.strip()})
    return rows


def series_summary(accession: str) -> dict[str, Any]:
    result: dict[str, Any] = {"accession": accession, "relations": [], "supplementary_files": []}
    try:
        text = url_text(f"https://www.ncbi.nlm.nih.gov/geo/query/acc.cgi?acc={accession}&targ=self&form=text&view=brief")
    except OSError as exc:
        result["summary_error"] = str(exc)
        return result
    for raw in text.splitlines():
        line = raw.strip()
        if line.startswith("!Series_title = "):
            result["title"] = line.split(" = ", 1)[1]
        elif line.startswith("!Series_type = "):
            result["type"] = line.split(" = ", 1)[1]
        elif line.startswith("!Series_overall_design = "):
            result["overall_design"] = line.split(" = ", 1)[1]
        elif line.startswith("!Series_summary = "):
            result.setdefault("summary", []).append(line.split(" = ", 1)[1])
        elif line.startswith("!Series_relation = "):
            result["relations"].append(line.split(" = ", 1)[1])
        elif line.startswith("!Series_supplementary_file = "):
            result["supplementary_files"].append(line.split(" = ", 1)[1])
    return result


def write_scan_manifest(scanned: list[dict[str, Any]], status: str, reason: str) -> None:
    payload = {
        "contact_id": CONTACT_ID,
        "created_at": now_iso(),
        "status": status,
        "reason": reason,
        "accessions_scanned": scanned,
        "decision": {
            "gse190665_processed_rna_available": False,
            "gse190665_role": "methylation-array series with normalized beta and IDAT files; not used as RNA function-marker input",
            "gse190986_rna_subseries_available": True,
            "usable_rna_subseries": sorted(RNA_SUBSERIES),
            "scope_boundary": "Mouse in-vivo RNA-seq marker-direction proxy only; not a functional assay and not a human carrier.",
        },
    }
    SCAN_MANIFEST_PATH.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def build_scan_manifest() -> list[dict[str, Any]]:
    if SCAN_MANIFEST_PATH.exists():
        try:
            cached = json.loads(SCAN_MANIFEST_PATH.read_text(encoding="utf-8"))
            records = cached.get("accessions_scanned")
            if isinstance(records, list) and records:
                return [record for record in records if isinstance(record, dict)]
        except (OSError, json.JSONDecodeError):
            pass
    scanned: list[dict[str, Any]] = []
    for accession in ["GSE190665", "GSE190986", "GSE190983", "GSE190984", "GSE190985"]:
        base = f"{GEO_ROOT}/{accession}"
        record = {
            "accession": accession,
            "matrix_url": f"{base}/matrix/",
            "suppl_url": f"{base}/suppl/",
            "matrix_files": dir_files(f"{base}/matrix/"),
            "supplementary_files": dir_files(f"{base}/suppl/"),
            "series": series_summary(accession),
        }
        names = [item["name"] for item in record["supplementary_files"]]
        record["processed_rna_files"] = [name for name in names if re.search(r"counts?\.tsv\.gz$", name)]
        record["has_processed_rna_counts"] = bool(record["processed_rna_files"])
        scanned.append(record)
    reason = (
        "GSE190665 itself exposes methylation-array files only; GSE190986 RNA SubSeries "
        "GSE190983/GSE190984/GSE190985 expose processed mouse count matrices with OSKM/dox and control sample columns."
    )
    write_scan_manifest(scanned, "processed_rna_available_via_gse190986_subseries", reason)
    return scanned


def marker_gene_ids(tmp_dir: Path) -> tuple[dict[str, str], dict[str, list[str]]]:
    del tmp_dir
    aliases = {symbol: [] for symbol in FALLBACK_MARKER_ENSEMBL}
    return dict(FALLBACK_MARKER_ENSEMBL), aliases


def parse_sample(column: str, accession: str) -> dict[str, Any] | None:
    parts = column.split("_")
    if len(parts) < 3:
        return None
    animal_id = parts[-1]
    condition = parts[-2]
    tissue = "_".join(parts[:-2])
    if accession == "GSE190983":
        condition = parts[-2]
        tissue = "_".join(parts[:-2])
        group = "reprogrammed" if condition == "4F" else "control" if condition == "Control" else "excluded"
    elif accession == "GSE190984":
        age_group = parts[0]
        condition = parts[-2]
        tissue = "_".join(parts[1:-2])
        if age_group != "Old":
            group = "excluded"
        else:
            group = "reprogrammed" if condition == "dox-treated" else "control" if condition == "non-dox" else "excluded"
    elif accession == "GSE190985":
        genotype = parts[0]
        condition = parts[-2]
        tissue = "_".join(parts[1:-2])
        if genotype != "4F":
            group = "excluded"
        else:
            group = "reprogrammed" if condition == "dox-treated" else "control" if condition == "non-dox" else "excluded"
    else:
        return None
    tissue = tissue.replace("Skeletal_Muscle", "Skeletal_Muscle")
    return {
        "sample": column,
        "accession": accession,
        "tissue": tissue,
        "condition": condition,
        "animal_id": animal_id,
        "group": group,
    }


def log2_cpm(count: float, library_size: float) -> float:
    if library_size <= 0.0:
        return float("nan")
    return math.log2((count / library_size) * 1_000_000.0 + 1.0)


def parse_count_matrix(path: Path, accession: str, ensembl_to_symbol: dict[str, str]) -> tuple[list[dict[str, Any]], dict[str, dict[str, float]], dict[str, int]]:
    with gzip.open(path, "rt", encoding="utf-8", newline="") as handle:
        reader = csv.reader(handle, delimiter="\t")
        header = next(reader)
        samples = [parse_sample(column, accession) for column in header]
        sample_records = [sample for sample in samples if sample is not None]
        library_sizes = {sample["sample"]: 0 for sample in sample_records}
        marker_counts: dict[str, dict[str, int]] = {symbol: {} for symbol in ensembl_to_symbol.values()}
        for row in reader:
            if not row:
                continue
            gene_id = row[0].strip()
            symbol = ensembl_to_symbol.get(gene_id)
            values = row[1:]
            for sample, raw_value in zip(sample_records, values):
                value = int(float(raw_value))
                library_sizes[sample["sample"]] += value
                if symbol:
                    marker_counts.setdefault(symbol, {})[sample["sample"]] = value
    expression: dict[str, dict[str, float]] = {}
    for symbol, counts in marker_counts.items():
        expression[symbol] = {}
        for sample, count in counts.items():
            expression[symbol][sample] = log2_cpm(float(count), float(library_sizes.get(sample, 0)))
    return sample_records, expression, library_sizes


def main() -> int:
    tmp_dir = Path("/tmp") / "cellstate_reality_gse190986"
    tmp_dir.mkdir(parents=True, exist_ok=True)
    scanned = build_scan_manifest()
    symbol_to_ensembl, aliases = marker_gene_ids(tmp_dir)
    ensembl_to_symbol = {ensembl: symbol for symbol, ensembl in symbol_to_ensembl.items()}
    missing_markers = sorted({symbol for panel in MARKERS.values() for symbol in panel} - set(symbol_to_ensembl))

    all_samples: list[dict[str, Any]] = []
    expression_by_accession: dict[str, dict[str, dict[str, float]]] = {}
    library_sizes_by_accession: dict[str, dict[str, int]] = {}
    source_urls: dict[str, str] = {}
    for accession, spec in RNA_SUBSERIES.items():
        file_name = str(spec["counts_file"])
        url = f"{GEO_ROOT}/{accession}/suppl/{file_name}"
        source_urls[accession] = url
        path = tmp_dir / file_name
        download(url, path)
        samples, expression, library_sizes = parse_count_matrix(path, accession, ensembl_to_symbol)
        all_samples.extend(samples)
        expression_by_accession[accession] = expression
        library_sizes_by_accession[accession] = library_sizes

    payload = {
        "contact_id": CONTACT_ID,
        "layer": "function_realization",
        "created_at": now_iso(),
        "geo_accessions": ["GSE190665", "GSE190986", "GSE190983", "GSE190984", "GSE190985"],
        "source_urls": source_urls,
        "scan_manifest": str(SCAN_MANIFEST_PATH.relative_to(OUT_DIR.parents[2])),
        "marker_panels": MARKERS,
        "marker_gene_ids": symbol_to_ensembl,
        "marker_aliases": aliases,
        "missing_markers": missing_markers,
        "rna_subseries": RNA_SUBSERIES,
        "samples": all_samples,
        "expression_log2_cpm": expression_by_accession,
        "library_sizes": library_sizes_by_accession,
        "scope_boundary": [
            "GSE190665 is recorded as methylation-only for this scan.",
            "Function marker directions are estimated from GSE190986 mouse RNA-seq SubSeries counts.",
            "This is not a direct functional assay and cannot establish functional rejuvenation.",
            "Mouse in-vivo evidence is not merged into the human GSE142439 scope.",
        ],
        "scan_accessions": scanned,
    }
    CURATED_PATH.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "contact_id": CONTACT_ID,
                "curated_path": str(CURATED_PATH),
                "manifest_path": str(SCAN_MANIFEST_PATH),
                "sample_count": len(all_samples),
                "marker_count": len(symbol_to_ensembl),
                "missing_markers": missing_markers,
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

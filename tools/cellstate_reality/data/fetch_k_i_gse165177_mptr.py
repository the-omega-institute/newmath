#!/usr/bin/env python3
"""抓取并整理 GSE165177 的 cell_identity 层 marker 输入。"""

from __future__ import annotations

import csv
import gzip
import json
import re
import tempfile
import urllib.request
from pathlib import Path
from typing import Any


CONTACT_ID = "k-i.gse165177-mptr"
LAYER = "cell_identity"
GEO_ACCESSION = "GSE165177"
SERIES_MATRIX_URL = "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165177/matrix/GSE165177_series_matrix.txt.gz"
PROCESSED_URLS = [
    "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165177/suppl/GSE165177_Log2_RPM_Transient_reprogramming.txt.gz",
    "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165177/suppl/GSE165177_Log2_RPM_Transient_reprogramming_part2_170621.txt.gz",
]
OUT_PATH = Path(__file__).resolve().parent / "k_i_gse165177_mptr_identity_inputs.json"
IDENTITY_MARKERS = [
    "COL1A1",
    "COL1A2",
    "COL3A1",
    "THY1",
    "DCN",
    "LUM",
    "VIM",
    "PDGFRA",
    "FAP",
    "S100A4",
]
PLURIPOTENCY_MARKERS = [
    "POU5F1",
    "NANOG",
    "LIN28A",
    "LIN28B",
    "SOX2",
]
EXTRA_BOUNDARY_MARKERS = [
    "KLF4",
    "MYC",
]


def download(url: str, path: Path) -> None:
    request = urllib.request.Request(url, headers={"User-Agent": "cellstate-reality-fetch"})
    with urllib.request.urlopen(request, timeout=120) as response, path.open("wb") as handle:
        while True:
            chunk = response.read(1024 * 1024)
            if not chunk:
                break
            handle.write(chunk)


def parse_series_matrix(path: Path) -> dict[str, Any]:
    fields = {
        "!Series_title",
        "!Series_geo_accession",
        "!Series_summary",
        "!Series_overall_design",
        "!Series_supplementary_file",
        "!Sample_title",
        "!Sample_geo_accession",
        "!Sample_source_name_ch1",
        "!Sample_characteristics_ch1",
    }
    parsed: dict[str, list[str]] = {}
    with gzip.open(path, "rt", encoding="utf-8", newline="") as handle:
        for raw_line in handle:
            if raw_line.startswith("!series_matrix_table_begin"):
                break
            row = next(csv.reader([raw_line.rstrip("\n")], delimiter="\t"))
            if row and row[0] in fields:
                parsed.setdefault(row[0], row[1:])
    titles = parsed.get("!Sample_title", [])
    gsms = parsed.get("!Sample_geo_accession", [])
    sources = parsed.get("!Sample_source_name_ch1", [])
    characteristics = parsed.get("!Sample_characteristics_ch1", [])
    if len(titles) != len(gsms) or len(titles) != len(sources):
        raise ValueError("GSE165177 sample annotation rows have inconsistent widths")
    samples: dict[str, dict[str, Any]] = {}
    for index, title in enumerate(titles):
        samples[title] = {
            "title": title,
            "gsm": gsms[index],
            "source_name": sources[index],
            "characteristics": characteristics[index] if index < len(characteristics) else "",
            "donor": parse_donor(title),
            "class": parse_class(title),
            "day": parse_day(title),
            "experiment": parse_experiment(title),
        }
    return {
        "series_title": first(parsed.get("!Series_title")),
        "series_summary": first(parsed.get("!Series_summary")),
        "overall_design": first(parsed.get("!Series_overall_design")),
        "supplementary_files": parsed.get("!Series_supplementary_file", []),
        "samples": samples,
    }


def first(values: list[str] | None) -> str:
    return values[0] if values else ""


def parse_donor(sample: str) -> str | None:
    match = re.match(r"^(O[123])(?:_| )", sample)
    return match.group(1) if match else None


def parse_day(sample: str) -> int | None:
    match = re.search(r"_(\d+)days_", sample)
    if match:
        return int(match.group(1))
    match = re.match(r"^iPSC_(\d+)$", sample)
    return int(match.group(1)) if match else None


def parse_experiment(sample: str) -> str | None:
    match = re.search(r"_(exp[12])$", sample)
    return match.group(1) if match else None


def parse_class(sample: str) -> str:
    normalized = sample.replace(" ", "_")
    if normalized in {"O1_Fib", "O2_Fib", "O3_Fib"}:
        return "fibroblast_baseline"
    if normalized.startswith("iPSC_"):
        return "ipsc_boundary"
    if "_negative_control_intermediate_" in normalized:
        return "negative_control_intermediate"
    if "_failing_to_transiently_reprogram_intermediate_" in normalized:
        return "failed_intermediate"
    if "_transient_reprogramming_intermediate_" in normalized:
        return "transient_intermediate"
    if "_negative_control_" in normalized:
        return "negative_control"
    if "_failed_to_transiently_reprogram_" in normalized:
        return "failed_to_reprogram"
    if "_transiently_reprogrammed_" in normalized:
        return "transiently_reprogrammed"
    return "other"


def parse_processed_matrix(path: Path, wanted: set[str]) -> tuple[list[str], dict[str, dict[str, Any]]]:
    genes: dict[str, dict[str, Any]] = {}
    sample_names: list[str] = []
    with gzip.open(path, "rt", encoding="utf-8", newline="") as handle:
        reader = csv.reader(handle, delimiter="\t")
        header = next(reader)
        if len(header) < 13 or header[0] != "Probe" or header[5] != "Feature":
            raise ValueError(f"unexpected processed matrix header in {path.name}")
        sample_names = header[12:]
        for row in reader:
            if len(row) < 13:
                continue
            gene = row[5].strip()
            if gene not in wanted:
                continue
            values = {sample: float(raw_value) for sample, raw_value in zip(sample_names, row[12:])}
            genes[gene] = {
                "ensembl_id": row[6],
                "description": row[7],
                "values": values,
            }
    return sample_names, genes


def choose_samples(sample_names: list[str]) -> list[str]:
    selected: list[str] = []
    for donor in ("O1", "O2", "O3"):
        baseline = f"{donor} Fib"
        if baseline in sample_names:
            selected.append(baseline)
        control = f"{donor}_negative_control_10days_exp2"
        treated = f"{donor}_transiently_reprogrammed_10days_exp2"
        if control in sample_names and treated in sample_names:
            selected.extend([control, treated])
    for boundary in ("iPSC_13", "iPSC_21"):
        if boundary in sample_names:
            selected.append(boundary)
    return selected


def main() -> int:
    wanted = set(IDENTITY_MARKERS + PLURIPOTENCY_MARKERS + EXTRA_BOUNDARY_MARKERS)
    tmp_dir = Path(tempfile.gettempdir())
    series_path = tmp_dir / "GSE165177_series_matrix.txt.gz"
    download(SERIES_MATRIX_URL, series_path)
    series = parse_series_matrix(series_path)

    all_sample_names: list[str] = []
    all_genes: dict[str, dict[str, Any]] = {}
    for index, url in enumerate(PROCESSED_URLS, 1):
        processed_path = tmp_dir / f"GSE165177_processed_{index}.txt.gz"
        download(url, processed_path)
        sample_names, genes = parse_processed_matrix(processed_path, wanted)
        all_sample_names.extend(sample for sample in sample_names if sample not in all_sample_names)
        all_genes.update(genes)

    selected_samples = choose_samples(all_sample_names)
    if not selected_samples:
        raise ValueError("no paired exp2 day-10 samples were found")
    missing_markers = [marker for marker in sorted(wanted) if marker not in all_genes]
    selected_gene_values: dict[str, dict[str, Any]] = {}
    for marker in sorted(all_genes):
        values = all_genes[marker]["values"]
        selected_gene_values[marker] = {
            "ensembl_id": all_genes[marker]["ensembl_id"],
            "description": all_genes[marker]["description"],
            "log2_rpm": {sample: values[sample] for sample in selected_samples if sample in values},
        }
    selected_annotations = {
        sample: series["samples"].get(
            sample,
            {
                "title": sample,
                "gsm": "",
                "source_name": "",
                "characteristics": "",
                "donor": parse_donor(sample),
                "class": parse_class(sample),
                "day": parse_day(sample),
                "experiment": parse_experiment(sample),
            },
        )
        for sample in selected_samples
    }
    pairs = []
    for donor in ("O1", "O2", "O3"):
        control = f"{donor}_negative_control_10days_exp2"
        treated = f"{donor}_transiently_reprogrammed_10days_exp2"
        if control in selected_samples and treated in selected_samples:
            pairs.append(
                {
                    "donor": donor,
                    "day": 10,
                    "experiment": "exp2",
                    "control_sample": control,
                    "treated_sample": treated,
                }
            )

    payload = {
        "contact_id": CONTACT_ID,
        "layer": LAYER,
        "geo_accession": GEO_ACCESSION,
        "organism": "Homo sapiens",
        "source_urls": {
            "series_matrix": SERIES_MATRIX_URL,
            "processed_matrices": PROCESSED_URLS,
        },
        "series": {
            "title": series["series_title"],
            "overall_design": series["overall_design"],
        },
        "units": "Log2 RPM as supplied by GEO supplementary processed matrices",
        "identity_markers": IDENTITY_MARKERS,
        "pluripotency_markers": PLURIPOTENCY_MARKERS,
        "extra_boundary_markers": EXTRA_BOUNDARY_MARKERS,
        "missing_markers": missing_markers,
        "selected_samples": selected_samples,
        "sample_annotations": selected_annotations,
        "paired_tests": pairs,
        "genes": selected_gene_values,
        "cannot_claim": [
            "The curated marker matrix can test only sameSig_I style identity-marker proximity and pluripotency-marker exclusion.",
            "It cannot establish age-clock shift, safety, function, renewable maintenance, organismal maintenance, rejuvenation, or immortality potential.",
        ],
    }
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "contact_id": CONTACT_ID,
                "output": str(OUT_PATH),
                "selected_sample_count": len(selected_samples),
                "pair_count": len(pairs),
                "marker_count": len(selected_gene_values),
                "missing_markers": missing_markers,
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

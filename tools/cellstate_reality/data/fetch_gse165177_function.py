#!/usr/bin/env python3
"""抓取并整理 GSE165177 human senescence/SASP marker 输入。"""

from __future__ import annotations

import csv
import gzip
import json
import re
import tempfile
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


CONTACT_ID = "k-f.gse165177-mptr-human"
LAYER = "function_realization"
GEO_ACCESSION = "GSE165177"
SERIES_MATRIX_URL = "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165177/matrix/GSE165177_series_matrix.txt.gz"
PROCESSED_URLS = [
    "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165177/suppl/GSE165177_Log2_RPM_Transient_reprogramming.txt.gz",
    "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165177/suppl/GSE165177_Log2_RPM_Transient_reprogramming_part2_170621.txt.gz",
]
OUT_DIR = Path(__file__).resolve().parent
CURATED_PATH = OUT_DIR / "gse165177_function_signature_inputs.json"
SCAN_MANIFEST_PATH = OUT_DIR / "k_f_human_scan_manifest.json"
USER_AGENT = "cellstate-reality-fetch"

SENESCENCE_MARKERS = ["CDKN2A", "CDKN1A", "TP53", "GLB1", "SERPINE1"]
LMNB1_REVERSE_MARKER = "LMNB1"
SASP_MARKERS = ["IL6", "IL1A", "IL1B", "CXCL8", "CXCL1", "CXCL2", "MMP3", "MMP1", "CCL2", "TNF"]
ALL_MARKERS = SENESCENCE_MARKERS + [LMNB1_REVERSE_MARKER] + SASP_MARKERS


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def request_url(url: str) -> urllib.request.Request:
    return urllib.request.Request(url, headers={"User-Agent": USER_AGENT})


def url_bytes(url: str, timeout: int = 20) -> bytes:
    with urllib.request.urlopen(request_url(url), timeout=timeout) as response:
        return response.read()


def url_text(url: str, timeout: int = 20) -> str:
    return url_bytes(url, timeout=timeout).decode("utf-8", errors="replace")


def download(url: str, path: Path) -> None:
    if path.exists() and path.stat().st_size > 0:
        return
    part = path.with_suffix(path.suffix + ".part")
    part.unlink(missing_ok=True)
    with urllib.request.urlopen(request_url(url), timeout=240) as response, part.open("wb") as handle:
        while True:
            chunk = response.read(1024 * 1024)
            if not chunk:
                break
            handle.write(chunk)
    part.replace(path)


def dir_files(url: str) -> list[dict[str, str]]:
    try:
        html = url_text(url, timeout=12)
    except OSError as exc:
        return [{"error": str(exc)}]
    rows: list[dict[str, str]] = []
    pattern = re.compile(r'<a href="([^"]+)">([^<]+)</a>\s+([0-9A-Za-z :.-]+)?\s+([0-9.]+[KMG]?|-)?')
    for href, name, modified, size in pattern.findall(html):
        if name == "Parent Directory":
            continue
        rows.append({"name": name, "href": href, "last_modified": modified.strip(), "size": size.strip()})
    return rows


def series_summary(accession: str) -> dict[str, Any]:
    result: dict[str, Any] = {
        "accession": accession,
        "summary": [],
        "overall_design": [],
        "supplementary_files": [],
        "relations": [],
    }
    try:
        text = url_text(
            f"https://www.ncbi.nlm.nih.gov/geo/query/acc.cgi?acc={accession}&targ=self&form=text&view=brief",
            timeout=20,
        )
    except OSError as exc:
        result["summary_error"] = str(exc)
        return result
    result["private"] = "currently private" in text.lower()
    for raw in text.splitlines():
        line = raw.strip()
        if line.startswith("!Series_title = "):
            result["title"] = line.split(" = ", 1)[1]
        elif line.startswith("!Series_type = "):
            result.setdefault("type", []).append(line.split(" = ", 1)[1])
        elif line.startswith("!Series_summary = "):
            result["summary"].append(line.split(" = ", 1)[1])
        elif line.startswith("!Series_overall_design = "):
            result["overall_design"].append(line.split(" = ", 1)[1])
        elif line.startswith("!Series_supplementary_file = "):
            result["supplementary_files"].append(line.split(" = ", 1)[1])
        elif line.startswith("!Series_platform_organism = "):
            result.setdefault("platform_organism", []).append(line.split(" = ", 1)[1])
        elif line.startswith("!Series_sample_organism = "):
            result["sample_organism"] = line.split(" = ", 1)[1]
        elif line.startswith("!Series_relation = "):
            result["relations"].append(line.split(" = ", 1)[1])
    if accession == "GSE311930":
        match = re.search(r"scheduled to be released on ([A-Za-z0-9, ]+)\.", text)
        if match:
            result["private_release_note"] = match.group(1)
    return result


def parse_series_matrix(path: Path) -> dict[str, Any]:
    parsed: dict[str, list[list[str]]] = {}
    with gzip.open(path, "rt", encoding="utf-8", newline="") as handle:
        for raw_line in handle:
            if raw_line.startswith("!series_matrix_table_begin"):
                break
            if not raw_line.startswith("!"):
                continue
            row = next(csv.reader([raw_line.rstrip("\n")], delimiter="\t"))
            parsed.setdefault(row[0], []).append(row[1:])

    titles = first_row(parsed, "!Sample_title")
    gsms = first_row(parsed, "!Sample_geo_accession")
    sources = first_row(parsed, "!Sample_source_name_ch1")
    organisms = first_row(parsed, "!Sample_organism_ch1")
    characteristic_rows = parsed.get("!Sample_characteristics_ch1", [])
    samples: dict[str, dict[str, Any]] = {}
    for index, title in enumerate(titles):
        characteristics = [row[index] for row in characteristic_rows if index < len(row)]
        samples[title] = {
            "title": title,
            "gsm": gsms[index] if index < len(gsms) else "",
            "source_name": sources[index] if index < len(sources) else "",
            "organism": organisms[index] if index < len(organisms) else "",
            "characteristics": characteristics,
            "donor": parse_donor(title),
            "class": parse_class(title),
            "day": parse_day(title),
            "experiment": parse_experiment(title),
            "donor_age_years": parse_donor_age(characteristics),
        }
    return {
        "series_title": first_scalar(parsed, "!Series_title"),
        "series_summary": first_scalar(parsed, "!Series_summary"),
        "overall_design": first_scalar(parsed, "!Series_overall_design"),
        "supplementary_files": first_row(parsed, "!Series_supplementary_file"),
        "samples": samples,
    }


def first_row(parsed: dict[str, list[list[str]]], key: str) -> list[str]:
    values = parsed.get(key, [])
    return values[0] if values else []


def first_scalar(parsed: dict[str, list[list[str]]], key: str) -> str:
    row = first_row(parsed, key)
    return row[0] if row else ""


def parse_donor(sample: str) -> str | None:
    match = re.match(r"^(O[123])(?:_| )", sample)
    return match.group(1) if match else None


def parse_day(sample: str) -> int | None:
    match = re.search(r"_(\d+)days_", sample)
    return int(match.group(1)) if match else None


def parse_experiment(sample: str) -> str | None:
    match = re.search(r"_(exp[12])$", sample)
    return match.group(1) if match else None


def parse_donor_age(characteristics: list[str]) -> int | None:
    for item in characteristics:
        match = re.search(r"donor age \(years\):\s*([0-9]+)", item)
        if match:
            return int(match.group(1))
    return None


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
    sample_names: list[str] = []
    genes: dict[str, dict[str, Any]] = {}
    with gzip.open(path, "rt", encoding="utf-8", newline="") as handle:
        reader = csv.reader(handle, delimiter="\t")
        header = next(reader)
        if len(header) < 13 or header[0] != "Probe" or header[5] != "Feature":
            raise ValueError(f"unexpected processed matrix header in {path.name}")
        sample_names = header[12:]
        for row in reader:
            if len(row) < 13:
                continue
            symbol = row[5].strip().upper()
            if symbol not in wanted:
                continue
            values = {sample: float(value) for sample, value in zip(sample_names, row[12:])}
            genes[symbol] = {
                "ensembl_id": row[6],
                "description": row[7],
                "log2_rpm": values,
            }
    return sample_names, genes


def selected_pairs(sample_names: list[str]) -> list[dict[str, Any]]:
    pairs: list[dict[str, Any]] = []
    for donor in ("O1", "O2", "O3"):
        control = f"{donor}_negative_control_10days_exp2"
        treated = f"{donor}_transiently_reprogrammed_10days_exp2"
        if control in sample_names and treated in sample_names:
            pairs.append(
                {
                    "donor": donor,
                    "day": 10,
                    "experiment": "exp2",
                    "control_sample": control,
                    "treated_sample": treated,
                    "generator_kind": "genetic MPTR OSKM lentiviral reprogramming factor induction",
                }
            )
    return pairs


def build_scan_manifest() -> dict[str, Any]:
    candidates: list[dict[str, Any]] = []
    for accession, root in [
        ("GSE247199", "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE247nnn/GSE247199"),
        ("GSE311930", "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE311nnn/GSE311930"),
        ("GSE142439", "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE142nnn/GSE142439"),
        ("GSE165177", "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165177"),
    ]:
        summary = series_summary(accession)
        matrix_files = dir_files(f"{root}/matrix/")
        suppl_files = dir_files(f"{root}/suppl/")
        names = [str(item.get("name", "")) for item in suppl_files if isinstance(item, dict)]
        matrix_names = [str(item.get("name", "")) for item in matrix_files if isinstance(item, dict)]
        processed_expression = [
            name
            for name in names
            if re.search(r"(log2|rpm|count|counts|tpm|fpkm|expression).*\.txt\.gz$", name, re.IGNORECASE)
        ]
        candidates.append(
            {
                "accession": accession,
                "geo_text_url": f"https://www.ncbi.nlm.nih.gov/geo/query/acc.cgi?acc={accession}&targ=self&form=text&view=brief",
                "matrix_url": f"{root}/matrix/",
                "suppl_url": f"{root}/suppl/",
                "series": summary,
                "matrix_files": matrix_names,
                "supplementary_files": names,
                "processed_expression_candidates": processed_expression,
                "decision": candidate_decision(accession, summary, names),
            }
        )
    payload = {
        "created_at": now_iso(),
        "status": "processed_human_rna_available",
        "selected_accession": GEO_ACCESSION,
        "selected_contact_id": CONTACT_ID,
        "selection_reason": (
            "GSE165177 is public Homo sapiens MPTR fibroblast RNA-seq with GEO supplementary Log2 RPM matrices "
            "and series-matrix sample titles separating transiently reprogrammed fibroblasts from negative controls."
        ),
        "accessions_scanned": candidates,
        "scope_boundary": [
            "GSE165177 is used only as a human transcriptional senescence/SASP marker-direction contact.",
            "No direct functional assay, identity preservation, age-clock shift, safety, rejuvenation, maintenance, or immortality claim is inferred.",
            "Chemical and genetic reprogramming generators are not merged.",
        ],
    }
    SCAN_MANIFEST_PATH.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def candidate_decision(accession: str, summary: dict[str, Any], suppl_names: list[str]) -> dict[str, Any]:
    sample_organism = str(summary.get("sample_organism", ""))
    has_processed = any(re.search(r"(Log2_RPM|count|counts|TPM|FPKM|expression).*\.txt\.gz$", name, re.IGNORECASE) for name in suppl_names)
    if accession == "GSE247199":
        return {
            "usable_for_this_task": False,
            "reason": "eLife 2024 SuperSeries is public but sample organism is Mus musculus and GEO suppl exposes RAW.tar rather than a small human processed RNA matrix.",
            "sample_organism": sample_organism,
        }
    if accession == "GSE311930":
        return {
            "usable_for_this_task": False,
            "reason": "GEO accession is private at scan time; no public processed matrix can be verified.",
            "private": bool(summary.get("private")),
            "release_note": summary.get("private_release_note", ""),
        }
    if accession == "GSE142439":
        return {
            "usable_for_this_task": False,
            "reason": "Human OSKMLN contact is methylation-array/RAW scope, not processed RNA for senescence/SASP markers.",
            "sample_organism": sample_organism,
            "has_processed_expression_matrix": has_processed,
        }
    return {
        "usable_for_this_task": sample_organism == "Homo sapiens" and has_processed,
        "reason": "Public human processed Log2 RPM RNA-seq with negative-control and transiently reprogrammed fibroblast samples.",
        "sample_organism": sample_organism,
        "has_processed_expression_matrix": has_processed,
    }


def main() -> int:
    scan_manifest = build_scan_manifest()
    tmp_dir = Path(tempfile.gettempdir()) / "cellstate-reality-gse165177-function"
    tmp_dir.mkdir(parents=True, exist_ok=True)

    series_path = tmp_dir / "GSE165177_series_matrix.txt.gz"
    download(SERIES_MATRIX_URL, series_path)
    series = parse_series_matrix(series_path)

    all_sample_names: list[str] = []
    all_genes: dict[str, dict[str, Any]] = {}
    wanted = set(ALL_MARKERS)
    for index, url in enumerate(PROCESSED_URLS, 1):
        processed_path = tmp_dir / f"GSE165177_processed_{index}.txt.gz"
        download(url, processed_path)
        sample_names, genes = parse_processed_matrix(processed_path, wanted)
        for sample in sample_names:
            if sample not in all_sample_names:
                all_sample_names.append(sample)
        all_genes.update(genes)

    pairs = selected_pairs(all_sample_names)
    pair_samples = sorted({sample for pair in pairs for sample in (pair["control_sample"], pair["treated_sample"])})
    missing_markers = sorted(wanted - set(all_genes))
    genes: dict[str, dict[str, Any]] = {}
    for marker in sorted(all_genes):
        values = all_genes[marker]["log2_rpm"]
        genes[marker] = {
            "ensembl_id": all_genes[marker]["ensembl_id"],
            "description": all_genes[marker]["description"],
            "log2_rpm": {sample: values[sample] for sample in pair_samples if sample in values},
        }

    sample_annotations = {
        sample: series["samples"].get(sample, {"title": sample, "organism": "", "characteristics": []})
        for sample in pair_samples
    }
    payload = {
        "contact_id": CONTACT_ID,
        "layer": LAYER,
        "geo_accession": GEO_ACCESSION,
        "organism": "Homo sapiens",
        "generator_kind": "genetic MPTR OSKM lentiviral reprogramming factor induction",
        "source_urls": {
            "series_matrix": SERIES_MATRIX_URL,
            "processed_matrices": PROCESSED_URLS,
        },
        "scan_manifest": str(SCAN_MANIFEST_PATH.relative_to(OUT_DIR.parents[2])),
        "series": {
            "title": series["series_title"],
            "summary": series["series_summary"],
            "overall_design": series["overall_design"],
            "supplementary_files": series["supplementary_files"],
        },
        "units": "Log2 RPM as supplied by GEO supplementary processed matrices",
        "marker_panels": {
            "senescence": SENESCENCE_MARKERS,
            "lmnb1_reverse": [LMNB1_REVERSE_MARKER],
            "sasp_inflammation": SASP_MARKERS,
        },
        "missing_markers": missing_markers,
        "paired_tests": pairs,
        "selected_samples": pair_samples,
        "sample_annotations": sample_annotations,
        "genes": genes,
        "scan_accessions": scan_manifest["accessions_scanned"],
        "cannot_claim": [
            "FunctionSignatureShiftUp here means only senescence/SASP transcriptional marker direction.",
            "It is not direct functional rejuvenation; direct assays such as proliferation, collagen, migration, or mitochondrial function are not supplied by this contact.",
            "It does not establish cell identity, age-clock shift, safety, rejuvenation, renewable maintenance, organismal maintenance, or immortality.",
            "The genetic MPTR OSKM generator is not merged with chemical reprogramming generators.",
        ],
    }
    CURATED_PATH.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "contact_id": CONTACT_ID,
                "curated_path": str(CURATED_PATH),
                "manifest_path": str(SCAN_MANIFEST_PATH),
                "pair_count": len(pairs),
                "selected_sample_count": len(pair_samples),
                "marker_count": len(genes),
                "missing_markers": missing_markers,
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

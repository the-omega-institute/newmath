#!/usr/bin/env python3
"""抓取并整理 GSE165180/GSE165179 MPTR Horvath353 甲基化输入。"""

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


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "cellstate_reality" / "data"
CONTACT_ID = "k-a.gse165180.horvath353"
LAYER = "age_signature"
SUPER_SERIES = "GSE165180"
METHYLATION_SERIES = "GSE165179"
PLATFORM = "GPL21145 Illumina Infinium MethylationEPIC"
GSE165180_MATRIX_DIR = "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165180/matrix/"
GSE165180_SUPPL_DIR = "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165180/suppl/"
GSE165180_GPL21145_MATRIX_URL = (
    "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165180/matrix/"
    "GSE165180-GPL21145_series_matrix.txt.gz"
)
GSE165179_SERIES_URL = "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165179/matrix/GSE165179_series_matrix.txt.gz"
GSE165179_MATRIX_URL = (
    "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165179/suppl/"
    "GSE165179_Matrix_processed_transient.txt.gz"
)
COEFF_URL = (
    "https://static-content.springer.com/esm/art%3A10.1186%2Fgb-2013-14-10-r115/"
    "MediaObjects/13059_2013_3156_MOESM23_ESM.csv"
)
LOCAL_GSE165179_CACHE = DATA_DIR / "gse165179_transient_clock_inputs.json"
OUT_PATH = DATA_DIR / "gse165180_horvath353_crossmethod_inputs.json"
MANIFEST_PATH = DATA_DIR / "gse165180_methylation_scan_manifest.json"
SELECTED_DONORS = ["O1", "O2", "O3"]
SELECTED_DAY = 10
SELECTED_EXPERIMENT = "exp2"


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def download(url: str, path: Path) -> None:
    request = urllib.request.Request(url, headers={"User-Agent": "cellstate-reality-fetch"})
    with urllib.request.urlopen(request, timeout=240) as response, path.open("wb") as handle:
        while True:
            chunk = response.read(1024 * 1024)
            if not chunk:
                break
            handle.write(chunk)


def read_url_text(url: str) -> str:
    request = urllib.request.Request(url, headers={"User-Agent": "cellstate-reality-fetch"})
    with urllib.request.urlopen(request, timeout=120) as response:
        return response.read().decode("utf-8", errors="replace")


def parse_html_links(html: str) -> list[str]:
    return sorted(set(re.findall(r'href="([^"]+)"', html)))


def first(values: list[str] | None) -> str:
    return values[0] if values else ""


def parse_characteristic_value(value: str) -> tuple[str, str] | None:
    if ":" not in value:
        return None
    key, raw = value.split(":", 1)
    return key.strip().lower(), raw.strip()


def normalized_title(title: str) -> str:
    return title.replace(" ", "_")


def parse_donor(title: str) -> str | None:
    match = re.match(r"^(O[123])(?:_| )", title)
    return match.group(1) if match else None


def parse_day(title: str) -> int | None:
    normalized = normalized_title(title)
    if normalized in {"O1_Fib", "O2_Fib", "O3_Fib"}:
        return 0
    match = re.search(r"_(\d+)days_", normalized)
    return int(match.group(1)) if match else None


def parse_experiment(title: str) -> str | None:
    match = re.search(r"_(exp[12])$", normalized_title(title))
    return match.group(1) if match else None


def parse_condition(title: str) -> str:
    normalized = normalized_title(title)
    if normalized in {"O1_Fib", "O2_Fib", "O3_Fib"}:
        return "baseline"
    if "_transiently_reprogrammed_" in normalized:
        return "transiently_reprogrammed"
    if "_negative_control_" in normalized:
        return "negative_control"
    if "_failed_to_transiently_reprogram_" in normalized:
        return "failed_to_reprogram"
    if "_transient_reprogramming_intermediate_" in normalized:
        return "transient_intermediate"
    if "_failing_to_transiently_reprogram_intermediate_" in normalized:
        return "failed_intermediate"
    if "_negative_control_intermediate_" in normalized:
        return "negative_control_intermediate"
    return "other"


def parse_series_matrix(path: Path) -> dict[str, Any]:
    fields = {
        "!Series_title",
        "!Series_geo_accession",
        "!Series_summary",
        "!Series_overall_design",
        "!Series_relation",
        "!Sample_title",
        "!Sample_geo_accession",
        "!Sample_source_name_ch1",
        "!Sample_characteristics_ch1",
    }
    parsed: dict[str, list[list[str]]] = {}
    with gzip.open(path, "rt", encoding="utf-8", newline="") as handle:
        for raw_line in handle:
            if raw_line.startswith("!series_matrix_table_begin"):
                break
            row = next(csv.reader([raw_line.rstrip("\n")], delimiter="\t"))
            if row and row[0] in fields:
                parsed.setdefault(row[0], []).append(row[1:])

    titles = parsed.get("!Sample_title", [[]])[0]
    gsms = parsed.get("!Sample_geo_accession", [[]])[0]
    sources = parsed.get("!Sample_source_name_ch1", [[]])[0]
    characteristics = parsed.get("!Sample_characteristics_ch1", [])
    if len(titles) != len(gsms) or len(titles) != len(sources):
        raise ValueError(f"{path.name}: sample annotation rows have inconsistent widths")

    samples: dict[str, dict[str, Any]] = {}
    for index, title in enumerate(titles):
        parsed_characteristics: dict[str, str] = {}
        raw_characteristics: list[str] = []
        for row in characteristics:
            if index >= len(row):
                continue
            raw_characteristics.append(row[index])
            parsed_value = parse_characteristic_value(row[index])
            if parsed_value is not None:
                key, value = parsed_value
                parsed_characteristics[key] = value
        donor_age = parsed_characteristics.get("donor age (years)")
        samples[title] = {
            "title": title,
            "normalized_title": normalized_title(title),
            "gsm": gsms[index],
            "source_name": sources[index],
            "characteristics": parsed_characteristics,
            "raw_characteristics": raw_characteristics,
            "donor": parse_donor(title),
            "condition": parse_condition(title),
            "day": parse_day(title),
            "experiment": parse_experiment(title),
            "donor_age_years": int(donor_age) if donor_age and donor_age.isdigit() else None,
        }
    series_rows = {key: rows[0] for key, rows in parsed.items() if rows and key.startswith("!Series")}
    return {
        "title": first(series_rows.get("!Series_title")),
        "summary": first(series_rows.get("!Series_summary")),
        "overall_design": first(series_rows.get("!Series_overall_design")),
        "relations": series_rows.get("!Series_relation", []),
        "samples": samples,
    }


def parse_coefficients(path: Path) -> tuple[float, dict[str, float]]:
    with path.open("r", encoding="utf-8-sig", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None or "CpGmarker" not in reader.fieldnames or "CoefficientTraining" not in reader.fieldnames:
            raise ValueError("Horvath coefficient table is missing required columns")
        intercept: float | None = None
        coefficients: dict[str, float] = {}
        for row in reader:
            marker = str(row.get("CpGmarker", "")).strip()
            raw_weight = str(row.get("CoefficientTraining", "")).strip()
            if not marker or not raw_weight:
                continue
            weight = float(raw_weight)
            if marker == "(Intercept)":
                intercept = weight
            else:
                coefficients[marker] = weight
    if intercept is None:
        raise ValueError("Horvath coefficient table did not contain an intercept row")
    if len(coefficients) != 353:
        raise ValueError(f"expected 353 Horvath clock CpGs, found {len(coefficients)}")
    return intercept, coefficients


def sample_columns(header: list[str]) -> list[tuple[str, int]]:
    columns: list[tuple[str, int]] = []
    if not header or header[0] != "ID_REF":
        raise ValueError("processed matrix header must start with ID_REF")
    index = 1
    while index < len(header):
        sample = header[index].strip()
        if not sample:
            raise ValueError(f"empty sample name at column {index}")
        if index + 1 >= len(header) or header[index + 1].strip() != "Detection Pval":
            raise ValueError(f"missing Detection Pval column after {sample}")
        columns.append((sample, index))
        index += 2
    return columns


def parse_processed_matrix(path: Path, wanted_markers: set[str]) -> tuple[list[str], dict[str, dict[str, float]]]:
    beta: dict[str, dict[str, float]] = {}
    with gzip.open(path, "rt", encoding="utf-8", newline="") as handle:
        reader = csv.reader(handle)
        header = next(reader)
        columns = sample_columns(header)
        samples = [sample for sample, _ in columns]
        for row in reader:
            if not row:
                continue
            marker = row[0].strip()
            if marker not in wanted_markers:
                continue
            values: dict[str, float] = {}
            for sample, column_index in columns:
                if column_index >= len(row):
                    raise ValueError(f"row width mismatch for {marker}")
                raw_value = row[column_index].strip()
                if raw_value in {"", "NA", "NaN"}:
                    continue
                value = float(raw_value)
                if value < 0.0 or value > 1.0:
                    raise ValueError(f"beta value outside [0, 1] for {marker} {sample}: {value}")
                values[sample] = value
            beta[marker] = values
    return samples, beta


def selected_pairs(samples: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    by_key = {
        (
            sample.get("donor"),
            sample.get("condition"),
            sample.get("day"),
            sample.get("experiment"),
        ): title
        for title, sample in samples.items()
    }
    pairs: list[dict[str, Any]] = []
    for donor in SELECTED_DONORS:
        baseline = by_key.get((donor, "baseline", 0, None))
        treated = by_key.get((donor, "transiently_reprogrammed", SELECTED_DAY, SELECTED_EXPERIMENT))
        if baseline is None or treated is None:
            continue
        pairs.append(
            {
                "donor": donor,
                "baseline_sample": baseline,
                "treated_sample": treated,
                "treated_condition": "transiently_reprogrammed",
                "day": SELECTED_DAY,
                "experiment": SELECTED_EXPERIMENT,
            }
        )
    return pairs


def load_from_local_cache(coefficients: dict[str, float]) -> tuple[list[str], dict[str, dict[str, float]], str]:
    if not LOCAL_GSE165179_CACHE.exists():
        return [], {}, "absent"
    payload = json.loads(LOCAL_GSE165179_CACHE.read_text(encoding="utf-8"))
    beta = payload.get("beta")
    samples = payload.get("samples")
    if not isinstance(beta, dict) or not isinstance(samples, list):
        return [], {}, "invalid"
    sample_names = [str(sample.get("title")) for sample in samples if isinstance(sample, dict) and sample.get("title")]
    selected_beta: dict[str, dict[str, float]] = {}
    for marker in coefficients:
        values = beta.get(marker)
        if not isinstance(values, dict):
            continue
        selected_beta[marker] = {str(sample): float(value) for sample, value in values.items()}
    return sample_names, selected_beta, "used"


def write_manifest(
    *,
    matrix_links: list[str],
    suppl_links: list[str],
    series: dict[str, Any],
    selected_samples: list[dict[str, Any]],
    pairs: list[dict[str, Any]],
    covered: int,
    cache_status: str,
) -> dict[str, Any]:
    manifest = {
        "status": "available" if covered > 0 and len(pairs) == len(SELECTED_DONORS) else "needs_data",
        "scanned_at": now_iso(),
        "super_series": SUPER_SERIES,
        "methylation_subseries": METHYLATION_SERIES,
        "platform": PLATFORM,
        "checked_urls": [
            GSE165180_MATRIX_DIR,
            GSE165180_SUPPL_DIR,
            GSE165180_GPL21145_MATRIX_URL,
            GSE165179_SERIES_URL,
            GSE165179_MATRIX_URL,
            COEFF_URL,
        ],
        "gse165180_matrix_links": matrix_links,
        "gse165180_suppl_links": suppl_links,
        "super_series_relation": ["SuperSeries of: GSE165179"],
        "availability": {
            "gse165180_top_level_processed_table_rows": 0,
            "gse165180_top_level_raw_tar": "GSE165180_RAW.tar",
            "gse165179_processed_beta_matrix": GSE165179_MATRIX_URL,
            "processed_beta_matrix_readable": covered > 0,
            "local_gse165179_horvath_cache": cache_status,
        },
        "sample_time_structure": {
            "selected_contrast": "same-donor baseline fibroblast versus day-10 exp2 transiently reprogrammed MPTR fibroblast",
            "selected_samples": selected_samples,
            "pairs": pairs,
            "pairing": "same donor baseline-versus-treated",
        },
        "horvath353_join": {
            "clock_cpg_total": 353,
            "clock_cpg_covered": covered,
            "coverage_ratio": covered / 353.0,
        },
        "cannot_claim": [
            "This scan only establishes availability of human methylation age_signature data.",
            "It does not test identity, function, safety, rejuvenation, maintenance, or immortality.",
            "GSE165180/GSE165179 and GSE142439 remain separate cohorts and are not merged into one carrier.",
        ],
        "series": {
            "title": series.get("title"),
            "summary": series.get("summary"),
            "overall_design": series.get("overall_design"),
        },
    }
    MANIFEST_PATH.write_text(json.dumps(manifest, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return manifest


def main() -> int:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    tmp_dir = Path(tempfile.gettempdir())
    gse165179_series_path = tmp_dir / "GSE165179_series_matrix.txt.gz"
    coeff_path = tmp_dir / "horvath353_coefficients.csv"

    matrix_links = parse_html_links(read_url_text(GSE165180_MATRIX_DIR))
    suppl_links = parse_html_links(read_url_text(GSE165180_SUPPL_DIR))
    download(GSE165179_SERIES_URL, gse165179_series_path)
    download(COEFF_URL, coeff_path)

    intercept, coefficients = parse_coefficients(coeff_path)
    series = parse_series_matrix(gse165179_series_path)
    sample_names, beta, cache_status = load_from_local_cache(coefficients)
    if cache_status != "used":
        matrix_path = tmp_dir / "GSE165179_Matrix_processed_transient.txt.gz"
        download(GSE165179_MATRIX_URL, matrix_path)
        sample_names, beta = parse_processed_matrix(matrix_path, set(coefficients))

    if set(sample_names) != set(series["samples"]):
        missing_in_series = sorted(set(sample_names) - set(series["samples"]))
        missing_in_matrix = sorted(set(series["samples"]) - set(sample_names))
        raise ValueError(
            "GSE165179 matrix samples and series annotations differ: "
            f"missing_in_series={missing_in_series}; missing_in_matrix={missing_in_matrix}"
        )

    pairs = selected_pairs(series["samples"])
    selected_titles = sorted({title for pair in pairs for title in (pair["baseline_sample"], pair["treated_sample"])})
    selected_samples = [series["samples"][title] for title in selected_titles]
    selected_beta = {
        marker: {sample: values[sample] for sample in selected_titles if sample in values}
        for marker, values in beta.items()
        if marker in coefficients
    }
    covered = len(selected_beta)
    payload = {
        "contact_id": CONTACT_ID,
        "layer": LAYER,
        "super_series": SUPER_SERIES,
        "geo_accession": METHYLATION_SERIES,
        "platform": PLATFORM,
        "source_urls": {
            "gse165180_gpl21145_series_matrix": GSE165180_GPL21145_MATRIX_URL,
            "gse165179_series_matrix": GSE165179_SERIES_URL,
            "gse165179_processed_beta_matrix": GSE165179_MATRIX_URL,
            "clock_coefficients": COEFF_URL,
        },
        "series": {
            "title": series["title"],
            "summary": series["summary"],
            "overall_design": series["overall_design"],
        },
        "intercept": intercept,
        "clock_coefficients": coefficients,
        "clock_cpg_total": len(coefficients),
        "clock_cpg_covered": covered,
        "clock_cpg_coverage_ratio": covered / float(len(coefficients)),
        "beta": {marker: selected_beta[marker] for marker in coefficients if marker in selected_beta},
        "samples": selected_samples,
        "pairs": pairs,
        "cannot_claim": [
            "The curated matrix is age_signature-only.",
            "MPTR transient-phase pluripotency safety is not evaluated by this methylation clock contact.",
            "This contact does not merge GSE165180/GSE165179 with GSE142439.",
        ],
    }
    OUT_PATH.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    manifest = write_manifest(
        matrix_links=matrix_links,
        suppl_links=suppl_links,
        series=series,
        selected_samples=selected_samples,
        pairs=pairs,
        covered=covered,
        cache_status=cache_status,
    )
    print(
        json.dumps(
            {
                "contact_id": CONTACT_ID,
                "curated_output": str(OUT_PATH.relative_to(REPO_ROOT)),
                "manifest": str(MANIFEST_PATH.relative_to(REPO_ROOT)),
                "manifest_status": manifest["status"],
                "clock_cpg_total": len(coefficients),
                "clock_cpg_covered": covered,
                "sample_count": len(selected_samples),
                "pair_count": len(pairs),
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

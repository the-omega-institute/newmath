#!/usr/bin/env python3
"""抓取 GSE165179 MPTR 甲基化矩阵并整理 Horvath353 年龄输入。"""

from __future__ import annotations

import csv
import gzip
import json
import math
import re
import tempfile
import urllib.request
from pathlib import Path
from typing import Any


CONTACT_ID = "k-a.gse165179-transient"
LAYER = "age_signature"
GEO_ACCESSION = "GSE165179"
PLATFORM = "GPL21145 Illumina Infinium MethylationEPIC"
MATRIX_URL = "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165179/suppl/GSE165179_Matrix_processed_transient.txt.gz"
SERIES_MATRIX_URL = "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165179/matrix/GSE165179_series_matrix.txt.gz"
COEFF_URL = "https://static-content.springer.com/esm/art%3A10.1186%2Fgb-2013-14-10-r115/MediaObjects/13059_2013_3156_MOESM23_ESM.csv"
OUT_PATH = Path(__file__).resolve().parent / "gse165179_transient_clock_inputs.json"
ADULT_AGE = 20.0


def download(url: str, path: Path) -> None:
    request = urllib.request.Request(url, headers={"User-Agent": "cellstate-reality-fetch"})
    with urllib.request.urlopen(request, timeout=180) as response, path.open("wb") as handle:
        while True:
            chunk = response.read(1024 * 1024)
            if not chunk:
                break
            handle.write(chunk)


def first(values: list[str] | None) -> str:
    return values[0] if values else ""


def parse_donor(sample: str) -> str | None:
    match = re.match(r"^(O[123])(?:_| )", sample)
    return match.group(1) if match else None


def parse_day(sample: str) -> int | None:
    if re.match(r"^O[123] Fib$", sample):
        return 0
    match = re.search(r"_(\d+)days_", sample)
    return int(match.group(1)) if match else None


def parse_experiment(sample: str) -> str | None:
    match = re.search(r"_(exp[12])$", sample)
    return match.group(1) if match else None


def parse_condition(sample: str) -> str:
    normalized = sample.replace(" ", "_")
    if normalized in {"O1_Fib", "O2_Fib", "O3_Fib"}:
        return "baseline"
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


def parse_characteristic_value(value: str) -> tuple[str, str] | None:
    if ":" not in value:
        return None
    key, raw = value.split(":", 1)
    return key.strip().lower(), raw.strip()


def parse_series_matrix(path: Path) -> dict[str, Any]:
    fields = {
        "!Series_title",
        "!Series_geo_accession",
        "!Series_summary",
        "!Series_overall_design",
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
        raise ValueError("GSE165179 sample annotation rows have inconsistent widths")

    samples: dict[str, dict[str, Any]] = {}
    for index, title in enumerate(titles):
        parsed_characteristics: dict[str, str] = {}
        for row in characteristics:
            if index >= len(row):
                continue
            parsed_value = parse_characteristic_value(row[index])
            if parsed_value is not None:
                key, value = parsed_value
                parsed_characteristics[key] = value
        donor_age = parsed_characteristics.get("donor age (years)")
        samples[title] = {
            "title": title,
            "gsm": gsms[index],
            "source_name": sources[index],
            "characteristics": parsed_characteristics,
            "donor": parse_donor(title),
            "condition": parse_condition(title),
            "day": parse_day(title),
            "experiment": parse_experiment(title),
            "donor_age_years": int(donor_age) if donor_age and donor_age.isdigit() else None,
        }
    series_rows = {key: rows[0] for key, rows in parsed.items() if rows and key.startswith("!Series")}
    return {
        "series_title": first(series_rows.get("!Series_title")),
        "series_summary": first(series_rows.get("!Series_summary")),
        "overall_design": first(series_rows.get("!Series_overall_design")),
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
        columns.append((sample, index))
        if index + 1 < len(header) and header[index + 1].strip() == "Detection Pval":
            index += 2
        else:
            raise ValueError(f"missing Detection Pval column after {sample}")
    return columns


def parse_processed_matrix(path: Path, wanted_markers: set[str]) -> tuple[list[str], dict[str, dict[str, float]]]:
    beta: dict[str, dict[str, float]] = {}
    samples: list[str] = []
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


def dnam_age(clock_sum: float) -> float:
    if clock_sum < 0.0:
        return (1.0 + ADULT_AGE) * math.exp(clock_sum) - 1.0
    return (1.0 + ADULT_AGE) * clock_sum + ADULT_AGE


def score_samples(
    sample_names: list[str],
    intercept: float,
    coefficients: dict[str, float],
    beta: dict[str, dict[str, float]],
) -> dict[str, dict[str, Any]]:
    scores: dict[str, dict[str, Any]] = {}
    for sample in sample_names:
        linear = intercept
        used = 0
        for marker, weight in coefficients.items():
            marker_values = beta.get(marker)
            if not isinstance(marker_values, dict) or sample not in marker_values:
                continue
            linear += weight * float(marker_values[sample])
            used += 1
        scores[sample] = {
            "clock_cpg_used": used,
            "clock_linear_score": linear,
            "dnam_age": dnam_age(linear),
        }
    return scores


def selected_pairs(samples: dict[str, dict[str, Any]], scores: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    pairs: list[dict[str, Any]] = []
    by_key = {
        (
            sample.get("donor"),
            sample.get("condition"),
            sample.get("day"),
            sample.get("experiment"),
        ): title
        for title, sample in samples.items()
    }
    for donor in ("O1", "O2", "O3"):
        baseline = by_key.get((donor, "baseline", 0, None))
        treated = by_key.get((donor, "transiently_reprogrammed", 10, "exp2"))
        if baseline is None or treated is None:
            continue
        pairs.append(
            {
                "donor": donor,
                "baseline_sample": baseline,
                "treated_sample": treated,
                "day": 10,
                "experiment": "exp2",
                "baseline_age": scores[baseline]["dnam_age"],
                "treated_age": scores[treated]["dnam_age"],
                "delta_treated_minus_baseline": scores[treated]["dnam_age"] - scores[baseline]["dnam_age"],
            }
        )
    return pairs


def main() -> int:
    tmp_dir = Path(tempfile.gettempdir())
    matrix_path = tmp_dir / "GSE165179_Matrix_processed_transient.txt.gz"
    series_path = tmp_dir / "GSE165179_series_matrix.txt.gz"
    coeff_path = tmp_dir / "horvath353_coefficients.csv"
    download(MATRIX_URL, matrix_path)
    download(SERIES_MATRIX_URL, series_path)
    download(COEFF_URL, coeff_path)

    intercept, coefficients = parse_coefficients(coeff_path)
    series = parse_series_matrix(series_path)
    sample_names, beta = parse_processed_matrix(matrix_path, set(coefficients))
    if set(sample_names) != set(series["samples"]):
        missing_in_series = sorted(set(sample_names) - set(series["samples"]))
        missing_in_matrix = sorted(set(series["samples"]) - set(sample_names))
        raise ValueError(
            "GSE165179 matrix samples and series annotations differ: "
            f"missing_in_series={missing_in_series}; missing_in_matrix={missing_in_matrix}"
        )

    scores = score_samples(sample_names, intercept, coefficients, beta)
    samples: list[dict[str, Any]] = []
    for sample in sample_names:
        annotation = dict(series["samples"][sample])
        annotation.update(scores[sample])
        samples.append(annotation)
    covered = len(beta)
    pairs = selected_pairs(series["samples"], scores)
    ordered_beta = {marker: beta[marker] for marker in coefficients if marker in beta}
    payload = {
        "contact_id": CONTACT_ID,
        "layer": LAYER,
        "geo_accession": GEO_ACCESSION,
        "platform": PLATFORM,
        "source_urls": {
            "processed_beta_matrix": MATRIX_URL,
            "series_matrix": SERIES_MATRIX_URL,
            "clock_coefficients": COEFF_URL,
        },
        "series": {
            "title": series["series_title"],
            "overall_design": series["overall_design"],
        },
        "intercept": intercept,
        "clock_coefficients": coefficients,
        "clock_cpg_total": len(coefficients),
        "clock_cpg_covered": covered,
        "clock_cpg_coverage_ratio": covered / float(len(coefficients)),
        "beta": ordered_beta,
        "samples": samples,
        "age_shift_pairs": pairs,
        "cannot_claim": [
            "The methylation matrix tests Horvath353 age_signature only.",
            "It does not test cell identity, safety, function, renewable maintenance, organismal maintenance, rejuvenation, or immortality.",
            "A same-scope join must use explicit donor and condition matches to a separate identity contact.",
        ],
    }
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "contact_id": CONTACT_ID,
                "output": str(OUT_PATH),
                "clock_cpg_total": len(coefficients),
                "clock_cpg_covered": covered,
                "sample_count": len(samples),
                "age_shift_pair_count": len(pairs),
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Fetch and curate the GSE142439 Horvath353 age-clock input table."""

from __future__ import annotations

import csv
import gzip
import json
import tempfile
import urllib.request
from pathlib import Path
from typing import Any


CONTACT_ID = "k-a.gse142439.horvath353"
LAYER = "age_signature"
GEO_ACCESSION = "GSE142439"
PLATFORM = "GPL21145 Infinium MethylationEPIC"
MATRIX_URL = "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE142nnn/GSE142439/matrix/GSE142439_series_matrix.txt.gz"
COEFF_URL = "https://static-content.springer.com/esm/art%3A10.1186%2Fgb-2013-14-10-r115/MediaObjects/13059_2013_3156_MOESM23_ESM.csv"
OUT_PATH = Path(__file__).resolve().parent / "gse142439_horvath353_clock_inputs.json"


def download(url: str, path: Path) -> None:
    request = urllib.request.Request(url, headers={"User-Agent": "cellstate-reality-fetch"})
    with urllib.request.urlopen(request, timeout=120) as response, path.open("wb") as handle:
        while True:
            chunk = response.read(1024 * 1024)
            if not chunk:
                break
            handle.write(chunk)


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


def parse_samples(gsms: list[str]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    if len(gsms) != 16:
        raise ValueError(f"expected 16 GSE142439 samples, found {len(gsms)}")
    samples: list[dict[str, Any]] = []
    pairs: list[dict[str, Any]] = []
    for index, gsm in enumerate(gsms):
        pair_index = index // 2
        person = pair_index + 1
        cell_type = "SkinFibroblasts" if person <= 4 else "VeinEndothelialCells"
        treatment = "Normal" if index % 2 == 0 else "Treated"
        samples.append(
            {
                "gsm": gsm,
                "person": person,
                "cell_type": cell_type,
                "treatment": treatment,
            }
        )
    by_pair: dict[tuple[int, str], dict[str, str]] = {}
    for sample in samples:
        key = (int(sample["person"]), str(sample["cell_type"]))
        bucket = by_pair.setdefault(key, {})
        bucket[str(sample["treatment"]).lower()] = str(sample["gsm"])
    for person in range(1, 9):
        cell_type = "SkinFibroblasts" if person <= 4 else "VeinEndothelialCells"
        bucket = by_pair.get((person, cell_type), {})
        if "normal" not in bucket or "treated" not in bucket:
            raise ValueError(f"missing paired samples for person {person} {cell_type}")
        pairs.append(
            {
                "person": person,
                "cell_type": cell_type,
                "normal_gsm": bucket["normal"],
                "treated_gsm": bucket["treated"],
            }
        )
    return samples, pairs


def parse_matrix(path: Path, wanted_markers: set[str]) -> tuple[list[str], dict[str, dict[str, float]]]:
    in_table = False
    gsm_order: list[str] = []
    beta: dict[str, dict[str, float]] = {}
    with gzip.open(path, "rt", encoding="utf-8", newline="") as handle:
        for raw_line in handle:
            line = raw_line.rstrip("\n")
            if line == "!series_matrix_table_begin":
                in_table = True
                continue
            if line == "!series_matrix_table_end":
                break
            if not in_table:
                continue
            row = next(csv.reader([line], delimiter="\t"))
            if not row:
                continue
            if row[0] == "ID_REF":
                gsm_order = [item.strip() for item in row[1:]]
                continue
            marker = row[0].strip()
            if marker not in wanted_markers:
                continue
            if not gsm_order:
                raise ValueError("matrix table data appeared before the sample header")
            if len(row) - 1 != len(gsm_order):
                raise ValueError(f"row width mismatch for {marker}")
            values: dict[str, float] = {}
            for gsm, raw_value in zip(gsm_order, row[1:]):
                value = float(raw_value)
                if value < 0.0 or value > 1.0:
                    raise ValueError(f"beta value outside [0, 1] for {marker} {gsm}: {value}")
                values[gsm] = value
            beta[marker] = values
    if not gsm_order:
        raise ValueError("GSE142439 matrix table header was not found")
    return gsm_order, beta


def main() -> int:
    tmp_dir = Path(tempfile.gettempdir())
    matrix_path = tmp_dir / "GSE142439_series_matrix.txt.gz"
    coeff_path = tmp_dir / "horvath353_coefficients.csv"
    download(MATRIX_URL, matrix_path)
    download(COEFF_URL, coeff_path)

    intercept, coefficients = parse_coefficients(coeff_path)
    gsm_order, beta = parse_matrix(matrix_path, set(coefficients))
    samples, pairs = parse_samples(gsm_order)
    covered = len(beta)
    if covered == 0:
        raise ValueError("no Horvath clock CpGs were found in the GSE142439 matrix")

    ordered_beta = {marker: beta[marker] for marker in coefficients if marker in beta}
    payload = {
        "contact_id": CONTACT_ID,
        "layer": LAYER,
        "geo_accession": GEO_ACCESSION,
        "platform": PLATFORM,
        "source_urls": {
            "beta_matrix": MATRIX_URL,
            "clock_coefficients": COEFF_URL,
        },
        "intercept": intercept,
        "clock_coefficients": coefficients,
        "clock_cpg_total": len(coefficients),
        "clock_cpg_covered": covered,
        "beta": ordered_beta,
        "samples": samples,
        "pairs": pairs,
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
                "pair_count": len(pairs),
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""重取 MPTR 全时序数据并扫描 age x identity x safety 推广边界。"""

from __future__ import annotations

import csv
import gzip
import json
import math
import re
import tempfile
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
CELLSTATE_ROOT = REPO_ROOT / "tools" / "cellstate_reality"
DATA_DIR = CELLSTATE_ROOT / "data"
OUT_DIR = CELLSTATE_ROOT / "out"
PANEL_PATH = DATA_DIR / "k_i_gse165177_mptr_identity_inputs.json"
CURATED_PATH = DATA_DIR / "gse165180_phase_frontier_inputs.json"
CSV_PATH = OUT_DIR / "gse165180_phase_frontier.csv"
CERT_PATH = OUT_DIR / "gse165180_phase_frontier_certificate.json"

EXPERIMENT_ID = "gse165180_phase_frontier"
CLAIM_ID = "cellstate.promotion-frontier.gse165180"
CONJECTURE_ID = "cellstate.promotion-frontier.gse165180"
LOCAL_NAME = "CellStatePromotionFrontierUp"
AGE_CONTACT_ID = "k-a.gse165179-transient"
IDENTITY_CONTACT_ID = "k-i.gse165177-mptr"

AGE_MATRIX_URL = (
    "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165179/suppl/"
    "GSE165179_Matrix_processed_transient.txt.gz"
)
AGE_SERIES_URL = "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165179/matrix/GSE165179_series_matrix.txt.gz"
RNA_SERIES_URL = "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165177/matrix/GSE165177_series_matrix.txt.gz"
RNA_MATRIX_URLS = [
    "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165177/suppl/"
    "GSE165177_Log2_RPM_Transient_reprogramming.txt.gz",
    "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE165nnn/GSE165177/suppl/"
    "GSE165177_Log2_RPM_Transient_reprogramming_part2_170621.txt.gz",
]
COEFF_URL = (
    "https://static-content.springer.com/esm/art%3A10.1186%2Fgb-2013-14-10-r115/"
    "MediaObjects/13059_2013_3156_MOESM23_ESM.csv"
)

ADULT_AGE = 20.0
TAU_CPG = 0.93
CLOCK_CPG_TOTAL = 353
IDENTITY_RMS_THRESHOLD = 1.5
SAFETY_MAX_THRESHOLD = 1.0
STRICT_POSITIVE_THRESHOLD = 0.0
BLOCKED_PROMOTIONS = ["RejuvenationUp", "RenewableMaintenanceUp", "ImmortalityPotentialUp"]
CASE_LABELS = [
    "case_0.no_age_gain",
    "case_1.clock_only",
    "case_2.identity_or_safety_break",
    "case_3.identity_safe_age_reset_candidate",
]
CASE_SHORT_NAMES = {
    "case_0.no_age_gain": "case_0",
    "case_1.clock_only": "case_1",
    "case_2.identity_or_safety_break": "case_2",
    "case_3.identity_safe_age_reset_candidate": "case_3",
}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def download(url: str, path: Path) -> None:
    request = urllib.request.Request(url, headers={"User-Agent": "cellstate-reality-fetch"})
    with urllib.request.urlopen(request, timeout=240) as response, path.open("wb") as handle:
        while True:
            chunk = response.read(1024 * 1024)
            if not chunk:
                break
            handle.write(chunk)


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


def parse_exp(title: str) -> str | None:
    match = re.search(r"_(exp[12])$", normalized_title(title))
    return match.group(1) if match else None


def parse_condition(title: str) -> str:
    normalized = normalized_title(title)
    if normalized in {"O1_Fib", "O2_Fib", "O3_Fib"}:
        return "baseline"
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


def control_condition_for(condition: str) -> str | None:
    if condition in {"transiently_reprogrammed", "failed_to_reprogram"}:
        return "negative_control"
    if condition in {"transient_intermediate", "failed_intermediate"}:
        return "negative_control_intermediate"
    return None


def scope_key(sample: dict[str, Any]) -> tuple[str, int, str, str] | None:
    donor = sample.get("donor")
    day = sample.get("day")
    condition = sample.get("condition")
    exp = sample.get("exp")
    if isinstance(donor, str) and isinstance(day, int) and isinstance(condition, str) and isinstance(exp, str):
        return donor, day, condition, exp
    return None


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
        condition = parse_condition(title)
        samples[title] = {
            "title": title,
            "normalized_title": normalized_title(title),
            "gsm": gsms[index],
            "source_name": sources[index],
            "characteristics": parsed_characteristics,
            "raw_characteristics": raw_characteristics,
            "donor": parse_donor(title),
            "condition": condition,
            "day": parse_day(title),
            "exp": parse_exp(title),
            "role": "control" if control_condition_for(condition) is None and condition.startswith("negative_control") else "candidate",
        }
    series_rows = {key: rows[0] for key, rows in parsed.items() if rows and key.startswith("!Series")}
    return {
        "title": first(series_rows.get("!Series_title")),
        "summary": first(series_rows.get("!Series_summary")),
        "overall_design": first(series_rows.get("!Series_overall_design")),
        "samples": samples,
    }


def parse_coefficients(path: Path) -> tuple[float, dict[str, float]]:
    with path.open("r", encoding="utf-8-sig", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None or "CpGmarker" not in reader.fieldnames:
            raise ValueError("Horvath coefficient table is missing CpGmarker")
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
    if len(coefficients) != CLOCK_CPG_TOTAL:
        raise ValueError(f"expected {CLOCK_CPG_TOTAL} Horvath CpGs, found {len(coefficients)}")
    return intercept, coefficients


def age_sample_columns(header: list[str]) -> list[tuple[str, int]]:
    columns: list[tuple[str, int]] = []
    if not header or header[0] != "ID_REF":
        raise ValueError("GSE165179 processed matrix header must start with ID_REF")
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


def parse_age_matrix(path: Path, wanted_markers: set[str]) -> tuple[list[str], dict[str, dict[str, float]]]:
    beta: dict[str, dict[str, float]] = {}
    with gzip.open(path, "rt", encoding="utf-8", newline="") as handle:
        reader = csv.reader(handle)
        header = next(reader)
        columns = age_sample_columns(header)
        samples = [sample for sample, _ in columns]
        for row in reader:
            if not row:
                continue
            marker = row[0].strip()
            if marker not in wanted_markers:
                continue
            values: dict[str, float] = {}
            for sample, column_index in columns:
                raw_value = row[column_index].strip() if column_index < len(row) else ""
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


def score_age_samples(
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
            if isinstance(marker_values, dict) and sample in marker_values:
                linear += weight * float(marker_values[sample])
                used += 1
        scores[sample] = {
            "clock_cpg_used": used,
            "clock_cpg_total": len(coefficients),
            "clock_cpg_coverage_ratio": used / float(len(coefficients)),
            "clock_linear_score": linear,
            "dnam_age": dnam_age(linear),
        }
    return scores


def parse_rna_matrix(path: Path, wanted_genes: set[str]) -> tuple[list[str], dict[str, dict[str, Any]]]:
    genes: dict[str, dict[str, Any]] = {}
    with gzip.open(path, "rt", encoding="utf-8", newline="") as handle:
        reader = csv.reader(handle, delimiter="\t")
        header = next(reader)
        if len(header) < 13 or header[0] != "Probe" or header[5] != "Feature":
            raise ValueError(f"unexpected GSE165177 processed matrix header in {path.name}")
        sample_names = header[12:]
        for row in reader:
            if len(row) < 13:
                continue
            gene = row[5].strip()
            if gene not in wanted_genes:
                continue
            values = {sample: float(raw_value) for sample, raw_value in zip(sample_names, row[12:])}
            if gene not in genes:
                genes[gene] = {
                    "ensembl_id": row[6],
                    "description": row[7],
                    "log2_rpm": {},
                }
            genes[gene]["log2_rpm"].update(values)
    return sample_names, genes


def load_marker_panels() -> tuple[list[str], list[str]]:
    payload = json.loads(PANEL_PATH.read_text(encoding="utf-8"))
    identity = [str(item) for item in payload.get("identity_markers", []) if isinstance(item, str)]
    safety = [str(item) for item in payload.get("pluripotency_markers", []) if isinstance(item, str)]
    if not identity or not safety:
        raise ValueError(f"{PANEL_PATH}: marker panel is missing")
    return identity, safety


def rms(values: list[float]) -> float | None:
    if not values:
        return None
    return math.sqrt(sum(value * value for value in values) / float(len(values)))


def build_age_samples(series: dict[str, Any], scores: dict[str, dict[str, Any]]) -> dict[str, dict[str, Any]]:
    samples: dict[str, dict[str, Any]] = {}
    for title, annotation in series["samples"].items():
        sample = dict(annotation)
        sample.update(scores.get(title, {}))
        samples[title] = sample
    return samples


def build_rna_samples(series: dict[str, Any], sample_names: list[str], genes: dict[str, dict[str, Any]]) -> dict[str, dict[str, Any]]:
    samples: dict[str, dict[str, Any]] = {}
    for sample_name in sample_names:
        title = sample_name
        annotation = series["samples"].get(title) or series["samples"].get(title.replace("_", " "))
        if isinstance(annotation, dict):
            sample = dict(annotation)
        else:
            condition = parse_condition(title)
            sample = {
                "title": title,
                "normalized_title": normalized_title(title),
                "gsm": "",
                "source_name": "",
                "characteristics": {},
                "raw_characteristics": [],
                "donor": parse_donor(title),
                "condition": condition,
                "day": parse_day(title),
                "exp": parse_exp(title),
                "role": "control" if condition.startswith("negative_control") else "candidate",
            }
        sample["marker_expression"] = {
            gene: gene_payload["log2_rpm"][sample_name]
            for gene, gene_payload in genes.items()
            if sample_name in gene_payload.get("log2_rpm", {})
        }
        samples[sample_name] = sample
    return samples


def paired_rows(samples: dict[str, dict[str, Any]], value_key: str) -> dict[tuple[str, int, str, str], dict[str, Any]]:
    by_scope: dict[tuple[str, int, str, str], str] = {}
    for title, sample in samples.items():
        key = scope_key(sample)
        if key is not None:
            by_scope[key] = title

    rows: dict[tuple[str, int, str, str], dict[str, Any]] = {}
    for treated_title, treated in samples.items():
        condition = str(treated.get("condition") or "")
        control_condition = control_condition_for(condition)
        if control_condition is None:
            continue
        donor = treated.get("donor")
        day = treated.get("day")
        exp = treated.get("exp")
        if not isinstance(donor, str) or not isinstance(day, int) or not isinstance(exp, str):
            continue
        control_title = by_scope.get((donor, day, control_condition, exp))
        if control_title is None:
            continue
        control = samples[control_title]
        key = (donor, day, condition, exp)
        rows[key] = {
            "donor": donor,
            "day": day,
            "condition": condition,
            "exp": exp,
            "control_condition": control_condition,
            "control_sample": control_title,
            "treated_sample": treated_title,
            "control": control,
            "treated": treated,
            "control_value": control.get(value_key),
            "treated_value": treated.get(value_key),
        }
    return rows


def identity_safety_metrics(
    rna_pair: dict[str, Any],
    identity_markers: list[str],
    safety_markers: list[str],
) -> dict[str, Any]:
    control_values = rna_pair["control"].get("marker_expression", {})
    treated_values = rna_pair["treated"].get("marker_expression", {})
    identity_expr: dict[str, dict[str, float]] = {}
    safety_expr: dict[str, dict[str, float]] = {}
    identity_deltas: dict[str, float] = {}
    safety_deltas: dict[str, float] = {}

    for marker in identity_markers:
        if marker in control_values and marker in treated_values:
            control_value = float(control_values[marker])
            treated_value = float(treated_values[marker])
            identity_expr[marker] = {"control": control_value, "treated": treated_value}
            identity_deltas[marker] = treated_value - control_value
    for marker in safety_markers:
        if marker in control_values and marker in treated_values:
            control_value = float(control_values[marker])
            treated_value = float(treated_values[marker])
            safety_expr[marker] = {"control": control_value, "treated": treated_value}
            safety_deltas[marker] = treated_value - control_value

    identity_cost = rms(list(identity_deltas.values()))
    safety_values = list(safety_deltas.values())
    return {
        "identity_expression": identity_expr,
        "safety_expression": safety_expr,
        "identity_marker_deltas": identity_deltas,
        "safety_marker_deltas": safety_deltas,
        "identity_cost": identity_cost,
        "safety_risk": max(safety_values) if safety_values else None,
        "safety_pos_count": sum(1 for value in safety_values if value > STRICT_POSITIVE_THRESHOLD),
        "identity_marker_count": len(identity_deltas),
        "safety_marker_count": len(safety_deltas),
    }


def classify(age_gain: float, metrics: dict[str, Any] | None) -> str:
    if age_gain <= 0.0:
        return "case_0.no_age_gain"
    if metrics is None or metrics.get("identity_cost") is None or metrics.get("safety_risk") is None:
        return "case_1.clock_only"
    identity_cost = float(metrics["identity_cost"])
    safety_risk = float(metrics["safety_risk"])
    safety_pos_count = int(metrics.get("safety_pos_count") or 0)
    if identity_cost <= IDENTITY_RMS_THRESHOLD and safety_risk <= SAFETY_MAX_THRESHOLD and safety_pos_count == 0:
        return "case_3.identity_safe_age_reset_candidate"
    return "case_2.identity_or_safety_break"


def check(name: str, passed: bool, reason: str, value: Any | None = None) -> dict[str, Any]:
    item: dict[str, Any] = {"name": name, "passed": bool(passed), "reason": reason}
    if value is not None:
        item["value"] = value
    return item


def write_csv(rows: list[dict[str, Any]]) -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "donor",
        "day",
        "condition",
        "exp",
        "age_gain",
        "identity_cost",
        "safety_risk",
        "safety_pos_count",
        "case",
    ]
    with CSV_PATH.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow({key: row.get(key, "") for key in fieldnames})


def main() -> int:
    started_at = now_iso()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    tmp_dir = Path(tempfile.gettempdir())
    identity_markers, safety_markers = load_marker_panels()
    wanted_genes = set(identity_markers + safety_markers)

    age_matrix_path = tmp_dir / "GSE165179_Matrix_processed_transient.txt.gz"
    age_series_path = tmp_dir / "GSE165179_series_matrix.txt.gz"
    rna_series_path = tmp_dir / "GSE165177_series_matrix.txt.gz"
    coeff_path = tmp_dir / "horvath353_coefficients.csv"
    download(AGE_MATRIX_URL, age_matrix_path)
    download(AGE_SERIES_URL, age_series_path)
    download(RNA_SERIES_URL, rna_series_path)
    download(COEFF_URL, coeff_path)

    intercept, coefficients = parse_coefficients(coeff_path)
    age_series = parse_series_matrix(age_series_path)
    age_sample_names, beta = parse_age_matrix(age_matrix_path, set(coefficients))
    age_scores = score_age_samples(age_sample_names, intercept, coefficients, beta)
    age_samples = build_age_samples(age_series, age_scores)

    rna_series = parse_series_matrix(rna_series_path)
    rna_sample_names: list[str] = []
    genes: dict[str, dict[str, Any]] = {}
    for index, url in enumerate(RNA_MATRIX_URLS, 1):
        rna_matrix_path = tmp_dir / f"GSE165177_Log2_RPM_full_{index}.txt.gz"
        download(url, rna_matrix_path)
        sample_names, parsed_genes = parse_rna_matrix(rna_matrix_path, wanted_genes)
        for sample_name in sample_names:
            if sample_name not in rna_sample_names:
                rna_sample_names.append(sample_name)
        for gene, payload in parsed_genes.items():
            if gene not in genes:
                genes[gene] = {
                    "ensembl_id": payload.get("ensembl_id", ""),
                    "description": payload.get("description", ""),
                    "log2_rpm": {},
                }
            genes[gene]["log2_rpm"].update(payload.get("log2_rpm", {}))
    rna_samples = build_rna_samples(rna_series, rna_sample_names, genes)

    age_pairs = paired_rows(age_samples, "dnam_age")
    rna_pairs = paired_rows(rna_samples, "marker_expression")
    all_keys = sorted(set(age_pairs) | set(rna_pairs))
    joined_keys = sorted(set(age_pairs) & set(rna_pairs))

    rows: list[dict[str, Any]] = []
    joined_details: list[dict[str, Any]] = []
    missing_modalities: list[dict[str, Any]] = []
    for key in all_keys:
        donor, day, condition, exp = key
        age_pair = age_pairs.get(key)
        rna_pair = rna_pairs.get(key)
        if age_pair is None:
            missing_modalities.append(
                {"donor": donor, "day": day, "condition": condition, "exp": exp, "has_age": False, "has_rna": True}
            )
            continue
        control_age = age_pair.get("control_value")
        treated_age = age_pair.get("treated_value")
        if control_age is None or treated_age is None:
            missing_modalities.append(
                {"donor": donor, "day": day, "condition": condition, "exp": exp, "has_age": False, "has_rna": rna_pair is not None}
            )
            continue
        age_gain = float(control_age) - float(treated_age)
        metrics = identity_safety_metrics(rna_pair, identity_markers, safety_markers) if rna_pair is not None else None
        if rna_pair is None:
            missing_modalities.append(
                {"donor": donor, "day": day, "condition": condition, "exp": exp, "has_age": True, "has_rna": False}
            )
        case_label = classify(age_gain, metrics)
        row = {
            "donor": donor,
            "day": day,
            "condition": condition,
            "exp": exp,
            "age_gain": age_gain,
            "identity_cost": "" if metrics is None or metrics.get("identity_cost") is None else metrics["identity_cost"],
            "safety_risk": "" if metrics is None or metrics.get("safety_risk") is None else metrics["safety_risk"],
            "safety_pos_count": "" if metrics is None else metrics["safety_pos_count"],
            "case": case_label,
        }
        rows.append(row)
        if metrics is not None:
            joined_details.append(
                {
                    "scope": {"donor": donor, "day": day, "condition": condition, "exp": exp},
                    "age": {
                        "control_sample": age_pair["control_sample"],
                        "treated_sample": age_pair["treated_sample"],
                        "control_dnam_age": control_age,
                        "treated_dnam_age": treated_age,
                        "age_gain": age_gain,
                    },
                    "rna": {
                        "control_sample": rna_pair["control_sample"],
                        "treated_sample": rna_pair["treated_sample"],
                        "identity_cost": metrics["identity_cost"],
                        "safety_risk": metrics["safety_risk"],
                        "safety_pos_count": metrics["safety_pos_count"],
                        "identity_marker_deltas": metrics["identity_marker_deltas"],
                        "safety_marker_deltas": metrics["safety_marker_deltas"],
                    },
                    "case": case_label,
                }
            )

    rows.sort(key=lambda row: (str(row["donor"]), int(row["day"]), str(row["exp"]), str(row["condition"])))
    joined_details.sort(
        key=lambda item: (
            str(item["scope"]["donor"]),
            int(item["scope"]["day"]),
            str(item["scope"]["exp"]),
            str(item["scope"]["condition"]),
        )
    )
    case_label_counts = {label: 0 for label in CASE_LABELS}
    for row in rows:
        case_label_counts[str(row["case"])] = case_label_counts.get(str(row["case"]), 0) + 1
    case_counts = {short: case_label_counts[label] for label, short in CASE_SHORT_NAMES.items()}
    exists_case_3 = case_counts["case_3"] > 0

    marker_missing = sorted(wanted_genes - set(genes))
    min_clock_coverage = min(sample["clock_cpg_coverage_ratio"] for sample in age_samples.values())
    age_coverage_ok = min_clock_coverage >= TAU_CPG
    joined_three_layer_count = len(joined_details)
    age_gain_rows = [row for row in rows if float(row["age_gain"]) > 0.0]
    sparse = joined_three_layer_count == 0 or (age_gain_rows and not any(item["case"] != "case_1.clock_only" for item in rows))
    if not age_coverage_ok or marker_missing or joined_three_layer_count == 0:
        status = "needs_data"
        promotion_decision = "needs_data"
    elif exists_case_3:
        status = "passed"
        promotion_decision = "support IdentitySafeAgeResetCandidateUp only"
    else:
        status = "failed"
        promotion_decision = (
            "negative theorem: under this MPTR contact and fixed markers, age gain does not promote "
            "to identity-safe age reset"
        )

    write_csv(rows)

    curated_age_samples = [
        {
            "title": sample["title"],
            "gsm": sample.get("gsm", ""),
            "donor": sample.get("donor"),
            "day": sample.get("day"),
            "condition": sample.get("condition"),
            "exp": sample.get("exp"),
            "dnam_age": sample.get("dnam_age"),
            "clock_linear_score": sample.get("clock_linear_score"),
            "clock_cpg_used": sample.get("clock_cpg_used"),
            "clock_cpg_total": sample.get("clock_cpg_total"),
            "clock_cpg_coverage_ratio": sample.get("clock_cpg_coverage_ratio"),
            "characteristics": sample.get("characteristics", {}),
        }
        for sample in sorted(age_samples.values(), key=lambda item: str(item.get("title") or ""))
    ]
    curated_rna_samples = [
        {
            "title": sample["title"],
            "gsm": sample.get("gsm", ""),
            "donor": sample.get("donor"),
            "day": sample.get("day"),
            "condition": sample.get("condition"),
            "exp": sample.get("exp"),
            "marker_expression": sample.get("marker_expression", {}),
            "characteristics": sample.get("characteristics", {}),
        }
        for sample in sorted(rna_samples.values(), key=lambda item: str(item.get("title") or ""))
    ]
    curated = {
        "contact_ids": [AGE_CONTACT_ID, IDENTITY_CONTACT_ID],
        "source_urls": {
            "gse165179_processed_beta_matrix": AGE_MATRIX_URL,
            "gse165179_series_matrix": AGE_SERIES_URL,
            "gse165177_series_matrix": RNA_SERIES_URL,
            "gse165177_processed_log2_rpm_matrices": RNA_MATRIX_URLS,
            "horvath353_coefficients": COEFF_URL,
        },
        "thresholds": {
            "tau_cpg": TAU_CPG,
            "identity_rms_max": IDENTITY_RMS_THRESHOLD,
            "safety_max_delta": SAFETY_MAX_THRESHOLD,
            "strict_positive_delta": STRICT_POSITIVE_THRESHOLD,
        },
        "clock": {
            "intercept": intercept,
            "clock_cpg_total": len(coefficients),
            "clock_cpg_covered_in_matrix": len(beta),
            "minimum_sample_coverage_ratio": min_clock_coverage,
        },
        "identity_markers": identity_markers,
        "safety_markers": safety_markers,
        "missing_markers": marker_missing,
        "age_samples": curated_age_samples,
        "rna_samples": curated_rna_samples,
        "scope_pairs": {
            "age_pair_count": len(age_pairs),
            "rna_pair_count": len(rna_pairs),
            "joined_pair_count": len(joined_keys),
            "joined_three_layer_count": joined_three_layer_count,
            "missing_modalities": missing_modalities,
        },
    }
    CURATED_PATH.write_text(json.dumps(curated, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    note = (
        "Case 3 exists: IdentitySafeAgeResetCandidateUp is locally supported, while function, repeat-cycle, "
        "and organismal contacts remain absent."
        if exists_case_3
        else (
            "No Case 3 scope was found; all age-gain rows with computable identity and safety either lacked a joined "
            "modality or broke the fixed identity/safety boundary."
        )
    )
    if status == "needs_data":
        note = (
            "Needs data: at least one required layer is absent from the joined frontier or coverage is below threshold; "
            "missing modalities are listed explicitly."
        )
    certificate = {
        "local_name": LOCAL_NAME,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "conjecture_id": CONJECTURE_ID,
        "contact_ids": [AGE_CONTACT_ID, IDENTITY_CONTACT_ID],
        "thresholds": {
            "tau_CpG": TAU_CPG,
            "identity_rms_max": IDENTITY_RMS_THRESHOLD,
            "pluripotency_max_delta": SAFETY_MAX_THRESHOLD,
            "strict_no_positive_delta": STRICT_POSITIVE_THRESHOLD,
        },
        "case_counts": case_counts,
        "case_label_counts": case_label_counts,
        "exists_case_3": exists_case_3,
        "promotion_decision": promotion_decision,
        "blocked_promotions": BLOCKED_PROMOTIONS,
        "join_coverage": {
            "age_pair_scopes": len(age_pairs),
            "rna_pair_scopes": len(rna_pairs),
            "joined_scopes": len(joined_keys),
            "joined_three_layer_scopes": joined_three_layer_count,
            "age_gain_rows": len(age_gain_rows),
            "missing_modality_scopes": missing_modalities,
            "sparse": sparse,
        },
        "outputs": {"curated_inputs": rel(CURATED_PATH), "frontier_csv": rel(CSV_PATH)},
        "note": note,
    }
    CERT_PATH.write_text(json.dumps(certificate, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    checks = [
        check(
            "age.coverage.floor",
            age_coverage_ok,
            "Every scored methylation sample must meet the fixed Horvath353 CpG coverage floor.",
            {"minimum_ratio": min_clock_coverage, "threshold": TAU_CPG, "clock_cpg_covered_in_matrix": len(beta)},
        ),
        check(
            "marker.panel.coverage",
            not marker_missing,
            "RNA matrices must contain every fixed identity and pluripotency marker.",
            {"missing_markers": marker_missing, "identity_markers": identity_markers, "safety_markers": safety_markers},
        ),
        check(
            "full-timeseries.join",
            joined_three_layer_count > 0,
            "At least one true donor/day/condition/exp scope must join age, identity, and safety readbacks.",
            {
                "age_pair_scopes": len(age_pairs),
                "rna_pair_scopes": len(rna_pairs),
                "joined_three_layer_scopes": joined_three_layer_count,
            },
        ),
        check(
            "case3.exists",
            exists_case_3,
            "Case 3 requires age gain, identity RMS within threshold, safety max within threshold, and strict no-positive pluripotency deltas.",
            {"case_counts": case_counts},
        ),
        check(
            "promotion.boundary",
            True,
            "The certificate blocks rejuvenation, renewable maintenance, and immortality promotions.",
            {"blocked_promotions": BLOCKED_PROMOTIONS},
        ),
    ]
    result = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "contact_ids": [AGE_CONTACT_ID, IDENTITY_CONTACT_ID],
        "outputs": {"curated_inputs": rel(CURATED_PATH), "frontier_csv": rel(CSV_PATH), "certificate": rel(CERT_PATH)},
        "case_counts": case_counts,
        "case_label_counts": case_label_counts,
        "exists_case_3": exists_case_3,
        "promotion_decision": promotion_decision,
        "join_coverage": certificate["join_coverage"],
        "negative_theorem": None
        if exists_case_3 or status == "needs_data"
        else "Under this MPTR contact and fixed marker thresholds, age gain does not promote to identity-safe age reset.",
        "cannot_claim": BLOCKED_PROMOTIONS + ["function", "repeat-cycle maintenance", "organismal outcome"],
        "note": note,
    }
    print(
        json.dumps(
            {
                "experiment_id": EXPERIMENT_ID,
                "claim_id": CLAIM_ID,
                "started_at": started_at,
                "completed_at": now_iso(),
                "status": status,
                "checks": checks,
                "result": result,
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

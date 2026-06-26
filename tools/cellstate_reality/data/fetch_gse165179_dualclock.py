#!/usr/bin/env python3
"""抓取并整理 GSE165179 MPTR skin&blood 与 pan-tissue 双钟输入。"""

from __future__ import annotations

import csv
import json
import tempfile
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import fetch_gse165180_methylation as base
import fetch_gse165180_timecourse as timecourse


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "cellstate_reality" / "data"
OUT_PATH = DATA_DIR / "gse165179_dualclock_inputs.json"
CONTACT_ID = "k-a.gse165180.horvath353"
SUPER_SERIES = "GSE165180"
METHYLATION_SERIES = "GSE165179"
HORVATH2_URL = "https://raw.githubusercontent.com/bio-learn/biolearn/master/biolearn/data/Horvath2.csv"
HORVATH1_URL = "https://raw.githubusercontent.com/bio-learn/biolearn/master/biolearn/data/Horvath1.csv"
CLOCKS = {
    "skin_blood_horvath2": {
        "display_name": "skin&blood Horvath2",
        "coefficient_url": HORVATH2_URL,
        "total_cpgs": 391,
        "linear_offset": -0.447119319,
    },
    "pan_tissue_horvath1": {
        "display_name": "pan-tissue Horvath1",
        "coefficient_url": HORVATH1_URL,
        "total_cpgs": 353,
        "linear_offset": 0.696,
    },
}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def download(url: str, path: Path, *, attempts: int = 3, timeout: int = 480) -> None:
    last_error: Exception | None = None
    for _ in range(attempts):
        try:
            request = urllib.request.Request(url, headers={"User-Agent": "cellstate-reality-fetch"})
            with urllib.request.urlopen(request, timeout=timeout) as response, path.open("wb") as handle:
                while True:
                    chunk = response.read(1024 * 1024)
                    if not chunk:
                        return
                    handle.write(chunk)
            return
        except Exception as exc:
            last_error = exc
    if last_error is not None:
        raise last_error


def parse_biolearn_coefficients(path: Path, expected_total: int) -> dict[str, float]:
    with path.open("r", encoding="utf-8-sig", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None or "CpGmarker" not in reader.fieldnames or "CoefficientTraining" not in reader.fieldnames:
            raise ValueError(f"{path.name}: missing CpGmarker/CoefficientTraining columns")
        coefficients: dict[str, float] = {}
        for row in reader:
            marker = str(row.get("CpGmarker", "")).strip()
            raw = str(row.get("CoefficientTraining", "")).strip()
            if not marker or marker == "(Intercept)" or not raw:
                continue
            if not marker.startswith("cg"):
                continue
            coefficients[marker] = float(raw)
    if len(coefficients) != expected_total:
        raise ValueError(f"{path.name}: expected {expected_total} CpGs, found {len(coefficients)}")
    return coefficients


def load_matrix(wanted_markers: set[str]) -> tuple[list[str], dict[str, dict[str, float]], str]:
    matrix_path = Path(tempfile.gettempdir()) / "GSE165179_Matrix_processed_transient.txt.gz"
    try:
        download(base.GSE165179_MATRIX_URL, matrix_path)
        sample_names, beta = base.parse_processed_matrix(matrix_path, wanted_markers)
        return sample_names, beta, "downloaded"
    except Exception:
        if not timecourse.LOCAL_CACHE.exists():
            raise
        payload = json.loads(timecourse.LOCAL_CACHE.read_text(encoding="utf-8"))
        source_beta = payload.get("beta")
        samples = payload.get("samples")
        if not isinstance(source_beta, dict) or not isinstance(samples, list):
            raise
        sample_names = [str(sample.get("title")) for sample in samples if isinstance(sample, dict) and sample.get("title")]
        beta = {}
        for marker in wanted_markers:
            values = source_beta.get(marker)
            if isinstance(values, dict):
                beta[marker] = {str(sample): float(value) for sample, value in values.items()}
        return sample_names, beta, "local_cache_after_download_failure"


def annotated_pairs(
    samples: dict[str, dict[str, Any]],
    selected_samples: list[dict[str, Any]],
    pairs: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    selected_by_title = {str(sample["title"]): sample for sample in selected_samples}
    rows: list[dict[str, Any]] = []
    for pair in pairs:
        baseline = selected_by_title[str(pair["baseline_sample"])]
        treated = selected_by_title[str(pair["treated_sample"])]
        rows.append(
            {
                "donor": str(pair["donor"]),
                "day": int(pair["day"]),
                "phase_length_days": int(pair["phase_length_days"]),
                "experiment": pair.get("experiment"),
                "baseline": {
                    "title": str(pair["baseline_sample"]),
                    "gsm": str(baseline.get("gsm") or samples[str(pair["baseline_sample"])].get("gsm") or ""),
                    "sample_title": str(pair["baseline_sample"]),
                    "condition": str(baseline.get("condition") or ""),
                    "cell_type": str(baseline.get("characteristics", {}).get("cell type", "")),
                    "phase_length_days": str(baseline.get("characteristics", {}).get("length of reprogramming phase (days)", "")),
                },
                "treated": {
                    "title": str(pair["treated_sample"]),
                    "gsm": str(treated.get("gsm") or samples[str(pair["treated_sample"])].get("gsm") or ""),
                    "sample_title": str(pair["treated_sample"]),
                    "condition": str(treated.get("condition") or ""),
                    "cell_type": str(treated.get("characteristics", {}).get("cell type", "")),
                    "phase_length_days": str(treated.get("characteristics", {}).get("length of reprogramming phase (days)", "")),
                },
            }
        )
    return rows


def main() -> int:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    tmp_dir = Path(tempfile.gettempdir())
    series_path = tmp_dir / "GSE165179_series_matrix.txt.gz"
    download(base.GSE165179_SERIES_URL, series_path)
    series = base.parse_series_matrix(series_path)

    clock_payload: dict[str, dict[str, Any]] = {}
    wanted_markers: set[str] = set()
    for clock_id, spec in CLOCKS.items():
        coeff_path = tmp_dir / f"{clock_id}.csv"
        download(str(spec["coefficient_url"]), coeff_path, timeout=120)
        coefficients = parse_biolearn_coefficients(coeff_path, int(spec["total_cpgs"]))
        wanted_markers.update(coefficients)
        clock_payload[clock_id] = {
            "display_name": spec["display_name"],
            "coefficient_url": spec["coefficient_url"],
            "clock_cpg_total": spec["total_cpgs"],
            "linear_offset": spec["linear_offset"],
            "coefficients": coefficients,
        }

    matrix_samples, beta, matrix_source = load_matrix(wanted_markers)
    if set(matrix_samples) != set(series["samples"]):
        missing_in_series = sorted(set(matrix_samples) - set(series["samples"]))
        missing_in_matrix = sorted(set(series["samples"]) - set(matrix_samples))
        raise ValueError(
            "GSE165179 matrix samples and series annotations differ: "
            f"missing_in_series={missing_in_series}; missing_in_matrix={missing_in_matrix}"
        )

    _rows, selected_samples, pairs = timecourse.timecourse_scope(series["samples"], matrix_samples)
    selected_titles = {str(sample["title"]) for sample in selected_samples}
    selected_beta = {
        marker: {sample: values[sample] for sample in sorted(selected_titles) if sample in values}
        for marker, values in beta.items()
        if marker in wanted_markers
    }

    for clock_id, clock in clock_payload.items():
        coefficients = clock["coefficients"]
        covered = sum(1 for marker in coefficients if marker in selected_beta)
        total = int(clock["clock_cpg_total"])
        clock["clock_cpg_covered"] = covered
        clock["clock_cpg_coverage_ratio"] = covered / float(total)

    selected_sample_rows = [
        {
            "title": str(sample["title"]),
            "gsm": str(sample.get("gsm") or ""),
            "donor": sample.get("donor"),
            "condition": sample.get("condition"),
            "day": sample.get("day"),
            "experiment": sample.get("experiment"),
            "cell_type": sample.get("characteristics", {}).get("cell type"),
            "phase_length_days": sample.get("characteristics", {}).get("length of reprogramming phase (days)"),
            "donor_age_years": sample.get("donor_age_years"),
        }
        for sample in selected_samples
    ]

    payload = {
        "contact_id": CONTACT_ID,
        "layer": "age_signature",
        "super_series": SUPER_SERIES,
        "geo_accession": METHYLATION_SERIES,
        "platform": base.PLATFORM,
        "created_at": now_iso(),
        "source_urls": {
            "series_matrix": base.GSE165179_SERIES_URL,
            "processed_beta_matrix": base.GSE165179_MATRIX_URL,
            "skin_blood_horvath2_coefficients": HORVATH2_URL,
            "pan_tissue_horvath1_coefficients": HORVATH1_URL,
        },
        "matrix_source": matrix_source,
        "series": {
            "title": series.get("title"),
            "summary": series.get("summary"),
            "overall_design": series.get("overall_design"),
        },
        "clock_formula": {
            "linear_score": "z = sum_j w_j * beta_sample_j over covered CpGs",
            "skin_blood_horvath2": "DNAmAge = anti_trafo(z - 0.447119319)",
            "pan_tissue_horvath1": "DNAmAge = anti_trafo(z + 0.696)",
            "anti_trafo": "x < 0: (1+20)*exp(x)-1; otherwise: (1+20)*x+20",
        },
        "clocks": clock_payload,
        "beta": {marker: selected_beta[marker] for marker in sorted(selected_beta)},
        "beta_marker_union_covered": len(selected_beta),
        "samples": selected_sample_rows,
        "pairs": pairs,
        "sample_phase_annotations": annotated_pairs(series["samples"], selected_samples, pairs),
        "cannot_claim": [
            "This curated input supports only age_signature-layer DNAm clock method comparison.",
            "It does not establish identity, function, safety, rejuvenation, maintenance, or immortality.",
            "Clock direction is a proxy readback and not biological proof that cells are truly younger or older.",
            "GSE165180/GSE165179 and GSE142439 are not merged into one cohort.",
        ],
    }
    OUT_PATH.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(
        json.dumps(
            {
                "curated_output": rel(OUT_PATH),
                "matrix_source": matrix_source,
                "sample_count": len(selected_samples),
                "pair_count": len(pairs),
                "treated_days": sorted({int(pair["day"]) for pair in pairs}),
                "coverage": {
                    clock_id: {
                        "covered": clock["clock_cpg_covered"],
                        "total": clock["clock_cpg_total"],
                        "ratio": clock["clock_cpg_coverage_ratio"],
                    }
                    for clock_id, clock in clock_payload.items()
                },
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

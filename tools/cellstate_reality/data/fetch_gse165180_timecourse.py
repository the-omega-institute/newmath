#!/usr/bin/env python3
"""抓取并整理 GSE165180/GSE165179 MPTR 全时相 Horvath353 输入。"""

from __future__ import annotations

import json
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import fetch_gse165180_methylation as base


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "cellstate_reality" / "data"
CONTACT_ID = "k-a.gse165180.horvath353"
LAYER = "age_signature"
SUPER_SERIES = "GSE165180"
METHYLATION_SERIES = "GSE165179"
OUT_PATH = DATA_DIR / "gse165180_horvath353_timecourse_inputs.json"
MANIFEST_PATH = DATA_DIR / "gse165180_timecourse_scan_manifest.json"
LOCAL_CACHE = DATA_DIR / "gse165179_transient_clock_inputs.json"


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def phase_days(sample: dict[str, Any]) -> int | None:
    raw = sample.get("characteristics", {}).get("length of reprogramming phase (days)")
    if raw is None or str(raw).strip() == "":
        return None
    try:
        return int(str(raw).strip())
    except ValueError:
        return None


def is_baseline_fibroblast(sample: dict[str, Any]) -> bool:
    return (
        sample.get("condition") == "baseline"
        and sample.get("day") == 0
        and phase_days(sample) == 0
        and sample.get("characteristics", {}).get("cell type") == "Fibroblast"
    )


def is_transient_fibroblast(sample: dict[str, Any]) -> bool:
    return (
        sample.get("condition") == "transiently_reprogrammed"
        and isinstance(sample.get("day"), int)
        and sample.get("day") == phase_days(sample)
        and sample.get("characteristics", {}).get("cell type") == "Transiently reprogrammed fibroblast"
    )


def load_cache(coefficients: dict[str, float]) -> tuple[list[str], dict[str, dict[str, float]]] | None:
    if not LOCAL_CACHE.exists():
        return None
    payload = json.loads(LOCAL_CACHE.read_text(encoding="utf-8"))
    beta = payload.get("beta")
    samples = payload.get("samples")
    if not isinstance(beta, dict) or not isinstance(samples, list):
        return None
    sample_names = [str(sample.get("title")) for sample in samples if isinstance(sample, dict) and sample.get("title")]
    selected_beta: dict[str, dict[str, float]] = {}
    for marker in coefficients:
        values = beta.get(marker)
        if isinstance(values, dict):
            selected_beta[marker] = {str(sample): float(value) for sample, value in values.items()}
    return sample_names, selected_beta


def load_matrix(coefficients: dict[str, float]) -> tuple[list[str], dict[str, dict[str, float]], str]:
    matrix_path = Path(tempfile.gettempdir()) / "GSE165179_Matrix_processed_transient.txt.gz"
    try:
        base.download(base.GSE165179_MATRIX_URL, matrix_path)
        sample_names, beta = base.parse_processed_matrix(matrix_path, set(coefficients))
        return sample_names, beta, "downloaded"
    except Exception:
        cached = load_cache(coefficients)
        if cached is None:
            raise
        sample_names, beta = cached
        return sample_names, beta, "local_cache_after_download_failure"


def timecourse_scope(
    samples: dict[str, dict[str, Any]],
    matrix_samples: list[str],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    matrix_set = set(matrix_samples)
    baselines = {str(sample["donor"]): title for title, sample in samples.items() if is_baseline_fibroblast(sample)}
    rows: list[dict[str, Any]] = []
    pairs: list[dict[str, Any]] = []
    selected_titles: set[str] = set()
    sorted_samples = sorted(
        samples.items(),
        key=lambda item: (
            str(item[1].get("donor") or ""),
            int(item[1].get("day") or 0),
            str(item[1].get("condition") or ""),
            str(item[1].get("experiment") or ""),
            item[0],
        ),
    )
    for title, sample in sorted_samples:
        available = title in matrix_set
        include = available and (is_baseline_fibroblast(sample) or is_transient_fibroblast(sample))
        rows.append(
            {
                "donor": sample.get("donor"),
                "day": sample.get("day"),
                "phase_length_days": phase_days(sample),
                "experiment": sample.get("experiment"),
                "title": title,
                "gsm": sample.get("gsm"),
                "condition": sample.get("condition"),
                "cell_type": sample.get("characteristics", {}).get("cell type"),
                "available_in_matrix": available,
                "included_in_timecourse": include,
            }
        )
        if include:
            selected_titles.add(title)
        if available and is_transient_fibroblast(sample):
            donor = str(sample.get("donor") or "")
            baseline = baselines.get(donor)
            if baseline is not None and baseline in matrix_set:
                pairs.append(
                    {
                        "donor": donor,
                        "day": int(sample["day"]),
                        "phase_length_days": int(sample["day"]),
                        "experiment": sample.get("experiment"),
                        "baseline_sample": baseline,
                        "treated_sample": title,
                        "treated_condition": "transiently_reprogrammed",
                    }
                )
                selected_titles.add(baseline)
                selected_titles.add(title)
    return rows, [samples[title] for title in sorted(selected_titles)], pairs


def manifest_per_day(pairs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    for day in sorted({int(pair["day"]) for pair in pairs}):
        day_pairs = [pair for pair in pairs if int(pair["day"]) == day]
        result.append(
            {
                "day": day,
                "donor_count": len({str(pair["donor"]) for pair in day_pairs}),
                "observation_count": len(day_pairs),
                "samples": [
                    {
                        "donor": pair["donor"],
                        "experiment": pair.get("experiment"),
                        "baseline_sample": pair["baseline_sample"],
                        "treated_sample": pair["treated_sample"],
                    }
                    for pair in day_pairs
                ],
            }
        )
    return result


def write_manifest(
    *,
    series: dict[str, Any],
    rows: list[dict[str, Any]],
    selected_samples: list[dict[str, Any]],
    pairs: list[dict[str, Any]],
    covered: int,
    matrix_source: str,
) -> dict[str, Any]:
    manifest = {
        "status": "available" if pairs and covered > 0 else "needs_data",
        "scanned_at": now_iso(),
        "super_series": SUPER_SERIES,
        "methylation_subseries": METHYLATION_SERIES,
        "platform": base.PLATFORM,
        "source_urls": {
            "series_matrix": base.GSE165179_SERIES_URL,
            "processed_beta_matrix": base.GSE165179_MATRIX_URL,
            "clock_coefficients": base.COEFF_URL,
        },
        "matrix_source": matrix_source,
        "series": {
            "title": series.get("title"),
            "summary": series.get("summary"),
            "overall_design": series.get("overall_design"),
        },
        "timecourse_rows": rows,
        "selected_scope": {
            "baseline_rule": "cell type Fibroblast with phase length 0",
            "treated_rule": "cell type Transiently reprogrammed fibroblast with phase length equal to sample day",
            "donors": sorted({str(pair["donor"]) for pair in pairs}),
            "treated_days": sorted({int(pair["day"]) for pair in pairs}),
            "per_day": manifest_per_day(pairs),
            "selected_samples": [
                {
                    "title": sample["title"],
                    "gsm": sample.get("gsm"),
                    "donor": sample.get("donor"),
                    "condition": sample.get("condition"),
                    "day": sample.get("day"),
                    "experiment": sample.get("experiment"),
                    "cell_type": sample.get("characteristics", {}).get("cell type"),
                    "phase_length_days": sample.get("characteristics", {}).get("length of reprogramming phase (days)"),
                }
                for sample in selected_samples
            ],
            "pairs": pairs,
        },
        "horvath353_join": {
            "clock_cpg_total": 353,
            "clock_cpg_covered": covered,
            "coverage_ratio": covered / 353.0,
        },
        "cannot_claim": [
            "This scan only establishes availability of human methylation age_signature data.",
            "Intermediate, failed, and negative-control MPTR samples are listed but not used as transiently reprogrammed fibroblast treated samples.",
            "It does not test identity, function, safety, rejuvenation, maintenance, or immortality.",
            "GSE165180/GSE165179 and GSE142439 remain separate cohorts and are not merged into one carrier.",
        ],
    }
    MANIFEST_PATH.write_text(json.dumps(manifest, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return manifest


def main() -> int:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    tmp_dir = Path(tempfile.gettempdir())
    series_path = tmp_dir / "GSE165179_series_matrix.txt.gz"
    coeff_path = tmp_dir / "horvath353_coefficients.csv"
    base.download(base.GSE165179_SERIES_URL, series_path)
    base.download(base.COEFF_URL, coeff_path)

    intercept, coefficients = base.parse_coefficients(coeff_path)
    series = base.parse_series_matrix(series_path)
    matrix_samples, beta, matrix_source = load_matrix(coefficients)
    if set(matrix_samples) != set(series["samples"]):
        missing_in_series = sorted(set(matrix_samples) - set(series["samples"]))
        missing_in_matrix = sorted(set(series["samples"]) - set(matrix_samples))
        raise ValueError(
            "GSE165179 matrix samples and series annotations differ: "
            f"missing_in_series={missing_in_series}; missing_in_matrix={missing_in_matrix}"
        )

    rows, selected_samples, pairs = timecourse_scope(series["samples"], matrix_samples)
    selected_titles = {sample["title"] for sample in selected_samples}
    selected_beta = {
        marker: {sample: values[sample] for sample in sorted(selected_titles) if sample in values}
        for marker, values in beta.items()
        if marker in coefficients
    }
    covered = len(selected_beta)
    manifest = write_manifest(
        series=series,
        rows=rows,
        selected_samples=selected_samples,
        pairs=pairs,
        covered=covered,
        matrix_source=matrix_source,
    )
    payload = {
        "contact_id": CONTACT_ID,
        "layer": LAYER,
        "super_series": SUPER_SERIES,
        "geo_accession": METHYLATION_SERIES,
        "platform": base.PLATFORM,
        "source_urls": {
            "series_matrix": base.GSE165179_SERIES_URL,
            "processed_beta_matrix": base.GSE165179_MATRIX_URL,
            "clock_coefficients": base.COEFF_URL,
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
        "manifest": rel(MANIFEST_PATH),
        "cannot_claim": [
            "The curated matrix is age_signature-only.",
            "MPTR transient-phase pluripotency safety is not evaluated by this methylation clock contact.",
            "This contact does not merge GSE165180/GSE165179 with GSE142439.",
        ],
    }
    OUT_PATH.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                "contact_id": CONTACT_ID,
                "curated_output": rel(OUT_PATH),
                "manifest": rel(MANIFEST_PATH),
                "manifest_status": manifest["status"],
                "matrix_source": matrix_source,
                "clock_cpg_total": len(coefficients),
                "clock_cpg_covered": covered,
                "sample_count": len(selected_samples),
                "pair_count": len(pairs),
                "treated_days": sorted({int(pair["day"]) for pair in pairs}),
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Run the ORF-constrained external ACA puncture challenge."""
from __future__ import annotations

import json
import math
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
import sys


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "bio_reality" / "data"
DATA_PATH = DATA_DIR / "orf_constrained_aca_puncture_challenge_dataset.json"
CODE_DATA_PATH = DATA_DIR / "ncbi_genetic_codes.json"
EXPERIMENT_ID = "orf_constrained_aca_puncture_challenge"
CLAIM_ID = "h2.external.aca_puncture_orf_validated"
ACA = "ACA"

MIN_SUPPORTED_SPECIES = 40
MIN_ORF_ELIGIBLE_ACA_WINDOWS = 80
MIN_MATCHED_PAIRS = 80
MIN_POSITIVE_WIN_RATE = 0.75
MAX_MATCHED_SIGN_TEST_P = 0.0001
MIN_CONSERVED_COLUMNS_TOTAL = 500
MIN_ASP_SUPPORT_RATE = 0.85
MAX_THR_SUPPORT_RATE = 0.10
MAX_ALIGNMENT_P = 0.0001
MAX_CONTAMINATION_FRACTION = 0.05
MIN_COMPLETENESS_FRACTION = 0.90
MAX_BINNING_WARNING_FRACTION = 0.10
FORBIDDEN_PROMOTIONS = (
    "translation",
    "protein structure",
    "physical admissibility",
    "biological function",
    "global biological law",
)

sys.path.insert(0, str(DATA_DIR))

from codon_topology_refs import median_closure, reassignment_set, wnr_union_cun  # noqa: E402


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def emit(result: dict[str, Any]) -> int:
    print(json.dumps(result, sort_keys=False))
    return 0


def base_result(started_at: str) -> dict[str, Any]:
    return {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "started_at": started_at,
    }


def relative(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def needs_data(started_at: str, missing_data: list[str]) -> int:
    result = base_result(started_at)
    result.update(
        {
            "status": "needs_data",
            "completed_at": now_iso(),
            "checks": [],
            "result": {"missing_data": missing_data},
            "notes": "ORF-constrained external ACA reassignment challenge data is required before the claim can be tested",
        }
    )
    return emit(result)


def needs_external_audit_tables(started_at: str, data: dict[str, Any]) -> int:
    unresolved = data.get("unresolved_required_audit_tables")
    missing_tables = [str(item) for item in unresolved if isinstance(item, str)] if isinstance(unresolved, list) else []
    checks = [
        {
            "name": "orf_constrained_dataset_loaded",
            "passed": True,
            "actual": relative(DATA_PATH),
            "expected": "curated ORF-constrained external ACA reassignment challenge dataset",
        },
        {
            "name": "external_audit_tables_available",
            "passed": False,
            "actual": {
                "orf_eligible_aca_windows": len(optional_rows(data, "orf_eligible_aca_windows")),
                "matched_control_pairs": len(optional_rows(data, "matched_control_pairs")),
                "conserved_alignment_columns": len(optional_rows(data, "conserved_alignment_columns")),
                "species_qc": len(optional_rows(data, "species_qc")),
                "trna_candidates": len(optional_rows(data, "trna_candidates")),
                "missing_external_audit_tables": missing_tables,
            },
            "expected": "non-empty external window, control, alignment, QC, and tRNA audit tables before confirmatory scoring",
        },
        {"name": "independent_inference_without_geometry", **inference_without_geometry(data)},
        {"name": "median_closure_preserved_after_aca", **median_closure_preserved()},
        {"name": "no_geometry_to_higher_layer_promotion", **no_forbidden_promotion(data)},
    ]
    result = base_result(started_at)
    result.update(
        {
            "status": "needs_data",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {
                "scope": "external_code_read_aca_reassignment_challenge_over_orf_eligible_windows_only",
                "source": data.get("source", ""),
                "snapshot_date": data.get("snapshot_date", ""),
                "missing_external_audit_tables": missing_tables,
                "required_reality_contact": "window-level ORF, matched-control, conserved-alignment, species-QC, and tRNA audit tables independent of BEDC geometry",
                "stronger_statistic": "prospective no-geometry ORF-constrained holdout with at least 40 supported species, 80 ORF-eligible ACA windows, 80 matched control pairs, sign-test win rate at least 0.75 with p <= 0.0001, and at least 500 conserved columns with Asp support rate at least 0.85",
            },
        }
    )
    return emit(result)


def parse_time(value: Any) -> datetime | None:
    text = str(value or "").strip()
    if not text:
        return None
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    try:
        return datetime.fromisoformat(text)
    except ValueError:
        return None


def timestamp_before(left: Any, right: Any) -> bool:
    left_time = parse_time(left)
    right_time = parse_time(right)
    return left_time is not None and right_time is not None and left_time < right_time


def binomial_upper_tail(successes: int, n: int, p: float = 0.5) -> float:
    if not 0 <= successes <= n:
        raise ValueError("successes must be between 0 and n")
    return sum(math.comb(n, k) * (p ** k) * ((1.0 - p) ** (n - k)) for k in range(successes, n + 1))


def rows(data: dict[str, Any], key: str) -> list[dict[str, Any]]:
    raw = data.get(key)
    if not isinstance(raw, list):
        raise ValueError(f"{key} must be a list")
    parsed = [item for item in raw if isinstance(item, dict)]
    if len(parsed) != len(raw):
        raise ValueError(f"{key} must contain only objects")
    return parsed


def optional_rows(data: dict[str, Any], key: str) -> list[dict[str, Any]]:
    raw = data.get(key, [])
    if not isinstance(raw, list):
        raise ValueError(f"{key} must be a list when present")
    parsed = [item for item in raw if isinstance(item, dict)]
    if len(parsed) != len(raw):
        raise ValueError(f"{key} must contain only objects")
    return parsed


def protocol_frozen_before_holdout(data: dict[str, Any]) -> dict[str, Any]:
    flags = (
        "r13_frozen_before_external_evidence",
        "m13_frozen_before_external_evidence",
        "orf_classifier_frozen_before_external_evidence",
        "thresholds_preregistered",
        "analysis_no_geometry_input",
    )
    flags_ok = all(data.get(flag) is True for flag in flags)
    temporal_ok = timestamp_before(data.get("protocol_frozen_at"), data.get("prospective_holdout_observed_at"))
    return {
        "passed": flags_ok and temporal_ok,
        "actual": {
            "protocol_frozen_at": data.get("protocol_frozen_at"),
            "prospective_holdout_observed_at": data.get("prospective_holdout_observed_at"),
            **{flag: data.get(flag) for flag in flags},
        },
        "expected": "all freeze flags true and protocol_frozen_at before prospective_holdout_observed_at",
    }


def inference_without_geometry(data: dict[str, Any]) -> dict[str, Any]:
    methods = data.get("reassignment_inference_methods")
    passed = (
        isinstance(methods, list)
        and bool(methods)
        and all(isinstance(method, str) and method.strip() for method in methods)
        and data.get("geometry_inputs_used") == []
    )
    return {
        "passed": passed,
        "actual": {
            "reassignment_inference_methods": methods,
            "geometry_inputs_used": data.get("geometry_inputs_used"),
        },
        "expected": "non-empty independent inference method list and no geometry inputs",
    }


def positive_support(data: dict[str, Any]) -> dict[str, Any]:
    windows = rows(data, "orf_eligible_aca_windows")
    supported = [
        row for row in windows
        if row.get("orf_eligible") is True
        and str(row.get("codon") or "").upper().replace("T", "U") == ACA
        and row.get("aca_to_asp_called") is True
        and int(row.get("aca_codon_count") or 0) > 0
    ]
    species = {str(row.get("species_id") or row.get("taxon_id") or "") for row in supported}
    species.discard("")
    return {
        "passed": len(species) >= MIN_SUPPORTED_SPECIES and len(supported) >= MIN_ORF_ELIGIBLE_ACA_WINDOWS,
        "actual": {
            "supported_species": len(species),
            "supported_orf_eligible_aca_windows": len(supported),
            "input_windows": len(windows),
        },
        "expected": {
            "min_supported_species": MIN_SUPPORTED_SPECIES,
            "min_orf_eligible_aca_windows": MIN_ORF_ELIGIBLE_ACA_WINDOWS,
        },
    }


def matched_control_sign_test(data: dict[str, Any]) -> dict[str, Any]:
    pairs = rows(data, "matched_control_pairs")
    scored = [
        row for row in pairs
        if row.get("positive_orf_eligible") is True
        and row.get("control_valid") is True
        and isinstance(row.get("positive_aca_score"), (int, float))
        and isinstance(row.get("control_aca_score"), (int, float))
    ]
    wins = sum(1 for row in scored if float(row["positive_aca_score"]) > float(row["control_aca_score"]))
    ties = sum(1 for row in scored if float(row["positive_aca_score"]) == float(row["control_aca_score"]))
    n = len(scored) - ties
    win_rate = wins / n if n else 0.0
    p_value = binomial_upper_tail(wins, n) if n else 1.0
    passed = n >= MIN_MATCHED_PAIRS and win_rate >= MIN_POSITIVE_WIN_RATE and p_value <= MAX_MATCHED_SIGN_TEST_P
    return {
        "passed": passed,
        "actual": {
            "informative_pairs": n,
            "positive_wins": wins,
            "ties_removed": ties,
            "positive_win_rate": win_rate,
            "binomial_upper_tail_p": p_value,
        },
        "expected": {
            "min_pairs": MIN_MATCHED_PAIRS,
            "min_positive_win_rate": MIN_POSITIVE_WIN_RATE,
            "max_binomial_upper_tail_p": MAX_MATCHED_SIGN_TEST_P,
        },
    }


def alignment_enrichment(data: dict[str, Any]) -> dict[str, Any]:
    columns = rows(data, "conserved_alignment_columns")
    asp = sum(1 for row in columns if str(row.get("reference_residue") or "").upper() == "D")
    thr = sum(1 for row in columns if str(row.get("reference_residue") or "").upper() == "T")
    n = len(columns)
    asp_rate = asp / n if n else 0.0
    thr_rate = thr / n if n else 0.0
    p_value = binomial_upper_tail(asp, n) if n else 1.0
    passed = (
        n >= MIN_CONSERVED_COLUMNS_TOTAL
        and asp_rate >= MIN_ASP_SUPPORT_RATE
        and thr_rate <= MAX_THR_SUPPORT_RATE
        and p_value <= MAX_ALIGNMENT_P
    )
    return {
        "passed": passed,
        "actual": {
            "columns": n,
            "asp_support": asp,
            "thr_support": thr,
            "asp_support_rate": asp_rate,
            "thr_support_rate": thr_rate,
            "binomial_upper_tail_p": p_value,
        },
        "expected": {
            "min_columns_total": MIN_CONSERVED_COLUMNS_TOTAL,
            "min_asp_support_rate": MIN_ASP_SUPPORT_RATE,
            "max_thr_support_rate": MAX_THR_SUPPORT_RATE,
            "max_binomial_upper_tail_p": MAX_ALIGNMENT_P,
        },
    }


def artifact_qc(data: dict[str, Any]) -> dict[str, Any]:
    species = rows(data, "species_qc")
    if not species:
        return {"passed": False, "actual": {"species_rows": 0}, "expected": "non-empty species QC rows"}
    contamination_ok = all(float(row.get("contamination_fraction") or 1.0) <= MAX_CONTAMINATION_FRACTION for row in species)
    completeness_ok = all(float(row.get("completeness_fraction") or 0.0) >= MIN_COMPLETENESS_FRACTION for row in species)
    binning_warnings = sum(1 for row in species if row.get("binning_warning") is True)
    warning_fraction = binning_warnings / len(species)
    high_gc_ok = data.get("high_gc_control_passed") is True
    phylogeny_ok = data.get("phylogenetic_coherence_passed") is True
    return {
        "passed": contamination_ok and completeness_ok and warning_fraction <= MAX_BINNING_WARNING_FRACTION and high_gc_ok and phylogeny_ok,
        "actual": {
            "species_rows": len(species),
            "contamination_ok": contamination_ok,
            "completeness_ok": completeness_ok,
            "binning_warning_fraction": warning_fraction,
            "high_gc_control_passed": high_gc_ok,
            "phylogenetic_coherence_passed": phylogeny_ok,
        },
        "expected": {
            "max_contamination_fraction": MAX_CONTAMINATION_FRACTION,
            "min_completeness_fraction": MIN_COMPLETENESS_FRACTION,
            "max_binning_warning_fraction": MAX_BINNING_WARNING_FRACTION,
            "require_high_gc_control": True,
            "require_phylogenetic_coherence": True,
        },
    }


def trna_identity_support(data: dict[str, Any]) -> dict[str, Any]:
    candidates = rows(data, "trna_candidates")
    supported = [
        row for row in candidates
        if str(row.get("anticodon") or "").upper().replace("T", "U") == "UGU"
        and row.get("canonical_thr_identity_element_absent") is True
        and row.get("asp_identity_support") is True
    ]
    return {
        "passed": bool(supported),
        "actual": {"supported_trna_candidates": len(supported), "candidate_rows": len(candidates)},
        "expected": "at least one tRNAUGU candidate with Thr identity loss and Asp-supporting identity evidence",
    }


def prospective_holdout(data: dict[str, Any], support: dict[str, Any], alignment: dict[str, Any]) -> dict[str, Any]:
    temporal_ok = timestamp_before(data.get("protocol_frozen_at"), data.get("prospective_holdout_observed_at"))
    no_geometry_ok = data.get("geometry_inputs_used") == [] and data.get("prospective_holdout_geometry_inputs_used") == []
    passed = bool(temporal_ok and no_geometry_ok and support["passed"] and alignment["passed"])
    return {
        "passed": passed,
        "actual": {
            "temporal_holdout_ok": temporal_ok,
            "geometry_inputs_used": data.get("geometry_inputs_used"),
            "prospective_holdout_geometry_inputs_used": data.get("prospective_holdout_geometry_inputs_used"),
            "positive_support_passed": support["passed"],
            "alignment_enrichment_passed": alignment["passed"],
        },
        "expected": "prospective frozen no-geometry holdout satisfying the ORF support and Asp-column enrichment thresholds",
    }


def median_closure_preserved() -> dict[str, Any]:
    code_data = json.loads(CODE_DATA_PATH.read_text(encoding="utf-8"))
    r13 = reassignment_set(code_data)
    m13 = median_closure(r13)
    r14 = set(r13)
    r14.add(ACA)
    m14 = median_closure(r14)
    expected = wnr_union_cun()
    passed = ACA not in r13 and ACA in m13 and m13 == expected and m14 == expected
    return {
        "passed": passed,
        "actual": {
            "aca_in_r13": ACA in r13,
            "aca_in_m13": ACA in m13,
            "r13_size": len(r13),
            "r14_size": len(r14),
            "m13": sorted(m13),
            "m14": sorted(m14),
        },
        "expected": {
            "aca_in_r13": False,
            "aca_in_m13": True,
            "m13": sorted(expected),
            "m14": sorted(expected),
        },
    }


def no_forbidden_promotion(data: dict[str, Any]) -> dict[str, Any]:
    cannot_claim = data.get("cannot_claim")
    if not isinstance(cannot_claim, list):
        passed = False
    else:
        text = " ".join(str(item).lower() for item in cannot_claim if isinstance(item, str))
        passed = all(term in text for term in FORBIDDEN_PROMOTIONS)
    return {
        "passed": passed,
        "actual": cannot_claim,
        "expected": "explicit cannot-claim boundary for translation, structure, physical admissibility, function, and global law",
    }


def main() -> int:
    started_at = now_iso()
    missing = []
    for path in (DATA_PATH, CODE_DATA_PATH):
        if not path.exists() or path.stat().st_size == 0:
            missing.append(relative(path))
    if missing:
        return needs_data(started_at, missing)

    result = base_result(started_at)
    try:
        data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
        if isinstance(data, dict) and data.get("unresolved_required_audit_tables"):
            audit_table_keys = (
                "orf_eligible_aca_windows",
                "matched_control_pairs",
                "conserved_alignment_columns",
                "species_qc",
                "trna_candidates",
            )
            if all(not optional_rows(data, key) for key in audit_table_keys):
                return needs_external_audit_tables(started_at, data)
        support = positive_support(data)
        alignment = alignment_enrichment(data)
        checks = [
            {
                "name": "orf_constrained_dataset_loaded",
                "passed": isinstance(data, dict) and DATA_PATH.exists(),
                "actual": relative(DATA_PATH),
                "expected": "curated ORF-constrained external ACA reassignment challenge dataset",
            },
            {"name": "protocol_frozen_before_prospective_holdout", **protocol_frozen_before_holdout(data)},
            {"name": "independent_inference_without_geometry", **inference_without_geometry(data)},
            {"name": "orf_eligible_positive_support_minimum", **support},
            {"name": "orf_matched_control_sign_test", **matched_control_sign_test(data)},
            {"name": "conserved_asp_alignment_enrichment", **alignment},
            {"name": "artifact_qc_clean", **artifact_qc(data)},
            {"name": "trna_identity_support", **trna_identity_support(data)},
            {"name": "prospective_holdout_stronger_than_metadata_contact", **prospective_holdout(data, support, alignment)},
            {"name": "median_closure_preserved_after_aca", **median_closure_preserved()},
            {"name": "no_geometry_to_higher_layer_promotion", **no_forbidden_promotion(data)},
        ]
        result.update(
            {
                "status": "passed" if all(check["passed"] for check in checks) else "failed",
                "completed_at": now_iso(),
                "checks": checks,
                "result": {
                    "scope": "external_code_read_aca_reassignment_challenge_over_orf_eligible_windows_only",
                    "source": data.get("source", ""),
                    "snapshot_date": data.get("snapshot_date", ""),
                    "stronger_statistic": "prospective no-geometry ORF-constrained holdout with at least 40 supported species, 80 ORF-eligible ACA windows, 80 matched control pairs, sign-test win rate at least 0.75 with p <= 0.0001, and at least 500 conserved columns with Asp support rate at least 0.85",
                },
            }
        )
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    return emit(result)


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Run the external ACA puncture challenge for the code-read layer."""
from __future__ import annotations

import json
import math
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
import sys


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "bio_reality" / "data"
DATA_PATH = DATA_DIR / "external_aca_puncture_challenge_dataset.json"
CODE_DATA_PATH = DATA_DIR / "ncbi_genetic_codes.json"
EXPERIMENT_ID = "external_aca_puncture_challenge"
CLAIM_ID = "h2.external.aca_puncture_fill_in"
ACA = "ACA"
MIN_SPECIES = 20
MIN_CONSERVED_COLUMNS_TOTAL = 245
MIN_ASP_SUPPORT_RATE = 0.80
MAX_THR_SUPPORT_RATE = 0.20
MAX_ALIGNMENT_P = 0.001
MIN_HOLDOUT_SPECIES = 40
MIN_HOLDOUT_CONSERVED_COLUMNS_TOTAL = 500
MIN_HOLDOUT_ASP_SUPPORT_RATE = 0.85
MAX_HOLDOUT_THR_SUPPORT_RATE = 0.10
MAX_HOLDOUT_ALIGNMENT_P = 0.0001
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
            "notes": "external ACA reassignment audit data is required before the challenge can be tested",
        }
    )
    return emit(result)


def parse_time(value: str) -> datetime:
    text = value.strip()
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    return datetime.fromisoformat(text)


def binomial_upper_tail(successes: int, n: int, p: float = 0.5) -> float:
    if not 0 <= successes <= n:
        raise ValueError("successes must be between 0 and n")
    return sum(math.comb(n, k) * (p ** k) * ((1.0 - p) ** (n - k)) for k in range(successes, n + 1))


def timestamp_before(left: Any, right: Any) -> bool:
    left_text = str(left or "")
    right_text = str(right or "")
    if not left_text or not right_text:
        return False
    return parse_time(left_text) < parse_time(right_text)


def rows(data: dict[str, Any], key: str) -> list[dict[str, Any]]:
    raw = data.get(key)
    if not isinstance(raw, list):
        raise ValueError(f"{key} must be a list")
    return [item for item in raw if isinstance(item, dict)]


def optional_rows(data: dict[str, Any], key: str) -> list[dict[str, Any]]:
    raw = data.get(key, [])
    if not isinstance(raw, list):
        raise ValueError(f"{key} must be a list when present")
    return [item for item in raw if isinstance(item, dict)]


def protocol_frozen(data: dict[str, Any]) -> bool:
    flags = (
        "r13_frozen_before_external_evidence",
        "m13_frozen_before_external_evidence",
        "thresholds_preregistered",
        "analysis_no_geometry_input",
    )
    if not all(data.get(flag) is True for flag in flags):
        return False
    return timestamp_before(data.get("protocol_frozen_at"), data.get("external_evidence_observed_at"))


def inference_without_geometry(data: dict[str, Any]) -> bool:
    methods = data.get("reassignment_inference_methods")
    if not isinstance(methods, list) or not methods:
        return False
    geometry_inputs = data.get("geometry_inputs_used")
    return geometry_inputs == [] and all(isinstance(method, str) and method.strip() for method in methods)


def species_support(data: dict[str, Any]) -> dict[str, Any]:
    species = rows(data, "species")
    supported = [
        row for row in species
        if row.get("aca_to_asp_called") is True and int(row.get("aca_codon_count") or 0) > 0
    ]
    return {
        "passed": len(supported) >= MIN_SPECIES,
        "actual": {"supported_species": len(supported), "species_rows": len(species)},
        "expected": {"min_species": MIN_SPECIES},
    }


def conserved_column_support(data: dict[str, Any]) -> dict[str, Any]:
    species = rows(data, "species")
    total = sum(int(row.get("conserved_column_count") or 0) for row in species if row.get("aca_to_asp_called") is True)
    return {
        "passed": total >= MIN_CONSERVED_COLUMNS_TOTAL,
        "actual": {"conserved_columns_total": total},
        "expected": {"min_columns_total": MIN_CONSERVED_COLUMNS_TOTAL},
    }


def alignment_enrichment(data: dict[str, Any]) -> dict[str, Any]:
    columns = rows(data, "conserved_alignment_columns")
    if not columns:
        return {
            "passed": False,
            "actual": {"columns": 0},
            "expected": {
                "min_asp_support_rate": MIN_ASP_SUPPORT_RATE,
                "max_thr_support_rate": MAX_THR_SUPPORT_RATE,
                "max_binomial_upper_tail_p": MAX_ALIGNMENT_P,
            },
        }
    asp = sum(1 for row in columns if str(row.get("reference_residue") or "").upper() == "D")
    thr = sum(1 for row in columns if str(row.get("reference_residue") or "").upper() == "T")
    n = len(columns)
    asp_rate = asp / n
    thr_rate = thr / n
    p_value = binomial_upper_tail(asp, n)
    passed = asp_rate >= MIN_ASP_SUPPORT_RATE and thr_rate <= MAX_THR_SUPPORT_RATE and p_value <= MAX_ALIGNMENT_P
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
            "min_asp_support_rate": MIN_ASP_SUPPORT_RATE,
            "max_thr_support_rate": MAX_THR_SUPPORT_RATE,
            "max_binomial_upper_tail_p": MAX_ALIGNMENT_P,
        },
    }


def artifact_audit(data: dict[str, Any]) -> dict[str, Any]:
    species = rows(data, "species")
    if not species:
        return {"passed": False, "actual": {"species_rows": 0}, "expected": "non-empty species audit rows"}
    contamination_ok = all(float(row.get("contamination_fraction") or 1.0) <= MAX_CONTAMINATION_FRACTION for row in species)
    completeness_ok = all(float(row.get("completeness_fraction") or 0.0) >= MIN_COMPLETENESS_FRACTION for row in species)
    binning_warnings = sum(1 for row in species if row.get("binning_warning") is True)
    warning_fraction = binning_warnings / len(species)
    high_gc_ok = data.get("high_gc_control_passed") is True
    phylogeny_ok = data.get("phylogenetic_coherence_passed") is True
    passed = (
        contamination_ok
        and completeness_ok
        and warning_fraction <= MAX_BINNING_WARNING_FRACTION
        and high_gc_ok
        and phylogeny_ok
    )
    return {
        "passed": passed,
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


def prospective_holdout_challenge(data: dict[str, Any]) -> dict[str, Any]:
    holdout_species = optional_rows(data, "prospective_holdout_species")
    holdout_columns = optional_rows(data, "prospective_holdout_conserved_alignment_columns")
    supported_species = [
        row for row in holdout_species
        if row.get("aca_to_asp_called") is True and int(row.get("aca_codon_count") or 0) > 0
    ]
    conserved_total = sum(
        int(row.get("conserved_column_count") or 0)
        for row in holdout_species
        if row.get("aca_to_asp_called") is True
    )
    asp = sum(1 for row in holdout_columns if str(row.get("reference_residue") or "").upper() == "D")
    thr = sum(1 for row in holdout_columns if str(row.get("reference_residue") or "").upper() == "T")
    n = len(holdout_columns)
    asp_rate = asp / n if n else 0.0
    thr_rate = thr / n if n else 0.0
    p_value = binomial_upper_tail(asp, n) if n else 1.0
    temporal_holdout_ok = timestamp_before(data.get("protocol_frozen_at"), data.get("prospective_holdout_observed_at"))
    no_geometry_ok = data.get("prospective_holdout_geometry_inputs_used") == []
    passed = (
        temporal_holdout_ok
        and no_geometry_ok
        and len(supported_species) >= MIN_HOLDOUT_SPECIES
        and conserved_total >= MIN_HOLDOUT_CONSERVED_COLUMNS_TOTAL
        and asp_rate >= MIN_HOLDOUT_ASP_SUPPORT_RATE
        and thr_rate <= MAX_HOLDOUT_THR_SUPPORT_RATE
        and p_value <= MAX_HOLDOUT_ALIGNMENT_P
    )
    return {
        "passed": passed,
        "actual": {
            "protocol_frozen_at": data.get("protocol_frozen_at"),
            "prospective_holdout_observed_at": data.get("prospective_holdout_observed_at"),
            "temporal_holdout_ok": temporal_holdout_ok,
            "prospective_holdout_geometry_inputs_used": data.get("prospective_holdout_geometry_inputs_used"),
            "supported_species": len(supported_species),
            "species_rows": len(holdout_species),
            "conserved_columns_total": conserved_total,
            "holdout_columns": n,
            "asp_support": asp,
            "thr_support": thr,
            "asp_support_rate": asp_rate,
            "thr_support_rate": thr_rate,
            "binomial_upper_tail_p": p_value,
        },
        "expected": {
            "protocol_frozen_before_holdout_observation": True,
            "geometry_inputs_used": [],
            "min_species": MIN_HOLDOUT_SPECIES,
            "min_columns_total": MIN_HOLDOUT_CONSERVED_COLUMNS_TOTAL,
            "min_asp_support_rate": MIN_HOLDOUT_ASP_SUPPORT_RATE,
            "max_thr_support_rate": MAX_HOLDOUT_THR_SUPPORT_RATE,
            "max_binomial_upper_tail_p": MAX_HOLDOUT_ALIGNMENT_P,
        },
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


def no_forbidden_promotion(data: dict[str, Any]) -> bool:
    cannot_claim = data.get("cannot_claim")
    if not isinstance(cannot_claim, list):
        return False
    text = " ".join(str(item).lower() for item in cannot_claim if isinstance(item, str))
    return all(term in text for term in FORBIDDEN_PROMOTIONS)


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
        checks = [
            {
                "name": "external_aca_dataset_loaded",
                "passed": isinstance(data, dict) and DATA_PATH.exists(),
                "actual": relative(DATA_PATH),
                "expected": "curated external ACA reassignment audit dataset",
            },
            {
                "name": "protocol_frozen_before_external_observation",
                "passed": protocol_frozen(data),
                "actual": {
                    "protocol_frozen_at": data.get("protocol_frozen_at"),
                    "external_evidence_observed_at": data.get("external_evidence_observed_at"),
                    "r13_frozen_before_external_evidence": data.get("r13_frozen_before_external_evidence"),
                    "m13_frozen_before_external_evidence": data.get("m13_frozen_before_external_evidence"),
                    "thresholds_preregistered": data.get("thresholds_preregistered"),
                },
                "expected": "frozen protocol timestamp precedes external observation timestamp and all freeze flags are true",
            },
            {
                "name": "independent_reassignment_inference_without_geometry",
                "passed": inference_without_geometry(data),
                "actual": {
                    "reassignment_inference_methods": data.get("reassignment_inference_methods"),
                    "geometry_inputs_used": data.get("geometry_inputs_used"),
                },
                "expected": "non-empty reassignment inference method list and no geometry inputs",
            },
            {"name": "raap2_species_support_minimum", **species_support(data)},
            {"name": "conserved_column_support_minimum", **conserved_column_support(data)},
            {"name": "asp_over_thr_alignment_enrichment", **alignment_enrichment(data)},
            {"name": "artifact_audit_clean", **artifact_audit(data)},
            {"name": "trna_identity_support", **trna_identity_support(data)},
            {"name": "prospective_independent_holdout_challenge", **prospective_holdout_challenge(data)},
            {"name": "median_closure_preserved_after_aca", **median_closure_preserved()},
            {
                "name": "no_geometry_to_higher_layer_promotion",
                "passed": no_forbidden_promotion(data),
                "actual": data.get("cannot_claim"),
                "expected": "explicit cannot-claim boundary for translation, structure, physical admissibility, function, and global law",
            },
        ]
        result.update(
            {
                "status": "passed" if all(check["passed"] for check in checks) else "failed",
                "completed_at": now_iso(),
                "checks": checks,
                "result": {
                    "scope": "external_code_read_aca_reassignment_challenge_only",
                    "source": data.get("source", ""),
                    "snapshot_date": data.get("snapshot_date", ""),
                    "stronger_statistic": "failed metadata contact can only be rescued by a prospective independent holdout: at least 40 ACA-to-Asp species, at least 500 conserved columns, Asp support rate at least 0.85, Thr support rate at most 0.10, and exact one-sided binomial p <= 0.0001 after protocol freeze and without geometry input",
                },
            }
        )
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    return emit(result)


if __name__ == "__main__":
    raise SystemExit(main())

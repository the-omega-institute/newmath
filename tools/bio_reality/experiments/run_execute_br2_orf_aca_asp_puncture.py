#!/usr/bin/env python3
"""Execute the br2 ORF ACA-to-Asp puncture audit when external tables exist."""
from __future__ import annotations

import json
import math
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
import sys


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "bio_reality" / "data"
PACKET_PATH = DATA_DIR / "br2_orf_aca_asp_puncture_execution_packet.json"
AUDIT_PATH = DATA_DIR / "br2_orf_aca_asp_puncture_external_audit_tables.json"
CODE_DATA_PATH = DATA_DIR / "ncbi_genetic_codes.json"
EXPERIMENT_ID = "execute_br2_orf_aca_asp_puncture_v1"
CLAIM_ID = "h3.aca_puncture_bioreality_external_execution"
PACKET_ID = "br2_orf_aca_asp_puncture_v1"
ACA = "ACA"

MIN_SUPPORTED_SPECIES = 40
MIN_TARGET_WINDOWS = 80
MIN_CONTROL_PAIRS_PER_CLASS = 40
MIN_TARGET_WIN_RATE = 0.80
MAX_TARGET_SIGN_TEST_P = 0.00001
MIN_TARGET_OVER_CONTROL_WIN_RATE = 0.80
MAX_CONTROL_POSITIVE_RATE = 0.55
MIN_CONTROL_BINOMIAL_P = 0.05
MIN_ALIGNMENT_COLUMNS = 500
MIN_ASP_SUPPORT_RATE = 0.85
MAX_THR_SUPPORT_RATE = 0.10
MAX_ALIGNMENT_BINOMIAL_P = 0.0001
MAX_CONTAMINATION_FRACTION = 0.05
MIN_COMPLETENESS_FRACTION = 0.90
MAX_BINNING_WARNING_FRACTION = 0.10
CONTROL_CLASSES = (
    "nearest_outgroup",
    "standard_code_aca",
    "orf_ineligible",
    "m_minus_r_non_puncture",
    "off_m",
)

sys.path.insert(0, str(DATA_DIR))

from codon_topology_refs import median_closure, reassignment_set, wnr_union_cun  # noqa: E402


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def relative(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def emit(result: dict[str, Any]) -> int:
    print(json.dumps(result, sort_keys=False))
    return 0


def base_result(started_at: str) -> dict[str, Any]:
    return {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "started_at": started_at,
    }


def needs_data(started_at: str, missing_data: list[str]) -> int:
    result = base_result(started_at)
    result.update(
        {
            "status": "needs_data",
            "completed_at": now_iso(),
            "checks": [],
            "result": {
                "missing_data": missing_data,
                "required_reality_contact": "external packet plus window, control, alignment, QC, and tRNA or aaRS audit tables independent of BEDC geometry",
                "stronger_statistic": "prospective no-geometry execution audit with at least 40 supported species, 80 target ACA windows, 40 matched pairs for every control class, target exact sign-test p <= 1e-5, control enrichment not significant, and at least 500 conserved columns with Asp support rate at least 0.85",
            },
            "notes": "external execution packet and audit tables are required before the claim can be tested",
        }
    )
    return emit(result)


def load_json(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"{relative(path)} must contain a JSON object")
    return data


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


def codon(row: dict[str, Any]) -> str:
    return str(row.get("codon") or "").upper().replace("T", "U")


def number(value: Any, default: float = 0.0) -> float:
    return float(value) if isinstance(value, (int, float)) else default


def score(row: dict[str, Any]) -> float | None:
    for key in ("aca_to_asp_llr_over_thr", "llr_aca_asp_over_thr", "site_llr", "positive_aca_score", "target_aca_score"):
        value = row.get(key)
        if isinstance(value, (int, float)):
            return float(value)
    p_asp = row.get("p_asp")
    p_thr = row.get("p_thr")
    epsilon = row.get("epsilon", 1e-12)
    if isinstance(p_asp, (int, float)) and isinstance(p_thr, (int, float)) and isinstance(epsilon, (int, float)):
        return math.log2((float(p_asp) + float(epsilon)) / (float(p_thr) + float(epsilon)))
    return None


def execution_packet_locked_before_external_holdout(packet: dict[str, Any], audit: dict[str, Any]) -> dict[str, Any]:
    locked_flags = (
        "r13_locked_before_external_evidence",
        "m13_locked_before_external_evidence",
        "endpoint_locked_before_external_evidence",
        "thresholds_preregistered",
        "analysis_no_geometry_input",
    )
    flags_ok = all(packet.get(flag) is True for flag in locked_flags)
    packet_id_ok = str(packet.get("packet_id") or "") == PACKET_ID
    temporal_ok = timestamp_before(packet.get("packet_locked_at"), audit.get("external_holdout_observed_at"))
    endpoint = str(packet.get("endpoint") or "")
    endpoint_ok = "ACA" in endpoint.upper() and "ASP" in endpoint.upper() and "THR" in endpoint.upper()
    return {
        "passed": packet_id_ok and flags_ok and temporal_ok and endpoint_ok,
        "actual": {
            "packet_id": packet.get("packet_id"),
            "packet_locked_at": packet.get("packet_locked_at"),
            "external_holdout_observed_at": audit.get("external_holdout_observed_at"),
            "endpoint": packet.get("endpoint"),
            **{flag: packet.get(flag) for flag in locked_flags},
        },
        "expected": "packet id, endpoint, lock flags, and packet_locked_at before external_holdout_observed_at",
    }


def external_audit_tables_available(audit: dict[str, Any]) -> dict[str, Any]:
    counts = {
        "target_windows": len(optional_rows(audit, "target_windows")),
        "matched_control_pairs": len(optional_rows(audit, "matched_control_pairs")),
        "conserved_alignment_columns": len(optional_rows(audit, "conserved_alignment_columns")),
        "species_qc": len(optional_rows(audit, "species_qc")),
        "trna_or_aars_evidence": len(optional_rows(audit, "trna_or_aars_evidence")),
    }
    return {
        "passed": all(count > 0 for count in counts.values()),
        "actual": counts,
        "expected": "non-empty target, matched-control, alignment, QC, and tRNA or aaRS audit tables",
    }


def independent_execution_without_geometry(packet: dict[str, Any], audit: dict[str, Any]) -> dict[str, Any]:
    methods = audit.get("reassignment_inference_methods")
    geometry_inputs = list(audit.get("geometry_inputs_used") or []) + list(packet.get("geometry_inputs_used") or [])
    passed = (
        isinstance(methods, list)
        and bool(methods)
        and all(isinstance(method, str) and method.strip() for method in methods)
        and geometry_inputs == []
        and packet.get("analysis_no_geometry_input") is True
    )
    return {
        "passed": passed,
        "actual": {
            "reassignment_inference_methods": methods,
            "geometry_inputs_used": geometry_inputs,
            "analysis_no_geometry_input": packet.get("analysis_no_geometry_input"),
        },
        "expected": "non-empty external inference methods and no BEDC geometry inputs in execution scoring",
    }


def target_aca_asp_llr_sign_test(audit: dict[str, Any]) -> dict[str, Any]:
    targets = [
        row for row in rows(audit, "target_windows")
        if row.get("primary_qc_pass") is True
        and row.get("orf_eligible") is True
        and codon(row) == ACA
        and score(row) is not None
    ]
    species = {str(row.get("species_id") or row.get("taxon_id") or "") for row in targets}
    species.discard("")
    wins = sum(1 for row in targets if (score(row) or 0.0) > 0.0)
    n = len(targets)
    win_rate = wins / n if n else 0.0
    p_value = binomial_upper_tail(wins, n) if n else 1.0
    passed = (
        len(species) >= MIN_SUPPORTED_SPECIES
        and n >= MIN_TARGET_WINDOWS
        and win_rate >= MIN_TARGET_WIN_RATE
        and p_value <= MAX_TARGET_SIGN_TEST_P
    )
    return {
        "passed": passed,
        "actual": {
            "supported_species": len(species),
            "target_windows": n,
            "asp_over_thr_wins": wins,
            "win_rate": win_rate,
            "binomial_upper_tail_p": p_value,
        },
        "expected": {
            "min_supported_species": MIN_SUPPORTED_SPECIES,
            "min_target_windows": MIN_TARGET_WINDOWS,
            "min_target_win_rate": MIN_TARGET_WIN_RATE,
            "max_sign_test_p": MAX_TARGET_SIGN_TEST_P,
        },
    }


def control_specificity_gate(audit: dict[str, Any]) -> dict[str, Any]:
    pairs = rows(audit, "matched_control_pairs")
    per_class: dict[str, dict[str, Any]] = {}
    all_passed = True
    for control_class in CONTROL_CLASSES:
        subset = [
            row for row in pairs
            if str(row.get("control_class") or "") == control_class
            and row.get("primary_qc_pass") is not False
        ]
        informative = []
        control_positive = 0
        target_wins = 0
        for row in subset:
            target = row.get("target_llr")
            control = row.get("control_llr")
            if not isinstance(target, (int, float)):
                target = row.get("positive_aca_score")
            if not isinstance(control, (int, float)):
                control = row.get("control_aca_score")
            if isinstance(target, (int, float)) and isinstance(control, (int, float)) and float(target) != float(control):
                informative.append(row)
                if float(target) > float(control):
                    target_wins += 1
                if float(control) > 0.0:
                    control_positive += 1
        n = len(informative)
        target_over_control_rate = target_wins / n if n else 0.0
        control_positive_rate = control_positive / n if n else 0.0
        control_p = binomial_upper_tail(control_positive, n) if n else 1.0
        class_passed = (
            n >= MIN_CONTROL_PAIRS_PER_CLASS
            and target_over_control_rate >= MIN_TARGET_OVER_CONTROL_WIN_RATE
            and control_positive_rate <= MAX_CONTROL_POSITIVE_RATE
            and control_p >= MIN_CONTROL_BINOMIAL_P
        )
        per_class[control_class] = {
            "passed": class_passed,
            "informative_pairs": n,
            "target_over_control_rate": target_over_control_rate,
            "control_positive_rate": control_positive_rate,
            "control_binomial_upper_tail_p": control_p,
        }
        all_passed = all_passed and class_passed
    return {
        "passed": all_passed,
        "actual": per_class,
        "expected": {
            "min_pairs_per_class": MIN_CONTROL_PAIRS_PER_CLASS,
            "min_target_over_control_win_rate": MIN_TARGET_OVER_CONTROL_WIN_RATE,
            "max_control_positive_rate": MAX_CONTROL_POSITIVE_RATE,
            "min_control_binomial_p": MIN_CONTROL_BINOMIAL_P,
        },
    }


def asp_over_thr_alignment_enrichment(audit: dict[str, Any]) -> dict[str, Any]:
    columns = rows(audit, "conserved_alignment_columns")
    asp = sum(1 for row in columns if str(row.get("reference_residue") or row.get("aligned_residue") or "").upper() == "D")
    thr = sum(1 for row in columns if str(row.get("reference_residue") or row.get("aligned_residue") or "").upper() == "T")
    n = len(columns)
    asp_rate = asp / n if n else 0.0
    thr_rate = thr / n if n else 0.0
    p_value = binomial_upper_tail(asp, n) if n else 1.0
    passed = (
        n >= MIN_ALIGNMENT_COLUMNS
        and asp_rate >= MIN_ASP_SUPPORT_RATE
        and thr_rate <= MAX_THR_SUPPORT_RATE
        and p_value <= MAX_ALIGNMENT_BINOMIAL_P
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
            "min_alignment_columns": MIN_ALIGNMENT_COLUMNS,
            "min_asp_support_rate": MIN_ASP_SUPPORT_RATE,
            "max_thr_support_rate": MAX_THR_SUPPORT_RATE,
            "max_binomial_p": MAX_ALIGNMENT_BINOMIAL_P,
        },
    }


def artifact_qc_clean(audit: dict[str, Any]) -> dict[str, Any]:
    qc_rows = rows(audit, "species_qc")
    contamination_ok = all(number(row.get("contamination_fraction"), 1.0) <= MAX_CONTAMINATION_FRACTION for row in qc_rows)
    completeness_ok = all(number(row.get("completeness_fraction"), 0.0) >= MIN_COMPLETENESS_FRACTION for row in qc_rows)
    warnings = sum(1 for row in qc_rows if row.get("binning_warning") is True)
    warning_fraction = warnings / len(qc_rows) if qc_rows else 1.0
    high_gc_ok = audit.get("high_gc_control_passed") is True
    phylogeny_ok = audit.get("phylogenetic_coherence_passed") is True
    passed = bool(qc_rows) and contamination_ok and completeness_ok and warning_fraction <= MAX_BINNING_WARNING_FRACTION and high_gc_ok and phylogeny_ok
    return {
        "passed": passed,
        "actual": {
            "species_qc_rows": len(qc_rows),
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


def trna_or_aars_identity_support(audit: dict[str, Any]) -> dict[str, Any]:
    evidence = rows(audit, "trna_or_aars_evidence")
    supported = [
        row for row in evidence
        if (
            str(row.get("anticodon") or "").upper().replace("T", "U") == "UGU"
            and row.get("canonical_thr_identity_element_absent") is True
            and row.get("asp_identity_support") is True
        )
        or (
            str(row.get("evidence_type") or "").lower() == "aars"
            and row.get("asp_charging_support") is True
            and row.get("thr_charging_support") is not True
        )
    ]
    return {
        "passed": bool(supported),
        "actual": {
            "evidence_rows": len(evidence),
            "supported_rows": len(supported),
        },
        "expected": "at least one tRNAUGU or aaRS row supporting Asp identity over Thr identity",
    }


def median_closure_preserved_after_aca() -> dict[str, Any]:
    code_data = load_json(CODE_DATA_PATH)
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


def no_geometry_to_higher_layer_promotion(packet: dict[str, Any], audit: dict[str, Any]) -> dict[str, Any]:
    cannot_claim = []
    for source in (packet, audit):
        raw = source.get("cannot_claim")
        if isinstance(raw, list):
            cannot_claim.extend(str(item) for item in raw if isinstance(item, str))
    text = " ".join(cannot_claim).lower()
    required_terms = (
        ("geometry", "translation"),
        ("protein", "structure"),
        ("physical", "admissibility"),
        ("biological", "function"),
        ("global", "law"),
    )
    passed = bool(cannot_claim) and all(left in text and right in text for left, right in required_terms)
    return {
        "passed": passed,
        "actual": cannot_claim,
        "expected": "explicit boundary: geometry alone does not establish translation, structure, physical admissibility, function, or global biological law",
    }


def main() -> int:
    started_at = now_iso()
    missing = [
        relative(path)
        for path in (PACKET_PATH, AUDIT_PATH, CODE_DATA_PATH)
        if not path.exists() or path.stat().st_size == 0
    ]
    if missing:
        return needs_data(started_at, missing)

    result = base_result(started_at)
    try:
        packet = load_json(PACKET_PATH)
        audit = load_json(AUDIT_PATH)
        checks = [
            {"name": "execution_packet_locked_before_external_holdout", **execution_packet_locked_before_external_holdout(packet, audit)},
            {"name": "external_audit_tables_available", **external_audit_tables_available(audit)},
            {"name": "independent_execution_without_geometry", **independent_execution_without_geometry(packet, audit)},
            {"name": "target_aca_asp_llr_sign_test", **target_aca_asp_llr_sign_test(audit)},
            {"name": "control_specificity_gate", **control_specificity_gate(audit)},
            {"name": "asp_over_thr_alignment_enrichment", **asp_over_thr_alignment_enrichment(audit)},
            {"name": "artifact_qc_clean", **artifact_qc_clean(audit)},
            {"name": "trna_or_aars_identity_support", **trna_or_aars_identity_support(audit)},
            {"name": "median_closure_preserved_after_aca", **median_closure_preserved_after_aca()},
            {"name": "no_geometry_to_higher_layer_promotion", **no_geometry_to_higher_layer_promotion(packet, audit)},
        ]
        result.update(
            {
                "status": "passed" if all(check["passed"] for check in checks) else "failed",
                "completed_at": now_iso(),
                "checks": checks,
                "result": {
                    "scope": "external_aca_to_asp_execution_over_orf_eligible_windows_with_matched_controls",
                    "source": audit.get("source", ""),
                    "snapshot_date": audit.get("snapshot_date", ""),
                    "stronger_statistic": "no-geometry execution audit requiring target Asp-over-Thr exact sign-test p <= 1e-5, per-control specificity, Asp alignment enrichment p <= 1e-4, and clean QC plus tRNA or aaRS support",
                    "cannot_claim": [
                        "The audit does not derive translation from BEDC codon/window geometry alone.",
                        "The audit does not establish protein structure.",
                        "The audit does not establish physical admissibility.",
                        "The audit does not establish biological function.",
                        "The audit does not establish a global biological law.",
                    ],
                },
            }
        )
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    return emit(result)


if __name__ == "__main__":
    raise SystemExit(main())

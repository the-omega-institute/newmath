#!/usr/bin/env python3
"""Run curated ORF interval contact validation for the ORF-eligibility layer."""
from __future__ import annotations

import json
import math
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
import sys


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "bio_reality" / "data"
DATA_PATH = DATA_DIR / "curated_orf_interval_contact_dataset.json"
CODE_DATA_PATH = DATA_DIR / "ncbi_genetic_codes.json"
EXPERIMENT_ID = "curated_orf_interval_contact_validation"
CLAIM_ID = "h2.orf_eligibility.curated_interval_contact"
REQUIRED_CLASSES = {"positive_curated_orf", "matched_non_orf_decoy", "boundary_case"}
POSITIVE_MIN_N = 50
POSITIVE_MIN_ACCEPT_RATE = 0.90
POSITIVE_MAX_P = 0.001
DECOY_MIN_N = 50
DECOY_MIN_REJECT_RATE = 0.80
DECOY_MAX_P = 0.001
BOUNDARY_MIN_N = 20
BOUNDARY_MAX_PROMOTED_FRACTION = 0.10
SPLIT_MIN_COUNT = 3
SPLIT_MIN_POSITIVE_ACCEPT_RATE = 0.80
SPLIT_MIN_DECOY_REJECT_RATE = 0.70
BASELINE_MIN_PAIRS = 30
BASELINE_MIN_WIN_RATE = 0.65
BASELINE_MAX_P = 0.01
FORBIDDEN_PROMOTIONS = (
    "translation",
    "protein structure",
    "physical admissibility",
    "biological function",
    "global biological law",
)
DNA_TO_RNA = str.maketrans({"T": "U", "t": "u"})
ALLOWED_BASES = set("UCAG")

sys.path.insert(0, str(DATA_DIR))

from codon_topology_refs import table_by_id, validate_code_data  # noqa: E402


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
            "notes": "curated external ORF interval contact data is required before the claim can be tested",
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


def normalize_sequence(sequence: str) -> str:
    return sequence.translate(DNA_TO_RNA).upper()


def codons_in_frame(sequence: str, frame_offset: int) -> list[str]:
    return [
        sequence[index:index + 3]
        for index in range(frame_offset, len(sequence) - 2, 3)
    ]


def start_codons(table: dict[str, Any], codon_order: list[str]) -> set[str]:
    return {
        codon
        for codon, marker in zip(codon_order, table["starts"])
        if marker == "M"
    }


def stop_codons(table: dict[str, Any], codon_order: list[str]) -> set[str]:
    return {
        codon
        for codon, residue in zip(codon_order, table["aa"])
        if residue == "*"
    }


def classify_window(row: dict[str, Any], code_data: dict[str, Any]) -> dict[str, Any]:
    row_id = str(row.get("row_id") or row.get("window_id") or "")
    table_id = int(row.get("genetic_code_table_id", 1))
    frame_offset = int(row.get("frame_offset", 0))
    sequence = normalize_sequence(str(row.get("nucleotide_sequence") or ""))
    if not row_id:
        raise ValueError("row_id or window_id is required")
    if frame_offset not in {0, 1, 2}:
        raise ValueError(f"frame_offset must be 0, 1, or 2 for {row_id}")

    codon_order = code_data["codon_order"]
    table = table_by_id(code_data, table_id)
    starts = start_codons(table, codon_order)
    stops = stop_codons(table, codon_order)
    codons = codons_in_frame(sequence, frame_offset)
    ambiguous_codons = [codon for codon in codons if len(codon) != 3 or set(codon) - ALLOWED_BASES]
    start_positions = [
        {"codon_index": index, "codon": codon}
        for index, codon in enumerate(codons)
        if codon in starts
    ]
    stop_positions = [
        {"codon_index": index, "codon": codon}
        for index, codon in enumerate(codons)
        if codon in stops
    ]
    terminal_stop_hit = bool(stop_positions and stop_positions[-1]["codon_index"] == len(codons) - 1)
    orf_eligible = bool(start_positions and terminal_stop_hit and not ambiguous_codons)
    return {
        "row_id": row_id,
        "class": str(row.get("class") or ""),
        "matched_context_id": str(row.get("matched_context_id") or ""),
        "heldout_split": str(row.get("heldout_split") or ""),
        "orf_eligible": orf_eligible,
        "ambiguous_base_flag": bool(ambiguous_codons),
        "start_codon_hit": bool(start_positions),
        "terminal_stop_hit": terminal_stop_hit,
        "baseline_outputs": row.get("baseline_outputs") if isinstance(row.get("baseline_outputs"), dict) else {},
    }


def rows(data: dict[str, Any]) -> list[dict[str, Any]]:
    raw = data.get("rows")
    if not isinstance(raw, list):
        raise ValueError("curated_orf_interval_contact_dataset.json must contain a rows list")
    parsed = [item for item in raw if isinstance(item, dict)]
    if len(parsed) != len(raw):
        raise ValueError("all rows must be objects")
    return parsed


def protocol_frozen(data: dict[str, Any]) -> bool:
    flags = (
        "classifier_rules_frozen",
        "input_classes_frozen",
        "baselines_predeclared",
        "heldout_splits_frozen",
        "analysis_no_translation_or_structure_input",
    )
    if not all(data.get(flag) is True for flag in flags):
        return False
    frozen_at = str(data.get("protocol_frozen_at") or "")
    observed_at = str(data.get("external_evidence_observed_at") or "")
    if not frozen_at or not observed_at:
        return False
    return parse_time(frozen_at) < parse_time(observed_at)


def no_forbidden_promotion(data: dict[str, Any]) -> bool:
    cannot_claim = data.get("cannot_claim")
    if not isinstance(cannot_claim, list):
        return False
    text = " ".join(str(item).lower() for item in cannot_claim if isinstance(item, str))
    return all(term in text for term in FORBIDDEN_PROMOTIONS)


def class_rows(classified: list[dict[str, Any]], row_class: str) -> list[dict[str, Any]]:
    return [row for row in classified if row["class"] == row_class]


def positive_interval_check(classified: list[dict[str, Any]]) -> dict[str, Any]:
    positives = class_rows(classified, "positive_curated_orf")
    successes = sum(1 for row in positives if row["orf_eligible"])
    n = len(positives)
    rate = successes / n if n else 0.0
    p_value = binomial_upper_tail(successes, n) if n else 1.0
    return {
        "passed": n >= POSITIVE_MIN_N and rate >= POSITIVE_MIN_ACCEPT_RATE and p_value <= POSITIVE_MAX_P,
        "actual": {"accepted": successes, "n": n, "accept_rate": rate, "binomial_upper_tail_p": p_value},
        "expected": {
            "min_n": POSITIVE_MIN_N,
            "min_accept_rate": POSITIVE_MIN_ACCEPT_RATE,
            "max_binomial_upper_tail_p": POSITIVE_MAX_P,
        },
    }


def matched_decoy_check(classified: list[dict[str, Any]]) -> dict[str, Any]:
    decoys = class_rows(classified, "matched_non_orf_decoy")
    rejected = sum(1 for row in decoys if not row["orf_eligible"])
    n = len(decoys)
    rate = rejected / n if n else 0.0
    p_value = binomial_upper_tail(rejected, n) if n else 1.0
    return {
        "passed": n >= DECOY_MIN_N and rate >= DECOY_MIN_REJECT_RATE and p_value <= DECOY_MAX_P,
        "actual": {"rejected": rejected, "n": n, "reject_rate": rate, "binomial_upper_tail_p": p_value},
        "expected": {
            "min_n": DECOY_MIN_N,
            "min_reject_rate": DECOY_MIN_REJECT_RATE,
            "max_binomial_upper_tail_p": DECOY_MAX_P,
        },
    }


def boundary_check(classified: list[dict[str, Any]]) -> dict[str, Any]:
    boundary = class_rows(classified, "boundary_case")
    promoted = sum(1 for row in boundary if row["orf_eligible"] and not row["ambiguous_base_flag"])
    n = len(boundary)
    fraction = promoted / n if n else 1.0
    return {
        "passed": n >= BOUNDARY_MIN_N and fraction <= BOUNDARY_MAX_PROMOTED_FRACTION,
        "actual": {"promoted": promoted, "n": n, "promoted_fraction": fraction},
        "expected": {"min_n": BOUNDARY_MIN_N, "max_promoted_fraction": BOUNDARY_MAX_PROMOTED_FRACTION},
    }


def heldout_split_check(classified: list[dict[str, Any]]) -> dict[str, Any]:
    split_names = sorted({row["heldout_split"] for row in classified if row["heldout_split"]})
    split_results = []
    for split in split_names:
        split_rows = [row for row in classified if row["heldout_split"] == split]
        positives = class_rows(split_rows, "positive_curated_orf")
        decoys = class_rows(split_rows, "matched_non_orf_decoy")
        positive_rate = (sum(1 for row in positives if row["orf_eligible"]) / len(positives)) if positives else 0.0
        decoy_rate = (sum(1 for row in decoys if not row["orf_eligible"]) / len(decoys)) if decoys else 0.0
        split_results.append(
            {
                "heldout_split": split,
                "positive_n": len(positives),
                "decoy_n": len(decoys),
                "positive_accept_rate": positive_rate,
                "decoy_reject_rate": decoy_rate,
                "passed": bool(positives)
                and bool(decoys)
                and positive_rate >= SPLIT_MIN_POSITIVE_ACCEPT_RATE
                and decoy_rate >= SPLIT_MIN_DECOY_REJECT_RATE,
            }
        )
    passed = len(split_results) >= SPLIT_MIN_COUNT and all(item["passed"] for item in split_results)
    return {
        "passed": passed,
        "actual": {"split_count": len(split_results), "splits": split_results},
        "expected": {
            "min_splits": SPLIT_MIN_COUNT,
            "min_positive_accept_rate": SPLIT_MIN_POSITIVE_ACCEPT_RATE,
            "min_decoy_reject_rate": SPLIT_MIN_DECOY_REJECT_RATE,
        },
    }


def baseline_pairwise_check(classified: list[dict[str, Any]]) -> dict[str, Any]:
    positives = {row["matched_context_id"]: row for row in class_rows(classified, "positive_curated_orf") if row["matched_context_id"]}
    decoys = {row["matched_context_id"]: row for row in class_rows(classified, "matched_non_orf_decoy") if row["matched_context_id"]}
    wins = 0
    pairs = 0
    for key, positive in positives.items():
        decoy = decoys.get(key)
        if decoy is None:
            continue
        baselines = positive["baseline_outputs"]
        if not isinstance(baselines, dict) or not baselines:
            continue
        baseline_accepts_positive = any(bool(value) for value in baselines.values())
        classifier_win = positive["orf_eligible"] and not decoy["orf_eligible"] and not baseline_accepts_positive
        wins += 1 if classifier_win else 0
        pairs += 1
    win_rate = wins / pairs if pairs else 0.0
    p_value = binomial_upper_tail(wins, pairs) if pairs else 1.0
    return {
        "passed": pairs >= BASELINE_MIN_PAIRS and win_rate >= BASELINE_MIN_WIN_RATE and p_value <= BASELINE_MAX_P,
        "actual": {"wins": wins, "pairs": pairs, "win_rate": win_rate, "binomial_upper_tail_p": p_value},
        "expected": {
            "min_pairs": BASELINE_MIN_PAIRS,
            "min_win_rate": BASELINE_MIN_WIN_RATE,
            "max_binomial_upper_tail_p": BASELINE_MAX_P,
        },
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
        code_data = json.loads(CODE_DATA_PATH.read_text(encoding="utf-8"))
        validate_code_data(code_data)
        data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
        input_rows = rows(data)
        classified = [classify_window(row, code_data) for row in input_rows]
        observed_classes = {row["class"] for row in classified}
        checks = [
            {
                "name": "curated_interval_dataset_loaded",
                "passed": bool(classified),
                "actual": {"path": relative(DATA_PATH), "rows": len(classified)},
                "expected": "non-empty curated ORF interval contact dataset",
            },
            {
                "name": "protocol_frozen_before_external_observation",
                "passed": protocol_frozen(data),
                "actual": {
                    "protocol_frozen_at": data.get("protocol_frozen_at"),
                    "external_evidence_observed_at": data.get("external_evidence_observed_at"),
                    "classifier_rules_frozen": data.get("classifier_rules_frozen"),
                    "input_classes_frozen": data.get("input_classes_frozen"),
                    "baselines_predeclared": data.get("baselines_predeclared"),
                    "heldout_splits_frozen": data.get("heldout_splits_frozen"),
                    "analysis_no_translation_or_structure_input": data.get("analysis_no_translation_or_structure_input"),
                },
                "expected": "frozen protocol timestamp precedes external observation timestamp and all freeze flags are true",
            },
            {
                "name": "required_input_classes_present",
                "passed": REQUIRED_CLASSES.issubset(observed_classes),
                "actual": sorted(observed_classes),
                "expected": sorted(REQUIRED_CLASSES),
            },
            {
                "name": "classifier_frozen_and_geometry_only",
                "passed": data.get("classifier_id") == "orf_start_stop_window_eligibility" and data.get("classifier_rules_modified") is False,
                "actual": {
                    "classifier_id": data.get("classifier_id"),
                    "classifier_rules_modified": data.get("classifier_rules_modified"),
                },
                "expected": "frozen orf_start_stop_window_eligibility classifier with no rule modification",
            },
            {"name": "positive_interval_strong_binomial", **positive_interval_check(classified)},
            {"name": "matched_decoy_rejection_strong_binomial", **matched_decoy_check(classified)},
            {"name": "boundary_cases_not_promoted", **boundary_check(classified)},
            {"name": "heldout_split_stability", **heldout_split_check(classified)},
            {"name": "predeclared_baseline_pairwise_advantage", **baseline_pairwise_check(classified)},
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
                    "scope": "external_orf_interval_contact_only",
                    "source": data.get("source", ""),
                    "snapshot_date": data.get("snapshot_date", ""),
                    "row_count": len(classified),
                    "class_counts": {name: sum(1 for row in classified if row["class"] == name) for name in sorted(observed_classes)},
                    "stronger_statistic": "matched positive/decoy exact one-sided binomial tests, boundary non-promotion cap, held-out split stability, and paired baseline sign-test advantage",
                },
            }
        )
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    return emit(result)


if __name__ == "__main__":
    raise SystemExit(main())

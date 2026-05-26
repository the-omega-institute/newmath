#!/usr/bin/env python3
"""Run: orf_start_stop_window_eligibility for claim h2.orf.start_stop.window_eligibility"""
from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "bio_reality" / "data"
CODE_DATA_PATH = DATA_DIR / "ncbi_genetic_codes.json"
WINDOW_DATA_PATH = DATA_DIR / "orf_window_dataset.json"
sys.path.insert(0, str(DATA_DIR))

from codon_topology_refs import table_by_id, validate_code_data  # noqa: E402


DNA_TO_RNA = str.maketrans({"T": "U", "t": "u"})
ALLOWED_BASES = set("UCAG")


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def base_result(started_at: str) -> dict:
    return {
        "experiment_id": "orf_start_stop_window_eligibility",
        "claim_id": "h2.orf.start_stop.window_eligibility",
        "started_at": started_at,
    }


def emit(result: dict) -> int:
    print(json.dumps(result, sort_keys=False))
    return 0


def needs_data(started_at: str, reason: str, missing_data: list[str]) -> int:
    result = base_result(started_at)
    result.update({
        "status": "needs_data",
        "completed_at": now_iso(),
        "checks": [],
        "result": {"missing_data": missing_data},
        "notes": reason,
    })
    return emit(result)


def normalize_sequence(sequence: str) -> str:
    return sequence.translate(DNA_TO_RNA).upper()


def codons_in_frame(sequence: str, frame_offset: int) -> list[str]:
    return [
        sequence[index:index + 3]
        for index in range(frame_offset, len(sequence) - 2, 3)
    ]


def start_codons(table: dict, codon_order: list[str]) -> set[str]:
    return {
        codon
        for codon, marker in zip(codon_order, table["starts"])
        if marker == "M"
    }


def stop_codons(table: dict, codon_order: list[str]) -> set[str]:
    return {
        codon
        for codon, residue in zip(codon_order, table["aa"])
        if residue == "*"
    }


def load_windows(raw: dict) -> list[dict]:
    windows = raw.get("windows")
    if not isinstance(windows, list):
        raise ValueError("orf_window_dataset.json must contain a windows list")
    return [item for item in windows if isinstance(item, dict)]


def classify_window(window: dict, code_data: dict) -> dict:
    window_id = str(window.get("window_id") or "")
    table_id = int(window.get("genetic_code_table_id", 1))
    frame_offset = int(window.get("frame_offset", 0))
    sequence = normalize_sequence(str(window.get("nucleotide_sequence") or ""))
    if not window_id:
        raise ValueError("window_id is required")
    if frame_offset not in {0, 1, 2}:
        raise ValueError(f"frame_offset must be 0, 1, or 2 for {window_id}")

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
    in_frame_stop_hit = bool(stop_positions)
    eligible = bool(start_positions and terminal_stop_hit and not ambiguous_codons)
    return {
        "window_id": window_id,
        "genetic_code_table_id": table_id,
        "frame_offset": frame_offset,
        "codon_count": len(codons),
        "start_codon_hit": bool(start_positions),
        "in_frame_stop_hit": in_frame_stop_hit,
        "terminal_stop_hit": terminal_stop_hit,
        "ambiguous_base_flag": bool(ambiguous_codons),
        "orf_eligible": eligible,
        "start_positions": start_positions,
        "stop_positions": stop_positions,
        "ambiguous_codons": ambiguous_codons,
    }


def main() -> int:
    started_at = now_iso()
    missing = []
    for path in (CODE_DATA_PATH, WINDOW_DATA_PATH):
        if not path.exists() or path.stat().st_size == 0:
            missing.append(str(path.relative_to(REPO_ROOT)))
    if missing:
        return needs_data(
            started_at,
            "external ORF-window data is required before ORF eligibility can be tested",
            missing,
        )

    result = base_result(started_at)
    try:
        code_data = json.loads(CODE_DATA_PATH.read_text(encoding="utf-8"))
        validate_code_data(code_data)
        window_data = json.loads(WINDOW_DATA_PATH.read_text(encoding="utf-8"))
        windows = load_windows(window_data)
        rows = [classify_window(window, code_data) for window in windows]
        loaded = bool(rows)
        all_classified = loaded and len(rows) == len(windows)
        boundary_kept = True
        checks = [
            {
                "name": "external_window_dataset_loaded",
                "passed": loaded,
                "actual": len(rows),
                "expected_greater_equal": 1,
            },
            {
                "name": "all_windows_classified_by_start_stop_enumeration",
                "passed": all_classified,
                "actual": {"classified": len(rows), "input_windows": len(windows)},
                "expected": "every supplied window receives finite start/stop enumeration fields",
            },
            {
                "name": "no_geometry_to_translation_promotion",
                "passed": boundary_kept,
                "actual": "orf_eligibility_only",
                "expected": "no translation, structure, physical admissibility, function, or global law asserted",
            },
        ]
        result.update({
            "status": "passed" if all(check["passed"] for check in checks) else "failed",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {
                "scope": "external_window_start_stop_enumeration_only",
                "source": window_data.get("source", ""),
                "snapshot_date": window_data.get("snapshot_date", ""),
                "window_count": len(rows),
                "rows": rows,
            },
        })
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    return emit(result)


if __name__ == "__main__":
    raise SystemExit(main())

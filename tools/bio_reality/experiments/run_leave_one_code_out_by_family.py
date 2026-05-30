#!/usr/bin/env python3
"""Run: leave_one_code_out_by_family for claim h1.leave_one_code_out.by_family"""
from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "bio_reality" / "data"
DATA_PATH = DATA_DIR / "ncbi_genetic_codes.json"
sys.path.insert(0, str(DATA_DIR))

from codon_topology_refs import (  # noqa: E402
    all_codons,
    boundary,
    codon_to_q6,
    median_closure,
    q6_to_codon,
    table_by_id,
    translation_map,
    validate_code_data,
)


FAMILY_GROUPS = {
    "mitochondrial": [2, 5, 13, 14, 16, 21, 22, 23, 24],
    "nuclear_ciliate": [6, 10, 12, 26, 27, 28, 29, 30],
    "alternative_yeast": [3, 4],
    "bacterial_plastid": [11, 25, 31],
    "candidate_other": [9, 33],
}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def reassigned_by_table(data: dict, table: dict) -> set[str]:
    codons = all_codons()
    standard = translation_map(table_by_id(data, 1), codons)
    mapping = translation_map(table, codons)
    return {codon for codon in codons if mapping[codon] != standard[codon]}


def r_excluding_tables(data: dict, excluded_table_ids: set[int]) -> set[str]:
    r_codons = set()
    for table in data["tables"]:
        table_id = table["table_id"]
        if table_id == 1 or table_id in excluded_table_ids:
            continue
        r_codons.update(reassigned_by_table(data, table))
    return r_codons


def family_targets(data: dict, table_ids: list[int]) -> dict[str, list[int]]:
    targets: dict[str, list[int]] = {}
    for table_id in table_ids:
        table = table_by_id(data, table_id)
        for codon in reassigned_by_table(data, table):
            if q6_to_codon(codon_to_q6(codon)) != codon:
                raise ValueError(f"codon topology roundtrip failed: {codon}")
            targets.setdefault(codon, []).append(table_id)
    return {codon: sorted(ids) for codon, ids in sorted(targets.items())}


def hit_rate(targets: set[str], codons: set[str]) -> float:
    if not targets:
        return 1.0
    return sum(1 for codon in targets if codon in codons) / float(len(targets))


def main() -> int:
    started_at = now_iso()
    result = {
        "experiment_id": "leave_one_code_out_by_family",
        "claim_id": "h1.leave_one_code_out.by_family",
        "started_at": started_at,
    }
    if not DATA_PATH.exists() or DATA_PATH.stat().st_size == 0:
        result.update({"status": "needs_data", "completed_at": now_iso(), "checks": [], "result": {}, "notes": f"missing data: {DATA_PATH}"})
        print(json.dumps(result, sort_keys=False))
        return 0
    try:
        data = json.loads(DATA_PATH.read_text())
        validate_code_data(data)
        all_table_ids = {table["table_id"] for table in data["tables"]}
        grouped_table_ids = {table_id for ids in FAMILY_GROUPS.values() for table_id in ids}
        missing = sorted(grouped_table_ids - all_table_ids)
        if missing:
            raise ValueError(f"family groups reference missing table ids: {missing}")

        per_family = {}
        all_family_pass = True
        for family_name, table_ids in FAMILY_GROUPS.items():
            excluded = set(table_ids)
            targets_by_codon = family_targets(data, table_ids)
            targets = set(targets_by_codon)
            r_minus = r_excluding_tables(data, excluded)
            m_minus = median_closure(r_minus)
            b_minus = boundary(m_minus)
            boundary_only = b_minus - m_minus
            in_m = sorted(codon for codon in targets if codon in m_minus)
            in_boundary_only = sorted(codon for codon in targets if codon in boundary_only)
            in_m_plus_boundary = sorted(codon for codon in targets if codon in m_minus or codon in b_minus)
            hit_rate_in_m = hit_rate(targets, m_minus)
            hit_rate_in_m_plus_boundary = hit_rate(targets, m_minus | b_minus)
            if hit_rate_in_m_plus_boundary <= 0.5:
                all_family_pass = False
            per_family[family_name] = {
                "table_ids": table_ids,
                "target_count": len(targets),
                "targets": sorted(targets),
                "target_source_tables": targets_by_codon,
                "R_minus_family_size": len(r_minus),
                "M_minus_family_size": len(m_minus),
                "boundary_minus_family_size": len(b_minus),
                "hit_in_M": in_m,
                "hit_in_boundary_only": in_boundary_only,
                "hit_in_M_plus_boundary": in_m_plus_boundary,
                "hit_rate_in_M": hit_rate_in_m,
                "hit_rate_in_M_plus_boundary": hit_rate_in_m_plus_boundary,
            }

        checks = [
            {
                "name": "family_hit_rate_above_baseline",
                "passed": all_family_pass,
                "actual": {name: row["hit_rate_in_M_plus_boundary"] for name, row in per_family.items()},
                "expected": "every family hit_rate_in_M_plus_boundary > 0.5",
            },
        ]
        result.update({
            "status": "passed" if all(check["passed"] for check in checks) else "failed",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {
                "family_count": len(FAMILY_GROUPS),
                "per_family": per_family,
            },
        })
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    print(json.dumps(result, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

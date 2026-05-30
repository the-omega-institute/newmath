#!/usr/bin/env python3
"""Run: leave_one_code_out for claim h1.leave.one.code.out"""
from __future__ import annotations

import json
import random
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
    median_closure,
    table_by_id,
    translation_map,
    validate_code_data,
)


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def reassigned_by_table(data: dict, table: dict) -> set[str]:
    codons = data["codon_order"]
    standard = translation_map(table_by_id(data, 1), codons)
    mapping = translation_map(table, codons)
    return {codon for codon in codons if mapping[codon] != standard[codon]}


def r_excluding_table(data: dict, excluded_table_id: int) -> set[str]:
    r_codons = set()
    for table in data["tables"]:
        if table["table_id"] in (1, excluded_table_id):
            continue
        r_codons.update(reassigned_by_table(data, table))
    return r_codons


def hit_rate(targets: set[str], codons: set[str]) -> float:
    if not targets:
        return 1.0
    return sum(1 for codon in targets if codon in codons) / float(len(targets))


def baseline_hit_rate(codons: list[str], target_sizes: list[int], seed: int = 42, samples: int = 100) -> float:
    rng = random.Random(seed)
    rates = []
    for target_size in target_sizes:
        if target_size == 0:
            rates.append(1.0)
            continue
        per_target_rates = []
        for _ in range(samples):
            random_targets = set(rng.sample(codons, target_size))
            sample = set(rng.sample(codons, 13))
            per_target_rates.append(hit_rate(random_targets, sample))
        rates.append(sum(per_target_rates) / float(len(per_target_rates)))
    return sum(rates) / float(len(rates)) if rates else 0.0


def main() -> int:
    started_at = now_iso()
    result = {"experiment_id": "leave_one_code_out", "claim_id": "h1.leave.one.code.out", "started_at": started_at}
    if not DATA_PATH.exists() or DATA_PATH.stat().st_size == 0:
        result.update({"status": "needs_data", "completed_at": now_iso(), "checks": [], "result": {}, "notes": f"missing data: {DATA_PATH}"})
        print(json.dumps(result, sort_keys=False))
        return 0
    try:
        data = json.loads(DATA_PATH.read_text())
        validate_code_data(data)
        codons = all_codons()
        rows = []
        total_targets = 0
        total_in_m = 0
        total_in_boundary = 0
        target_sizes = []
        for table in data["tables"]:
            table_id = table["table_id"]
            if table_id == 1:
                continue
            targets = reassigned_by_table(data, table)
            if not targets:
                continue
            r_minus = r_excluding_table(data, table_id)
            m_minus = median_closure(r_minus)
            boundary_minus = boundary(m_minus)
            in_m = sorted(codon for codon in targets if codon in m_minus)
            in_boundary = sorted(codon for codon in targets if codon in boundary_minus)
            total_targets += len(targets)
            total_in_m += len(in_m)
            total_in_boundary += len(in_m) + len([codon for codon in in_boundary if codon not in m_minus])
            target_sizes.append(len(targets))
            rows.append({
                "table_id": table_id,
                "name": table["name"],
                "excluded_reassignments": sorted(targets),
                "M_minus_size": len(m_minus),
                "hit_in_M": in_m,
                "hit_in_boundary_only": sorted(codon for codon in in_boundary if codon not in m_minus),
            })
        observed_in_m = total_in_m / float(total_targets) if total_targets else 0.0
        observed_with_boundary = total_in_boundary / float(total_targets) if total_targets else 0.0
        baseline = baseline_hit_rate(codons, target_sizes)
        checks = [
            {"name": "hit_rate_above_baseline", "passed": observed_with_boundary > baseline + 0.10, "actual": observed_with_boundary, "baseline": baseline, "expected_margin": 0.10},
        ]
        result.update({
            "status": "passed" if all(check["passed"] for check in checks) else "failed",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {
                "tables_evaluated": len(rows),
                "total_targets": total_targets,
                "hit_rate_in_M_minus_T": observed_in_m,
                "hit_rate_in_M_minus_T_plus_boundary": observed_with_boundary,
                "baseline_hit_rate": baseline,
                "rows": rows,
            },
        })
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    print(json.dumps(result, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

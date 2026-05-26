#!/usr/bin/env python3
"""Run: leave_one_codon_out_module for claim h1.leave_one_codon_out.module_classification"""
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
    reassignment_set,
)


MODULES = {
    "stop_trp": {"UGA", "UAA", "UAG"},
    "ile_met": {"AUA"},
    "agr": {"AGA", "AGG"},
    "cun": {"CUA", "CUC", "CUG", "CUU"},
    "ar_lys": {"AAA"},
    "ssn": {"UCA", "UUA"},
}

CATEGORIES = ("predictable", "boundary", "anchor")


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def module_for_codon(codon: str) -> str | None:
    for module_name, codons in MODULES.items():
        if codon in codons:
            return module_name
    return None


def empty_module_rows() -> dict[str, dict[str, list[str]]]:
    return {module_name: {category: [] for category in CATEGORIES} for module_name in MODULES}


def classify_codon(codon: str, r_codons: set[str]) -> tuple[str, int, int]:
    r_minus = set(r_codons)
    r_minus.remove(codon)
    m_minus = median_closure(r_minus)
    b_minus = boundary(m_minus)
    if codon in m_minus:
        return "predictable", len(m_minus), len(b_minus)
    if codon in b_minus:
        return "boundary", len(m_minus), len(b_minus)
    return "anchor", len(m_minus), len(b_minus)


def main() -> int:
    started_at = now_iso()
    result = {
        "experiment_id": "leave_one_codon_out_module",
        "claim_id": "h1.leave_one_codon_out.module_classification",
        "started_at": started_at,
    }
    if not DATA_PATH.exists() or DATA_PATH.stat().st_size == 0:
        result.update({"status": "needs_data", "completed_at": now_iso(), "checks": [], "result": {}, "notes": f"missing data: {DATA_PATH}"})
        print(json.dumps(result, sort_keys=False))
        return 0
    try:
        codon_universe = set(all_codons())
        r_codons = reassignment_set(json.loads(DATA_PATH.read_text()))
        per_module = empty_module_rows()
        classification = {}
        rows = []
        assigned_codons = set()
        unassigned_codons = []

        for codon in sorted(r_codons):
            if codon not in codon_universe:
                raise ValueError(f"codon is outside codon universe: {codon}")
            if q6_to_codon(codon_to_q6(codon)) != codon:
                raise ValueError(f"codon topology roundtrip failed: {codon}")
            module_name = module_for_codon(codon)
            if module_name is None:
                unassigned_codons.append(codon)
                continue
            category, m_minus_size, boundary_minus_size = classify_codon(codon, r_codons)
            per_module[module_name][category].append(codon)
            classification[codon] = {"module": module_name, "category": category}
            assigned_codons.add(codon)
            rows.append({
                "codon": codon,
                "module": module_name,
                "category": category,
                "M_minus_size": m_minus_size,
                "boundary_minus_size": boundary_minus_size,
            })

        for module_rows in per_module.values():
            for category in CATEGORIES:
                module_rows[category].sort()

        module_catalog = set().union(*MODULES.values())
        missing_from_modules = sorted(r_codons - module_catalog)
        extra_module_codons = sorted(module_catalog - r_codons)
        complete = (
            len(r_codons) == 13
            and assigned_codons == r_codons
            and not unassigned_codons
            and not missing_from_modules
            and not extra_module_codons
            and all(
                sum(len(per_module[module_name][category]) for category in CATEGORIES) == len(MODULES[module_name])
                for module_name in MODULES
            )
        )
        every_module_has_recoverable = all(
            bool(per_module[module_name]["predictable"] or per_module[module_name]["boundary"])
            for module_name in MODULES
        )
        checks = [
            {
                "name": "module_classification_complete",
                "passed": complete,
                "actual": {
                    "R_size": len(r_codons),
                    "assigned_count": len(assigned_codons),
                    "unassigned_codons": unassigned_codons,
                    "missing_from_modules": missing_from_modules,
                    "extra_module_codons": extra_module_codons,
                },
                "expected": "all 13 R codons assigned to exactly one module and category",
            },
            {
                "name": "every_module_has_predictable_or_boundary",
                "passed": every_module_has_recoverable,
                "actual": {
                    module_name: sorted(per_module[module_name]["predictable"] + per_module[module_name]["boundary"])
                    for module_name in MODULES
                },
                "expected": "each module has at least one predictable or boundary codon",
            },
        ]
        result.update({
            "status": "passed" if all(check["passed"] for check in checks) else "failed",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {
                "R_codons": sorted(r_codons),
                "classification": classification,
                "per_module": per_module,
                "rows": rows,
            },
        })
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    print(json.dumps(result, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Run: check_f3_saturation for claim h0.f3.saturation"""
from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "bio_reality" / "data"
DATA_PATH = DATA_DIR / "ncbi_genetic_codes.json"
sys.path.insert(0, str(DATA_DIR))

from codon_topology_refs import median_closure, reassignment_set, wobble_partner  # noqa: E402


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def f3_saturation(codons: set[str]) -> set[str]:
    saturated = set(codons)
    changed = True
    while changed:
        changed = False
        for codon in list(saturated):
            partner = wobble_partner(codon)
            if partner not in saturated:
                saturated.add(partner)
                changed = True
    return saturated


def main() -> int:
    started_at = now_iso()
    result = {"experiment_id": "check_f3_saturation", "claim_id": "h0.f3.saturation", "started_at": started_at}
    if not DATA_PATH.exists() or DATA_PATH.stat().st_size == 0:
        result.update({"status": "needs_data", "completed_at": now_iso(), "checks": [], "result": {}, "notes": f"missing data: {DATA_PATH}"})
        print(json.dumps(result, sort_keys=False))
        return 0
    try:
        r_codons = reassignment_set(json.loads(DATA_PATH.read_text()))
        m_codons = median_closure(r_codons)
        boundary_failures = sorted(codon for codon in m_codons if wobble_partner(codon) not in m_codons)
        sat_r = f3_saturation(r_codons)
        m_without_gap_pair = m_codons - {"ACA", "ACG"}
        m_from_gap_seed = median_closure(r_codons | {"ACA"})
        checks = [
            {"name": "f3_boundary_is_zero", "passed": not boundary_failures, "actual": boundary_failures, "expected": []},
            {"name": "Sat_f3_R_equals_M_without_ACA_ACG", "passed": sat_r == m_without_gap_pair, "actual": sorted(sat_r), "expected": sorted(m_without_gap_pair)},
            {"name": "M_equals_Med_R_union_ACA", "passed": m_from_gap_seed == m_codons, "actual": sorted(m_from_gap_seed), "expected": sorted(m_codons)},
        ]
        result.update({
            "status": "passed" if all(check["passed"] for check in checks) else "failed",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {
                "M_codons": sorted(m_codons),
                "Sat_f3_R": sorted(sat_r),
                "gap_pair": ["ACA", "ACG"],
                "boundary_failures": boundary_failures,
            },
        })
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    print(json.dumps(result, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Run: check_M_equals_WNR_CUN for claim h0.M.equals.WNR.CUN"""
from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "bio_reality" / "data"
DATA_PATH = DATA_DIR / "ncbi_genetic_codes.json"
sys.path.insert(0, str(DATA_DIR))

from codon_topology_refs import median_closure, reassignment_set, wnr_union_cun  # noqa: E402


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def main() -> int:
    started_at = now_iso()
    result = {"experiment_id": "check_M_equals_WNR_CUN", "claim_id": "h0.M.equals.WNR.CUN", "started_at": started_at}
    if not DATA_PATH.exists() or DATA_PATH.stat().st_size == 0:
        result.update({"status": "needs_data", "completed_at": now_iso(), "checks": [], "result": {}, "notes": f"missing data: {DATA_PATH}"})
        print(json.dumps(result, sort_keys=False))
        return 0
    try:
        r_codons = reassignment_set(json.loads(DATA_PATH.read_text()))
        m_codons = median_closure(r_codons)
        expected = wnr_union_cun()
        checks = [
            {"name": "M_cardinality_equals_20", "passed": len(m_codons) == 20, "actual": len(m_codons), "expected": 20},
            {"name": "M_equals_WNR_union_CUN", "passed": m_codons == expected, "actual": sorted(m_codons), "expected": sorted(expected)},
        ]
        result.update({
            "status": "passed" if all(check["passed"] for check in checks) else "failed",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {"M_codons": sorted(m_codons), "size": len(m_codons), "R_codons": sorted(r_codons)},
        })
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    print(json.dumps(result, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

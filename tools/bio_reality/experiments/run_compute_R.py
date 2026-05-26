#!/usr/bin/env python3
"""Run: compute_R for claim h0.R.cardinality.13"""
from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "bio_reality" / "data"
DATA_PATH = DATA_DIR / "ncbi_genetic_codes.json"
sys.path.insert(0, str(DATA_DIR))

from codon_topology_refs import expected_r_set, reassignment_set  # noqa: E402


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def main() -> int:
    started_at = now_iso()
    result = {"experiment_id": "compute_R", "claim_id": "h0.R.cardinality.13", "started_at": started_at}
    if not DATA_PATH.exists() or DATA_PATH.stat().st_size == 0:
        result.update({"status": "needs_data", "completed_at": now_iso(), "checks": [], "result": {}, "notes": f"missing data: {DATA_PATH}"})
        print(json.dumps(result, sort_keys=False))
        return 0
    try:
        data = json.loads(DATA_PATH.read_text())
        r_codons = reassignment_set(data)
        expected = expected_r_set()
        checks = [
            {"name": "R_cardinality_equals_13", "passed": len(r_codons) == 13, "actual": len(r_codons), "expected": 13},
            {"name": "R_matches_expected_codons", "passed": r_codons == expected, "actual": sorted(r_codons), "expected": sorted(expected)},
        ]
        result.update({
            "status": "passed" if all(check["passed"] for check in checks) else "failed",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {"R_codons": sorted(r_codons), "size": len(r_codons)},
        })
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    print(json.dumps(result, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

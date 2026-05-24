#!/usr/bin/env python3
"""Run: check_motif_compression for claim h0.R.motif.compression"""
from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "bio_reality" / "data"
DATA_PATH = DATA_DIR / "ncbi_genetic_codes.json"
sys.path.insert(0, str(DATA_DIR))

from codon_topology_refs import motif_rhs, reassignment_set  # noqa: E402


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def main() -> int:
    started_at = now_iso()
    result = {"experiment_id": "check_motif_compression", "claim_id": "h0.R.motif.compression", "started_at": started_at}
    if not DATA_PATH.exists() or DATA_PATH.stat().st_size == 0:
        result.update({"status": "needs_data", "completed_at": now_iso(), "checks": [], "result": {}, "notes": f"missing data: {DATA_PATH}"})
        print(json.dumps(result, sort_keys=False))
        return 0
    try:
        r_codons = reassignment_set(json.loads(DATA_PATH.read_text()))
        rhs = motif_rhs()
        extra = rhs - r_codons
        missing = r_codons - rhs
        checks = [
            {"name": "R_equals_motif_union", "passed": r_codons == rhs, "actual": sorted(r_codons), "expected": sorted(rhs)},
            {"name": "no_extra", "passed": not extra, "actual": sorted(extra), "expected": []},
            {"name": "no_missing", "passed": not missing, "actual": sorted(missing), "expected": []},
        ]
        result.update({
            "status": "passed" if all(check["passed"] for check in checks) else "failed",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {"R_codons": sorted(r_codons), "motif_union": sorted(rhs), "extra": sorted(extra), "missing": sorted(missing)},
        })
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    print(json.dumps(result, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

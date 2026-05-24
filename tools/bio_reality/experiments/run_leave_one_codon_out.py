#!/usr/bin/env python3
"""Run: leave_one_codon_out for claim h1.leave.one.codon.out"""
from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "bio_reality" / "data"
DATA_PATH = DATA_DIR / "ncbi_genetic_codes.json"
sys.path.insert(0, str(DATA_DIR))

from codon_topology_refs import boundary, median_closure, reassignment_set  # noqa: E402


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def main() -> int:
    started_at = now_iso()
    result = {"experiment_id": "leave_one_codon_out", "claim_id": "h1.leave.one.codon.out", "started_at": started_at}
    if not DATA_PATH.exists() or DATA_PATH.stat().st_size == 0:
        result.update({"status": "needs_data", "completed_at": now_iso(), "checks": [], "result": {}, "notes": f"missing data: {DATA_PATH}"})
        print(json.dumps(result, sort_keys=False))
        return 0
    try:
        r_codons = reassignment_set(json.loads(DATA_PATH.read_text()))
        predictable = []
        boundary_only = []
        anchors = []
        classification = {}
        rows = []
        for codon in sorted(r_codons):
            r_minus = set(r_codons)
            r_minus.remove(codon)
            m_minus = median_closure(r_minus)
            b_minus = boundary(m_minus)
            if codon in m_minus:
                category = "predictable"
                predictable.append(codon)
            elif codon in b_minus:
                category = "boundary"
                boundary_only.append(codon)
            else:
                category = "anchor"
                anchors.append(codon)
            classification[codon] = category
            rows.append({"codon": codon, "category": category, "M_minus_size": len(m_minus)})
        predictable_count = len(predictable)
        boundary_count = len(boundary_only)
        anchor_count = len(anchors)
        recovery_rate = (predictable_count + boundary_count) / float(len(r_codons))
        checks = [
            {
                "name": "recovery_rate_above_threshold",
                "passed": recovery_rate >= 0.85,
                "actual": recovery_rate,
                "expected_greater_equal": 0.85,
            },
            {
                "name": "closure_coverage_high",
                "passed": predictable_count >= 5,
                "actual": predictable_count,
                "expected_greater_equal": 5,
            },
        ]
        result.update({
            "status": "passed" if all(check["passed"] for check in checks) else "failed",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {
                "predictable_count": predictable_count,
                "boundary_count": boundary_count,
                "anchor_count": anchor_count,
                "recovery_rate": recovery_rate,
                "classification": classification,
                "predictable": predictable,
                "boundary": boundary_only,
                "anchor": anchors,
                "structural_anchor": anchors,
                "rows": rows,
            },
        })
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    print(json.dumps(result, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

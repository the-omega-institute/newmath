#!/usr/bin/env python3
"""Run: check_quotient_geometry for claim h0.quotient.geometry"""
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
    codon_to_q6,
    cubical_f_vector,
    expected_projected_m,
    median_closure,
    projected_f_vector,
    q5_projection,
    q6_to_codon,
    reassignment_set,
)


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def lift_q5(q5: tuple[int, ...]) -> set[str]:
    return {q6_to_codon(q5 + (0,)), q6_to_codon(q5 + (1,))}


def main() -> int:
    started_at = now_iso()
    result = {"experiment_id": "check_quotient_geometry", "claim_id": "h0.quotient.geometry", "started_at": started_at}
    if not DATA_PATH.exists() or DATA_PATH.stat().st_size == 0:
        result.update({"status": "needs_data", "completed_at": now_iso(), "checks": [], "result": {}, "notes": f"missing data: {DATA_PATH}"})
        print(json.dumps(result, sort_keys=False))
        return 0
    try:
        r_codons = reassignment_set(json.loads(DATA_PATH.read_text()))
        m_codons = median_closure(r_codons)
        projected = {q5_projection(codon) for codon in m_codons}
        expected_projection = expected_projected_m()
        product_lift = set()
        for q5 in projected:
            product_lift.update(lift_q5(q5))
        product_failures = sorted(q6_to_codon(codon_to_q6(codon)) for codon in product_lift.symmetric_difference(m_codons))
        quotient_f = projected_f_vector(projected)[:4]
        m_f = cubical_f_vector(m_codons)[:5]
        checks = [
            {"name": "pi_M_matches_expected_quotient", "passed": projected == expected_projection, "actual": sorted(projected), "expected": sorted(expected_projection)},
            {"name": "M_is_product_decomposition", "passed": not product_failures, "actual": product_failures, "expected": []},
            {"name": "quotient_f_vector_matches", "passed": quotient_f == [10, 14, 6, 1], "actual": quotient_f, "expected": [10, 14, 6, 1]},
            {"name": "M_f_vector_matches", "passed": m_f == [20, 38, 26, 8, 1], "actual": m_f, "expected": [20, 38, 26, 8, 1]},
        ]
        result.update({
            "status": "passed" if all(check["passed"] for check in checks) else "failed",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {
                "pi_M_size": len(projected),
                "pi_M": [list(point) for point in sorted(projected)],
                "quotient_f_vector": quotient_f,
                "M_f_vector": m_f,
                "M_codons": sorted(m_codons),
            },
        })
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    print(json.dumps(result, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

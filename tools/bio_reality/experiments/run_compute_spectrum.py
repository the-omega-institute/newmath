#!/usr/bin/env python3
"""Run: compute_spectrum for claim h0.spectrum"""
from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "bio_reality" / "data"
DATA_PATH = DATA_DIR / "ncbi_genetic_codes.json"
sys.path.insert(0, str(DATA_DIR))

from codon_topology_refs import median_closure, reassignment_set, spectral_radius_killed_walk  # noqa: E402


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def radial_polynomial(mu: float) -> float:
    return mu ** 6 - 12.0 * (mu ** 4) + 26.0 * (mu ** 2) - 9.0


def main() -> int:
    started_at = now_iso()
    result = {"experiment_id": "compute_spectrum", "claim_id": "h0.spectrum", "started_at": started_at}
    if not DATA_PATH.exists() or DATA_PATH.stat().st_size == 0:
        result.update({"status": "needs_data", "completed_at": now_iso(), "checks": [], "result": {}, "notes": f"missing data: {DATA_PATH}"})
        print(json.dumps(result, sort_keys=False))
        return 0
    try:
        r_codons = reassignment_set(json.loads(DATA_PATH.read_text()))
        m_codons = median_closure(r_codons)
        lambda_m = spectral_radius_killed_walk(m_codons)
        lambda_r = spectral_radius_killed_walk(r_codons)
        mu = 6.0 * lambda_m - 1.0
        polynomial_value = radial_polynomial(mu)
        checks = [
            {"name": "spectral_radius_in_tolerance", "passed": abs(lambda_m - 0.675248) < 1e-4, "actual": lambda_m, "expected": 0.675248, "tolerance": 1e-4},
            {"name": "cubic_polynomial_satisfied", "passed": abs(polynomial_value) < 1e-3, "actual": polynomial_value, "expected_abs_less_than": 1e-3},
        ]
        result.update({
            "status": "passed" if all(check["passed"] for check in checks) else "failed",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {"lambda_M": lambda_m, "lambda_R": lambda_r, "mu": mu, "radial_polynomial_value": polynomial_value},
        })
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    print(json.dumps(result, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

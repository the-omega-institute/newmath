#!/usr/bin/env python3
"""Run: null_model_uniform for claim h0.null.model.significance"""
from __future__ import annotations

import argparse
import json
import random
from datetime import datetime, timezone
from pathlib import Path
import sys


REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "tools" / "bio_reality" / "data"
DATA_PATH = DATA_DIR / "ncbi_genetic_codes.json"
sys.path.insert(0, str(DATA_DIR))

from codon_topology_refs import all_codons, median, median_closure, reassignment_set  # noqa: E402


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=10000)
    parser.add_argument("--seed", type=int, default=42)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    started_at = now_iso()
    result = {"experiment_id": "null_model_uniform", "claim_id": "h0.null.model.significance", "started_at": started_at}
    if not DATA_PATH.exists() or DATA_PATH.stat().st_size == 0:
        result.update({"status": "needs_data", "completed_at": now_iso(), "checks": [], "result": {}, "notes": f"missing data: {DATA_PATH}"})
        print(json.dumps(result, sort_keys=False))
        return 0
    try:
        if args.samples <= 0:
            raise ValueError("--samples must be positive")
        codons = all_codons()
        observed_r = reassignment_set(json.loads(DATA_PATH.read_text()))
        observed_m_size = len(median_closure(observed_r))
        rng = random.Random(args.seed)
        closure_sizes = []
        ge_observed = 0
        for _ in range(args.samples):
            sample = set(rng.sample(codons, 13))
            size = len(median_closure(sample))
            closure_sizes.append(size)
            if size >= observed_m_size:
                ge_observed += 1
        p_value = ge_observed / float(args.samples)
        checks = [
            {"name": "p_value_significant", "passed": p_value < 0.01, "actual": p_value, "expected_less_than": 0.01},
        ]
        result.update({
            "status": "passed" if all(check["passed"] for check in checks) else "failed",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {
                "samples": args.samples,
                "seed": args.seed,
                "observed_M_size": observed_m_size,
                "min": min(closure_sizes),
                "max": max(closure_sizes),
                "median": median(closure_sizes),
                "p_value": p_value,
                "count_ge_observed": ge_observed,
            },
        })
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    print(json.dumps(result, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Run: null_model_uniform for claim h0.null.model.significance"""
from __future__ import annotations

import argparse
from collections import Counter
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
    parser.add_argument("--position-samples", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=42)
    return parser.parse_args()


def base_counts_by_position(codons: set[str]) -> list[dict[str, int]]:
    return [dict(Counter(codon[position] for codon in codons)) for position in range(3)]


def position_base_multisets(codons: set[str]) -> list[list[str]]:
    return [[codon[position] for codon in sorted(codons)] for position in range(3)]


def sample_position_preserving(multisets: list[list[str]], rng: random.Random) -> set[str] | None:
    shuffled = []
    for bases in multisets:
        position_bases = list(bases)
        rng.shuffle(position_bases)
        shuffled.append(position_bases)
    sample = {"".join(parts) for parts in zip(*shuffled)}
    if len(sample) != len(multisets[0]):
        return None
    return sample


def median_closure_size_summary(closure_sizes: list[int], le_observed: int, samples: int) -> dict:
    return {
        "N": samples,
        "min": min(closure_sizes),
        "max": max(closure_sizes),
        "median": median(closure_sizes),
        "count_le_observed": le_observed,
    }


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
        if args.position_samples <= 0:
            raise ValueError("--position-samples must be positive")
        codons = all_codons()
        observed_r = reassignment_set(json.loads(DATA_PATH.read_text()))
        observed_m_size = len(median_closure(observed_r))
        rng_uniform = random.Random(args.seed)
        uniform_closure_sizes = []
        uniform_le_observed = 0
        for _ in range(args.samples):
            sample = set(rng_uniform.sample(codons, 13))
            size = len(median_closure(sample))
            uniform_closure_sizes.append(size)
            if size <= observed_m_size:
                uniform_le_observed += 1
        p_uniform_lower_tail = uniform_le_observed / float(args.samples)

        rng_position = random.Random(args.seed)
        position_multisets = position_base_multisets(observed_r)
        position_closure_sizes = []
        position_le_observed = 0
        duplicate_retries = 0
        max_attempts = args.position_samples * 1000
        attempts = 0
        while len(position_closure_sizes) < args.position_samples:
            if attempts >= max_attempts:
                raise RuntimeError("could not draw enough distinct position-preserving samples")
            attempts += 1
            sample = sample_position_preserving(position_multisets, rng_position)
            if sample is None:
                duplicate_retries += 1
                continue
            size = len(median_closure(sample))
            position_closure_sizes.append(size)
            if size <= observed_m_size:
                position_le_observed += 1
        p_position_lower_tail = position_le_observed / float(args.position_samples)

        checks = [
            {
                "name": "p_value_uniform_lower_tail_significant",
                "passed": p_uniform_lower_tail < 0.01,
                "actual": p_uniform_lower_tail,
                "expected_less_than": 0.01,
            },
            {
                "name": "p_value_position_preserving_lower_tail_significant",
                "passed": p_position_lower_tail < 0.05,
                "actual": p_position_lower_tail,
                "expected_less_than": 0.05,
            },
        ]
        result.update({
            "status": "passed" if any(check["passed"] for check in checks) else "failed",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {
                "seed": args.seed,
                "observed_M_size": observed_m_size,
                "observed_position_base_counts": base_counts_by_position(observed_r),
                "tail_tested": "lower_tail_closure_size",
                "scope": "codon_window_geometry_only",
                "uniform_null": {
                    **median_closure_size_summary(uniform_closure_sizes, uniform_le_observed, args.samples),
                    "p_uniform_lower_tail": p_uniform_lower_tail,
                },
                "position_preserving_null": {
                    **median_closure_size_summary(position_closure_sizes, position_le_observed, args.position_samples),
                    "p_value_position_preserving_lower_tail": p_position_lower_tail,
                    "distinct_sample_attempts": attempts,
                    "duplicate_retries": duplicate_retries,
                },
            },
        })
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    print(json.dumps(result, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

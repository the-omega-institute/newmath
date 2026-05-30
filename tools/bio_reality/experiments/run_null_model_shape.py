#!/usr/bin/env python3
"""Run: null_model_shape for claim h0.M.shape.significance"""
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

from codon_topology_refs import median, median_closure, reassignment_set  # noqa: E402


# Phase 1 verified ground truth: Med(R) equals WNR union CUN exactly.
M_TRUE = tuple(sorted({
    "AAA",
    "AAG",
    "ACA",
    "ACG",
    "AGA",
    "AGG",
    "AUA",
    "AUG",
    "CUA",
    "CUC",
    "CUG",
    "CUU",
    "UAA",
    "UAG",
    "UCA",
    "UCG",
    "UGA",
    "UGG",
    "UUA",
    "UUG",
}))


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=42)
    return parser.parse_args()


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


def mean(values: list[float]) -> float:
    if not values:
        raise ValueError("mean of empty list")
    return sum(values) / float(len(values))


def p95(values: list[float]) -> float:
    if not values:
        raise ValueError("p95 of empty list")
    ordered = sorted(values)
    index = int(0.95 * (len(ordered) - 1))
    return float(ordered[index])


def distribution_summary(values: list[float]) -> dict:
    return {"mean": mean(values), "median": median(values), "p95": p95(values)}


def jaccard(left: set[str], right: set[str]) -> float:
    union = left | right
    if not union:
        return 1.0
    return len(left & right) / float(len(union))


def main() -> int:
    args = parse_args()
    started_at = now_iso()
    result = {"experiment_id": "null_model_shape", "claim_id": "h0.M.shape.significance", "started_at": started_at}
    if not DATA_PATH.exists() or DATA_PATH.stat().st_size == 0:
        result.update({"status": "needs_data", "completed_at": now_iso(), "checks": [], "result": {}, "notes": f"missing data: {DATA_PATH}"})
        print(json.dumps(result, sort_keys=False))
        return 0
    try:
        if args.samples <= 0:
            raise ValueError("--samples must be positive")

        m_true = set(M_TRUE)
        observed_r = reassignment_set(json.loads(DATA_PATH.read_text()))
        position_multisets = position_base_multisets(observed_r)
        rng = random.Random(args.seed)

        exact_shape_matches = 0
        high_jaccard_matches = 0
        jaccard_values = []
        size_diffs = []
        duplicate_retries = 0
        max_attempts = args.samples * 1000
        attempts = 0

        while len(jaccard_values) < args.samples:
            if attempts >= max_attempts:
                raise RuntimeError("could not draw enough distinct position-preserving samples")
            attempts += 1
            sample = sample_position_preserving(position_multisets, rng)
            if sample is None:
                duplicate_retries += 1
                continue

            m_sample = median_closure(sample)
            exact_shape_match = tuple(sorted(m_sample)) == M_TRUE
            jaccard_to_m_true = jaccard(m_sample, m_true)
            size_diff = abs(len(m_sample) - len(m_true))

            if exact_shape_match:
                exact_shape_matches += 1
            if jaccard_to_m_true >= 0.9:
                high_jaccard_matches += 1
            jaccard_values.append(jaccard_to_m_true)
            size_diffs.append(size_diff)

        p_exact = exact_shape_matches / float(args.samples)
        p_jaccard = high_jaccard_matches / float(args.samples)
        checks = [
            {"name": "p_value_exact_shape_significant", "passed": p_exact < 0.05, "actual": p_exact, "expected_less_than": 0.05},
            {
                "name": "p_value_high_jaccard_significant",
                "passed": p_jaccard < 0.05,
                "actual": p_jaccard,
                "expected_less_than": 0.05,
            },
        ]
        result.update({
            "status": "passed" if any(check["passed"] for check in checks) else "failed",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {
                "seed": args.seed,
                "N": args.samples,
                "M_true": list(M_TRUE),
                "observed_R_codons": sorted(observed_r),
                "p_exact": p_exact,
                "p_jaccard_ge_0.9": p_jaccard,
                "jaccard_distribution_summary": distribution_summary(jaccard_values),
                "size_diff_summary": distribution_summary(size_diffs),
                "exact_shape_matches": exact_shape_matches,
                "jaccard_ge_0.9_matches": high_jaccard_matches,
                "distinct_sample_attempts": attempts,
                "duplicate_retries": duplicate_retries,
            },
            "notes": (
                "Even if |Med(S)| >= 20 is generic under position-preserving null, "
                "the precise shape Med(S) == WNR union CUN is what carries the geometric content."
            ),
        })
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    print(json.dumps(result, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

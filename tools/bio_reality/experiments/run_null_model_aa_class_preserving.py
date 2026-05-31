#!/usr/bin/env python3
"""Run: null_model_aa_class_preserving for claim h0.null.model.aa_class_preserving"""
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

from codon_topology_refs import (  # noqa: E402
    all_codons,
    codon_to_q6,
    median,
    median_closure,
    q6_to_codon,
    reassignment_set,
    table_by_id,
    translation_map,
    validate_code_data,
)


AA_CLASS_ORDER = ("stop", "aromatic", "charged", "polar", "hydrophobic", "special")
AA_CLASS_BY_RESIDUE = {
    "*": "stop",
    "F": "aromatic",
    "W": "aromatic",
    "Y": "aromatic",
    "D": "charged",
    "E": "charged",
    "H": "charged",
    "K": "charged",
    "R": "charged",
    "C": "polar",
    "N": "polar",
    "Q": "polar",
    "S": "polar",
    "T": "polar",
    "A": "hydrophobic",
    "I": "hydrophobic",
    "L": "hydrophobic",
    "M": "hydrophobic",
    "V": "hydrophobic",
    "G": "special",
    "P": "special",
}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=42)
    return parser.parse_args()


def aa_class(aa: str) -> str:
    if aa not in AA_CLASS_BY_RESIDUE:
        raise ValueError(f"unclassified amino-acid label: {aa!r}")
    return AA_CLASS_BY_RESIDUE[aa]


def standard_labels(data: dict) -> dict[str, str]:
    codons = all_codons()
    standard = translation_map(table_by_id(data, 1), codons)
    for codon in codons:
        if q6_to_codon(codon_to_q6(codon)) != codon:
            raise ValueError(f"codon topology roundtrip failed: {codon}")
    return standard


def pools_by_class(standard: dict[str, str]) -> dict[str, list[str]]:
    pools = {name: [] for name in AA_CLASS_ORDER}
    for codon in all_codons():
        pools[aa_class(standard[codon])].append(codon)
    return {name: sorted(codons) for name, codons in pools.items()}


def sample_aa_class_preserving(
    pools: dict[str, list[str]],
    class_counts: dict[str, int],
    rng: random.Random,
) -> set[str]:
    sample = set()
    for class_name in AA_CLASS_ORDER:
        count = class_counts.get(class_name, 0)
        if count > len(pools[class_name]):
            raise ValueError(f"class {class_name!r} needs {count} codons, pool has {len(pools[class_name])}")
        sample.update(rng.sample(pools[class_name], count))
    return sample


def percentile(values: list[int], fraction: float) -> float:
    if not values:
        raise ValueError("percentile of empty list")
    ordered = sorted(values)
    index = int(fraction * (len(ordered) - 1))
    return float(ordered[index])


def size_summary(values: list[int]) -> dict:
    return {
        "min": min(values),
        "max": max(values),
        "median": median(values),
        "p5": percentile(values, 0.05),
        "p95": percentile(values, 0.95),
    }


def class_distribution(codons: set[str], standard: dict[str, str]) -> dict:
    rows = {}
    for class_name in AA_CLASS_ORDER:
        members = sorted(codon for codon in codons if aa_class(standard[codon]) == class_name)
        if members:
            rows[class_name] = {
                "count": len(members),
                "codons": members,
                "standard_aa_labels": {codon: standard[codon] for codon in members},
            }
    return rows


def main() -> int:
    args = parse_args()
    started_at = now_iso()
    result = {
        "experiment_id": "null_model_aa_class_preserving",
        "claim_id": "h0.null.model.aa_class_preserving",
        "started_at": started_at,
    }
    if not DATA_PATH.exists() or DATA_PATH.stat().st_size == 0:
        result.update({"status": "needs_data", "completed_at": now_iso(), "checks": [], "result": {}, "notes": f"missing data: {DATA_PATH}"})
        print(json.dumps(result, sort_keys=False))
        return 0
    try:
        if args.samples <= 0:
            raise ValueError("--samples must be positive")
        if args.samples > 5000:
            raise ValueError("--samples must not exceed 5000")

        data = json.loads(DATA_PATH.read_text())
        validate_code_data(data)
        standard = standard_labels(data)
        observed_r = reassignment_set(data)
        observed_m = median_closure(observed_r)
        observed_m_size = len(observed_m)
        distribution = class_distribution(observed_r, standard)
        class_counts = {class_name: distribution.get(class_name, {"count": 0})["count"] for class_name in AA_CLASS_ORDER}
        pools = pools_by_class(standard)
        rng = random.Random(args.seed)

        closure_sizes = []
        lower_tail_count = 0
        exact_match_count = 0
        for _ in range(args.samples):
            sample = sample_aa_class_preserving(pools, class_counts, rng)
            if len(sample) != len(observed_r):
                raise ValueError("sample cardinality does not match observed R")
            m_sample = median_closure(sample)
            closure_size = len(m_sample)
            closure_sizes.append(closure_size)
            if closure_size <= observed_m_size:
                lower_tail_count += 1
            if m_sample == observed_m:
                exact_match_count += 1

        p_lower_tail = lower_tail_count / float(args.samples)
        p_exact_shape = exact_match_count / float(args.samples)
        checks = [
            {
                "name": "p_value_aa_class_lower_tail_significant",
                "passed": p_lower_tail < 0.05,
                "actual": p_lower_tail,
                "expected_less_than": 0.05,
            },
            {
                "name": "p_value_aa_class_exact_shape_significant",
                "passed": p_exact_shape < 0.05,
                "actual": p_exact_shape,
                "expected_less_than": 0.05,
            },
        ]
        result.update({
            "status": "passed" if all(check["passed"] for check in checks) else "failed",
            "completed_at": now_iso(),
            "checks": checks,
            "result": {
                "seed": args.seed,
                "N": args.samples,
                "observed_R_codons": sorted(observed_r),
                "observed_M_size": observed_m_size,
                "observed_M_codons": sorted(observed_m),
                "aa_class_distribution_of_R": distribution,
                "sampled_size_distribution_summary": size_summary(closure_sizes),
                "lower_tail_count_le_observed_M_size": lower_tail_count,
                "p_value_aa_class_lower_tail": p_lower_tail,
                "exact_match_count": exact_match_count,
                "p_value_aa_class_exact_shape": p_exact_shape,
            },
        })
    except Exception as exc:
        result.update({"status": "error", "completed_at": now_iso(), "checks": [], "result": {}, "notes": str(exc)})
    print(json.dumps(result, sort_keys=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

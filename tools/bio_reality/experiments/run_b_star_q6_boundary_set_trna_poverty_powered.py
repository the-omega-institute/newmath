#!/usr/bin/env python3
"""Window6 boundary-set R tRNA-poverty mechanism test."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import sys
from typing import Any


SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from run_b_star_q6_translation_survival_powered import standard_code  # noqa: E402
from run_b_star_q6_trna_supply_increment_powered import (  # noqa: E402
    DOS_REIS_2004_WOBBLE_S,
    codon_w_values,
    records_from_gtrnadb_fasta_payload,
)


EXPERIMENT_ID = "b_star_q6_boundary_set_trna_poverty_powered"
CLAIM_ID = "h3.cross_layer_relation.boundary_set_trna_poverty.b_star_q6_window6_R_mechanism_powered"

DATA_DIR = pathlib.Path("tools/bio_reality/data")
GTRNADB_GLOB = "gtrnadb_trna_all_copy_*.json"
R_BOUNDARY_CODONS = [
    "AAA",
    "AGA",
    "AGG",
    "AUA",
    "CUA",
    "CUC",
    "CUG",
    "CUU",
    "UAA",
    "UAG",
    "UCA",
    "UGA",
    "UUA",
]
R_SENSE_CODONS = ["AAA", "AGA", "AGG", "AUA", "CUA", "CUC", "CUG", "CUU", "UCA", "UUA"]
R_STOP_CODONS = ["UAA", "UAG", "UGA"]

PERMUTATION_COUNT = 1000
MIN_COMPLETE_ORGANISMS = 5
SIGNIFICANCE_ALPHA = 0.05
EPS = 1e-12
SEED = f"sha256:{EXPERIMENT_ID}:R-sense-tRNA-poverty-permutation"


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def median(values: list[float]) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    middle = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[middle]
    return 0.5 * (ordered[middle - 1] + ordered[middle])


def stable_int(material: str) -> int:
    return int.from_bytes(hashlib.sha256(material.encode("utf-8")).digest()[:8], "big")


def deterministic_permutation(n: int, material: str) -> list[int]:
    out = list(range(n))
    for index in range(n - 1, 0, -1):
        swap = stable_int(f"{material}|index={index}|n={n}") % (index + 1)
        out[index], out[swap] = out[swap], out[index]
    return out


def exact_binomial_upper_tail(k: int, n: int, p: float = 0.5) -> float:
    if n <= 0:
        return 1.0
    return sum(math.comb(n, i) * (p ** i) * ((1.0 - p) ** (n - i)) for i in range(k, n + 1))


def exact_binomial_two_sided(k: int, n: int, p: float = 0.5) -> float:
    if n <= 0:
        return 1.0
    observed = math.comb(n, k) * (p ** k) * ((1.0 - p) ** (n - k))
    total = 0.0
    for i in range(n + 1):
        probability = math.comb(n, i) * (p ** i) * ((1.0 - p) ** (n - i))
        if probability <= observed + 1e-18:
            total += probability
    return min(1.0, total)


def validate_boundary_set(code: dict[str, str]) -> dict[str, object]:
    missing = [codon for codon in R_BOUNDARY_CODONS if codon not in code]
    stop_mismatch = [codon for codon in R_STOP_CODONS if code.get(codon) != "*"]
    sense_mismatch = [codon for codon in R_SENSE_CODONS if code.get(codon) == "*"]
    duplicate_count = len(R_BOUNDARY_CODONS) - len(set(R_BOUNDARY_CODONS))
    if missing or stop_mismatch or sense_mismatch or duplicate_count:
        raise ValueError(
            "invalid Window6 R definition: "
            f"missing={missing}, stop_mismatch={stop_mismatch}, "
            f"sense_mismatch={sense_mismatch}, duplicate_count={duplicate_count}"
        )
    return {
        "R_boundary_codons": R_BOUNDARY_CODONS,
        "R_sense_codons": R_SENSE_CODONS,
        "R_stop_codons": R_STOP_CODONS,
        "R_boundary_size": len(R_BOUNDARY_CODONS),
        "R_sense_size": len(R_SENSE_CODONS),
        "R_stop_size": len(R_STOP_CODONS),
    }


def direction_label(diff: float) -> str:
    if diff < -EPS:
        return "R_lower_tRNA_poor"
    if diff > EPS:
        return "R_higher_tRNA_rich"
    return "tie"


def compare_r_vs_nonr(
    *,
    organism: str,
    weights: dict[str, float],
    codons: list[str],
    r_codons: list[str],
    permutation_count: int,
) -> dict[str, object]:
    r_set = set(r_codons)
    nonr_codons = [codon for codon in codons if codon not in r_set]
    r_values = [weights[codon] for codon in r_codons]
    nonr_values = [weights[codon] for codon in nonr_codons]
    r_mean = mean(r_values)
    nonr_mean = mean(nonr_values)
    observed = r_mean - nonr_mean

    k = len(r_codons)
    null_diffs: list[float] = []
    for trial in range(permutation_count):
        permutation = deterministic_permutation(len(codons), f"{SEED}|{organism}|trial={trial}")
        selected = set(codons[index] for index in permutation[:k])
        selected_mean = mean([weights[codon] for codon in codons if codon in selected])
        complement_mean = mean([weights[codon] for codon in codons if codon not in selected])
        null_diffs.append(selected_mean - complement_mean)

    lower_tail = (1 + sum(1 for value in null_diffs if value <= observed + EPS)) / (permutation_count + 1)
    upper_tail = (1 + sum(1 for value in null_diffs if value >= observed - EPS)) / (permutation_count + 1)
    two_sided = (1 + sum(1 for value in null_diffs if abs(value) >= abs(observed) - EPS)) / (permutation_count + 1)

    return {
        "organism": organism,
        "status": "computed",
        "R_mean_w": r_mean,
        "nonR_mean_w": nonr_mean,
        "diff_R_minus_nonR": observed,
        "direction": direction_label(observed),
        "perm_p": lower_tail,
        "perm_p_lower_tail": lower_tail,
        "perm_p_upper_tail": upper_tail,
        "perm_p_two_sided": two_sided,
        "R_codon_w": {codon: weights[codon] for codon in r_codons},
        "R_codon_raw_W": None,
        "nonR_codon_count": len(nonr_codons),
        "sense_codon_count": len(codons),
        "null_summary": {
            "n": len(null_diffs),
            "mean": mean(null_diffs),
            "median": median(null_diffs),
            "min": min(null_diffs) if null_diffs else None,
            "max": max(null_diffs) if null_diffs else None,
        },
    }


def gtrnadb_paths(repo: pathlib.Path) -> list[pathlib.Path]:
    return sorted((repo / DATA_DIR).glob(GTRNADB_GLOB))


def organism_from_path(path: pathlib.Path) -> str:
    stem = path.stem
    prefix = "gtrnadb_trna_all_copy_"
    return stem[len(prefix) :] if stem.startswith(prefix) else stem


def compute_organism(repo: pathlib.Path, path: pathlib.Path, code: dict[str, str], codons: list[str]) -> dict[str, object]:
    organism = organism_from_path(path)
    try:
        payload = load_json(path)
        if not isinstance(payload, dict):
            raise ValueError("GtRNAdb payload must be a JSON object")
        records, source_summary = records_from_gtrnadb_fasta_payload(payload)
        weights, raw_w, _contributors = codon_w_values(code=code, codons=codons, records=records)
        if any(codon not in weights for codon in R_SENSE_CODONS):
            missing = [codon for codon in R_SENSE_CODONS if codon not in weights]
            raise ValueError(f"R sense codons missing weights: {missing}")
        if not all(math.isfinite(weights[codon]) and weights[codon] > 0.0 for codon in codons):
            raise ValueError("nonfinite or nonpositive normalized w value")

        row = compare_r_vs_nonr(
            organism=organism,
            weights=weights,
            codons=codons,
            r_codons=R_SENSE_CODONS,
            permutation_count=PERMUTATION_COUNT,
        )
        row["R_codon_raw_W"] = {codon: raw_w[codon] for codon in R_SENSE_CODONS}
        row["zero_raw_W_filled_by_geometric_mean_count"] = sum(1 for value in raw_w.values() if value == 0.0)
        row["trna_source_summary"] = {
            "path": str(path.relative_to(repo)),
            "source_kind": payload.get("source_kind"),
            "source_name": payload.get("source_name"),
            "source_url": payload.get("source_url"),
            "payload_sha256": payload.get("payload_sha256"),
            "organism_label": payload.get("organism_label"),
            "gtrnadb_domain": payload.get("gtrnadb_domain"),
            "gtrnadb_genome_id": payload.get("gtrnadb_genome_id"),
            "reported_total_trna_all_copies": payload.get("total_trna_all_copies"),
            "reported_trna_fasta_header_count": payload.get("trna_fasta_header_count"),
            "usable_tai_record_count": source_summary.get("usable_tai_record_count"),
            "skipped_trna_records": source_summary.get("skipped_trna_records"),
        }
        return row
    except Exception as exc:
        return {
            "organism": organism,
            "status": "skipped",
            "path": str(path.relative_to(repo)) if path.is_relative_to(repo) else str(path),
            "reason": f"{type(exc).__name__}: {exc}",
        }


def direction_summary(rows: list[dict[str, object]]) -> dict[str, object]:
    counts = {"R_lower_tRNA_poor": 0, "R_higher_tRNA_rich": 0, "tie": 0}
    organisms_by_direction = {"R_lower_tRNA_poor": [], "R_higher_tRNA_rich": [], "tie": []}
    for row in rows:
        direction = str(row.get("direction", "tie"))
        if direction not in counts:
            direction = "tie"
        counts[direction] += 1
        organisms_by_direction[direction].append(str(row.get("organism")))

    directional_n = counts["R_lower_tRNA_poor"] + counts["R_higher_tRNA_rich"]
    lower_count = counts["R_lower_tRNA_poor"]
    return {
        "n_computed": len(rows),
        "n_directional_non_tie": directional_n,
        "counts": counts,
        "organisms_by_direction": organisms_by_direction,
        "R_lower_fraction_all_computed": lower_count / len(rows) if rows else None,
        "R_lower_fraction_non_tie": lower_count / directional_n if directional_n else None,
        "majority_direction": max(counts, key=lambda key: (counts[key], key)) if rows else None,
        "majority_count": max(counts.values()) if rows else 0,
    }


def compact_per_organism(rows: list[dict[str, object]]) -> list[dict[str, object]]:
    compact: list[dict[str, object]] = []
    for row in rows:
        if row.get("status") != "computed":
            compact.append(row)
            continue
        compact.append(
            {
                "organism": row["organism"],
                "status": row["status"],
                "R_mean_w": row["R_mean_w"],
                "nonR_mean_w": row["nonR_mean_w"],
                "diff": row["diff_R_minus_nonR"],
                "perm_p": row["perm_p"],
                "perm_p_two_sided": row["perm_p_two_sided"],
                "direction": row["direction"],
            }
        )
    return sorted(compact, key=lambda item: str(item.get("organism")))


def main() -> None:
    repo = pathlib.Path.cwd()
    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        boundary_definition = validate_boundary_set(code)
        paths = gtrnadb_paths(repo)
        if not paths:
            emit(
                "needs_data",
                reason="no GtRNAdb tRNA copy JSON files found",
                expected_glob=str(DATA_DIR / GTRNADB_GLOB),
                checks={
                    "trna_weights_computed": {"passed": False},
                    "R_lower_than_nonR_sign_test": {"passed": False},
                    "cross_organism_consistency": {"passed": False},
                },
            )

        per_organism = [compute_organism(repo, path, code, codons) for path in paths]
        computed = [row for row in per_organism if row.get("status") == "computed"]
        skipped = [row for row in per_organism if row.get("status") != "computed"]
        n_computed = len(computed)
        diffs = [float(row["diff_R_minus_nonR"]) for row in computed]
        lower_count = sum(1 for diff in diffs if diff < -EPS)
        higher_count = sum(1 for diff in diffs if diff > EPS)
        tie_count = n_computed - lower_count - higher_count
        directional_n = lower_count + higher_count
        sign_p_lower = exact_binomial_upper_tail(lower_count, directional_n, 0.5) if directional_n else 1.0
        sign_p_two_sided = exact_binomial_two_sided(lower_count, directional_n, 0.5) if directional_n else 1.0
        mean_diff = mean(diffs)
        median_diff = median(diffs)
        pooled_R_mean = mean([float(row["R_mean_w"]) for row in computed])
        pooled_nonR_mean = mean([float(row["nonR_mean_w"]) for row in computed])
        pooled_diff = pooled_R_mean - pooled_nonR_mean
        directions = direction_summary(computed)

        enough_data = n_computed >= MIN_COMPLETE_ORGANISMS and directional_n >= MIN_COMPLETE_ORGANISMS
        sign_test_passed = enough_data and lower_count > higher_count and sign_p_lower < SIGNIFICANCE_ALPHA
        effect_direction_passed = enough_data and mean_diff < -EPS and median_diff < -EPS and pooled_diff < -EPS
        consistency_passed = enough_data and lower_count > (directional_n / 2.0) and effect_direction_passed
        passed = sign_test_passed and consistency_passed
        status = "needs_data" if not enough_data else ("passed" if passed else "failed")

        checks = {
            "trna_weights_computed": {
                "passed": enough_data,
                "organisms_computed": n_computed,
                "organisms_skipped": len(skipped),
                "minimum_complete_organisms": MIN_COMPLETE_ORGANISMS,
                "sense_codon_count": len(codons),
                "R_sense_codon_count": len(R_SENSE_CODONS),
                "data_policy": "all local tools/bio_reality/data/gtrnadb_trna_all_copy_*.json payloads are attempted; malformed or unavailable payloads are skipped with reasons",
            },
            "R_lower_than_nonR_sign_test": {
                "passed": sign_test_passed,
                "lower_count": lower_count,
                "higher_count": higher_count,
                "tie_count": tie_count,
                "n_directional_non_tie": directional_n,
                "binomial_p_one_sided_lower": sign_p_lower,
                "binomial_p_two_sided": sign_p_two_sided,
                "alpha": SIGNIFICANCE_ALPHA,
                "rule": "one-sided exact sign test over organisms with nonzero diff; H1 is R_mean_w < nonR_mean_w",
            },
            "cross_organism_consistency": {
                "passed": consistency_passed,
                "mean_diff_R_minus_nonR": mean_diff,
                "median_diff_R_minus_nonR": median_diff,
                "pooled_mean_R_w": pooled_R_mean,
                "pooled_mean_nonR_w": pooled_nonR_mean,
                "pooled_diff_R_minus_nonR": pooled_diff,
                "direction_summary": directions,
                "rule": "directional majority lower and mean, median, and pooled mean effects all negative",
            },
        }

        if status == "passed":
            mechanism_call = "R sense codons are systematically tRNA-poor under GtRNAdb tGCN plus dos Reis wobble weights; this supports a tRNA-supply mechanism for R avoidance."
            reason = None
        elif status == "failed":
            mechanism_call = "R sense codons are not systematically tRNA-poor under this GtRNAdb tGCN plus dos Reis wobble test."
            reason = "R_lower_than_nonR_sign_test and/or cross_organism_consistency did not pass"
        else:
            mechanism_call = "needs_data"
            reason = f"computed organisms n={n_computed}, directional non-tie n={directional_n}, minimum={MIN_COMPLETE_ORGANISMS}"

        emit(
            status,
            reason=reason,
            seed=SEED,
            permutation_count=PERMUTATION_COUNT,
            alpha=SIGNIFICANCE_ALPHA,
            boundary_definition=boundary_definition,
            organisms_requested=len(paths),
            organisms_computed=n_computed,
            organisms_skipped=len(skipped),
            sign_test={
                "lower_count": lower_count,
                "higher_count": higher_count,
                "tie_count": tie_count,
                "n_directional_non_tie": directional_n,
                "binomial_p_one_sided_lower": sign_p_lower,
                "binomial_p_two_sided": sign_p_two_sided,
            },
            combined_effect={
                "mean_diff_R_minus_nonR": mean_diff,
                "median_diff_R_minus_nonR": median_diff,
                "pooled_mean_R_w": pooled_R_mean,
                "pooled_mean_nonR_w": pooled_nonR_mean,
                "pooled_diff_R_minus_nonR": pooled_diff,
            },
            mechanism_call=mechanism_call,
            method={
                "weight": "Route C dos Reis tAI codon weights: W_codon=sum_same-aa_isoacceptors (1-s_wobble)*tGCN over compatible anticodons; w_codon=W_codon/max(W); zero W filled by geometric mean of nonzero normalized W",
                "wobble_s_values": {f"{left}:{right}": value for (left, right), value in DOS_REIS_2004_WOBBLE_S.items()},
                "canonical_watson_crick_s": 0.0,
                "anticodon_A_treated_as_inosine": True,
                "initiator_iMet_excluded_from_elongator_tai": True,
                "per_organism_statistic": "mean(w for 10 fixed R-sense codons) - mean(w for all non-R sense codons)",
                "per_organism_null": "deterministic SHA256-seeded same-size random codon subsets of all 61 standard sense codons",
                "cross_organism_gate": "exact one-sided sign test plus negative mean, median, and pooled effects",
            },
            cross_organism_consistency=directions,
            per_organism=compact_per_organism(per_organism),
            checks=checks,
            cannot_claim=[
                "tRNA gene copy number is a proxy for tRNA supply, not direct mature tRNA abundance or charging",
                "dos Reis wobble penalties and GtRNAdb gene models are modeling choices reused from Route C",
                "the test is codon-level and does not prove that tRNA scarcity causally drives R avoidance in expression data",
                "there is no phylogenetic comparative correction, so cross-organism sign counts are descriptive rather than independent evolutionary replicates",
                "a failed call would mean this tRNA-poverty mechanism did not clear the specified gates, not that R avoidance has no mechanism",
            ],
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit(
            "needs_data",
            reason=f"{type(exc).__name__}: {exc}",
            checks={
                "trna_weights_computed": {"passed": False},
                "R_lower_than_nonR_sign_test": {"passed": False},
                "cross_organism_consistency": {"passed": False},
            },
        )


if __name__ == "__main__":
    main()

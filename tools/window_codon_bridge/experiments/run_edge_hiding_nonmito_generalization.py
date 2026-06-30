#!/usr/bin/env python3
"""Support-gated non-mitochondrial reassignment edge-hiding stress test."""
from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import random
import sys
from typing import Any


EXPERIMENT_ID = "edge_hiding_nonmito_generalization"
CLAIM_ID = "bridge.genetic_code.edge_hiding_nonmito_generalization"
ALPHA = 0.01
COMBINED_MONTE_CARLO_DRAWS = 200000
COMBINED_SEED = "edge_hiding_nonmito_generalization.cluster_product"
STOP = "*"

EXPERIMENT_DIR = Path(__file__).resolve().parent
PROBE_PATH = EXPERIMENT_DIR / "_edgehide_nonmito_fetch_probe.py"
ALT_PATH = EXPERIMENT_DIR / "run_edge_hiding_alternative_code_reassignment.py"


def load_module(path: Path, name: str) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PROBE = load_module(PROBE_PATH, "_edgehide_nonmito_fetch_probe")
ALT = load_module(ALT_PATH, "_edgehide_alt_reassign")


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    if status in {"certified", "coincidence"}:
        sys.exit(0)
    if status == "refuted":
        sys.exit(2)
    sys.exit(3)


def stable_seed(text: str) -> int:
    return int.from_bytes(hashlib.sha256(text.encode("utf-8")).digest()[:16], "big")


def round_float(value: float | None, digits: int = 12) -> float | None:
    if value is None:
        return None
    if not math.isfinite(value):
        return value
    rounded = round(value, digits)
    return 0.0 if rounded == -0.0 else rounded


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def median(values: list[float]) -> float:
    ordered = sorted(values)
    n = len(ordered)
    mid = n // 2
    if n % 2:
        return float(ordered[mid])
    return (float(ordered[mid - 1]) + float(ordered[mid])) / 2.0


def dna(codon: str) -> str:
    return codon.upper().replace("U", "T")


def apply_updates(standard: list[str], codon_to_index: dict[str, int], updates: dict[str, str]) -> list[str]:
    labels = standard[:]
    for codon, target in updates.items():
        labels[codon_to_index[dna(codon)]] = target
    return labels


def event_result(
    event: dict[str, object],
    standard: list[str],
    codon_to_index: dict[str, int],
    edges: list[tuple[int, int]],
    baseline_h: int,
) -> dict[str, object]:
    observed_updates = {dna(codon): str(target) for codon, target in dict(event["reassignments"]).items()}
    observed_labels = apply_updates(standard, codon_to_index, observed_updates)
    observed_h = int(ALT.edge_count(observed_labels, edges, sense_only=True))
    observed_delta = observed_h - baseline_h
    target_counts = Counter(observed_updates.values())
    candidate_deltas: list[int] = []
    candidate_records: list[dict[str, object]] = []
    for candidate_codons_raw in event["matched_support"]["candidate_codons"]:  # type: ignore[index]
        candidate_codons = [dna(str(codon)) for codon in candidate_codons_raw]
        if len(candidate_codons) != sum(target_counts.values()):
            continue
        updates: dict[str, str] = {}
        cursor = 0
        for target, count in sorted(target_counts.items()):
            for codon in sorted(candidate_codons)[cursor : cursor + count]:
                updates[codon] = target
            cursor += count
        labels = apply_updates(standard, codon_to_index, updates)
        delta = int(ALT.edge_count(labels, edges, sense_only=True)) - baseline_h
        candidate_deltas.append(delta)
        candidate_records.append({"codons": sorted(candidate_codons), "delta_H_sense": delta})
    if not candidate_deltas:
        raise ValueError(f"{event['event_id']} has no matched candidate deltas")
    median_delta = median([float(value) for value in candidate_deltas])
    centered = [float(value) - median_delta for value in candidate_deltas]
    observed_centered = float(observed_delta) - median_delta
    p_upper = sum(value >= observed_delta for value in candidate_deltas) / len(candidate_deltas)
    observed_set = sorted(observed_updates)
    return {
        "event_id": event["event_id"],
        "cluster_key": event["cluster_key"],
        "reassigned_codons": event["reassigned_codons"],
        "transition_matrix": event["transition_matrix"],
        "n_reassigned_rows": event["n_reassigned_rows"],
        "n_outgroup_rows": event["n_outgroup_rows"],
        "outgroup_usage_available": event["outgroup_usage_available"],
        "genomic_gc": event["genomic_gc"],
        "transition_support_size": event["transition_support_size"],
        "matched_support": event["matched_support"]["matched_support"],  # type: ignore[index]
        "matched_rule": event["matched_support"]["rule"],  # type: ignore[index]
        "matched_low_support": event["matched_support"]["low_support"],  # type: ignore[index]
        "matched_nondegenerate": event["matched_support"]["nondegenerate"],  # type: ignore[index]
        "availability_signature": event["matched_support"]["observed_signature"],  # type: ignore[index]
        "observed_delta_H_sense": observed_delta,
        "null_delta_H_sense_median": round_float(median_delta),
        "D": round_float(observed_centered),
        "p_upper_event_descriptive": round_float(p_upper),
        "distinct_null_delta_H_sense": sorted(set(candidate_deltas)),
        "candidate_delta_H_sense": candidate_deltas,
        "candidate_records": candidate_records,
        "_centered_null": centered,
        "_observed_centered": observed_centered,
        "observed_in_matched_stratum": any(record["codons"] == observed_set for record in candidate_records),
    }


def product_tail(
    distributions: list[list[float]],
    observed: float,
    seed_text: str,
    draws: int,
) -> dict[str, object]:
    product_size = 1
    for values in distributions:
        product_size *= len(values)
    hits = 0
    total = 0
    if product_size <= 500000:
        def rec(pos: int, acc: float) -> None:
            nonlocal hits, total
            if pos == len(distributions):
                total += 1
                if acc / len(distributions) >= observed:
                    hits += 1
                return
            for value in distributions[pos]:
                rec(pos + 1, acc + float(value))

        rec(0, 0.0)
        method = "exact_product"
    else:
        rng = random.Random(stable_seed(seed_text))
        total = draws
        for _draw in range(draws):
            sampled = sum(float(rng.choice(values)) for values in distributions) / len(distributions)
            if sampled >= observed:
                hits += 1
        method = "monte_carlo_product"
    return {
        "p_upper": hits / total if total else math.nan,
        "hits": hits,
        "total": total,
        "product_size": product_size,
        "method": method,
    }


def product_mean_distribution(distributions: list[list[float]]) -> list[float]:
    values: list[float] = []

    def rec(pos: int, acc: float) -> None:
        if pos == len(distributions):
            values.append(acc / len(distributions))
            return
        for value in distributions[pos]:
            rec(pos + 1, acc + float(value))

    rec(0, 0.0)
    return values


def cluster_results(events: list[dict[str, object]]) -> list[dict[str, object]]:
    grouped: dict[str, list[dict[str, object]]] = defaultdict(list)
    for event in events:
        grouped[str(event["cluster_key"])].append(event)
    out: list[dict[str, object]] = []
    for key, items in sorted(grouped.items()):
        observed = mean([float(item["_observed_centered"]) for item in items])
        distributions = [list(item["_centered_null"]) for item in items]  # type: ignore[arg-type]
        tail = product_tail(
            distributions,
            observed,
            f"{COMBINED_SEED}.cluster.{key}",
            COMBINED_MONTE_CARLO_DRAWS,
        )
        codon_sets = sorted({",".join(str(codon) for codon in item["reassigned_codons"]) for item in items})
        out.append(
            {
                "cluster_key": key,
                "size": len(items),
                "event_ids": [item["event_id"] for item in items],
                "observed_codon_sets": codon_sets,
                "D": round_float(observed),
                "p_upper_cluster_descriptive": round_float(float(tail["p_upper"])),
                "cluster_product_method": tail["method"],
                "cluster_product_support": tail["product_size"],
                "event_D_values": [item["D"] for item in items],
                "support_min": min(int(item["matched_support"]) for item in items),
                "support_max": max(int(item["matched_support"]) for item in items),
                "all_strata_low_support": all(bool(item["matched_low_support"]) for item in items),
            }
        )
    return out


def compact_event(event: dict[str, object]) -> dict[str, object]:
    return {
        "event_id": event["event_id"],
        "cluster_key": event["cluster_key"],
        "reassigned_codons": event["reassigned_codons"],
        "transition_matrix": event["transition_matrix"],
        "n_reassigned_rows": event["n_reassigned_rows"],
        "n_outgroup_rows": event["n_outgroup_rows"],
        "outgroup_usage_available": event["outgroup_usage_available"],
        "genomic_gc": event["genomic_gc"],
        "transition_support_size": event["transition_support_size"],
        "matched_support": event["matched_support"],
        "matched_rule": event["matched_rule"],
        "matched_low_support": event["matched_low_support"],
        "matched_nondegenerate": event["matched_nondegenerate"],
        "availability_signature": event["availability_signature"],
        "observed_delta_H_sense": event["observed_delta_H_sense"],
        "null_delta_H_sense_median": event["null_delta_H_sense_median"],
        "D": event["D"],
        "p_upper_event_descriptive": event["p_upper_event_descriptive"],
        "distinct_null_delta_H_sense": event["distinct_null_delta_H_sense"],
        "observed_in_matched_stratum": event["observed_in_matched_stratum"],
    }


def main() -> None:
    try:
        panel = PROBE.build_panel(force_refresh=True)
    except Exception as exc:
        emit(
            "needs_external",
            reason=f"fetch/support probe failed: {type(exc).__name__}:{exc}",
            probe={},
            note=(
                "descriptive-underpowered: the five-event non-mitochondrial stress test could "
                "not reach the data/support audit."
            ),
        )
    if panel.get("status") != "ok":
        emit(
            "needs_external",
            reason=str(panel.get("reason") or "support audit failed"),
            probe={
                "n_usable_events": panel.get("n_usable_events"),
                "independent_cluster_count": panel.get("independent_cluster_count"),
                "support_gate": panel.get("support_gate"),
                "events": panel.get("events"),
            },
            note=(
                "descriptive-underpowered: support gate did not pass for the scoped five-event "
                "non-mitochondrial panel; no certification is claimed."
            ),
        )
    support_gate = dict(panel["support_gate"])
    if not support_gate.get("passed"):
        emit(
            "needs_external",
            reason="support gate failed before certification test",
            probe={
                "n_usable_events": panel.get("n_usable_events"),
                "independent_cluster_count": panel.get("independent_cluster_count"),
                "support_gate": support_gate,
            },
            note=(
                "descriptive-underpowered: independent clusters or exact matched-null support "
                "were insufficient; no certification is claimed."
            ),
        )

    codons = list(panel["codon_order"])
    standard = list(panel["standard_labels"])
    codon_to_index = {codon: idx for idx, codon in enumerate(codons)}
    edges = ALT.hamming1_edges(codons)
    baseline_h = int(ALT.edge_count(standard, edges, sense_only=True))
    event_items = [
        event_result(event, standard, codon_to_index, edges, baseline_h)
        for event in panel["events"]
        if event.get("usable")
    ]
    clusters = cluster_results(event_items)
    K = len(clusters)
    T = mean([float(cluster["D"]) for cluster in clusters])
    by_cluster = {
        key: [item for item in event_items if str(item["cluster_key"]) == key]
        for key in sorted({str(item["cluster_key"]) for item in event_items})
    }
    cluster_null_distributions = [
        product_mean_distribution([list(item["_centered_null"]) for item in items])
        for _key, items in sorted(by_cluster.items())
    ]
    cluster_tail = product_tail(
        cluster_null_distributions,
        T,
        f"{COMBINED_SEED}.clusters",
        COMBINED_MONTE_CARLO_DRAWS,
    )
    combined_p = float(cluster_tail["p_upper"])
    direction_consistent = all(float(cluster["D"]) > 0.0 for cluster in clusters)
    non_cgg_trp_clusters = [cluster for cluster in clusters if str(cluster["cluster_key"]) != "R>W:1"]
    not_single_cgg_trp_driven = bool(non_cgg_trp_clusters) and mean([float(cluster["D"]) for cluster in non_cgg_trp_clusters]) > 0.0
    all_low_support = all(bool(event["matched_low_support"]) for event in event_items)
    if K < 3 or any(not bool(event["matched_nondegenerate"]) for event in event_items):
        status = "needs_external"
        reason = "support gate failed after event reconstruction"
    elif T > 0.0 and combined_p <= ALPHA and direction_consistent and not_single_cgg_trp_driven:
        status = "certified"
        reason = "support-gated exact-permutation evidence clears the scoped fragile threshold"
    elif T <= 0.0:
        status = "refuted"
        reason = "natural reassignment identities are not more synonymous-edge-preserving than the matched null"
    else:
        status = "coincidence"
        reason = "availability/GC matched null removes or weakens the edge-hiding preference below the certification threshold"
    if status == "certified" and all_low_support:
        reason = (
            reason
            + "; every matched stratum is low-support, so the certification is fragile and scoped"
        )
    note = (
        f"Support-gated non-mitochondrial edge-hiding stress test scoped to ~5 real events "
        f"and {K} independent transition clusters; all inference is fragile/low-power "
        f"exact-permutation evidence, not causal, and not a Window6 repetition."
    )
    emit(
        status,
        reason=reason,
        source_repo=panel.get("source_repo"),
        cache_path=str(PROBE.CACHE_PATH),
        n_events=len(event_items),
        K=K,
        support_gate=support_gate,
        standard_H_sense=baseline_h,
        T=round_float(T),
        cluster_combined_p=round_float(combined_p),
        combined_p_method=cluster_tail["method"],
        combined_product_support=cluster_tail["product_size"],
        direction_consistent=direction_consistent,
        cgg_trp_cluster_merged=True,
        not_single_cgg_trp_driven=not_single_cgg_trp_driven,
        all_matched_strata_low_support=all_low_support,
        clusters=clusters,
        events=[compact_event(event) for event in event_items],
        verdict_note=note,
    )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Matched reassignment test for alternative genetic-code edge hiding."""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import combinations
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import random
import sys
from typing import Any


EXPERIMENT_ID = "edge_hiding_alternative_code_reassignment"
CLAIM_ID = "bridge.genetic_code.edge_hiding_alternative_code_reassignment"
EXACT_ENUMERATION_LIMIT = 200000
MONTE_CARLO_DRAWS = 20000
CLUSTER_MONTE_CARLO_DRAWS = 20000
NULL_SEED_PREFIX = "edge_hiding_alternative_code_reassignment.transition_matrix"
CLUSTER_SEED_PREFIX = "edge_hiding_alternative_code_reassignment.cluster_tail"
ALPHA = 0.01
BASES = ("T", "C", "A", "G")
STOP = "*"

EXPERIMENT_DIR = Path(__file__).resolve().parent
PROBE_PATH = EXPERIMENT_DIR / "_edgehide_reassign_fetch_probe.py"


def load_probe_module() -> Any:
    spec = importlib.util.spec_from_file_location("_edgehide_reassign_fetch_probe", PROBE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load _edgehide_reassign_fetch_probe.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


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


def variance(values: list[float]) -> float:
    if len(values) < 2:
        return 0.0
    center = mean(values)
    return sum((value - center) * (value - center) for value in values) / (len(values) - 1)


def normal_sf(z: float) -> float:
    return 0.5 * math.erfc(z / math.sqrt(2.0))


def p_to_z_upper(p: float) -> float:
    lo, hi = -10.0, 10.0
    target = min(max(p, 1.0e-300), 1.0 - 1.0e-16)
    for _ in range(90):
        mid = (lo + hi) / 2.0
        if normal_sf(mid) > target:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2.0


def chi_square_sf_wilson_hilferty(x: float, df: int) -> float:
    if df <= 0:
        return math.nan
    if x <= 0:
        return 1.0
    z = ((x / df) ** (1.0 / 3.0) - (1.0 - 2.0 / (9.0 * df))) / math.sqrt(2.0 / (9.0 * df))
    return normal_sf(z)


def fisher_upper_p(p_values: list[float]) -> float:
    if not p_values:
        return math.nan
    statistic = -2.0 * sum(math.log(max(p, 1.0e-300)) for p in p_values)
    return chi_square_sf_wilson_hilferty(statistic, 2 * len(p_values))


def stouffer_upper_p(p_values: list[float]) -> float:
    if not p_values:
        return math.nan
    z = sum(p_to_z_upper(p) for p in p_values) / math.sqrt(len(p_values))
    return normal_sf(z)


def hamming1_edges(codons: list[str]) -> list[tuple[int, int]]:
    index = {codon: idx for idx, codon in enumerate(codons)}
    edges: list[tuple[int, int]] = []
    for codon in codons:
        left = index[codon]
        for pos in range(3):
            for base in BASES:
                if base == codon[pos]:
                    continue
                other = codon[:pos] + base + codon[pos + 1 :]
                right = index[other]
                if left < right:
                    edges.append((left, right))
    return edges


def edge_count(labels: list[str], edges: list[tuple[int, int]], sense_only: bool) -> int:
    total = 0
    for left, right in edges:
        label = labels[left]
        if label == labels[right] and (not sense_only or label != STOP):
            total += 1
    return total


def multinomial_count(total: int, counts: list[int]) -> int:
    out = math.factorial(total)
    for count in counts:
        out //= math.factorial(count)
    return out


def assignment_options(indices: list[int], target_counts: list[tuple[str, int]]) -> list[dict[int, str]]:
    labels: list[str] = []
    for target, count in target_counts:
        labels.extend([target] * count)
    if not labels:
        return [{}]
    options: list[dict[int, str]] = []

    def rec(remaining: tuple[int, ...], pos: int, assigned: dict[int, str]) -> None:
        if pos == len(target_counts):
            options.append(dict(assigned))
            return
        target, count = target_counts[pos]
        for chosen in combinations(remaining, count):
            next_assigned = dict(assigned)
            for index in chosen:
                next_assigned[index] = target
            chosen_set = set(chosen)
            next_remaining = tuple(index for index in remaining if index not in chosen_set)
            rec(next_remaining, pos + 1, next_assigned)

    rec(tuple(indices), 0, {})
    return options


def random_assignment(
    indices: list[int],
    target_counts: list[tuple[str, int]],
    rng: random.Random,
) -> dict[int, str]:
    shuffled = indices[:]
    rng.shuffle(shuffled)
    out: dict[int, str] = {}
    cursor = 0
    for target, count in target_counts:
        for index in shuffled[cursor : cursor + count]:
            out[index] = target
        cursor += count
    return out


def transition_matrix(standard: list[str], target: list[str]) -> dict[tuple[str, str], int]:
    matrix: dict[tuple[str, str], int] = defaultdict(int)
    for source, dest in zip(standard, target):
        if source != dest:
            matrix[(source, dest)] += 1
    return dict(sorted(matrix.items()))


def cluster_key(matrix: dict[tuple[str, str], int]) -> str:
    return "|".join(f"{source}>{target}:{count}" for (source, target), count in sorted(matrix.items()))


def source_targets(matrix: dict[tuple[str, str], int]) -> dict[str, list[tuple[str, int]]]:
    grouped: dict[str, list[tuple[str, int]]] = defaultdict(list)
    for (source, target), count in sorted(matrix.items()):
        grouped[source].append((target, count))
    return dict(grouped)


def null_support_size(standard: list[str], matrix: dict[tuple[str, str], int]) -> int:
    grouped = source_targets(matrix)
    support = 1
    for source, targets in grouped.items():
        pool_size = sum(1 for label in standard if label == source)
        changed = sum(count for _target, count in targets)
        counts = [count for _target, count in targets]
        counts.append(pool_size - changed)
        support *= multinomial_count(pool_size, counts)
    return support


def null_distribution(
    standard: list[str],
    matrix: dict[tuple[str, str], int],
    edges: list[tuple[int, int]],
    exact_limit: int,
    draws: int,
    seed_text: str,
) -> dict[str, object]:
    grouped = source_targets(matrix)
    per_source_indices = {
        source: [idx for idx, label in enumerate(standard) if label == source] for source in grouped
    }
    support = null_support_size(standard, matrix)
    values_all: list[int] = []
    values_sense: list[int] = []
    if support <= exact_limit:
        source_options = [
            assignment_options(per_source_indices[source], grouped[source]) for source in sorted(grouped)
        ]

        def rec(pos: int, updates: dict[int, str]) -> None:
            if pos == len(source_options):
                labels = standard[:]
                for index, label in updates.items():
                    labels[index] = label
                values_all.append(edge_count(labels, edges, sense_only=False))
                values_sense.append(edge_count(labels, edges, sense_only=True))
                return
            for option in source_options[pos]:
                next_updates = dict(updates)
                next_updates.update(option)
                rec(pos + 1, next_updates)

        rec(0, {})
        method = "exact"
    else:
        rng = random.Random(stable_seed(seed_text))
        sources = sorted(grouped)
        for _draw in range(draws):
            labels = standard[:]
            for source in sources:
                for index, label in random_assignment(per_source_indices[source], grouped[source], rng).items():
                    labels[index] = label
            values_all.append(edge_count(labels, edges, sense_only=False))
            values_sense.append(edge_count(labels, edges, sense_only=True))
        method = "monte_carlo"
    return {
        "method": method,
        "support_size": support,
        "sample_size": len(values_all),
        "all": values_all,
        "sense": values_sense,
    }


def distribution_summary(values: list[int], observed: int, baseline: int) -> dict[str, object]:
    deltas = [value - baseline for value in values]
    expected = mean(deltas)
    return {
        "expected_delta": expected,
        "z": observed - baseline - expected,
        "p_upper": sum(delta >= observed - baseline for delta in deltas) / len(deltas),
        "distinct_delta": len(set(deltas)),
        "min_delta": min(deltas),
        "max_delta": max(deltas),
        "sd_delta": math.sqrt(variance([float(value) for value in deltas])),
    }


def table_family(name: str) -> str:
    lowered = name.lower()
    if "mitochondrial" in lowered:
        return "mitochondrial"
    if "nuclear" in lowered:
        return "nuclear"
    if "plastid" in lowered:
        return "plastid"
    return "other"


def table_result(
    table: dict[str, object],
    standard: list[str],
    edges: list[tuple[int, int]],
    standard_e_all: int,
    standard_e_sense: int,
) -> dict[str, object]:
    labels = list(str(table["ncbieaa"]))
    matrix = transition_matrix(standard, labels)
    key = cluster_key(matrix)
    dist = null_distribution(
        standard,
        matrix,
        edges,
        EXACT_ENUMERATION_LIMIT,
        MONTE_CARLO_DRAWS,
        f"{NULL_SEED_PREFIX}.{key}",
    )
    observed_e_all = edge_count(labels, edges, sense_only=False)
    observed_e_sense = edge_count(labels, edges, sense_only=True)
    all_summary = distribution_summary(dist["all"], observed_e_all, standard_e_all)  # type: ignore[arg-type]
    sense_summary = distribution_summary(dist["sense"], observed_e_sense, standard_e_sense)  # type: ignore[arg-type]
    reassigned = sum(1 for source, dest in zip(standard, labels) if source != dest)
    return {
        "table_id": int(table["id"]),
        "table_name": str(table["name"]),
        "family": table_family(str(table["name"])),
        "R_t": reassigned,
        "low_resolution": reassigned <= 2,
        "cluster_key": key,
        "transition_matrix": {f"{source}>{target}": count for (source, target), count in matrix.items()},
        "null_method": dist["method"],
        "null_support": dist["support_size"],
        "null_sample_size": dist["sample_size"],
        "e_all": observed_e_all,
        "delta_e_all": observed_e_all - standard_e_all,
        "expected_delta_e_all": all_summary["expected_delta"],
        "Z_all": all_summary["z"],
        "p_all": all_summary["p_upper"],
        "distinct_delta_e_all": all_summary["distinct_delta"],
        "delta_e_all_range": [all_summary["min_delta"], all_summary["max_delta"]],
        "sd_delta_e_all": all_summary["sd_delta"],
        "_null_delta_e_all": [value - standard_e_all for value in dist["all"]],  # type: ignore[operator]
        "e_sense": observed_e_sense,
        "delta_e_sense": observed_e_sense - standard_e_sense,
        "expected_delta_e_sense": sense_summary["expected_delta"],
        "Z_sense": sense_summary["z"],
        "p_sense": sense_summary["p_upper"],
        "distinct_delta_e_sense": sense_summary["distinct_delta"],
        "delta_e_sense_range": [sense_summary["min_delta"], sense_summary["max_delta"]],
        "sd_delta_e_sense": sense_summary["sd_delta"],
        "_null_delta_e_sense": [value - standard_e_sense for value in dist["sense"]],  # type: ignore[operator]
    }


def cluster_tail_p(
    items: list[dict[str, object]],
    observed_delta_key: str,
    null_delta_key: str,
    seed_text: str,
) -> tuple[float, int]:
    observed = mean([float(item[observed_delta_key]) for item in items])
    distributions = [list(item[null_delta_key]) for item in items]  # type: ignore[arg-type]
    product_size = 1
    for values in distributions:
        product_size *= len(values)
    hits = 0
    total = 0
    if product_size <= EXACT_ENUMERATION_LIMIT:
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
    else:
        rng = random.Random(stable_seed(seed_text))
        total = CLUSTER_MONTE_CARLO_DRAWS
        for _draw in range(total):
            sampled = sum(float(rng.choice(values)) for values in distributions) / len(distributions)
            if sampled >= observed:
                hits += 1
    return hits / total, product_size


def cluster_summaries(results: list[dict[str, object]], key_name: str = "cluster_key") -> list[dict[str, object]]:
    grouped: dict[str, list[dict[str, object]]] = defaultdict(list)
    for result in results:
        if not result["low_resolution"]:
            grouped[str(result[key_name])].append(result)
    summaries = []
    for key, items in sorted(grouped.items()):
        z_all = mean([float(item["Z_all"]) for item in items])
        z_sense = mean([float(item["Z_sense"]) for item in items])
        p_all, cluster_support_all = cluster_tail_p(
            items,
            "delta_e_all",
            "_null_delta_e_all",
            f"{CLUSTER_SEED_PREFIX}.all.{key}",
        )
        p_sense, cluster_support_sense = cluster_tail_p(
            items,
            "delta_e_sense",
            "_null_delta_e_sense",
            f"{CLUSTER_SEED_PREFIX}.sense.{key}",
        )
        families = Counter(str(item["family"]) for item in items)
        summaries.append(
            {
                "cluster_key": key,
                "size": len(items),
                "table_ids": [int(item["table_id"]) for item in items],
                "families": dict(sorted(families.items())),
                "Z_all": z_all,
                "Z_sense": z_sense,
                "p_all": p_all,
                "p_sense": p_sense,
                "cluster_null_support_all": cluster_support_all,
                "cluster_null_support_sense": cluster_support_sense,
                "support_min": min(int(item["null_support"]) for item in items),
                "support_max": max(int(item["null_support"]) for item in items),
                "distinct_delta_e_all": sorted({int(item["distinct_delta_e_all"]) for item in items}),
                "distinct_delta_e_sense": sorted({int(item["distinct_delta_e_sense"]) for item in items}),
            }
        )
    return summaries


def family_sensitivity(results: list[dict[str, object]]) -> dict[str, object]:
    by_family: dict[str, list[dict[str, object]]] = defaultdict(list)
    for result in results:
        if not result["low_resolution"]:
            by_family[str(result["family"])].append(result)
    out: dict[str, object] = {}
    for family, items in sorted(by_family.items()):
        clusters = cluster_summaries(items)
        p_values = [float(cluster["p_all"]) for cluster in clusters]
        sense_p_values = [float(cluster["p_sense"]) for cluster in clusters]
        out[family] = {
            "n_tables": len(items),
            "K": len(clusters),
            "T_all": round_float(mean([float(cluster["Z_all"]) for cluster in clusters])) if clusters else None,
            "T_sense": round_float(mean([float(cluster["Z_sense"]) for cluster in clusters])) if clusters else None,
            "fisher_p_all": round_float(fisher_upper_p(p_values)) if p_values else None,
            "stouffer_p_all": round_float(stouffer_upper_p(p_values)) if p_values else None,
            "fisher_p_sense": round_float(fisher_upper_p(sense_p_values)) if sense_p_values else None,
            "stouffer_p_sense": round_float(stouffer_upper_p(sense_p_values)) if sense_p_values else None,
        }
    non_mito = [result for result in results if str(result["family"]) != "mitochondrial" and not result["low_resolution"]]
    clusters = cluster_summaries(non_mito)
    p_values = [float(cluster["p_all"]) for cluster in clusters]
    sense_p_values = [float(cluster["p_sense"]) for cluster in clusters]
    out["non_mitochondrial"] = {
        "n_tables": len(non_mito),
        "K": len(clusters),
        "T_all": round_float(mean([float(cluster["Z_all"]) for cluster in clusters])) if clusters else None,
        "T_sense": round_float(mean([float(cluster["Z_sense"]) for cluster in clusters])) if clusters else None,
        "fisher_p_all": round_float(fisher_upper_p(p_values)) if p_values else None,
        "stouffer_p_all": round_float(stouffer_upper_p(p_values)) if p_values else None,
        "fisher_p_sense": round_float(fisher_upper_p(sense_p_values)) if sense_p_values else None,
        "stouffer_p_sense": round_float(stouffer_upper_p(sense_p_values)) if sense_p_values else None,
    }
    return out


def compact_table_result(result: dict[str, object]) -> dict[str, object]:
    return {
        "table_name": result["table_name"],
        "family": result["family"],
        "R_t": result["R_t"],
        "low_resolution": result["low_resolution"],
        "delta_e_all": result["delta_e_all"],
        "delta_e_sense": result["delta_e_sense"],
        "expected_delta_e_all": round_float(float(result["expected_delta_e_all"])),
        "expected_delta_e_sense": round_float(float(result["expected_delta_e_sense"])),
        "Z_all": round_float(float(result["Z_all"])),
        "Z_sense": round_float(float(result["Z_sense"])),
        "p_all": round_float(float(result["p_all"])),
        "p_sense": round_float(float(result["p_sense"])),
        "null_method": result["null_method"],
        "null_support": result["null_support"],
        "null_sample_size": result["null_sample_size"],
        "distinct_delta_e_all": result["distinct_delta_e_all"],
        "distinct_delta_e_sense": result["distinct_delta_e_sense"],
    }


def main() -> None:
    try:
        probe = load_probe_module()
        panel = probe.build_panel(force_refresh=True)
    except Exception as exc:
        emit(
            "needs_external",
            reason=f"gc.prt fetch probe failed: {type(exc).__name__}:{exc}",
            note="No path-level edge-hiding reassignment verdict was computed.",
        )
    if not panel.get("fetchable"):
        emit("needs_external", fetch_probe=panel, note="NCBI gc.prt was not fetchable.")

    codons = list(panel["codon_order"])  # type: ignore[index]
    if codons != ["".join(parts) for parts in zip("T" * 16 + "C" * 16 + "A" * 16 + "G" * 16, "TTTTCCCCAAAAGGGG" * 4, "TCAG" * 16)]:
        emit("needs_external", reason="gc.prt codon order is not the expected Base1/Base2/Base3 T,C,A,G order")
    edges = hamming1_edges(codons)
    tables = list(panel["tables"])  # type: ignore[index]
    standard_rows = [table for table in tables if int(table["id"]) == 1]
    if len(standard_rows) != 1:
        emit("needs_external", reason="gc.prt did not expose a unique standard code id=1")
    standard = list(str(standard_rows[0]["ncbieaa"]))
    standard_e_all = edge_count(standard, edges, sense_only=False)
    standard_e_sense = edge_count(standard, edges, sense_only=True)
    candidates = [
        table
        for table in tables
        if int(table["id"]) != 1 and str(table["ncbieaa"]) != str(standard_rows[0]["ncbieaa"])
    ]
    if len(candidates) < 10:
        emit(
            "needs_external",
            reason="gc.prt yielded fewer than 10 AA-distinct nonstandard genetic-code tables",
            fetch_probe={"source": panel.get("source"), "n_nonstandard_aa_distinct": len(candidates)},
        )

    results = [table_result(table, standard, edges, standard_e_all, standard_e_sense) for table in candidates]
    all_cluster_count = len({str(result["cluster_key"]) for result in results})
    clusters = cluster_summaries(results)
    p_values_all = [float(cluster["p_all"]) for cluster in clusters]
    p_values_sense = [float(cluster["p_sense"]) for cluster in clusters]
    T_all = mean([float(cluster["Z_all"]) for cluster in clusters]) if clusters else math.nan
    T_sense = mean([float(cluster["Z_sense"]) for cluster in clusters]) if clusters else math.nan
    fisher_p_all = fisher_upper_p(p_values_all)
    stouffer_p_all = stouffer_upper_p(p_values_all)
    fisher_p_sense = fisher_upper_p(p_values_sense)
    stouffer_p_sense = stouffer_upper_p(p_values_sense)
    combined_p_all = min(fisher_p_all, stouffer_p_all)
    combined_p_sense = min(fisher_p_sense, stouffer_p_sense)
    singleton_ratio_analyzed = sum(1 for cluster in clusters if int(cluster["size"]) == 1) / len(clusters) if clusters else math.nan
    all_cluster_sizes = Counter(str(result["cluster_key"]) for result in results)
    singleton_ratio_all = (
        sum(1 for size in all_cluster_sizes.values() if size == 1) / len(all_cluster_sizes)
        if all_cluster_sizes
        else math.nan
    )
    sensitivity = family_sensitivity(results)
    mitochondrial = sensitivity.get("mitochondrial", {})
    non_mito = sensitivity.get("non_mitochondrial", {})
    non_mito_direction_ok = (
        isinstance(non_mito, dict)
        and non_mito.get("K", 0)
        and float(non_mito.get("T_all") or 0.0) > 0.0
        and float(non_mito.get("T_sense") or 0.0) > 0.0
    )
    single_mito_driven = (
        isinstance(mitochondrial, dict)
        and int(mitochondrial.get("K") or 0) >= 1
        and not non_mito_direction_ok
    )
    direction_consistent = T_all > 0.0 and T_sense > 0.0 and combined_p_sense <= 0.05
    if combined_p_all <= ALPHA and direction_consistent and not single_mito_driven:
        status = "certified"
        verdict_note = (
            "Path-level evolutionary edge-hiding evidence under exact transition-matrix matched "
            "permutations; this is not a causal proof."
        )
    elif T_all <= 0.0 or T_sense <= 0.0:
        status = "refuted"
        verdict_note = "Natural reassignments are not more edge-preserving than the matched null."
    else:
        status = "coincidence"
        verdict_note = (
            "Natural reassignments do not clear the registered cluster-level evidence threshold "
            "under the matched null."
        )

    emit(
        status,
        source=panel.get("source"),
        codon_order="Base1/Base2/Base3 DNA T,C,A,G from gc.prt",
        n_tables=len(results),
        n_low_resolution=sum(1 for result in results if result["low_resolution"]),
        standard_e_all=standard_e_all,
        standard_e_sense=standard_e_sense,
        exact_enumeration_limit=EXACT_ENUMERATION_LIMIT,
        monte_carlo_draws=MONTE_CARLO_DRAWS,
        cluster_monte_carlo_draws=CLUSTER_MONTE_CARLO_DRAWS,
        K=all_cluster_count,
        K_analyzed=len(clusters),
        singleton_ratio=round_float(singleton_ratio_all),
        singleton_ratio_analyzed=round_float(singleton_ratio_analyzed),
        T=round_float(T_all),
        T_sense=round_float(T_sense),
        cluster_combined_p=round_float(combined_p_all),
        cluster_combined_p_method="min(fisher_wilson_hilferty,stouffer)",
        fisher_p_all=round_float(fisher_p_all),
        stouffer_p_all=round_float(stouffer_p_all),
        fisher_p_sense=round_float(fisher_p_sense),
        stouffer_p_sense=round_float(stouffer_p_sense),
        e_sense_version={
            "T_sense": round_float(T_sense),
            "cluster_combined_p_sense": round_float(combined_p_sense),
            "direction_consistent": direction_consistent,
        },
        mito_nuclear_sensitivity=sensitivity,
        single_mito_driven=single_mito_driven,
        cluster_diagnostics=[
            {
                "cluster_key": cluster["cluster_key"],
                "size": cluster["size"],
                "table_ids": cluster["table_ids"],
                "families": cluster["families"],
                "Z_all": round_float(float(cluster["Z_all"])),
                "Z_sense": round_float(float(cluster["Z_sense"])),
                "p_all": round_float(float(cluster["p_all"])),
                "p_sense": round_float(float(cluster["p_sense"])),
                "cluster_null_support_all": cluster["cluster_null_support_all"],
                "cluster_null_support_sense": cluster["cluster_null_support_sense"],
                "support_min": cluster["support_min"],
                "support_max": cluster["support_max"],
                "distinct_delta_e_all": cluster["distinct_delta_e_all"],
                "distinct_delta_e_sense": cluster["distinct_delta_e_sense"],
            }
            for cluster in clusters
        ],
        per_table={str(result["table_id"]): compact_table_result(result) for result in results},
        note=(
            verdict_note
            + " The statistic deepens the already-certified edge-hiding positive signal and is "
            "not an independent Window6 repetition."
        ),
    )


if __name__ == "__main__":
    main()

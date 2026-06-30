#!/usr/bin/env python3
"""Specificity test for reassignment edge hiding against missense physicochemical load."""
from __future__ import annotations

from bisect import bisect_right
from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import random
import sys
from typing import Any


EXPERIMENT_ID = "edge_hiding_reassignment_specificity"
CLAIM_ID = "bridge.genetic_code.edge_hiding_reassignment_specificity"
PRIMARY_PROPERTY = "WOEC730101"
PROPERTY_BATTERY = (
    "WOEC730101",
    "GRAR740102",
    "GRAR740103",
    "KYTJ820101",
)
PROPERTY_LABELS = {
    "WOEC730101": "polar_requirement",
    "GRAR740102": "grantham_polarity",
    "GRAR740103": "grantham_volume",
    "KYTJ820101": "kyte_doolittle_hydropathy",
}
EXACT_ENUMERATION_LIMIT = 200000
MONTE_CARLO_DRAWS = 20000
COMBINED_NULL_DRAWS = 200000
MIN_STRATUM_SIZE = 200
ALPHA = 0.01
STOP = "*"

EXPERIMENT_DIR = Path(__file__).resolve().parent
ALT_PATH = EXPERIMENT_DIR / "run_edge_hiding_alternative_code_reassignment.py"
AAINDEX_PROBE_PATH = EXPERIMENT_DIR / "_edgehide_spec_fetch_probe.py"


def load_module(path: Path, name: str) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


ALT = load_module(ALT_PATH, "_edgehide_alt_reassign")
AAINDEX_PROBE = load_module(AAINDEX_PROBE_PATH, "_edgehide_spec_fetch_probe")


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


def population_sd(values: list[float]) -> float:
    center = mean(values)
    return math.sqrt(sum((value - center) * (value - center) for value in values) / len(values))


def pearson(xs: list[float], ys: list[float]) -> float | None:
    if len(xs) != len(ys) or len(xs) < 2:
        return None
    x_mean = mean(xs)
    y_mean = mean(ys)
    dx = [x - x_mean for x in xs]
    dy = [y - y_mean for y in ys]
    denom_x = math.sqrt(sum(x * x for x in dx))
    denom_y = math.sqrt(sum(y * y for y in dy))
    if denom_x == 0.0 or denom_y == 0.0:
        return None
    return sum(x * y for x, y in zip(dx, dy)) / (denom_x * denom_y)


def percentile(sorted_values: list[float], value: float) -> float:
    if not sorted_values:
        return math.nan
    return bisect_right(sorted_values, value) / len(sorted_values)


def decile_from_percentile(rank: float) -> int:
    if not math.isfinite(rank):
        return 9
    return min(9, max(0, int(rank * 10.0)))


def code_key(labels: list[str]) -> str:
    return "".join(labels)


def normalize_properties(aa_panel: dict[str, object]) -> dict[str, dict[str, float]]:
    records = aa_panel["records"]
    assert isinstance(records, dict)
    out: dict[str, dict[str, float]] = {}
    for index_id in PROPERTY_BATTERY:
        record = records[index_id]
        assert isinstance(record, dict)
        raw_values = record["values"]
        assert isinstance(raw_values, dict)
        values = {aa: float(raw_values[aa]) for aa in "ARNDCQEGHILKMFPSTWYV"}
        sd = population_sd(list(values.values()))
        if sd == 0.0:
            raise ValueError(f"{index_id} has zero amino-acid standard deviation")
        center = mean(list(values.values()))
        out[index_id] = {aa: (value - center) / sd for aa, value in values.items()}
    return out


def h_sense(labels: list[str], edges: list[tuple[int, int]]) -> int:
    return int(ALT.edge_count(labels, edges, sense_only=True))


def h_all(labels: list[str], edges: list[tuple[int, int]]) -> int:
    return int(ALT.edge_count(labels, edges, sense_only=False))


def missense_cost(labels: list[str], edges: list[tuple[int, int]], property_values: dict[str, float]) -> float:
    total = 0.0
    count = 0
    for left, right in edges:
        aa_left = labels[left]
        aa_right = labels[right]
        if aa_left == STOP or aa_right == STOP or aa_left == aa_right:
            continue
        diff = property_values[aa_left] - property_values[aa_right]
        total += diff * diff
        count += 1
    if count == 0:
        return math.nan
    return total / count


def full_error_load(labels: list[str], edges: list[tuple[int, int]], property_values: dict[str, float]) -> float:
    total = 0.0
    count = 0
    for left, right in edges:
        aa_left = labels[left]
        aa_right = labels[right]
        if aa_left == STOP or aa_right == STOP:
            continue
        diff = property_values[aa_left] - property_values[aa_right]
        total += diff * diff
        count += 1
    if count == 0:
        return math.nan
    return total / count


def code_record(labels: list[str], edges: list[tuple[int, int]], properties: dict[str, dict[str, float]]) -> dict[str, object]:
    costs = {index_id: missense_cost(labels, edges, values) for index_id, values in properties.items()}
    raw_load = {index_id: full_error_load(labels, edges, values) for index_id, values in properties.items()}
    return {
        "labels": labels,
        "code_key": code_key(labels),
        "H_sense": h_sense(labels, edges),
        "H_all": h_all(labels, edges),
        "F": costs,
        "raw_full_error_load_descriptive": raw_load,
    }


def null_state_records(
    standard: list[str],
    matrix: dict[tuple[str, str], int],
    edges: list[tuple[int, int]],
    properties: dict[str, dict[str, float]],
    seed_text: str,
) -> dict[str, object]:
    grouped = ALT.source_targets(matrix)
    per_source_indices = {
        source: [idx for idx, label in enumerate(standard) if label == source] for source in grouped
    }
    support = int(ALT.null_support_size(standard, matrix))
    records: list[dict[str, object]] = []
    if support <= EXACT_ENUMERATION_LIMIT:
        source_options = [
            ALT.assignment_options(per_source_indices[source], grouped[source]) for source in sorted(grouped)
        ]

        def rec(pos: int, updates: dict[int, str]) -> None:
            if pos == len(source_options):
                labels = standard[:]
                for index, label in updates.items():
                    labels[index] = label
                records.append(code_record(labels, edges, properties))
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
        for _draw in range(MONTE_CARLO_DRAWS):
            labels = standard[:]
            for source in sources:
                assignment = ALT.random_assignment(per_source_indices[source], grouped[source], rng)
                for index, label in assignment.items():
                    labels[index] = label
            records.append(code_record(labels, edges, properties))
        method = "monte_carlo"
    return {
        "method": method,
        "support_size": support,
        "sample_size": len(records),
        "records": records,
    }


def assign_deciles(records: list[dict[str, object]], metric_key: str) -> dict[int, list[dict[str, object]]]:
    ordered = sorted(records, key=lambda record: (float(record[metric_key]), str(record["code_key"])))
    bins: dict[int, list[dict[str, object]]] = {idx: [] for idx in range(10)}
    n = len(ordered)
    for idx, record in enumerate(ordered):
        decile = min(9, (idx * 10) // n)
        bins[decile].append(record)
    return bins


def expand_decile_support(
    bins: dict[int, list[dict[str, object]]],
    observed_deciles: set[int],
    min_size: int = MIN_STRATUM_SIZE,
) -> tuple[list[dict[str, object]], list[int]]:
    chosen: set[int] = set(observed_deciles)
    for radius in range(10):
        for decile in list(observed_deciles):
            if decile - radius >= 0:
                chosen.add(decile - radius)
            if decile + radius <= 9:
                chosen.add(decile + radius)
        selected = [record for decile in sorted(chosen) for record in bins[decile]]
        if len(selected) >= min_size or len(chosen) == 10:
            return selected, sorted(chosen)
    return [record for decile in range(10) for record in bins[decile]], list(range(10))


def matched_by_metric(
    records: list[dict[str, object]],
    observed_metric_values: list[float],
    metric_name: str,
) -> dict[str, object]:
    sorted_metric = sorted(float(record[metric_name]) for record in records)
    observed_percentiles = [percentile(sorted_metric, value) for value in observed_metric_values]
    observed_deciles = {decile_from_percentile(rank) for rank in observed_percentiles}
    bins = assign_deciles(records, metric_name)
    selected, selected_deciles = expand_decile_support(bins, observed_deciles)
    return {
        "records": selected,
        "observed_percentiles": observed_percentiles,
        "observed_deciles": sorted(observed_deciles),
        "selected_deciles": selected_deciles,
    }


def add_q_phys(records: list[dict[str, object]]) -> None:
    sorted_by_property = {
        index_id: sorted(float(record["F"][index_id]) for record in records)  # type: ignore[index]
        for index_id in PROPERTY_BATTERY
    }
    for record in records:
        costs = record["F"]
        assert isinstance(costs, dict)
        q_values = {
            index_id: percentile(sorted_by_property[index_id], float(costs[index_id]))
            for index_id in PROPERTY_BATTERY
        }
        record["Q_phys"] = min(q_values.values())
        record["Q_phys_by_property"] = q_values


def support_digest(records: list[dict[str, object]]) -> dict[str, object]:
    h_values = [int(record["H_sense"]) for record in records]
    return {
        "n_states": len(records),
        "unique_code_count": len({str(record["code_key"]) for record in records}),
        "distinct_H_sense": len(set(h_values)),
        "H_sense_min": min(h_values) if h_values else None,
        "H_sense_median": round_float(median([float(value) for value in h_values])) if h_values else None,
        "H_sense_max": max(h_values) if h_values else None,
    }


def cluster_specificity(
    cluster_key: str,
    items: list[dict[str, object]],
    standard: list[str],
    edges: list[tuple[int, int]],
    properties: dict[str, dict[str, float]],
) -> dict[str, object]:
    matrix = items[0]["matrix"]
    assert isinstance(matrix, dict)
    state_panel = null_state_records(
        standard,
        matrix,  # type: ignore[arg-type]
        edges,
        properties,
        f"{EXPERIMENT_ID}.transition_matrix.{cluster_key}",
    )
    records = state_panel["records"]
    assert isinstance(records, list)
    add_q_phys(records)
    observed_records = [
        code_record(list(str(item["ncbieaa"])), edges, properties)
        for item in items
    ]
    for observed in observed_records:
        observed["Q_phys"] = min(
            percentile(
                sorted(float(record["F"][index_id]) for record in records),  # type: ignore[index]
                float(observed["F"][index_id]),  # type: ignore[index]
            )
            for index_id in PROPERTY_BATTERY
        )
    observed_h = [float(record["H_sense"]) for record in observed_records]
    observed_h_all = [float(record["H_all"]) for record in observed_records]
    observed_mean_h = mean(observed_h)
    observed_mean_h_all = mean(observed_h_all)
    for record in records:
        costs = record["F"]
        assert isinstance(costs, dict)
        record["F_PR"] = float(costs[PRIMARY_PROPERTY])
    pr_match = matched_by_metric(
        records,
        [float(record["F"][PRIMARY_PROPERTY]) for record in observed_records],  # type: ignore[index]
        "F_PR",
    )
    phys_match = matched_by_metric(
        records,
        [float(record["Q_phys"]) for record in observed_records],
        "Q_phys",
    )
    correlations = {}
    h_values = [float(record["H_sense"]) for record in records]
    for index_id in PROPERTY_BATTERY:
        f_values = [float(record["F"][index_id]) for record in records]  # type: ignore[index]
        correlations[index_id] = round_float(pearson(h_values, f_values))
    q_corr = pearson(h_values, [float(record["Q_phys"]) for record in records])
    pr_records = pr_match["records"]
    phys_records = phys_match["records"]
    assert isinstance(pr_records, list)
    assert isinstance(phys_records, list)
    pr_h = [float(record["H_sense"]) for record in pr_records]
    phys_h = [float(record["H_sense"]) for record in phys_records]
    pr_median = median(pr_h)
    phys_median = median(phys_h)
    pr_d = observed_mean_h - pr_median
    phys_d = observed_mean_h - phys_median
    return {
        "cluster_key": cluster_key,
        "size": len(items),
        "table_ids": [int(item["table_id"]) for item in items],
        "families": dict(sorted(Counter(str(item["family"]) for item in items).items())),
        "transition_matrix": items[0]["transition_matrix"],
        "null_method": state_panel["method"],
        "null_support": state_panel["support_size"],
        "null_sample_size": state_panel["sample_size"],
        "observed_H_sense_mean": observed_mean_h,
        "observed_H_all_mean": observed_mean_h_all,
        "observed_F": {
            index_id: round_float(mean([float(record["F"][index_id]) for record in observed_records]))  # type: ignore[index]
            for index_id in PROPERTY_BATTERY
        },
        "observed_Q_phys_mean": round_float(mean([float(record["Q_phys"]) for record in observed_records])),
        "full_support": support_digest(records),
        "H_sense_Fp_corr": correlations,
        "H_sense_Q_phys_corr": round_float(q_corr),
        "PR": {
            "D_k": pr_d,
            "median_H_sense": pr_median,
            "support": support_digest(pr_records),
            "observed_percentiles": [round_float(float(value)) for value in pr_match["observed_percentiles"]],  # type: ignore[index]
            "observed_deciles": pr_match["observed_deciles"],
            "selected_deciles": pr_match["selected_deciles"],
            "_H_values": [int(record["H_sense"]) for record in pr_records],
        },
        "phys": {
            "D_k": phys_d,
            "median_H_sense": phys_median,
            "support": support_digest(phys_records),
            "observed_percentiles": [round_float(float(value)) for value in phys_match["observed_percentiles"]],  # type: ignore[index]
            "observed_deciles": phys_match["observed_deciles"],
            "selected_deciles": phys_match["selected_deciles"],
            "_H_values": [int(record["H_sense"]) for record in phys_records],
        },
        "raw_full_error_load_descriptive": {
            index_id: round_float(mean([float(record["raw_full_error_load_descriptive"][index_id]) for record in observed_records]))  # type: ignore[index]
            for index_id in PROPERTY_BATTERY
        },
    }


def combined_cluster_null(clusters: list[dict[str, object]], null_name: str) -> dict[str, object]:
    if not clusters:
        return {"T_spec": math.nan, "p": math.nan, "draws": 0, "product_support_log10": None}
    d_values = [float(cluster[null_name]["D_k"]) for cluster in clusters]  # type: ignore[index]
    medians = [float(cluster[null_name]["median_H_sense"]) for cluster in clusters]  # type: ignore[index]
    h_lists = [list(cluster[null_name]["_H_values"]) for cluster in clusters]  # type: ignore[index]
    t_obs = mean(d_values)
    product_log10 = sum(math.log10(len(values)) for values in h_lists if values)
    rng = random.Random(stable_seed(f"{EXPERIMENT_ID}.combined.{null_name}.{COMBINED_NULL_DRAWS}"))
    hits = 0
    for _draw in range(COMBINED_NULL_DRAWS):
        sampled = mean([
            float(rng.choice(values)) - median_value
            for values, median_value in zip(h_lists, medians)
        ])
        if sampled >= t_obs:
            hits += 1
    return {
        "T_spec": t_obs,
        "p": (1 + hits) / (1 + COMBINED_NULL_DRAWS),
        "draws": COMBINED_NULL_DRAWS,
        "product_support_log10": product_log10,
    }


def dominance(clusters: list[dict[str, object]], null_name: str) -> dict[str, object]:
    d_values = [float(cluster[null_name]["D_k"]) for cluster in clusters]  # type: ignore[index]
    if not d_values:
        return {
            "ok": False,
            "max_cluster_share": None,
            "largest_cluster_key": None,
            "leave_one_largest_out_T": None,
            "leave_one_largest_out_direction": False,
        }
    total = sum(d_values)
    largest_index = max(range(len(d_values)), key=lambda idx: d_values[idx])
    share = d_values[largest_index] / total if total > 0.0 else math.inf
    if len(d_values) > 1:
        loo_t = (total - d_values[largest_index]) / (len(d_values) - 1)
    else:
        loo_t = math.nan
    direction = bool(math.isfinite(loo_t) and loo_t > 0.0)
    return {
        "ok": bool(total > 0.0 and (share <= 0.5 or direction)),
        "max_cluster_share": round_float(share),
        "largest_cluster_key": clusters[largest_index]["cluster_key"],
        "largest_cluster_D_k": round_float(d_values[largest_index]),
        "leave_one_largest_out_T": round_float(loo_t),
        "leave_one_largest_out_direction": direction,
    }


def compact_cluster(cluster: dict[str, object]) -> dict[str, object]:
    pr = cluster["PR"]
    phys = cluster["phys"]
    assert isinstance(pr, dict)
    assert isinstance(phys, dict)
    return {
        "cluster_key": cluster["cluster_key"],
        "size": cluster["size"],
        "table_ids": cluster["table_ids"],
        "families": cluster["families"],
        "null_method": cluster["null_method"],
        "null_support": cluster["null_support"],
        "null_sample_size": cluster["null_sample_size"],
        "observed_H_sense_mean": round_float(float(cluster["observed_H_sense_mean"])),
        "observed_H_all_mean": round_float(float(cluster["observed_H_all_mean"])),
        "observed_F": cluster["observed_F"],
        "observed_Q_phys_mean": cluster["observed_Q_phys_mean"],
        "full_support": cluster["full_support"],
        "H_sense_Fp_corr": cluster["H_sense_Fp_corr"],
        "H_sense_Q_phys_corr": cluster["H_sense_Q_phys_corr"],
        "PR": {
            "D_k": round_float(float(pr["D_k"])),
            "median_H_sense": round_float(float(pr["median_H_sense"])),
            "support": pr["support"],
            "observed_percentiles": pr["observed_percentiles"],
            "observed_deciles": pr["observed_deciles"],
            "selected_deciles": pr["selected_deciles"],
        },
        "phys": {
            "D_k": round_float(float(phys["D_k"])),
            "median_H_sense": round_float(float(phys["median_H_sense"])),
            "support": phys["support"],
            "observed_percentiles": phys["observed_percentiles"],
            "observed_deciles": phys["observed_deciles"],
            "selected_deciles": phys["selected_deciles"],
        },
        "raw_full_error_load_descriptive": cluster["raw_full_error_load_descriptive"],
    }


def raw_path_gate(
    panel: dict[str, object],
    standard: list[str],
    edges: list[tuple[int, int]],
    standard_e_all: int,
    standard_e_sense: int,
    candidates: list[dict[str, object]],
) -> dict[str, object]:
    results = [
        ALT.table_result(table, standard, edges, standard_e_all, standard_e_sense)
        for table in candidates
    ]
    clusters = ALT.cluster_summaries(results)
    p_values_all = [float(cluster["p_all"]) for cluster in clusters]
    p_values_sense = [float(cluster["p_sense"]) for cluster in clusters]
    t_all = ALT.mean([float(cluster["Z_all"]) for cluster in clusters]) if clusters else math.nan
    t_sense = ALT.mean([float(cluster["Z_sense"]) for cluster in clusters]) if clusters else math.nan
    fisher_p_all = ALT.fisher_upper_p(p_values_all)
    stouffer_p_all = ALT.stouffer_upper_p(p_values_all)
    fisher_p_sense = ALT.fisher_upper_p(p_values_sense)
    stouffer_p_sense = ALT.stouffer_upper_p(p_values_sense)
    combined_p_all = min(fisher_p_all, stouffer_p_all)
    combined_p_sense = min(fisher_p_sense, stouffer_p_sense)
    sensitivity = ALT.family_sensitivity(results)
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
    reproduced = bool(
        combined_p_all <= ALPHA
        and t_all > 0.0
        and t_sense > 0.0
        and combined_p_sense <= 0.05
        and not single_mito_driven
    )
    return {
        "reproduced": reproduced,
        "source": panel.get("source"),
        "K_analyzed": len(clusters),
        "T_all": round_float(t_all),
        "T_sense": round_float(t_sense),
        "cluster_combined_p": round_float(combined_p_all),
        "cluster_combined_p_sense": round_float(combined_p_sense),
        "fisher_p_all": round_float(fisher_p_all),
        "stouffer_p_all": round_float(stouffer_p_all),
        "fisher_p_sense": round_float(fisher_p_sense),
        "stouffer_p_sense": round_float(stouffer_p_sense),
        "single_mito_driven": single_mito_driven,
    }


def table_items(candidates: list[dict[str, object]], standard: list[str]) -> list[dict[str, object]]:
    items: list[dict[str, object]] = []
    for table in candidates:
        labels = list(str(table["ncbieaa"]))
        matrix = ALT.transition_matrix(standard, labels)
        reassigned = sum(1 for source, dest in zip(standard, labels) if source != dest)
        items.append(
            {
                "table_id": int(table["id"]),
                "table_name": str(table["name"]),
                "family": ALT.table_family(str(table["name"])),
                "ncbieaa": str(table["ncbieaa"]),
                "R_t": reassigned,
                "low_resolution": reassigned <= 2,
                "cluster_key": ALT.cluster_key(matrix),
                "matrix": matrix,
                "transition_matrix": {
                    f"{source}>{target}": count for (source, target), count in matrix.items()
                },
            }
        )
    return items


def main() -> None:
    try:
        aa_panel = AAINDEX_PROBE.build_panel(force_refresh=True)
    except Exception as exc:
        emit(
            "needs_external",
            reason=f"AAindex1 fetch probe failed: {type(exc).__name__}:{exc}",
            note="No specificity verdict was computed.",
        )
    if not aa_panel.get("fetchable"):
        emit("needs_external", fetch_probe=aa_panel, note="AAindex1 was not fetchable.")

    try:
        gc_probe = ALT.load_probe_module()
        gc_panel = gc_probe.build_panel(force_refresh=True)
    except Exception as exc:
        emit(
            "needs_external",
            reason=f"gc.prt fetch probe failed: {type(exc).__name__}:{exc}",
            aaindex_fetch_probe=aa_panel,
        )
    if not gc_panel.get("fetchable"):
        emit("needs_external", fetch_probe=gc_panel, aaindex_fetch_probe=aa_panel)

    properties = normalize_properties(aa_panel)
    codons = list(gc_panel["codon_order"])  # type: ignore[index]
    expected_codons = [
        "".join(parts)
        for parts in zip("T" * 16 + "C" * 16 + "A" * 16 + "G" * 16, "TTTTCCCCAAAAGGGG" * 4, "TCAG" * 16)
    ]
    if codons != expected_codons:
        emit("needs_external", reason="gc.prt codon order is not the expected Base1/Base2/Base3 T,C,A,G order")
    edges = ALT.hamming1_edges(codons)
    tables = list(gc_panel["tables"])  # type: ignore[index]
    standard_rows = [table for table in tables if int(table["id"]) == 1]
    if len(standard_rows) != 1:
        emit("needs_external", reason="gc.prt did not expose a unique standard code id=1")
    standard = list(str(standard_rows[0]["ncbieaa"]))
    standard_e_all = h_all(standard, edges)
    standard_e_sense = h_sense(standard, edges)
    candidates = [
        table
        for table in tables
        if int(table["id"]) != 1 and str(table["ncbieaa"]) != str(standard_rows[0]["ncbieaa"])
    ]
    if len(candidates) < 10:
        emit(
            "needs_external",
            reason="gc.prt yielded fewer than 10 AA-distinct nonstandard genetic-code tables",
            aaindex_fetch_probe=aa_panel,
            gc_fetch_probe={"source": gc_panel.get("source"), "n_nonstandard_aa_distinct": len(candidates)},
        )

    raw_gate = raw_path_gate(gc_panel, standard, edges, standard_e_all, standard_e_sense, candidates)
    if not raw_gate["reproduced"]:
        emit(
            "refuted",
            aaindex_fetch_probe={
                "source": aa_panel.get("source"),
                "sample_values": aa_panel.get("sample_values"),
            },
            raw_path_gate=raw_gate,
            gates={
                "raw_path_reproduced": False,
                "nondegenerate_clusters": False,
                "dominance_ok": False,
                "leave_one_largest_out_direction": {"PR": False, "phys": False},
            },
            note="The path-level edge-hiding gate did not reproduce, so the specificity layer was not certified.",
        )

    items = table_items(candidates, standard)
    grouped: dict[str, list[dict[str, object]]] = defaultdict(list)
    for item in items:
        if not item["low_resolution"]:
            grouped[str(item["cluster_key"])].append(item)
    cluster_ledgers = [
        cluster_specificity(cluster_key, cluster_items, standard, edges, properties)
        for cluster_key, cluster_items in sorted(grouped.items())
    ]
    certification_clusters = [
        cluster
        for cluster in cluster_ledgers
        if int(cluster["PR"]["support"]["distinct_H_sense"]) >= 2  # type: ignore[index]
        and int(cluster["phys"]["support"]["distinct_H_sense"]) >= 2  # type: ignore[index]
    ]
    pr_result = combined_cluster_null(certification_clusters, "PR")
    phys_result = combined_cluster_null(certification_clusters, "phys")
    pr_dominance = dominance(certification_clusters, "PR")
    phys_dominance = dominance(certification_clusters, "phys")
    nondegenerate_ok = len(certification_clusters) > 0 and len(certification_clusters) == len(cluster_ledgers)
    dominance_ok = bool(pr_dominance["ok"] and phys_dominance["ok"])
    certified = bool(
        raw_gate["reproduced"]
        and nondegenerate_ok
        and float(pr_result["T_spec"]) > 0.0
        and float(pr_result["p"]) <= ALPHA
        and float(phys_result["T_spec"]) > 0.0
        and float(phys_result["p"]) <= ALPHA
        and dominance_ok
    )
    if certified:
        status = "certified"
    elif float(pr_result["T_spec"]) <= 0.0 or float(phys_result["T_spec"]) <= 0.0:
        status = "refuted"
    else:
        status = "coincidence"

    note = (
        "Scope: this test asks whether the certified edge-hiding signal is reducible to "
        "missense-only physicochemical conservation. It does not test independence from a "
        "full error-minimization objective that includes identity edges, because edge hiding "
        "is exactly the identity endpoint of physicochemical conservation. The primary scale "
        "is WOEC730101 polar requirement; GRAR740102 polarity, GRAR740103 volume, and "
        "KYTJ820101 hydropathy are sensitivity scales. The statistic is non-causal and is "
        "not an independent Window6 repetition."
    )
    emit(
        status,
        primary_property=PRIMARY_PROPERTY,
        property_battery=list(PROPERTY_BATTERY),
        aaindex_fetch_probe={
            "source": aa_panel.get("source"),
            "target_indices": aa_panel.get("target_indices"),
            "sample_values": aa_panel.get("sample_values"),
        },
        gc_source=gc_panel.get("source"),
        n_tables=len(candidates),
        n_low_resolution=sum(1 for item in items if item["low_resolution"]),
        standard_H_all=standard_e_all,
        standard_H_sense=standard_e_sense,
        exact_enumeration_limit=EXACT_ENUMERATION_LIMIT,
        monte_carlo_draws=MONTE_CARLO_DRAWS,
        combined_null_draws=COMBINED_NULL_DRAWS,
        min_stratum_size=MIN_STRATUM_SIZE,
        raw_path_gate=raw_gate,
        T_spec_PR=round_float(float(pr_result["T_spec"])),
        p_PR=round_float(float(pr_result["p"])),
        T_spec_phys=round_float(float(phys_result["T_spec"])),
        p_phys=round_float(float(phys_result["p"])),
        K_total=len(cluster_ledgers),
        K_analyzed=len(certification_clusters),
        gates={
            "raw_path_reproduced": bool(raw_gate["reproduced"]),
            "nondegenerate_clusters": nondegenerate_ok,
            "dominance_ok": dominance_ok,
            "leave_one_largest_out_direction": {
                "PR": bool(pr_dominance["leave_one_largest_out_direction"]),
                "phys": bool(phys_dominance["leave_one_largest_out_direction"]),
            },
            "missense_cost_non_tautology": True,
        },
        dominance={
            "PR": pr_dominance,
            "phys": phys_dominance,
        },
        matched_null_support={
            "PR_product_support_log10": round_float(float(pr_result["product_support_log10"])),
            "phys_product_support_log10": round_float(float(phys_result["product_support_log10"])),
            "PR_min_effective_sample_size": min(
                int(cluster["PR"]["support"]["unique_code_count"]) for cluster in certification_clusters  # type: ignore[index]
            )
            if certification_clusters
            else 0,
            "phys_min_effective_sample_size": min(
                int(cluster["phys"]["support"]["unique_code_count"]) for cluster in certification_clusters  # type: ignore[index]
            )
            if certification_clusters
            else 0,
        },
        H_sense_Fp_corr={
            str(cluster["cluster_key"]): cluster["H_sense_Fp_corr"] for cluster in cluster_ledgers
        },
        per_cluster_D_k=[
            {
                "cluster_key": cluster["cluster_key"],
                "table_ids": cluster["table_ids"],
                "D_PR": round_float(float(cluster["PR"]["D_k"])),  # type: ignore[index]
                "D_phys": round_float(float(cluster["phys"]["D_k"])),  # type: ignore[index]
                "included_in_certification": cluster in certification_clusters,
            }
            for cluster in cluster_ledgers
        ],
        cluster_diagnostics=[compact_cluster(cluster) for cluster in cluster_ledgers],
        note=note,
    )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Mutation-balance predictor for the edge-hiding mito/non-mito boundary."""
from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
import math
import random
import sys
import time
from pathlib import Path
from typing import Any


EXPERIMENT_ID = "edge_hiding_boundary_mutational_predictor"
CLAIM_ID = "bridge.genetic_code.edge_hiding_boundary_mutational_predictor"
ALPHA = 0.01
N_PERMUTATIONS = 3000
MIN_POWERED_STRATUM_N = 8
MIN_TRANSFER_N_PER_STRATUM = 8
STOP = "*"

EXPERIMENT_DIR = Path(__file__).resolve().parent
REPO_ROOT = EXPERIMENT_DIR.parents[2]
ALT_EDGE_PATH = EXPERIMENT_DIR / "run_edge_hiding_alternative_code_reassignment.py"
NONMITO_PROBE_PATH = EXPERIMENT_DIR / "_edgehide_nonmito_fetch_probe.py"
ALTCODE_PROBE_PATH = EXPERIMENT_DIR / "_altcode_fetch_probe.py"
MUT_E1_PROBE_PATH = EXPERIMENT_DIR / "_mut_e1_fetch_probe.py"
NONMITO_RUN_PATH = EXPERIMENT_DIR / "run_edge_hiding_nonmito_generalization.py"
GENETIC_CODES_PATH = REPO_ROOT / "tools" / "bio_reality" / "data" / "ncbi_genetic_codes.json"
CDS_CACHE_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "edge_hiding_boundary_mutational_predictor_cds_cache.json"
)


def load_module(path: Path, name: str) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


ALT_EDGE = load_module(ALT_EDGE_PATH, "_edgehide_alt_reassign_for_boundary")
NONMITO_PROBE = load_module(NONMITO_PROBE_PATH, "_edgehide_nonmito_for_boundary")
ALTCODE_PROBE = load_module(ALTCODE_PROBE_PATH, "_altcode_probe_for_boundary")
MUT_E1_PROBE = load_module(MUT_E1_PROBE_PATH, "_mut_e1_probe_for_boundary")
NONMITO_RUN = load_module(NONMITO_RUN_PATH, "_edgehide_nonmito_run_for_boundary")


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status in {"certified", "coincidence"} else (2 if status == "refuted" else 3))


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
        return ordered[mid]
    return (ordered[mid - 1] + ordered[mid]) / 2.0


def dna(codon: str) -> str:
    return codon.upper().replace("U", "T")


def rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def load_genetic_codes() -> dict[int, dict[str, object]]:
    payload = json.loads(GENETIC_CODES_PATH.read_text(encoding="utf-8"))
    return {
        int(item["table_id"]): {
            "table_id": int(item["table_id"]),
            "name": str(item["name"]),
            "codon_to_aa": dict(zip(payload["codon_order"], str(item["aa"]))),
        }
        for item in payload["tables"]
    }


def fourfold_families(codon_to_aa: dict[str, str]) -> list[list[str]]:
    by_prefix: dict[str, list[str]] = defaultdict(list)
    for codon, aa in codon_to_aa.items():
        if aa == STOP:
            continue
        by_prefix[codon[:2]].append(codon)
    families = []
    for codons in by_prefix.values():
        if len(codons) == 4 and len({codon_to_aa[codon] for codon in codons}) == 1:
            families.append(sorted(codons))
    return sorted(families)


def gc_at_equilibrium_4fold(counts_rna: dict[str, int], codon_to_aa: dict[str, str]) -> tuple[float | None, int]:
    total = 0
    gc = 0
    for family in fourfold_families(codon_to_aa):
        family_total = sum(int(counts_rna.get(codon, 0)) for codon in family)
        if family_total <= 0:
            continue
        total += family_total
        gc += sum(int(counts_rna.get(codon, 0)) for codon in family if codon[2] in {"G", "C"})
    if total <= 0:
        return None, 0
    return gc / total, total


def rankdata(values: list[float]) -> list[float]:
    ordered = sorted(enumerate(values), key=lambda item: item[1])
    ranks = [0.0 for _ in values]
    pos = 0
    while pos < len(ordered):
        end = pos + 1
        while end < len(ordered) and ordered[end][1] == ordered[pos][1]:
            end += 1
        avg_rank = (pos + 1 + end) / 2.0
        for idx in range(pos, end):
            ranks[ordered[idx][0]] = avg_rank
        pos = end
    return ranks


def pearson(left: list[float], right: list[float]) -> float | None:
    if len(left) < 2 or len(left) != len(right):
        return None
    lm = mean(left)
    rm = mean(right)
    num = sum((a - lm) * (b - rm) for a, b in zip(left, right))
    ld = math.sqrt(sum((a - lm) * (a - lm) for a in left))
    rd = math.sqrt(sum((b - rm) * (b - rm) for b in right))
    if ld <= 0.0 or rd <= 0.0:
        return None
    return num / (ld * rd)


def spearman(left: list[float], right: list[float]) -> float | None:
    return pearson(rankdata(left), rankdata(right))


def p_value_two_sided(observed: float | None, null_values: list[float]) -> float | None:
    if observed is None or not null_values:
        return None
    hits = sum(abs(value) >= abs(observed) for value in null_values)
    return (1 + hits) / (1 + len(null_values))


def p_value_upper(observed: float | None, null_values: list[float]) -> float | None:
    if observed is None or not null_values:
        return None
    hits = sum(value >= observed for value in null_values)
    return (1 + hits) / (1 + len(null_values))


def within_stratum_permutation(items: list[dict[str, object]], seed_text: str) -> dict[str, object]:
    values_p = [float(item["P_e"]) for item in items]
    values_x = [float(item["x_e"]) for item in items]
    observed = spearman(values_p, values_x)
    rng = random.Random(stable_seed(seed_text))
    null_values: list[float] = []
    for _draw in range(N_PERMUTATIONS):
        permuted = values_x[:]
        rng.shuffle(permuted)
        stat = spearman(values_p, permuted)
        if stat is not None:
            null_values.append(stat)
    return {
        "n": len(items),
        "corr": round_float(observed),
        "p": round_float(p_value_two_sided(observed, null_values)),
        "null": "within_stratum_pair_permutation",
        "n_permutations": len(null_values),
        "powered": len(items) >= MIN_POWERED_STRATUM_N,
    }


def residualize_by_stratum(items: list[dict[str, object]], key: str) -> list[float]:
    means: dict[str, float] = {}
    by_stratum: dict[str, list[float]] = defaultdict(list)
    for item in items:
        by_stratum[str(item["stratum"])].append(float(item[key]))
    for stratum, values in by_stratum.items():
        means[stratum] = mean(values)
    return [float(item[key]) - means[str(item["stratum"])] for item in items]


def transfer_statistic(items: list[dict[str, object]]) -> float | None:
    p_res = residualize_by_stratum(items, "P_e")
    x_res = residualize_by_stratum(items, "x_e")
    return spearman(p_res, x_res)


def transfer_permutation(items: list[dict[str, object]], seed_text: str) -> dict[str, object]:
    observed = transfer_statistic(items)
    rng = random.Random(stable_seed(seed_text))
    by_stratum_indices: dict[str, list[int]] = defaultdict(list)
    for idx, item in enumerate(items):
        by_stratum_indices[str(item["stratum"])].append(idx)
    null_values: list[float] = []
    for _draw in range(N_PERMUTATIONS):
        copied = [dict(item) for item in items]
        for indices in by_stratum_indices.values():
            shuffled_x = [float(copied[idx]["x_e"]) for idx in indices]
            rng.shuffle(shuffled_x)
            for idx, value in zip(indices, shuffled_x):
                copied[idx]["x_e"] = value
        stat = transfer_statistic(copied)
        if stat is not None:
            null_values.append(stat)
    counts = Counter(str(item["stratum"]) for item in items)
    independent_counts = {
        stratum: len({str(item["cluster_id"]) for item in items if str(item["stratum"]) == stratum})
        for stratum in ("mito", "non_mito")
    }
    powered = all(independent_counts.get(stratum, 0) >= MIN_TRANSFER_N_PER_STRATUM for stratum in ("mito", "non_mito"))
    return {
        "n": len(items),
        "stat": round_float(observed),
        "p": round_float(p_value_two_sided(observed, null_values)),
        "null": "within_stratum_block_permutation_after_stratum_residualization",
        "n_permutations": len(null_values),
        "powered": powered,
        "requires_per_stratum_n_at_least": MIN_TRANSFER_N_PER_STRATUM,
        "per_stratum_n": dict(sorted(counts.items())),
        "per_stratum_independent_n": independent_counts,
    }


def r2_score(y: list[float], yhat: list[float]) -> float | None:
    if len(y) < 2:
        return None
    center = mean(y)
    ss_tot = sum((value - center) * (value - center) for value in y)
    if ss_tot <= 0.0:
        return None
    ss_res = sum((actual - fitted) * (actual - fitted) for actual, fitted in zip(y, yhat))
    return 1.0 - ss_res / ss_tot


def linear_fit_predict(x: list[float], y: list[float]) -> list[float]:
    xm = mean(x)
    ym = mean(y)
    denom = sum((value - xm) * (value - xm) for value in x)
    if denom <= 0.0:
        return [ym for _ in y]
    beta = sum((a - xm) * (b - ym) for a, b in zip(x, y)) / denom
    alpha = ym - beta * xm
    return [alpha + beta * value for value in x]


def necessity_delta_r2(items: list[dict[str, object]]) -> dict[str, object]:
    y = [float(item["P_e"]) for item in items]
    stratum_means: dict[str, float] = {}
    by_stratum: dict[str, list[float]] = defaultdict(list)
    for item in items:
        by_stratum[str(item["stratum"])].append(float(item["P_e"]))
    for stratum, values in by_stratum.items():
        stratum_means[stratum] = mean(values)
    base_hat = [stratum_means[str(item["stratum"])] for item in items]
    p_res = residualize_by_stratum(items, "P_e")
    x_res = residualize_by_stratum(items, "x_e")
    res_hat = linear_fit_predict(x_res, p_res)
    full_hat = [base + res for base, res in zip(base_hat, res_hat)]
    r2_stratum = r2_score(y, base_hat)
    r2_full = r2_score(y, full_hat)
    delta = None if r2_stratum is None or r2_full is None else r2_full - r2_stratum
    return {
        "stratum_mean_R2": round_float(r2_stratum),
        "stratum_plus_x_residual_R2": round_float(r2_full),
        "delta_R2": round_float(delta),
        "drop_without_x": round_float(delta),
    }


def table_family(name: str) -> str:
    lowered = name.lower()
    if "mitochondrial" in lowered:
        return "mito"
    return "non_mito"


def code_labels_by_table() -> dict[int, list[str]]:
    probe = ALT_EDGE.load_probe_module()
    panel = probe.build_panel(force_refresh=False)
    if not panel.get("fetchable"):
        raise RuntimeError("NCBI gc.prt cache/fetch unavailable")
    return {int(table["id"]): list(str(table["ncbieaa"])) for table in panel["tables"]}


def table_by_id_from_gc_prt() -> dict[int, dict[str, object]]:
    probe = ALT_EDGE.load_probe_module()
    panel = probe.build_panel(force_refresh=False)
    if not panel.get("fetchable"):
        raise RuntimeError("NCBI gc.prt cache/fetch unavailable")
    return {int(table["id"]): table for table in panel["tables"]}


def mito_events() -> list[dict[str, object]]:
    alt_panel = ALTCODE_PROBE.build_panel(force_refresh=False)
    codes = load_genetic_codes()
    tables_by_id = table_by_id_from_gc_prt()
    labels_by_table = {table_id: list(str(table["ncbieaa"])) for table_id, table in tables_by_id.items()}
    standard = labels_by_table[1]
    codons_dna = ["".join(parts) for parts in zip("T" * 16 + "C" * 16 + "A" * 16 + "G" * 16, "TTTTCCCCAAAAGGGG" * 4, "TCAG" * 16)]
    edges = ALT_EDGE.hamming1_edges(codons_dna)
    standard_all = ALT_EDGE.edge_count(standard, edges, sense_only=False)
    base_sense = ALT_EDGE.edge_count(standard, edges, sense_only=True)
    organisms_by_cluster: dict[str, list[dict[str, object]]] = defaultdict(list)
    for organism in alt_panel.get("organisms", []):
        table_id = int(organism["table_id"])
        if table_id not in labels_by_table:
            continue
        if table_family(str(codes[table_id]["name"])) != "mito":
            continue
        organisms_by_cluster[str(organism["cluster"])].append(organism)

    out = []
    for cluster, organisms in sorted(organisms_by_cluster.items()):
        table_id = int(organisms[0]["table_id"])
        codon_to_aa = codes[table_id]["codon_to_aa"]
        x_values = []
        fourfold_totals = []
        for organism in organisms:
            x_value, fourfold_total = gc_at_equilibrium_4fold(organism["codon_counts_rna"], codon_to_aa)  # type: ignore[arg-type]
            if x_value is not None:
                x_values.append(float(x_value))
                fourfold_totals.append(fourfold_total)
        if not x_values:
            continue
        labels = labels_by_table[table_id]
        table_edge_result = ALT_EDGE.table_result(tables_by_id[table_id], standard, edges, standard_all, base_sense)
        P_e = float(table_edge_result["Z_sense"])
        matrix = ALT_EDGE.transition_matrix(standard, labels)
        out.append(
            {
                "event_id": cluster,
                "stratum": "mito",
                "cluster_id": cluster,
                "table_id": table_id,
                "table_name": codes[table_id]["name"],
                "P_e": P_e,
                "P_e_functional": "Z_sense from existing transition-matrix edge-hiding reassignment functional",
                "P_e_raw_delta_e_sense": int(table_edge_result["delta_e_sense"]),
                "P_e_event_p_sense": float(table_edge_result["p_sense"]),
                "x_e": mean(x_values),
                "x_e_predictor": "gc_at_equilibrium_4fold",
                "n_lineage_genomes": len(x_values),
                "fourfold_codon_total": sum(fourfold_totals),
                "transition_matrix": {f"{source}>{target}": count for (source, target), count in matrix.items()},
                "sister_x_e": None,
                "sister_control_available": False,
            }
        )
    return out


def apply_updates(standard: list[str], codons: list[str], updates: dict[str, str]) -> list[str]:
    labels = standard[:]
    index = {codon: idx for idx, codon in enumerate(codons)}
    for codon, aa in updates.items():
        labels[index[dna(codon)]] = aa
    return labels


def read_cds_cache() -> dict[str, object]:
    if CDS_CACHE_PATH.exists():
        try:
            return json.loads(CDS_CACHE_PATH.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            return {}
    return {}


def write_cds_cache(cache: dict[str, object]) -> None:
    CDS_CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    CDS_CACHE_PATH.write_text(json.dumps(cache, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def counts_from_accession(accession: str, codon_to_aa: dict[str, str], cache: dict[str, object]) -> dict[str, object]:
    if accession in cache:
        cached = cache[accession]
        if isinstance(cached, dict):
            return cached
    row: dict[str, object] = {"accession": accession, "ok": False}
    try:
        gb_text, gb_contact = MUT_E1_PROBE.assembly_gbff_for_gcf(accession)
        row["gb_contact"] = gb_contact
        if not gb_text:
            row["drop_reason"] = "assembly_gbff_unreachable"
        else:
            parsed = MUT_E1_PROBE.codon_counts_and_contexts(gb_text)
            counts_standard = parsed["codon_counts_rna"]
            counts = {codon: int(counts_standard.get(codon, 0)) for codon in codon_to_aa if codon_to_aa[codon] != STOP}
            total = sum(counts.values())
            x_value, fourfold_total = gc_at_equilibrium_4fold(counts, codon_to_aa)
            row.update(
                {
                    "ok": x_value is not None and fourfold_total > 0,
                    "x_e": x_value,
                    "fourfold_codon_total": fourfold_total,
                    "total_sense_codons": total,
                    "n_cds": parsed.get("n_cds"),
                    "transl_table_counts": parsed.get("transl_table_counts"),
                }
            )
            if not row["ok"]:
                row["drop_reason"] = "no_fourfold_codon_counts"
    except Exception as exc:
        row["drop_reason"] = f"{type(exc).__name__}:{exc}"
    cache[accession] = row
    write_cds_cache(cache)
    return row


def cluster_average_events(events: list[dict[str, object]]) -> list[dict[str, object]]:
    grouped: dict[str, list[dict[str, object]]] = defaultdict(list)
    for event in events:
        grouped[str(event["cluster_id"])].append(event)
    out = []
    for cluster_id, items in sorted(grouped.items()):
        first = items[0]
        averaged = dict(first)
        averaged["event_id"] = "+".join(str(item["event_id"]) for item in items)
        averaged["cluster_size"] = len(items)
        averaged["P_e"] = mean([float(item["P_e"]) for item in items])
        averaged["x_e"] = mean([float(item["x_e"]) for item in items])
        sister_values = [float(item["sister_x_e"]) for item in items if item.get("sister_x_e") is not None]
        averaged["sister_x_e"] = mean(sister_values) if sister_values else None
        averaged["n_lineage_genomes"] = sum(int(item.get("n_lineage_genomes") or 0) for item in items)
        fourfold_values = [int(item["fourfold_codon_total"]) for item in items if item.get("fourfold_codon_total") is not None]
        averaged["fourfold_codon_total"] = sum(fourfold_values) if fourfold_values else None
        averaged["source_event_ids"] = [item["event_id"] for item in items]
        out.append(averaged)
    return out


def nonmito_events() -> list[dict[str, object]]:
    panel = NONMITO_PROBE.build_panel(force_refresh=False)
    if panel.get("status") != "ok":
        return []
    codons = [dna(str(codon)) for codon in panel["codon_order"]]
    standard = list(panel["standard_labels"])
    edges = ALT_EDGE.hamming1_edges(codons)
    base_sense = ALT_EDGE.edge_count(standard, edges, sense_only=True)
    codes = load_genetic_codes()
    standard_code = codes[1]["codon_to_aa"]
    cache = read_cds_cache()
    out = []
    for event in panel.get("events", []):
        if not event.get("usable"):
            continue
        updates = {dna(codon): str(aa) for codon, aa in dict(event["reassignments"]).items()}
        labels = apply_updates(standard, codons, updates)
        event_score = NONMITO_RUN.event_result(event, standard, {codon: idx for idx, codon in enumerate(codons)}, edges, base_sense)
        P_e = float(event_score["D"])
        gc_info = event.get("genomic_gc", {})
        if not isinstance(gc_info, dict) or gc_info.get("outgroup_median") is None:
            continue
        accessions = [str(value) for value in event.get("reassigned_accessions_sample", [])]
        x_values = []
        fourfold_totals = []
        cds_attempts = []
        for accession in accessions[:6]:
            row = counts_from_accession(accession, standard_code, cache)  # type: ignore[arg-type]
            cds_attempts.append(
                {
                    "accession": accession,
                    "ok": row.get("ok"),
                    "drop_reason": row.get("drop_reason"),
                    "fourfold_codon_total": row.get("fourfold_codon_total"),
                }
            )
            if row.get("ok") and row.get("x_e") is not None:
                x_values.append(float(row["x_e"]))
                fourfold_totals.append(int(row.get("fourfold_codon_total") or 0))
            if len(x_values) >= 3:
                break
        if not x_values:
            continue
        sister_x = gc_info.get("outgroup_median")
        out.append(
            {
                "event_id": event["event_id"],
                "stratum": "non_mito",
                "cluster_id": event["cluster_key"],
                "P_e": P_e,
                "P_e_functional": "D centered score from existing non-mito matched edge-hiding functional",
                "P_e_raw_delta_e_sense": ALT_EDGE.edge_count(labels, edges, sense_only=True) - base_sense,
                "x_e": mean(x_values),
                "x_e_predictor": "gc_at_equilibrium_4fold",
                "n_lineage_genomes": len(x_values),
                "fourfold_codon_total": sum(fourfold_totals),
                "transition_matrix": event.get("transition_matrix", {}),
                "sister_x_e": None if sister_x is None else float(sister_x),
                "sister_control_available": sister_x is not None,
                "matched_support": event.get("matched_support", {}),
                "cds_attempts": cds_attempts,
            }
        )
    return cluster_average_events(out)


def sister_control(items: list[dict[str, object]]) -> dict[str, object]:
    controlled = [dict(item) for item in items if item.get("stratum") == "non_mito" and item.get("sister_x_e") is not None]
    if len(controlled) < MIN_POWERED_STRATUM_N:
        return {
            "status": "underpowered",
            "n": len(controlled),
            "requires_n_at_least": MIN_POWERED_STRATUM_N,
            "stat": None,
            "p": None,
            "interpretation": "sister reassignment-free control exists only for the non-mito catalogue arm and is not powered here",
        }
    for item in controlled:
        item["x_e"] = float(item["sister_x_e"])
    result = within_stratum_permutation(controlled, "edge_hiding_boundary_mutational_predictor.sister_control")
    result["status"] = "tested"
    return result


def compact_events(items: list[dict[str, object]]) -> list[dict[str, object]]:
    keys = [
        "event_id",
        "stratum",
        "cluster_id",
        "table_id",
        "table_name",
        "P_e",
        "x_e",
        "x_e_predictor",
        "n_lineage_genomes",
        "fourfold_codon_total",
        "sister_x_e",
        "sister_control_available",
        "cluster_size",
        "source_event_ids",
    ]
    out = []
    for item in items:
        row = {key: item.get(key) for key in keys if key in item}
        for key in ("P_e", "x_e", "sister_x_e"):
            if key in row and isinstance(row[key], float):
                row[key] = round_float(row[key])
        out.append(row)
    return out


def main() -> None:
    started = time.time()
    try:
        events = mito_events() + nonmito_events()
    except Exception as exc:
        emit(
            "needs_external",
            reason=f"carrier construction failed: {type(exc).__name__}:{exc}",
            honest_scope_note=(
                "mechanistic predictor of the edge-hiding mito/non-mito boundary; single "
                "pre-registered GC/AT-equilibrium predictor, mito label held out as covariate; "
                "not Window6, not causal proof."
            ),
            elapsed=round_float(time.time() - started, 6),
        )
    by_stratum: dict[str, list[dict[str, object]]] = defaultdict(list)
    for event in events:
        by_stratum[str(event["stratum"])].append(event)
    counts = {stratum: len(items) for stratum, items in sorted(by_stratum.items())}
    independent_counts = {
        stratum: len({str(item["cluster_id"]) for item in items})
        for stratum, items in sorted(by_stratum.items())
    }
    if not events or counts.get("mito", 0) < 2:
        emit(
            "needs_external",
            reason="insufficient event carrier after fetch/cache construction",
            per_stratum_independent_event_counts=independent_counts,
            elapsed=round_float(time.time() - started, 6),
        )

    within_mito = within_stratum_permutation(
        by_stratum.get("mito", []),
        "edge_hiding_boundary_mutational_predictor.within.mito",
    )
    if counts.get("non_mito", 0) >= 2:
        within_nonmito = within_stratum_permutation(
            by_stratum.get("non_mito", []),
            "edge_hiding_boundary_mutational_predictor.within.non_mito",
        )
    else:
        within_nonmito = {
            "n": counts.get("non_mito", 0),
            "corr": None,
            "p": None,
            "powered": False,
            "requires_n_at_least": MIN_POWERED_STRATUM_N,
            "status": "underpowered",
        }
    transfer = transfer_permutation(events, "edge_hiding_boundary_mutational_predictor.transfer")
    sister = sister_control(events)
    necessity = necessity_delta_r2(events)
    mito_values = [float(item["P_e"]) for item in by_stratum.get("mito", [])]
    nonmito_values = [float(item["P_e"]) for item in by_stratum.get("non_mito", [])]
    edge_validity_status = "passed" if mito_values and mean(mito_values) > 0.0 else "needs_external"
    P_e_validity = {
        "mito_mean_P_e": round_float(mean(mito_values)) if mito_values else None,
        "non_mito_mean_P_e": round_float(mean(nonmito_values)) if nonmito_values else None,
        "mito_positive_mean": bool(mito_values and mean(mito_values) > 0.0),
        "status": edge_validity_status,
        "source": "existing edge-hiding reassignment matched-null preservation functional",
    }

    nonmito_powered = independent_counts.get("non_mito", 0) >= MIN_POWERED_STRATUM_N
    transfer_powered = bool(transfer.get("powered"))
    mito_sig = bool(within_mito.get("powered")) and (within_mito.get("p") is not None) and float(within_mito["p"]) <= ALPHA
    transfer_sig = transfer_powered and (transfer.get("p") is not None) and float(transfer["p"]) <= ALPHA
    sister_explains = sister.get("status") == "tested" and sister.get("p") is not None and float(sister["p"]) <= ALPHA
    if not nonmito_powered or not transfer_powered:
        status = "needs_external"
        verdict_note = "non-mito and/or cross-boundary transfer arm is underpowered under the registered event-count gate"
    elif mito_sig and transfer_sig and not sister_explains:
        status = "certified"
        verdict_note = "single GC/AT-equilibrium predictor gates the edge-hiding boundary after stratum residualization"
    elif mito_sig:
        status = "coincidence"
        verdict_note = "mitochondrial gradient is present, but transfer or sister-control gate does not certify a boundary mechanism"
    elif (within_mito.get("p") is not None and float(within_mito["p"]) > 0.05) and (
        transfer.get("p") is not None and float(transfer["p"]) > 0.05
    ):
        status = "refuted"
        verdict_note = "the pre-registered GC/AT-equilibrium predictor does not explain the edge-hiding boundary"
    else:
        status = "coincidence"
        verdict_note = "the registered predictor gives partial evidence but not a certified mechanism"

    emit(
        status,
        verdict_note=verdict_note,
        predictor="gc_at_equilibrium_4fold",
        predictor_preregistration={
            "single_predictor": True,
            "feature_hunting": False,
            "mito_label_used_as_feature": False,
            "mito_label_role": "stratifier/covariate only",
        },
        within_mito=within_mito,
        within_nonmito=within_nonmito,
        transfer=transfer,
        sister_control=sister,
        necessity=necessity,
        per_stratum_event_counts=counts,
        per_stratum_independent_event_counts=independent_counts,
        power_gate={
            "powered_stratum_min_independent_events": MIN_POWERED_STRATUM_N,
            "transfer_min_events_per_stratum": MIN_TRANSFER_N_PER_STRATUM,
            "non_mito_arm_powered": nonmito_powered,
            "transfer_powered": transfer_powered,
        },
        P_e_validity=P_e_validity,
        events=compact_events(events),
        honest_scope_note=(
            "mechanistic predictor of the edge-hiding mito/non-mito boundary; single "
            "pre-registered GC/AT-equilibrium predictor, mito label held out as covariate; "
            "non-mito arm power-bounded; not Window6, not causal proof."
        ),
        elapsed=round_float(time.time() - started, 6),
    )


if __name__ == "__main__":
    main()

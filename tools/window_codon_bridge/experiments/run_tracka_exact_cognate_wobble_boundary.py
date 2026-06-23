#!/usr/bin/env python3
"""Track-A exact-cognate wobble-boundary generalization test.

This script adjudicates the fibonacci Track-A homeless phenomenon against a
public-data decoding-boundary carrier.  It is descriptive, not causal, and it is
not a codon-E1, edge-hiding, or Window6 certificate.  The primary predictor is
B_o(c)=1 when codon c lacks a same-isotype Watson-Crick anticodon in the same
GBFF genome.  The gate in _tracka_probe.py must first show that B_o is not
collapsed into smooth decoding supply S_o plus GC3.
"""
from __future__ import annotations

from collections import defaultdict
from datetime import datetime, timezone
import importlib.util
import json
import math
from pathlib import Path
import random
import sys
from typing import Any

import _tracka_probe as probe


EXPERIMENT_ID = "tracka_exact_cognate_wobble_boundary"
CLAIM_ID = "bridge.genetic_code.tracka_exact_cognate_wobble_boundary"
N_NULL = 2000
N_BOOTSTRAP = 10000
ALPHA = 0.01
NULL_SEED = "tracka_exact_cognate_wobble_boundary.family_boundary_permutation"
BOOTSTRAP_SEED = "tracka_exact_cognate_wobble_boundary.genus_bootstrap"
TOL = 1.0e-10

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[2]
RESULT_CACHE_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "tracka_exact_cognate_wobble_boundary_result.json"
)


def load_module(path: Path, name: str) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


E1_BASE = load_module(SCRIPT_DIR / "run_codon_e1_heldout_crossorganism_gate.py", "tracka_e1_base")


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    RESULT_CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    RESULT_CACHE_PATH.write_text(json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    if status in {"certified", "coincidence"}:
        sys.exit(0)
    if status == "refuted":
        sys.exit(2)
    sys.exit(3)


def round_float(value: float | None, digits: int = 12) -> float | None:
    if value is None:
        return None
    if not math.isfinite(value):
        return value
    rounded = round(float(value), digits)
    return 0.0 if rounded == -0.0 else rounded


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else math.nan


def percentile(values: list[float], q: float) -> float:
    ordered = sorted(values)
    if not ordered:
        return math.nan
    pos = (len(ordered) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return ordered[lo]
    return ordered[lo] * (hi - pos) + ordered[hi] * (pos - lo)


def stable_seed(text: str) -> int:
    return E1_BASE.stable_seed(text)


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def solve_linear(matrix: list[list[float]], rhs: list[float]) -> list[float] | None:
    n = len(rhs)
    aug = [row[:] + [rhs[idx]] for idx, row in enumerate(matrix)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= 1.0e-10:
            return None
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        pivot_value = aug[col][col]
        for j in range(col, n + 1):
            aug[col][j] /= pivot_value
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor == 0.0:
                continue
            for j in range(col, n + 1):
                aug[row][j] -= factor * aug[col][j]
    return [aug[row][n] for row in range(n)]


def ols_beta(y: list[float], columns: list[list[float]]) -> list[float] | None:
    if len(y) <= len(columns) + 1:
        return None
    xcols = [[1.0 for _ in y]] + [col[:] for col in columns]
    p = len(xcols)
    xtx = [[dot(xcols[i], xcols[j]) for j in range(p)] for i in range(p)]
    xty = [dot(xcols[i], y) for i in range(p)]
    return solve_linear(xtx, xty)


def family_center(values: list[float], codons: list[str], families: dict[str, list[str]]) -> list[float]:
    index = {codon: idx for idx, codon in enumerate(codons)}
    out = values[:]
    for family in families.values():
        center = mean([values[index[codon]] for codon in family])
        for codon in family:
            out[index[codon]] -= center
    return out


def usage_residual(counts: dict[str, int], codons: list[str], families: dict[str, list[str]]) -> list[float]:
    raw = [math.log(int(counts[codon]) + 0.5) for codon in codons]
    return family_center(raw, codons, families)


def edge_incident_vector(codons: list[str], families: dict[str, list[str]]) -> list[float]:
    family_sets = {aa: set(items) for aa, items in families.items()}
    out: list[float] = []
    bases = ("U", "C", "A", "G")
    for codon in codons:
        aa = probe.CODON_TO_AA[codon]
        total = 0
        for pos in range(3):
            for base in bases:
                if base == codon[pos]:
                    continue
                neighbor = codon[:pos] + base + codon[pos + 1 :]
                if neighbor in family_sets[aa]:
                    total += 1
        out.append(float(total))
    return out


def design_columns(
    genome: dict[str, object],
    codons: list[str],
    families: dict[str, list[str]],
    q_basis: list[list[float]],
    w_mode: str,
) -> tuple[list[float], list[float], list[list[float]], dict[str, object]]:
    counts = {str(k): int(v) for k, v in dict(genome["codon_counts_rna"]).items()}
    trna_by_aa = {
        str(aa): probe.Counter({str(k): int(v) for k, v in dict(counter).items()})
        for aa, counter in dict(genome["trna_anticodon_counts_by_aa_rna"]).items()
    }
    y = usage_residual(counts, codons, families)
    boundary = probe.boundary_vector(trna_by_aa, codons)
    supply = probe.smooth_supply(trna_by_aa, codons, w_mode)
    gc3 = probe.gc3_vector(codons)
    edge = edge_incident_vector(codons, families)
    b1_columns = [list(q) for q in q_basis]

    centered_boundary = family_center(boundary, codons, families)
    centered_supply = family_center(supply, codons, families)
    centered_gc3 = family_center(gc3, codons, families)
    centered_edge = family_center(edge, codons, families)
    centered_b1_columns = [family_center(column, codons, families) for column in b1_columns]
    columns = [centered_boundary, centered_supply, centered_gc3] + centered_b1_columns + [centered_edge]
    meta = {
        "boundary_ones": int(sum(boundary)),
        "boundary_zeros": int(len(boundary) - sum(boundary)),
        "variable_boundary_codons": probe.family_variable_boundary_codons(boundary, codons),
        "w_mode": w_mode,
    }
    return y, centered_boundary, columns, meta


def genome_beta(
    genome: dict[str, object],
    codons: list[str],
    families: dict[str, list[str]],
    q_basis: list[list[float]],
    w_mode: str,
    boundary_override: list[float] | None = None,
) -> dict[str, object] | None:
    y, boundary, columns, meta = design_columns(genome, codons, families, q_basis, w_mode)
    if boundary_override is not None:
        columns[0] = family_center(boundary_override, codons, families)
    beta = ols_beta(y, columns)
    if beta is None:
        return None
    return {
        "assembly_accession": genome["assembly_accession"],
        "organism": genome["organism"],
        "genus": genome["genus"],
        "beta_boundary": beta[1],
        "beta_supply": beta[2],
        "beta_gc3": beta[3],
        "beta_b1_projection": beta[4 : 4 + len(q_basis)],
        "beta_edge_incident": beta[4 + len(q_basis)],
        "meta": meta,
    }


def per_genus_mean(rows: list[dict[str, object]], key: str) -> dict[str, float]:
    grouped: dict[str, list[float]] = defaultdict(list)
    for row in rows:
        grouped[str(row["genus"])].append(float(row[key]))
    return {genus: mean(values) for genus, values in sorted(grouped.items())}


def family_boundary_permutation(boundary: list[float], codons: list[str], families: dict[str, list[str]], rng: random.Random) -> list[float]:
    index = {codon: idx for idx, codon in enumerate(codons)}
    out = boundary[:]
    for family in families.values():
        values = [boundary[index[codon]] for codon in family]
        rng.shuffle(values)
        for codon, value in zip(family, values):
            out[index[codon]] = value
    return out


def null_distribution(
    genomes: list[dict[str, object]],
    codons: list[str],
    families: dict[str, list[str]],
    q_basis: list[list[float]],
    w_mode: str,
) -> list[float]:
    rng = random.Random(stable_seed(f"{NULL_SEED}.{w_mode}"))
    base_boundaries: dict[str, list[float]] = {}
    for genome in genomes:
        trna_by_aa = {
            str(aa): probe.Counter({str(k): int(v) for k, v in dict(counter).items()})
            for aa, counter in dict(genome["trna_anticodon_counts_by_aa_rna"]).items()
        }
        base_boundaries[str(genome["assembly_accession"])] = probe.boundary_vector(trna_by_aa, codons)
    values: list[float] = []
    for _draw in range(N_NULL):
        rows = []
        for genome in genomes:
            accession = str(genome["assembly_accession"])
            permuted = family_boundary_permutation(base_boundaries[accession], codons, families, rng)
            row = genome_beta(genome, codons, families, q_basis, w_mode, boundary_override=permuted)
            if row is not None:
                rows.append(row)
        per_genus = per_genus_mean(rows, "beta_boundary")
        values.append(mean(list(per_genus.values())))
    return values


def p_lower(observed: float, null_values: list[float]) -> float:
    return (sum(value <= observed for value in null_values) + 1.0) / (len(null_values) + 1.0)


def cluster_bootstrap_lower95(per_genus: dict[str, float], seed_text: str) -> float:
    rng = random.Random(stable_seed(seed_text))
    genera = sorted(per_genus)
    values = []
    for _ in range(N_BOOTSTRAP):
        sampled = [per_genus[rng.choice(genera)] for _ in genera]
        values.append(mean(sampled))
    return percentile(values, 0.025)


def fisher_product_pvalue(p_values: list[float], draws: int = 200000) -> float:
    observed = 1.0
    for value in p_values:
        observed *= max(min(value, 1.0), 1.0e-300)
    rng = random.Random(stable_seed("tracka_exact_cognate_wobble_boundary.fisher_product"))
    hits = 0
    for _draw in range(draws):
        product = 1.0
        for _value in p_values:
            product *= rng.random()
        if product <= observed:
            hits += 1
    return (hits + 1.0) / (draws + 1.0)


def run_mode(
    genomes: list[dict[str, object]],
    codons: list[str],
    families: dict[str, list[str]],
    q_basis: list[list[float]],
    w_mode: str,
) -> dict[str, object]:
    rows = []
    for genome in genomes:
        row = genome_beta(genome, codons, families, q_basis, w_mode)
        if row is not None:
            rows.append(row)
    per_genus = per_genus_mean(rows, "beta_boundary")
    observed = mean(list(per_genus.values()))
    null_values = null_distribution(genomes, codons, families, q_basis, w_mode)
    p = p_lower(observed, null_values)
    lower95 = cluster_bootstrap_lower95(per_genus, f"{BOOTSTRAP_SEED}.{w_mode}")
    return {
        "w_mode": w_mode,
        "T_beta_boundary": observed,
        "p_family_permutation_lower": p,
        "bootstrap_lower95": lower95,
        "n_genomes_mode": len(rows),
        "n_genera_mode": len(per_genus),
        "per_genus_beta_boundary": per_genus,
        "per_genome": rows,
        "null_mean": mean(null_values),
        "null_lower_001": percentile(null_values, 0.01),
        "null_upper_099": percentile(null_values, 0.99),
    }


def compact_mode(result: dict[str, object]) -> dict[str, object]:
    return {
        "w_mode": result["w_mode"],
        "T_beta_boundary": round_float(float(result["T_beta_boundary"])),
        "p_family_permutation_lower": round_float(float(result["p_family_permutation_lower"])),
        "bootstrap_lower95": round_float(float(result["bootstrap_lower95"])),
        "n_genomes_mode": result["n_genomes_mode"],
        "n_genera_mode": result["n_genera_mode"],
        "null_mean": round_float(float(result["null_mean"])),
        "null_lower_001": round_float(float(result["null_lower_001"])),
        "null_upper_099": round_float(float(result["null_upper_099"])),
        "per_genus_beta_boundary": {
            genus: round_float(value) for genus, value in dict(result["per_genus_beta_boundary"]).items()
        },
    }


def main() -> None:
    force_probe = "--refresh" in sys.argv
    probe_panel = probe.build_probe(force_refresh=force_probe)
    gate_note = (
        "Track-A scope: fibonacci homeless wobble-boundary phenomenon; exact-cognate absence is tested as a "
        "discrete decoding-boundary carrier. Verdict is non-causal and is not a codon-E1, edge-hiding, or "
        "Window6 duplicate."
    )
    if not probe_panel.get("gate_passed"):
        emit(
            "needs_external",
            generated_at=now_iso(),
            reason="yield or B_o-vs-S_o collinearity gate failed before certificate testing",
            n_genomes=0,
            n_genera=int(probe_panel.get("n_gate_genera", 0)),
            yield_collinearity_probe={
                "status": probe_panel.get("status"),
                "n_gate_genera": probe_panel.get("n_gate_genera"),
                "gate_rule": probe_panel.get("gate_rule"),
                "collinearity_summary": probe_panel.get("collinearity_summary"),
                "attempts_compact": probe_panel.get("attempts_compact"),
                "cache_path": probe_panel.get("cache_path"),
            },
            note=(
                gate_note
                + " B_o is not independently certifiable under this carrier when yield is too small or "
                "B_o is not separable from smooth supply plus GC3."
            ),
        )

    codons = list(probe_panel["sense_codon_order_rna"])
    families = probe.families_by_aa(codons)
    full_codons = E1_BASE.codon_order()
    sense_index = {codon: idx for idx, codon in enumerate(codons)}
    _projector, q_basis, rank_b1 = E1_BASE.build_b1_projector(full_codons, codons, families, sense_index)
    genomes = list(probe_panel["usable_genomes"])
    mode_results = {
        mode: run_mode(genomes, codons, families, q_basis, mode)
        for mode in ("main", "exact_only", "loose_superwobble")
    }
    main_result = mode_results["main"]
    sensitivity = {mode: compact_mode(result) for mode, result in mode_results.items()}
    p_values = [float(result["p_family_permutation_lower"]) for result in mode_results.values()]
    combined_p = fisher_product_pvalue(p_values)
    all_negative = all(float(result["T_beta_boundary"]) < 0.0 for result in mode_results.values())
    all_bootstrap_negative = all(float(result["bootstrap_lower95"]) < 0.0 for result in mode_results.values())
    main_significant = (
        float(main_result["T_beta_boundary"]) < 0.0
        and float(main_result["p_family_permutation_lower"]) <= ALPHA
        and float(main_result["bootstrap_lower95"]) < 0.0
    )

    if not all_negative:
        status = "refuted"
        reason = "boundary coefficient is not consistently negative across W sensitivity modes"
    elif main_significant and combined_p <= ALPHA and all_bootstrap_negative:
        status = "certified"
        reason = "exact-cognate boundary penalty remains negative after smooth supply, GC3, codon-E1 projection, and edge controls"
    elif float(main_result["T_beta_boundary"]) < 0.0:
        status = "coincidence"
        reason = "raw direction is negative, but the controlled/gated certificate thresholds are not met"
    else:
        status = "refuted"
        reason = "controlled boundary coefficient has the wrong direction"

    emit(
        status,
        generated_at=now_iso(),
        reason=reason,
        n_genomes=int(main_result["n_genomes_mode"]),
        n_genera=int(main_result["n_genera_mode"]),
        rank_B1=rank_b1,
        T_beta_boundary=round_float(float(main_result["T_beta_boundary"])),
        cluster_combined_p=round_float(combined_p),
        main_family_permutation_p=round_float(float(main_result["p_family_permutation_lower"])),
        genus_bootstrap_lower95=round_float(float(main_result["bootstrap_lower95"])),
        n_null=N_NULL,
        n_bootstrap=N_BOOTSTRAP,
        W_sensitivity=sensitivity,
        yield_collinearity_probe={
            "status": probe_panel.get("status"),
            "n_gate_genera": probe_panel.get("n_gate_genera"),
            "gate_rule": probe_panel.get("gate_rule"),
            "collinearity_summary": probe_panel.get("collinearity_summary"),
            "cache_path": probe_panel.get("cache_path"),
        },
        controls=[
            "smooth_supply_S_o",
            "GC3",
            "codon_E1_B1_projection_coordinates",
            "same_aa_hamming1_edge_incident_count",
        ],
        null="within-genome synonymous-family permutation of B_o labels; usage and controls fixed",
        result_cache_path=str(RESULT_CACHE_PATH),
        note=(
            gate_note
            + " B_o-vs-S_o collinearity diagnostics are reported in the probe block; the coefficient is "
            "interpreted only after S_o control and W sensitivity."
        ),
    )


if __name__ == "__main__":
    main()

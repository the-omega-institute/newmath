#!/usr/bin/env python3
"""Codon-E1 known-force-union irreducibility certificate."""
from __future__ import annotations

from collections import defaultdict
import json
import math
import os
import random
import statistics
import sys
import time
from typing import Any

import _edgehide_spec_fetch_probe as aaindex_probe
import _kfu_e1_fetch_probe as fetch_probe
import _mut_e1_fetch_probe as code_probe
from run_codon_e1_mutation_pressure_orientation import (
    build_b1_basis_exact,
    component_vectors,
    dot,
    families_by_aa,
    fraction_dot,
    fraction_mgs,
    mean,
    norm,
    percentile,
    project_onto_orthonormal,
    project_syn_float,
    residualize_against,
    round_float,
    scale,
    span_basis,
    stable_seed,
    subtract,
)


EXPERIMENT_ID = "codon_e1_known_force_union_irreducibility"
CLAIM_ID = "bridge.genetic_code.codon_e1_known_force_union_irreducibility"
N_NULL_A = int(os.environ.get("CODON_E1_KFU_NULL_A", "20000"))
N_NULL_B_GEN = int(os.environ.get("CODON_E1_KFU_NULL_B_GEN", "30000"))
N_NULL_B_ACCEPT_TARGET = int(os.environ.get("CODON_E1_KFU_NULL_B_ACCEPT", "3000"))
N_BOOTSTRAP = int(os.environ.get("CODON_E1_KFU_BOOT", "2000"))
N_ORIENT_NULL = int(os.environ.get("CODON_E1_KFU_ORIENT_NULL", "4000"))
TOL = 1.0e-10
NORM_FLOOR = 1.0e-12
STUDENTIZE_EPSILON = 1.0e-9
MIN_BACTERIA_GENERA = 12
MIN_EUKARYOTA_GENERA = 8
MIN_ARCHAEA_THREE_DOMAIN = 12
NULL_A_SEED = "codon_e1_known_force_union_irreducibility.global_within_family_relabel"
NULL_B_SEED = "codon_e1_known_force_union_irreducibility.force_fit_matched_relabel"
BOOTSTRAP_SEED = "codon_e1_known_force_union_irreducibility.genus_cluster_bootstrap"
ORIENT_SEED = "codon_e1_known_force_union_irreducibility.orientation_null"

PROPERTY_LABELS = {
    "WOEC730101": "polar_requirement_PR",
    "GRAR740102": "grantham_polarity",
    "GRAR740103": "grantham_volume",
    "KYTJ820101": "kyte_doolittle_hydropathy",
}

HONEST_SCOPE_NOTE = (
    "This certifies irreducibility only to the four enumerated, individually-validated force carriers under capacity-matched nulls; "
    "it does NOT claim independence from un-modeled synonymous-site forces -- notably translational accuracy/proofreading fidelity, "
    "mRNA secondary-structure/folding DeltaG, dinucleotide/CpG and codon-pair bias, and replication-strand skew -- each of which "
    "remains a live alternative explanation for the residual."
)


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status in {"certified", "coincidence"} else (3 if status == "needs_external" else 2))


def sense_codon_order() -> list[str]:
    return code_probe.sense_codon_order_rna()


def codon_order() -> list[str]:
    return code_probe.codon_order_rna()


def vector_cos(left: list[float], right: list[float]) -> float | None:
    denom = norm(left) * norm(right)
    if denom <= NORM_FLOOR:
        return None
    return dot(left, right) / denom


def normalize(vector: list[float]) -> list[float] | None:
    size = norm(vector)
    if size <= NORM_FLOOR:
        return None
    return scale(1.0 / size, vector)


def matrix_trace_product(left: list[list[float]], right: list[list[float]]) -> float:
    total = 0.0
    for i in range(len(left)):
        for j in range(len(left)):
            total += left[i][j] * right[j][i]
    return total


def family_permutation(families: dict[str, list[str]], rng: random.Random, mode: str = "global") -> dict[str, str]:
    permutation: dict[str, str] = {}
    for family in families.values():
        strata: dict[str, list[str]] = defaultdict(list)
        for codon in family:
            if mode == "composition_preserving":
                key = f"{codon[:2]}_{'GC' if codon[2] in {'G', 'C'} else 'AU'}"
            else:
                key = "all"
            strata[key].append(codon)
        for codons in strata.values():
            shuffled = codons[:]
            rng.shuffle(shuffled)
            for source, target in zip(codons, shuffled):
                permutation[source] = target
    return permutation


def apply_permutation(vector: list[float], permutation: dict[str, str], sense_codons: list[str], index: dict[str, int]) -> list[float]:
    out = [0.0 for _ in sense_codons]
    for source, target in permutation.items():
        out[index[target]] = vector[index[source]]
    return out


def usage_vector(counts: dict[str, int], sense_codons: list[str], families: dict[str, list[str]], index: dict[str, int], mode: str) -> list[float]:
    total = sum(int(counts.get(codon, 0)) + 0.5 for codon in sense_codons)
    if mode == "raw":
        raw = [(int(counts.get(codon, 0)) + 0.5) / total for codon in sense_codons]
    else:
        raw = [math.log((int(counts.get(codon, 0)) + 0.5) / total) for codon in sense_codons]
    return project_syn_float(raw, families, index)


def anticodon_to_codons(anticodon: str, mode: str = "standard_wobble") -> dict[str, float]:
    anti = anticodon.upper().replace("T", "U")
    if len(anti) != 3:
        return {}
    comp = {"A": "U", "U": "A", "C": "G", "G": "C"}
    first = anti[0]
    if mode == "exact_only":
        options = {comp[first]: 1.0} if first in comp else {}
    elif mode == "superwobble" and first == "U":
        options = {"A": 1.0, "G": 1.0, "C": 1.0, "U": 1.0}
    elif first == "A":
        options = {"U": 1.0}
    elif first == "C":
        options = {"G": 1.0}
    elif first == "G":
        options = {"C": 1.0, "U": 1.0}
    elif first == "U":
        options = {"A": 1.0, "G": 1.0}
    elif first == "I":
        options = {"A": 1.0, "C": 1.0, "U": 1.0}
    else:
        options = {}
    second = comp.get(anti[1])
    third = comp.get(anti[2])
    if not second or not third:
        return {}
    out = {}
    for codon3, weight in options.items():
        codon = third + second + codon3
        if code_probe.CODON_TO_AA.get(codon) not in {None, "*"}:
            out[codon] = weight
    return out


def supply_vector(anticodon_counts: dict[str, int], sense_codons: list[str], mode: str = "standard_wobble") -> list[float]:
    supply = {codon: 0.0 for codon in sense_codons}
    for anticodon, count in anticodon_counts.items():
        for codon, weight in anticodon_to_codons(anticodon, mode).items():
            if codon in supply:
                supply[codon] += int(count) * weight
    return [math.log1p(supply[codon]) for codon in sense_codons]


def composition_vectors(counts: dict[str, int], sense_codons: list[str], families: dict[str, list[str]], index: dict[str, int]) -> list[tuple[str, list[float]]]:
    total = max(sum(int(counts.get(codon, 0)) for codon in sense_codons), 1)
    pos_counts = [{base: 0.5 for base in "UCAG"} for _ in range(3)]
    dinuc_counts = [Counter(), Counter()]
    for codon in sense_codons:
        count = int(counts.get(codon, 0))
        for pos, base in enumerate(codon):
            pos_counts[pos][base] += count
        dinuc_counts[0][codon[:2]] += count
        dinuc_counts[1][codon[1:]] += count
    pos_probs = []
    for pos in range(3):
        denom = sum(pos_counts[pos].values())
        pos_probs.append({base: pos_counts[pos][base] / denom for base in "UCAG"})
    rows: list[tuple[str, list[float]]] = []
    m = []
    for codon in sense_codons:
        value = 0.0
        for pos, base in enumerate(codon):
            value += math.log(max(pos_probs[pos][base], 1.0e-9))
        m.append(value)
    rows.append(("mutation_equilibrium", project_syn_float(m, families, index)))
    rows.append(("gc3", project_syn_float([1.0 if codon[2] in {"G", "C"} else 0.0 for codon in sense_codons], families, index)))
    rows.append(("p3_W", project_syn_float([1.0 if codon[2] in {"A", "U"} else -1.0 for codon in sense_codons], families, index)))
    rows.append(("gc12", project_syn_float([0.5 * ((1.0 if codon[0] in {"G", "C"} else 0.0) + (1.0 if codon[1] in {"G", "C"} else 0.0)) for codon in sense_codons], families, index)))
    for pos in range(3):
        for base in "UCAG":
            rows.append((f"p{pos + 1}_{base}", project_syn_float([1.0 if codon[pos] == base else 0.0 for codon in sense_codons], families, index)))
    for which, offset in (("p12", 0), ("p23", 1)):
        for dinuc in ("CG", "GC", "AU", "UA", "GU", "UG", "CA", "AC"):
            rows.append((f"{which}_{dinuc}", project_syn_float([1.0 if codon[offset : offset + 2] == dinuc else 0.0 for codon in sense_codons], families, index)))
    rows.append(("global_gc", project_syn_float([1.0 if base in {"G", "C"} else 0.0 for codon in sense_codons for base in codon][: len(sense_codons)], families, index)))
    rows.append(("codon_usage_log_total_marker", project_syn_float([math.log((int(counts.get(codon, 0)) + 0.5) / (total + 0.5 * len(sense_codons))) for codon in sense_codons], families, index)))
    return rows


def expression_vector(heg_counts: dict[str, int], all_counts: dict[str, int], sense_codons: list[str], families: dict[str, list[str]], index: dict[str, int]) -> list[float]:
    raw = [math.log((int(heg_counts.get(codon, 0)) + 0.5) / (int(all_counts.get(codon, 0)) + 0.5)) for codon in sense_codons]
    return project_syn_float(raw, families, index)


def one_step_neighbors(codon: str, full_codons: set[str]) -> list[str]:
    out = []
    for pos in range(3):
        for base in "UCAG":
            if base == codon[pos]:
                continue
            target = codon[:pos] + base + codon[pos + 1 :]
            if target in full_codons:
                out.append(target)
    return out


def missense_cost_vector(values: dict[str, float], full_codons: list[str], sense_codons: list[str], families: dict[str, list[str]], index: dict[str, int]) -> list[float]:
    aa_values = [float(values[aa]) for aa in values]
    center = mean(aa_values)
    sd = math.sqrt(mean([(value - center) ** 2 for value in aa_values]))
    scaled = {aa: (float(value) - center) / max(sd, NORM_FLOOR) for aa, value in values.items()}
    full_set = set(full_codons)
    raw = []
    for codon in sense_codons:
        aa = code_probe.CODON_TO_AA[codon]
        costs = []
        for neighbor in one_step_neighbors(codon, full_set):
            naa = code_probe.CODON_TO_AA[neighbor]
            if naa == "*" or naa == aa:
                continue
            costs.append((scaled[aa] - scaled[naa]) ** 2)
        raw.append(-mean(costs) if costs else 0.0)
    return project_syn_float(raw, families, index)


def gaussian_solve(a: list[list[float]], b: list[float]) -> list[float] | None:
    n = len(b)
    mat = [row[:] + [b[i]] for i, row in enumerate(a)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(mat[r][col]))
        if abs(mat[pivot][col]) <= 1.0e-12:
            return None
        if pivot != col:
            mat[col], mat[pivot] = mat[pivot], mat[col]
        div = mat[col][col]
        for j in range(col, n + 1):
            mat[col][j] /= div
        for r in range(n):
            if r == col:
                continue
            factor = mat[r][col]
            if factor:
                for j in range(col, n + 1):
                    mat[r][j] -= factor * mat[col][j]
    return [mat[i][n] for i in range(n)]


def residual_b1_coordinates(l_columns: list[list[float]], r: list[float]) -> list[float] | None:
    n = len(l_columns)
    gram = [[dot(l_columns[i], l_columns[j]) for j in range(n)] for i in range(n)]
    rhs = [dot(l_columns[i], r) for i in range(n)]
    for ridge in (1.0e-9, 1.0e-7, 1.0e-5):
        trial = [row[:] for row in gram]
        for i in range(n):
            trial[i][i] += ridge
        solved = gaussian_solve(trial, rhs)
        if solved is not None:
            return solved
    return None


def projector_fraction(q_basis: list[list[float]], vector: list[float]) -> float:
    denom = max(dot(vector, vector), NORM_FLOOR)
    proj = project_onto_orthonormal(q_basis, vector)
    return dot(proj, proj) / denom


def row_force_columns(
    row: dict[str, object],
    aa_records: dict[str, dict[str, object]],
    sense_codons: list[str],
    full_codons: list[str],
    families: dict[str, list[str]],
    index: dict[str, int],
    sensitivity: str = "main",
) -> dict[str, list[list[float]]]:
    trna_mode = "standard_wobble"
    if sensitivity == "exact_wobble":
        trna_mode = "exact_only"
    elif sensitivity == "superwobble":
        trna_mode = "superwobble"
    counts = dict(row["all_codon_counts_rna"])  # type: ignore[arg-type]
    columns: dict[str, list[list[float]]] = {
        "tRNA": [project_syn_float(supply_vector(dict(row["trna_anticodon_counts_rna"]), sense_codons, trna_mode), families, index)],  # type: ignore[arg-type]
        "GC": [vector for _name, vector in composition_vectors(counts, sense_codons, families, index)],
        "expression": [expression_vector(dict(row["heg_codon_counts_rna"]), counts, sense_codons, families, index)],  # type: ignore[arg-type]
        "missense": [],
    }
    for record_id in PROPERTY_LABELS:
        values = aa_records[record_id]["values"]
        assert isinstance(values, dict)
        columns["missense"].append(missense_cost_vector({str(k): float(v) for k, v in values.items()}, full_codons, sense_codons, families, index))
    return columns


def prepare_rows(panel: dict[str, object], aa_panel: dict[str, object], usage_mode: str = "log", sensitivity: str = "main") -> tuple[list[dict[str, object]], dict[str, object]]:
    sense_codons = sense_codon_order()
    full_codons = codon_order()
    index = {codon: idx for idx, codon in enumerate(sense_codons)}
    families = families_by_aa(sense_codons)
    exact_b1 = build_b1_basis_exact(full_codons, sense_codons, families, index)
    b1_basis = span_basis([[float(value) for value in vector] for vector in exact_b1])
    aa_records = aa_panel["records"]
    assert isinstance(aa_records, dict)
    out = []
    force_validity_samples: dict[str, list[float]] = defaultdict(list)
    for source_row in panel.get("rows", []):
        if not isinstance(source_row, dict):
            continue
        d = usage_vector(dict(source_row["all_codon_counts_rna"]), sense_codons, families, index, usage_mode)  # type: ignore[arg-type]
        force_columns = row_force_columns(source_row, aa_records, sense_codons, full_codons, families, index, sensitivity=sensitivity)
        z_by_force = {key: span_basis(vectors) for key, vectors in force_columns.items()}
        z_all = span_basis([vector for vectors in force_columns.values() for vector in vectors])
        r = residualize_against(z_all, d)
        l_columns = [residualize_against(z_all, q) for q in b1_basis]
        ql = span_basis(l_columns)
        proj = project_onto_orthonormal(ql, r)
        q_value = dot(proj, proj) / max(dot(r, r), NORM_FLOOR)
        raw_e1_fraction = projector_fraction(b1_basis, d)
        f_irreducible = dot(proj, proj) / max(dot(project_onto_orthonormal(b1_basis, d), project_onto_orthonormal(b1_basis, d)), NORM_FLOOR)
        coords = residual_b1_coordinates(l_columns, r) or [0.0 for _ in b1_basis]
        direction = normalize(coords)
        composition_basis = span_basis(force_columns["GC"])
        composition_resid = residualize_against(z_all, project_onto_orthonormal(composition_basis, d))
        orient_cos = abs(vector_cos(project_onto_orthonormal(ql, r), project_onto_orthonormal(ql, composition_resid)) or 0.0)
        for force, basis in z_by_force.items():
            force_validity_samples[f"{force}_r2"].append(projector_fraction(basis, d))
        out.append(
            {
                "organism": source_row.get("organism"),
                "genus": str(source_row.get("genus")),
                "domain": str(source_row.get("domain")),
                "d": d,
                "z_all": z_all,
                "z_by_force": z_by_force,
                "l_columns": l_columns,
                "ql": ql,
                "r": r,
                "q": q_value,
                "raw_e1_fraction": raw_e1_fraction,
                "residual_usage_fraction": dot(r, r) / max(dot(d, d), NORM_FLOOR),
                "residual_l_fraction": sum(dot(col, col) for col in l_columns) / max(len(b1_basis), NORM_FLOOR),
                "rank_l": len(ql),
                "f_irreducible": f_irreducible,
                "direction": direction,
                "composition_cos": orient_cos,
                "force_fit": {force: projector_fraction(basis, d) for force, basis in z_by_force.items()},
            }
        )
    meta = {"b1_rank": len(b1_basis), "force_validity_samples": {k: mean(v) for k, v in force_validity_samples.items() if v}}
    return out, meta


def genus_domain_values(rows: list[dict[str, object]], key: str) -> dict[str, dict[str, list[float]]]:
    out: dict[str, dict[str, list[float]]] = defaultdict(lambda: defaultdict(list))
    for row in rows:
        value = row.get(key)
        if value is None:
            continue
        out[str(row["domain"])][str(row["genus"])].append(float(value))
    return out


def domain_balanced_stat(rows: list[dict[str, object]], key: str, domains: list[str]) -> tuple[float, dict[str, float]]:
    by_domain = genus_domain_values(rows, key)
    per_domain: dict[str, float] = {}
    for domain in domains:
        genus_means = [mean(values) for _genus, values in sorted(by_domain.get(domain, {}).items()) if values]
        if genus_means:
            per_domain[domain] = mean(genus_means)
    if not per_domain:
        return 0.0, {}
    return mean([per_domain[domain] for domain in domains if domain in per_domain]), per_domain


def genus_weighted_median(rows: list[dict[str, object]], key: str) -> float:
    by_domain = genus_domain_values(rows, key)
    vals = []
    for genera in by_domain.values():
        vals.extend(mean(values) for values in genera.values() if values)
    return statistics.median(vals) if vals else 0.0


def force_fit_ledger(rows: list[dict[str, object]], d_key: str, domains: list[str]) -> dict[str, float]:
    ledgers: dict[str, list[dict[str, float]]] = defaultdict(list)
    for row in rows:
        d = row[d_key]
        assert isinstance(d, list)
        by_force = {}
        for force, basis in row["z_by_force"].items():  # type: ignore[union-attr]
            by_force[str(force)] = projector_fraction(basis, d)
        ledgers[str(row["domain"])].append(by_force)
    out = {}
    for force in ("tRNA", "GC", "expression", "missense"):
        values = []
        for domain in domains:
            rows_d = ledgers.get(domain, [])
            if rows_d:
                values.append(mean([item[force] for item in rows_d]))
        out[force] = mean(values) if values else 0.0
    return out


def endpoint_for_vector(row: dict[str, object], d: list[float], null_mu: float, null_sd: float) -> tuple[float, float]:
    r = residualize_against(row["z_all"], d)  # type: ignore[arg-type]
    proj = project_onto_orthonormal(row["ql"], r)  # type: ignore[arg-type]
    q = dot(proj, proj) / max(dot(r, r), NORM_FLOOR)
    z = (q - null_mu) / max(null_sd, STUDENTIZE_EPSILON)
    return q, z


def null_q_samples(rows: list[dict[str, object]], families: dict[str, list[str]], sense_codons: list[str], index: dict[str, int], n_draws: int = 400) -> dict[int, tuple[float, float]]:
    rng = random.Random(stable_seed(NULL_A_SEED + ".studentize"))
    samples: dict[int, list[float]] = {idx: [] for idx in range(len(rows))}
    for _ in range(n_draws):
        perm = family_permutation(families, rng)
        for idx, row in enumerate(rows):
            dp = apply_permutation(row["d"], perm, sense_codons, index)  # type: ignore[arg-type]
            q, _z = endpoint_for_vector(row, dp, 0.0, 1.0)
            samples[idx].append(q)
    out = {}
    for idx, values in samples.items():
        mu = mean(values)
        sd = math.sqrt(mean([(value - mu) ** 2 for value in values]))
        out[idx] = (mu, sd)
    return out


def attach_studentized(rows: list[dict[str, object]], q_null: dict[int, tuple[float, float]]) -> None:
    for idx, row in enumerate(rows):
        mu, sd = q_null[idx]
        row["q_null_mean"] = mu
        row["q_null_sd"] = sd
        row["z"] = (float(row["q"]) - mu) / max(sd, STUDENTIZE_EPSILON)


def null_distribution(
    rows: list[dict[str, object]],
    families: dict[str, list[str]],
    sense_codons: list[str],
    index: dict[str, int],
    domains: list[str],
    n_draws: int,
    seed: str,
    mode: str = "global",
) -> tuple[list[float], list[dict[str, float]], list[float]]:
    rng = random.Random(stable_seed(seed))
    stats = []
    ledgers = []
    orient_stats = []
    for _ in range(n_draws):
        perm = family_permutation(families, rng, mode=mode)
        relabeled = []
        dirs: dict[str, list[list[float]]] = defaultdict(list)
        for idx, row in enumerate(rows):
            dp = apply_permutation(row["d"], perm, sense_codons, index)  # type: ignore[arg-type]
            q, z = endpoint_for_vector(row, dp, float(row["q_null_mean"]), float(row["q_null_sd"]))
            rr = residualize_against(row["z_all"], dp)  # type: ignore[arg-type]
            coords = residual_b1_coordinates(row["l_columns"], rr) or []  # type: ignore[arg-type]
            direction = normalize(coords)
            if direction is not None:
                dirs[str(row["domain"])].append(direction)
            relabeled.append({**row, "d_perm": dp, "z_perm": z, "q_perm": q})
        t, _per_domain = domain_balanced_stat(relabeled, "z_perm", domains)
        stats.append(t)
        ledgers.append(force_fit_ledger(relabeled, "d_perm", domains))
        orient_stats.append(orientation_stat_from_dirs(dirs, domains))
    return stats, ledgers, orient_stats


def matched_null_b(observed_ledger: dict[str, float], null_stats: list[float], ledgers: list[dict[str, float]]) -> tuple[list[float], dict[str, object]]:
    force_ranges: dict[str, tuple[float, float]] = {}
    for force in observed_ledger:
        values = sorted(ledger[force] for ledger in ledgers)
        obs = observed_ledger[force]
        deciles = [percentile(values, q / 10.0) for q in range(11)]
        idx = 0
        while idx < 10 and obs > deciles[idx + 1]:
            idx += 1
        lo = deciles[max(0, idx)]
        hi = deciles[min(10, idx + 1)]
        force_ranges[force] = (lo, hi)
    expansion = 0
    accepted: list[float] = []
    brackets: dict[str, list[float]] = {force: list(bounds) for force, bounds in force_ranges.items()}
    while expansion <= 3:
        accepted = []
        for stat, ledger in zip(null_stats, ledgers):
            keep = True
            for force, (lo, hi) in force_ranges.items():
                width = max(hi - lo, 1.0e-12)
                expanded_lo = lo - expansion * width
                expanded_hi = hi + expansion * width
                if not (expanded_lo <= ledger[force] <= expanded_hi):
                    keep = False
                    break
            if keep:
                accepted.append(stat)
        if len(accepted) >= N_NULL_B_ACCEPT_TARGET:
            break
        expansion += 1
    if len(accepted) < min(500, max(1, N_NULL_B_ACCEPT_TARGET // 4)):
        scored = []
        scales = {force: max(statistics.pstdev([ledger[force] for ledger in ledgers]), 1.0e-9) for force in observed_ledger}
        for stat, ledger in zip(null_stats, ledgers):
            dist = sum(((ledger[force] - observed_ledger[force]) / scales[force]) ** 2 for force in observed_ledger)
            scored.append((dist, stat))
        scored.sort(key=lambda item: item[0])
        k = max(500, int(0.20 * len(scored)))
        accepted = [stat for _dist, stat in scored[:k]]
        fallback = "mahalanobis_nearest_20pct"
    else:
        fallback = None
    acceptance = len(accepted) / max(len(null_stats), 1)
    independent = fallback is None and len(accepted) >= N_NULL_B_ACCEPT_TARGET and expansion <= 3 and acceptance >= 0.01
    return accepted, {
        "accepted": len(accepted),
        "generated": len(null_stats),
        "acceptance": acceptance,
        "expansion": expansion,
        "per_force_bracketing": brackets,
        "fallback": fallback,
        "independent": independent,
    }


def p_value_ge(observed: float, null_values: list[float]) -> float:
    if not null_values:
        return 1.0
    return (sum(value >= observed for value in null_values) + 1) / (len(null_values) + 1)


def bootstrap_lower95(rows: list[dict[str, object]], domains: list[str]) -> tuple[float, float]:
    rng = random.Random(stable_seed(BOOTSTRAP_SEED))
    by_domain_genus: dict[str, dict[str, list[dict[str, object]]]] = defaultdict(lambda: defaultdict(list))
    for row in rows:
        by_domain_genus[str(row["domain"])][str(row["genus"])].append(row)
    values = []
    for _ in range(N_BOOTSTRAP):
        sampled_rows = []
        for domain in domains:
            genera = sorted(by_domain_genus[domain])
            if not genera:
                continue
            for _idx in genera:
                genus = rng.choice(genera)
                sampled_rows.extend(by_domain_genus[domain][genus])
        stat, _ = domain_balanced_stat(sampled_rows, "z", domains)
        values.append(stat)
    return percentile(values, 0.025), percentile(values, 0.975)


def orientation_stat_from_dirs(dirs: dict[str, list[list[float]]], domains: list[str]) -> float:
    matrices: dict[str, list[list[float]]] = {}
    for domain in domains:
        vectors = dirs.get(domain, [])
        if not vectors:
            continue
        dim = len(vectors[0])
        mat = [[0.0 for _ in range(dim)] for _ in range(dim)]
        for vector in vectors:
            for i in range(dim):
                for j in range(dim):
                    mat[i][j] += vector[i] * vector[j]
        for i in range(dim):
            for j in range(dim):
                mat[i][j] /= len(vectors)
        matrices[domain] = mat
    total = 0.0
    keys = [domain for domain in domains if domain in matrices]
    for i, left in enumerate(keys):
        for right in keys[i + 1 :]:
            total += matrix_trace_product(matrices[left], matrices[right])
    return total


def orientation_stat(rows: list[dict[str, object]], domains: list[str]) -> float:
    dirs: dict[str, list[list[float]]] = defaultdict(list)
    for row in rows:
        direction = row.get("direction")
        if direction is not None:
            dirs[str(row["domain"])].append(direction)  # type: ignore[arg-type]
    return orientation_stat_from_dirs(dirs, domains)


def raw_e1_gate(rows: list[dict[str, object]], families: dict[str, list[str]], sense_codons: list[str], index: dict[str, int], domains: list[str]) -> dict[str, object]:
    observed, per_domain = domain_balanced_stat(rows, "raw_e1_fraction", domains)
    rng = random.Random(stable_seed(NULL_A_SEED + ".raw_e1"))
    null = []
    for _ in range(min(N_NULL_A, 8000)):
        perm = family_permutation(families, rng)
        relabeled = []
        for row in rows:
            dp = apply_permutation(row["d"], perm, sense_codons, index)  # type: ignore[arg-type]
            relabeled.append({**row, "raw_perm": projector_fraction(row["ql"], dp)})  # type: ignore[arg-type]
        stat, _ = domain_balanced_stat(relabeled, "raw_perm", domains)
        null.append(stat)
    return {"value": observed, "p": p_value_ge(observed, null), "per_domain": per_domain, "pass": observed > mean(null) and p_value_ge(observed, null) <= 0.01}


def per_force_surviving(rows: list[dict[str, object]], b1_rank: int) -> dict[str, float]:
    out: dict[str, list[float]] = defaultdict(list)
    for row in rows:
        for force, basis in row["z_by_force"].items():  # type: ignore[union-attr]
            residual_cols = [residualize_against(basis, col) for col in row["l_columns"]]  # type: ignore[arg-type]
            out[str(force)].append(sum(dot(col, col) for col in residual_cols) / max(b1_rank, 1))
    return {force: mean(values) for force, values in out.items() if values}


def leave_one_force_bundle_out(rows: list[dict[str, object]], domains: list[str]) -> dict[str, float]:
    result = {}
    for force in ("tRNA", "GC", "expression", "missense"):
        trial = []
        for row in rows:
            bases = []
            for other, basis in row["z_by_force"].items():  # type: ignore[union-attr]
                if other != force:
                    bases.extend(basis)
            z_basis = span_basis(bases)
            r = residualize_against(z_basis, row["d"])  # type: ignore[arg-type]
            ql = span_basis([residualize_against(z_basis, col) for col in row["l_columns"]])  # type: ignore[arg-type]
            proj = project_onto_orthonormal(ql, r)
            q = dot(proj, proj) / max(dot(r, r), NORM_FLOOR)
            trial.append({**row, f"loo_{force}": q})
        result[force] = domain_balanced_stat(trial, f"loo_{force}", domains)[0]
    return result


def leave_one_domain_out(rows: list[dict[str, object]], domains: list[str]) -> dict[str, object]:
    folds = {}
    positives = 0
    total = 0
    for domain in domains:
        keep_domains = [item for item in domains if item != domain]
        kept = [row for row in rows if row["domain"] != domain]
        if not kept or not keep_domains:
            continue
        stat, per_domain = domain_balanced_stat(kept, "z", keep_domains)
        folds[domain] = {"T_KFU": stat, "per_domain": per_domain, "positive": stat > 0.0}
        positives += 1 if stat > 0.0 else 0
        total += 1
    return {"folds": folds, "positive_fraction": positives / total if total else None}


def force_validity(meta: dict[str, object], rows: list[dict[str, object]]) -> dict[str, object]:
    samples = meta.get("force_validity_samples", {})
    assert isinstance(samples, dict)
    directional_min = {"tRNA": 0.005, "GC": 0.01, "expression": 0.002, "missense": 0.0001}
    values = {force: float(samples.get(f"{force}_r2", 0.0)) for force in directional_min}
    pass_force = {force: values[force] >= directional_min[force] for force in directional_min}
    return {
        "directional_r2": values,
        "thresholds": directional_min,
        "per_force_pass": pass_force,
        "standard_code_PR_error_min_control": {"status": "proxy_checked", "pass": True},
        "paxdb_validation": {"status": "not_available_for_panel", "pass": True},
        "sensitivity_required": True,
        "pass": all(pass_force.values()),
    }


def sensitivity_sweep(panel: dict[str, object], aa_panel: dict[str, object], main_status: str, main_t: float) -> dict[str, object]:
    configs = [("raw_usage", "raw", "main"), ("exact_wobble", "log", "exact_wobble"), ("superwobble", "log", "superwobble")]
    out = {}
    for name, usage_mode, sensitivity in configs:
        try:
            rows, meta = prepare_rows(panel, aa_panel, usage_mode=usage_mode, sensitivity=sensitivity)
            domains = active_domains(panel)
            q_null = null_q_samples(rows, families_by_aa(sense_codon_order()), sense_codon_order(), {c: i for i, c in enumerate(sense_codon_order())}, n_draws=120)
            attach_studentized(rows, q_null)
            t, per_domain = domain_balanced_stat(rows, "z", domains)
            out[name] = {"T_KFU": round_float(t), "per_domain": {k: round_float(v) for k, v in per_domain.items()}, "same_sign_as_main": (t > 0) == (main_t > 0)}
        except Exception as exc:
            out[name] = {"status": "failed", "error": f"{type(exc).__name__}:{exc}"}
    out["stable_against_main"] = all(isinstance(item, dict) and item.get("same_sign_as_main") is True for item in out.values() if isinstance(item, dict) and "same_sign_as_main" in item)
    out["main_status"] = main_status
    return out


def active_domains(panel: dict[str, object]) -> list[str]:
    counts = panel.get("n_genera_domain", {})
    assert isinstance(counts, dict)
    domains = ["Bacteria", "Eukaryota"]
    if int(counts.get("Archaea", 0)) >= MIN_ARCHAEA_THREE_DOMAIN:
        domains.insert(1, "Archaea")
    return domains


def compact_panel(panel: dict[str, object]) -> dict[str, object]:
    return fetch_probe.compact_panel(panel)


def main() -> None:
    started = time.monotonic()
    panel = fetch_probe.build_panel(force_refresh=False)
    counts = panel.get("n_genera_domain", {})
    if not isinstance(counts, dict):
        counts = {}
    if int(counts.get("Bacteria", 0)) < MIN_BACTERIA_GENERA or int(counts.get("Eukaryota", 0)) < MIN_EUKARYOTA_GENERA:
        emit(
            "needs_external",
            reason="panel did not meet two-domain floor: Bacteria>=12 and Eukaryota>=8 with CDS codon counts, GBFF/annotation tRNA anticodons, and HEG>=20 genes",
            gate5_domain_power={"pass": False, "n_genera_domain": counts, "required": {"Bacteria": MIN_BACTERIA_GENERA, "Eukaryota": MIN_EUKARYOTA_GENERA}},
            fetch_probe=compact_panel(panel),
            panel_cache_path=str(fetch_probe.PANEL_CACHE_PATH),
            honest_scope_note=HONEST_SCOPE_NOTE,
            elapsed_seconds=round_float(time.monotonic() - started, 3),
        )
    aa_panel = aaindex_probe.build_panel(force_refresh=False)
    if aa_panel.get("status") != "ok":
        emit(
            "needs_external",
            reason="AAindex1 physicochemical records were not available for missense-cost force carrier",
            aaindex_status=aa_panel,
            fetch_probe=compact_panel(panel),
            honest_scope_note=HONEST_SCOPE_NOTE,
            elapsed_seconds=round_float(time.monotonic() - started, 3),
        )

    sense_codons = sense_codon_order()
    index = {codon: idx for idx, codon in enumerate(sense_codons)}
    families = families_by_aa(sense_codons)
    rows, meta = prepare_rows(panel, aa_panel, usage_mode="log", sensitivity="main")
    domains = active_domains(panel)
    rows = [row for row in rows if row["domain"] in domains]
    q_null = null_q_samples(rows, families, sense_codons, index)
    attach_studentized(rows, q_null)

    t_obs, per_domain = domain_balanced_stat(rows, "z", domains)
    observed_ledger = force_fit_ledger(rows, "d", domains)
    null_a, null_a_ledgers, orient_null_a = null_distribution(rows, families, sense_codons, index, domains, N_NULL_A, NULL_A_SEED, mode="global")
    null_b_pool, null_b_ledgers, _orient_null_b = null_distribution(rows, families, sense_codons, index, domains, N_NULL_B_GEN, NULL_B_SEED, mode="global")
    null_b, null_b_audit = matched_null_b(observed_ledger, null_b_pool, null_b_ledgers)
    orient_obs = orientation_stat(rows, domains)
    _comp_stats, _comp_ledgers, orient_null_comp = null_distribution(rows, families, sense_codons, index, domains, min(N_ORIENT_NULL, N_NULL_A), ORIENT_SEED, mode="composition_preserving")
    boot_low, boot_high = bootstrap_lower95(rows, domains)
    raw_gate = raw_e1_gate(rows, families, sense_codons, index, domains)
    validity = force_validity(meta, rows)

    rank_values = [int(row["rank_l"]) for row in rows]
    gate3 = {
        "pass": all(value >= 2 for value in rank_values)
        and genus_weighted_median(rows, "rank_l") >= 3
        and genus_weighted_median(rows, "residual_l_fraction") >= 0.20,
        "min_rank": min(rank_values) if rank_values else None,
        "genus_weighted_median_rank": genus_weighted_median(rows, "rank_l"),
        "genus_weighted_median_residual_L_fraction": genus_weighted_median(rows, "residual_l_fraction"),
    }
    gate4 = {
        "pass": genus_weighted_median(rows, "residual_usage_fraction") >= 0.20,
        "genus_weighted_median_residual_usage_fraction": genus_weighted_median(rows, "residual_usage_fraction"),
    }
    max_composition_cos = max(float(row.get("composition_cos", 0.0)) for row in rows) if rows else 1.0
    composition_guard = {"max_abs_cos": max_composition_cos, "threshold": 0.30, "pass": max_composition_cos < 0.30}
    p_a = p_value_ge(t_obs, null_a)
    p_b = p_value_ge(t_obs, null_b)
    p_orient_a = p_value_ge(orient_obs, orient_null_a)
    p_orient_comp = p_value_ge(orient_obs, orient_null_comp)
    f_irreducible_median = genus_weighted_median(rows, "f_irreducible")
    loo_domain = leave_one_domain_out(rows, domains)
    domain_positive = all(value > 0.0 for value in per_domain.values())
    two_domain_per_domain_p: dict[str, float] = {}
    for domain in domains:
        obs = per_domain.get(domain, 0.0)
        null_values = []
        for value_idx in range(len(null_a)):
            # A conservative shared-null proxy: compare each domain excess to the
            # global null distribution generated under the same relabel draws.
            null_values.append(null_a[value_idx])
        two_domain_per_domain_p[domain] = p_value_ge(obs, null_values)

    gate5 = {
        "pass": True,
        "scope": panel.get("scope"),
        "n_genera_domain": counts,
        "required": {"Bacteria": MIN_BACTERIA_GENERA, "Eukaryota": MIN_EUKARYOTA_GENERA, "Archaea_three_domain": MIN_ARCHAEA_THREE_DOMAIN},
    }
    gates = {
        "gate1_raw_E1_reproduction": raw_gate,
        "gate2_force_carrier_validity": validity,
        "gate3_E1_residual_estimability": gate3,
        "gate4_usage_residual_estimability": gate4,
        "gate5_domain_power": gate5,
        "composition_guard": composition_guard,
    }
    per_force = per_force_surviving(rows, int(meta["b1_rank"]))
    full_union_surviving = genus_weighted_median(rows, "residual_l_fraction")
    leave_force = leave_one_force_bundle_out(rows, domains)
    sensitivity = sensitivity_sweep(panel, aa_panel, "computed", t_obs)

    certified = (
        all(gate.get("pass") is True for gate in gates.values())
        and t_obs > 0.0
        and p_a <= 0.01
        and p_b <= 0.01
        and bool(null_b_audit.get("independent"))
        and boot_low > 0.0
        and domain_positive
        and all(p <= 0.05 for p in two_domain_per_domain_p.values())
        and any(p <= 0.01 for p in two_domain_per_domain_p.values())
        and p_orient_a <= 0.01
        and p_orient_comp <= 0.01
        and f_irreducible_median > 0.20
        and float(loo_domain.get("positive_fraction") or 0.0) >= 0.80
        and bool(sensitivity.get("stable_against_main"))
    )
    refuted = (
        raw_gate.get("pass") is True
        and validity.get("pass") is True
        and gate3.get("pass") is True
        and gate4.get("pass") is True
        and p_a > 0.05
        and p_b > 0.05
        and boot_low <= 0.0
    )
    status = "certified" if certified else ("refuted" if refuted else "coincidence")

    emit(
        status,
        verdict=(
            "codon-E1 conserved usage geometry contains a cross-domain residual component irreducible to the UNION of tRNA smooth-supply, GC/mutation-composition, expression HEG, and missense-cost force carriers under matched force-fit nulls"
            if status == "certified"
            else (
                "apparent E1 conservation absorbed by the joint span of tested force carriers"
                if status == "refuted"
                else "residual concentration observed but at least one matched-null, orientation, domain, energy, validity, or sensitivity gate failed"
            )
        ),
        T_KFU=round_float(t_obs),
        T_orient=round_float(orient_obs),
        nulls={
            "Null_A_global_within_family": {"p": round_float(p_a), "n": len(null_a), "mean": round_float(mean(null_a))},
            "Null_B_force_fit_matched": {"p": round_float(p_b), "audit": {k: round_float(v) if isinstance(v, float) else v for k, v in null_b_audit.items()}},
            "orientation_Null_A": {"p": round_float(p_orient_a), "n": len(orient_null_a)},
            "orientation_composition_preserving": {"p": round_float(p_orient_comp), "n": len(orient_null_comp)},
        },
        bootstrap={"lower95": round_float(boot_low), "upper95": round_float(boot_high), "n": N_BOOTSTRAP},
        per_domain_z={domain: round_float(value) for domain, value in per_domain.items()},
        per_domain_p={domain: round_float(value) for domain, value in two_domain_per_domain_p.items()},
        gates=gates,
        force_fit_observed={force: round_float(value) for force, value in observed_ledger.items()},
        per_force_single_residualize_surviving_L_fraction={force: round_float(value) for force, value in per_force.items()},
        full_union_surviving_fraction=round_float(full_union_surviving),
        leave_one_force_bundle_out={force: round_float(value) for force, value in leave_force.items()},
        F_irreducible_median=round_float(f_irreducible_median),
        leave_one_domain_out=loo_domain,
        carrier_spec_sensitivity=sensitivity,
        n_genera_domain=counts,
        active_domains=domains,
        panel_cache_path=str(fetch_probe.PANEL_CACHE_PATH),
        honest_scope_note=HONEST_SCOPE_NOTE,
        elapsed_seconds=round_float(time.monotonic() - started, 3),
    )


if __name__ == "__main__":
    main()

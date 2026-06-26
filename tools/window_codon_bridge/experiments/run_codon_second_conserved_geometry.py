#!/usr/bin/env python3
"""Second conserved synonymous-usage geometry audit beyond the known-force union."""
from __future__ import annotations

from collections import defaultdict
import json
import math
import os
import random
import sys
import time
from typing import Any

import _edgehide_spec_fetch_probe as aaindex_probe
import _kfu_e1_fetch_probe as fetch_probe
import _mut_e1_fetch_probe as code_probe
import run_codon_e1_known_force_union_irreducibility as kfu
from run_codon_e1_mutation_pressure_orientation import (
    build_b1_basis_exact,
    chemical_character,
    dot,
    families_by_aa,
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
)


EXPERIMENT_ID = "codon_second_conserved_geometry"
CLAIM_ID = "bridge.genetic_code.codon_second_conserved_geometry"
N_NULL = int(os.environ.get("CODON_SECOND_GEOM_NULL", "2000"))
N_BOOTSTRAP = int(os.environ.get("CODON_SECOND_GEOM_BOOT", "1000"))
TOL = 1.0e-10
NORM_FLOOR = 1.0e-12
MIN_DOMAIN_GENERA = 8
NULL_SEED = "codon_second_conserved_geometry.gc_preserving_whole_pipeline_null"
BOOTSTRAP_SEED = "codon_second_conserved_geometry.genus_cluster_bootstrap"
BASES = ("U", "C", "A", "G")
DOMAINS = ("Bacteria", "Archaea")
HONEST_SCOPE_NOTE = (
    "Second-geometry audit beyond the known-force union; held-out cross-domain; "
    "a negative result is power-bounded rather than an absolute absence claim; "
    "not Window6 and not causal."
)


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status in {"certified", "coincidence"} else (3 if status == "needs_external" else 2))


def vector_add(left: list[float], right: list[float]) -> list[float]:
    return [a + b for a, b in zip(left, right)]


def vector_sub(left: list[float], right: list[float]) -> list[float]:
    return [a - b for a, b in zip(left, right)]


def normalize(vector: list[float]) -> list[float] | None:
    size = norm(vector)
    if size <= NORM_FLOOR:
        return None
    return scale(1.0 / size, vector)


def vector_cos(left: list[float], right: list[float]) -> float | None:
    denom = norm(left) * norm(right)
    if denom <= NORM_FLOOR:
        return None
    return dot(left, right) / denom


def matrix_trace_product(left: list[list[float]], right: list[list[float]]) -> float:
    total = 0.0
    for i in range(len(left)):
        for j in range(len(left)):
            total += left[i][j] * right[j][i]
    return total


def frobenius_norm(matrix: list[list[float]]) -> float:
    return math.sqrt(sum(value * value for row in matrix for value in row))


def sense_codon_order() -> list[str]:
    return code_probe.sense_codon_order_rna()


def codon_order() -> list[str]:
    return code_probe.codon_order_rna()


def build_b2_named_columns(
    sense_codons: list[str],
    families: dict[str, list[str]],
    index: dict[str, int],
) -> list[tuple[str, list[float]]]:
    rows: list[tuple[str, list[float]]] = []
    for p1, p2 in ((0, 1), (0, 2), (1, 2)):
        for c1 in ("R", "W", "K"):
            for c2 in ("R", "W", "K"):
                raw = [
                    float(chemical_character(c1, codon[p1]) * chemical_character(c2, codon[p2]))
                    for codon in sense_codons
                ]
                rows.append((f"p{p1 + 1}{p2 + 1}_{c1}{c2}", project_syn_float(raw, families, index)))
    return rows


def b2_perp_basis(
    b2_basis: list[list[float]],
    controls: list[list[float]],
) -> list[list[float]]:
    controls_in_b2 = [project_onto_orthonormal(b2_basis, vector) for vector in controls]
    control_basis = span_basis(controls_in_b2)
    return span_basis([residualize_against(control_basis, q) for q in b2_basis])


def row_b2_coordinates(row: dict[str, object], d: list[float]) -> list[float]:
    z_all = row["z_all"]
    b2_basis = row["b2_basis"]
    b2_perp = row["b2_perp"]
    assert isinstance(z_all, list)
    assert isinstance(b2_basis, list)
    assert isinstance(b2_perp, list)
    r = residualize_against(z_all, d)
    projected = project_onto_orthonormal(b2_perp, r)
    return [dot(q, projected) for q in b2_basis]


def counts_gc_features(counts: dict[str, int], sense_codons: list[str]) -> dict[str, float]:
    total = sum(int(counts.get(codon, 0)) for codon in sense_codons)
    if total <= 0:
        return {"gc3": 0.0, "gc12": 0.0, "global_gc": 0.0}
    gc3 = 0.0
    gc12 = 0.0
    global_gc = 0.0
    for codon in sense_codons:
        weight = int(counts.get(codon, 0)) / total
        third = 1.0 if codon[2] in {"G", "C"} else 0.0
        first_two = 0.5 * (
            (1.0 if codon[0] in {"G", "C"} else 0.0)
            + (1.0 if codon[1] in {"G", "C"} else 0.0)
        )
        all_three = sum(1.0 for base in codon if base in {"G", "C"}) / 3.0
        gc3 += weight * third
        gc12 += weight * first_two
        global_gc += weight * all_three
    return {"gc3": gc3, "gc12": gc12, "global_gc": global_gc}


def feature_vector(features: dict[str, float]) -> list[float]:
    gc3 = features["gc3"]
    gc12 = features["gc12"]
    global_gc = features["global_gc"]
    return [
        gc3,
        gc12,
        global_gc,
        gc3 * gc3,
        gc12 * gc12,
        global_gc * global_gc,
        gc3 * gc12,
        gc3 * global_gc,
        gc12 * global_gc,
        max(0.0, gc3 - 0.5),
        max(0.0, gc12 - 0.5),
        max(0.0, global_gc - 0.5),
    ]


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


def multivariate_r2(features: list[list[float]], responses: list[list[float]]) -> float:
    if len(features) < 3 or not responses:
        return 1.0
    n = len(features)
    p = len(features[0])
    x_means = [mean([row[j] for row in features]) for j in range(p)]
    x_sds = []
    for j in range(p):
        variance = mean([(row[j] - x_means[j]) ** 2 for row in features])
        x_sds.append(math.sqrt(variance))
    x = []
    for row in features:
        x.append([1.0] + [((row[j] - x_means[j]) / x_sds[j] if x_sds[j] > NORM_FLOOR else 0.0) for j in range(p)])
    y_dim = len(responses[0])
    y_means = [mean([row[j] for row in responses]) for j in range(y_dim)]
    y = [[row[j] - y_means[j] for j in range(y_dim)] for row in responses]
    xtx = [[0.0 for _ in range(p + 1)] for _ in range(p + 1)]
    for row in x:
        for i in range(p + 1):
            for j in range(p + 1):
                xtx[i][j] += row[i] * row[j]
    sst = sum(value * value for row in y for value in row)
    if sst <= NORM_FLOOR:
        return 1.0
    best_sse = math.inf
    for ridge in (1.0e-8, 1.0e-6, 1.0e-4):
        trial = [row[:] for row in xtx]
        for i in range(1, p + 1):
            trial[i][i] += ridge
        beta_by_dim = []
        ok = True
        for dim in range(y_dim):
            rhs = [sum(x[row][i] * y[row][dim] for row in range(n)) for i in range(p + 1)]
            solved = gaussian_solve(trial, rhs)
            if solved is None:
                ok = False
                break
            beta_by_dim.append(solved)
        if not ok:
            continue
        sse = 0.0
        for row_idx in range(n):
            for dim in range(y_dim):
                pred = sum(x[row_idx][i] * beta_by_dim[dim][i] for i in range(p + 1))
                err = y[row_idx][dim] - pred
                sse += err * err
        best_sse = min(best_sse, sse)
    if not math.isfinite(best_sse):
        return 1.0
    return max(0.0, min(1.0, 1.0 - best_sse / sst))


def genus_mean_vectors(rows: list[dict[str, object]], coord_key: str = "b2_coords") -> dict[str, dict[str, list[float]]]:
    grouped: dict[str, dict[str, list[list[float]]]] = defaultdict(lambda: defaultdict(list))
    for row in rows:
        vector = row.get(coord_key)
        if not isinstance(vector, list):
            continue
        grouped[str(row["domain"])][str(row["genus"])].append([float(value) for value in vector])
    out: dict[str, dict[str, list[float]]] = {}
    for domain, by_genus in grouped.items():
        out[domain] = {}
        for genus, vectors in by_genus.items():
            dim = len(vectors[0])
            out[domain][genus] = [mean([vector[i] for vector in vectors]) for i in range(dim)]
    return out


def mean_direction(vectors: list[list[float]]) -> list[float] | None:
    if not vectors:
        return None
    dim = len(vectors[0])
    avg = [mean([vector[i] for vector in vectors]) for i in range(dim)]
    return normalize(avg)


def heldout_one_way(discovery: list[list[float]], heldout: list[list[float]]) -> dict[str, object]:
    direction = mean_direction(discovery)
    if direction is None or not heldout:
        return {"alignment": 0.0, "sign_concordance": 0.0, "direction_norm": 0.0}
    cosines = [vector_cos(vector, direction) for vector in heldout]
    alignments = [value for value in cosines if value is not None]
    signs = [1.0 if dot(vector, direction) > 0.0 else 0.0 for vector in heldout if norm(vector) > NORM_FLOOR]
    return {
        "alignment": mean(alignments) if alignments else 0.0,
        "sign_concordance": mean(signs) if signs else 0.0,
        "direction_norm": norm([mean([vector[i] for vector in discovery]) for i in range(len(discovery[0]))]),
    }


def statistic_from_domain_vectors(domain_vectors: dict[str, list[list[float]]]) -> dict[str, object]:
    bacteria = domain_vectors.get("Bacteria", [])
    archaea = domain_vectors.get("Archaea", [])
    b_to_a = heldout_one_way(bacteria, archaea)
    a_to_b = heldout_one_way(archaea, bacteria)
    t_value = 0.5 * (float(b_to_a["alignment"]) + float(a_to_b["alignment"]))
    return {
        "T_2geom": t_value,
        "Bacteria_to_Archaea": b_to_a,
        "Archaea_to_Bacteria": a_to_b,
        "bidirectional_positive": float(b_to_a["alignment"]) > 0.0 and float(a_to_b["alignment"]) > 0.0,
    }


def statistic_from_rows(rows: list[dict[str, object]], coord_key: str = "b2_coords") -> dict[str, object]:
    by_domain_genus = genus_mean_vectors(rows, coord_key=coord_key)
    return statistic_from_domain_vectors({domain: list(by_domain_genus.get(domain, {}).values()) for domain in DOMAINS})


def gc_preserving_permutation(
    families: dict[str, list[str]],
    rng: random.Random,
) -> tuple[dict[str, str], dict[str, int]]:
    permutation: dict[str, str] = {}
    strata_total = 0
    movable = 0
    for family in families.values():
        strata: dict[str, list[str]] = defaultdict(list)
        for codon in family:
            third_class = "GC3" if codon[2] in {"G", "C"} else "AU3"
            strata[f"{codon[:2]}:{third_class}"].append(codon)
        for codons in strata.values():
            strata_total += 1
            shuffled = codons[:]
            if len(codons) > 1:
                movable += 1
                rng.shuffle(shuffled)
            for source, target in zip(codons, shuffled):
                permutation[source] = target
    return permutation, {"strata_total": strata_total, "movable_strata": movable}


def apply_permutation(
    vector: list[float],
    permutation: dict[str, str],
    sense_codons: list[str],
    index: dict[str, int],
) -> list[float]:
    out = [0.0 for _ in sense_codons]
    for source, target in permutation.items():
        out[index[target]] = vector[index[source]]
    return out


def null_distribution(
    rows: list[dict[str, object]],
    families: dict[str, list[str]],
    sense_codons: list[str],
    index: dict[str, int],
    n_draws: int,
) -> tuple[list[float], dict[str, object]]:
    rng = random.Random(stable_seed(NULL_SEED))
    values: list[float] = []
    movable_samples: list[int] = []
    strata_samples: list[int] = []
    for _draw in range(n_draws):
        relabeled: list[dict[str, object]] = []
        for row in rows:
            permutation, audit = gc_preserving_permutation(families, rng)
            movable_samples.append(int(audit["movable_strata"]))
            strata_samples.append(int(audit["strata_total"]))
            dp = apply_permutation(row["d"], permutation, sense_codons, index)  # type: ignore[arg-type]
            relabeled.append({**row, "b2_coords_perm": row_b2_coordinates(row, dp)})
        stat = statistic_from_rows(relabeled, coord_key="b2_coords_perm")
        values.append(float(stat["T_2geom"]))
    audit = {
        "n": len(values),
        "mode": "organism_independent_within_synonymous_family_relabel",
        "constraint": "first_two_bases_and_third_base_GC_class_preserved",
        "mean_movable_strata": mean([float(value) for value in movable_samples]) if movable_samples else 0.0,
        "mean_strata_total": mean([float(value) for value in strata_samples]) if strata_samples else 0.0,
    }
    return values, audit


def p_value_ge(observed: float, null_values: list[float]) -> float:
    if not null_values:
        return 1.0
    return (sum(value >= observed for value in null_values) + 1) / (len(null_values) + 1)


def bootstrap_lower95(rows: list[dict[str, object]]) -> float:
    rng = random.Random(stable_seed(BOOTSTRAP_SEED))
    by_domain_genus = genus_mean_vectors(rows)
    values = []
    for _ in range(N_BOOTSTRAP):
        sampled: dict[str, list[list[float]]] = {}
        for domain in DOMAINS:
            genera = sorted(by_domain_genus.get(domain, {}))
            if not genera:
                sampled[domain] = []
                continue
            sampled[domain] = [by_domain_genus[domain][rng.choice(genera)] for _item in genera]
        values.append(float(statistic_from_domain_vectors(sampled)["T_2geom"]))
    return percentile(values, 0.025) if values else 0.0


def covariance_matrix(vectors: list[list[float]]) -> list[list[float]]:
    if not vectors:
        return []
    dim = len(vectors[0])
    center = [mean([vector[i] for vector in vectors]) for i in range(dim)]
    mat = [[0.0 for _ in range(dim)] for _ in range(dim)]
    for vector in vectors:
        centered = [vector[i] - center[i] for i in range(dim)]
        for i in range(dim):
            for j in range(dim):
                mat[i][j] += centered[i] * centered[j]
    denom = max(len(vectors) - 1, 1)
    for i in range(dim):
        for j in range(dim):
            mat[i][j] /= denom
    return mat


def free_covariance_alignment(rows: list[dict[str, object]]) -> float | None:
    by_domain_genus = genus_mean_vectors(rows, coord_key="r_coords")
    matrices = {}
    for domain in DOMAINS:
        vectors = list(by_domain_genus.get(domain, {}).values())
        if len(vectors) < 2:
            return None
        matrices[domain] = covariance_matrix(vectors)
    denom = frobenius_norm(matrices["Bacteria"]) * frobenius_norm(matrices["Archaea"])
    if denom <= NORM_FLOOR:
        return None
    return matrix_trace_product(matrices["Bacteria"], matrices["Archaea"]) / denom


def raw_e1_gate(rows: list[dict[str, object]], b1_basis: list[list[float]]) -> dict[str, object]:
    by_domain: dict[str, list[float]] = defaultdict(list)
    for row in rows:
        d = row["d"]
        assert isinstance(d, list)
        projected = project_onto_orthonormal(b1_basis, d)
        fraction = dot(projected, projected) / max(dot(d, d), NORM_FLOOR)
        by_domain[str(row["domain"])].append(fraction)
    per_domain = {domain: mean(values) for domain, values in by_domain.items() if values}
    value = mean([per_domain[domain] for domain in DOMAINS if domain in per_domain]) if per_domain else 0.0
    return {
        "pass": value > 0.05 and all(per_domain.get(domain, 0.0) > 0.0 for domain in DOMAINS),
        "raw_E1_fraction_domain_balanced": value,
        "per_domain": per_domain,
    }


def top_necessity_contrasts(
    conserved_coords: list[float] | None,
    b2_basis: list[list[float]],
    named_b2: list[tuple[str, list[float]]],
) -> list[dict[str, object]]:
    if conserved_coords is None:
        return []
    conserved_vector = [0.0 for _ in b2_basis[0]]
    for coeff, q in zip(conserved_coords, b2_basis):
        for idx, value in enumerate(q):
            conserved_vector[idx] += coeff * value
    unit = normalize(conserved_vector)
    if unit is None:
        return []
    rows = []
    for name, vector in named_b2:
        cos = vector_cos(unit, vector)
        if cos is not None:
            rows.append((abs(cos), cos, name))
    rows.sort(reverse=True)
    return [{"contrast": name, "cos": round_float(cos), "abs_cos": round_float(abs_cos)} for abs_cos, cos, name in rows[:6]]


def main() -> None:
    started = time.monotonic()
    panel = fetch_probe.build_panel(force_refresh=False)
    counts = panel.get("n_genera_domain", {})
    if not isinstance(counts, dict):
        counts = {}
    n_genera = {domain: int(counts.get(domain, 0)) for domain in DOMAINS}
    power_pass = all(n_genera[domain] >= MIN_DOMAIN_GENERA for domain in DOMAINS)
    if not power_pass:
        emit(
            "needs_external",
            reason="panel lacks Bacteria>=8 and Archaea>=8 genus clusters with KFU carrier data",
            n_genera=n_genera,
            honest_scope_note=HONEST_SCOPE_NOTE,
            elapsed_seconds=round_float(time.monotonic() - started, 3),
        )

    aa_panel = aaindex_probe.build_panel(force_refresh=False)
    if aa_panel.get("status") != "ok":
        emit(
            "needs_external",
            reason="AAindex1 physicochemical records were not available for missense force carrier",
            aaindex_status=aa_panel,
            honest_scope_note=HONEST_SCOPE_NOTE,
            elapsed_seconds=round_float(time.monotonic() - started, 3),
        )

    full_codons = codon_order()
    sense_codons = sense_codon_order()
    index = {codon: idx for idx, codon in enumerate(sense_codons)}
    families = families_by_aa(sense_codons)
    exact_b1 = build_b1_basis_exact(full_codons, sense_codons, families, index)
    b1_basis = span_basis([[float(value) for value in vector] for vector in exact_b1])
    named_b2 = build_b2_named_columns(sense_codons, families, index)
    b2_basis = span_basis([vector for _name, vector in named_b2])

    prepared, _meta = kfu.prepare_rows(panel, aa_panel, usage_mode="log", sensitivity="main")
    rows = [row for row in prepared if row.get("domain") in DOMAINS]
    for row in rows:
        controls = b1_basis + list(row["z_all"])  # type: ignore[arg-type]
        row["b2_basis"] = b2_basis
        row["b2_perp"] = b2_perp_basis(b2_basis, controls)
        row["b2_perp_rank"] = len(row["b2_perp"])  # type: ignore[arg-type]
        row["b2_coords"] = row_b2_coordinates(row, row["d"])  # type: ignore[arg-type]
        row["r_coords"] = [dot(q, row["r"]) for q in b2_basis]  # type: ignore[arg-type]
        source_counts = dict(row.get("source_counts", {}))
        if not source_counts:
            source_counts = {}

    source_by_key = {
        (str(row.get("organism")), str(row.get("genus")), str(row.get("domain"))): row
        for row in panel.get("rows", [])
        if isinstance(row, dict)
    }
    completeness_features = []
    completeness_responses = []
    for row in rows:
        source = source_by_key.get((str(row.get("organism")), str(row.get("genus")), str(row.get("domain"))))
        if source is None:
            continue
        counts_row = dict(source["all_codon_counts_rna"])  # type: ignore[arg-type]
        completeness_features.append(feature_vector(counts_gc_features(counts_row, sense_codons)))
        completeness_responses.append(row["r"])  # type: ignore[arg-type]
    completeness_r2 = multivariate_r2(completeness_features, completeness_responses)

    min_b2_rank = min((int(row["b2_perp_rank"]) for row in rows), default=0)
    median_b2_rank = percentile([float(row["b2_perp_rank"]) for row in rows], 0.5) if rows else 0.0
    estimability_pass = min_b2_rank >= 2
    observed = statistic_from_rows(rows)
    t_obs = float(observed["T_2geom"])
    by_domain_genus = genus_mean_vectors(rows)
    conserved_direction = mean_direction(list(by_domain_genus.get("Bacteria", {}).values()))
    null_values, null_audit = null_distribution(rows, families, sense_codons, index, N_NULL)
    p_null = p_value_ge(t_obs, null_values)
    boot_low = bootstrap_lower95(rows)
    free_align = free_covariance_alignment(rows)
    raw_gate = raw_e1_gate(rows, b1_basis)
    completeness_gate = {"pass": completeness_r2 < 0.10, "R2": completeness_r2, "threshold": 0.10}
    gates = {
        "power_scope": {"pass": power_pass, "n_genera": n_genera, "required_per_domain": MIN_DOMAIN_GENERA},
        "B2_perp_estimability": {"pass": estimability_pass, "min_rank": min_b2_rank, "median_rank": median_b2_rank},
        "raw_E1_conservation": raw_gate,
        "completeness": completeness_gate,
    }

    b_to_a = observed["Bacteria_to_Archaea"]
    a_to_b = observed["Archaea_to_Bacteria"]
    bidirectional = bool(observed["bidirectional_positive"])
    certified = (
        t_obs > 0.0
        and p_null <= 0.01
        and boot_low > 0.0
        and bidirectional
        and estimability_pass
        and completeness_gate["pass"]
        and raw_gate["pass"]
    )
    if not estimability_pass:
        status = "needs_external"
        verdict = "B2_perp is non-estimable after controlling B1 and the known-force union."
    elif not completeness_gate["pass"]:
        status = "needs_external"
        verdict = "union residual still carries recoverable GC composition, so second-geometry attribution is not valid on this panel."
    elif certified:
        status = "certified"
        verdict = "a second-order codon geometry orthogonal to the known-force union is held-out conserved across Bacteria and Archaea on this panel."
    elif p_null > 0.05:
        status = "refuted"
        verdict = "known-force union plus first-order E1 exhausts the currently detectable cross-domain synonymous-usage conservation at this power; no detectable second geometry."
    else:
        status = "coincidence"
        verdict = "held-out second-order alignment is suggestive but fails at least one certification gate."

    emit(
        status,
        verdict=verdict,
        T_2geom=round_float(t_obs),
        held_out={
            "Bacteria_to_Archaea": {
                "alignment": round_float(float(b_to_a["alignment"])),
                "sign_concordance": round_float(float(b_to_a["sign_concordance"])),
                "direction_norm": round_float(float(b_to_a["direction_norm"])),
            },
            "Archaea_to_Bacteria": {
                "alignment": round_float(float(a_to_b["alignment"])),
                "sign_concordance": round_float(float(a_to_b["sign_concordance"])),
                "direction_norm": round_float(float(a_to_b["direction_norm"])),
            },
            "bidirectional_positive": bidirectional,
        },
        null={"p": round_float(p_null), "n": len(null_values), "mean": round_float(mean(null_values)), "audit": null_audit},
        bootstrap={"lower95": round_float(boot_low), "n": N_BOOTSTRAP},
        completeness_R2=round_float(completeness_r2),
        B2_perp_rank={"min": min_b2_rank, "median": round_float(median_b2_rank), "raw_B2_rank": len(b2_basis)},
        free_covariance_alignment_exploratory=round_float(free_align),
        per_domain={
            domain: {
                "n_genera": len(by_domain_genus.get(domain, {})),
                "mean_B2_coord_norm": round_float(mean([norm(vector) for vector in by_domain_genus.get(domain, {}).values()]) if by_domain_genus.get(domain) else 0.0),
            }
            for domain in DOMAINS
        },
        n_genera=n_genera,
        gates=gates,
        necessity={"position_pair_contrast_naming": top_necessity_contrasts(conserved_direction, b2_basis, named_b2)},
        honest_scope_note=HONEST_SCOPE_NOTE,
        panel_cache_path=str(fetch_probe.PANEL_CACHE_PATH),
        elapsed_seconds=round_float(time.monotonic() - started, 3),
    )


if __name__ == "__main__":
    try:
        main()
    except SystemExit:
        raise
    except Exception as exc:
        emit(
            "needs_external",
            reason=f"{type(exc).__name__}:{exc}",
            honest_scope_note=HONEST_SCOPE_NOTE,
        )

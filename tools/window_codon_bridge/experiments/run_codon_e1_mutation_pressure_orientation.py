#!/usr/bin/env python3
"""Codon-E1 mutation-pressure orientation concordance test."""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import random
import sys
from typing import Any

import _mut_e1_fetch_probe as fetch_probe


EXPERIMENT_ID = "codon_e1_mutation_pressure_orientation"
CLAIM_ID = "bridge.genetic_code.codon_e1_mutation_pressure_orientation"
N_NULL = int(os.environ.get("CODON_E1_MUT_N_NULL", "20000"))
N_BOOTSTRAP = int(os.environ.get("CODON_E1_MUT_N_BOOTSTRAP", "10000"))
EPSILON_MAIN = 1.0e-12
NORM_FLOOR = 1.0e-12
TOL = 1.0e-10
MIN_CLADES = 6
MIN_SPECIES = 6
NULL_SEED = "codon_e1_mutation_pressure_orientation.global_synonymous_relabel"
GC_NULL_SEED = "codon_e1_mutation_pressure_orientation.gc_equilibrium_stratified_relabel"
BOOTSTRAP_SEED = "codon_e1_mutation_pressure_orientation.species_bootstrap"
SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[2]
PANEL_CACHE_PATH = REPO_ROOT / "tools" / "window_codon_bridge" / "synced" / "codon_e1_mutation_pressure_orientation_panel.json"

BASES = ("U", "C", "A", "G")
DNA_BASES = ("T", "C", "A", "G")
COMPLEMENT = str.maketrans("ACGT", "TGCA")


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status in {"certified", "coincidence"} else (3 if status == "needs_external" else 2))


def stable_seed(text: str) -> int:
    return int.from_bytes(hashlib.sha256(text.encode("utf-8")).digest()[:16], "big")


def round_float(value: float | None, digits: int = 12) -> float | None:
    if value is None:
        return None
    if not math.isfinite(value):
        return value
    rounded = round(float(value), digits)
    return 0.0 if rounded == -0.0 else rounded


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def percentile(values: list[float], q: float) -> float:
    ordered = sorted(values)
    pos = (len(ordered) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return ordered[lo]
    return ordered[lo] * (hi - pos) + ordered[hi] * (pos - lo)


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def norm(vector: list[float]) -> float:
    return math.sqrt(dot(vector, vector))


def subtract(left: list[float], right: list[float]) -> list[float]:
    return [a - b for a, b in zip(left, right)]


def scale(factor: float, vector: list[float]) -> list[float]:
    return [factor * value for value in vector]


def vector_cos(left: list[float], right: list[float]) -> float | None:
    denom = norm(left) * norm(right)
    if denom <= NORM_FLOOR:
        return None
    return dot(left, right) / denom


def codon_order() -> list[str]:
    return fetch_probe.codon_order_rna()


def sense_codon_order() -> list[str]:
    return fetch_probe.sense_codon_order_rna()


def families_by_aa(codons: list[str]) -> dict[str, list[str]]:
    families: dict[str, list[str]] = defaultdict(list)
    for codon in codons:
        families[fetch_probe.CODON_TO_AA[codon]].append(codon)
    return dict(families)


def chemical_character(character: str, base: str) -> int:
    values = {
        "R": {"A": 1, "G": 1, "C": -1, "U": -1},
        "W": {"A": 1, "U": 1, "C": -1, "G": -1},
        "K": {"U": 1, "G": 1, "C": -1, "A": -1},
    }
    return values[character][base]


def project_syn_fraction(vector: list[Fraction], families: dict[str, list[str]], index: dict[str, int]) -> list[Fraction]:
    out = vector[:]
    for family in families.values():
        family_mean = sum(vector[index[codon]] for codon in family) / Fraction(len(family), 1)
        for codon in family:
            out[index[codon]] -= family_mean
    return out


def project_syn_float(vector: list[float], families: dict[str, list[str]], index: dict[str, int]) -> list[float]:
    out = vector[:]
    for family in families.values():
        family_mean = sum(vector[index[codon]] for codon in family) / len(family)
        for codon in family:
            out[index[codon]] -= family_mean
    return out


def fraction_dot(left: list[Fraction], right: list[Fraction]) -> Fraction:
    return sum((a * b for a, b in zip(left, right)), Fraction(0, 1))


def fraction_mgs(columns: list[list[Fraction]]) -> list[list[Fraction]]:
    basis: list[list[Fraction]] = []
    for column in columns:
        working = column[:]
        for q in basis:
            denom = fraction_dot(q, q)
            if denom == 0:
                continue
            coeff = fraction_dot(q, working) / denom
            if coeff:
                working = [value - coeff * q_value for value, q_value in zip(working, q)]
        if any(value != 0 for value in working):
            basis.append(working)
    return basis


def build_b1_basis_exact(
    full_codons: list[str],
    sense_codons: list[str],
    families: dict[str, list[str]],
    sense_index: dict[str, int],
) -> list[list[Fraction]]:
    full_index = {codon: idx for idx, codon in enumerate(full_codons)}
    columns: list[list[Fraction]] = []
    for position in range(3):
        for character in ("R", "W", "K"):
            full = [Fraction(chemical_character(character, codon[position]), 1) for codon in full_codons]
            restricted = [full[full_index[codon]] for codon in sense_codons]
            columns.append(project_syn_fraction(restricted, families, sense_index))
    return fraction_mgs(columns)


def project_onto_fraction_basis(q_basis: list[list[Fraction]], vector: list[float]) -> list[float]:
    out = [0.0 for _ in vector]
    for q in q_basis:
        denom_f = fraction_dot(q, q)
        if denom_f == 0:
            continue
        denom = float(denom_f)
        coeff = sum(float(qv) * value for qv, value in zip(q, vector)) / denom
        if coeff:
            for idx, qv in enumerate(q):
                out[idx] += coeff * float(qv)
    return out


def span_basis(vectors: list[list[float]]) -> list[list[float]]:
    basis: list[list[float]] = []
    for vector in vectors:
        working = vector[:]
        for q in basis:
            working = subtract(working, scale(dot(q, working), q))
        size = norm(working)
        if size > TOL:
            basis.append(scale(1.0 / size, working))
    return basis


def project_onto_orthonormal(q_basis: list[list[float]], vector: list[float]) -> list[float]:
    out = [0.0 for _ in vector]
    for q in q_basis:
        coeff = dot(q, vector)
        if coeff:
            for idx, qv in enumerate(q):
                out[idx] += coeff * qv
    return out


def residualize_against(q_basis: list[list[float]], vector: list[float]) -> list[float]:
    return subtract(vector, project_onto_orthonormal(q_basis, vector))


def component_vectors(sense_codons: list[str], families: dict[str, list[str]], index: dict[str, int]) -> dict[str, list[float]]:
    rows: dict[str, list[float]] = {}
    for position in range(3):
        for character in ("R", "W", "K"):
            raw = [float(chemical_character(character, codon[position])) for codon in sense_codons]
            rows[f"p{position + 1}_{character}"] = project_syn_float(raw, families, index)
    return rows


def basis_without_named_components(b1_basis: list[list[Fraction]], remove: list[list[float]]) -> list[list[float]]:
    b1_float = [[float(value) for value in q] for q in b1_basis]
    remove_basis = span_basis([project_onto_fraction_basis(b1_basis, vector) for vector in remove])
    keep = []
    for q in b1_float:
        reduced = residualize_against(remove_basis, q)
        for prior in keep:
            reduced = subtract(reduced, scale(dot(prior, reduced), prior))
        size = norm(reduced)
        if size > TOL:
            keep.append(scale(1.0 / size, reduced))
    return keep


def gc_equilibrium_basis(
    sense_codons: list[str],
    families: dict[str, list[str]],
    index: dict[str, int],
    b1_basis: list[list[Fraction]],
) -> tuple[list[str], list[list[float]]]:
    raw_rows: list[tuple[str, list[float]]] = []
    for pos in range(3):
        raw_rows.append((f"p{pos + 1}_weak_strong", [1.0 if codon[pos] in {"G", "C"} else -1.0 for codon in sense_codons]))
        raw_rows.append((f"p{pos + 1}_gc_indicator", [1.0 if codon[pos] in {"G", "C"} else 0.0 for codon in sense_codons]))
    raw_rows.extend(
        [
            ("dinuc_12_CpG", [1.0 if codon[0:2] == "CG" else 0.0 for codon in sense_codons]),
            ("dinuc_23_CpG", [1.0 if codon[1:3] == "CG" else 0.0 for codon in sense_codons]),
            ("dinuc_12_GpC", [1.0 if codon[0:2] == "GC" else 0.0 for codon in sense_codons]),
            ("dinuc_23_GpC", [1.0 if codon[1:3] == "GC" else 0.0 for codon in sense_codons]),
        ]
    )
    names = []
    vectors = []
    for name, raw in raw_rows:
        projected = project_onto_fraction_basis(b1_basis, project_syn_float(raw, families, index))
        names.append(name)
        vectors.append(projected)
    return names, span_basis(vectors)


def substitution_rate(spectrum: dict[str, float], context_dna: str, alt_base_dna: str) -> float:
    center = context_dna[1]
    if alt_base_dna == center:
        return 0.0
    if center in {"C", "T"}:
        key = f"{context_dna[0]}[{center}>{alt_base_dna}]{context_dna[2]}"
    else:
        comp_context = context_dna.translate(COMPLEMENT)[::-1]
        comp_alt = alt_base_dna.translate(COMPLEMENT)
        key = f"{comp_context[0]}[{comp_context[1]}>{comp_alt}]{comp_context[2]}"
    return float(spectrum.get(key, 0.0))


def mutation_pressure_vector(
    row: dict[str, object],
    sense_codons: list[str],
    index: dict[str, int],
    epsilon: float,
) -> tuple[list[float], dict[str, object]]:
    spectrum = row["sbs_spectrum"]
    context_counts = row["codon_context_counts"]
    assert isinstance(spectrum, dict) and isinstance(context_counts, dict)
    influx = [0.0 for _ in sense_codons]
    outflux = [0.0 for _ in sense_codons]
    audited_contexts = 0
    synonymous_edges = 0
    for source in sense_codons:
        source_dna = source.replace("U", "T")
        source_aa = fetch_probe.CODON_TO_AA[source]
        per_pos = context_counts[source]
        assert isinstance(per_pos, list)
        for pos in range(3):
            counter = per_pos[pos]
            assert isinstance(counter, dict)
            total = sum(int(v) for v in counter.values())
            if total <= 0:
                continue
            for alt in DNA_BASES:
                if alt == source_dna[pos]:
                    continue
                target_dna = source_dna[:pos] + alt + source_dna[pos + 1 :]
                target = target_dna.replace("T", "U")
                if target not in index or fetch_probe.CODON_TO_AA[target] != source_aa:
                    continue
                rate_sum = 0.0
                for context, count in counter.items():
                    rate_sum += int(count) * substitution_rate(spectrum, str(context), alt)
                avg_rate = rate_sum / total
                outflux[index[source]] += avg_rate
                influx[index[target]] += avg_rate
                synonymous_edges += 1
                audited_contexts += total
    return [math.log(influx[idx] + epsilon) - math.log(outflux[idx] + epsilon) for idx in range(len(sense_codons))], {
        "synonymous_directed_edges": synonymous_edges,
        "context_weighted_edge_observations": audited_contexts,
    }


def gc3_from_counts(counts: dict[str, int], sense_codons: list[str]) -> float:
    total = sum(int(counts[codon]) for codon in sense_codons)
    return sum(int(counts[codon]) for codon in sense_codons if codon[2] in {"G", "C"}) / total


def statistic(rows: list[dict[str, object]], key: str) -> tuple[float, dict[str, float]]:
    by_species: dict[str, list[float]] = defaultdict(list)
    for row in rows:
        value = row.get(key)
        if value is not None:
            by_species[str(row["species_key"])].append(float(value))
    per_species = {species: mean(values) for species, values in sorted(by_species.items()) if values}
    return mean(list(per_species.values())), per_species


def bootstrap_lower95(per_species: dict[str, float], seed: str) -> float:
    rng = random.Random(stable_seed(seed))
    species = sorted(per_species)
    values = []
    for _ in range(N_BOOTSTRAP):
        values.append(mean([per_species[rng.choice(species)] for _ in species]))
    return percentile(values, 0.025)


def p_value_ge(observed: float, null_values: list[float]) -> float:
    return (sum(value >= observed for value in null_values) + 1) / (len(null_values) + 1)


def family_permutation(families: dict[str, list[str]], rng: random.Random, gc_stratified: bool) -> dict[str, str]:
    permutation: dict[str, str] = {}
    for family in families.values():
        strata: dict[str, list[str]] = defaultdict(list)
        if gc_stratified:
            for codon in family:
                strata[("GC" if codon[2] in {"G", "C"} else "AU") + "_" + codon[:2]].append(codon)
        else:
            strata["all"] = family[:]
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


def endpoint_cos(
    d: list[float],
    z: list[float],
    b1_basis: list[list[Fraction]],
    endpoint_basis: list[list[float]] | None,
    gc_basis: list[list[float]],
) -> float | None:
    if endpoint_basis is None:
        x = project_onto_fraction_basis(b1_basis, d)
        y = project_onto_fraction_basis(b1_basis, z)
    else:
        x = project_onto_orthonormal(endpoint_basis, d)
        y = project_onto_orthonormal(endpoint_basis, z)
    if gc_basis:
        x = residualize_against(gc_basis, x)
        y = residualize_against(gc_basis, y)
        x = project_onto_fraction_basis(b1_basis, x)
        y = project_onto_fraction_basis(b1_basis, y)
    return vector_cos(x, y)


def compute_rows(
    panel: dict[str, object],
    b1_basis: list[list[Fraction]],
    endpoint_bases: dict[str, list[list[float]] | None],
    gc_basis: list[list[float]],
    sense_codons: list[str],
    families: dict[str, list[str]],
    index: dict[str, int],
) -> list[dict[str, object]]:
    rows = []
    for entry in panel["clades"]:
        assert isinstance(entry, dict)
        counts = {codon: int(entry["codon_counts_rna"][codon]) for codon in sense_codons}  # type: ignore[index]
        total = sum(counts.values())
        usage = [counts[codon] / total for codon in sense_codons]
        d = project_syn_float(usage, families, index)
        m, audit = mutation_pressure_vector(entry, sense_codons, index, EPSILON_MAIN)
        z = project_syn_float(m, families, index)
        row: dict[str, object] = {
            "clade": entry["clade"],
            "species_key": entry["species_key"],
            "reference_accession": entry["reference_accession"],
            "gc3": gc3_from_counts(counts, sense_codons),
            "d": d,
            "z": z,
            "mutation_audit": audit,
        }
        for endpoint, basis in endpoint_bases.items():
            row[f"C_{endpoint}"] = endpoint_cos(d, z, b1_basis, basis, gc_basis if endpoint == "gc_equilibrium_residualized" else [])
        rows.append(row)
    return rows


def relabeled_stat(
    rows: list[dict[str, object]],
    permutation: dict[str, str],
    endpoint: str,
    b1_basis: list[list[Fraction]],
    endpoint_basis: list[list[float]] | None,
    gc_basis: list[list[float]],
    sense_codons: list[str],
    index: dict[str, int],
) -> float:
    relabeled = []
    for row in rows:
        d = [float(value) for value in row["d"]]  # type: ignore[union-attr]
        z = [float(value) for value in row["z"]]  # type: ignore[union-attr]
        zp = apply_permutation(z, permutation, sense_codons, index)
        relabeled.append({**row, f"C_{endpoint}": endpoint_cos(d, zp, b1_basis, endpoint_basis, gc_basis if endpoint == "gc_equilibrium_residualized" else [])})
    return statistic(relabeled, f"C_{endpoint}")[0]


def null_distribution(
    rows: list[dict[str, object]],
    families: dict[str, list[str]],
    endpoint: str,
    b1_basis: list[list[Fraction]],
    endpoint_basis: list[list[float]] | None,
    gc_basis: list[list[float]],
    sense_codons: list[str],
    index: dict[str, int],
    seed: str,
    gc_stratified: bool,
) -> list[float]:
    rng = random.Random(stable_seed(seed))
    values = []
    for _ in range(N_NULL):
        permutation = family_permutation(families, rng, gc_stratified)
        values.append(relabeled_stat(rows, permutation, endpoint, b1_basis, endpoint_basis, gc_basis, sense_codons, index))
    return values


def pearson(x_values: list[float], y_values: list[float]) -> float | None:
    if len(x_values) < 3 or len(x_values) != len(y_values):
        return None
    xm = mean(x_values)
    ym = mean(y_values)
    x = [value - xm for value in x_values]
    y = [value - ym for value in y_values]
    denom = norm(x) * norm(y)
    if denom <= NORM_FLOOR:
        return None
    return dot(x, y) / denom


def component_ledger(rows: list[dict[str, object]], components: dict[str, list[float]]) -> dict[str, object]:
    out = {}
    for name, vector in components.items():
        masses_x = []
        masses_y = []
        for row in rows:
            d = row["d"]  # type: ignore[assignment]
            z = row["z"]  # type: ignore[assignment]
            denom_x = max(dot(d, d), NORM_FLOOR)
            denom_y = max(dot(z, z), NORM_FLOOR)
            vden = max(dot(vector, vector), NORM_FLOOR)
            masses_x.append((dot(d, vector) ** 2 / vden) / denom_x)
            masses_y.append((dot(z, vector) ** 2 / vden) / denom_y)
        out[name] = {"usage_mass": round_float(mean(masses_x)), "mutation_mass": round_float(mean(masses_y))}
    return out


def compact_panel(panel: dict[str, object]) -> dict[str, object]:
    return {
        "generated_at": panel.get("generated_at"),
        "status": panel.get("status"),
        "n_clades": panel.get("n_clades"),
        "n_species": panel.get("n_species"),
        "species": panel.get("species"),
        "attempts_compact": panel.get("attempts_compact"),
        "cache_path": str(fetch_probe.PROBE_CACHE_PATH),
    }


def main() -> None:
    panel = fetch_probe.build_probe(force_refresh=False, panel_target=MIN_CLADES)
    PANEL_CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    PANEL_CACHE_PATH.write_text(json.dumps(panel, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if panel.get("status") != "ok" or int(panel.get("n_clades", 0)) < MIN_CLADES or int(panel.get("n_species", 0)) < MIN_SPECIES:
        emit(
            "needs_external",
            reason="fetch probe did not yield at least six cross-species Ruis clades with SBS 96-vector and paired reference CDS codon/context counts",
            fetch_probe=compact_panel(panel),
            note="drift-orientation candidate only; not Window6; not causal",
        )

    full_codons = codon_order()
    sense_codons = sense_codon_order()
    index = {codon: idx for idx, codon in enumerate(sense_codons)}
    families = families_by_aa(sense_codons)
    b1_basis = build_b1_basis_exact(full_codons, sense_codons, families, index)
    components = component_vectors(sense_codons, families, index)
    minus_p3w = basis_without_named_components(b1_basis, [components["p3_W"]])
    minus_all_p3 = basis_without_named_components(b1_basis, [components[f"p3_{char}"] for char in ("R", "W", "K")])
    gc_basis_names, gc_basis = gc_equilibrium_basis(sense_codons, families, index, b1_basis)
    endpoints: dict[str, list[list[float]] | None] = {
        "full_B1": None,
        "minus_p3W": minus_p3w,
        "minus_all_p3": minus_all_p3,
        "gc_equilibrium_residualized": None,
    }
    rows = compute_rows(panel, b1_basis, endpoints, gc_basis, sense_codons, families, index)
    endpoint_payload: dict[str, object] = {}
    primary_ok = False
    any_nonprimary_significant = False
    for endpoint, basis in endpoints.items():
        key = f"C_{endpoint}"
        observed, per_species = statistic(rows, key)
        null_global = null_distribution(rows, families, endpoint, b1_basis, basis, gc_basis, sense_codons, index, NULL_SEED + "." + endpoint, False)
        null_gc = null_distribution(rows, families, endpoint, b1_basis, basis, gc_basis, sense_codons, index, GC_NULL_SEED + "." + endpoint, True)
        p_global = p_value_ge(observed, null_global)
        p_gc = p_value_ge(observed, null_gc)
        lower = bootstrap_lower95(per_species, BOOTSTRAP_SEED + "." + endpoint)
        if endpoint == "gc_equilibrium_residualized":
            primary_ok = p_global <= 0.01 and p_gc <= 0.01 and lower > 0.0
        elif p_global <= 0.01:
            any_nonprimary_significant = True
        endpoint_payload[endpoint] = {
            "T": round_float(observed),
            "p_global_synonymous_relabel": round_float(p_global),
            "p_gc_equilibrium_stratified_relabel": round_float(p_gc),
            "bootstrap_lower95": round_float(lower),
            "per_species": {species: round_float(value) for species, value in per_species.items()},
            "null_global_mean": round_float(mean(null_global)),
            "null_gc_stratified_mean": round_float(mean(null_gc)),
            "rank": 6 if endpoint in {"full_B1", "gc_equilibrium_residualized"} else len(basis or []),
        }

    primary = endpoint_payload["gc_equilibrium_residualized"]
    if primary_ok:
        status = "certified"
    elif any_nonprimary_significant:
        status = "coincidence"
    else:
        status = "refuted"

    gc3 = [float(row["gc3"]) for row in rows]
    primary_c = [float(row["C_gc_equilibrium_residualized"]) for row in rows if row["C_gc_equilibrium_residualized"] is not None]
    gc3_for_primary = [float(row["gc3"]) for row in rows if row["C_gc_equilibrium_residualized"] is not None]
    emit(
        status,
        primary_endpoint="gc_equilibrium_residualized",
        primary=primary,
        endpoints=endpoint_payload,
        n_clades=int(panel["n_clades"]),
        n_species=int(panel["n_species"]),
        species=list(panel["species"]),
        rank_B1=len(b1_basis),
        rank_minus_p3W=len(minus_p3w),
        rank_minus_all_p3=len(minus_all_p3),
        gc_equilibrium_basis={
            "source_names": gc_basis_names,
            "rank_after_B1_projection": len(gc_basis),
            "construction": "synonymous-centered position weak/strong, GC-indicator, and CpG/GpC dinucleotide context axes projected into frozen B1; x and y are residualized before the primary cosine",
        },
        gc_checks={
            "gc3_by_clade": {str(row["clade"]): round_float(float(row["gc3"])) for row in rows},
            "primary_cosine_gc3_pearson": round_float(pearson(gc3_for_primary, primary_c)),
            "mean_gc3": round_float(mean(gc3)),
        },
        component_ledger=component_ledger(rows, components),
        strand_audit={
            "sbs_convention": "96-channel pyrimidine-canonical SBS labels such as A[C>A]A",
            "coding_strand_application": "CDS coding-strand contexts are used directly when the mutated base is C/T; A/G centers are reverse-complemented to the pyrimidine-canonical SBS key with left/right reversed",
            "context_source": "GenBank reference CDS coordinates from each Ruis clade reference accession",
            "mean_context_weighted_edge_observations": round_float(mean([float(row["mutation_audit"]["context_weighted_edge_observations"]) for row in rows])),  # type: ignore[index]
        },
        filters=panel.get("filters"),
        n_null=N_NULL,
        n_bootstrap=N_BOOTSTRAP,
        epsilon_main=EPSILON_MAIN,
        relabel_seeds={
            "global": stable_seed(NULL_SEED),
            "gc_equilibrium_stratified": stable_seed(GC_NULL_SEED),
            "bootstrap": stable_seed(BOOTSTRAP_SEED),
        },
        panel_cache_path=str(PANEL_CACHE_PATH),
        fetch_probe=compact_panel(panel),
        note="drift-orientation concordance only; not Window6; not causal proof",
    )


if __name__ == "__main__":
    main()

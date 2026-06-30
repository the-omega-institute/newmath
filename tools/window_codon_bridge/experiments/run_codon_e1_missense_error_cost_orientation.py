#!/usr/bin/env python3
"""Codon-E1 local missense-error-cost orientation test."""
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

import _misscost_e1_fetch_probe as fetch_probe
import _mut_e1_fetch_probe as code_probe


EXPERIMENT_ID = "codon_e1_missense_error_cost_orientation"
CLAIM_ID = "bridge.genetic_code.codon_e1_missense_error_cost_orientation"
N_NULL = int(os.environ.get("CODON_E1_MISSCOST_N_NULL", "20000"))
N_BOOTSTRAP = int(os.environ.get("CODON_E1_MISSCOST_N_BOOTSTRAP", "10000"))
N_CODE_NULL = int(os.environ.get("CODON_E1_MISSCOST_CODE_N_NULL", "5000"))
MIN_GENERA = 4
NORM_FLOOR = 1.0e-12
TOL = 1.0e-10
NULL_A_SEED = "codon_e1_missense_error_cost_orientation.global_synonymous_relabel"
NULL_B_SEED = "codon_e1_missense_error_cost_orientation.gc_wobble_stratified_relabel"
BOOTSTRAP_SEED = "codon_e1_missense_error_cost_orientation.genus_bootstrap"
CODE_SEED = "codon_e1_missense_error_cost_orientation.standard_code_sanity"
SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[2]
PANEL_CACHE_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "codon_e1_missense_error_cost_orientation_panel.json"
)

PROPERTY_LABELS = {
    "WOEC730101": "polar_requirement_PR",
    "GRAR740102": "grantham_polarity",
    "GRAR740103": "grantham_volume",
    "KYTJ820101": "kyte_doolittle_hydropathy",
}
PR_INDEX = "WOEC730101"
BASES = ("U", "C", "A", "G")


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
    return code_probe.codon_order_rna()


def sense_codon_order() -> list[str]:
    return code_probe.sense_codon_order_rna()


def families_by_aa(codons: list[str]) -> dict[str, list[str]]:
    families: dict[str, list[str]] = defaultdict(list)
    for codon in codons:
        families[code_probe.CODON_TO_AA[codon]].append(codon)
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


def basis_without_named_components(b1_basis: list[list[float]], remove: list[list[float]]) -> list[list[float]]:
    remove_basis = span_basis([project_onto_orthonormal(b1_basis, vector) for vector in remove])
    keep = []
    for q in b1_basis:
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
    b1_basis: list[list[float]],
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
        projected = project_onto_orthonormal(b1_basis, project_syn_float(raw, families, index))
        names.append(name)
        vectors.append(projected)
    return names, span_basis(vectors)


def one_step_neighbors(codon: str, full_codons: set[str]) -> list[str]:
    out = []
    for pos in range(3):
        for base in BASES:
            if base == codon[pos]:
                continue
            target = codon[:pos] + base + codon[pos + 1 :]
            if target in full_codons:
                out.append(target)
    return out


def local_missense_cost(
    property_values: dict[str, float],
    full_codons: list[str],
    sense_codons: list[str],
) -> list[float]:
    values = [float(property_values[aa]) for aa in sorted(property_values)]
    center = mean(values)
    sd = math.sqrt(mean([(value - center) ** 2 for value in values]))
    full_set = set(full_codons)
    costs = []
    for codon in sense_codons:
        aa = code_probe.CODON_TO_AA[codon]
        terms = []
        for target in one_step_neighbors(codon, full_set):
            target_aa = code_probe.CODON_TO_AA[target]
            if target_aa == "*" or target_aa == aa:
                continue
            terms.append(((float(property_values[aa]) - float(property_values[target_aa])) / sd) ** 2)
        costs.append(mean(terms))
    return costs


def synonymous_escape_degree(sense_codons: list[str]) -> list[float]:
    sense_set = set(sense_codons)
    values = []
    for codon in sense_codons:
        aa = code_probe.CODON_TO_AA[codon]
        degree = 0
        for target in one_step_neighbors(codon, sense_set):
            if code_probe.CODON_TO_AA[target] == aa:
                degree += 1
        values.append(float(degree))
    return values


def control_basis(
    sense_codons: list[str],
    families: dict[str, list[str]],
    index: dict[str, int],
    b1_basis: list[list[float]],
    components: dict[str, list[float]],
) -> tuple[list[str], list[list[float]], dict[str, object]]:
    gc_names, gc_basis = gc_equilibrium_basis(sense_codons, families, index, b1_basis)
    raw_controls: list[tuple[str, list[float]]] = [
        (
            "GC3",
            project_onto_orthonormal(
                b1_basis,
                project_syn_float([1.0 if codon[2] in {"G", "C"} else 0.0 for codon in sense_codons], families, index),
            ),
        )
    ]
    for name in ("p3_W", "p3_R", "p3_K"):
        raw_controls.append((name, project_onto_orthonormal(b1_basis, components[name])))
    raw_controls.append(
        (
            "edge_hiding_synonymous_neighbor_degree_proxy",
            project_onto_orthonormal(b1_basis, project_syn_float(synonymous_escape_degree(sense_codons), families, index)),
        )
    )
    zero_family_controls = 0
    for aa, codons in families.items():
        raw = [1.0 if codon in codons else 0.0 for codon in sense_codons]
        projected = project_onto_orthonormal(b1_basis, project_syn_float(raw, families, index))
        if norm(projected) <= TOL:
            zero_family_controls += 1
        raw_controls.append((f"family_size_free_composition_{aa}", projected))
    names = [name for name, _vector in raw_controls]
    vectors = [vector for _name, vector in raw_controls]
    basis = span_basis(vectors)
    return names, basis, {
        "raw_control_count": len(raw_controls),
        "rank_after_B1_projection": len(basis),
        "family_composition_zero_rank_controls": zero_family_controls,
        "gc_equilibrium_basis_reference_rank": len(gc_basis),
        "gc_equilibrium_basis_reference_names": gc_names,
        "edge_hiding_control_scope": "synonymous one-step neighbor degree proxy",
    }


def usage_residual(row: dict[str, object], sense_codons: list[str], families: dict[str, list[str]], index: dict[str, int]) -> list[float] | None:
    counts_raw = row.get("codon_counts_rna")
    if not isinstance(counts_raw, dict):
        return None
    counts = {codon: int(counts_raw.get(codon, 0)) for codon in sense_codons}
    total = sum(counts.values())
    if total <= 0:
        return None
    usage = [counts[codon] / total for codon in sense_codons]
    return project_syn_float(usage, families, index)


def p_value_ge(observed: float, null_values: list[float]) -> float:
    return (sum(value >= observed for value in null_values) + 1) / (len(null_values) + 1)


def p_value_le(observed: float, null_values: list[float]) -> float:
    return (sum(value <= observed for value in null_values) + 1) / (len(null_values) + 1)


def statistic(rows: list[dict[str, object]], key: str, cluster_key: str = "genus") -> tuple[float | None, dict[str, float]]:
    by_cluster: dict[str, list[float]] = defaultdict(list)
    for row in rows:
        value = row.get(key)
        if value is not None:
            by_cluster[str(row[cluster_key])].append(float(value))
    per_cluster = {cluster: mean(values) for cluster, values in sorted(by_cluster.items()) if values}
    if not per_cluster:
        return None, {}
    return mean(list(per_cluster.values())), per_cluster


def bootstrap_lower95(per_cluster: dict[str, float], seed: str) -> float | None:
    if not per_cluster:
        return None
    rng = random.Random(stable_seed(seed))
    clusters = sorted(per_cluster)
    values = []
    for _ in range(N_BOOTSTRAP):
        values.append(mean([per_cluster[rng.choice(clusters)] for _ in clusters]))
    return percentile(values, 0.025)


def family_permutation(
    families: dict[str, list[str]],
    rng: random.Random,
    gc_wobble_stratified: bool,
) -> tuple[dict[str, str], int, int]:
    permutation: dict[str, str] = {}
    expansions = 0
    strata_count = 0
    for family in families.values():
        strata: dict[str, list[str]] = defaultdict(list)
        if gc_wobble_stratified:
            for codon in family:
                strata["GC3" if codon[2] in {"G", "C"} else "AU3"].append(codon)
            if any(len(codons) < 2 for codons in strata.values()):
                strata = {"expanded_family": family[:]}
                expansions += 1
        else:
            strata["all"] = family[:]
        for codons in strata.values():
            strata_count += 1
            shuffled = codons[:]
            rng.shuffle(shuffled)
            for source, target in zip(codons, shuffled):
                permutation[source] = target
    return permutation, expansions, strata_count


def apply_permutation(vector: list[float], permutation: dict[str, str], sense_codons: list[str], index: dict[str, int]) -> list[float]:
    out = [0.0 for _ in sense_codons]
    for source, target in permutation.items():
        out[index[target]] = vector[index[source]]
    return out


def relabeled_stats(
    rows: list[dict[str, object]],
    cost_vectors: dict[str, list[float]],
    permutation: dict[str, str],
    basis: list[list[float]],
    sense_codons: list[str],
    index: dict[str, int],
    subset_domain: str | None = None,
) -> dict[str, float]:
    by_property: dict[str, list[dict[str, object]]] = {key: [] for key in cost_vectors}
    y_by_property = {
        key: project_onto_orthonormal(basis, apply_permutation(vector, permutation, sense_codons, index))
        for key, vector in cost_vectors.items()
    }
    for row in rows:
        if subset_domain is not None and row["domain"] != subset_domain:
            continue
        x = row["x_perp"]
        assert isinstance(x, list)
        for key, y in y_by_property.items():
            by_property[key].append({**row, f"C_{key}": vector_cos(x, y)})
    out = {}
    for key, keyed_rows in by_property.items():
        value, _clusters = statistic(keyed_rows, f"C_{key}")
        out[key] = float(value) if value is not None else 0.0
    return out


def null_distributions(
    rows: list[dict[str, object]],
    cost_vectors: dict[str, list[float]],
    families: dict[str, list[str]],
    basis: list[list[float]],
    sense_codons: list[str],
    index: dict[str, int],
    seed: str,
    gc_wobble_stratified: bool,
    domains: list[str],
) -> tuple[dict[str, list[float]], list[float], dict[str, list[float]], dict[str, float]]:
    rng = random.Random(stable_seed(seed))
    values = {key: [] for key in cost_vectors}
    max_values: list[float] = []
    domain_values = {domain: [] for domain in domains}
    expansion_rates = []
    for _ in range(N_NULL):
        permutation, expansions, strata_count = family_permutation(families, rng, gc_wobble_stratified)
        stats = relabeled_stats(rows, cost_vectors, permutation, basis, sense_codons, index)
        for key, value in stats.items():
            values[key].append(value)
        max_values.append(max(stats.values()))
        for domain in domains:
            domain_stat = relabeled_stats(rows, {PR_INDEX: cost_vectors[PR_INDEX]}, permutation, basis, sense_codons, index, subset_domain=domain)
            domain_values[domain].append(domain_stat[PR_INDEX])
        if strata_count:
            expansion_rates.append(expansions / strata_count)
    return values, max_values, domain_values, {
        "mean_adjacent_bin_expansion_rate": mean(expansion_rates) if expansion_rates else 0.0,
        "draws": N_NULL,
    }


def build_rows(
    panel: dict[str, object],
    sense_codons: list[str],
    families: dict[str, list[str]],
    index: dict[str, int],
    b1_basis: list[list[float]],
    primary_basis: list[list[float]],
    y_raw: dict[str, list[float]],
    y_perp: dict[str, list[float]],
) -> list[dict[str, object]]:
    rows = []
    for entry in panel.get("organisms", []):
        if not isinstance(entry, dict):
            continue
        d = usage_residual(entry, sense_codons, families, index)
        if d is None:
            continue
        x_raw = project_onto_orthonormal(b1_basis, d)
        x_perp = project_onto_orthonormal(primary_basis, d)
        row: dict[str, object] = {
            "organism": entry.get("organism"),
            "genus": str(entry.get("genus", "")).lower(),
            "domain": entry.get("domain"),
            "x_raw": x_raw,
            "x_perp": x_perp,
            "x_ratio": (norm(x_perp) ** 2) / max(norm(x_raw) ** 2, NORM_FLOOR),
        }
        for key in y_raw:
            row[f"C_raw_{key}"] = vector_cos(x_raw, y_raw[key])
            row[f"C_perp_{key}"] = vector_cos(x_perp, y_perp[key])
        rows.append(row)
    return rows


def domain_genus_summary(rows: list[dict[str, object]]) -> dict[str, dict[str, int]]:
    out: dict[str, dict[str, int]] = {}
    genera: dict[str, set[str]] = defaultdict(set)
    for row in rows:
        domain = str(row["domain"])
        out.setdefault(domain, {"organisms": 0, "genera": 0})
        out[domain]["organisms"] += 1
        genera[domain].add(str(row["genus"]))
    for domain, genus_set in genera.items():
        out[domain]["genera"] = len(genus_set)
    return dict(sorted(out.items()))


def genus_weighted_median(values_by_genus: dict[str, list[float]]) -> float:
    values = [mean(values) for _genus, values in sorted(values_by_genus.items()) if values]
    return percentile(values, 0.5)


def code_error_cost(code_map: dict[str, str], property_values: dict[str, float], full_codons: list[str], sense_codons: list[str]) -> float:
    values = [float(property_values[aa]) for aa in sorted(property_values)]
    center = mean(values)
    sd = math.sqrt(mean([(value - center) ** 2 for value in values]))
    full_set = set(full_codons)
    terms = []
    for codon in sense_codons:
        aa = code_map[codon]
        for target in one_step_neighbors(codon, full_set):
            if target not in code_map:
                continue
            target_aa = code_map[target]
            if target_aa == aa:
                continue
            terms.append(((float(property_values[aa]) - float(property_values[target_aa])) / sd) ** 2)
    return mean(terms)


def code_table_sanity(property_values: dict[str, float], full_codons: list[str], families: dict[str, list[str]]) -> dict[str, object]:
    sense_codons = [codon for family in families.values() for codon in family]
    standard = {codon: code_probe.CODON_TO_AA[codon] for codon in sense_codons}
    observed = code_error_cost(standard, property_values, full_codons, sense_codons)
    rng = random.Random(stable_seed(CODE_SEED))
    aa_labels = sorted(families)
    null_values = []
    family_items = sorted(families.items())
    for _ in range(N_CODE_NULL):
        shuffled = aa_labels[:]
        rng.shuffle(shuffled)
        random_code = {}
        for (_aa, codons), new_aa in zip(family_items, shuffled):
            for codon in codons:
                random_code[codon] = new_aa
        null_values.append(code_error_cost(random_code, property_values, full_codons, sense_codons))
    p_lower = p_value_le(observed, null_values)
    return {
        "observed_standard_code_cost": round_float(observed),
        "random_code_mean_cost": round_float(mean(null_values)),
        "p_lower_tail": round_float(p_lower),
        "passed": p_lower <= 0.01,
        "n_random_codes": N_CODE_NULL,
        "random_code_model": "amino-acid labels permuted across standard synonymous codon blocks, preserving block degeneracy profile and stop exclusions",
    }


def leave_one_family_out(
    rows: list[dict[str, object]],
    y_perp_pr: list[float],
    families: dict[str, list[str]],
    index: dict[str, int],
) -> dict[str, object]:
    values = {}
    positive = 0
    for aa, codons in sorted(families.items()):
        mask = [1.0 for _ in y_perp_pr]
        for codon in codons:
            mask[index[codon]] = 0.0
        folded_rows = []
        y_fold = [value * mask[idx] for idx, value in enumerate(y_perp_pr)]
        for row in rows:
            x = row["x_perp"]
            assert isinstance(x, list)
            x_fold = [value * mask[idx] for idx, value in enumerate(x)]
            folded_rows.append({**row, "C_fold": vector_cos(x_fold, y_fold)})
        stat, _clusters = statistic(folded_rows, "C_fold")
        value = float(stat) if stat is not None else 0.0
        values[aa] = value
        if value > 0:
            positive += 1
    return {
        "positive_fraction": positive / len(families),
        "positive_folds": positive,
        "n_folds": len(families),
        "per_family_T": {aa: round_float(value) for aa, value in values.items()},
    }


def compact_panel(panel: dict[str, object]) -> dict[str, object]:
    return {
        "status": panel.get("status"),
        "domain_summary": panel.get("domain_summary"),
        "thick_domains": panel.get("thick_domains"),
        "n_domains": panel.get("n_domains"),
        "n_organisms": panel.get("n_organisms"),
        "n_genera": panel.get("n_genera"),
        "source_status": panel.get("source_status"),
        "cache_path": str(PANEL_CACHE_PATH),
    }


def main() -> None:
    try:
        panel = fetch_probe.build_panel(force_refresh=False)
    except Exception as exc:
        emit(
            "needs_external",
            reason=f"fetch probe failed gracefully: {type(exc).__name__}:{exc}",
            panel_cache_path=str(PANEL_CACHE_PATH),
            scope_note="bio-internal E1 mechanism audit; not Window6; edge-hiding escape control is a synonymous-neighbor-degree proxy",
        )
    if panel.get("status") != "ok":
        emit(
            "needs_external",
            reason="panel or AAindex battery is not externally available at the required thickness",
            fetch_probe=compact_panel(panel),
            panel_cache_path=str(PANEL_CACHE_PATH),
            scope_note="bio-internal E1 mechanism audit; not Window6; edge-hiding escape control is a synonymous-neighbor-degree proxy",
        )

    aaindex_panel = panel.get("aaindex")
    if not isinstance(aaindex_panel, dict) or aaindex_panel.get("status") != "ok":
        emit(
            "needs_external",
            reason="AAindex battery unavailable",
            fetch_probe=compact_panel(panel),
            panel_cache_path=str(PANEL_CACHE_PATH),
            scope_note="bio-internal E1 mechanism audit; not Window6; edge-hiding escape control is a synonymous-neighbor-degree proxy",
        )
    records = aaindex_panel.get("records")
    if not isinstance(records, dict) or PR_INDEX not in records:
        emit(
            "needs_external",
            reason="AAindex battery does not contain the pre-registered PR index",
            fetch_probe=compact_panel(panel),
            panel_cache_path=str(PANEL_CACHE_PATH),
            scope_note="bio-internal E1 mechanism audit; not Window6; edge-hiding escape control is a synonymous-neighbor-degree proxy",
        )

    full_codons = codon_order()
    sense_codons = sense_codon_order()
    index = {codon: idx for idx, codon in enumerate(sense_codons)}
    families = families_by_aa(sense_codons)
    exact_b1_basis = build_b1_basis_exact(full_codons, sense_codons, families, index)
    b1_basis = span_basis([[float(value) for value in vector] for vector in exact_b1_basis])
    components = component_vectors(sense_codons, families, index)
    control_names, z_basis, control_audit = control_basis(sense_codons, families, index, b1_basis, components)
    primary_basis = basis_without_named_components(b1_basis, z_basis)

    cost_vectors: dict[str, list[float]] = {}
    y_raw: dict[str, list[float]] = {}
    y_perp: dict[str, list[float]] = {}
    property_payload: dict[str, object] = {}
    for index_id in PROPERTY_LABELS:
        record = records.get(index_id)
        if not isinstance(record, dict) or not isinstance(record.get("values"), dict):
            emit(
                "needs_external",
                reason=f"AAindex record {index_id} unavailable or malformed",
                fetch_probe=compact_panel(panel),
                panel_cache_path=str(PANEL_CACHE_PATH),
                scope_note="bio-internal E1 mechanism audit; not Window6; edge-hiding escape control is a synonymous-neighbor-degree proxy",
            )
        values = {aa: float(value) for aa, value in record["values"].items()}  # type: ignore[union-attr]
        cost = local_missense_cost(values, full_codons, sense_codons)
        ell = project_syn_float(cost, families, index)
        robust = [-value for value in ell]
        cost_vectors[index_id] = robust
        y_raw[index_id] = project_onto_orthonormal(b1_basis, robust)
        y_perp[index_id] = project_onto_orthonormal(primary_basis, robust)
        property_payload[index_id] = {
            "label": PROPERTY_LABELS[index_id],
            "raw_norm": round_float(norm(y_raw[index_id])),
            "orthogonalized_norm": round_float(norm(y_perp[index_id])),
        }

    rows = build_rows(panel, sense_codons, families, index, b1_basis, primary_basis, y_raw, y_perp)
    domain_summary = domain_genus_summary(rows)
    thick_domains = [domain for domain, values in domain_summary.items() if int(values.get("genera", 0)) >= MIN_GENERA]
    if len(thick_domains) < 2:
        emit(
            "needs_external",
            reason="fewer than two domains have at least MIN_GENERA independent genera",
            n_genera=sum(values["genera"] for values in domain_summary.values()),
            n_domains=len(domain_summary),
            n_organisms=len(rows),
            domain_summary=domain_summary,
            fetch_probe=compact_panel(panel),
            panel_cache_path=str(PANEL_CACHE_PATH),
            scope_note="bio-internal E1 mechanism audit; not Window6; edge-hiding escape control is a synonymous-neighbor-degree proxy",
        )

    raw_T_pr, raw_per_genus_pr = statistic(rows, f"C_raw_{PR_INDEX}")
    T_pr, per_genus_pr = statistic(rows, f"C_perp_{PR_INDEX}")
    if raw_T_pr is None or T_pr is None:
        emit(
            "needs_external",
            reason="primary cosine is non-estimable",
            fetch_probe=compact_panel(panel),
            panel_cache_path=str(PANEL_CACHE_PATH),
            scope_note="bio-internal E1 mechanism audit; not Window6; edge-hiding escape control is a synonymous-neighbor-degree proxy",
        )

    x_ratios_by_genus: dict[str, list[float]] = defaultdict(list)
    for row in rows:
        x_ratios_by_genus[str(row["genus"])].append(float(row["x_ratio"]))
    gate1_value = genus_weighted_median(x_ratios_by_genus)
    gate2_value = (norm(y_perp[PR_INDEX]) ** 2) / max(norm(y_raw[PR_INDEX]) ** 2, NORM_FLOOR)
    code_gate = code_table_sanity({aa: float(records[PR_INDEX]["values"][aa]) for aa in records[PR_INDEX]["values"]}, full_codons, families)  # type: ignore[index]
    gate_payload = {
        "gate1_e1_estimability_median_x_perp_over_x": round_float(gate1_value),
        "gate1_passed": gate1_value >= 0.10,
        "gate2_cost_carrier_estimability_y_perp_over_y": round_float(gate2_value),
        "gate2_passed": gate2_value >= 0.10,
        "gate3_code_table_sanity": code_gate,
        "gate4_no_stop_artifact": {
            "passed": True,
            "main_endpoint": "sense codons only; Stop neighbors excluded from local missense cost",
            "stop_neighbor_policy": "excluded before cost averaging",
        },
    }
    gates_passed = bool(gate_payload["gate1_passed"]) and bool(gate_payload["gate2_passed"]) and bool(code_gate["passed"])

    domains = sorted(domain_summary)
    null_a, null_a_max, null_a_domains, null_a_audit = null_distributions(
        rows, cost_vectors, families, primary_basis, sense_codons, index, NULL_A_SEED, False, domains
    )
    null_b, null_b_max, null_b_domains, null_b_audit = null_distributions(
        rows, cost_vectors, families, primary_basis, sense_codons, index, NULL_B_SEED, True, domains
    )
    p_a = p_value_ge(float(T_pr), null_a[PR_INDEX])
    p_b = p_value_ge(float(T_pr), null_b[PR_INDEX])
    p_max_a = p_value_ge(float(T_pr), null_a_max)
    p_max_b = p_value_ge(float(T_pr), null_b_max)
    bootstrap_lower = bootstrap_lower95(per_genus_pr, BOOTSTRAP_SEED)

    property_stats = {}
    observed_battery_values = []
    for index_id in PROPERTY_LABELS:
        obs, per_genus = statistic(rows, f"C_perp_{index_id}")
        obs_value = float(obs) if obs is not None else 0.0
        observed_battery_values.append(obs_value)
        property_stats[index_id] = {
            "label": PROPERTY_LABELS[index_id],
            "T": round_float(obs_value),
            "p_null_A": round_float(p_value_ge(obs_value, null_a[index_id])),
            "p_null_B": round_float(p_value_ge(obs_value, null_b[index_id])),
            "per_genus": {genus: round_float(value) for genus, value in per_genus.items()},
        }
    observed_battery_max = max(observed_battery_values)
    battery_max_p_observed_max_a = p_value_ge(observed_battery_max, null_a_max)
    battery_max_p_observed_max_b = p_value_ge(observed_battery_max, null_b_max)

    per_domain = {}
    domain_certifying = 0
    domain_same_direction = 0
    for domain in domains:
        domain_rows = [row for row in rows if row["domain"] == domain]
        domain_T, domain_per_genus = statistic(domain_rows, f"C_perp_{PR_INDEX}")
        if domain_T is None:
            continue
        p_domain_a = p_value_ge(float(domain_T), null_a_domains[domain])
        p_domain_b = p_value_ge(float(domain_T), null_b_domains[domain])
        if domain_T > 0:
            domain_same_direction += 1
        if domain_T > 0 and p_domain_a <= 0.01 and p_domain_b <= 0.01:
            domain_certifying += 1
        per_domain[domain] = {
            "T_PR": round_float(float(domain_T)),
            "p_null_A": round_float(p_domain_a),
            "p_null_B": round_float(p_domain_b),
            "n_genera": len(domain_per_genus),
            "n_organisms": len(domain_rows),
            "thick_domain": len(domain_per_genus) >= MIN_GENERA,
        }

    loo = leave_one_family_out(rows, y_perp[PR_INDEX], families, index)
    raw_edge_basis = basis_without_named_components(
        b1_basis,
        [project_onto_orthonormal(b1_basis, project_syn_float(synonymous_escape_degree(sense_codons), families, index))],
    )
    y_edge_only_control = project_onto_orthonormal(raw_edge_basis, cost_vectors[PR_INDEX])
    edge_control_rows = []
    for row in rows:
        x_edge = project_onto_orthonormal(raw_edge_basis, row["x_raw"])  # type: ignore[arg-type]
        edge_control_rows.append({**row, "C_edge_control_only": vector_cos(x_edge, y_edge_only_control)})
    T_edge_control_only, _edge_clusters = statistic(edge_control_rows, "C_edge_control_only")

    certified = (
        gates_passed
        and float(T_pr) > 0
        and p_a <= 0.01
        and p_b <= 0.01
        and bootstrap_lower is not None
        and bootstrap_lower > 0.0
        and p_max_a <= 0.01
        and p_max_b <= 0.01
        and domain_certifying >= 2
        and domain_same_direction >= min(3, len(per_domain))
        and float(loo["positive_fraction"]) >= 0.80
    )
    raw_pass = raw_T_pr is not None and raw_T_pr > 0
    coincidence = (
        (raw_pass and (p_b > 0.01 or not gates_passed))
        or p_max_a > 0.01
        or p_max_b > 0.01
        or domain_certifying < 2
        or domain_same_direction < min(3, len(per_domain))
        or float(loo["positive_fraction"]) < 0.80
        or bootstrap_lower is None
        or bootstrap_lower <= 0.0
    )
    if certified:
        status = "certified"
    elif not gates_passed:
        status = "needs_external"
    elif float(T_pr) <= 0 or p_a > 0.05 or p_b > 0.05 or bootstrap_lower is None or bootstrap_lower <= 0.0:
        status = "refuted"
    elif coincidence:
        status = "coincidence"
    else:
        status = "refuted"

    emit(
        status,
        T_PR={
            "Version_A_raw": round_float(float(raw_T_pr)),
            "Version_B_GC_wobble_edge_orthogonalized": round_float(float(T_pr)),
        },
        null_p_values={
            "Null_A_global_within_family_PR": round_float(p_a),
            "Null_B_GC_wobble_stratified_PR": round_float(p_b),
            "Null_C_max_over_property_PR_against_max_A": round_float(p_max_a),
            "Null_C_max_over_property_PR_against_max_B": round_float(p_max_b),
            "observed_battery_max_against_max_A": round_float(battery_max_p_observed_max_a),
            "observed_battery_max_against_max_B": round_float(battery_max_p_observed_max_b),
        },
        bootstrap_lower95=round_float(bootstrap_lower),
        per_domain_T=per_domain,
        leave_one_aa_family_out=loo,
        validity_gates=gate_payload,
        battery=property_stats,
        battery_max_null={
            "observed_PR": round_float(float(T_pr)),
            "observed_battery_max": round_float(observed_battery_max),
            "null_A_max_mean": round_float(mean(null_a_max)),
            "null_B_max_mean": round_float(mean(null_b_max)),
        },
        edge_hiding_control_comparison={
            "edge_control_only_T_PR": round_float(float(T_edge_control_only)) if T_edge_control_only is not None else None,
            "full_control_T_PR": round_float(float(T_pr)),
            "control_basis": control_audit,
            "control_names": control_names,
        },
        confound_null_audit={
            "Null_A": null_a_audit,
            "Null_B": null_b_audit,
        },
        n_genera=sum(values["genera"] for values in domain_summary.values()),
        n_domains=len(domain_summary),
        n_organisms=len(rows),
        domain_summary=domain_summary,
        rank_B1=len(exact_b1_basis),
        rank_B1_after_controls=len(primary_basis),
        property_carrier=property_payload,
        n_null=N_NULL,
        n_bootstrap=N_BOOTSTRAP,
        panel_cache_path=str(PANEL_CACHE_PATH),
        fetch_probe=compact_panel(panel),
        honest_scope_note="bio-internal E1 mechanism audit; not Window6; edge-hiding escape control is a synonymous-neighbor-degree proxy",
    )


if __name__ == "__main__":
    main()

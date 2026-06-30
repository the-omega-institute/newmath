#!/usr/bin/env python3
"""Alternative-code deformation test for the codon-E1 certificate.

The statistic lives wholly in codon H(3,4) and code-table synonymy.  It is not
Window6 forcing; the verdict repeats that scope boundary.
"""
from __future__ import annotations

from collections import defaultdict
from itertools import product
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import random
import sys
from typing import Any


EXPERIMENT_ID = "codon_e1_alternative_code_deformation"
CLAIM_ID = "bridge.genetic_code.codon_e1_alternative_code_deformation"
BASES = ("U", "C", "A", "G")
N_NULL = 20000
N_BOOTSTRAP = 10000
ALPHA = 0.01
MIN_ORGANISMS_PER_TABLE = 3
TOL = 1.0e-12
MGS_TOL = 1.0e-10
NULL_SEED_PREFIX = "codon_e1_alternative_code_deformation.global_synonymous_relabel"
BOOTSTRAP_SEED_PREFIX = "codon_e1_alternative_code_deformation.cluster_bootstrap"

EXPERIMENT_DIR = Path(__file__).resolve().parent
REPO_ROOT = EXPERIMENT_DIR.parents[2]
GENETIC_CODES_PATH = REPO_ROOT / "tools" / "bio_reality" / "data" / "ncbi_genetic_codes.json"
PROBE_PATH = EXPERIMENT_DIR / "_altcode_fetch_probe.py"


def load_probe_module() -> Any:
    spec = importlib.util.spec_from_file_location("_altcode_fetch_probe", PROBE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load _altcode_fetch_probe.py")
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


def percentile(values: list[float], q: float) -> float:
    ordered = sorted(values)
    if not ordered:
        raise ValueError("empty percentile")
    pos = (len(ordered) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return ordered[lo]
    return ordered[lo] * (hi - pos) + ordered[hi] * (pos - lo)


def codon_order() -> list[str]:
    return ["".join(parts) for parts in product(BASES, repeat=3)]


def load_genetic_codes() -> dict[int, dict[str, object]]:
    payload = json.loads(GENETIC_CODES_PATH.read_text(encoding="utf-8"))
    tables: dict[int, dict[str, object]] = {}
    for item in payload["tables"]:
        table_id = int(item["table_id"])
        tables[table_id] = {
            "table_id": table_id,
            "name": item["name"],
            "codon_to_aa": dict(zip(payload["codon_order"], str(item["aa"]))),
        }
    return tables


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def norm(vector: list[float]) -> float:
    return math.sqrt(dot(vector, vector))


def modified_gram_schmidt(columns: list[list[float]], tol: float = MGS_TOL) -> list[list[float]]:
    basis: list[list[float]] = []
    for column in columns:
        working = column[:]
        for q in basis:
            coeff = dot(q, working)
            if coeff:
                for idx, q_value in enumerate(q):
                    working[idx] -= coeff * q_value
        size = norm(working)
        if size <= tol:
            continue
        basis.append([value / size for value in working])
    return basis


def first_order_rwk_columns(full_codons: list[str]) -> list[list[float]]:
    characters = (
        {"A": 1.0, "G": 1.0, "U": -1.0, "C": -1.0},  # R
        {"A": 1.0, "U": 1.0, "C": -1.0, "G": -1.0},  # W
        {"G": 1.0, "U": 1.0, "A": -1.0, "C": -1.0},  # K
    )
    columns: list[list[float]] = []
    for position in range(3):
        for character in characters:
            columns.append([character[codon[position]] for codon in full_codons])
    return columns


def sense_codons(codon_to_aa: dict[str, str], full_codons: list[str]) -> list[str]:
    return [codon for codon in full_codons if codon_to_aa[codon] != "*"]


def families_by_aa(codons: list[str], codon_to_aa: dict[str, str]) -> dict[str, list[str]]:
    families: dict[str, list[str]] = defaultdict(list)
    for codon in codons:
        families[codon_to_aa[codon]].append(codon)
    return dict(families)


def project_syn(vector: list[float], families: dict[str, list[str]], index: dict[str, int]) -> list[float]:
    out = vector[:]
    for family in families.values():
        family_mean = sum(vector[index[codon]] for codon in family) / len(family)
        for codon in family:
            out[index[codon]] -= family_mean
    return out


def max_abs_family_mean(vector: list[float], families: dict[str, list[str]], index: dict[str, int]) -> float:
    if not families:
        return 0.0
    return max(abs(sum(vector[index[codon]] for codon in family) / len(family)) for family in families.values())


def build_b1_basis(
    full_codons: list[str],
    sense: list[str],
    families: dict[str, list[str]],
    sense_index: dict[str, int],
) -> list[list[float]]:
    full_index = {codon: idx for idx, codon in enumerate(full_codons)}
    columns = []
    for full_column in first_order_rwk_columns(full_codons):
        restricted = [full_column[full_index[codon]] for codon in sense]
        columns.append(project_syn(restricted, families, sense_index))
    return modified_gram_schmidt(columns)


def build_standard_restricted_basis(
    full_codons: list[str],
    target_sense: list[str],
    target_families: dict[str, list[str]],
    target_index: dict[str, int],
    standard_codon_to_aa: dict[str, str],
) -> list[list[float]]:
    standard_sense = sense_codons(standard_codon_to_aa, full_codons)
    standard_index = {codon: idx for idx, codon in enumerate(standard_sense)}
    standard_families = families_by_aa(standard_sense, standard_codon_to_aa)
    standard_basis = build_b1_basis(full_codons, standard_sense, standard_families, standard_index)
    columns: list[list[float]] = []
    for q in standard_basis:
        extended = {codon: 0.0 for codon in full_codons}
        for codon in standard_sense:
            extended[codon] = q[standard_index[codon]]
        restricted = [extended[codon] for codon in target_sense]
        columns.append(project_syn(restricted, target_families, target_index))
    return modified_gram_schmidt(columns)


def residual_from_counts(
    counts: dict[str, int],
    total: int,
    sense: list[str],
    families: dict[str, list[str]],
    index: dict[str, int],
) -> list[float]:
    if total <= 0:
        raw = [0.0 for _ in sense]
    else:
        raw = [float(counts.get(codon, 0)) / total for codon in sense]
    return project_syn(raw, families, index)


def basis_quadratic(vector: list[float], q_basis: list[list[float]]) -> float:
    return sum(dot(vector, q) ** 2 for q in q_basis)


def r_value(vector: list[float], q_basis: list[list[float]]) -> float:
    norm_sq = dot(vector, vector)
    if norm_sq <= TOL:
        return math.nan
    return basis_quadratic(vector, q_basis) / norm_sq


def cluster_mean(values: dict[str, list[float]]) -> dict[str, float]:
    return {cluster: mean(items) for cluster, items in sorted(values.items()) if items}


def statistic_from_organisms(organisms: list[dict[str, object]], q_basis: list[list[float]]) -> tuple[float, dict[str, float]]:
    by_cluster: dict[str, list[float]] = defaultdict(list)
    for organism in organisms:
        value = r_value(organism["residual"], q_basis)  # type: ignore[arg-type]
        if math.isfinite(value):
            by_cluster[str(organism["cluster"])].append(value)
    per_cluster = cluster_mean(by_cluster)
    return mean(list(per_cluster.values())), per_cluster


def delta_statistic_from_organisms(
    organisms: list[dict[str, object]],
    q_basis: list[list[float]],
    standard_restricted_basis: list[list[float]],
) -> tuple[float, dict[str, float]]:
    by_cluster: dict[str, list[float]] = defaultdict(list)
    for organism in organisms:
        vector = organism["residual"]  # type: ignore[assignment]
        value = r_value(vector, q_basis) - r_value(vector, standard_restricted_basis)  # type: ignore[arg-type]
        if math.isfinite(value):
            by_cluster[str(organism["cluster"])].append(value)
    per_cluster = cluster_mean(by_cluster)
    return mean(list(per_cluster.values())), per_cluster


def family_permutation(families: dict[str, list[str]], rng: random.Random) -> dict[str, str]:
    permutation: dict[str, str] = {}
    for family in families.values():
        shuffled = family[:]
        rng.shuffle(shuffled)
        for source, target in zip(family, shuffled):
            permutation[source] = target
    return permutation


def apply_permutation(vector: list[float], permutation: dict[str, str], sense: list[str], index: dict[str, int]) -> list[float]:
    out = [0.0 for _ in sense]
    for source, target in permutation.items():
        out[index[target]] = vector[index[source]]
    return out


def relabeled_organisms(
    organisms: list[dict[str, object]],
    permutation: dict[str, str],
    sense: list[str],
    index: dict[str, int],
) -> list[dict[str, object]]:
    relabeled = []
    for organism in organisms:
        relabeled.append(
            {
                "cluster": organism["cluster"],
                "residual": apply_permutation(organism["residual"], permutation, sense, index),  # type: ignore[arg-type]
            }
        )
    return relabeled


def bootstrap_lower95(per_cluster: dict[str, float], center: float, seed_text: str) -> float:
    rng = random.Random(stable_seed(seed_text))
    clusters = sorted(per_cluster)
    values: list[float] = []
    for _draw in range(N_BOOTSTRAP):
        sampled = [per_cluster[rng.choice(clusters)] for _ in clusters]
        values.append(mean(sampled) - center)
    return percentile(values, 0.025)


def table_result(
    table_id: int,
    entries: list[dict[str, object]],
    codes: dict[int, dict[str, object]],
    full_codons: list[str],
) -> dict[str, object]:
    codon_to_aa = codes[table_id]["codon_to_aa"]  # type: ignore[assignment]
    standard_codon_to_aa = codes[1]["codon_to_aa"]  # type: ignore[assignment]
    sense = sense_codons(codon_to_aa, full_codons)  # type: ignore[arg-type]
    index = {codon: idx for idx, codon in enumerate(sense)}
    families = families_by_aa(sense, codon_to_aa)  # type: ignore[arg-type]
    residual_dim = sum(len(family) - 1 for family in families.values())
    q_basis = build_b1_basis(full_codons, sense, families, index)
    standard_restricted_basis = build_standard_restricted_basis(
        full_codons, sense, families, index, standard_codon_to_aa  # type: ignore[arg-type]
    )
    organisms: list[dict[str, object]] = []
    max_family_mean = 0.0
    for entry in entries:
        counts = entry["codon_counts_rna"]
        total = int(entry["total_sense_codons"])
        residual = residual_from_counts(counts, total, sense, families, index)  # type: ignore[arg-type]
        max_family_mean = max(max_family_mean, max_abs_family_mean(residual, families, index))
        if dot(residual, residual) > TOL:
            organisms.append({"cluster": entry["cluster"], "organism": entry["organism"], "residual": residual})

    observed_t, per_cluster = statistic_from_organisms(organisms, q_basis)
    observed_delta, per_cluster_delta = delta_statistic_from_organisms(
        organisms, q_basis, standard_restricted_basis
    )
    rng = random.Random(stable_seed(f"{NULL_SEED_PREFIX}.{table_id}"))
    null_values: list[float] = []
    null_delta_values: list[float] = []
    max_relabel_family_mean = 0.0
    for draw in range(N_NULL):
        permutation = family_permutation(families, rng)
        relabeled = relabeled_organisms(organisms, permutation, sense, index)
        if draw == 0 and relabeled:
            max_relabel_family_mean = max_abs_family_mean(relabeled[0]["residual"], families, index)  # type: ignore[arg-type]
        relabeled_t, _ = statistic_from_organisms(relabeled, q_basis)
        relabeled_delta, _ = delta_statistic_from_organisms(relabeled, q_basis, standard_restricted_basis)
        null_values.append(relabeled_t)
        null_delta_values.append(relabeled_delta)

    null_mean = mean(null_values)
    null_delta_mean = mean(null_delta_values)
    p = (sum(value >= observed_t for value in null_values) + 1) / (len(null_values) + 1)
    p_delta = (sum(value >= observed_delta for value in null_delta_values) + 1) / (len(null_delta_values) + 1)
    lower95 = bootstrap_lower95(per_cluster, null_mean, f"{BOOTSTRAP_SEED_PREFIX}.{table_id}.T")
    delta_lower95 = bootstrap_lower95(
        per_cluster_delta, null_delta_mean, f"{BOOTSTRAP_SEED_PREFIX}.{table_id}.delta"
    )
    isotropic_baseline = len(q_basis) / residual_dim if residual_dim > 0 else math.nan
    standard_baseline = mean(
        [r_value(organism["residual"], standard_restricted_basis) for organism in organisms]  # type: ignore[arg-type]
    )
    certified = p <= ALPHA and lower95 > 0.0 and observed_delta > 0.0 and p_delta <= ALPHA and delta_lower95 > 0.0
    refuted = observed_t <= isotropic_baseline or observed_delta <= 0.0
    return {
        "table_id": table_id,
        "table_name": codes[table_id]["name"],
        "n_organisms": len(entries),
        "n_clusters": len(per_cluster),
        "sense_codons": len(sense),
        "residual_dim": residual_dim,
        "rank_B1_t": len(q_basis),
        "rank_B1_standard_restricted": len(standard_restricted_basis),
        "T": observed_t,
        "null_mean": null_mean,
        "p": p,
        "bootstrap_lower95": lower95,
        "delta_T": observed_delta,
        "delta_null_mean": null_delta_mean,
        "p_delta": p_delta,
        "bootstrap_delta_lower95": delta_lower95,
        "isotropic_baseline": isotropic_baseline,
        "standard_restricted_mean": standard_baseline,
        "max_abs_family_mean": max_family_mean,
        "max_relabel_family_mean": max_relabel_family_mean,
        "per_cluster_T": per_cluster,
        "per_cluster_delta": per_cluster_delta,
        "certified": certified,
        "refuted": refuted,
    }


def needs_external_verdict(panel: dict[str, object]) -> None:
    fetch_probe = panel.get("source_status", {})
    details = (
        "alternative-code codon usage not fetchable: fewer than two code tables have at least "
        f"{MIN_ORGANISMS_PER_TABLE} numeric table-assigned organisms"
    )
    emit(
        "needs_external",
        reason=details,
        fetch_probe=fetch_probe,
        T_by_table={},
        null_mean_by_table={},
        p_by_table={},
        bootstrap_lower95_by_table={},
        delta_T_by_table={},
        isotropic_baseline_by_table={},
        n_organisms_by_table={},
        note="No alternative-code deformation verdict was computed; this is not Window6 forcing.",
    )


def main() -> None:
    try:
        probe = load_probe_module()
        panel = probe.build_panel(force_refresh=False)
        if not panel.get("fetchable"):
            needs_external_verdict(panel)

        codes = load_genetic_codes()
        full_codons = codon_order()
        by_table: dict[int, list[dict[str, object]]] = defaultdict(list)
        for entry in panel["organisms"]:
            table_id = int(entry["table_id"])
            if table_id != 1:
                by_table[table_id].append(entry)
        powered = {
            table_id: entries
            for table_id, entries in sorted(by_table.items())
            if len(entries) >= MIN_ORGANISMS_PER_TABLE
        }
        if len(powered) < 2:
            needs_external_verdict(panel)

        results = {table_id: table_result(table_id, entries, codes, full_codons) for table_id, entries in powered.items()}
        certified_tables = [table_id for table_id, result in results.items() if result["certified"]]
        refuted_tables = [table_id for table_id, result in results.items() if result["refuted"] and not result["certified"]]
        if certified_tables and len(certified_tables) == len(results):
            status = "certified"
        elif refuted_tables and len(refuted_tables) == len(results):
            status = "refuted"
        else:
            status = "coincidence"

        def by_table_float(key: str) -> dict[str, float | None]:
            return {str(table_id): round_float(result[key]) for table_id, result in results.items()}  # type: ignore[arg-type]

        note = (
            "This is a codon-E1 alternative-code deformation test with table-specific synonymy, "
            "matched within-family relabel nulls, and lineage-cluster bootstrap. It is not Window6 "
            "forcing and does not certify a Window6 bridge."
        )
        emit(
            status,
            T_by_table=by_table_float("T"),
            null_mean_by_table=by_table_float("null_mean"),
            p_by_table=by_table_float("p"),
            bootstrap_lower95_by_table=by_table_float("bootstrap_lower95"),
            delta_T_by_table=by_table_float("delta_T"),
            delta_null_mean_by_table=by_table_float("delta_null_mean"),
            p_delta_by_table=by_table_float("p_delta"),
            bootstrap_delta_lower95_by_table=by_table_float("bootstrap_delta_lower95"),
            isotropic_baseline_by_table=by_table_float("isotropic_baseline"),
            standard_restricted_mean_by_table=by_table_float("standard_restricted_mean"),
            n_organisms_by_table={str(table_id): result["n_organisms"] for table_id, result in results.items()},
            n_clusters_by_table={str(table_id): result["n_clusters"] for table_id, result in results.items()},
            rank_B1_by_table={str(table_id): result["rank_B1_t"] for table_id, result in results.items()},
            rank_B1_standard_restricted_by_table={
                str(table_id): result["rank_B1_standard_restricted"] for table_id, result in results.items()
            },
            n_null=N_NULL,
            n_bootstrap=N_BOOTSTRAP,
            table_details={
                str(table_id): {
                    "table_name": result["table_name"],
                    "per_cluster_T": {
                        cluster: round_float(value) for cluster, value in result["per_cluster_T"].items()
                    },
                    "per_cluster_delta": {
                        cluster: round_float(value) for cluster, value in result["per_cluster_delta"].items()
                    },
                    "max_abs_family_mean": round_float(result["max_abs_family_mean"], 14),
                    "max_relabel_family_mean": round_float(result["max_relabel_family_mean"], 14),
                    "certified": result["certified"],
                    "refuted": result["refuted"],
                }
                for table_id, result in results.items()
            },
            fetch_probe=panel.get("source_status", {}),
            note=note,
        )
    except Exception as exc:
        emit(
            "needs_external",
            reason=f"alternative-code codon usage not fetchable: {type(exc).__name__}:{exc}",
            fetch_probe={},
            T_by_table={},
            null_mean_by_table={},
            p_by_table={},
            bootstrap_lower95_by_table={},
            delta_T_by_table={},
            isotropic_baseline_by_table={},
            n_organisms_by_table={},
            note="Experiment failed before a valid alternative-code verdict; this is not Window6 forcing.",
        )


if __name__ == "__main__":
    main()

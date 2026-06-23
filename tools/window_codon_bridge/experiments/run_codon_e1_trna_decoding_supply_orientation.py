#!/usr/bin/env python3
"""Codon-E1/tRNA decoding-supply orientation concordance test.

This is not Window6 forcing and not a causal proof.  B1 is reused from the
frozen standard-code codon-E1 construction; no tRNA data refits B1.
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

import _e1_trna_fetch_probe as fetch_probe


EXPERIMENT_ID = "codon_e1_trna_decoding_supply_orientation"
CLAIM_ID = "bridge.genetic_code.codon_e1_trna_decoding_supply_orientation"
N_NULL = 20000
N_BOOTSTRAP = 10000
N_PANEL_TARGET = 30
MIN_GENOMES = 6
MIN_GENERA = 6
NORM_FLOOR = 1.0e-12
TOL = 1.0e-10
NULL_SEED = "codon_e1_trna_decoding_supply_orientation.global_synonymous_relabel"
RESTRICTED_NULL_SEED = "codon_e1_trna_decoding_supply_orientation.restricted_gc3_wobble_relabel"
BOOTSTRAP_SEED = "codon_e1_trna_decoding_supply_orientation.genus_bootstrap"
W_VERSION = "binary_wobble_bacteria_archaea_standard_table_1_11"
PENALTY_W_VERSION = "tai_style_wobble_penalty_bacteria_archaea_standard_table_1_11"

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[2]
PANEL_CACHE_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "codon_e1_trna_decoding_supply_orientation_panel.json"
)


def load_base_module() -> Any:
    path = SCRIPT_DIR / "run_codon_e1_heldout_crossorganism_gate.py"
    spec = importlib.util.spec_from_file_location("codon_e1_base", path)
    if spec is None or spec.loader is None:
        raise RuntimeError("could not load codon-E1 base module")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


base = load_base_module()


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def emit(status: str, **fields: object) -> None:
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
    }
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status in {"certified", "coincidence"} else (3 if status == "needs_external" else 2))


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


def stable_seed(text: str) -> int:
    return base.stable_seed(text)


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def norm(vector: list[float]) -> float:
    return math.sqrt(dot(vector, vector))


def subtract(left: list[float], right: list[float]) -> list[float]:
    return [a - b for a, b in zip(left, right)]


def scale(factor: float, vector: list[float]) -> list[float]:
    return [factor * value for value in vector]


def project_onto_basis(q_basis: list[list[float]], vector: list[float]) -> list[float]:
    result = [0.0 for _ in vector]
    for q in q_basis:
        coefficient = dot(q, vector)
        if coefficient == 0.0:
            continue
        for idx, value in enumerate(q):
            result[idx] += coefficient * value
    return result


def basis_coordinates(q_basis: list[list[float]], vector: list[float]) -> list[float]:
    return [dot(q, vector) for q in q_basis]


def anticodon_to_codons(anticodon: str, mode: str) -> dict[str, float]:
    anti = anticodon.upper().replace("T", "U")
    if len(anti) != 3:
        return {}
    first_options: dict[str, float]
    first = anti[0]
    if mode == "watson_crick":
        first_options = {complement(first): 1.0} if complement(first) else {}
    elif mode == "tai_penalty":
        first_options = wobble_options(first, penalty=True)
    else:
        first_options = wobble_options(first, penalty=False)
    second = complement(anti[1])
    third = complement(anti[2])
    if not second or not third:
        return {}
    result: dict[str, float] = {}
    for codon3, weight in first_options.items():
        codon = third + second + codon3
        if codon in base.CODON_TO_AA and base.CODON_TO_AA[codon] != "*":
            result[codon] = float(weight)
    return result


def complement(base_char: str) -> str | None:
    return {"A": "U", "U": "A", "C": "G", "G": "C", "I": None}.get(base_char)


def wobble_options(base_char: str, penalty: bool) -> dict[str, float]:
    if base_char == "A":
        return {"U": 1.0}
    if base_char == "C":
        return {"G": 1.0}
    if base_char == "G":
        return {"C": 1.0, "U": 0.5 if penalty else 1.0}
    if base_char == "U":
        return {"A": 1.0, "G": 0.5 if penalty else 1.0}
    if base_char == "I":
        value = 0.5 if penalty else 1.0
        return {"A": value, "C": value, "U": value}
    return {}


def supply_vector(
    anticodon_counts: dict[str, int],
    sense_codons: list[str],
    mode: str,
) -> list[float]:
    supply = {codon: 0.0 for codon in sense_codons}
    for anticodon, count in anticodon_counts.items():
        for codon, weight in anticodon_to_codons(anticodon, mode).items():
            if codon in supply:
                supply[codon] += int(count) * weight
    return [math.log1p(supply[codon]) for codon in sense_codons]


def vector_cos(left: list[float], right: list[float]) -> float | None:
    denom = norm(left) * norm(right)
    if denom <= NORM_FLOOR:
        return None
    return dot(left, right) / denom


def genus_weighted_mean(rows: list[dict[str, object]], key: str) -> tuple[float, dict[str, float], dict[str, list[float]]]:
    by_genus: dict[str, list[float]] = defaultdict(list)
    for row in rows:
        value = row.get(key)
        if value is None:
            continue
        by_genus[str(row["genus"])].append(float(value))
    per_genus = {genus: mean(values) for genus, values in sorted(by_genus.items()) if values}
    return mean(list(per_genus.values())), per_genus, by_genus


def bootstrap_lower95(per_genus: dict[str, float], seed: str) -> float:
    rng = random.Random(stable_seed(seed))
    genera = sorted(per_genus)
    values = []
    for _ in range(N_BOOTSTRAP):
        values.append(mean([per_genus[rng.choice(genera)] for _ in genera]))
    return percentile(values, 0.025)


def p_value_ge(observed: float, null_values: list[float]) -> float:
    return (sum(value >= observed for value in null_values) + 1) / (len(null_values) + 1)


def pearson(x_values: list[float], y_values: list[float]) -> float | None:
    if len(x_values) < 3 or len(x_values) != len(y_values):
        return None
    x_mean = mean(x_values)
    y_mean = mean(y_values)
    x = [value - x_mean for value in x_values]
    y = [value - y_mean for value in y_values]
    denom = norm(x) * norm(y)
    if denom <= NORM_FLOOR:
        return None
    return dot(x, y) / denom


def residualize_by_genus_gc3(rows: list[dict[str, object]], key: str) -> tuple[float, dict[str, float]]:
    by_genus_values: dict[str, list[tuple[float, float]]] = defaultdict(list)
    for row in rows:
        value = row.get(key)
        if value is not None:
            by_genus_values[str(row["genus"])].append((float(value), float(row["gc3"])))
    flat_y = [item[0] for values in by_genus_values.values() for item in values]
    flat_x = [item[1] for values in by_genus_values.values() for item in values]
    if len(flat_y) < 3:
        per_genus = {genus: mean([value for value, _gc in values]) for genus, values in by_genus_values.items()}
        return mean(list(per_genus.values())), per_genus
    x_mean = mean(flat_x)
    y_mean = mean(flat_y)
    xc = [value - x_mean for value in flat_x]
    yc = [value - y_mean for value in flat_y]
    denom = dot(xc, xc)
    slope = dot(yc, xc) / denom if denom > NORM_FLOOR else 0.0
    intercept = y_mean - slope * x_mean
    per_obs: dict[int, float] = {}
    cursor = 0
    by_genus_resid: dict[str, list[float]] = {}
    for genus, values in by_genus_values.items():
        residuals = []
        for value, gc in values:
            residuals.append(value - (intercept + slope * gc))
            per_obs[cursor] = residuals[-1]
            cursor += 1
        by_genus_resid[genus] = residuals
    per_genus = {genus: mean(values) for genus, values in sorted(by_genus_resid.items())}
    return mean(list(per_genus.values())), per_genus


def gc3_from_counts(counts: dict[str, int], sense_codons: list[str]) -> float:
    total = sum(int(counts[codon]) for codon in sense_codons)
    if total <= 0:
        return 0.0
    return sum(int(counts[codon]) for codon in sense_codons if codon[2] in {"G", "C"}) / total


def family_permutation(families: dict[str, list[str]], rng: random.Random) -> dict[str, str]:
    return base.family_permutation(families, rng)


def restricted_family_permutation(families: dict[str, list[str]], rng: random.Random) -> dict[str, str]:
    permutation: dict[str, str] = {}
    for family_codons in families.values():
        strata: dict[str, list[str]] = defaultdict(list)
        for codon in family_codons:
            strata["GC" if codon[2] in {"G", "C"} else "AU"].append(codon)
        for codons in strata.values():
            shuffled = codons[:]
            rng.shuffle(shuffled)
            for source, target in zip(codons, shuffled):
                permutation[source] = target
    return permutation


def apply_permutation_vector(
    vector: list[float],
    permutation: dict[str, str],
    sense_codons: list[str],
    sense_index: dict[str, int],
) -> list[float]:
    out = [0.0 for _ in sense_codons]
    for source, target in permutation.items():
        out[sense_index[target]] = vector[sense_index[source]]
    return out


def projector_without_vector(q_basis: list[list[float]], vector: list[float]) -> list[list[float]]:
    vector_norm = norm(vector)
    if vector_norm <= TOL:
        return [q[:] for q in q_basis]
    unit = scale(1.0 / vector_norm, vector)
    keep: list[list[float]] = []
    for q in q_basis:
        reduced = subtract(q, scale(dot(unit, q), unit))
        for prior in keep:
            reduced = subtract(reduced, scale(dot(prior, reduced), prior))
        norm_reduced = norm(reduced)
        if norm_reduced > TOL:
            keep.append(scale(1.0 / norm_reduced, reduced))
    return keep


def build_component_basis(
    sense_codons: list[str],
    families: dict[str, list[str]],
    sense_index: dict[str, int],
) -> tuple[list[str], list[list[float]]]:
    rows: list[tuple[str, list[float]]] = []
    for position in range(3):
        for character in ("R", "W", "K"):
            raw = [chemical_character(character, codon[position]) for codon in sense_codons]
            projected = base.project_syn(raw, families, sense_index)
            rows.append((f"p{position + 1}_{character}", projected))
    names = [name for name, _vec in rows]
    vectors = [vec for _name, vec in rows]
    return names, vectors


def chemical_character(character: str, base_char: str) -> float:
    values = {
        "R": {"A": 1.0, "G": 1.0, "C": -1.0, "U": -1.0},
        "W": {"A": 1.0, "U": 1.0, "C": -1.0, "G": -1.0},
        "K": {"U": 1.0, "G": 1.0, "C": -1.0, "A": -1.0},
    }
    return values[character][base_char]


def build_panel(force_refresh: bool = False) -> dict[str, object]:
    if PANEL_CACHE_PATH.exists() and not force_refresh:
        cached = json.loads(PANEL_CACHE_PATH.read_text(encoding="utf-8"))
        if int(cached.get("n_genomes", 0)) >= N_PANEL_TARGET:
            return cached
    summaries, source_status = fetch_probe.candidate_summaries(retmax=260)
    organisms: list[dict[str, object]] = []
    attempts: list[dict[str, object]] = []
    seen_genera: set[str] = set()
    for summary in summaries:
        if len(organisms) >= N_PANEL_TARGET:
            break
        row = fetch_probe.fetch_assembly_payload(summary)
        attempts.append(fetch_probe.compact_attempt(row))
        if not row.get("ok_numeric"):
            continue
        genus = str(row["genus"])
        if genus in seen_genera:
            continue
        seen_genera.add(genus)
        organisms.append(
            {
                "assembly_accession": row["assembly_accession"],
                "organism": row["organism"],
                "species_name": row["species_name"],
                "genus": row["genus"],
                "taxid": row["taxid"],
                "transl_table": row["transl_table"],
                "ftp_path_refseq": row["ftp_path_refseq"],
                "codon_counts_rna": row["codon_counts_rna"],
                "trna_anticodon_counts_rna": row["trna_anticodon_counts_rna"],
                "cds_meta": row["cds_meta"],
                "trna_meta": row["trna_meta"],
                "sample_codon_counts": row["sample_codon_counts"],
                "sample_trna_anticodon_counts": row["sample_trna_anticodon_counts"],
            }
        )
    panel = {
        "generated_at": now_iso(),
        "provenance": {
            "source": "RefSeq assembly FTP via NCBI EUtils assembly summaries",
            "files": ["*_cds_from_genomic.fna.gz", "*_genomic.gff.gz", "*_genomic.gbff.gz fallback"],
            "not_window6": True,
            "not_causal_closure": True,
        },
        "sense_codon_order_rna": base.sense_codon_order(),
        "fetchability_source_status": source_status,
        "attempts_compact": attempts,
        "organisms": organisms,
        "n_genomes": len(organisms),
        "n_genera": len({str(item["genus"]) for item in organisms}),
        "panel_target": N_PANEL_TARGET,
        "filters": {
            "assembly_level": "Complete Genome",
            "transl_table_allowed": [1, 11],
            "min_complete_cds": 300,
            "one_genome_per_genus": True,
        },
    }
    PANEL_CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    PANEL_CACHE_PATH.write_text(json.dumps(panel, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return panel


def compute_rows(
    panel: dict[str, object],
    mode: str,
    q_basis: list[list[float]],
    q_minus: list[list[float]],
    component_vectors: list[list[float]],
    p3_unit: list[float],
    sense_codons: list[str],
    families: dict[str, list[str]],
    sense_index: dict[str, int],
) -> list[dict[str, object]]:
    rows = []
    for entry in panel["organisms"]:
        assert isinstance(entry, dict)
        counts = entry["codon_counts_rna"]
        anticodons = entry["trna_anticodon_counts_rna"]
        assert isinstance(counts, dict) and isinstance(anticodons, dict)
        total = sum(int(counts[codon]) for codon in sense_codons)
        usage = [int(counts[codon]) / total for codon in sense_codons]
        d = base.project_syn(usage, families, sense_index)
        supply = supply_vector({str(k): int(v) for k, v in anticodons.items()}, sense_codons, mode)
        s = base.project_syn(supply, families, sense_index)
        x = project_onto_basis(q_basis, d)
        y = project_onto_basis(q_basis, s)
        xm = project_onto_basis(q_minus, d)
        ym = project_onto_basis(q_minus, s)
        x_full41 = d
        y_full41 = s
        component_num = [
            (dot(vector, d) * dot(vector, s)) / max(dot(vector, vector), NORM_FLOOR)
            for vector in component_vectors
        ]
        denom = dot(x, y)
        component_contrib = {
            f"basis_{idx}": value / denom if abs(denom) > NORM_FLOOR else None
            for idx, value in enumerate(component_num)
        }
        rows.append(
            {
                "assembly_accession": entry["assembly_accession"],
                "organism": entry["organism"],
                "genus": entry["genus"],
                "gc3": gc3_from_counts({str(k): int(v) for k, v in counts.items()}, sense_codons),
                "C_full": vector_cos(x, y),
                "C_minus_p3W": vector_cos(xm, ym),
                "C_positive": vector_cos(x_full41, y_full41),
                "x": x,
                "y": y,
                "xm": xm,
                "ym": ym,
                "d": d,
                "s": s,
                "p3W_usage_mass": dot(d, p3_unit) ** 2 / max(dot(x, x), NORM_FLOOR),
                "p3W_supply_mass": dot(s, p3_unit) ** 2 / max(dot(y, y), NORM_FLOOR),
                "component_contrib": component_contrib,
            }
        )
    return rows


def statistic_from_rows(rows: list[dict[str, object]], key: str, gc_residualize: bool = False) -> tuple[float, dict[str, float]]:
    if gc_residualize:
        return residualize_by_genus_gc3(rows, key)
    observed, per_genus, _raw = genus_weighted_mean(rows, key)
    return observed, per_genus


def relabeled_stat(
    rows: list[dict[str, object]],
    permutation: dict[str, str],
    q_basis: list[list[float]],
    q_minus: list[list[float]],
    sense_codons: list[str],
    sense_index: dict[str, int],
    key: str,
    gc_residualize: bool = False,
) -> float:
    relabeled_rows = []
    for row in rows:
        d = [float(value) for value in row["d"]]  # type: ignore[union-attr]
        s = [float(value) for value in row["s"]]  # type: ignore[union-attr]
        sp = apply_permutation_vector(s, permutation, sense_codons, sense_index)
        if key == "C_full":
            x = project_onto_basis(q_basis, d)
            y = project_onto_basis(q_basis, sp)
        elif key == "C_minus_p3W":
            x = project_onto_basis(q_minus, d)
            y = project_onto_basis(q_minus, sp)
        elif key == "C_positive":
            x = d
            y = sp
        else:
            raise ValueError(key)
        relabeled_rows.append({**row, key: vector_cos(x, y)})
    return statistic_from_rows(relabeled_rows, key, gc_residualize=gc_residualize)[0]


def null_values(
    rows: list[dict[str, object]],
    families: dict[str, list[str]],
    q_basis: list[list[float]],
    q_minus: list[list[float]],
    sense_codons: list[str],
    sense_index: dict[str, int],
    key: str,
    seed: str,
    restricted: bool = False,
    gc_residualize: bool = False,
) -> list[float]:
    rng = random.Random(stable_seed(seed))
    values = []
    for _ in range(N_NULL):
        permutation = restricted_family_permutation(families, rng) if restricted else family_permutation(families, rng)
        values.append(relabeled_stat(rows, permutation, q_basis, q_minus, sense_codons, sense_index, key, gc_residualize))
    return values


def component_ledger(rows: list[dict[str, object]], component_names: list[str]) -> dict[str, object]:
    sums = {name: 0.0 for name in component_names}
    n = 0
    for row in rows:
        contrib = row["component_contrib"]
        assert isinstance(contrib, dict)
        values = list(contrib.values())
        if any(value is None for value in values):
            continue
        n += 1
        for idx, name in enumerate(component_names):
            sums[name] += float(contrib[f"basis_{idx}"])
    means = {name: sums[name] / n for name in component_names} if n else {name: math.nan for name in component_names}
    grouped = {
        "p3_W": means.get("p3_W"),
        "p3_R": means.get("p3_R"),
        "p1_RWK": sum(means.get(f"p1_{char}", 0.0) for char in ("R", "W", "K")),
        "p2_surviving": sum(means.get(f"p2_{char}", 0.0) for char in ("R", "W", "K")),
        "p3_other": means.get("p3_K", 0.0),
    }
    return {
        "component_order": component_names,
        "mean_dot_contribution_fraction": {key: round_float(value) for key, value in means.items()},
        "grouped": {key: round_float(value) for key, value in grouped.items()},
        "mean_p3W_usage_mass": round_float(mean([float(row["p3W_usage_mass"]) for row in rows])),
        "mean_p3W_supply_mass": round_float(mean([float(row["p3W_supply_mass"]) for row in rows])),
    }


def main() -> None:
    full_codons = base.codon_order()
    sense_codons = base.sense_codon_order()
    sense_index = {codon: idx for idx, codon in enumerate(sense_codons)}
    families = base.families_by_aa(sense_codons)
    _projector, q_basis_list, rank_b1 = base.build_b1_projector(full_codons, sense_codons, families, sense_index)
    q_basis = [list(row) for row in q_basis_list]
    component_names, component_vectors = build_component_basis(sense_codons, families, sense_index)
    p3_vector = component_vectors[component_names.index("p3_W")]
    p3_in_b1 = project_onto_basis(q_basis, p3_vector)
    p3_unit = scale(1.0 / max(norm(p3_in_b1), NORM_FLOOR), p3_in_b1)
    q_minus = projector_without_vector(q_basis, p3_unit)

    panel = build_panel(force_refresh=False)
    if int(panel.get("n_genomes", 0)) < MIN_GENOMES or int(panel.get("n_genera", 0)) < MIN_GENERA:
        emit(
            "needs_external",
            reason="fewer than the required complete RefSeq genomes yielded numeric CDS codon counts and tRNA anticodon copy numbers",
            fetch_probe={
                "panel_cache_path": str(PANEL_CACHE_PATH),
                "n_genomes": panel.get("n_genomes"),
                "n_genera": panel.get("n_genera"),
                "attempts_compact": panel.get("attempts_compact"),
            },
            note="not Window6 forcing; not causal closure",
        )

    rows = compute_rows(panel, "binary", q_basis, q_minus, component_vectors, p3_unit, sense_codons, families, sense_index)
    penalty_rows = compute_rows(panel, "tai_penalty", q_basis, q_minus, component_vectors, p3_unit, sense_codons, families, sense_index)
    wc_rows = compute_rows(panel, "watson_crick", q_basis, q_minus, component_vectors, p3_unit, sense_codons, families, sense_index)

    T_full, per_genus_full = statistic_from_rows(rows, "C_full")
    T_minus, per_genus_minus = statistic_from_rows(rows, "C_minus_p3W", gc_residualize=True)
    T_positive, per_genus_positive = statistic_from_rows(rows, "C_positive")
    null_full = null_values(rows, families, q_basis, q_minus, sense_codons, sense_index, "C_full", NULL_SEED)
    null_minus = null_values(
        rows,
        families,
        q_basis,
        q_minus,
        sense_codons,
        sense_index,
        "C_minus_p3W",
        NULL_SEED + ".minus_p3W_gc3",
        gc_residualize=True,
    )
    restricted_minus = null_values(
        rows,
        families,
        q_basis,
        q_minus,
        sense_codons,
        sense_index,
        "C_minus_p3W",
        RESTRICTED_NULL_SEED,
        restricted=True,
        gc_residualize=True,
    )
    null_positive = null_values(rows, families, q_basis, q_minus, sense_codons, sense_index, "C_positive", NULL_SEED + ".positive")

    p_full = p_value_ge(T_full, null_full)
    p_minus = p_value_ge(T_minus, null_minus)
    p_restricted = p_value_ge(T_minus, restricted_minus)
    positive_p = p_value_ge(T_positive, null_positive)
    positive_passed = T_positive > 0.0 and positive_p <= 0.01
    lower_full = bootstrap_lower95(per_genus_full, BOOTSTRAP_SEED + ".full")
    lower_minus = bootstrap_lower95(per_genus_minus, BOOTSTRAP_SEED + ".minus_p3W")

    wc_t, _wc_g = statistic_from_rows(wc_rows, "C_full")
    penalty_t, _penalty_g = statistic_from_rows(penalty_rows, "C_full")

    all_checks_ok = rank_b1 == 6 and len(q_minus) == 5 and int(panel["n_genomes"]) >= MIN_GENOMES
    if not all_checks_ok or not positive_passed:
        status = "refuted"
    elif p_full <= 0.01 and lower_full > 0.0 and p_minus <= 0.01 and lower_minus > 0.0 and p_restricted <= 0.01:
        status = "certified"
    elif p_full <= 0.01:
        status = "coincidence"
    else:
        status = "refuted"

    emit(
        status,
        T_full=round_float(T_full),
        p_full=round_float(p_full),
        bootstrap_lower95_full=round_float(lower_full),
        T_minus_p3W=round_float(T_minus),
        p_minus_p3W=round_float(p_minus),
        bootstrap_lower95_minus_p3W=round_float(lower_minus),
        T_restricted_null_p=round_float(p_restricted),
        positive_control={
            "corr": round_float(T_positive),
            "p": round_float(positive_p),
            "passed": bool(positive_passed),
            "bootstrap_lower95": round_float(bootstrap_lower95(per_genus_positive, BOOTSTRAP_SEED + ".positive")),
        },
        component_ledger=component_ledger(rows, component_names),
        n_genomes=int(panel["n_genomes"]),
        n_genera=int(panel["n_genera"]),
        rank_B1=rank_b1,
        rank_B1_minus_p3W=len(q_minus),
        W_version=W_VERSION,
        W_sensitivity={
            "watson_crick_only_T_full": round_float(wc_t),
            "tai_style_penalty_T_full": round_float(penalty_t),
            "penalty_W_version": PENALTY_W_VERSION,
        },
        n_null=N_NULL,
        n_bootstrap=N_BOOTSTRAP,
        norm_floor=NORM_FLOOR,
        relabel_seed=base.stable_seed(NULL_SEED),
        restricted_relabel_seed=base.stable_seed(RESTRICTED_NULL_SEED),
        panel_cache_path=str(PANEL_CACHE_PATH),
        per_genus_full={genus: round_float(value) for genus, value in per_genus_full.items()},
        per_genus_minus_p3W_gc3_residualized={genus: round_float(value) for genus, value in per_genus_minus.items()},
        note=(
            "decoding-supply orientation concordance only; not Window6 forcing; "
            "not causal closure or causal proof; B1 is reused from the frozen standard-code artifact and is not refit"
        ),
    )


if __name__ == "__main__":
    main()

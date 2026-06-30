#!/usr/bin/env python3
"""Neutral-edge tRNA proxy coupling against the Window6 edge score.

The data boundary is deliberately narrow: real per-gene codon counts, a fixed
global tAI/tRNA proxy vector, and the pre-registered neutral synonymous
Hamming-1 edge graph. Because the tRNA proxy is global, the strict model with
edge fixed effects cannot identify edge-only regressors; the estimable result
below is therefore marked reduced and keeps the edge-FE diagnostic explicit.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import product
import glob
import json
import math
import random
import sys
from pathlib import Path


EXPERIMENT_ID = "claim20_neutral_trna_edge_coupling"
CLAIM_ID = "bridge.genetic_code.neutral_trna_edge_coupling"
DATA_DIR = Path("tools/bio_reality/data")
SELECTION_VECTOR_PATH = Path("papers/window_codon_bridge/data/codon_q6_selection_vectors.json")
RANDOM_SEED = 200620
GENES_PER_SPECIES = 25
MIN_PAIR_COUNT = 5
CV_SPLITS = 5
NULL_DRAWS = 100
RESIDUALIZE_PASSES = 3

BASES = ("U", "C", "A", "G")
ALL_CODONS = ["".join(chars) for chars in product(BASES, repeat=3)]
THIRD_GC = {"G", "C"}

CODON_TO_AA = {
    "UUU": "F", "UUC": "F", "UUA": "L", "UUG": "L",
    "UCU": "S", "UCC": "S", "UCA": "S", "UCG": "S",
    "UAU": "Y", "UAC": "Y", "UAA": "*", "UAG": "*",
    "UGU": "C", "UGC": "C", "UGA": "*", "UGG": "W",
    "CUU": "L", "CUC": "L", "CUA": "L", "CUG": "L",
    "CCU": "P", "CCC": "P", "CCA": "P", "CCG": "P",
    "CAU": "H", "CAC": "H", "CAA": "Q", "CAG": "Q",
    "CGU": "R", "CGC": "R", "CGA": "R", "CGG": "R",
    "AUU": "I", "AUC": "I", "AUA": "I", "AUG": "M",
    "ACU": "T", "ACC": "T", "ACA": "T", "ACG": "T",
    "AAU": "N", "AAC": "N", "AAA": "K", "AAG": "K",
    "AGU": "S", "AGC": "S", "AGA": "R", "AGG": "R",
    "GUU": "V", "GUC": "V", "GUA": "V", "GUG": "V",
    "GCU": "A", "GCC": "A", "GCA": "A", "GCG": "A",
    "GAU": "D", "GAC": "D", "GAA": "E", "GAG": "E",
    "GGU": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def normalize_codon(codon: str) -> str:
    return codon.upper().replace("T", "U")


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def sample_sd(values: list[float]) -> float:
    if len(values) < 2:
        return 0.0
    center = mean(values)
    return math.sqrt(sum((value - center) ** 2 for value in values) / (len(values) - 1))


def zscore_by_group(values: dict[int, float], groups: dict[int, str]) -> dict[int, float]:
    by_group: dict[str, list[tuple[int, float]]] = defaultdict(list)
    for key, value in values.items():
        by_group[groups[key]].append((key, value))
    result: dict[int, float] = {}
    for items in by_group.values():
        raw = [value for _key, value in items]
        center = mean(raw)
        scale = sample_sd(raw)
        for key, value in items:
            result[key] = 0.0 if scale <= 0.0 else (value - center) / scale
    return result


def round_float(value: float | None, digits: int = 10) -> float | None:
    if value is None or not math.isfinite(value):
        return None
    return round(float(value), digits)


def load_selection_vectors() -> dict[str, dict[str, float]]:
    data = json.loads(SELECTION_VECTOR_PATH.read_text(encoding="utf-8"))
    vectors: dict[str, dict[str, float]] = {}
    for row in data.get("vectors", []):
        codon = normalize_codon(str(row.get("codon", "")))
        if codon not in ALL_CODONS:
            continue
        if CODON_TO_AA[codon] == "*":
            continue
        vectors[codon] = {
            "d_perp": float(row["d_perp_loading"]),
            "f3": float(row["f3_loading"]),
            "tai": float(row["trna_supply_tai_mean"]),
        }
    if len(vectors) != 61:
        raise ValueError(f"selection vector file yielded {len(vectors)} sense codons, expected 61")
    return vectors


def hamming1(left: str, right: str) -> bool:
    return sum(1 for a, b in zip(left, right) if a != b) == 1


def neutral_edges(codons: list[str]) -> list[dict[str, object]]:
    degree: Counter[str] = Counter()
    pairs: list[tuple[str, str, str]] = []
    for index, left in enumerate(codons):
        aa = CODON_TO_AA[left]
        for right in codons[index + 1:]:
            if CODON_TO_AA[right] == aa and hamming1(left, right):
                degree[left] += 1
                degree[right] += 1
                if aa != "*":
                    pairs.append((left, right, aa))
    edge_rows = []
    for edge_id, (left, right, aa) in enumerate(pairs):
        left_class = degree_class(degree[left])
        right_class = degree_class(degree[right])
        edge_rows.append(
            {
                "edge_id": edge_id,
                "c1": left,
                "c2": right,
                "aa": aa,
                "edge_class": "-".join(sorted((left_class, right_class))),
            }
        )
    return edge_rows


def degree_class(degree: int) -> str:
    if degree == 3:
        return "deg3"
    if degree == 1:
        return "deg1"
    if degree == 2:
        return "deg2"
    return "deg0or4"


def decorate_edges(
    base_edges: list[dict[str, object]],
    vectors: dict[str, dict[str, float]],
    mapping: dict[str, str] | None = None,
) -> list[dict[str, object]]:
    mapping = mapping or {codon: codon for codon in ALL_CODONS}
    raw_h: dict[int, float] = {}
    raw_t: dict[int, float] = {}
    aa_by_edge: dict[int, str] = {}
    provisional: list[dict[str, object]] = []
    for base in base_edges:
        edge_id = int(base["edge_id"])
        c1 = mapping[str(base["c1"])]
        c2 = mapping[str(base["c2"])]
        aa = str(base["aa"])
        raw_h[edge_id] = abs(vectors[c1]["d_perp"] - vectors[c2]["d_perp"])
        raw_t[edge_id] = math.log(vectors[c1]["tai"] + 0.5) - math.log(vectors[c2]["tai"] + 0.5)
        aa_by_edge[edge_id] = aa
        provisional.append(
            {
                "edge_id": edge_id,
                "c1": c1,
                "c2": c2,
                "aa": aa,
                "edge_class": str(base["edge_class"]),
                "delta_gc3": float((c1[2] in THIRD_GC) - (c2[2] in THIRD_GC)),
                "delta_f3": vectors[c1]["f3"] - vectors[c2]["f3"],
            }
        )
    h_center = mean(list(raw_h.values()))
    h_scale = sample_sd(list(raw_h.values()))
    h_values = {key: 0.0 if h_scale <= 0.0 else (value - h_center) / h_scale for key, value in raw_h.items()}
    t_values = zscore_by_group(raw_t, aa_by_edge)
    for row in provisional:
        edge_id = int(row["edge_id"])
        row["H"] = h_values[edge_id]
        row["T"] = t_values[edge_id]
    return provisional


def third_gc_value(codon: str) -> int:
    return int(codon[2] in THIRD_GC)


def gc3_preserving_mapping(rng: random.Random) -> dict[str, str]:
    mapping = {codon: codon for codon in ALL_CODONS}
    by_aa: dict[str, list[str]] = defaultdict(list)
    for codon in ALL_CODONS:
        aa = CODON_TO_AA[codon]
        if aa != "*":
            by_aa[aa].append(codon)
    for codons in by_aa.values():
        buckets: dict[tuple[int, int], list[str]] = defaultdict(list)
        family_size = len(codons)
        for codon in codons:
            buckets[(third_gc_value(codon), family_size)].append(codon)
        for bucket in buckets.values():
            shuffled = bucket[:]
            rng.shuffle(shuffled)
            for old, new in zip(bucket, shuffled):
                mapping[old] = new
    return mapping


class GeneRecord:
    __slots__ = ("species", "species_id", "gc3", "log_length", "counts", "logp_by_aa")

    def __init__(
        self,
        species: str,
        species_id: int,
        gc3: float,
        log_length: float,
        counts: dict[str, int],
        logp_by_aa: dict[str, dict[str, float]],
    ) -> None:
        self.species = species
        self.species_id = species_id
        self.gc3 = gc3
        self.log_length = log_length
        self.counts = counts
        self.logp_by_aa = logp_by_aa


def organism_from_path(path: Path) -> str:
    name = path.name
    prefix = "cds_codon_counts_"
    suffix = ".json"
    if name.startswith(prefix) and name.endswith(suffix):
        return name[len(prefix):-len(suffix)]
    return path.stem


def parse_gene_counts(raw_counts: object) -> dict[str, int] | None:
    if not isinstance(raw_counts, dict):
        return None
    counts = {codon: 0 for codon in ALL_CODONS}
    for raw_codon, raw_count in raw_counts.items():
        codon = normalize_codon(str(raw_codon))
        if codon not in counts:
            continue
        try:
            count = int(raw_count)
        except (TypeError, ValueError):
            return None
        if count < 0:
            return None
        counts[codon] += count
    return counts


def gene_logp_by_aa(counts: dict[str, int], families: dict[str, list[str]]) -> dict[str, dict[str, float]]:
    result: dict[str, dict[str, float]] = {}
    for aa, codons in families.items():
        total = sum(counts[codon] for codon in codons)
        denom = total + 0.5 * len(codons)
        result[aa] = {codon: math.log((counts[codon] + 0.5) / denom) for codon in codons}
    return result


def load_gene_records(families: dict[str, list[str]], rng: random.Random) -> tuple[list[GeneRecord], list[str], list[str]]:
    paths = sorted(Path(path) for path in glob.glob(str(DATA_DIR / "cds_codon_counts_*.json")))
    records: list[GeneRecord] = []
    species_names: list[str] = []
    checks: list[str] = [f"usage_files={len(paths)}"]
    if len(paths) < 25:
        return records, species_names, checks + ["usage_file_count_below_25"]
    for species_id, path in enumerate(paths):
        data = json.loads(path.read_text(encoding="utf-8"))
        species = str(data.get("organism") or organism_from_path(path))
        genes = data.get("genes", [])
        if not isinstance(genes, list):
            checks.append(f"skipped_{species}:genes_not_list")
            continue
        parsed: list[tuple[dict[str, int], int, float]] = []
        for gene in genes:
            if not isinstance(gene, dict):
                continue
            counts = parse_gene_counts(gene.get("codon_counts"))
            if counts is None:
                continue
            total = sum(counts[codon] for codon in ALL_CODONS if CODON_TO_AA[codon] != "*")
            if total <= 0:
                continue
            gc3 = sum(counts[codon] for codon in ALL_CODONS if CODON_TO_AA[codon] != "*" and codon[2] in THIRD_GC) / total
            parsed.append((counts, total, gc3))
        if not parsed:
            checks.append(f"skipped_{species}:no_valid_genes")
            continue
        if len(parsed) > GENES_PER_SPECIES:
            parsed = rng.sample(parsed, GENES_PER_SPECIES)
        current_id = len(species_names)
        species_names.append(species)
        for counts, total, gc3 in parsed:
            records.append(
                GeneRecord(
                    species=species,
                    species_id=current_id,
                    gc3=gc3,
                    log_length=math.log(total),
                    counts=counts,
                    logp_by_aa=gene_logp_by_aa(counts, families),
                )
            )
    checks.append(f"sampled_genes_per_species_max={GENES_PER_SPECIES}")
    checks.append(f"sampled_gene_records={len(records)}")
    return records, species_names, checks


def build_dataset(records: list[GeneRecord], edges: list[dict[str, object]], aa_to_id: dict[str, int]) -> dict[str, list]:
    y: list[float] = []
    t_col: list[float] = []
    th_col: list[float] = []
    gc3_col: list[float] = []
    dgc3_col: list[float] = []
    df3_col: list[float] = []
    logl_col: list[float] = []
    species_group: list[int] = []
    aa_group: list[int] = []
    edge_group: list[int] = []
    retained_by_edge: Counter[int] = Counter()
    for record in records:
        for edge in edges:
            c1 = str(edge["c1"])
            c2 = str(edge["c2"])
            aa = str(edge["aa"])
            if record.counts[c1] + record.counts[c2] < MIN_PAIR_COUNT:
                continue
            logp = record.logp_by_aa[aa]
            t_value = float(edge["T"])
            h_value = float(edge["H"])
            y.append(logp[c1] - logp[c2])
            t_col.append(t_value)
            th_col.append(t_value * h_value)
            gc3_col.append(record.gc3)
            dgc3_col.append(float(edge["delta_gc3"]))
            df3_col.append(float(edge["delta_f3"]))
            logl_col.append(record.log_length)
            species_group.append(record.species_id)
            aa_group.append(aa_to_id[aa])
            edge_id = int(edge["edge_id"])
            edge_group.append(edge_id)
            retained_by_edge[edge_id] += 1
    return {
        "y": y,
        "cols": {
            "T": t_col,
            "TH": th_col,
            "GC3": gc3_col,
            "delta_GC3": dgc3_col,
            "delta_f3": df3_col,
            "logL": logl_col,
        },
        "groups": {"species": species_group, "aa": aa_group, "edge": edge_group},
        "retained_by_edge": retained_by_edge,
    }


def subset_dataset(data: dict[str, list], keep_species: set[int]) -> dict[str, list]:
    indices = [i for i, species in enumerate(data["groups"]["species"]) if species in keep_species]
    return {
        "y": [data["y"][i] for i in indices],
        "cols": {name: [values[i] for i in indices] for name, values in data["cols"].items()},
        "groups": {name: [values[i] for i in indices] for name, values in data["groups"].items()},
    }


def residualize(
    y_values: list[float],
    columns: list[list[float]],
    group_arrays: list[list[int]],
    passes: int = RESIDUALIZE_PASSES,
) -> tuple[list[float], list[list[float]]]:
    y = y_values[:]
    cols = [column[:] for column in columns]
    if not y:
        return y, cols
    p = len(cols)
    group_sizes = [(max(groups) + 1 if groups else 0) for groups in group_arrays]
    for _ in range(passes):
        for group_index, groups in enumerate(group_arrays):
            size = group_sizes[group_index]
            sums_y = [0.0] * size
            sums_x = [[0.0] * p for _ in range(size)]
            counts = [0] * size
            for i, group in enumerate(groups):
                counts[group] += 1
                sums_y[group] += y[i]
                sx = sums_x[group]
                for j in range(p):
                    sx[j] += cols[j][i]
            for i, group in enumerate(groups):
                count = counts[group]
                if count == 0:
                    continue
                y[i] -= sums_y[group] / count
                sx = sums_x[group]
                for j in range(p):
                    cols[j][i] -= sx[j] / count
    return y, cols


def solve_linear(a: list[list[float]], b: list[float]) -> list[float] | None:
    n = len(b)
    matrix = [row[:] + [b[i]] for i, row in enumerate(a)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(matrix[row][col]))
        if abs(matrix[pivot][col]) < 1e-10:
            return None
        if pivot != col:
            matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
        scale = matrix[col][col]
        for j in range(col, n + 1):
            matrix[col][j] /= scale
        for row in range(n):
            if row == col:
                continue
            factor = matrix[row][col]
            if factor == 0.0:
                continue
            for j in range(col, n + 1):
                matrix[row][j] -= factor * matrix[col][j]
    return [matrix[i][n] for i in range(n)]


def fit_ols(data: dict[str, list], column_names: list[str], fixed_effects: tuple[str, ...]) -> dict[str, object] | None:
    if len(data["y"]) <= len(column_names) + 2:
        return None
    columns = [data["cols"][name] for name in column_names]
    groups = [data["groups"][name] for name in fixed_effects]
    y_res, x_res = residualize(data["y"], columns, groups)
    p = len(column_names)
    xtx = [[0.0 for _ in range(p)] for _ in range(p)]
    xty = [0.0 for _ in range(p)]
    sst = sum(value * value for value in y_res)
    for i, y_value in enumerate(y_res):
        row = [x_res[j][i] for j in range(p)]
        for j in range(p):
            xty[j] += row[j] * y_value
            for k in range(j, p):
                xtx[j][k] += row[j] * row[k]
    for j in range(p):
        for k in range(j):
            xtx[j][k] = xtx[k][j]
    beta = solve_linear(xtx, xty)
    if beta is None:
        return None
    sse = 0.0
    for i, y_value in enumerate(y_res):
        pred = sum(beta[j] * x_res[j][i] for j in range(p))
        resid = y_value - pred
        sse += resid * resid
    return {"beta": dict(zip(column_names, beta)), "sse": sse, "sst": sst, "n": len(y_res)}


def transformed_sse(data: dict[str, list], column_names: list[str], beta: dict[str, float], fixed_effects: tuple[str, ...]) -> tuple[float, float, int]:
    columns = [data["cols"][name] for name in column_names]
    groups = [data["groups"][name] for name in fixed_effects]
    y_res, x_res = residualize(data["y"], columns, groups)
    sse = 0.0
    sst = sum(value * value for value in y_res)
    for i, y_value in enumerate(y_res):
        pred = sum(beta[column_names[j]] * x_res[j][i] for j in range(len(column_names)))
        resid = y_value - pred
        sse += resid * resid
    return sse, sst, len(y_res)


def fit_models(data: dict[str, list], fixed_effects: tuple[str, ...] = ("species", "aa")) -> dict[str, object] | None:
    baseline_cols = ["T", "GC3", "delta_GC3", "delta_f3", "logL"]
    full_cols = ["T", "TH", "GC3", "delta_GC3", "delta_f3", "logL"]
    baseline = fit_ols(data, baseline_cols, fixed_effects)
    full = fit_ols(data, full_cols, fixed_effects)
    if baseline is None or full is None:
        return None
    n = int(full["n"])
    sse_base = max(float(baseline["sse"]), 1e-300)
    sse_full = max(float(full["sse"]), 1e-300)
    d_ll = 0.5 * n * math.log(sse_base / sse_full)
    return {"baseline": baseline, "full": full, "dLL": d_ll}


def cv_lift(data: dict[str, list], species_count: int, rng: random.Random) -> tuple[list[float], list[str]]:
    species = list(range(species_count))
    lifts: list[float] = []
    checks: list[str] = []
    baseline_cols = ["T", "GC3", "delta_GC3", "delta_f3", "logL"]
    full_cols = ["T", "TH", "GC3", "delta_GC3", "delta_f3", "logL"]
    for split in range(CV_SPLITS):
        shuffled = species[:]
        rng.shuffle(shuffled)
        holdout_count = max(1, round(0.2 * len(shuffled)))
        test_species = set(shuffled[:holdout_count])
        train_species = set(shuffled[holdout_count:])
        train = subset_dataset(data, train_species)
        test = subset_dataset(data, test_species)
        baseline = fit_ols(train, baseline_cols, ("species", "aa"))
        full = fit_ols(train, full_cols, ("species", "aa"))
        if baseline is None or full is None or not test["y"]:
            checks.append(f"cv_split_{split}:fit_or_test_empty")
            continue
        sse_base, _sst_base, n_test = transformed_sse(test, baseline_cols, baseline["beta"], ("species", "aa"))
        sse_full, _sst_full, _n = transformed_sse(test, full_cols, full["beta"], ("species", "aa"))
        lifts.append(0.5 * n_test * math.log(max(sse_base, 1e-300) / max(sse_full, 1e-300)))
    return lifts, checks


def permute_h_by_stratum(edges: list[dict[str, object]], rng: random.Random) -> dict[int, float]:
    strata: dict[tuple[str, str, int, int], list[int]] = defaultdict(list)
    for edge in edges:
        df3_bin = int(abs(float(edge["delta_f3"])) * 4.0)
        key = (str(edge["aa"]), str(edge["edge_class"]), int(abs(float(edge["delta_gc3"]))), df3_bin)
        strata[key].append(int(edge["edge_id"]))
    h_by_edge = {int(edge["edge_id"]): float(edge["H"]) for edge in edges}
    result = h_by_edge.copy()
    for edge_ids in strata.values():
        values = [h_by_edge[edge_id] for edge_id in edge_ids]
        rng.shuffle(values)
        for edge_id, value in zip(edge_ids, values):
            result[edge_id] = value
    return result


def dataset_with_permuted_h(data: dict[str, list], permuted_h: dict[int, float]) -> dict[str, list]:
    edge_group = data["groups"]["edge"]
    t_col = data["cols"]["T"]
    return {
        "y": data["y"],
        "cols": {
            "T": t_col,
            "TH": [t_col[i] * permuted_h[edge_group[i]] for i in range(len(t_col))],
            "GC3": data["cols"]["GC3"],
            "delta_GC3": data["cols"]["delta_GC3"],
            "delta_f3": data["cols"]["delta_f3"],
            "logL": data["cols"]["logL"],
        },
        "groups": data["groups"],
    }


def empirical_upper_p(observed: float, null_values: list[float]) -> float:
    if observed <= 0.0:
        return 1.0
    return (sum(1 for value in null_values if value >= observed - 1e-12) + 1) / (len(null_values) + 1)


def column_norm_after_edge_absorption(data: dict[str, list], column_name: str) -> float:
    _y, cols = residualize([0.0] * len(data["y"]), [data["cols"][column_name]], [data["groups"]["edge"]], passes=2)
    return math.sqrt(sum(value * value for value in cols[0]))


def main() -> None:
    rng = random.Random(RANDOM_SEED)
    checks: list[str] = []
    try:
        vectors = load_selection_vectors()
    except Exception as exc:
        emit("needs_derivation", beta_bridge=None, beta_T=None, checks=[f"selection_vectors_error:{exc}"], note="selection vector load failed")

    families: dict[str, list[str]] = defaultdict(list)
    for codon in ALL_CODONS:
        aa = CODON_TO_AA[codon]
        if aa != "*":
            families[aa].append(codon)
    families = {aa: codons for aa, codons in sorted(families.items()) if len(codons) > 1}
    aa_to_id = {aa: index for index, aa in enumerate(sorted(families))}

    base_edges = neutral_edges(ALL_CODONS)
    edges = decorate_edges(base_edges, vectors)
    degree_hist = Counter()
    for codon in ALL_CODONS:
        degree_hist[sum(1 for other in ALL_CODONS if other != codon and CODON_TO_AA[other] == CODON_TO_AA[codon] and hamming1(codon, other))] += 1
    merged_degree_profile = [degree_hist[3], degree_hist[1], degree_hist[2], degree_hist[0] + degree_hist[4]]
    checks.append(f"standard_code_neutral_adjacency_codons_28_22_8_6={merged_degree_profile}")
    checks.append(f"sense_neutral_edges_with_tai_proxy={len(edges)}")
    checks.append(f"edge_class_counts={dict(sorted(Counter(str(edge['edge_class']) for edge in edges).items()))}")

    records, species_names, data_checks = load_gene_records(families, rng)
    checks.extend(data_checks)
    if len(species_names) < 25 or not records:
        emit(
            "needs_derivation",
            beta_bridge=None,
            beta_T=None,
            cv_median_dLL=None,
            cv_frac_positive=None,
            null1_p=None,
            null2_p=None,
            null3="reduced (global tRNA proxy)",
            n_species=len(species_names),
            n_edges=len(edges),
            checks=checks,
            note="insufficient real codon-count data for the pre-registered threshold",
        )

    data = build_dataset(records, edges, aa_to_id)
    checks.append(f"gene_edge_observations={len(data['y'])}")
    checks.append(f"edges_with_retained_observations={len(data['retained_by_edge'])}")
    if len(data["y"]) < 1000 or len(data["retained_by_edge"]) < 40:
        emit(
            "needs_derivation",
            beta_bridge=None,
            beta_T=None,
            cv_median_dLL=None,
            cv_frac_positive=None,
            null1_p=None,
            null2_p=None,
            null3="reduced (global tRNA proxy)",
            n_species=len(species_names),
            n_edges=len(edges),
            checks=checks,
            note="too few gene-edge observations after the pair-count threshold",
        )

    t_edge_norm = column_norm_after_edge_absorption(data, "T")
    th_edge_norm = column_norm_after_edge_absorption(data, "TH")
    checks.append(f"strict_edge_fe_T_norm={t_edge_norm:.6g}")
    checks.append(f"strict_edge_fe_TH_norm={th_edge_norm:.6g}")
    checks.append("strict_edge_fe_identifiability=not_identified_for_global_T_proxy")

    fitted = fit_models(data)
    if fitted is None:
        emit(
            "needs_derivation",
            beta_bridge=None,
            beta_T=None,
            cv_median_dLL=None,
            cv_frac_positive=None,
            null1_p=None,
            null2_p=None,
            null3="reduced (global tRNA proxy)",
            n_species=len(species_names),
            n_edges=len(edges),
            checks=checks,
            note="OLS normal equations were singular in the reduced estimable model",
        )
    full_beta = fitted["full"]["beta"]
    beta_bridge = float(full_beta["TH"])
    beta_t = float(full_beta["T"])
    checks.append(f"reduced_model_train_dLL={float(fitted['dLL']):.6g}")

    cv_values, cv_checks = cv_lift(data, len(species_names), rng)
    checks.extend(cv_checks)
    if not cv_values:
        emit(
            "needs_derivation",
            beta_bridge=round_float(beta_bridge),
            beta_T=round_float(beta_t),
            cv_median_dLL=None,
            cv_frac_positive=None,
            null1_p=None,
            null2_p=None,
            null3="reduced (global tRNA proxy)",
            n_species=len(species_names),
            n_edges=len(edges),
            checks=checks,
            note="species-heldout CV produced no usable folds",
        )
    sorted_cv = sorted(cv_values)
    cv_median = sorted_cv[len(sorted_cv) // 2] if len(sorted_cv) % 2 else 0.5 * (sorted_cv[len(sorted_cv) // 2 - 1] + sorted_cv[len(sorted_cv) // 2])
    cv_frac_positive = sum(1 for value in cv_values if value > 0.0) / len(cv_values)
    checks.append(f"cv_splits_used={len(cv_values)}")

    null1_values: list[float] = []
    null1_failures = 0
    for _draw in range(NULL_DRAWS):
        mapping = gc3_preserving_mapping(rng)
        perm_edges = decorate_edges(base_edges, vectors, mapping)
        perm_data = build_dataset(records, perm_edges, aa_to_id)
        fit = fit_models(perm_data)
        if fit is None:
            null1_failures += 1
            continue
        null1_values.append(float(fit["full"]["beta"]["TH"]))
    checks.append(f"null1_draws_used={len(null1_values)}")
    if null1_failures:
        checks.append(f"null1_fit_failures={null1_failures}")

    null2_values: list[float] = []
    null2_failures = 0
    for _draw in range(NULL_DRAWS):
        permuted_h = permute_h_by_stratum(edges, rng)
        perm_data = dataset_with_permuted_h(data, permuted_h)
        fit = fit_models(perm_data)
        if fit is None:
            null2_failures += 1
            continue
        null2_values.append(float(fit["full"]["beta"]["TH"]))
    checks.append(f"null2_draws_used={len(null2_values)}")
    if null2_failures:
        checks.append(f"null2_fit_failures={null2_failures}")

    if len(null1_values) < 50 or len(null2_values) < 50:
        emit(
            "needs_derivation",
            beta_bridge=round_float(beta_bridge),
            beta_T=round_float(beta_t),
            cv_median_dLL=round_float(cv_median),
            cv_frac_positive=round_float(cv_frac_positive),
            null1_p=None,
            null2_p=None,
            null3="reduced (global tRNA proxy)",
            n_species=len(species_names),
            n_edges=len(edges),
            checks=checks,
            note="permutation nulls did not yield enough fitted draws",
        )

    null1_p = empirical_upper_p(beta_bridge, null1_values)
    null2_p = empirical_upper_p(beta_bridge, null2_values)
    cv_pass = cv_median > 0.0 and cv_frac_positive >= 0.70
    null1_pass = null1_p < 0.01
    null2_pass = null2_p < 0.01

    if beta_bridge > 0.0 and cv_pass and null1_pass and null2_pass:
        status = "certified"
        note = "Reduced global-tRNA-proxy result passes species-heldout CV and both required nulls; strict edge-FE identification awaits species-specific tRNA."
    elif beta_bridge <= 0.0:
        status = "refuted"
        note = "Reduced global-tRNA-proxy interaction is non-positive; strict edge-FE model is not identified with edge-only T."
    else:
        status = "coincidence"
        note = "Reduced global-tRNA-proxy interaction does not pass the pre-registered CV/null gates; strict edge-FE model is not identified with edge-only T."

    emit(
        status,
        beta_bridge=round_float(beta_bridge),
        beta_T=round_float(beta_t),
        cv_median_dLL=round_float(cv_median),
        cv_frac_positive=round_float(cv_frac_positive),
        null1_p=round_float(null1_p),
        null2_p=round_float(null2_p),
        null3="reduced (global tRNA proxy)",
        n_species=len(species_names),
        n_edges=len(edges),
        n_gene_edge_observations=len(data["y"]),
        null_draws=NULL_DRAWS,
        checks=checks,
        note=note,
    )


if __name__ == "__main__":
    main()

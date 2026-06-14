#!/usr/bin/env python3
"""Window6 four-cell partition versus real codon selection vectors.

The test fixes the Window6 partition from the finite Foldbin/Zeckendorf
construction, then asks how much four-dimensional codon selection variance is
explained by the four cells against two nonparametric null models.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import product
import json
import math
import random
import sys
from pathlib import Path
from typing import Iterable


EXPERIMENT_ID = "bcd_fourcell_selection_enrichment"
CLAIM_ID = "bridge.window6_codon_q6.fourcell_selection_enrichment"
DATA_PATH = Path("papers/window_codon_bridge/data/codon_q6_selection_vectors.json")
RANDOM_SEED = 406270
NULL_DRAWS = 10000

BASES = ("U", "C", "A", "G")
BASE_TO_BITS = {"U": (0, 0), "C": (0, 1), "A": (1, 0), "G": (1, 1)}
VISIBLE_WEIGHTS = (1, 2, 3, 5, 8, 13)
TAIL_WEIGHTS = (21, 34, 55)
CELL_ORDER = ("U_2", "U_1", "U_L", "U_R")
CELL_SIZES = (27, 22, 9, 6)
EDGE_MATRIX = [
    [28, 63, 23, 20],
    [63, 21, 21, 6],
    [23, 21, 2, 6],
    [20, 6, 6, 2],
]
FIELDS = (
    "trna_supply_tai_mean",
    "f3_loading",
    "d_perp_loading",
    "optimal_loading",
)


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def codon_to_q6(codon: str) -> tuple[int, ...]:
    bits: list[int] = []
    for base in codon.upper().replace("T", "U"):
        if base not in BASE_TO_BITS:
            raise ValueError(f"invalid RNA base in codon {codon!r}")
        bits.extend(BASE_TO_BITS[base])
    if len(bits) != 6:
        raise ValueError(f"codon must encode six Q6 bits: {codon!r}")
    return tuple(bits)


def int_to_label(value: int) -> str:
    return format(value, "06b")


def label_to_int(label: str) -> int:
    return int(label, 2)


def no_adjacent_ones(bits: tuple[int, ...]) -> bool:
    return all(not (bits[index] and bits[index + 1]) for index in range(len(bits) - 1))


def visible_value(word: tuple[int, ...]) -> int:
    return sum(bit * weight for bit, weight in zip(word, VISIBLE_WEIGHTS))


def reconstruct_window6_cells() -> dict[str, set[str]]:
    cells = {cell: set() for cell in CELL_ORDER}
    for word in product((0, 1), repeat=6):
        if not no_adjacent_ones(word):
            continue
        boundary = word[0] == 1 and word[5] == 1
        weight = sum(word)
        if boundary:
            cell = "U_R"
        elif weight == 2:
            cell = "U_2"
        elif weight == 1:
            cell = "U_1"
        elif weight in (0, 3):
            cell = "U_L"
        else:
            raise AssertionError(f"unclassified visible word: {word!r}")
        for tail in product((0, 1), repeat=3):
            c7, c8, c9 = tail
            if c7 and c8:
                continue
            if c8 and c9:
                continue
            if word[5] and c7:
                continue
            value = visible_value(word) + sum(bit * weight for bit, weight in zip(tail, TAIL_WEIGHTS))
            if value <= 63:
                cells[cell].add(int_to_label(value))
    return cells


def cell_by_label(cells: dict[str, set[str]]) -> dict[str, str]:
    mapping = {label: cell for cell, labels in cells.items() for label in labels}
    if len(mapping) != 64:
        raise RuntimeError("Window6 cell reconstruction did not cover Q6")
    return mapping


def edge_matrix(cells: dict[str, set[str]]) -> list[list[int]]:
    owner = {label_to_int(label): cell for cell, labels in cells.items() for label in labels}
    matrix = [[0 for _ in CELL_ORDER] for _ in CELL_ORDER]
    for value in range(64):
        for axis in range(6):
            neighbor = value ^ (1 << axis)
            if value < neighbor:
                left = CELL_ORDER.index(owner[value])
                right = CELL_ORDER.index(owner[neighbor])
                matrix[left][right] += 1
                if left != right:
                    matrix[right][left] += 1
    return matrix


def load_vectors() -> list[dict[str, object]]:
    data = json.loads(DATA_PATH.read_text())
    if data.get("schema") != "codon_q6_selection_vectors.v1":
        raise ValueError(f"unexpected data schema: {data.get('schema')!r}")
    rows = []
    for row in data["vectors"]:
        codon = str(row["codon"])
        bits = tuple(int(bit) for bit in row["q6_bits"])
        label = "".join(str(bit) for bit in bits)
        if bits != codon_to_q6(codon):
            raise ValueError(f"codon/q6 mismatch for {codon}")
        if label != row["q6_label"]:
            raise ValueError(f"q6 label mismatch for {codon}")
        rows.append(dict(row))
    if len(rows) != 64:
        raise ValueError(f"expected 64 codon rows, got {len(rows)}")
    if len({str(row["q6_label"]) for row in rows}) != 64:
        raise ValueError("q6 labels are not a 64-point bijection")
    return rows


def mean(values: Iterable[float]) -> float:
    values = list(values)
    return sum(values) / len(values)


def population_sd(values: list[float]) -> float:
    m = mean(values)
    return math.sqrt(sum((value - m) ** 2 for value in values) / len(values))


def zscore_columns(rows: list[dict[str, object]], fields: tuple[str, ...], impute_missing: bool) -> list[list[float]]:
    columns: list[list[float]] = []
    for field in fields:
        observed = [float(row[field]) for row in rows if row.get(field) is not None]
        if not observed:
            raise ValueError(f"field {field} has no observed values")
        fill = mean(observed)
        raw = [fill if row.get(field) is None and impute_missing else row.get(field) for row in rows]
        if any(value is None for value in raw):
            missing = [str(row["codon"]) for row, value in zip(rows, raw) if value is None]
            raise ValueError(f"field {field} missing for {missing}")
        values = [float(value) for value in raw]
        center = mean(values)
        scale = population_sd(values)
        if scale <= 0.0:
            raise ValueError(f"field {field} has zero variance")
        columns.append([(value - center) / scale for value in values])
    return [[columns[col][row] for col in range(len(fields))] for row in range(len(rows))]


def trace_r2(y: list[list[float]], labels: list[str]) -> float:
    n = len(y)
    p = len(y[0]) if y else 0
    overall = [sum(row[col] for row in y) / n for col in range(p)]
    total = sum((row[col] - overall[col]) ** 2 for row in y for col in range(p))
    if total <= 0.0:
        return 0.0
    groups: dict[str, list[int]] = defaultdict(list)
    for index, label in enumerate(labels):
        groups[label].append(index)
    between = 0.0
    for indices in groups.values():
        centroid = [sum(y[index][col] for index in indices) / len(indices) for col in range(p)]
        between += len(indices) * sum((centroid[col] - overall[col]) ** 2 for col in range(p))
    return between / total


def per_axis_eta2(y: list[list[float]], labels: list[str]) -> dict[str, float]:
    out = {}
    for col, field in enumerate(FIELDS):
        column = [[row[col]] for row in y]
        out[field] = trace_r2(column, labels)
    return out


def centroids(y: list[list[float]], labels: list[str]) -> dict[str, dict[str, float]]:
    out: dict[str, dict[str, float]] = {}
    for cell in CELL_ORDER:
        indices = [index for index, label in enumerate(labels) if label == cell]
        out[cell] = {
            field: sum(y[index][col] for index in indices) / len(indices)
            for col, field in enumerate(FIELDS)
        }
    return out


def rounded(value: object, digits: int = 12) -> object:
    if isinstance(value, float):
        return round(value, digits)
    if isinstance(value, dict):
        return {key: rounded(item, digits) for key, item in value.items()}
    if isinstance(value, list):
        return [rounded(item, digits) for item in value]
    return value


def random_labels_by_sizes(sizes: tuple[int, ...], rng: random.Random) -> list[str]:
    labels = []
    for cell, size in zip(CELL_ORDER, sizes):
        labels.extend([cell] * size)
    rng.shuffle(labels)
    return labels


def empirical_ge_p(observed: float, values: list[float]) -> float:
    return (sum(1 for value in values if value >= observed - 1e-15) + 1) / (len(values) + 1)


def null_summary(observed: float, values: list[float]) -> dict[str, object]:
    values_sorted = sorted(values)
    n = len(values_sorted)
    avg = sum(values_sorted) / n
    var = sum((value - avg) ** 2 for value in values_sorted) / (n - 1) if n > 1 else 0.0
    return {
        "draws": n,
        "p_ge_observed": empirical_ge_p(observed, values_sorted),
        "mean": avg,
        "sd": math.sqrt(var),
        "min": values_sorted[0],
        "q05": values_sorted[int(0.05 * (n - 1))],
        "median": values_sorted[int(0.50 * (n - 1))],
        "q95": values_sorted[int(0.95 * (n - 1))],
        "max": values_sorted[-1],
    }


def size_preserving_null(y: list[list[float]], sizes: tuple[int, ...], rng: random.Random) -> list[float]:
    return [trace_r2(y, random_labels_by_sizes(sizes, rng)) for _ in range(NULL_DRAWS)]


def codon_gc_total(codon: str) -> int:
    return sum(1 for base in codon if base in ("G", "C"))


def conservative_key(row: dict[str, object]) -> tuple[object, ...]:
    codon = str(row["codon"])
    return (
        row["amino_acid"],
        codon[2] in ("G", "C"),
        codon_gc_total(codon),
    )


def stratified_label_permutation(
    rows: list[dict[str, object]],
    labels: list[str],
    rng: random.Random,
) -> list[str]:
    strata: dict[tuple[object, ...], list[int]] = defaultdict(list)
    for index, row in enumerate(rows):
        strata[conservative_key(row)].append(index)
    sampled = labels[:]
    for indices in strata.values():
        values = [sampled[index] for index in indices]
        rng.shuffle(values)
        for index, value in zip(indices, values):
            sampled[index] = value
    return sampled


def gc_conservative_null(
    rows: list[dict[str, object]],
    y: list[list[float]],
    labels: list[str],
    rng: random.Random,
) -> tuple[list[float], dict[str, object]]:
    strata = defaultdict(list)
    for index, row in enumerate(rows):
        strata[conservative_key(row)].append(index)
    sizes = sorted((len(indices) for indices in strata.values()), reverse=True)
    values = [trace_r2(y, stratified_label_permutation(rows, labels, rng)) for _ in range(NULL_DRAWS)]
    metadata = {
        "model": "permute Window6 cell labels within amino_acid x GC3 x total_GC strata",
        "base_composition_control": "total_GC is the strongest nondegenerate base-composition control combined with synonymous family and GC3; full U/C/A/G count strata freeze all codons in this 64-row table",
        "strata": len(sizes),
        "singleton_strata": sum(1 for size in sizes if size == 1),
        "movable_codons": sum(size for size in sizes if size > 1),
        "largest_strata": sizes[:10],
    }
    return values, metadata


def cell_counts(labels: list[str]) -> dict[str, int]:
    counts = Counter(labels)
    return {cell: counts[cell] for cell in CELL_ORDER}


def report_for_rows(
    rows: list[dict[str, object]],
    labels: list[str],
    rng: random.Random,
    impute_missing: bool,
    sizes_for_free_null: tuple[int, ...],
) -> dict[str, object]:
    y = zscore_columns(rows, FIELDS, impute_missing)
    observed = trace_r2(y, labels)
    free_values = size_preserving_null(y, sizes_for_free_null, rng)
    conservative_values, conservative_meta = gc_conservative_null(rows, y, labels, rng)
    free = null_summary(observed, free_values)
    conservative = null_summary(observed, conservative_values)
    conservative.update(conservative_meta)
    return {
        "n": len(rows),
        "R2_cell": observed,
        "per_axis_eta2": per_axis_eta2(y, labels),
        "p_size_preserving": free["p_ge_observed"],
        "p_gc_conservative": conservative["p_ge_observed"],
        "cell_counts": cell_counts(labels),
        "cell_centroids": centroids(y, labels),
        "nulls": {
            "size_preserving": free,
            "gc_conservative": conservative,
        },
    }


def status_from_pvalues(p_size: float, p_gc: float) -> tuple[str, str]:
    if p_size <= 0.05 and p_gc <= 0.05:
        return (
            "certified",
            "The Window6 four-cell partition explains 4D selection variance beyond the strict same-size null and the synonymous-family/GC conservative null.",
        )
    if p_size <= 0.05:
        return (
            "coincidence",
            "The four-cell partition beats the same-size null, but the signal does not survive the synonymous-family/GC conservative null.",
        )
    return (
        "refuted",
        "The four-cell partition does not explain more 4D selection variance than strict same-size random partitions.",
    )


def main() -> None:
    rng = random.Random(RANDOM_SEED)
    cells = reconstruct_window6_cells()
    owner = cell_by_label(cells)
    rows = load_vectors()
    labels = [owner[str(row["q6_label"])] for row in rows]
    sense_rows = [row for row in rows if bool(row["is_sense"])]
    sense_labels = [owner[str(row["q6_label"])] for row in sense_rows]

    observed_sizes = tuple(len(cells[cell]) for cell in CELL_ORDER)
    observed_edge_matrix = edge_matrix(cells)
    stop_missing = {
        field: [str(row["codon"]) for row in rows if row.get(field) is None]
        for field in FIELDS
    }
    checks = [
        check_row("window6_cell_sizes", list(observed_sizes), list(CELL_SIZES)),
        check_row("window6_edge_matrix", observed_edge_matrix, EDGE_MATRIX),
        check_row("codon_vector_count", len(rows), 64),
        check_row("codon_q6_encoding_count", len({tuple(codon_to_q6(str(row["codon"]))) for row in rows}), 64),
        check_row("sense_vector_count", len(sense_rows), 61),
        check_row("selection_missing_codons", stop_missing, {field: ["UAA", "UAG", "UGA"] for field in FIELDS}),
    ]
    if not all(row["ok"] for row in checks):
        emit(
            "needs_derivation",
            R2_cell=None,
            per_axis_eta2={},
            p_size_preserving=None,
            p_gc_conservative=None,
            cell_centroids={},
            checks=checks,
            note="Self-checks failed before running the selection-enrichment verdict.",
        )

    all_report = report_for_rows(rows, labels, rng, True, CELL_SIZES)
    sense_sizes = tuple(cell_counts(sense_labels)[cell] for cell in CELL_ORDER)
    sense_report = report_for_rows(sense_rows, sense_labels, rng, False, sense_sizes)
    status, note = status_from_pvalues(
        float(all_report["p_size_preserving"]),
        float(all_report["p_gc_conservative"]),
    )

    emit(
        status,
        R2_cell=rounded(all_report["R2_cell"]),
        per_axis_eta2=rounded(all_report["per_axis_eta2"]),
        p_size_preserving=rounded(all_report["p_size_preserving"]),
        p_gc_conservative=rounded(all_report["p_gc_conservative"]),
        cell_centroids=rounded(all_report["cell_centroids"]),
        sense_only=rounded({
            "R2_cell": sense_report["R2_cell"],
            "per_axis_eta2": sense_report["per_axis_eta2"],
            "p_size_preserving": sense_report["p_size_preserving"],
            "p_gc_conservative": sense_report["p_gc_conservative"],
            "cell_counts": sense_report["cell_counts"],
            "cell_centroids": sense_report["cell_centroids"],
            "nulls": sense_report["nulls"],
        }),
        cell_counts=all_report["cell_counts"],
        nulls=rounded(all_report["nulls"]),
        checks=checks,
        note=note,
    )


if __name__ == "__main__":
    main()

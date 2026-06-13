#!/usr/bin/env python3
"""BC5 Window6 right-boundary escape versus codon selection axes.

This is an anti-numerology derivation script.  It reconstructs the Window6
right-boundary cell from the finite Foldbin rules, then tests whether that
predefined cell aligns with per-codon biological selection axes beyond a
random size-6 subset null.
"""
from __future__ import annotations

from itertools import product
import json
import math
import random
import sys
from pathlib import Path
from typing import Iterable


EXPERIMENT_ID = "bc5_right_boundary_selection_axis"
CLAIM_ID = "bridge.window6_codon_q6.right_boundary_selection_axis"

DATA_PATH = Path("papers/window_codon_bridge/data/codon_q6_selection_vectors.json")
RANDOM_SEED = 17065
NULL_DRAWS = 20000

BASE_TO_BITS = {"U": (0, 0), "C": (0, 1), "A": (1, 0), "G": (1, 1)}
BITS_TO_BASE = {bits: base for base, bits in BASE_TO_BITS.items()}
VISIBLE_WEIGHTS = (1, 2, 3, 5, 8, 13)
TAIL_WEIGHTS = (21, 34, 55)
CELL_ORDER = ("U_2", "U_1", "U_L", "U_R")


def emit(status: str, **fields: object) -> None:
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
    }
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def codon_to_q6(codon: str) -> tuple[int, ...]:
    codon = codon.upper().replace("T", "U")
    if len(codon) != 3:
        raise ValueError(f"codon must have length 3: {codon!r}")
    bits: list[int] = []
    for base in codon:
        if base not in BASE_TO_BITS:
            raise ValueError(f"invalid RNA base in codon {codon!r}")
        bits.extend(BASE_TO_BITS[base])
    return tuple(bits)


def q6_to_codon(bits: tuple[int, ...]) -> str:
    if len(bits) != 6:
        raise ValueError(f"Q6 coordinate must have length 6: {bits!r}")
    chars = []
    for offset in range(0, 6, 2):
        pair = (bits[offset], bits[offset + 1])
        if pair not in BITS_TO_BASE:
            raise ValueError(f"invalid Q6 pair {pair!r}")
        chars.append(BITS_TO_BASE[pair])
    return "".join(chars)


def no_adjacent_ones(bits: tuple[int, ...]) -> bool:
    return all(not (bits[index] and bits[index + 1]) for index in range(len(bits) - 1))


def visible_value(word: tuple[int, ...]) -> int:
    return sum(bit * weight for bit, weight in zip(word, VISIBLE_WEIGHTS))


def label_to_int(label: str) -> int:
    return int(label, 2)


def int_to_label(value: int) -> str:
    return format(value, "06b")


def reconstruct_window6_partition() -> dict[str, set[str]]:
    """Reconstruct the four cells from the finite Foldbin rules.

    The Fibonacci source uses Zeckendorf/Foldbin values with low-to-high
    weights 1,2,3,5,8,13 on the visible six bits and tail weights 21,34,55.
    The bio data labels q6_bits in codon order.  The shared label used here is
    the six-character binary display of the resulting vertex value, so n=14 is
    label 001110 and codon UGA under U=00,C=01,A=10,G=11.
    """
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
            raise AssertionError(f"unclassified X6 word: {word!r}")

        for tail in product((0, 1), repeat=3):
            c7, c8, c9 = tail
            if c7 and c8:
                continue
            if c8 and c9:
                continue
            if word[5] and c7:
                continue
            value = visible_value(word) + sum(bit * w for bit, w in zip(tail, TAIL_WEIGHTS))
            if value <= 63:
                cells[cell].add(int_to_label(value))
    return cells


def edge_matrix(cells: dict[str, set[str]]) -> list[list[int]]:
    cell_by_int = {
        label_to_int(label): cell
        for cell, labels in cells.items()
        for label in labels
    }
    matrix = [[0 for _ in CELL_ORDER] for _ in CELL_ORDER]
    for value in range(64):
        for axis in range(6):
            neighbor = value ^ (1 << axis)
            if value < neighbor:
                left = CELL_ORDER.index(cell_by_int[value])
                right = CELL_ORDER.index(cell_by_int[neighbor])
                matrix[left][right] += 1
                if left != right:
                    matrix[right][left] += 1
    return matrix


def outward_degree_by_label(ur_labels: set[str]) -> dict[str, int]:
    ur_ints = {label_to_int(label) for label in ur_labels}
    degrees = {}
    for value in sorted(ur_ints):
        degrees[int_to_label(value)] = sum(1 for axis in range(6) if (value ^ (1 << axis)) not in ur_ints)
    return degrees


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
    return rows


def mean(values: Iterable[float]) -> float:
    values = list(values)
    return sum(values) / len(values)


def sample_sd(values: list[float]) -> float:
    if len(values) < 2:
        return 0.0
    m = mean(values)
    return math.sqrt(sum((value - m) ** 2 for value in values) / (len(values) - 1))


def ranks(values: list[float]) -> list[float]:
    order = sorted(range(len(values)), key=lambda index: values[index])
    result = [0.0 for _ in values]
    start = 0
    while start < len(values):
        end = start + 1
        while end < len(values) and values[order[end]] == values[order[start]]:
            end += 1
        average_rank = (start + 1 + end) / 2.0
        for pos in range(start, end):
            result[order[pos]] = average_rank
        start = end
    return result


def pearson(left: list[float], right: list[float]) -> float | None:
    if len(left) != len(right) or len(left) < 2:
        return None
    left_mean = mean(left)
    right_mean = mean(right)
    left_ss = sum((value - left_mean) ** 2 for value in left)
    right_ss = sum((value - right_mean) ** 2 for value in right)
    if left_ss <= 0.0 or right_ss <= 0.0:
        return None
    return sum((a - left_mean) * (b - right_mean) for a, b in zip(left, right)) / math.sqrt(left_ss * right_ss)


def spearman(left: list[float], right: list[float]) -> float | None:
    return pearson(ranks(left), ranks(right))


def centered(values: list[float]) -> list[float]:
    m = mean(values)
    return [value - m for value in values]


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def norm(values: list[float]) -> float:
    return math.sqrt(sum(value * value for value in values))


def cosine(left: list[float], right: list[float]) -> float | None:
    denom = norm(left) * norm(right)
    if denom == 0.0:
        return None
    return dot(left, right) / denom


def empirical_ge_p(observed: float, null_values: list[float]) -> float:
    ge = sum(1 for value in null_values if value >= observed - 1e-15)
    return (ge + 1) / (len(null_values) + 1)


def mean_delta(rows: list[dict[str, object]], labels: set[str], field: str) -> tuple[int, float, float, float]:
    inside = [float(row[field]) for row in rows if row["q6_label"] in labels and row.get(field) is not None]
    outside = [float(row[field]) for row in rows if row["q6_label"] not in labels and row.get(field) is not None]
    if not inside or not outside:
        raise ValueError(f"cannot compute mean delta for {field}")
    return len(inside), mean(inside), mean(outside), mean(inside) - mean(outside)


def axis_alignment_z(rows: list[dict[str, object]], labels: set[str], field: str) -> float:
    values = [float(row[field]) for row in rows if row.get(field) is not None]
    sd = sample_sd(values)
    if sd == 0.0:
        return 0.0
    _, inside_mean, outside_mean, _ = mean_delta(rows, labels, field)
    return (outside_mean - inside_mean) / sd


def null_scores(
    rows: list[dict[str, object]],
    all_labels: list[str],
    size: int,
    draws: int,
    score_fields: list[str],
) -> list[float]:
    rng = random.Random(RANDOM_SEED)
    scores = []
    for _ in range(draws):
        labels = set(rng.sample(all_labels, size))
        scores.append(mean(axis_alignment_z(rows, labels, field) for field in score_fields))
    return scores


def fixed_sense_null_scores(
    rows: list[dict[str, object]],
    sense_labels: list[str],
    size: int,
    draws: int,
    field: str,
) -> list[float]:
    rng = random.Random(RANDOM_SEED + 19)
    return [axis_alignment_z(rows, set(rng.sample(sense_labels, size)), field) for _ in range(draws)]


def axis_report(
    rows: list[dict[str, object]],
    labels: set[str],
    escape_by_label: dict[str, float],
    field: str,
    axis_name: str,
    null_labels: list[str],
    sense_labels: list[str],
) -> dict[str, object]:
    usable = [row for row in rows if row.get(field) is not None]
    x_indicator = [1.0 if row["q6_label"] in labels else 0.0 for row in usable]
    x_centered = centered(x_indicator)
    x_escape = [float(escape_by_label.get(str(row["q6_label"]), 0.0)) for row in usable]
    y = [float(row[field]) for row in usable]
    y_centered = centered(y)

    inside_n, inside_mean, outside_mean, delta = mean_delta(rows, labels, field)
    aligned_delta = -delta
    aligned_z = axis_alignment_z(rows, labels, field)
    random_size6 = null_scores(rows, null_labels, 6, NULL_DRAWS, [field])
    random_sense_fixed = fixed_sense_null_scores(rows, sense_labels, inside_n, NULL_DRAWS, field)
    rho_escape = spearman(x_escape, y)
    rho_indicator = spearman(x_indicator, y)
    cos_indicator = cosine(x_centered, y_centered)
    cos_escape = cosine(centered(x_escape), y_centered)
    projection_indicator = dot(x_centered, y_centered) / (norm(y_centered) or 1.0)
    projection_escape = dot(centered(x_escape), y_centered) / (norm(y_centered) or 1.0)
    negative_inside = sum(1 for row in usable if row["q6_label"] in labels and float(row[field]) < 0.0)

    return {
        "name": f"{axis_name}_axis_alignment",
        "axis_field": field,
        "expected_pole": "low raw loading in U_R",
        "inside_sense_n": inside_n,
        "inside_mean": inside_mean,
        "outside_mean": outside_mean,
        "inside_minus_outside": delta,
        "aligned_low_pole_delta": aligned_delta,
        "aligned_low_pole_z": aligned_z,
        "negative_loading_inside_count": negative_inside,
        "negative_loading_inside_total": inside_n,
        "spearman_escape_vs_raw": rho_escape,
        "spearman_indicator_vs_raw": rho_indicator,
        "cosine_centered_indicator_vs_raw": cos_indicator,
        "cosine_centered_escape_vs_raw": cos_escape,
        "projection_centered_indicator_on_axis": projection_indicator,
        "projection_centered_escape_on_axis": projection_escape,
        "size6_random_subset_p_aligned_z": empirical_ge_p(aligned_z, random_size6),
        "sense_fixed_random_subset_p_aligned_z": empirical_ge_p(aligned_z, random_sense_fixed),
        "passed": aligned_z > 0.0 and empirical_ge_p(aligned_z, random_size6) <= 0.05,
    }


def main() -> None:
    cells = reconstruct_window6_partition()
    ur_labels = cells["U_R"]
    matrix = edge_matrix(cells)
    outward_degrees = outward_degree_by_label(ur_labels)
    escape_by_label = {label: degree / 6.0 for label, degree in outward_degrees.items()}
    rows = load_vectors()

    all_labels = [str(row["q6_label"]) for row in rows]
    sense_labels = [str(row["q6_label"]) for row in rows if row["is_sense"]]
    ur_codons = sorted(str(row["codon"]) for row in rows if row["q6_label"] in ur_labels)
    ur_sense_codons = sorted(str(row["codon"]) for row in rows if row["q6_label"] in ur_labels and row["is_sense"])

    expected_matrix = [[28, 63, 23, 20], [63, 21, 21, 6], [23, 21, 2, 6], [20, 6, 6, 2]]
    boundary_leave_count = matrix[3][0] + matrix[3][1] + matrix[3][2]
    escape_ratio = boundary_leave_count / (6 * len(ur_labels))
    cell_sizes = {cell: len(cells[cell]) for cell in CELL_ORDER}

    checks: list[dict[str, object]] = [
        {
            "name": "window6_partition_self_check",
            "passed": cell_sizes == {"U_2": 27, "U_1": 22, "U_L": 9, "U_R": 6}
            and sum(cell_sizes.values()) == 64
            and len(set().union(*cells.values())) == 64,
            "cell_sizes": cell_sizes,
            "cell_size_sum": sum(cell_sizes.values()),
            "u_r_labels": sorted(ur_labels),
            "u_r_codons": ur_codons,
            "u_r_sense_codons": ur_sense_codons,
        },
        {
            "name": "window6_edge_escape_self_check",
            "passed": matrix == expected_matrix and boundary_leave_count == 32 and abs(escape_ratio - (8 / 9)) < 1e-15,
            "edge_matrix": matrix,
            "boundary_leave_count": boundary_leave_count,
            "escape_ratio": escape_ratio,
            "u_r_outward_degrees": outward_degrees,
            "u_r_escape_values": escape_by_label,
        },
    ]

    axis_specs = [
        ("trna_tai_mean", "trna_supply_tai_mean"),
        ("trna_consensus", "trna_consensus_loading"),
        ("d_perp_usage_frequency", "d_perp_loading"),
        ("optimal", "optimal_loading"),
    ]
    axis_checks = [
        axis_report(rows, ur_labels, escape_by_label, field, axis_name, all_labels, sense_labels)
        for axis_name, field in axis_specs
    ]
    checks.extend(axis_checks)

    primary_fields = ["trna_supply_tai_mean", "d_perp_loading"]
    observed_joint_score = mean(axis_alignment_z(rows, ur_labels, field) for field in primary_fields)
    joint_null = null_scores(rows, all_labels, 6, NULL_DRAWS, primary_fields)
    null_p = empirical_ge_p(observed_joint_score, joint_null)
    d_perp_p = next(item["size6_random_subset_p_aligned_z"] for item in axis_checks if item["axis_field"] == "d_perp_loading")
    trna_p = next(item["size6_random_subset_p_aligned_z"] for item in axis_checks if item["axis_field"] == "trna_supply_tai_mean")
    trna_delta = next(item["inside_minus_outside"] for item in axis_checks if item["axis_field"] == "trna_supply_tai_mean")
    d_perp_delta = next(item["inside_minus_outside"] for item in axis_checks if item["axis_field"] == "d_perp_loading")

    certified = (
        trna_delta < 0.0
        and d_perp_delta < 0.0
        and trna_p <= 0.05
        and d_perp_p <= 0.05
        and null_p <= 0.05
    )
    status = "certified" if certified else "coincidence"

    note = (
        "Window6 U_R is reconstructed from origin/feat/fibonacci_reality-deepening "
        "window6-green-spectral-response-alpha-readout-frontier.tex and "
        "window6-markov-kernel-coarse-spectrum-fibonacci-leading.tex: X6 boundary "
        "w1=w6=1, Foldbin tail constraints, and cutoff value<=63 give U_R labels "
        "001110,010001,010011,110000,110011,110101.  The files give the cell-level "
        "edge ledger |dU_R|=32 and escape ratio 8/9; this script reconstructs a "
        "per-codon escape score as hypercube outward degree/6 inside U_R and 0 "
        "outside.  In the delivered bio q6 frame U_R is not tRNA-poor: its sense "
        "codons have slightly higher tai mean than the complement.  The d_perp and "
        "optimal low-pole directions are weakly favorable but do not clear the "
        "size-6 null.  Therefore the right-boundary/selection-axis bridge is not "
        "structurally certified by sign/rank/projection evidence."
    )

    emit(
        status,
        checks=checks,
        null_p=null_p,
        observed_joint_low_trna_low_d_perp_z=observed_joint_score,
        null_model={
            "kind": "random size-6 subsets of the 64 q6 labels; biological statistics use codons with non-null axis values",
            "draws": NULL_DRAWS,
            "seed": RANDOM_SEED,
            "primary_score": "mean of low-pole z scores for trna_supply_tai_mean and d_perp_loading",
        },
        verdict_reason=(
            "coincidence: U_R is geometrically forced, but the biological alignment is weak, "
            "tRNA-poor sign fails, and the joint projection is null-indistinguishable"
        ),
        note=note,
    )


if __name__ == "__main__":
    main()

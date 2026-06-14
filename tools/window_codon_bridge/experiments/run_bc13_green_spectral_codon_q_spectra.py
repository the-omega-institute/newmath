#!/usr/bin/env python3
"""Window6 Green/resolvent spectrum versus codon q1/q3/q4 cube spectra.

This is a label-free spectral audit.  The Window side is the finite four-cell
coarse Markov kernel from the Green/resolvent calculation.  The codon side is
the standard-code Q6 partition under the encoding U/T=00, C=01, A=10, G=11.

The codon q-layer operator used here is the reversible quotient/coface
affinity operator: every q-dimensional cube face contributes one clique on its
vertices, then the clique weights are pushed to amino-acid/stop blocks.  For
q=1 this is exactly the one-bit Q6 edge quotient; q=3 and q=4 use the same
label-free coface rule behind q3_spectrum and q4_spectrum.
"""
from __future__ import annotations

from collections import Counter
from itertools import combinations, product
import json
import math
import random
import sys
from typing import Hashable


EXPERIMENT_ID = "bc13_green_spectral_codon_q_spectra"
CLAIM_ID = "bridge.window6_codon_q6.green_spectral_codon_q_spectra"
RANDOM_SEED = 613046
NULL_DRAWS = 2000

BASES = ("T", "C", "A", "G")
BASE_TO_BITS = {"T": "00", "C": "01", "A": "10", "G": "11"}
BITS_TO_BASE = {value: key for key, value in BASE_TO_BITS.items()}

WINDOW_CELL_NAMES = ("U_2", "U_1", "U_L", "U_R")
WINDOW_CELL_SIZES = (27, 22, 9, 6)
WINDOW_EDGE_MATRIX = (
    (28, 63, 23, 20),
    (63, 21, 21, 6),
    (23, 21, 2, 6),
    (20, 6, 6, 2),
)
WINDOW_EXPECTED_EIGENVALUES = (1.0, 0.0932570603, -0.0706075224, -0.1736035222)

MODULES = {
    "Stop/Trp": {"TAA", "TAG", "TGA", "TGG"},
    "Ile/Met": {"ATT", "ATC", "ATA", "ATG"},
}

CODON_TO_FAMILY = {
    "TTT": "F", "TTC": "F", "TTA": "L", "TTG": "L",
    "TCT": "S", "TCC": "S", "TCA": "S", "TCG": "S",
    "TAT": "Y", "TAC": "Y", "TAA": "*", "TAG": "*",
    "TGT": "C", "TGC": "C", "TGA": "*", "TGG": "W",
    "CTT": "L", "CTC": "L", "CTA": "L", "CTG": "L",
    "CCT": "P", "CCC": "P", "CCA": "P", "CCG": "P",
    "CAT": "H", "CAC": "H", "CAA": "Q", "CAG": "Q",
    "CGT": "R", "CGC": "R", "CGA": "R", "CGG": "R",
    "ATT": "I", "ATC": "I", "ATA": "I", "ATG": "M",
    "ACT": "T", "ACC": "T", "ACA": "T", "ACG": "T",
    "AAT": "N", "AAC": "N", "AAA": "K", "AAG": "K",
    "AGT": "S", "AGC": "S", "AGA": "R", "AGG": "R",
    "GTT": "V", "GTC": "V", "GTA": "V", "GTG": "V",
    "GCT": "A", "GCC": "A", "GCA": "A", "GCG": "A",
    "GAT": "D", "GAC": "D", "GAA": "E", "GAG": "E",
    "GGT": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}

HISTOGRAM_BINS = (-1.0, -0.75, -0.5, -0.25, 0.0, 0.25, 0.5, 0.75, 1.000000001)
QUANTILE_POINTS = tuple(index / 10 for index in range(11))


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def approx_check(name: str, observed: list[float], expected: tuple[float, ...], tol: float) -> dict[str, object]:
    ok = len(observed) == len(expected) and all(abs(a - b) <= tol for a, b in zip(observed, expected))
    return {
        "name": name,
        "ok": ok,
        "observed": [round(value, 10) for value in observed],
        "expected": [round(value, 10) for value in expected],
        "tol": tol,
    }


def codon_order() -> list[str]:
    return ["".join(parts) for parts in product(BASES, repeat=3)]


def bits(codon: str) -> str:
    return "".join(BASE_TO_BITS[base] for base in codon)


def codon_from_bits(word: str) -> str:
    return "".join(BITS_TO_BASE[word[index : index + 2]] for index in (0, 2, 4))


def multiplicity_pattern(labels: list[str]) -> str:
    return "+".join(str(value) for value in sorted(Counter(labels).values(), reverse=True))


def q1_spectrum(table: dict[str, str]) -> tuple[list[int], list[int]]:
    same_by_direction: list[int] = []
    diff_by_direction: list[int] = []
    for direction in range(6):
        same = 0
        diff = 0
        for point in product("01", repeat=6):
            if point[direction] == "1":
                continue
            neighbor = list(point)
            neighbor[direction] = "1"
            left = codon_from_bits("".join(point))
            right = codon_from_bits("".join(neighbor))
            if table[left] == table[right]:
                same += 1
            else:
                diff += 1
        same_by_direction.append(same)
        diff_by_direction.append(diff)
    return same_by_direction, diff_by_direction


def q3_spectrum(table: dict[str, str]) -> tuple[Counter[str], list[dict[str, object]]]:
    total: Counter[str] = Counter()
    cubes: list[dict[str, object]] = []
    for free in combinations(range(6), 3):
        fixed = [index for index in range(6) if index not in free]
        for values in product("01", repeat=3):
            word = [""] * 6
            for index, value in zip(fixed, values):
                word[index] = value
            vertices: list[str] = []
            for local in product("01", repeat=3):
                candidate = word.copy()
                for index, value in zip(free, local):
                    candidate[index] = value
                vertices.append(codon_from_bits("".join(candidate)))
            pattern = multiplicity_pattern([table[codon] for codon in vertices])
            total[pattern] += 1
            cubes.append({"free_bits": free, "vertices": tuple(vertices), "pattern": pattern})
    return total, cubes


def q4_spectrum(table: dict[str, str]) -> tuple[dict[str, object], list[dict[str, object]]]:
    max_distribution: Counter[int] = Counter()
    complete_six: Counter[str] = Counter()
    cubes: list[dict[str, object]] = []
    class_sizes = Counter(table.values())
    for free in combinations(range(6), 4):
        fixed = [index for index in range(6) if index not in free]
        for values in product("01", repeat=2):
            word = [""] * 6
            for index, value in zip(fixed, values):
                word[index] = value
            vertices: list[str] = []
            for local in product("01", repeat=4):
                candidate = word.copy()
                for index, value in zip(free, local):
                    candidate[index] = value
                vertices.append(codon_from_bits("".join(candidate)))
            labels = [table[codon] for codon in vertices]
            counts = Counter(labels)
            max_distribution[max(counts.values())] += 1
            for label, count in counts.items():
                if count == 6 and class_sizes[label] == 6:
                    complete_six[label] += 1
            cubes.append(
                {
                    "free_bits": free,
                    "vertices": tuple(vertices),
                    "pattern": multiplicity_pattern(labels),
                    "class_counts": dict(sorted(counts.items())),
                }
            )
    return {
        "max_class_size_distribution": dict(sorted(max_distribution.items())),
        "complete_six_class_occurrences": dict(sorted(complete_six.items())),
    }, cubes


def containing_cube_patterns(cubes: list[dict[str, object]], tile: set[str]) -> dict[str, int]:
    patterns: Counter[str] = Counter()
    for cube in cubes:
        if tile.issubset(set(cube["vertices"])):
            patterns[str(cube["pattern"])] += 1
    return dict(sorted(patterns.items()))


def containing_q4_neighborhoods(cubes: list[dict[str, object]], tile: set[str]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for cube in cubes:
        if tile.issubset(set(cube["vertices"])):
            rows.append(cube)
    rows.sort(key=lambda item: item["free_bits"])
    return rows


def q_faces(q: int) -> list[list[int]]:
    codons = codon_order()
    codon_index = {codon: index for index, codon in enumerate(codons)}
    faces: list[list[int]] = []
    for free in combinations(range(6), q):
        fixed = [index for index in range(6) if index not in free]
        for values in product("01", repeat=6 - q):
            word = [""] * 6
            for index, value in zip(fixed, values):
                word[index] = value
            face: list[int] = []
            for local in product("01", repeat=q):
                candidate = word.copy()
                for index, value in zip(free, local):
                    candidate[index] = value
                face.append(codon_index[codon_from_bits("".join(candidate))])
            faces.append(face)
    return faces


def jacobi_eigenvalues(matrix: list[list[float]], tol: float = 1e-12, max_rotations: int = 1600) -> list[float]:
    n = len(matrix)
    a = [row[:] for row in matrix]
    for _ in range(max_rotations):
        p = 0
        q = 1 if n > 1 else 0
        max_value = 0.0
        for i in range(n):
            for j in range(i + 1, n):
                value = abs(a[i][j])
                if value > max_value:
                    max_value = value
                    p = i
                    q = j
        if max_value <= tol:
            break
        if abs(a[p][p] - a[q][q]) <= tol:
            angle = math.pi / 4
        else:
            angle = 0.5 * math.atan2(2.0 * a[p][q], a[q][q] - a[p][p])
        c = math.cos(angle)
        s = math.sin(angle)
        app = a[p][p]
        aqq = a[q][q]
        apq = a[p][q]
        a[p][p] = c * c * app - 2.0 * s * c * apq + s * s * aqq
        a[q][q] = s * s * app + 2.0 * s * c * apq + c * c * aqq
        a[p][q] = 0.0
        a[q][p] = 0.0
        for r in range(n):
            if r == p or r == q:
                continue
            arp = a[r][p]
            arq = a[r][q]
            a[r][p] = c * arp - s * arq
            a[p][r] = a[r][p]
            a[r][q] = s * arp + c * arq
            a[q][r] = a[r][q]
    return sorted((a[i][i] for i in range(n)), reverse=True)


def normalized_operator_eigenvalues(weights: list[list[float]]) -> list[float]:
    n = len(weights)
    degrees = [sum(row) for row in weights]
    sym = [[0.0 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if degrees[i] > 0 and degrees[j] > 0:
                sym[i][j] = weights[i][j] / math.sqrt(degrees[i] * degrees[j])
    return jacobi_eigenvalues(sym)


def window_weights() -> list[list[float]]:
    weights: list[list[float]] = []
    for i, row in enumerate(WINDOW_EDGE_MATRIX):
        out: list[float] = []
        for j, value in enumerate(row):
            out.append(float(2 * value if i == j else value))
        weights.append(out)
    return weights


def quotient_coface_weights(labels: list[Hashable], faces: list[list[int]]) -> list[list[float]]:
    names = sorted(set(labels), key=lambda item: str(item))
    index = {name: pos for pos, name in enumerate(names)}
    weights = [[0.0 for _ in names] for _ in names]
    for face in faces:
        for left_pos, right_pos in combinations(face, 2):
            left = index[labels[left_pos]]
            right = index[labels[right_pos]]
            if left == right:
                weights[left][left] += 2.0
            else:
                weights[left][right] += 1.0
                weights[right][left] += 1.0
    return weights


def density_histogram(eigenvalues: list[float]) -> dict[str, float]:
    counts = [0] * (len(HISTOGRAM_BINS) - 1)
    for value in eigenvalues:
        placed = False
        for index in range(len(HISTOGRAM_BINS) - 1):
            if HISTOGRAM_BINS[index] <= value < HISTOGRAM_BINS[index + 1]:
                counts[index] += 1
                placed = True
                break
        if not placed:
            if value < HISTOGRAM_BINS[0]:
                counts[0] += 1
            else:
                counts[-1] += 1
    total = len(eigenvalues)
    return {
        f"{HISTOGRAM_BINS[index]:.2f}:{HISTOGRAM_BINS[index + 1]:.2f}": counts[index] / total
        for index in range(len(counts))
    }


def quantiles(values: list[float], points: tuple[float, ...] = QUANTILE_POINTS) -> list[float]:
    ordered = sorted(values)
    if len(ordered) == 1:
        return [ordered[0] for _ in points]
    out: list[float] = []
    for point in points:
        raw = point * (len(ordered) - 1)
        lo = int(math.floor(raw))
        hi = int(math.ceil(raw))
        if lo == hi:
            out.append(ordered[lo])
        else:
            frac = raw - lo
            out.append(ordered[lo] * (1.0 - frac) + ordered[hi] * frac)
    return out


def spectral_signature(name: str, eigenvalues: list[float]) -> dict[str, object]:
    ordered = sorted(eigenvalues, reverse=True)
    laplacian = sorted(1.0 - value for value in ordered)
    nontrivial_abs = max((abs(value) for value in ordered[1:]), default=0.0)
    return {
        "name": name,
        "dimension": len(ordered),
        "sorted_normalized_adjacency_eigenvalues": [round(value, 10) for value in ordered],
        "sorted_normalized_laplacian_eigenvalues": [round(value, 10) for value in laplacian],
        "spectral_gap_lambda1_minus_lambda2": round(ordered[0] - ordered[1], 10) if len(ordered) > 1 else None,
        "absolute_spectral_gap": round(ordered[0] - nontrivial_abs, 10),
        "moments": {f"S{k}": round(sum(value**k for value in ordered), 10) for k in range(1, 5)},
        "normalized_moments": {f"M{k}": round(sum(value**k for value in ordered) / len(ordered), 10) for k in range(1, 5)},
        "spectral_density_histogram": density_histogram(ordered),
        "laplacian_quantiles": [round(value, 10) for value in quantiles(laplacian)],
    }


def signature_distance(left: dict[str, object], right: dict[str, object]) -> dict[str, object]:
    left_moments = left["normalized_moments"]
    right_moments = right["normalized_moments"]
    moment_rmse = math.sqrt(
        sum((float(left_moments[f"M{k}"]) - float(right_moments[f"M{k}"])) ** 2 for k in range(1, 5)) / 4.0
    )
    left_hist = left["spectral_density_histogram"]
    right_hist = right["spectral_density_histogram"]
    density_l1 = sum(abs(float(left_hist[key]) - float(right_hist[key])) for key in left_hist)
    left_quantiles = [float(value) for value in left["laplacian_quantiles"]]
    right_quantiles = [float(value) for value in right["laplacian_quantiles"]]
    quantile_l2 = math.sqrt(sum((a - b) ** 2 for a, b in zip(left_quantiles, right_quantiles)) / len(left_quantiles))
    ordered_gap_diff = abs(
        float(left["spectral_gap_lambda1_minus_lambda2"]) - float(right["spectral_gap_lambda1_minus_lambda2"])
    )
    absolute_gap_diff = abs(float(left["absolute_spectral_gap"]) - float(right["absolute_spectral_gap"]))
    score = density_l1 + quantile_l2 + 3.0 * moment_rmse + 0.5 * ordered_gap_diff + 0.5 * absolute_gap_diff
    return {
        "score": round(score, 10),
        "density_l1": round(density_l1, 10),
        "moment_rmse": round(moment_rmse, 10),
        "laplacian_quantile_l2": round(quantile_l2, 10),
        "ordered_gap_diff": round(ordered_gap_diff, 10),
        "absolute_gap_diff": round(absolute_gap_diff, 10),
        "dimension_match": left["dimension"] == right["dimension"],
    }


def random_partition_labels(sizes: list[int], rng: random.Random) -> list[int]:
    labels: list[int] = []
    for block, size in enumerate(sizes):
        labels.extend([block] * size)
    rng.shuffle(labels)
    return labels


def null_stats(observed_score: float, values: list[float]) -> dict[str, object]:
    ordered = sorted(values)
    mean = sum(values) / len(values)
    variance = sum((value - mean) ** 2 for value in values) / (len(values) - 1)
    lower_tail = (sum(1 for value in values if value <= observed_score) + 1) / (len(values) + 1)
    upper_tail = (sum(1 for value in values if value >= observed_score) + 1) / (len(values) + 1)
    return {
        "draws": len(values),
        "min": round(ordered[0], 10),
        "q01": round(ordered[int(0.01 * (len(ordered) - 1))], 10),
        "q05": round(ordered[int(0.05 * (len(ordered) - 1))], 10),
        "q50": round(ordered[int(0.50 * (len(ordered) - 1))], 10),
        "q95": round(ordered[int(0.95 * (len(ordered) - 1))], 10),
        "max": round(ordered[-1], 10),
        "mean": round(mean, 10),
        "sd": round(math.sqrt(variance), 10),
        "observed_score": round(observed_score, 10),
        "lower_tail_p_closer_or_equal": lower_tail,
        "upper_tail_p_farther_or_equal": upper_tail,
    }


def run_nulls(
    window_signature: dict[str, object],
    q_face_map: dict[str, list[list[int]]],
    family_sizes: list[int],
    rng: random.Random,
) -> dict[str, object]:
    nulls: dict[str, object] = {}
    for q_name, faces in q_face_map.items():
        observed_scores: list[float] = []
        for _ in range(NULL_DRAWS):
            labels = random_partition_labels(family_sizes, rng)
            weights = quotient_coface_weights(labels, faces)
            signature = spectral_signature(f"null_{q_name}", normalized_operator_eigenvalues(weights))
            observed_scores.append(float(signature_distance(window_signature, signature)["score"]))
        nulls[q_name] = observed_scores
    return nulls


def main() -> None:
    rng = random.Random(RANDOM_SEED)
    checks: list[dict[str, object]] = []

    window_degrees = [sum(row) for row in window_weights()]
    checks.append(check_row("window_degree_ledger", [int(value) for value in window_degrees], [6 * size for size in WINDOW_CELL_SIZES]))
    window_eigenvalues = normalized_operator_eigenvalues(window_weights())
    checks.append(approx_check("window_markov_spectrum", window_eigenvalues, WINDOW_EXPECTED_EIGENVALUES, 1e-7))

    codons = codon_order()
    table = dict(CODON_TO_FAMILY)
    labels = [table[codon] for codon in codons]
    q1_same, q1_diff = q1_spectrum(table)
    q3_total, q3_cubes = q3_spectrum(table)
    q4_summary, q4_cubes = q4_spectrum(table)
    stop_q4 = containing_q4_neighborhoods(q4_cubes, MODULES["Stop/Trp"])
    ile_q4 = containing_q4_neighborhoods(q4_cubes, MODULES["Ile/Met"])

    checks.append(check_row("codon_q6_encoding_count", len({bits(codon) for codon in codons}), 64))
    checks.append(check_row("codon_family_count", len(set(labels)), 21))
    checks.append(check_row("q1_same_by_direction", q1_same, [0, 2, 0, 1, 17, 30]))
    checks.append(check_row("q1_diff_by_direction", q1_diff, [32, 30, 32, 31, 15, 2]))
    checks.append(check_row("q1_same_total", sum(q1_same), 50))
    checks.append(check_row("q3_6_plus_2_count", q3_total["6+2"], 1))
    checks.append(check_row("q3_stop_trp_neighborhoods", containing_cube_patterns(q3_cubes, MODULES["Stop/Trp"]), {"3+2+2+1": 4}))
    checks.append(
        check_row(
            "q3_ile_met_neighborhoods",
            containing_cube_patterns(q3_cubes, MODULES["Ile/Met"]),
            {"3+2+2+1": 2, "4+3+1": 2},
        )
    )
    checks.append(
        check_row(
            "q4_max_class_size_distribution",
            q4_summary["max_class_size_distribution"],
            {2: 17, 3: 15, 4: 23, 6: 5},
        )
    )
    checks.append(check_row("q4_complete_six_class_occurrences", q4_summary["complete_six_class_occurrences"], {"L": 3, "R": 1, "S": 1}))
    checks.append(check_row("q4_stop_trp_neighborhood_count", len(stop_q4), 6))
    checks.append(check_row("q4_ile_met_neighborhood_count", len(ile_q4), 6))
    checks.append(check_row("q4_stop_trp_local_counts", all(row["class_counts"].get("*") == 3 and row["class_counts"].get("W") == 1 for row in stop_q4), True))
    checks.append(check_row("q4_ile_met_local_counts", all(row["class_counts"].get("I") == 3 and row["class_counts"].get("M") == 1 for row in ile_q4), True))

    if not all(row["ok"] for row in checks):
        emit(
            "needs_derivation",
            window_spectrum={},
            codon_q_spectra={},
            nulls={},
            checks=checks,
            note="self-check failed; no bridge verdict emitted",
        )

    q_face_map = {"q1": q_faces(1), "q3": q_faces(3), "q4": q_faces(4)}
    window_signature = spectral_signature("window_green_resolvent_four_cell", window_eigenvalues)

    codon_signatures: dict[str, dict[str, object]] = {}
    comparisons: dict[str, dict[str, object]] = {}
    for q_name, faces in q_face_map.items():
        weights = quotient_coface_weights(labels, faces)
        eigenvalues = normalized_operator_eigenvalues(weights)
        signature = spectral_signature(f"codon_{q_name}_coface_affinity", eigenvalues)
        codon_signatures[q_name] = signature
        comparisons[q_name] = signature_distance(window_signature, signature)

    family_sizes = sorted(Counter(labels).values(), reverse=True)
    raw_null_scores = run_nulls(window_signature, q_face_map, family_sizes, rng)
    nulls = {
        q_name: {
            **null_stats(float(comparisons[q_name]["score"]), scores),
            "model": "random Q6 vertex partition with the standard-code family-size multiset; same q-face coface operator",
        }
        for q_name, scores in raw_null_scores.items()
    }

    q_summary = {
        "q1_source_spectrum": {"same_by_direction": q1_same, "diff_by_direction": q1_diff, "same_total": sum(q1_same)},
        "q3_source_spectrum": {
            "total": dict(sorted(q3_total.items())),
            "stop_trp_neighborhoods": containing_cube_patterns(q3_cubes, MODULES["Stop/Trp"]),
            "ile_met_neighborhoods": containing_cube_patterns(q3_cubes, MODULES["Ile/Met"]),
        },
        "q4_source_spectrum": q4_summary,
        "q_layer_operator_note": "q-dimensional cube faces are converted to label-free quotient/coface affinity Markov operators before eigenvalue comparison",
        "q1": codon_signatures["q1"],
        "q3": codon_signatures["q3"],
        "q4": codon_signatures["q4"],
        "comparisons_to_window": comparisons,
    }

    all_dimension_match = all(row["dimension_match"] for row in comparisons.values())
    all_extreme_close = all(nulls[q_name]["lower_tail_p_closer_or_equal"] <= 0.01 for q_name in ("q1", "q3", "q4"))
    all_profile_close = all(
        comparisons[q_name]["density_l1"] <= 0.35
        and comparisons[q_name]["moment_rmse"] <= 0.06
        and comparisons[q_name]["laplacian_quantile_l2"] <= 0.12
        for q_name in ("q1", "q3", "q4")
    )
    any_moment_near = any(comparisons[q_name]["moment_rmse"] <= 0.06 for q_name in ("q1", "q3", "q4"))

    if all_dimension_match and all_extreme_close and all_profile_close:
        status = "certified"
        note = (
            "All q-layer spectral profiles match the Window Green/resolvent signature in dimension, density, moments, "
            "gaps, and extreme lower-tail null position. This would require a separate structural map to remain credible."
        )
    elif any_moment_near and not all_profile_close:
        status = "coincidence"
        note = (
            "At least one normalized moment is close, but the full spectral profile fails density/gap/quantile compatibility "
            "or the null extremality test. This is not a spectral isomorphism certificate."
        )
    else:
        status = "refuted"
        note = (
            "The Window Green/resolvent object is a four-state reversible Markov spectrum, while the codon q1/q3/q4 "
            "coface-affinity spectra are 21-family quotient spectra. Dimension, spectral density, gap, and moment profiles "
            "are incompatible, and the observed distances are not certified as extreme close under the fixed-size Q6 null."
        )

    emit(
        status,
        window_spectrum={
            "source": "origin/feat/fibonacci_reality-deepening Window6 Green/resolvent finite four-cell kernel; alpha readout ignored",
            "cell_order": WINDOW_CELL_NAMES,
            "cell_sizes": WINDOW_CELL_SIZES,
            "edge_matrix": WINDOW_EDGE_MATRIX,
            "signature": window_signature,
        },
        codon_q_spectra=q_summary,
        nulls=nulls,
        checks=checks,
        note=note,
    )


if __name__ == "__main__":
    main()

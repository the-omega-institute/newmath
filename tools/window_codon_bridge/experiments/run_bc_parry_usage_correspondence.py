#!/usr/bin/env python3
"""BC Parry measure versus codon usage-frequency axis.

The experiment keeps the map fixed by the shared Q6 encoding
U=00,C=01,A=10,G=11.  It reconstructs the Window6 maximal-entropy Parry
measure from the no-adjacent-one transfer operator and tests its induced
per-codon weights against biological loading axes by rank and projection.
"""
from __future__ import annotations

from itertools import product, permutations
import json
import math
import random
import sys
from pathlib import Path


EXPERIMENT_ID = "bc_parry_usage_correspondence"
CLAIM_ID = "bridge.window6_codon_q6.parry_measure_usage_correspondence"

DATA_PATH = Path("papers/window_codon_bridge/data/codon_q6_selection_vectors.json")
RANDOM_SEED = 607006
NULL_DRAWS = 5000

BASES = ("U", "C", "A", "G")
BASE_TO_BITS = {"U": (0, 0), "C": (0, 1), "A": (1, 0), "G": (1, 1)}
BITS_TO_BASE = {bits: base for base, bits in BASE_TO_BITS.items()}

VENDOR_NOTE = (
    "Parry measure reconstructed from origin/feat/fibonacci_reality-deepening "
    "forced_window_structure/window6-parry-measure-golden-maximal-entropy.tex "
    "and window6-transfer-operator-golden-perron-spectrum.tex: transfer matrix "
    "[[1,1],[1,0]], Perron root phi, transition kernel "
    "[[1/phi,1/phi^2],[1,0]], stationary distribution "
    "(phi^2/(phi^2+1),1/(phi^2+1))."
)


def emit(status: str, **fields: object) -> None:
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
    }
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def codon_order() -> list[str]:
    return ["".join(chars) for chars in product(BASES, repeat=3)]


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


def bits_to_label(bits: tuple[int, ...]) -> str:
    return "".join(str(bit) for bit in bits)


def label_to_bits(label: str) -> tuple[int, ...]:
    return tuple(int(char) for char in label)


def load_vectors() -> list[dict[str, object]]:
    data = json.loads(DATA_PATH.read_text())
    rows = []
    for row in data.get("vectors", []):
        codon = str(row["codon"])
        bits = tuple(int(bit) for bit in row["q6_bits"])
        label = bits_to_label(bits)
        if bits != codon_to_q6(codon):
            raise ValueError(f"codon/q6 mismatch for {codon}")
        if label != row["q6_label"]:
            raise ValueError(f"q6 label mismatch for {codon}")
        rows.append(dict(row))
    rows.sort(key=lambda row: codon_order().index(str(row["codon"])))
    if len(rows) != 64:
        raise ValueError(f"expected 64 codon rows, got {len(rows)}")
    if [str(row["codon"]) for row in rows] != codon_order():
        raise ValueError("codon rows do not cover the canonical Q6 codon order")
    return rows


def mat_vec(matrix: list[list[float]], vector: list[float]) -> list[float]:
    return [sum(row[index] * vector[index] for index in range(len(vector))) for row in matrix]


def norm(values: list[float]) -> float:
    return math.sqrt(sum(value * value for value in values))


def power_iteration(matrix: list[list[float]], steps: int = 80) -> tuple[float, list[float]]:
    vector = [1.0 for _ in matrix]
    for _ in range(steps):
        nxt = mat_vec(matrix, vector)
        scale = norm(nxt)
        if scale == 0.0:
            raise ValueError("power iteration reached zero vector")
        vector = [value / scale for value in nxt]
    image = mat_vec(matrix, vector)
    eigenvalue = sum(a * b for a, b in zip(vector, image)) / sum(a * a for a in vector)
    return eigenvalue, vector


def parry_data() -> dict[str, object]:
    phi = (1.0 + math.sqrt(5.0)) / 2.0
    transfer = [[1.0, 1.0], [1.0, 0.0]]
    lambda_power, right_power = power_iteration(transfer)
    right_exact = [phi, 1.0]
    left_exact = [phi, 1.0]
    transition = [
        [1.0 / phi, 1.0 / (phi * phi)],
        [1.0, 0.0],
    ]
    stationary = [
        (phi * phi) / (phi * phi + 1.0),
        1.0 / (phi * phi + 1.0),
    ]
    return {
        "phi": phi,
        "transfer": transfer,
        "lambda_power": lambda_power,
        "right_power": right_power,
        "right_exact": right_exact,
        "left_exact": left_exact,
        "transition": transition,
        "stationary": stationary,
    }


def no_adjacent_ones(bits: tuple[int, ...]) -> bool:
    return all(not (bits[index] and bits[index + 1]) for index in range(len(bits) - 1))


def parry_weight_for_bits(bits: tuple[int, ...], pdata: dict[str, object]) -> float:
    transition = pdata["transition"]
    stationary = pdata["stationary"]
    assert isinstance(transition, list)
    assert isinstance(stationary, list)
    weight = float(stationary[bits[0]])
    for left, right in zip(bits, bits[1:]):
        weight *= float(transition[left][right])
    return weight


def parry_weights_by_label(pdata: dict[str, object]) -> dict[str, float]:
    return {
        bits_to_label(bits): parry_weight_for_bits(bits, pdata)
        for bits in product((0, 1), repeat=6)
    }


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def centered(values: list[float]) -> list[float]:
    m = mean(values)
    return [value - m for value in values]


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def cosine(left: list[float], right: list[float]) -> float | None:
    denom = norm(left) * norm(right)
    if denom == 0.0:
        return None
    return dot(left, right) / denom


def ranks(values: list[float]) -> list[float]:
    order = sorted(range(len(values)), key=lambda index: values[index])
    result = [0.0 for _ in values]
    start = 0
    while start < len(values):
        end = start + 1
        while end < len(values) and values[order[end]] == values[order[start]]:
            end += 1
        average = (start + 1 + end) / 2.0
        for pos in range(start, end):
            result[order[pos]] = average
        start = end
    return result


def pearson(left: list[float], right: list[float]) -> float | None:
    if len(left) != len(right) or len(left) < 2:
        return None
    left_c = centered(left)
    right_c = centered(right)
    denom = norm(left_c) * norm(right_c)
    if denom == 0.0:
        return None
    return dot(left_c, right_c) / denom


def spearman(left: list[float], right: list[float]) -> float | None:
    return pearson(ranks(left), ranks(right))


def sample_sd(values: list[float]) -> float:
    if len(values) < 2:
        return 0.0
    m = mean(values)
    return math.sqrt(sum((value - m) ** 2 for value in values) / (len(values) - 1))


def quantile(sorted_values: list[float], q: float) -> float:
    if not sorted_values:
        return 0.0
    pos = q * (len(sorted_values) - 1)
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return sorted_values[lo]
    frac = pos - lo
    return sorted_values[lo] * (1.0 - frac) + sorted_values[hi] * frac


def null_summary(observed: float, values: list[float], tail: str = "upper") -> dict[str, object]:
    sorted_values = sorted(values)
    m = mean(values)
    sd = sample_sd(values)
    if tail == "lower":
        p_value = (sum(1 for value in values if value <= observed + 1e-15) + 1) / (len(values) + 1)
    elif tail == "two_sided_abs":
        p_value = (sum(1 for value in values if abs(value) >= abs(observed) - 1e-15) + 1) / (len(values) + 1)
    else:
        p_value = (sum(1 for value in values if value >= observed - 1e-15) + 1) / (len(values) + 1)
    return {
        "draws": len(values),
        "seed": RANDOM_SEED,
        "observed": observed,
        "mean": m,
        "sd": sd,
        "q05": quantile(sorted_values, 0.05),
        "q50": quantile(sorted_values, 0.50),
        "q95": quantile(sorted_values, 0.95),
        "p_value": p_value,
        "tail": tail,
    }


def residualize_against_one_covariate(values: list[float], covariate: list[float]) -> list[float]:
    x = centered(covariate)
    y = centered(values)
    denom = dot(x, x)
    if denom == 0.0:
        return y
    beta = dot(y, x) / denom
    return [y[index] - beta * x[index] for index in range(len(values))]


def group_demean(values: list[float], groups: list[str]) -> list[float]:
    sums: dict[str, float] = {}
    counts: dict[str, int] = {}
    for value, group in zip(values, groups):
        sums[group] = sums.get(group, 0.0) + value
        counts[group] = counts.get(group, 0) + 1
    return [value - sums[group] / counts[group] for value, group in zip(values, groups)]


def partial_spearman_gc3(left: list[float], right: list[float], gc3: list[float]) -> float | None:
    left_resid = residualize_against_one_covariate(ranks(left), gc3)
    right_resid = residualize_against_one_covariate(ranks(right), gc3)
    return pearson(left_resid, right_resid)


def aa_residual_spearman(left: list[float], right: list[float], amino_acids: list[str]) -> float | None:
    left_resid = group_demean(left, amino_acids)
    right_resid = group_demean(right, amino_acids)
    return spearman(left_resid, right_resid)


def field_values(rows: list[dict[str, object]], weights: dict[str, float], field: str, sense_only: bool) -> dict[str, object]:
    usable = [
        row for row in rows
        if row.get(field) is not None and (not sense_only or bool(row["is_sense"]))
    ]
    parry = [weights[str(row["q6_label"])] for row in usable]
    axis = [float(row[field]) for row in usable]
    parry_centered = centered(parry)
    axis_centered = centered(axis)
    axis_norm = norm(axis_centered)
    gc3 = [1.0 if str(row["codon"])[2] in ("C", "G") else 0.0 for row in usable]
    amino_acids = [str(row["amino_acid"]) for row in usable]
    cos = cosine(parry_centered, axis_centered)
    return {
        "n": len(usable),
        "spearman": spearman(parry, axis),
        "pearson_centered": pearson(parry, axis),
        "cosine_centered": cos,
        "projection_on_unit_axis": None if axis_norm == 0.0 else dot(parry_centered, axis_centered) / axis_norm,
        "projection_fraction_of_parry_energy": None if cos is None else cos * cos,
        "partial_spearman_gc3": partial_spearman_gc3(parry, axis, gc3),
        "aa_residual_spearman": aa_residual_spearman(parry, axis, amino_acids) if sense_only else None,
    }


def primary_score(rows: list[dict[str, object]], weights: dict[str, float], sense_only: bool) -> float:
    report = field_values(rows, weights, "d_perp_loading", sense_only)
    value = report["cosine_centered"]
    return float(value) if value is not None else 0.0


def label_permutation_null(
    rows: list[dict[str, object]],
    base_weights: dict[str, float],
    observed: float,
    rng: random.Random,
    sense_only: bool,
) -> dict[str, object]:
    labels = sorted(base_weights)
    values = [base_weights[label] for label in labels]
    scores = []
    for _ in range(NULL_DRAWS):
        shuffled = values[:]
        rng.shuffle(shuffled)
        weights = dict(zip(labels, shuffled))
        scores.append(primary_score(rows, weights, sense_only))
    summary = null_summary(observed, scores, "upper")
    summary["model"] = "random permutation of Parry weights over the 64 codon/Q6 labels"
    return summary


def hypercube_automorphisms() -> list[tuple[tuple[int, ...], tuple[int, ...]]]:
    return [
        (axis_perm, flips)
        for axis_perm in permutations(range(6))
        for flips in product((0, 1), repeat=6)
    ]


def apply_automorphism(bits: tuple[int, ...], axis_perm: tuple[int, ...], flips: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(bits[axis_perm[index]] ^ flips[index] for index in range(6))


def automorphism_null(
    rows: list[dict[str, object]],
    base_weights: dict[str, float],
    observed: float,
    rng: random.Random,
    sense_only: bool,
) -> dict[str, object]:
    automorphisms = hypercube_automorphisms()
    labels = sorted(base_weights)
    scores = []
    for _ in range(NULL_DRAWS):
        axis_perm, flips = rng.choice(automorphisms)
        weights = {}
        for label in labels:
            moved = apply_automorphism(label_to_bits(label), axis_perm, flips)
            weights[label] = base_weights[bits_to_label(moved)]
        scores.append(primary_score(rows, weights, sense_only))
    summary = null_summary(observed, scores, "upper")
    summary["model"] = "random Q6 graph automorphism: coordinate permutation plus coordinate bit flips"
    return summary


def check_row(name: str, passed: bool, **fields: object) -> dict[str, object]:
    return {"name": name, "passed": passed, **fields}


def parry_checks(pdata: dict[str, object], weights: dict[str, float]) -> list[dict[str, object]]:
    phi = float(pdata["phi"])
    transfer = pdata["transfer"]
    transition = pdata["transition"]
    stationary = pdata["stationary"]
    left = pdata["left_exact"]
    right = pdata["right_exact"]
    assert isinstance(transfer, list)
    assert isinstance(transition, list)
    assert isinstance(stationary, list)
    assert isinstance(left, list)
    assert isinstance(right, list)

    mv = mat_vec(transfer, [float(value) for value in right])
    um = [
        sum(float(left[index]) * float(transfer[index][column]) for index in range(2))
        for column in range(2)
    ]
    pi_p = [
        sum(float(stationary[index]) * float(transition[index][column]) for index in range(2))
        for column in range(2)
    ]
    entropy = 0.0
    for index, row in enumerate(transition):
        for prob in row:
            p = float(prob)
            if p > 0.0:
                entropy -= float(stationary[index]) * p * math.log(p)
    admissible = [label for label, value in weights.items() if value > 0.0]
    row_sums = [sum(float(value) for value in row) for row in transition]
    return [
        check_row(
            "perron_power_iteration",
            abs(float(pdata["lambda_power"]) - phi) < 1e-12,
            observed=float(pdata["lambda_power"]),
            expected=phi,
        ),
        check_row(
            "right_perron_vector",
            max(abs(mv[index] - phi * float(right[index])) for index in range(2)) < 1e-12,
            observed=mv,
            expected=[phi * float(right[index]) for index in range(2)],
        ),
        check_row(
            "left_perron_vector",
            max(abs(um[index] - phi * float(left[index])) for index in range(2)) < 1e-12,
            observed=um,
            expected=[phi * float(left[index]) for index in range(2)],
        ),
        check_row(
            "transition_row_stochastic",
            max(abs(value - 1.0) for value in row_sums) < 1e-12,
            observed=row_sums,
            expected=[1.0, 1.0],
        ),
        check_row(
            "stationary_distribution",
            max(abs(float(stationary[index]) - pi_p[index]) for index in range(2)) < 1e-12,
            observed=pi_p,
            expected=stationary,
        ),
        check_row(
            "parry_word_weights_normalize",
            abs(sum(weights.values()) - 1.0) < 1e-12,
            observed=sum(weights.values()),
            expected=1.0,
        ),
        check_row(
            "admissible_width6_count",
            len(admissible) == 21 and all(no_adjacent_ones(label_to_bits(label)) for label in admissible),
            observed=len(admissible),
            expected=21,
        ),
        check_row(
            "entropy_log_phi",
            abs(entropy - math.log(phi)) < 1e-12,
            observed=entropy,
            expected=math.log(phi),
        ),
    ]


def data_checks(rows: list[dict[str, object]]) -> list[dict[str, object]]:
    labels = [str(row["q6_label"]) for row in rows]
    codons = [str(row["codon"]) for row in rows]
    stop_axis_null = [
        str(row["codon"]) for row in rows
        if not row["is_sense"]
        and row.get("d_perp_loading") is None
        and row.get("optimal_loading") is None
        and row.get("trna_supply_tai_mean") is None
    ]
    return [
        check_row(
            "codon_q6_bijection",
            len(set(labels)) == 64 and all(q6_to_codon(label_to_bits(str(row["q6_label"]))) == row["codon"] for row in rows),
            observed={"labels": len(set(labels)), "codons": len(set(codons))},
            expected={"labels": 64, "codons": 64},
        ),
        check_row(
            "sense_codon_count",
            sum(1 for row in rows if row["is_sense"]) == 61,
            observed=sum(1 for row in rows if row["is_sense"]),
            expected=61,
        ),
        check_row(
            "axis_non_null_sense",
            all(row.get("d_perp_loading") is not None for row in rows if row["is_sense"])
            and all(row.get("optimal_loading") is not None for row in rows if row["is_sense"])
            and all(row.get("trna_supply_tai_mean") is not None for row in rows if row["is_sense"]),
            observed={
                "d_perp": sum(1 for row in rows if row["is_sense"] and row.get("d_perp_loading") is not None),
                "optimal": sum(1 for row in rows if row["is_sense"] and row.get("optimal_loading") is not None),
                "trna": sum(1 for row in rows if row["is_sense"] and row.get("trna_supply_tai_mean") is not None),
            },
            expected=61,
        ),
        check_row(
            "stop_codons_have_no_usage_axis_values",
            sorted(stop_axis_null) == ["UAA", "UAG", "UGA"],
            observed=sorted(stop_axis_null),
            expected=["UAA", "UAG", "UGA"],
        ),
    ]


def main() -> None:
    rng = random.Random(RANDOM_SEED)
    rows = load_vectors()
    pdata = parry_data()
    weights = parry_weights_by_label(pdata)
    checks = data_checks(rows) + parry_checks(pdata, weights)

    if not all(row["passed"] for row in checks):
        emit(
            "needs_derivation",
            spearman={},
            projection={},
            partial={},
            nulls={},
            checks=checks,
            note=VENDOR_NOTE + " Self-check failed before the correspondence test.",
        )

    field_names = ("d_perp_loading", "optimal_loading", "trna_supply_tai_mean")
    sense_reports = {field: field_values(rows, weights, field, True) for field in field_names}
    all_reports = {field: field_values(rows, weights, field, False) for field in field_names}
    observed_sense = float(sense_reports["d_perp_loading"]["cosine_centered"] or 0.0)
    observed_all = float(all_reports["d_perp_loading"]["cosine_centered"] or 0.0)
    nulls = {
        "sense_label_permutation": label_permutation_null(rows, weights, observed_sense, rng, True),
        "sense_q6_automorphism": automorphism_null(rows, weights, observed_sense, rng, True),
        "all_label_permutation": label_permutation_null(rows, weights, observed_all, rng, False),
        "all_q6_automorphism": automorphism_null(rows, weights, observed_all, rng, False),
    }

    d_sense = sense_reports["d_perp_loading"]
    d_rho = float(d_sense["spearman"] or 0.0)
    d_cos = float(d_sense["cosine_centered"] or 0.0)
    d_partial_gc3 = float(d_sense["partial_spearman_gc3"] or 0.0)
    d_aa_resid = float(d_sense["aa_residual_spearman"] or 0.0)
    null_significant = (
        nulls["sense_label_permutation"]["p_value"] <= 0.05
        and nulls["sense_q6_automorphism"]["p_value"] <= 0.05
    )
    confound_resistant = d_partial_gc3 > 0.0 and d_aa_resid > 0.0
    certified = d_rho > 0.0 and d_cos > 0.0 and null_significant and confound_resistant
    anti_aligned = d_rho < -0.20 and d_cos < -0.20
    status = "certified" if certified else ("refuted" if anti_aligned else "coincidence")

    verdict_reason = (
        "certified: the canonical Parry cylinder weights align positively with d_perp, "
        "clear both label-free nulls, and retain positive GC3/AA residual alignment"
        if certified
        else (
            "refuted: the canonical Parry cylinder weights are negatively aligned with the d_perp usage axis"
            if status == "refuted"
            else "coincidence: the Parry measure is canonical, but the d_perp alignment does not clear both nulls and confound checks"
        )
    )

    emit(
        status,
        spearman={
            "sense": {field: sense_reports[field]["spearman"] for field in field_names},
            "all_64": {field: all_reports[field]["spearman"] for field in field_names},
        },
        projection={
            "sense": {
                field: {
                    "cosine_centered": sense_reports[field]["cosine_centered"],
                    "projection_on_unit_axis": sense_reports[field]["projection_on_unit_axis"],
                    "projection_fraction_of_parry_energy": sense_reports[field]["projection_fraction_of_parry_energy"],
                    "n": sense_reports[field]["n"],
                }
                for field in field_names
            },
            "all_64": {
                field: {
                    "cosine_centered": all_reports[field]["cosine_centered"],
                    "projection_on_unit_axis": all_reports[field]["projection_on_unit_axis"],
                    "projection_fraction_of_parry_energy": all_reports[field]["projection_fraction_of_parry_energy"],
                    "n": all_reports[field]["n"],
                }
                for field in field_names
            },
        },
        partial={
            "sense_gc3_partial_spearman": {
                field: sense_reports[field]["partial_spearman_gc3"] for field in field_names
            },
            "sense_amino_acid_residual_spearman": {
                field: sense_reports[field]["aa_residual_spearman"] for field in field_names
            },
        },
        parry_weight_summary={
            "nonzero_codons": sum(1 for row in rows if weights[str(row["q6_label"])] > 0.0),
            "zero_codons": sum(1 for row in rows if weights[str(row["q6_label"])] == 0.0),
            "min": min(weights.values()),
            "max": max(weights.values()),
            "sum": sum(weights.values()),
            "all_64_weights_defined": True,
        },
        biological_axis_availability={
            "axis_defined_codons": {
                field: sum(1 for row in rows if row.get(field) is not None)
                for field in field_names
            },
            "missing_axis_codons": {
                field: [str(row["codon"]) for row in rows if row.get(field) is None]
                for field in field_names
            },
        },
        nulls=nulls,
        checks=checks,
        verdict_reason=verdict_reason,
        note=VENDOR_NOTE
        + " The tested alignment is label-free after fixing the shared Q6 encoding: "
        + "the primary score is centered cosine between Parry weights and d_perp on sense codons; "
        + "the nulls randomize codon/Q6 labels or Q6 graph automorphisms without amino-acid relabeling. "
        + "Parry weights are defined for all 64 Q6 vertices; the supplied biological loading axes are undefined "
        + "on the three stop codons, so axis correlations use the 61 codons with biological axis values.",
    )


if __name__ == "__main__":
    main()

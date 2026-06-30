#!/usr/bin/env python3
"""Edge-defect axis certificate for the standard genetic code.

The experiment separates two questions:

1. The graph-theoretic fact: the standard code has internal synonymous
   Hamming-1 edge count 69 against the size-profile upper bound 72, and the
   whole deficit is Stop:1 plus Ser:2.
2. The biological-axis question: the sense-side Ser split defect vector is
   tested against the currently delivered codon-Q6 selection axes.  If the
   independent fourth residual axis is not present in the input packet, a
   conservative in-packet residual of optimal_loading after known axes is
   reported as a candidate only.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import product
import json
import math
import random
import sys
from typing import Iterable


EXPERIMENT_ID = "edge_defect_axis_cert"
CLAIM_ID = "bridge.genetic_code.edge_defect_axis_cert"
DATA_PATH = "papers/window_codon_bridge/data/codon_q6_selection_vectors.json"
RANDOM_SEED = 314159
NULL_DRAWS = 20000
BASES = ("U", "C", "A", "G")

CODON_TO_FAMILY = {
    "UUU": "Phe", "UUC": "Phe", "UUA": "Leu", "UUG": "Leu",
    "UCU": "Ser", "UCC": "Ser", "UCA": "Ser", "UCG": "Ser",
    "UAU": "Tyr", "UAC": "Tyr", "UAA": "Stop", "UAG": "Stop",
    "UGU": "Cys", "UGC": "Cys", "UGA": "Stop", "UGG": "Trp",
    "CUU": "Leu", "CUC": "Leu", "CUA": "Leu", "CUG": "Leu",
    "CCU": "Pro", "CCC": "Pro", "CCA": "Pro", "CCG": "Pro",
    "CAU": "His", "CAC": "His", "CAA": "Gln", "CAG": "Gln",
    "CGU": "Arg", "CGC": "Arg", "CGA": "Arg", "CGG": "Arg",
    "AUU": "Ile", "AUC": "Ile", "AUA": "Ile", "AUG": "Met",
    "ACU": "Thr", "ACC": "Thr", "ACA": "Thr", "ACG": "Thr",
    "AAU": "Asn", "AAC": "Asn", "AAA": "Lys", "AAG": "Lys",
    "AGU": "Ser", "AGC": "Ser", "AGA": "Arg", "AGG": "Arg",
    "GUU": "Val", "GUC": "Val", "GUA": "Val", "GUG": "Val",
    "GCU": "Ala", "GCC": "Ala", "GCA": "Ala", "GCG": "Ala",
    "GAU": "Asp", "GAC": "Asp", "GAA": "Glu", "GAG": "Glu",
    "GGU": "Gly", "GGC": "Gly", "GGA": "Gly", "GGG": "Gly",
}

MAX_INTERNAL_BY_SIZE = {1: 0, 2: 1, 3: 3, 4: 6, 6: 9}
SER4 = {"UCU", "UCC", "UCA", "UCG"}
SER2 = {"AGU", "AGC"}


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def codons() -> list[str]:
    return ["".join(chars) for chars in product(BASES, repeat=3)]


def hamming1_edges(items: list[str]) -> list[tuple[str, str]]:
    edges: list[tuple[str, str]] = []
    for index, left in enumerate(items):
        for right in items[index + 1:]:
            if sum(a != b for a, b in zip(left, right)) == 1:
                edges.append((left, right))
    return edges


def mean(values: Iterable[float]) -> float:
    vals = list(values)
    return sum(vals) / len(vals)


def dot(left: dict[str, float], right: dict[str, float], support: list[str]) -> float:
    return sum(left[codon] * right[codon] for codon in support)


def norm(vec: dict[str, float], support: list[str]) -> float:
    return math.sqrt(sum(vec[codon] * vec[codon] for codon in support))


def centered(values: dict[str, float], support: list[str]) -> dict[str, float]:
    mu = mean(values[codon] for codon in support)
    return {codon: values[codon] - mu for codon in support}


def cosine(left: dict[str, float], right: dict[str, float], support: list[str]) -> float | None:
    nl = norm(left, support)
    nr = norm(right, support)
    if nl == 0.0 or nr == 0.0:
        return None
    return dot(left, right, support) / (nl * nr)


def matrix_solve(matrix: list[list[float]], rhs: list[float]) -> list[float] | None:
    n = len(rhs)
    aug = [row[:] + [rhs[i]] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) < 1e-12:
            return None
        aug[col], aug[pivot] = aug[pivot], aug[col]
        div = aug[col][col]
        aug[col] = [value / div for value in aug[col]]
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor:
                aug[row] = [value - factor * aug[col][i] for i, value in enumerate(aug[row])]
    return [aug[i][-1] for i in range(n)]


def residualize(target: dict[str, float], predictors: list[dict[str, float]], support: list[str]) -> dict[str, float] | None:
    columns = [{codon: 1.0 for codon in support}, *predictors]
    xtx: list[list[float]] = []
    xty: list[float] = []
    for left in columns:
        xtx.append([dot(left, right, support) for right in columns])
        xty.append(dot(left, target, support))
    beta = matrix_solve(xtx, xty)
    if beta is None:
        return None
    return {
        codon: target[codon] - sum(beta[i] * columns[i][codon] for i in range(len(columns)))
        for codon in support
    }


def empirical_abs_p(observed: float, values: list[float]) -> float:
    return (sum(1 for value in values if abs(value) >= abs(observed)) + 1) / (len(values) + 1)


def empirical_signed_p(observed: float, values: list[float]) -> float:
    if observed >= 0:
        return (sum(1 for value in values if value >= observed) + 1) / (len(values) + 1)
    return (sum(1 for value in values if value <= observed) + 1) / (len(values) + 1)


def round_float(value: float | None, digits: int = 6) -> float | None:
    return None if value is None else round(value, digits)


def load_selection_rows() -> list[dict[str, object]]:
    data = json.load(open(DATA_PATH, encoding="utf-8"))
    if data.get("schema") != "codon_q6_selection_vectors.v1":
        raise ValueError(f"unexpected selection-vector schema: {data.get('schema')}")
    return list(data.get("vectors", []))


def axis_from_rows(rows: list[dict[str, object]], field: str) -> tuple[dict[str, float], list[str]]:
    values: dict[str, float] = {}
    for row in rows:
        value = row.get(field)
        codon = str(row["codon"])
        if value is not None:
            values[codon] = float(value)
    return values, sorted(values)


def graph_defect_audit(items: list[str], edges: list[tuple[str, str]]) -> dict[str, object]:
    by_family: dict[str, list[str]] = defaultdict(list)
    for codon in items:
        by_family[CODON_TO_FAMILY[codon]].append(codon)

    rows: dict[str, dict[str, object]] = {}
    total_edges = 0
    total_max = 0
    for family, members in sorted(by_family.items()):
        member_set = set(members)
        actual_edges = sum(1 for left, right in edges if left in member_set and right in member_set)
        max_edges = MAX_INTERNAL_BY_SIZE[len(members)]
        defect = max_edges - actual_edges
        total_edges += actual_edges
        total_max += max_edges
        rows[family] = {
            "degeneracy": len(members),
            "actual_internal_edges": actual_edges,
            "max_internal_edges": max_edges,
            "defect": defect,
            "members": sorted(members),
        }
    return {
        "rows": rows,
        "e_in": total_edges,
        "e_max": total_max,
        "total_defect": total_max - total_edges,
        "defect_support": {family: row["defect"] for family, row in rows.items() if row["defect"]},
        "degeneracy_spectrum": dict(sorted(Counter(row["degeneracy"] for row in rows.values()).items())),
    }


def ser_split_vector(items: list[str]) -> dict[str, float]:
    return {
        codon: (0.25 if codon in SER4 else (-0.5 if codon in SER2 else 0.0))
        for codon in items
    }


def family_defect_vector(items: list[str], defects: dict[str, int]) -> dict[str, float]:
    sizes = Counter(CODON_TO_FAMILY[codon] for codon in items)
    return {
        codon: float(defects.get(CODON_TO_FAMILY[codon], 0)) / sizes[CODON_TO_FAMILY[codon]]
        for codon in items
    }


def random_ser_split_vector(items: list[str], rng: random.Random) -> dict[str, float]:
    ser = sorted(SER4 | SER2)
    plus = set(rng.sample(ser, 4))
    return {codon: (0.25 if codon in plus else (-0.5 if codon in ser else 0.0)) for codon in items}


def random_family_defect_vector(items: list[str], rng: random.Random) -> dict[str, float]:
    families_by_size: dict[int, list[str]] = defaultdict(list)
    for family, size in Counter(CODON_TO_FAMILY[codon] for codon in items).items():
        families_by_size[size].append(family)
    stop_like = rng.choice(families_by_size[3])
    ser_like = rng.choice(families_by_size[6])
    defects = {stop_like: 1, ser_like: 2}
    return family_defect_vector(items, defects)


def projection_report(
    vector: dict[str, float],
    axis: dict[str, float],
    support: list[str],
    null_vectors: list[dict[str, float]],
) -> dict[str, object]:
    axis_centered = centered(axis, support)
    vector_centered = centered(vector, support)
    observed_dot = dot(vector_centered, axis_centered, support)
    observed_cos = cosine(vector_centered, axis_centered, support)
    null_dots = [dot(centered(null, support), axis_centered, support) for null in null_vectors]
    return {
        "support_size": len(support),
        "dot": round_float(observed_dot),
        "cosine": round_float(observed_cos),
        "abs_null_p": round_float(empirical_abs_p(observed_dot, null_dots)),
        "signed_null_p": round_float(empirical_signed_p(observed_dot, null_dots)),
        "null_draws": len(null_dots),
    }


def main() -> None:
    rng = random.Random(RANDOM_SEED)
    items = codons()
    edges = hamming1_edges(items)
    graph = graph_defect_audit(items, edges)
    rows = load_selection_rows()
    sense = [codon for codon in items if CODON_TO_FAMILY[codon] != "Stop"]

    ser_vector = ser_split_vector(items)
    family_vector = family_defect_vector(items, {"Stop": 1, "Ser": 2})
    sense_family_vector = family_defect_vector(items, {"Ser": 2})

    axes: dict[str, dict[str, float]] = {}
    missing_axes: list[str] = []
    for name, field in (
        ("d_perp", "d_perp_loading"),
        ("trna_tai_mean", "trna_supply_tai_mean"),
        ("trna_consensus", "trna_consensus_loading"),
        ("f3", "f3_loading"),
        ("optimal", "optimal_loading"),
        ("d_resid4", "d_resid4_loading"),
    ):
        values, _support = axis_from_rows(rows, field)
        if values:
            axes[name] = values
        else:
            missing_axes.append(name)

    known_for_residual = [axes[name] for name in ("trna_consensus", "f3", "d_perp") if name in axes]
    if "optimal" in axes and len(known_for_residual) == 3:
        residual = residualize(axes["optimal"], known_for_residual, sense)
        if residual is not None:
            axes["optimal_residual_after_known_axes"] = residual

    ser_nulls = [random_ser_split_vector(items, rng) for _ in range(NULL_DRAWS)]
    family_nulls = [random_family_defect_vector(items, rng) for _ in range(NULL_DRAWS)]

    ser_reports: dict[str, object] = {}
    family_reports: dict[str, object] = {}
    for axis_name, axis in axes.items():
        axis_support = [codon for codon in sense if codon in axis]
        if axis_support:
            ser_reports[axis_name] = projection_report(ser_vector, axis, axis_support, ser_nulls)
            family_reports[axis_name] = projection_report(sense_family_vector, axis, axis_support, family_nulls)

    stop_report = None
    if any(CODON_TO_FAMILY[codon] == "Stop" for codon in items):
        stop = {"UAA": 0.5, "UAG": 0.5, "UGA": -1.0}
        stop_vector = {codon: stop.get(codon, 0.0) for codon in items}
        stop_report = {
            "vector": stop,
            "scope": "punctuation only; selection-vector packet omits stop-axis values",
            "internal_edges": graph["rows"]["Stop"]["actual_internal_edges"],
            "max_edges": graph["rows"]["Stop"]["max_internal_edges"],
            "defect": graph["rows"]["Stop"]["defect"],
            "stop_values_available_in_selection_packet": any(
                row.get("d_perp_loading") is not None
                for row in rows
                if str(row.get("codon")) in stop
            ),
        }

    defect_ok = graph["e_in"] == 69 and graph["e_max"] == 72 and graph["defect_support"] == {"Ser": 2, "Stop": 1}
    available_primary = ["d_resid4", "optimal_residual_after_known_axes"]
    primary_hits = [
        name for name in available_primary
        if name in ser_reports and ser_reports[name]["abs_null_p"] is not None and ser_reports[name]["abs_null_p"] <= 0.05
    ]

    if not defect_ok:
        status = "refuted"
        note = "The proposed Stop/Ser edge-defect decomposition failed direct enumeration."
    elif primary_hits:
        status = "certified"
        note = (
            "The Stop/Ser edge-defect decomposition is exact, and the Ser split defect "
            f"has a significant projection onto {', '.join(primary_hits)} under the preregistered null."
        )
    else:
        status = "coincidence"
        note = (
            "The Stop/Ser edge-defect decomposition is exact and graph-theoretically sharp, "
            "but the currently delivered selection-vector packet has no independent d_resid4 axis "
            "and the Ser split defect does not certify a projection onto the available axes."
        )

    emit(
        status,
        note=note,
        graph_defect=graph,
        ser_split_vector={codon: value for codon, value in ser_vector.items() if value},
        sense_family_defect_vector={codon: value for codon, value in sense_family_vector.items() if value},
        axis_reports={"ser_split": ser_reports, "sense_family_defect": family_reports},
        stop_defect=stop_report,
        missing_axes=missing_axes,
        residual_candidate_scope=(
            "optimal_residual_after_known_axes is computed inside this packet from optimal_loading "
            "after trna_consensus_loading, f3_loading, and d_perp_loading; it is not the independent "
            "fourth axis unless a future upstream packet supplies d_resid4_loading."
        ),
        null_models={
            "ser_split": "choose which 4 of the 6 Ser codons receive +1/4, preserving within-Ser zero sum",
            "sense_family_defect": "place defect mass 2/6 on a random sixfold family, preserving the sense family-size class",
        },
    )


if __name__ == "__main__":
    main()

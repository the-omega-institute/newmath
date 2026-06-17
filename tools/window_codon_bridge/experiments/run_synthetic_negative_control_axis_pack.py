#!/usr/bin/env python3
"""Synthetic negative-control audit for the codon projection harness."""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import combinations
import json
import math
import random
import sys
from pathlib import Path
from typing import Iterable


EXPERIMENT_ID = "synthetic_negative_control_axis_pack"
CLAIM_ID = "bridge.genetic_code.synthetic.negative.control.axis.pack"
DATA_PATH = Path("papers/window_codon_bridge/data/codon_q6_selection_vectors.json")
RANDOM_SEED = 282983
QR_TOL = 1e-10
ZERO_TOL = 1e-12
R2_REJECTION_THRESHOLD = 0.05
BASES = ("U", "C", "A", "G")
SER4 = {"UCU", "UCC", "UCA", "UCG"}
SER2 = {"AGU", "AGC"}
SIXFOLD = {
    "Ser": ("UCU", "UCC", "UCA", "UCG", "AGU", "AGC"),
    "Leu": ("UUA", "UUG", "CUU", "CUC", "CUA", "CUG"),
    "Arg": ("CGU", "CGC", "CGA", "CGG", "AGA", "AGG"),
}
SELECTION_FIELDS = (
    "d_perp_loading",
    "f3_loading",
    "optimal_loading",
    "trna_consensus_loading",
    "trna_supply_tai_centered_loading",
    "trna_supply_tai_mean",
)


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def norm(values: list[float]) -> float:
    return math.sqrt(dot(values, values))


def mean(values: Iterable[float]) -> float:
    vals = list(values)
    return sum(vals) / len(vals)


def centered(values: list[float]) -> list[float]:
    mu = mean(values)
    return [value - mu for value in values]


def zscore(values: list[float]) -> list[float]:
    vals = centered(values)
    nrm = norm(vals)
    if nrm <= ZERO_TOL:
        return vals
    return [value / nrm for value in vals]


def rounded(value: float | None, digits: int = 8) -> float | None:
    return None if value is None else round(float(value), digits)


def empirical_abs_p(observed: float, null_values: list[float]) -> float | None:
    if not null_values:
        return None
    return sum(1 for value in null_values if abs(value) >= abs(observed) - 1e-15) / len(null_values)


def orthonormal_basis(columns: list[list[float]], tol: float = QR_TOL) -> tuple[list[list[float]], list[int]]:
    basis: list[list[float]] = []
    kept_indices: list[int] = []
    for index, column in enumerate(columns):
        residual = column[:]
        for vector in basis:
            coeff = dot(residual, vector)
            residual = [value - coeff * vector[row] for row, value in enumerate(residual)]
        nrm = norm(residual)
        if nrm > tol:
            basis.append([value / nrm for value in residual])
            kept_indices.append(index)
    return basis, kept_indices


def residualize_with_basis(target: list[float], basis: list[list[float]]) -> list[float]:
    residual = target[:]
    for vector in basis:
        coeff = dot(residual, vector)
        residual = [value - coeff * vector[row] for row, value in enumerate(residual)]
    return residual


def residual_unit(target: list[float], basis: list[list[float]]) -> tuple[list[float] | None, float]:
    residual = residualize_with_basis(target, basis)
    nrm = norm(residual)
    if nrm <= ZERO_TOL:
        return None, nrm
    return [value / nrm for value in residual], nrm


def one_hot(values: list[str], omit_last: bool = True) -> list[tuple[str, list[float]]]:
    labels = sorted(set(values))
    if omit_last and labels:
        labels = labels[:-1]
    return [(label, [1.0 if value == label else 0.0 for value in values]) for label in labels]


def load_rows() -> list[dict[str, object]]:
    data = json.loads(DATA_PATH.read_text(encoding="utf-8"))
    if data.get("schema") != "codon_q6_selection_vectors.v1":
        raise ValueError(f"unexpected codon packet schema: {data.get('schema')}")
    rows = [dict(row) for row in data.get("vectors", []) if row.get("is_sense") is True]
    if len(rows) != 61:
        raise ValueError(f"expected 61 sense codons, found {len(rows)}")
    return rows


def codon_features(codon: str) -> dict[str, float | str]:
    return {
        "gc1": 1.0 if codon[0] in "GC" else 0.0,
        "gc2": 1.0 if codon[1] in "GC" else 0.0,
        "gc3": 1.0 if codon[2] in "GC" else 0.0,
        "gc_total": float(sum(1 for base in codon if base in "GC")),
        "gc_fraction": sum(1 for base in codon if base in "GC") / 3.0,
        "cpg": 1.0 if "CG" in codon else 0.0,
        "upa": 1.0 if "UA" in codon else 0.0,
        "purine_count": float(sum(1 for base in codon if base in "AG")),
        "pyrimidine_count": float(sum(1 for base in codon if base in "UC")),
        "wobble_base": codon[2],
        "wobble_gc": 1.0 if codon[2] in "GC" else 0.0,
        "first_two": codon[:2],
    }


def degeneracy_by_aa(rows: list[dict[str, object]]) -> dict[str, int]:
    counts = Counter(str(row["amino_acid"]) for row in rows)
    return {aa: int(count) for aa, count in counts.items()}


def build_control_blocks(rows: list[dict[str, object]]) -> tuple[dict[str, list[tuple[str, list[float]]]], dict[str, object]]:
    codons = [str(row["codon"]) for row in rows]
    amino_acids = [str(row["amino_acid"]) for row in rows]
    aa_degeneracy = degeneracy_by_aa(rows)
    features = [codon_features(codon) for codon in codons]

    blocks: dict[str, list[tuple[str, list[float]]]] = {
        "intercept": [("intercept", [1.0 for _ in rows])],
        "amino_acid": [(f"aa_{label}", column) for label, column in one_hot(amino_acids)],
        "selection_packet": [],
        "gc": [
            ("gc1", zscore([float(feature["gc1"]) for feature in features])),
            ("gc2", zscore([float(feature["gc2"]) for feature in features])),
            ("gc3", zscore([float(feature["gc3"]) for feature in features])),
            ("gc_total", zscore([float(feature["gc_fraction"]) for feature in features])),
            ("cpg", zscore([float(feature["cpg"]) for feature in features])),
            ("upa", zscore([float(feature["upa"]) for feature in features])),
        ],
        "wobble": [(f"wobble_{label}", column) for label, column in one_hot([str(codon[2]) for codon in codons])],
        "degeneracy": [("degeneracy", zscore([float(aa_degeneracy[aa]) for aa in amino_acids]))],
        "codon_pair_like": [],
        "stability_dwell_like": [],
    }
    for field in SELECTION_FIELDS:
        values = [row.get(field) for row in rows]
        if all(value is not None for value in values):
            blocks["selection_packet"].append((field, zscore([float(value) for value in values])))

    blocks["codon_pair_like"] = [
        ("first_two_gc", zscore([float(codon[0] in "GC") + float(codon[1] in "GC") for codon in codons])),
        ("same_first_pair", zscore([1.0 if codon[0] == codon[1] else 0.0 for codon in codons])),
        ("same_second_pair", zscore([1.0 if codon[1] == codon[2] else 0.0 for codon in codons])),
        ("purine_count", zscore([float(feature["purine_count"]) for feature in features])),
        ("pyrimidine_count", zscore([float(feature["pyrimidine_count"]) for feature in features])),
    ]
    blocks["stability_dwell_like"] = [
        (
            "mRNA_stability_proxy",
            zscore([
                0.9 * float(feature["gc_fraction"]) - 0.45 * float(feature["upa"]) + 0.25 * float(feature["cpg"])
                for feature in features
            ]),
        ),
        (
            "ribosome_dwell_proxy",
            zscore([
                0.55 * float(feature["wobble_gc"]) + 0.25 * float(feature["purine_count"]) + aa_degeneracy[aa] / 6.0
                for feature, aa in zip(features, amino_acids)
            ]),
        ),
    ]
    metadata = {
        "forbidden_blocks": sorted(blocks),
        "selection_fields_present": [name for name, _column in blocks["selection_packet"]],
        "uses_q6_labels_or_bits": False,
        "uses_stop_or_ser_edge_defect_support_in_raw_axis": False,
    }
    return blocks, metadata


def flatten_blocks(blocks: dict[str, list[tuple[str, list[float]]]]) -> tuple[list[str], list[list[float]], dict[str, list[str]]]:
    names: list[str] = []
    columns: list[list[float]] = []
    block_names: dict[str, list[str]] = {}
    for block, entries in blocks.items():
        block_names[block] = []
        for name, column in entries:
            names.append(f"{block}:{name}")
            columns.append(column)
            block_names[block].append(f"{block}:{name}")
    return names, columns, block_names


def rank_pruned_basis(names: list[str], columns: list[list[float]]) -> tuple[list[str], list[str], list[list[float]]]:
    basis, kept_indices = orthonormal_basis(columns)
    kept_set = set(kept_indices)
    kept = [names[index] for index in kept_indices]
    dropped = [name for index, name in enumerate(names) if index not in kept_set]
    return kept, dropped, basis


def block_basis(
    block_name: str,
    blocks: dict[str, list[tuple[str, list[float]]]],
) -> tuple[list[str], list[list[float]]]:
    entries = blocks.get(block_name, [])
    names = [f"{block_name}:{name}" for name, _column in entries]
    columns = [column for _name, column in entries]
    _kept, _dropped, basis = rank_pruned_basis(names, columns)
    return names, basis


def ser_split_vector(codons: list[str]) -> list[float]:
    scale = math.sqrt(12.0)
    return [1.0 / scale if codon in SER4 else (-2.0 / scale if codon in SER2 else 0.0) for codon in codons]


def contrast_vector(codons: list[str], plus: set[str], minus: set[str]) -> list[float]:
    plus_weight = 1.0 / math.sqrt(12.0)
    minus_weight = -2.0 / math.sqrt(12.0)
    return [plus_weight if codon in plus else (minus_weight if codon in minus else 0.0) for codon in codons]


def within_ser_null(codons: list[str], basis: list[list[float]], axis_unit: list[float]) -> list[float]:
    ser_codons = sorted(SER4 | SER2)
    values: list[float] = []
    for plus_tuple in combinations(ser_codons, 4):
        plus = set(plus_tuple)
        minus = set(ser_codons) - plus
        unit, _nrm = residual_unit(contrast_vector(codons, plus, minus), basis)
        if unit is not None:
            values.append(dot(axis_unit, unit))
    return values


def sixfold_family_null(codons: list[str], basis: list[list[float]], axis_unit: list[float]) -> list[float]:
    values: list[float] = []
    for family_codons in SIXFOLD.values():
        family = sorted(family_codons)
        for plus_tuple in combinations(family, 4):
            plus = set(plus_tuple)
            minus = set(family) - plus
            unit, _nrm = residual_unit(contrast_vector(codons, plus, minus), basis)
            if unit is not None:
                values.append(dot(axis_unit, unit))
    return values


def matched_key(codon: str, aa_size: int) -> tuple[int, int, int, int, str, int]:
    feature = codon_features(codon)
    return (
        int(feature["gc1"]),
        int(feature["gc2"]),
        int(feature["gc3"]),
        int(feature["gc_total"]),
        str(feature["wobble_base"]),
        aa_size,
    )


def matched_supports(codons: list[str], aa_by_codon: dict[str, str], aa_sizes: dict[str, int]) -> list[tuple[set[str], set[str]]]:
    target = Counter(matched_key(codon, aa_sizes[aa_by_codon[codon]]) for codon in sorted(SER4 | SER2))
    buckets: dict[tuple[int, int, int, int, str, int], list[str]] = defaultdict(list)
    for codon in codons:
        buckets[matched_key(codon, aa_sizes[aa_by_codon[codon]])].append(codon)
    if any(len(buckets[key]) < count for key, count in target.items()):
        return []
    groups: list[list[tuple[str, ...]]] = []
    for key, count in sorted(target.items()):
        groups.append(list(combinations(sorted(buckets[key]), count)))

    supports: list[tuple[str, ...]] = [()]
    for choices in groups:
        next_supports: list[tuple[str, ...]] = []
        for prefix in supports:
            used = set(prefix)
            for choice in choices:
                if used.isdisjoint(choice):
                    next_supports.append(tuple(sorted((*prefix, *choice))))
        supports = next_supports

    pairs: list[tuple[set[str], set[str]]] = []
    seen: set[tuple[tuple[str, ...], tuple[str, ...]]] = set()
    for support in supports:
        for plus_tuple in combinations(support, 4):
            plus = set(plus_tuple)
            minus = set(support) - plus
            key = (tuple(sorted(plus)), tuple(sorted(minus)))
            if key not in seen:
                pairs.append((plus, minus))
                seen.add(key)
    return pairs


def global_matched_null(
    codons: list[str],
    basis: list[list[float]],
    axis_unit: list[float],
    aa_by_codon: dict[str, str],
    aa_sizes: dict[str, int],
) -> list[float]:
    values: list[float] = []
    for plus, minus in matched_supports(codons, aa_by_codon, aa_sizes):
        unit, _nrm = residual_unit(contrast_vector(codons, plus, minus), basis)
        if unit is not None:
            values.append(dot(axis_unit, unit))
    return values


def synthetic_axes(rows: list[dict[str, object]]) -> dict[str, dict[str, object]]:
    codons = [str(row["codon"]) for row in rows]
    features = [codon_features(codon) for codon in codons]
    aa_sizes = degeneracy_by_aa(rows)
    rng = random.Random(RANDOM_SEED)
    random_sign = [1.0 if rng.random() >= 0.5 else -1.0 for _ in codons]
    return {
        "seeded_gaussian": {
            "factory": "seeded Gaussian values in locked sense-codon order",
            "values": [rng.gauss(0.0, 1.0) for _ in codons],
        },
        "seeded_rademacher": {
            "factory": "seeded label-free sign vector in locked sense-codon order",
            "values": random_sign,
        },
        "gc_only": {
            "factory": "GC fraction from codon spelling only",
            "values": [float(feature["gc_fraction"]) for feature in features],
        },
        "wobble_only": {
            "factory": "third-position GC indicator from codon spelling only",
            "values": [float(feature["wobble_gc"]) for feature in features],
        },
        "tai_like": {
            "factory": "deterministic proxy using amino-acid degeneracy, GC3, and codon spelling",
            "values": [
                (aa_sizes[str(row["amino_acid"])] / 6.0) + 0.4 * float(feature["wobble_gc"]) - 0.2 * float(feature["upa"])
                for row, feature in zip(rows, features)
            ],
        },
        "codon_pair_like": {
            "factory": "deterministic dinucleotide proxy from adjacent bases inside the codon",
            "values": [
                0.6 * float(feature["cpg"]) - 0.35 * float(feature["upa"]) + 0.2 * float(codon[0] == codon[1])
                for codon, feature in zip(codons, features)
            ],
        },
        "stability_dwell_like": {
            "factory": "deterministic chemistry proxy from GC, wobble, purine count, CpG, and UpA",
            "values": [
                0.5 * float(feature["gc_fraction"])
                + 0.2 * float(feature["wobble_gc"])
                + 0.1 * float(feature["purine_count"])
                + 0.25 * float(feature["cpg"])
                - 0.3 * float(feature["upa"])
                for feature in features
            ],
        },
    }


def projection_r2(target: list[float], basis: list[list[float]]) -> float:
    target_norm = norm(target)
    if target_norm <= ZERO_TOL:
        return 0.0
    residual = residualize_with_basis(target, basis)
    return max(0.0, min(1.0, 1.0 - (norm(residual) ** 2) / (target_norm ** 2)))


def audit_axis(
    name: str,
    spec: dict[str, object],
    codons: list[str],
    rows: list[dict[str, object]],
    controls_basis: list[list[float]],
    blocks: dict[str, list[tuple[str, list[float]]]],
) -> dict[str, object]:
    raw_values = [float(value) for value in spec["values"]]  # type: ignore[index]
    finite_raw = all(math.isfinite(value) for value in raw_values)
    axis_unit, axis_residual_norm = residual_unit(zscore(raw_values), controls_basis)
    ser_unit, ser_residual_norm = residual_unit(ser_split_vector(codons), controls_basis)
    forbidden_r2: dict[str, float] = {}
    if axis_unit is not None:
        for block_name in sorted(blocks):
            if block_name == "intercept":
                continue
            _names, local_basis = block_basis(block_name, blocks)
            forbidden_r2[block_name] = projection_r2(axis_unit, local_basis)

    report: dict[str, object] = {
        "axis_id": name,
        "factory": spec["factory"],
        "finite_raw_values": finite_raw,
        "raw_source_forbidden_label_free": True,
        "residual_norm": rounded(axis_residual_norm, 12),
        "ser_residual_norm": rounded(ser_residual_norm, 12),
        "forbidden_block_max_r2": rounded(max(forbidden_r2.values()) if forbidden_r2 else None),
        "forbidden_block_r2": {key: rounded(value) for key, value in forbidden_r2.items()},
    }
    if not finite_raw:
        report["audit_status"] = "invalid_raw"
        return report
    if axis_unit is None:
        report["audit_status"] = "exact_null_under_forbidden_controls"
        return report
    if ser_unit is None:
        report["audit_status"] = "ser_split_not_testable"
        return report

    observed = dot(axis_unit, ser_unit)
    aa_by_codon = {str(row["codon"]): str(row["amino_acid"]) for row in rows}
    aa_sizes = degeneracy_by_aa(rows)
    within = within_ser_null(codons, controls_basis, axis_unit)
    sixfold = sixfold_family_null(codons, controls_basis, axis_unit)
    matched = global_matched_null(codons, controls_basis, axis_unit, aa_by_codon, aa_sizes)
    report.update(
        {
            "audit_status": "tested_residual",
            "rho": rounded(observed),
            "abs_rho": rounded(abs(observed)),
            "within_ser_exact_p": rounded(empirical_abs_p(observed, within)),
            "within_ser_null_size": len(within),
            "sixfold_family_exact_p": rounded(empirical_abs_p(observed, sixfold)),
            "sixfold_family_null_size": len(sixfold),
            "global_matched_exact_p": rounded(empirical_abs_p(observed, matched)),
            "global_matched_null_size": len(matched),
            "forbidden_predictable": any(value >= R2_REJECTION_THRESHOLD for value in forbidden_r2.values()),
        }
    )
    return report


def self_check_payload(
    rows: list[dict[str, object]],
    kept_controls: list[str],
    dropped_controls: list[str],
    reports: dict[str, dict[str, object]],
    control_metadata: dict[str, object],
) -> tuple[bool, bool, list[str]]:
    checks: list[str] = []
    codons = [str(row["codon"]) for row in rows]
    if len(codons) == 61 and len(set(codons)) == 61:
        checks.append("sense_codon_order_has_61_unique_rows")
    else:
        checks.append("fail:sense_codon_order")
    if all(codon not in {"UAA", "UAG", "UGA"} for codon in codons):
        checks.append("sense_only_no_stop_codons")
    else:
        checks.append("fail:stop_codon_present")
    if set(SER4 | SER2).issubset(codons):
        checks.append("ser_six_codon_support_present_for_audit_only")
    else:
        checks.append("fail:ser_support_missing")
    if kept_controls and len(kept_controls) + len(dropped_controls) > len(kept_controls):
        checks.append("control_matrix_rank_pruned")
    else:
        checks.append("fail:control_matrix_pruning")
    if control_metadata.get("uses_q6_labels_or_bits") is False:
        checks.append("raw_factories_do_not_use_q6_labels_or_bits")
    else:
        checks.append("fail:q6_label_or_bits_used")
    if control_metadata.get("uses_stop_or_ser_edge_defect_support_in_raw_axis") is False:
        checks.append("raw_factories_do_not_use_stop_or_ser_edge_defect_support")
    else:
        checks.append("fail:edge_defect_support_used_in_raw_factory")
    if all(report.get("finite_raw_values") is True for report in reports.values()):
        checks.append("all_raw_axes_finite")
    else:
        checks.append("fail:nonfinite_raw_axis")
    if any(report.get("audit_status") == "exact_null_under_forbidden_controls" for report in reports.values()):
        checks.append("forbidden_negative_controls_collapse_when_expected")
    else:
        checks.append("fail:no_forbidden_control_collapsed")
    ser_split_testable = any(report.get("audit_status") == "tested_residual" for report in reports.values())
    if ser_split_testable:
        checks.append("ser_split_projection_test_reached_for_at_least_one_residual")
    else:
        checks.append("ser_split_not_testable_after_forbidden_controls")
    if all(report.get("audit_status") != "tested_residual" or report.get("global_matched_null_size", 0) > 0 for report in reports.values()):
        checks.append("tested_residuals_have_exact_matched_null")
    else:
        checks.append("fail:matched_null_missing")
    ok = not any(item.startswith("fail:") for item in checks)
    return ok, ser_split_testable, checks


def main() -> None:
    try:
        rows = load_rows()
        codons = [str(row["codon"]) for row in rows]
        blocks, control_metadata = build_control_blocks(rows)
        control_names, control_columns, block_names = flatten_blocks(blocks)
        kept_controls, dropped_controls, controls_basis = rank_pruned_basis(control_names, control_columns)
        axes = synthetic_axes(rows)
        reports = {
            name: audit_axis(name, spec, codons, rows, controls_basis, blocks)
            for name, spec in axes.items()
        }
        self_check_ok, ser_split_testable, checks = self_check_payload(
            rows, kept_controls, dropped_controls, reports, control_metadata
        )
        forbidden_predictable = [
            name for name, report in reports.items()
            if report.get("forbidden_predictable") is True
        ]
        exact_projection_hits = [
            name for name, report in reports.items()
            if report.get("audit_status") == "tested_residual"
            and report.get("global_matched_exact_p") is not None
            and float(report["global_matched_exact_p"]) <= 0.05
        ]
        if not self_check_ok:
            emit(
                "needs_derivation",
                reason="self-check failed, so the negative-control pack cannot classify the harness",
                checks=checks,
                control_matrix={"rank": len(kept_controls), "dropped_dependent_columns": dropped_controls},
                reports=reports,
            )
        if not ser_split_testable:
            emit(
                "needs_derivation",
                reason=(
                    "the forbidden-control matrix makes the SerSplit contrast non-testable, "
                    "so this negative-control pack cannot audit projection selectivity"
                ),
                checks=checks,
                codon_order_schema="codon_q6_selection_vectors.v1 sense-only locked order",
                random_seed=RANDOM_SEED,
                control_matrix={
                    "rows": len(codons),
                    "rank": len(kept_controls),
                    "kept_control_names": kept_controls,
                    "dropped_dependent_control_names": dropped_controls,
                    "block_names": block_names,
                    **control_metadata,
                },
                reports=reports,
            )
        note = (
            "Synthetic negative controls are deterministic and label-free. Any numerical SerSplit "
            "projection is classified as coincidence, not certification, because no biological or "
            "graph-theoretic forcing construction is present."
        )
        emit(
            "coincidence",
            note=note,
            checks=checks,
            codon_order_schema="codon_q6_selection_vectors.v1 sense-only locked order",
            random_seed=RANDOM_SEED,
            control_matrix={
                "rows": len(codons),
                "rank": len(kept_controls),
                "kept_control_names": kept_controls,
                "dropped_dependent_control_names": dropped_controls,
                "block_names": block_names,
                **control_metadata,
            },
            reports=reports,
            exact_projection_hits=exact_projection_hits,
            forbidden_predictable_residuals=forbidden_predictable,
            certification_rule=(
                "This experiment cannot emit certified: it is a synthetic negative-control pack, "
                "and number matches alone remain coincidence under the route contract."
            ),
        )
    except Exception as exc:
        emit(
            "needs_derivation",
            reason=f"experiment raised {type(exc).__name__}: {exc}",
            checks=["fail:exception"],
        )


if __name__ == "__main__":
    main()

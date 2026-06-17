#!/usr/bin/env python3
"""Exact Ser-split edge-defect non-estimability certificate."""
from __future__ import annotations

from fractions import Fraction
import json
import math
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.window_codon_bridge.experiments.run_synthetic_negative_control_axis_pack import (  # noqa: E402
    SER2,
    SER4,
    build_control_blocks,
    degeneracy_by_aa,
    flatten_blocks,
    load_rows,
    norm,
    one_hot,
    rank_pruned_basis,
    residualize_with_basis,
    ser_split_vector,
)


EXPERIMENT_ID = "sersplit_edge_defect_nonestimability_certificate"
CLAIM_ID = "bridge.genetic_code.sersplit.edge_defect.nonestimability.certificate"
ZERO_TOL = 1e-12
REGISTERED_EQUIVALENCE_TOL = 1e-9
WITNESS_NAMES = (
    "intercept:intercept",
    "amino_acid:aa_A",
    "amino_acid:aa_D",
    "amino_acid:aa_E",
    "amino_acid:aa_G",
    "amino_acid:aa_H",
    "amino_acid:aa_K",
    "amino_acid:aa_N",
    "amino_acid:aa_P",
    "amino_acid:aa_Q",
    "amino_acid:aa_R",
    "amino_acid:aa_S",
    "amino_acid:aa_V",
    "gc:gc1",
    "gc:gc3",
    "wobble:wobble_A",
    "wobble:wobble_C",
    "codon_pair_like:same_first_pair",
    "codon_pair_like:purine_count",
)


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def estimability_gate(target: list[float], control_basis: list[list[float]], eps: float = 1e-12) -> dict[str, object]:
    residual = residualize_with_basis(target, control_basis)
    residual_norm = norm(residual)
    return {"residual": residual, "residual_norm": residual_norm, "testable": residual_norm > eps}


def fraction_str(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def zscore_fraction_values(values: list[Fraction]) -> list[float]:
    mean = sum(values, Fraction(0)) / len(values)
    centered = [float(value - mean) for value in values]
    nrm = math.sqrt(sum(value * value for value in centered))
    if nrm <= ZERO_TOL:
        return centered
    return [value / nrm for value in centered]


def raw_semantic_control_columns(rows: list[dict[str, object]]) -> tuple[list[str], list[list[Fraction]]]:
    codons = [str(row["codon"]) for row in rows]
    amino_acids = [str(row["amino_acid"]) for row in rows]
    aa_degeneracy = degeneracy_by_aa(rows)
    names: list[str] = []
    columns: list[list[Fraction]] = []

    def add(name: str, values: list[int] | list[Fraction]) -> None:
        names.append(name)
        columns.append([Fraction(value) for value in values])

    add("intercept:intercept", [1 for _row in rows])
    for label, column in one_hot(amino_acids):
        add(f"amino_acid:aa_{label}", [int(value) for value in column])

    add("gc:gc1", [1 if codon[0] in "GC" else 0 for codon in codons])
    add("gc:gc2", [1 if codon[1] in "GC" else 0 for codon in codons])
    add("gc:gc3", [1 if codon[2] in "GC" else 0 for codon in codons])
    add("gc:gc_total", [Fraction(sum(1 for base in codon if base in "GC"), 3) for codon in codons])
    add("gc:cpg", [1 if "CG" in codon else 0 for codon in codons])
    add("gc:upa", [1 if "UA" in codon else 0 for codon in codons])

    for label, column in one_hot([codon[2] for codon in codons]):
        add(f"wobble:wobble_{label}", [int(value) for value in column])

    add("degeneracy:degeneracy", [aa_degeneracy[aa] for aa in amino_acids])
    add(
        "codon_pair_like:first_two_gc",
        [int(codon[0] in "GC") + int(codon[1] in "GC") for codon in codons],
    )
    add("codon_pair_like:same_first_pair", [1 if codon[0] == codon[1] else 0 for codon in codons])
    add("codon_pair_like:same_second_pair", [1 if codon[1] == codon[2] else 0 for codon in codons])
    add("codon_pair_like:purine_count", [sum(1 for base in codon if base in "AG") for codon in codons])
    add("codon_pair_like:pyrimidine_count", [sum(1 for base in codon if base in "UC") for codon in codons])
    add(
        "stability_dwell_like:mRNA_stability_proxy",
        [
            Fraction(9, 10) * Fraction(sum(1 for base in codon if base in "GC"), 3)
            - Fraction(9, 20) * int("UA" in codon)
            + Fraction(1, 4) * int("CG" in codon)
            for codon in codons
        ],
    )
    add(
        "stability_dwell_like:ribosome_dwell_proxy",
        [
            Fraction(11, 20) * int(codon[2] in "GC")
            + Fraction(1, 4) * sum(1 for base in codon if base in "AG")
            + Fraction(aa_degeneracy[aa], 6)
            for codon, aa in zip(codons, amino_acids)
        ],
    )
    return names, columns


def scaled_ser_split_target(codons: list[str]) -> list[Fraction]:
    return [Fraction(1 if codon in SER4 else (-2 if codon in SER2 else 0)) for codon in codons]


def solve_fraction_system(
    names: list[str],
    columns: list[list[Fraction]],
    target: list[Fraction],
) -> tuple[dict[str, Fraction] | None, int]:
    row_count = len(target)
    col_count = len(columns)
    matrix = [[columns[col][row] for col in range(col_count)] + [target[row]] for row in range(row_count)]
    pivot_row = 0
    pivots: list[int] = []
    for col in range(col_count):
        pivot = next((row for row in range(pivot_row, row_count) if matrix[row][col] != 0), None)
        if pivot is None:
            continue
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        scale = matrix[pivot_row][col]
        matrix[pivot_row] = [value / scale for value in matrix[pivot_row]]
        for row in range(row_count):
            if row == pivot_row or matrix[row][col] == 0:
                continue
            factor = matrix[row][col]
            matrix[row] = [value - factor * base for value, base in zip(matrix[row], matrix[pivot_row])]
        pivots.append(col)
        pivot_row += 1
        if pivot_row == row_count:
            break

    for row in range(pivot_row, row_count):
        if all(matrix[row][col] == 0 for col in range(col_count)) and matrix[row][-1] != 0:
            return None, pivot_row

    solution = [Fraction(0) for _col in range(col_count)]
    for row, col in enumerate(pivots):
        solution[col] = matrix[row][-1]
    return {names[index]: value for index, value in enumerate(solution) if value != 0}, pivot_row


def exact_column_rank(columns: list[list[Fraction]]) -> int:
    if not columns:
        return 0
    row_count = len(columns[0])
    col_count = len(columns)
    matrix = [[columns[col][row] for col in range(col_count)] for row in range(row_count)]
    pivot_row = 0
    for col in range(col_count):
        pivot = next((row for row in range(pivot_row, row_count) if matrix[row][col] != 0), None)
        if pivot is None:
            continue
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        scale = matrix[pivot_row][col]
        matrix[pivot_row] = [value / scale for value in matrix[pivot_row]]
        for row in range(row_count):
            if row == pivot_row or matrix[row][col] == 0:
                continue
            factor = matrix[row][col]
            matrix[row] = [value - factor * base for value, base in zip(matrix[row], matrix[pivot_row])]
        pivot_row += 1
        if pivot_row == row_count:
            break
    return pivot_row


def exact_residual(
    target: list[Fraction],
    names: list[str],
    columns_by_name: dict[str, list[Fraction]],
    coefficients: dict[str, Fraction],
) -> list[Fraction]:
    return [
        target[row] - sum(coefficients.get(name, Fraction(0)) * columns_by_name[name][row] for name in names)
        for row in range(len(target))
    ]


def centered_span_checks(
    rows: list[dict[str, object]],
    witness_names: tuple[str, ...],
    registered_columns_by_name: dict[str, list[float]],
) -> tuple[list[str], dict[str, object], list[str]]:
    codons = [str(row["codon"]) for row in rows]
    amino_acids = [str(row["amino_acid"]) for row in rows]
    aa_degeneracy = degeneracy_by_aa(rows)
    raw_values: dict[str, list[Fraction]] = {
        "gc:gc1": [Fraction(int(codon[0] in "GC")) for codon in codons],
        "gc:gc2": [Fraction(int(codon[1] in "GC")) for codon in codons],
        "gc:gc3": [Fraction(int(codon[2] in "GC")) for codon in codons],
        "gc:gc_total": [Fraction(sum(1 for base in codon if base in "GC"), 3) for codon in codons],
        "gc:cpg": [Fraction(int("CG" in codon)) for codon in codons],
        "gc:upa": [Fraction(int("UA" in codon)) for codon in codons],
        "degeneracy:degeneracy": [Fraction(aa_degeneracy[aa]) for aa in amino_acids],
        "codon_pair_like:first_two_gc": [
            Fraction(int(codon[0] in "GC") + int(codon[1] in "GC")) for codon in codons
        ],
        "codon_pair_like:same_first_pair": [Fraction(int(codon[0] == codon[1])) for codon in codons],
        "codon_pair_like:same_second_pair": [Fraction(int(codon[1] == codon[2])) for codon in codons],
        "codon_pair_like:purine_count": [Fraction(sum(1 for base in codon if base in "AG")) for codon in codons],
        "codon_pair_like:pyrimidine_count": [Fraction(sum(1 for base in codon if base in "UC")) for codon in codons],
    }
    checks: list[str] = []
    column_deviations: dict[str, float] = {}
    drifted_columns: list[str] = []
    for name in witness_names:
        if name.startswith(("intercept:", "amino_acid:", "wobble:")):
            continue
        registered_values = registered_columns_by_name.get(name)
        if registered_values is None:
            checks.append(f"fail:{name}:registered_control_column_missing")
            drifted_columns.append(name)
            continue
        values = raw_values[name]
        mean = sum(values, Fraction(0)) / len(values)
        centered = [value - mean for value in values]
        sum_squares = sum(value * value for value in centered)
        if sum_squares <= 0:
            checks.append(f"fail:{name}:zero_centered_column")
            drifted_columns.append(name)
            continue
        local_zscore = zscore_fraction_values(values)
        max_deviation = max(abs(local - registered) for local, registered in zip(local_zscore, registered_values))
        column_deviations[name] = max_deviation
        if max_deviation <= REGISTERED_EQUIVALENCE_TOL:
            checks.append(
                f"{name}:raw_column_equals_mean_times_intercept_plus_nonzero_scale_times_registered_zscore"
            )
        else:
            checks.append(f"fail:{name}:registered_zscore_column_drift:max_abs_deviation={max_deviation:.3e}")
            drifted_columns.append(name)
    report = {
        "tolerance": REGISTERED_EQUIVALENCE_TOL,
        "max_abs_deviation": max(column_deviations.values()) if column_deviations else None,
        "columns": column_deviations,
    }
    return checks, report, drifted_columns


def within_ser_contrast_basis(codons: list[str]) -> list[tuple[str, list[Fraction]]]:
    ser_codons = sorted(SER4 | SER2)
    anchor = ser_codons[-1]
    basis: list[tuple[str, list[Fraction]]] = []
    for codon in ser_codons[:-1]:
        vector = [
            Fraction(1) if row_codon == codon else (Fraction(-1) if row_codon == anchor else Fraction(0))
            for row_codon in codons
        ]
        basis.append((f"{codon}_minus_{anchor}", vector))
    return basis


def within_ser_subspace_report(
    codons: list[str],
    exact_columns: list[list[Fraction]],
) -> dict[str, object]:
    basis = within_ser_contrast_basis(codons)
    control_rank = exact_column_rank(exact_columns)
    basis_checks: list[dict[str, object]] = []
    all_absorbed = True
    for name, vector in basis:
        rank_with_appended = exact_column_rank([*exact_columns, vector])
        absorbed = rank_with_appended == control_rank
        all_absorbed = all_absorbed and absorbed
        basis_checks.append(
            {
                "basis_vector": name,
                "absorbed": absorbed,
                "rank_with_appended": rank_with_appended,
            }
        )
    return {
        "dim": len(basis),
        "basis": [name for name, _vector in basis],
        "control_rank": control_rank,
        "all_absorbed": all_absorbed,
        "permutation_null_degenerate": all_absorbed,
        "basis_checks": basis_checks,
    }


def main() -> None:
    try:
        rows = load_rows()
        codons = [str(row["codon"]) for row in rows]
        blocks, control_metadata = build_control_blocks(rows)
        control_names, control_columns, block_names = flatten_blocks(blocks)
        registered_columns_by_name = dict(zip(control_names, control_columns))
        kept_controls, dropped_controls, control_basis = rank_pruned_basis(control_names, control_columns)
        exact_names, exact_columns = raw_semantic_control_columns(rows)
        exact_name_set = set(exact_names)
        registered_exact_names = [name for name in control_names if not name.startswith("selection_packet:")]
        checks = [
            "sense_codon_order_has_61_unique_rows"
            if len(codons) == 61 and len(set(codons)) == 61
            else "fail:sense_codon_order",
            "sense_only_no_stop_codons"
            if all(codon not in {"UAA", "UAG", "UGA"} for codon in codons)
            else "fail:stop_codon_present",
            "registered_control_basis_reused_from_synthetic_negative_control_axis_pack",
            "exact_fraction_proof_excludes_float_selection_packet_columns",
            "raw_semantic_exact_columns_match_registered_nonselection_column_names"
            if exact_names == registered_exact_names
            else "fail:raw_semantic_column_name_drift",
            "witness_columns_are_registered_forbidden_controls"
            if set(WITNESS_NAMES).issubset(set(control_names))
            else "fail:witness_column_not_registered",
            "witness_columns_are_rank_kept_in_registered_basis"
            if set(WITNESS_NAMES).issubset(set(kept_controls))
            else "fail:witness_column_not_rank_kept",
        ]
        centered_checks, registered_equivalence, drifted_columns = centered_span_checks(
            rows, WITNESS_NAMES, registered_columns_by_name
        )
        checks.extend(centered_checks)

        columns_by_name = dict(zip(exact_names, exact_columns))
        witness_columns = [columns_by_name[name] for name in WITNESS_NAMES]
        nonselection_exact_columns = [columns_by_name[name] for name in registered_exact_names]
        within_ser_subspace = within_ser_subspace_report(codons, nonselection_exact_columns)
        if within_ser_subspace["all_absorbed"] is True:
            checks.append("within_ser_contrast_subspace_fully_absorbed")
        else:
            checks.append("within_ser_contrast_subspace_not_fully_absorbed")

        if drifted_columns:
            emit(
                "needs_derivation",
                reason=(
                    "registered control value drift detected for witness column(s): "
                    f"{', '.join(drifted_columns)}"
                ),
                checks=checks,
                registered_equivalence=registered_equivalence,
                within_ser_subspace=within_ser_subspace,
                control_matrix={"rows": len(codons), "rank": len(kept_controls)},
            )

        scaled_target = scaled_ser_split_target(codons)
        solution, witness_rank = solve_fraction_system(list(WITNESS_NAMES), witness_columns, scaled_target)

        if solution is None:
            emit(
                "needs_derivation",
                reason="the Ser-split collinearity was not certified by the exact rational witness system",
                checks=[*checks, "fail:exact_fraction_system_unsolved"],
                registered_equivalence=registered_equivalence,
                within_ser_subspace=within_ser_subspace,
                control_matrix={"rows": len(codons), "rank": len(kept_controls)},
            )

        residual = exact_residual(scaled_target, list(WITNESS_NAMES), columns_by_name, solution)
        if all(value == 0 for value in residual):
            checks.append("exact_scaled_ser_split_reconstruction_zero_residual")
        else:
            checks.append("fail:exact_scaled_ser_split_reconstruction_nonzero_residual")

        gate = estimability_gate(ser_split_vector(codons), control_basis)
        if gate["testable"] is False and float(gate["residual_norm"]) <= ZERO_TOL:
            checks.append("estimability_gate_rejects_ser_split_after_registered_controls")
        else:
            checks.append("fail:estimability_gate_did_not_reject_ser_split")

        if any(item.startswith("fail:") for item in checks):
            emit(
                "needs_derivation",
                reason="one or more exact certificate checks failed",
                checks=checks,
                registered_equivalence=registered_equivalence,
                within_ser_subspace=within_ser_subspace,
                witness_rank=witness_rank,
                control_matrix={"rows": len(codons), "rank": len(kept_controls)},
            )

        witness = [
            {"column": name, "coefficient_for_sqrt12_times_u": fraction_str(solution[name])}
            for name in WITNESS_NAMES
            if name in solution
        ]
        if within_ser_subspace["all_absorbed"] is True:
            reason = (
                "Exact rational elimination proves sqrt(12) times the Ser-split edge-defect contrast lies "
                "in the span of registered forbidden-control columns. Since the registered basis contains "
                "the corresponding amino-acid, base-composition, wobble, and codon-pair columns, the "
                "Ser-split residual is algebraically zero: v_SerSplit is undefined. The full 5-dimensional "
                "within-Ser zero-sum contrast space is also absorbed, so the 15-way within-Ser permutation "
                "null is degenerate: no within-Ser contrast is independently testable under this control "
                "basis."
            )
        else:
            reason = (
                "Exact rational elimination proves sqrt(12) times the Ser-split edge-defect contrast lies "
                "in the span of registered forbidden-control columns. Since the registered basis contains "
                "the corresponding amino-acid, base-composition, wobble, and codon-pair columns, the "
                "Ser-split residual is algebraically zero: v_SerSplit is undefined. The exact rank check "
                "does not certify full absorption of the 5-dimensional within-Ser zero-sum contrast space, "
                "so this certificate does not claim a degenerate 15-way within-Ser permutation null."
            )
        emit(
            "certified",
            reason=reason,
            codon_order_schema="codon_q6_selection_vectors.v1 sense-only locked order",
            target={
                "name": "SerSplit",
                "scaled_target": "sqrt(12) * u",
                "support": {"S4": sorted(SER4), "S2": sorted(SER2)},
                "coefficients": {"S4": "1", "S2": "-2", "elsewhere": "0"},
            },
            witness={
                "type": "exact_rational_solution_for_scaled_target",
                "columns": witness,
                "rank": witness_rank,
                "residual_squared_norm": "0",
                "ser_support_identity": "on Ser support, sqrt(12)*u = 1 - 3 * indicator(first base is purine)",
                "span_note": (
                    "Non-one-hot feature columns are verified against the registered z-scored forbidden "
                    "columns; each raw representative equals its mean times the intercept plus a nonzero "
                    "scalar times the registered z-scored column."
                ),
            },
            registered_equivalence=registered_equivalence,
            within_ser_subspace=within_ser_subspace,
            control_matrix={
                "rows": len(codons),
                "rank": len(kept_controls),
                "registered_columns": len(control_names),
                "kept_control_names": kept_controls,
                "dropped_dependent_control_names": dropped_controls,
                "block_names": block_names,
                **control_metadata,
            },
            estimability_gate={
                "residual_norm": 0.0 if abs(float(gate["residual_norm"])) <= ZERO_TOL else gate["residual_norm"],
                "testable": gate["testable"],
                "eps": ZERO_TOL,
            },
            checks=checks,
        )
    except Exception as exc:
        emit("needs_derivation", reason=f"experiment raised {type(exc).__name__}: {exc}", checks=["fail:exception"])


if __name__ == "__main__":
    main()

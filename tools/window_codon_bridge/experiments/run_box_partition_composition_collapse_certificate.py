#!/usr/bin/env python3
"""Box-partition composition-collapse certificate."""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
import json
import sys
from pathlib import Path
from typing import Hashable


ROOT = Path(__file__).resolve().parents[3]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.window_codon_bridge.experiments.run_sersplit_edge_defect_nonestimability_certificate import (  # noqa: E402
    REGISTERED_EQUIVALENCE_TOL,
    exact_column_rank,
    exact_residual,
    fraction_str,
    raw_semantic_control_columns,
    solve_fraction_system,
    zscore_fraction_values,
)
from tools.window_codon_bridge.experiments.run_synthetic_negative_control_axis_pack import (  # noqa: E402
    build_control_blocks,
    flatten_blocks,
    load_rows,
    norm,
    orthonormal_basis,
    rank_pruned_basis,
    residualize_with_basis,
)


EXPERIMENT_ID = "box_partition_composition_collapse_certificate"
CLAIM_ID = "bridge.genetic_code.box_partition.composition_collapse.certificate"
ZERO_TOL = 1e-12
RANK_TOL = 1e-10
STOP_CODONS = {"UAA", "UAG", "UGA"}
SIXFOLD_BRANCHES = {
    "Ser": {
        "plus_name": "UCN",
        "plus": {"UCU", "UCC", "UCA", "UCG"},
        "minus_name": "AGY",
        "minus": {"AGU", "AGC"},
        "aa_symbol": "S",
        "identity": "on Ser support, sqrt(12)*u = 1 - 3 * indicator(first base is purine)",
    },
    "Leu": {
        "plus_name": "CUN",
        "plus": {"CUU", "CUC", "CUA", "CUG"},
        "minus_name": "UUR",
        "minus": {"UUA", "UUG"},
        "aa_symbol": "L",
        "identity": (
            "on Leu support, sqrt(12)*u = 1 - 3 * indicator(first two bases are equal)"
        ),
    },
    "Arg": {
        "plus_name": "CGN",
        "plus": {"CGU", "CGC", "CGA", "CGG"},
        "minus_name": "AGR",
        "minus": {"AGA", "AGG"},
        "aa_symbol": "R",
        "identity": (
            "on Arg support, sqrt(12)*u = -2 + 3 * indicator(first base is GC) "
            "+ 3 * indicator(first two bases are equal)"
        ),
    },
}


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def quantized_float(value: float | None, digits: int = 12) -> float | None:
    return None if value is None else float(f"{float(value):.{digits}f}")


RAW_REGISTERED_BLOCKS = ("intercept:", "amino_acid:", "wobble:")
ZSCORE_REGISTERED_BLOCKS = ("gc:", "degeneracy:", "codon_pair_like:", "stability_dwell_like:")


def registered_equivalence_report(
    names: list[str],
    raw_columns: list[list[Fraction]],
    registered_columns_by_name: dict[str, list[float]],
) -> tuple[dict[str, object], list[str]]:
    deviations: dict[str, float] = {}
    drifted: list[str] = []
    modes: dict[str, str] = {}
    for name, column in zip(names, raw_columns):
        registered = registered_columns_by_name.get(name)
        if registered is None:
            drifted.append(name)
            continue
        if name.startswith(RAW_REGISTERED_BLOCKS):
            local_values = [float(value) for value in column]
            modes[name] = "direct_raw_column"
        elif name.startswith(ZSCORE_REGISTERED_BLOCKS):
            local_values = zscore_fraction_values(column)
            modes[name] = "raw_column_equals_mean_times_intercept_plus_nonzero_scale_times_registered_zscore"
        else:
            drifted.append(name)
            continue
        max_deviation = max(abs(local - registered_value) for local, registered_value in zip(local_values, registered))
        deviations[name] = max_deviation
        if max_deviation > REGISTERED_EQUIVALENCE_TOL:
            drifted.append(name)
    return {
        "tolerance": REGISTERED_EQUIVALENCE_TOL,
        "max_abs_deviation": max(deviations.values()) if deviations else None,
        "columns": deviations,
        "modes": modes,
        "fail_closed": not drifted,
    }, drifted


def scaled_branch_target(codons: list[str], plus: set[str], minus: set[str]) -> list[Fraction]:
    return [Fraction(1 if codon in plus else (-2 if codon in minus else 0)) for codon in codons]


def support_identity_holds(
    codons: list[str],
    aa: str,
    target: list[Fraction],
) -> bool:
    support = set(SIXFOLD_BRANCHES[aa]["plus"]) | set(SIXFOLD_BRANCHES[aa]["minus"])
    for index, codon in enumerate(codons):
        if codon not in support:
            continue
        if aa == "Ser":
            value = Fraction(1) - 3 * Fraction(int(codon[0] in "AG"))
        elif aa == "Leu":
            value = Fraction(1) - 3 * Fraction(int(codon[0] == codon[1]))
        elif aa == "Arg":
            value = Fraction(-2) + 3 * Fraction(int(codon[0] in "GC")) + 3 * Fraction(int(codon[0] == codon[1]))
        else:
            raise KeyError(aa)
        if value != target[index]:
            return False
    return True


def branch_identity_coefficients(aa: str) -> dict[str, Fraction]:
    if aa == "Ser":
        return {"constant": Fraction(1), "indicator(first base is purine)": Fraction(-3)}
    if aa == "Leu":
        return {"constant": Fraction(1), "indicator(first two bases are equal)": Fraction(-3)}
    if aa == "Arg":
        return {
            "constant": Fraction(-2),
            "indicator(first base is GC)": Fraction(3),
            "indicator(first two bases are equal)": Fraction(3),
        }
    raise KeyError(aa)


def branch_report(
    aa: str,
    codons: list[str],
    exact_names: list[str],
    exact_columns: list[list[Fraction]],
    columns_by_name: dict[str, list[Fraction]],
    control_basis: list[list[float]],
) -> tuple[dict[str, object], list[str]]:
    spec = SIXFOLD_BRANCHES[aa]
    plus = set(str(codon) for codon in spec["plus"])
    minus = set(str(codon) for codon in spec["minus"])
    target = scaled_branch_target(codons, plus, minus)
    solution, witness_rank = solve_fraction_system(exact_names, exact_columns, target)
    checks: list[str] = []

    witness: list[dict[str, str]] = []
    residual_squared_norm = "uncomputed"
    exact_zero = False
    if solution is None:
        residual = target
    else:
        residual = exact_residual(target, exact_names, columns_by_name, solution)
        exact_zero = all(value == 0 for value in residual)
        residual_squared_norm = fraction_str(sum(value * value for value in residual))
        witness = [
            {"column": name, "coefficient_for_sqrt12_times_u": fraction_str(solution[name])}
            for name in exact_names
            if name in solution
        ]

    float_target = [float(value) for value in target]
    float_residual = residualize_with_basis(float_target, control_basis)
    float_residual_norm = norm(float_residual)
    identity_ok = support_identity_holds(
        codons,
        aa,
        target,
    )
    if exact_zero:
        checks.append(f"{aa}:exact_fraction_witness_zero_residual")
    else:
        checks.append(f"fail:{aa}:exact_fraction_witness_nonzero_residual")
    if identity_ok:
        checks.append(f"{aa}:on_support_identity_verified")
    else:
        checks.append(f"fail:{aa}:on_support_identity_failed")
    if float_residual_norm <= ZERO_TOL:
        checks.append(f"{aa}:registered_float_gate_residual_zero")
    else:
        checks.append(f"fail:{aa}:registered_float_gate_residual_nonzero")

    report = {
        "in_span_C": exact_zero,
        "scaled_target": "sqrt(12) * u",
        "support": {
            str(spec["plus_name"]): sorted(plus),
            str(spec["minus_name"]): sorted(minus),
        },
        "coefficients": {str(spec["plus_name"]): "1", str(spec["minus_name"]): "-2", "elsewhere": "0"},
        "witness": {
            "type": "exact_rational_solution_for_scaled_target",
            "columns": witness,
            "rank": witness_rank,
            "residual_squared_norm": residual_squared_norm,
        },
        "on_support_identity": str(spec["identity"]),
        "on_support_identity_terms": {
            name: fraction_str(coefficient)
            for name, coefficient in branch_identity_coefficients(aa).items()
        },
        "residual_norm": 0.0 if float_residual_norm <= ZERO_TOL else quantized_float(float_residual_norm),
        "exact_residual_nonzero_entries": [
            {"codon": codon, "value": fraction_str(value)}
            for codon, value in zip(codons, residual)
            if value != 0
        ],
    }
    return report, checks


def indicator_contrast_columns(labels: list[Hashable]) -> tuple[list[str], list[list[Fraction]], dict[str, int]]:
    groups: dict[Hashable, list[int]] = defaultdict(list)
    for index, label in enumerate(labels):
        groups[label].append(index)
    ordered = sorted(groups, key=lambda item: str(item))
    anchor = ordered[-1]
    columns: list[list[Fraction]] = []
    names: list[str] = []
    for label in ordered[:-1]:
        column = [Fraction(0) for _label in labels]
        for index in groups[label]:
            column[index] = Fraction(1, len(groups[label]))
        for index in groups[anchor]:
            column[index] -= Fraction(1, len(groups[anchor]))
        columns.append(column)
        names.append(f"{label}_minus_{anchor}")
    group_sizes = {str(label): len(indices) for label, indices in sorted(groups.items(), key=lambda item: str(item[0]))}
    return names, columns, group_sizes


def full_box_partition_report(
    codons: list[str],
    exact_columns: list[list[Fraction]],
    control_basis: list[list[float]],
) -> tuple[dict[str, object], list[str]]:
    labels = [codon[:2] for codon in codons]
    contrast_names, contrast_columns, group_sizes = indicator_contrast_columns(labels)
    control_rank = exact_column_rank(exact_columns)
    exact_absorbed_rows: list[dict[str, object]] = []
    all_exact_absorbed = True
    for name, column in zip(contrast_names, contrast_columns):
        rank_with_appended = exact_column_rank([*exact_columns, column])
        absorbed = rank_with_appended == control_rank
        all_exact_absorbed = all_exact_absorbed and absorbed
        exact_absorbed_rows.append(
            {
                "basis_direction": name,
                "absorbed": absorbed,
                "rank_with_appended": rank_with_appended,
            }
        )

    float_columns = [[float(value) for value in column] for column in contrast_columns]
    contrast_basis, kept_indices = orthonormal_basis(float_columns)
    residual_columns = [residualize_with_basis(column, control_basis) for column in contrast_basis]
    residual_basis, residual_kept = orthonormal_basis(residual_columns, tol=RANK_TOL)
    residual_norms = [norm(column) for column in residual_columns]
    residual_rank = 0 if all_exact_absorbed else len(residual_basis)
    absorbed = all_exact_absorbed and residual_rank == 0
    checks = [
        "full_16_box_partition_exact_rank_absorbed"
        if all_exact_absorbed
        else "fail:full_16_box_partition_exact_rank_survives",
        "full_16_box_partition_registered_float_residual_rank_zero"
        if len(residual_basis) == 0 and (max(residual_norms) if residual_norms else 0.0) <= 2e-12
        else "fail:full_16_box_partition_registered_float_residual_rank_nonzero",
    ]
    return {
        "dim": len(contrast_columns),
        "box_count": len(set(labels)),
        "residual_rank": residual_rank,
        "absorbed": absorbed,
        "exact_control_rank": control_rank,
        "exact_rank_with_box_partition": exact_column_rank([*exact_columns, *contrast_columns]),
        "basis_directions": exact_absorbed_rows,
        "group_sizes": group_sizes,
        "float_cross_check": {
            "contrast_basis_dim": len(contrast_basis),
            "contrast_basis_source_indices": kept_indices,
            "residual_rank": len(residual_basis),
            "residual_rank_basis_source_indices": residual_kept,
            "max_residual_norm": quantized_float(max(residual_norms) if residual_norms else 0.0),
            "per_direction_residual_norms": [quantized_float(value) for value in residual_norms],
            "rank_tolerance": RANK_TOL,
        },
    }, checks


def main() -> None:
    try:
        rows = load_rows()
        codons = [str(row["codon"]) for row in rows]
        amino_acids = [str(row["amino_acid"]) for row in rows]
        blocks, control_metadata = build_control_blocks(rows)
        control_names, control_columns, block_names = flatten_blocks(blocks)
        registered_columns_by_name = dict(zip(control_names, control_columns))
        kept_controls, dropped_controls, control_basis = rank_pruned_basis(control_names, control_columns)
        exact_names, exact_columns = raw_semantic_control_columns(rows)
        columns_by_name = dict(zip(exact_names, exact_columns))
        registered_exact_names = [name for name in control_names if not name.startswith("selection_packet:")]

        checks = [
            "sense_codon_order_has_61_unique_rows"
            if len(codons) == 61 and len(set(codons)) == 61
            else "fail:sense_codon_order",
            "sense_only_no_stop_codons"
            if all(codon not in STOP_CODONS for codon in codons)
            else "fail:stop_codon_present",
            "registered_control_basis_reused_from_synthetic_negative_control_axis_pack",
            "exact_fraction_proof_excludes_float_selection_packet_columns",
            "no_rng_used_in_verdict_path",
            "raw_semantic_exact_columns_match_registered_nonselection_column_names"
            if exact_names == registered_exact_names
            else "fail:raw_semantic_column_name_drift",
            "all_amino_acid_one_hot_columns_registered"
            if all(f"amino_acid:aa_{aa}" in exact_names or aa == "Y" for aa in sorted(set(amino_acids)))
            else "fail:amino_acid_one_hot_column_missing",
        ]

        equivalence, drifted_columns = registered_equivalence_report(
            exact_names,
            exact_columns,
            registered_columns_by_name,
        )
        if drifted_columns:
            checks.append(f"fail:registered_column_equivalence_drift:{','.join(drifted_columns)}")
        else:
            checks.append("registered_nonselection_columns_match_fraction_semantic_reconstruction")

        branch_reports: dict[str, object] = {}
        for aa in ("Ser", "Leu", "Arg"):
            report, local_checks = branch_report(
                aa,
                codons,
                exact_names,
                exact_columns,
                columns_by_name,
                control_basis,
            )
            branch_reports[aa] = report
            checks.extend(local_checks)

        full_box_partition, full_box_checks = full_box_partition_report(codons, exact_columns, control_basis)
        checks.extend(full_box_checks)

        registered_equivalence = {
            "fail_closed": not drifted_columns,
            "max_deviation": equivalence["max_abs_deviation"],
            "semantic_fraction_columns": equivalence,
            "drifted_columns": drifted_columns,
        }

        sixfold_all_absorbed = all(
            bool(report["in_span_C"])
            for report in branch_reports.values()
            if isinstance(report, dict)
        )
        if sixfold_all_absorbed:
            checks.append("all_three_sixfold_branch_splits_exactly_in_span_C")
        else:
            checks.append("fail:some_sixfold_branch_split_survives")

        if registered_equivalence["fail_closed"] is not True:
            checks.append("fail:registered_column_equivalence_drift")

        if any(item.startswith("fail:") for item in checks):
            survivors = [
                aa for aa, report in branch_reports.items()
                if isinstance(report, dict) and report.get("in_span_C") is not True
            ]
            emit(
                "needs_derivation",
                reason=(
                    "the box-partition composition-collapse certificate is fail-closed; one or more "
                    "registered-column, exact-branch, or full-box absorption checks failed"
                ),
                per_amino_acid=branch_reports,
                surviving_branch_splits=survivors,
                full_box_partition=full_box_partition,
                registered_column_equivalence=registered_equivalence,
                control_matrix={
                    "rows": len(codons),
                    "registered_columns": len(control_names),
                    "rank": len(kept_controls),
                    "kept_control_names": kept_controls,
                    "dropped_dependent_control_names": dropped_controls,
                    "block_names": block_names,
                    **control_metadata,
                },
                checks=checks,
            )

        status = "certified"
        reason = (
            "Exact rational elimination proves the Ser, Leu, and Arg 4-vs-2 within-amino-acid branch "
            "splits all lie in the span of the registered composition control frame. The full mean-zero "
            "16-box first-two-position indicator subspace has exact residual rank zero after the same "
            "frame, so the 64-to-16 box partition is absorbed by composition controls rather than an "
            "independent forcing direction."
        )
        emit(
            status,
            reason=reason,
            codon_order_schema="codon_q6_selection_vectors sense-only locked order",
            per_amino_acid=branch_reports,
            full_box_partition=full_box_partition,
            registered_column_equivalence=registered_equivalence,
            oracle_exact_decomposition={
                "statement": (
                    "span(16 first-two-position box indicators) is contained in the span of amino-acid "
                    "one-hots plus the Ser, Leu, and Arg 4-vs-2 branch splits"
                ),
                "aa_one_hots_in_C": True,
                "sixfold_branch_splits_in_C": True,
                "box_partition_in_C": True,
            },
            control_matrix={
                "rows": len(codons),
                "registered_columns": len(control_names),
                "rank": len(kept_controls),
                "kept_control_names": kept_controls,
                "dropped_dependent_control_names": dropped_controls,
                "block_names": block_names,
                **control_metadata,
            },
            checks=checks,
        )
    except Exception as exc:
        emit("needs_derivation", reason=f"experiment raised {type(exc).__name__}: {exc}", checks=["fail:exception"])


if __name__ == "__main__":
    main()

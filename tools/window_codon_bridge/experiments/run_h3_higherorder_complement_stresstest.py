#!/usr/bin/env python3
"""H3 three-position chemistry interaction stress-test against span(C)."""
from __future__ import annotations

from fractions import Fraction
import inspect
from itertools import product
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.window_codon_bridge.experiments.run_box_partition_composition_collapse_certificate import (  # noqa: E402
    registered_equivalence_report,
)
from tools.window_codon_bridge.experiments.run_sersplit_edge_defect_nonestimability_certificate import (  # noqa: E402
    exact_column_rank,
    raw_semantic_control_columns,
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


EXPERIMENT_ID = "h3_higherorder_complement_stresstest"
CLAIM_ID = "bridge.genetic_code.h3_higherorder.complement_stresstest"
ZERO_TOL = 1e-12
RANK_TOL = 1e-10
STOP_CODONS = {"UAA", "UAG", "UGA"}
Q6_FIELDS = {"q6_bits", "q6_label"}
PARTITION_ORDER = ("RY", "WS", "KM")
PARTITIONS = {
    "RY": {"A": 1, "G": 1, "C": -1, "U": -1},
    "WS": {"A": 1, "U": 1, "G": -1, "C": -1},
    "KM": {"G": 1, "U": 1, "A": -1, "C": -1},
}


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def quantized_float(value: float | None, digits: int = 12) -> float | None:
    return None if value is None else float(f"{float(value):.{digits}f}")


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def mean_center(values: list[Fraction]) -> list[Fraction]:
    mean = sum(values, Fraction(0)) / len(values)
    return [value - mean for value in values]


def h3_columns(codons: list[str]) -> tuple[list[str], list[list[Fraction]], dict[str, object]]:
    names: list[str] = []
    columns: list[list[Fraction]] = []
    raw_sums: dict[str, str] = {}
    means: dict[str, str] = {}
    for choices in product(PARTITION_ORDER, repeat=3):
        name = "h3:" + "_".join(choices)
        raw = [
            Fraction(
                PARTITIONS[choices[0]][codon[0]]
                * PARTITIONS[choices[1]][codon[1]]
                * PARTITIONS[choices[2]][codon[2]]
            )
            for codon in codons
        ]
        centered = mean_center(raw)
        names.append(name)
        columns.append(centered)
        raw_sums[name] = fraction_str(sum(raw, Fraction(0)))
        means[name] = fraction_str(sum(raw, Fraction(0)) / len(raw))
    return names, columns, {"raw_sums": raw_sums, "means": means}


def fraction_str(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def h3_leakage_contract() -> dict[str, object]:
    return {
        "classification": "label_free_codon_spelling_only_higher_order_chemistry",
        "declared_inputs": ["codon_string", "fixed_RY_WS_KM_base_dichotomies"],
        "barred_inputs": sorted(Q6_FIELDS | {"Stop", "amino_acid", "family_counts", "selection_packet"}),
        "uses_q6_labels_or_bits": False,
        "uses_stop_codons": False,
        "uses_amino_acid_labels": False,
        "uses_counts": False,
        "uses_rng": False,
        "mean_centered_over": "61 sense codons",
        "pre_registered_before_residuals": True,
    }


def leakage_guard(
    codons: list[str],
    rows: list[dict[str, object]],
    h3_names: list[str],
    h3_cols: list[list[Fraction]],
    contract: dict[str, object],
) -> tuple[bool, list[dict[str, object]]]:
    declared_inputs = set(str(item) for item in contract["declared_inputs"])
    checks = [
        check_row("sense_codon_row_count", len(codons), 61),
        check_row("sense_codon_order_has_unique_rows", len(set(codons)), 61),
        check_row("sense_only_no_stop_codons", sorted(set(codons) & STOP_CODONS), []),
        check_row("h3_vector_count", len(h3_cols), 27),
        check_row("h3_names_are_partition_triples", h3_names, [f"h3:{'_'.join(item)}" for item in product(PARTITION_ORDER, repeat=3)]),
        check_row("h3_declared_inputs_are_q6_label_free", sorted(declared_inputs & Q6_FIELDS), []),
        check_row("h3_declared_inputs_exclude_amino_acid", "amino_acid" in declared_inputs, False),
        check_row("h3_declared_inputs_exclude_counts", "family_counts" in declared_inputs, False),
        check_row("h3_contract_uses_q6_labels_or_bits", contract["uses_q6_labels_or_bits"], False),
        check_row("h3_contract_uses_stop_codons", contract["uses_stop_codons"], False),
        check_row("h3_contract_uses_amino_acid_labels", contract["uses_amino_acid_labels"], False),
        check_row("h3_contract_uses_counts", contract["uses_counts"], False),
        check_row("h3_contract_uses_rng", contract["uses_rng"], False),
        check_row("h3_builder_takes_only_codon_strings", list(inspect.signature(h3_columns).parameters), ["codons"]),
        check_row(
            "h3_columns_are_mean_centered_exactly",
            [fraction_str(sum(column, Fraction(0))) for column in h3_cols],
            ["0" for _column in h3_cols],
        ),
        check_row(
            "input_packet_q6_fields_are_present_but_barred_from_h3_contract",
            {
                "packet_q6_fields": sorted(set(rows[0]) & Q6_FIELDS) if rows else [],
                "contract_barred_q6_fields": sorted(set(contract["barred_inputs"]) & Q6_FIELDS),
            },
            {
                "packet_q6_fields": sorted(Q6_FIELDS),
                "contract_barred_q6_fields": sorted(Q6_FIELDS),
            },
        ),
    ]
    return all(bool(row["ok"]) for row in checks), checks


def per_direction_absorption(
    h3_names: list[str],
    h3_cols: list[list[Fraction]],
    exact_control_rank: int,
    exact_control_columns: list[list[Fraction]],
    control_basis: list[list[float]],
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for name, column in zip(h3_names, h3_cols):
        rank_with_direction = exact_column_rank([*exact_control_columns, column])
        float_residual = residualize_with_basis([float(value) for value in column], control_basis)
        residual_norm = norm(float_residual)
        rows.append(
            {
                "direction": name,
                "absorbed": rank_with_direction == exact_control_rank,
                "rank_with_direction": rank_with_direction,
                "residual_norm": 0.0 if residual_norm <= ZERO_TOL else quantized_float(residual_norm),
            }
        )
    return rows


def residual_rank_float_cross_check(
    h3_cols: list[list[Fraction]],
    control_basis: list[list[float]],
) -> dict[str, object]:
    h3_float_cols = [[float(value) for value in column] for column in h3_cols]
    h3_basis, h3_kept = orthonormal_basis(h3_float_cols, tol=RANK_TOL)
    residual_columns = [residualize_with_basis(column, control_basis) for column in h3_basis]
    residual_basis, residual_kept = orthonormal_basis(residual_columns, tol=RANK_TOL)
    residual_norms = [norm(column) for column in residual_columns]
    return {
        "h3_basis_dim": len(h3_basis),
        "h3_basis_source_indices": h3_kept,
        "residual_rank": len(residual_basis),
        "residual_rank_basis_source_indices": residual_kept,
        "max_residual_norm": quantized_float(max(residual_norms) if residual_norms else 0.0),
        "per_basis_residual_norms": [0.0 if value <= ZERO_TOL else quantized_float(value) for value in residual_norms],
        "rank_tolerance": RANK_TOL,
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
        registered_exact_names = [name for name in control_names if not name.startswith("selection_packet:")]
        exact_control_rank = exact_column_rank(exact_columns)

        h3_names, h3_cols, h3_centering = h3_columns(codons)
        h3_dim = len(h3_cols)
        h3_span_rank = exact_column_rank(h3_cols)
        exact_rank_with_h3 = exact_column_rank([*exact_columns, *h3_cols])
        h3_residual_rank = exact_rank_with_h3 - exact_control_rank

        equivalence, drifted_columns = registered_equivalence_report(
            exact_names,
            exact_columns,
            registered_columns_by_name,
        )
        h3_contract = h3_leakage_contract()
        leakage_ok, leakage_checks = leakage_guard(codons, rows, h3_names, h3_cols, h3_contract)
        direction_rows = per_direction_absorption(
            h3_names,
            h3_cols,
            exact_control_rank,
            exact_columns,
            control_basis,
        )
        float_cross_check = residual_rank_float_cross_check(h3_cols, control_basis)

        structured_checks = [
            check_row("registered_nonselection_columns_match_fraction_reconstruction", exact_names, registered_exact_names),
            check_row("registered_nonselection_equivalence_fail_closed", not drifted_columns, True),
            check_row("registered_control_metadata_has_no_q6_inputs", control_metadata.get("uses_q6_labels_or_bits"), False),
            check_row("registered_control_names_have_no_q6_columns", [name for name in control_names if "q6" in name.lower()], []),
            check_row("exact_control_rank", exact_control_rank, 29),
            check_row("h3_dim", h3_dim, 27),
            check_row("h3_leakage_guard_ok", leakage_ok, True),
        ]
        structured_checks.extend(leakage_checks)

        checks = [
            "registered_control_basis_reused_from_synthetic_negative_control_axis_pack",
            "registered_equivalence_fail_closed_to_actual_control_columns",
            "exact_fraction_rank_uses_registered_nonselection_columns",
            "h3_pre_registered_before_residuals",
            "h3_uses_only_codon_spelling_and_fixed_chemistry_dichotomies",
            "no_rng_used_in_verdict_path",
        ]
        checks.extend(row["name"] if row["ok"] else f"fail:{row['name']}" for row in structured_checks)
        if drifted_columns:
            checks.append(f"fail:registered_column_equivalence_drift:{','.join(drifted_columns)}")

        registered_equivalence = {
            "fail_closed": not drifted_columns,
            "max_deviation": equivalence["max_abs_deviation"],
            "semantic_fraction_columns": equivalence,
            "drifted_columns": drifted_columns,
        }
        per_direction_residual_norms = {
            row["direction"]: row["residual_norm"]
            for row in direction_rows
        }
        measurement = {
            "h3_dim": h3_dim,
            "h3_span_rank": h3_span_rank,
            "exact_control_rank": exact_control_rank,
            "exact_rank_with_h3": exact_rank_with_h3,
            "h3_residual_rank": h3_residual_rank,
            "per_direction_residual_norms": per_direction_residual_norms,
        }
        h3_report = {
            "construction": "mean-centered chi_a(base1) * chi_b(base2) * chi_c(base3) for a,b,c in {RY,WS,KM}",
            "partition_order": list(PARTITION_ORDER),
            "partition_values": PARTITIONS,
            "dimension": h3_dim,
            "span_rank": h3_span_rank,
            "centering": h3_centering,
            "per_direction": direction_rows,
            "float_cross_check": float_cross_check,
        }
        forcing_status = {
            "closure_delimitation": h3_residual_rank > 0,
            "forcing_reopening": False,
            "window6_necessitation_test": False,
            "pre_registered_necessitation_null": False,
            "principle_selecting_h3_among_higher_order_audit_languages": False,
            "candidate_for_future_forcing_work": h3_residual_rank > 0,
            "math_to_bio_forcing_direction_closure_stands": True,
            "interpretation": (
                "H3 survival would delimit the certified composition absorption frame only; it does not "
                "supply a Window6 necessitation test or a selected forcing language."
            ),
        }

        fail_closed_ok = leakage_ok and not drifted_columns and not any(item.startswith("fail:") for item in checks)
        if not fail_closed_ok:
            emit(
                "needs_derivation",
                reason=(
                    "The H3 stress-test is fail-closed; leakage, registered-equivalence, or registered-column "
                    "checks did not pass."
                ),
                **measurement,
                h3=h3_report,
                registered_equivalence=registered_equivalence,
                leakage_checks={"ok": leakage_ok, "contract": h3_contract, "checks": leakage_checks},
                forcing_status=forcing_status,
                control_matrix={
                    "rows": len(codons),
                    "registered_columns": len(control_names),
                    "registered_rank_float": len(kept_controls),
                    "exact_nonselection_columns": len(exact_names),
                    "exact_nonselection_rank": exact_control_rank,
                    "kept_control_names": kept_controls,
                    "dropped_dependent_control_names": dropped_controls,
                    "block_names": block_names,
                    **control_metadata,
                },
                checks=checks,
                structured_checks=structured_checks,
            )

        if h3_residual_rank == 0:
            status = "certified"
            reason = (
                "Exact Fraction rank elimination against the actual registered non-selection control columns "
                "certifies H3 is contained in span(C). The registered q6-label-free leakage guard passes, so "
                "the closure absorbs the canonical three-position chemistry interaction class."
            )
        else:
            status = "refuted"
            reason = (
                "Exact Fraction rank elimination shows H3 has nonzero residual rank after the actual "
                "registered non-selection control columns. The closure does not absorb this higher-order "
                "three-position chemistry class: the surviving residual dimension is "
                f"{h3_residual_rank}. This is a delimitation of the composition-absorption frame, not a "
                "forcing reopening; no Window6 necessitation test, no pre-registered necessitation null, "
                "and no selection principle for H3 among higher-order audit languages is present here."
            )

        emit(
            status,
            reason=reason,
            **measurement,
            h3=h3_report,
            registered_equivalence=registered_equivalence,
            leakage_checks={"ok": leakage_ok, "contract": h3_contract, "checks": leakage_checks},
            forcing_status=forcing_status,
            control_matrix={
                "rows": len(codons),
                "registered_columns": len(control_names),
                "registered_rank_float": len(kept_controls),
                "exact_nonselection_columns": len(exact_names),
                "exact_nonselection_rank": exact_control_rank,
                "kept_control_names": kept_controls,
                "dropped_dependent_control_names": dropped_controls,
                "block_names": block_names,
                **control_metadata,
            },
            checks=checks,
            structured_checks=structured_checks,
        )
    except Exception as exc:
        emit("needs_derivation", reason=f"experiment raised {type(exc).__name__}: {exc}", checks=["fail:exception"])


if __name__ == "__main__":
    main()

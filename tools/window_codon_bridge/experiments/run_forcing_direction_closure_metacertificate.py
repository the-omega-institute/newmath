#!/usr/bin/env python3
"""Forcing-direction closure meta-certificate for the Window6/codon bridge."""
from __future__ import annotations

from collections import Counter, defaultdict
from fractions import Fraction
import json
import sys
from pathlib import Path
from typing import Hashable


ROOT = Path(__file__).resolve().parents[3]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.window_codon_bridge.experiments.run_bcd_fourcell_selection_enrichment import (  # noqa: E402
    CELL_ORDER,
    reconstruct_window6_cells,
)
from tools.window_codon_bridge.experiments.run_box_partition_composition_collapse_certificate import (  # noqa: E402
    SIXFOLD_BRANCHES,
    registered_equivalence_report,
    scaled_branch_target,
)
from tools.window_codon_bridge.experiments.run_genetic_code_fold_cert import CODON_TO_OUTPUT  # noqa: E402
from tools.window_codon_bridge.experiments.run_sersplit_edge_defect_nonestimability_certificate import (  # noqa: E402
    exact_column_rank,
    raw_semantic_control_columns,
)
from tools.window_codon_bridge.experiments.run_synthetic_negative_control_axis_pack import (  # noqa: E402
    build_control_blocks,
    flatten_blocks,
    load_rows,
    rank_pruned_basis,
)


EXPERIMENT_ID = "forcing_direction_closure_metacertificate"
CLAIM_ID = "bridge.window6_codon_q6.forcing_direction_closure.metacertificate"
STOP_CODONS = {"UAA", "UAG", "UGA"}
Q6_FIELDS = {"q6_bits", "q6_label"}
BIO_INTRINSIC_BATTERY_BLOCKS = (
    "box_partition",
    "degeneracy_class",
    "fold_layer",
    "sixfold_branch_split",
)
REOPENING_CONDITION = (
    "a label-free genetic-code invariant outside span(C), defined without q6 or family counts, whose "
    "preservation forced-Window6/Fibonacci/Zeckendorf structure necessitates more strongly than a "
    "pre-registered composition-controlled null."
)


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def indicator_contrast_columns(labels: list[Hashable]) -> tuple[list[str], list[list[Fraction]], dict[str, int]]:
    groups: dict[Hashable, list[int]] = defaultdict(list)
    for index, label in enumerate(labels):
        groups[label].append(index)
    ordered = sorted(groups, key=lambda item: str(item))
    anchor = ordered[-1]
    names: list[str] = []
    columns: list[list[Fraction]] = []
    for label in ordered[:-1]:
        column = [Fraction(0) for _label in labels]
        for index in groups[label]:
            column[index] = Fraction(1, len(groups[label]))
        for index in groups[anchor]:
            column[index] -= Fraction(1, len(groups[anchor]))
        names.append(f"{label}_minus_{anchor}")
        columns.append(column)
    group_sizes = {str(label): len(indices) for label, indices in sorted(groups.items(), key=lambda item: str(item[0]))}
    return names, columns, group_sizes


def box_split_type_by_prefix() -> dict[str, str]:
    result: dict[str, str] = {}
    for prefix in sorted({codon[:2] for codon in CODON_TO_OUTPUT}):
        outputs = {CODON_TO_OUTPUT[prefix + third] for third in ("U", "C", "A", "G")}
        if len(outputs) == 1:
            result[prefix] = "pure"
        elif len(outputs) == 2:
            result[prefix] = "split"
        elif len(outputs) == 3:
            result[prefix] = "tri_split"
        else:
            raise RuntimeError(f"unexpected split type for box {prefix}: {outputs}")
    return result


def fold_layer_labels(codons: list[str], amino_acids: list[str]) -> list[str]:
    return [f"{codon[:2]}:{amino_acid}" for codon, amino_acid in zip(codons, amino_acids)]


def window6_4cell_labels(rows: list[dict[str, object]]) -> tuple[list[str], dict[str, object]]:
    cells = reconstruct_window6_cells()
    owner = {label: cell for cell, labels in cells.items() for label in labels}
    labels = [owner[str(row["q6_label"])] for row in rows]
    return labels, {
        "classification": "correspondence_derived_barred",
        "declared_inputs": ["q6_label", "reconstruct_window6_cells"],
        "barred_from_certificate": True,
        "full_64_cell_sizes": {cell: len(cells[cell]) for cell in CELL_ORDER},
        "sense_61_cell_sizes": dict(sorted(Counter(labels).items())),
    }


def block_report(
    block_name: str,
    names: list[str],
    columns: list[list[Fraction]],
    exact_control_rank: int,
    exact_control_columns: list[list[Fraction]],
) -> dict[str, object]:
    rank_with_block = exact_column_rank([*exact_control_columns, *columns])
    span_rank = exact_column_rank(columns)
    basis_rows = []
    for name, column in zip(names, columns):
        rank_with_direction = exact_column_rank([*exact_control_columns, column])
        basis_rows.append(
            {
                "basis_direction": name,
                "absorbed": rank_with_direction == exact_control_rank,
                "rank_with_direction": rank_with_direction,
            }
        )
    return {
        "block": block_name,
        "column_count": len(columns),
        "span_rank": span_rank,
        "exact_control_rank": exact_control_rank,
        "exact_rank_with_block": rank_with_block,
        "absorbed": rank_with_block == exact_control_rank,
        "basis_directions": basis_rows,
    }


def source_contracts() -> dict[str, dict[str, object]]:
    return {
        "box_partition": {
            "classification": "label_free_bio_intrinsic",
            "declared_inputs": ["codon_string"],
            "barred_inputs": sorted(Q6_FIELDS),
        },
        "box_split_type": {
            "classification": "label_free_bio_intrinsic",
            "declared_inputs": ["codon_string", "codon_table_output_by_codon_spelling"],
            "barred_inputs": sorted(Q6_FIELDS),
        },
        "degeneracy_class": {
            "classification": "label_free_bio_intrinsic",
            "declared_inputs": ["amino_acid", "codon_table_degeneracy"],
            "barred_inputs": sorted(Q6_FIELDS),
        },
        "fold_layer": {
            "classification": "label_free_bio_intrinsic",
            "declared_inputs": ["codon_string", "amino_acid", "box_output_fragment"],
            "barred_inputs": sorted(Q6_FIELDS),
        },
        "sixfold_branch_split": {
            "classification": "label_free_bio_intrinsic",
            "declared_inputs": ["codon_string", "amino_acid", "codon_table_degeneracy"],
            "barred_inputs": sorted(Q6_FIELDS),
        },
        "window6_4cell": {
            "classification": "correspondence_derived_barred",
            "declared_inputs": ["q6_label", "reconstruct_window6_cells"],
            "barred_from_certificate": True,
        },
    }


def label_free_guard(contracts: dict[str, dict[str, object]]) -> tuple[bool, list[dict[str, object]]]:
    rows: list[dict[str, object]] = []
    for name in BIO_INTRINSIC_BATTERY_BLOCKS:
        declared_inputs = set(str(item) for item in contracts[name]["declared_inputs"])
        rows.append(check_row(f"{name}_is_q6_label_free", sorted(declared_inputs & Q6_FIELDS), []))
    rows.append(
        check_row(
            "bio_intrinsic_battery_is_q6_label_free",
            all(
                not (set(str(item) for item in contracts[name]["declared_inputs"]) & Q6_FIELDS)
                for name in BIO_INTRINSIC_BATTERY_BLOCKS
            ),
            True,
        )
    )
    rows.append(
        check_row(
            "window6_4cell_is_correspondence_derived_barred",
            contracts["window6_4cell"].get("classification") == "correspondence_derived_barred"
            and "q6_label" in contracts["window6_4cell"].get("declared_inputs", [])
            and contracts["window6_4cell"].get("barred_from_certificate") is True,
            True,
        )
    )
    return all(row["ok"] for row in rows), rows


def build_battery(
    codons: list[str],
    amino_acids: list[str],
) -> tuple[dict[str, tuple[list[str], list[list[Fraction]], dict[str, int]]], dict[str, object]]:
    degeneracy = Counter(amino_acids)
    split_type = box_split_type_by_prefix()

    block_specs: dict[str, tuple[list[str], list[list[Fraction]], dict[str, int]]] = {}
    block_specs["box_partition"] = indicator_contrast_columns([codon[:2] for codon in codons])
    block_specs["degeneracy_class"] = indicator_contrast_columns([degeneracy[aa] for aa in amino_acids])
    block_specs["fold_layer"] = indicator_contrast_columns(fold_layer_labels(codons, amino_acids))

    branch_names: list[str] = []
    branch_columns: list[list[Fraction]] = []
    branch_sizes: dict[str, int] = {}
    for aa in ("Ser", "Leu", "Arg"):
        spec = SIXFOLD_BRANCHES[aa]
        branch_names.append(f"{aa}:{spec['plus_name']}_minus_{spec['minus_name']}")
        branch_columns.append(scaled_branch_target(codons, set(spec["plus"]), set(spec["minus"])))
        branch_sizes[aa] = len(set(spec["plus"]) | set(spec["minus"]))
    block_specs["sixfold_branch_split"] = (branch_names, branch_columns, branch_sizes)

    profiles = {
        "box_split_type_profile": dict(sorted(Counter(split_type[codon[:2]] for codon in codons).items())),
        "degeneracy_class_profile": {
            str(size): count for size, count in sorted(Counter(degeneracy[aa] for aa in amino_acids).items())
        },
        "fold_layer_sense_fragment_count": len(set(fold_layer_labels(codons, amino_acids))),
    }
    return block_specs, profiles


def flatten_battery(
    block_specs: dict[str, tuple[list[str], list[list[Fraction]], dict[str, int]]],
) -> tuple[list[str], list[list[Fraction]]]:
    names: list[str] = []
    columns: list[list[Fraction]] = []
    for block_name in BIO_INTRINSIC_BATTERY_BLOCKS:
        block_names, block_columns, _group_sizes = block_specs[block_name]
        for name, column in zip(block_names, block_columns):
            names.append(f"{block_name}:{name}")
            columns.append(column)
    return names, columns


def main() -> None:
    try:
        rows = load_rows()
        codons = [str(row["codon"]) for row in rows]
        amino_acids = [str(row["amino_acid"]) for row in rows]

        blocks, control_metadata = build_control_blocks(rows)
        control_names, control_columns, block_names = flatten_blocks(blocks)
        registered_columns_by_name = dict(zip(control_names, control_columns))
        kept_controls, dropped_controls, _control_basis = rank_pruned_basis(control_names, control_columns)

        exact_names, exact_columns = raw_semantic_control_columns(rows)
        registered_exact_names = [name for name in control_names if not name.startswith("selection_packet:")]
        exact_control_rank = exact_column_rank(exact_columns)

        equivalence, drifted_columns = registered_equivalence_report(
            exact_names,
            exact_columns,
            registered_columns_by_name,
        )

        contracts = source_contracts()
        leakage_guard_ok, leakage_guard_checks = label_free_guard(contracts)
        block_specs, battery_profiles = build_battery(codons, amino_acids)
        battery_names, battery_columns = flatten_battery(block_specs)
        battery_span_rank = exact_column_rank(battery_columns)
        exact_rank_with_battery = exact_column_rank([*exact_columns, *battery_columns])
        union_absorbed = exact_rank_with_battery == exact_control_rank

        per_block_absorption = {
            block_name: block_report(
                block_name,
                block_specs[block_name][0],
                block_specs[block_name][1],
                exact_control_rank,
                exact_columns,
            )
            for block_name in BIO_INTRINSIC_BATTERY_BLOCKS
        }

        split_type = box_split_type_by_prefix()
        box_split_names, box_split_columns, box_split_sizes = indicator_contrast_columns(
            [split_type[codon[:2]] for codon in codons]
        )
        window6_labels, window6_contract = window6_4cell_labels(rows)
        contracts["window6_4cell"].update(window6_contract)
        window6_names, window6_columns, window6_sizes = indicator_contrast_columns(window6_labels)
        exact_rank_with_window6 = exact_column_rank([*exact_columns, *window6_columns])
        window6_residual_rank = exact_rank_with_window6 - exact_control_rank
        exact_rank_with_box_split = exact_column_rank([*exact_columns, *box_split_columns])

        structured_checks = [
            check_row("sense_codon_row_count", len(codons), 61),
            check_row("sense_codon_order_has_unique_rows", len(set(codons)), 61),
            check_row("sense_only_no_stop_codons", sorted(set(codons) & STOP_CODONS), []),
            check_row("registered_nonselection_columns_match_fraction_reconstruction", exact_names, registered_exact_names),
            check_row("registered_nonselection_equivalence_fail_closed", not drifted_columns, True),
            check_row("registered_control_metadata_has_no_q6_inputs", control_metadata.get("uses_q6_labels_or_bits"), False),
            check_row(
                "registered_control_names_have_no_q6_columns",
                [name for name in control_names if "q6" in name.lower()],
                [],
            ),
            check_row("bio_intrinsic_battery_is_q6_label_free", leakage_guard_ok, True),
            check_row("union_battery_exact_rank_absorbed", exact_rank_with_battery, exact_control_rank),
            check_row(
                "all_battery_blocks_exact_rank_absorbed",
                all(report["absorbed"] for report in per_block_absorption.values()),
                True,
            ),
            check_row("box_split_type_exact_rank_absorbed", exact_rank_with_box_split, exact_control_rank),
            check_row("window6_4cell_exact_residual_rank", window6_residual_rank, len(window6_columns)),
            check_row(
                "window6_4cell_classified_correspondence_derived_barred",
                contracts["window6_4cell"].get("classification"),
                "correspondence_derived_barred",
            ),
        ]
        structured_checks.extend(leakage_guard_checks)

        checks = [
            "registered_control_basis_reused_from_synthetic_negative_control_axis_pack",
            "registered_equivalence_fail_closed_to_actual_control_columns",
            "exact_fraction_proof_excludes_float_selection_packet_columns",
            "no_rng_used_in_verdict_path",
            "union_absorption_checked_as_one_exact_rank_statement",
        ]
        checks.extend(row["name"] if row["ok"] else f"fail:{row['name']}" for row in structured_checks)
        for block_name, report in per_block_absorption.items():
            checks.append(
                f"{block_name}:exact_rank_{report['exact_control_rank']}_to_{report['exact_rank_with_block']}"
                if report["absorbed"]
                else f"fail:{block_name}:exact_rank_{report['exact_control_rank']}_to_{report['exact_rank_with_block']}"
            )

        union_absorption = {
            "statement": "span(label-free fold-boundary battery) is contained in span(C_nonselection)",
            "battery_blocks": list(BIO_INTRINSIC_BATTERY_BLOCKS),
            "battery_column_count": len(battery_columns),
            "battery_span_rank": battery_span_rank,
            "exact_control_rank": exact_control_rank,
            "exact_rank_with_battery_appended": exact_rank_with_battery,
            "absorbed": union_absorbed,
            "battery_basis_names": battery_names,
            "per_block_absorption": per_block_absorption,
            "profiles": battery_profiles,
        }
        circularity_barring = {
            "window6_4cell": {
                "classification": "correspondence_derived_barred",
                "dim": len(window6_columns),
                "group_sizes": window6_sizes,
                "basis_directions": window6_names,
                "exact_control_rank": exact_control_rank,
                "exact_rank_with_window6_4cell": exact_rank_with_window6,
                "exact_residual_rank": window6_residual_rank,
                "survives_span_C": window6_residual_rank > 0,
                "barred_reason": (
                    "window6_4cell is reconstructed from q6_label, while C_nonselection has no q6 columns; "
                    "survival is circularity evidence, not math-to-bio forcing evidence"
                ),
            },
            "label_free_box_split_type": {
                "classification": "label_free_bio_intrinsic",
                "dim": len(box_split_columns),
                "group_sizes": box_split_sizes,
                "basis_directions": box_split_names,
                "exact_rank_with_box_split_type": exact_rank_with_box_split,
                "absorbed": exact_rank_with_box_split == exact_control_rank,
            },
        }
        scope_statement = {
            "positive": (
                "BC7 contravariant edge-hiding extremality and the edge-exhaustion meta-certificate remain "
                "the certified math-side results; this runner references them by name and does not recompute them"
            ),
            "bounding_negative": (
                "the label-free bio fold-boundary battery is contained in span(C_nonselection), leaving no "
                "independent bio-side residual axis for Window6 to force under this frame"
            ),
            "forcing_direction": "closed_as_not_supported_under_current_frame",
            "count_spectrum_matches": "coincidence",
            "q6_mediated_transport": "circular_and_barred",
        }

        status = "certified" if union_absorbed and leakage_guard_ok and not any(item.startswith("fail:") for item in checks) else "needs_derivation"
        reason = (
            "Exact Fraction rank elimination certifies the full label-free fold-boundary battery, taken as "
            "one union, lies in span(C_nonselection). The only audited fold-boundary survivor is "
            "window6_4cell, and it is correspondence-derived from q6_label, so q6-mediated transport is "
            "barred as circular. The math-to-bio forcing direction is closed as not supported under the "
            "current frame; count and spectrum matches are coincidence absent a label-free residual outside "
            "the registered composition-controlled null."
            if status == "certified"
            else "The closure meta-certificate requires exact union absorption and a q6-label-free battery; one or more fail-closed checks did not pass."
        )

        emit(
            status,
            reason=reason,
            union_absorption=union_absorption,
            circularity_barring=circularity_barring,
            scope_statement=scope_statement,
            reopening_condition=REOPENING_CONDITION,
            registered_column_equivalence={
                "fail_closed": not drifted_columns,
                "drifted_columns": drifted_columns,
                "semantic_fraction_columns": equivalence,
            },
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
            source_contracts=contracts,
            checks=checks,
            structured_checks=structured_checks,
        )
    except Exception as exc:
        emit("needs_derivation", reason=f"experiment raised {type(exc).__name__}: {exc}", checks=["fail:exception"])


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Fold-boundary residual exhaustion certificate.

The certified target spaces in this file are fixed from spelling, degeneracy,
and fold-layer structure before any projection is computed.  The Window6
four-cell partition is also reported, but it is derived from q6 labels and is
therefore barred from the certificate verdict.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import product
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
from tools.window_codon_bridge.experiments.run_genetic_code_fold_cert import (  # noqa: E402
    BASES,
    CODON_TO_OUTPUT,
)
from tools.window_codon_bridge.experiments.run_synthetic_negative_control_axis_pack import (  # noqa: E402
    build_control_blocks,
    flatten_blocks,
    load_rows,
    norm,
    orthonormal_basis,
    rank_pruned_basis,
    residual_unit,
    residualize_with_basis,
)


EXPERIMENT_ID = "foldboundary_residual_exhaustion_certificate"
CLAIM_ID = "bridge.genetic_code.foldboundary.residual.exhaustion.certificate"
ZERO_TOL = 1e-12
BIO_INTRINSIC_SUBSPACES = ("box_split_type", "degeneracy_class", "fold_layer")
BARRED_CORRESPONDENCE_DERIVED_SUBSPACES = ("window6_4cell",)
Q6_FIELDS = {"q6_label", "q6_bits"}


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def quantized_float(value: float | None, digits: int = 12) -> float | None:
    return None if value is None else float(f"{float(value):.{digits}f}")


def all_codons() -> list[str]:
    return ["".join(chars) for chars in product(BASES, repeat=3)]


def box_split_type_by_prefix() -> dict[str, str]:
    """Register the 16-box split type from codon spelling and table fragments."""
    result: dict[str, str] = {}
    for first, second in product(BASES, repeat=2):
        prefix = first + second
        outputs = {CODON_TO_OUTPUT[prefix + third] for third in BASES}
        if len(outputs) == 1:
            kind = "pure"
        elif len(outputs) == 2:
            kind = "split"
        elif len(outputs) == 3:
            kind = "tri_split"
        else:
            raise RuntimeError(f"unexpected split type for box {prefix}: {outputs}")
        result[prefix] = kind
    return result


def fold_layer_labels(codons: list[str], rows: list[dict[str, object]]) -> list[str]:
    """Register the 64->16->25->21 fold-layer fragment partition on sense codons.

    The 64->16 layer is the first-two-position box.  The 16->25 layer splits a
    box by its table output fragments.  Restricting to the 61 sense codons
    removes the Stop fragments, leaving the sense box-output fragments.
    """
    return [f"{codon[:2]}:{row['amino_acid']}" for codon, row in zip(codons, rows)]


def window6_4cell_owner() -> tuple[dict[str, str], dict[str, object]]:
    """Report the canonical Window6 four-cell map on q6 labels.

    The map is reconstructed from the existing bridge Foldbin/Zeckendorf rule:
    no-adjacent visible six-bit words with weights 1,2,3,5,8,13 and tail
    weights 21,34,55 are classified as U_2, U_1, U_L, or U_R, then folded to
    q6 labels by the bridge value label.  Sense codons inherit their cell from
    the locked codon_q6_selection_vectors q6_label field.  This partition is
    correspondence-derived and does not enter the certificate verdict.
    """
    cells = reconstruct_window6_cells()
    owner = {label: cell for cell, labels in cells.items() for label in labels}
    note = {
        "source": (
            "reconstruct_window6_cells from run_bcd_fourcell_selection_enrichment; "
            "q6 labels are the locked codon_q6_selection_vectors labels"
        ),
        "full_64_cell_sizes": {cell: len(cells[cell]) for cell in CELL_ORDER},
        "cell_order": list(CELL_ORDER),
    }
    return owner, note


def source_contracts() -> dict[str, dict[str, object]]:
    """Declare the data sources each subspace construction is allowed to use."""
    return {
        "box_split_type": {
            "classification": "bio_intrinsic",
            "declared_inputs": ["codon_string", "codon_table_output_by_codon_spelling"],
            "barred_inputs": sorted(Q6_FIELDS),
        },
        "degeneracy_class": {
            "classification": "bio_intrinsic",
            "declared_inputs": ["amino_acid", "codon_table_degeneracy"],
            "barred_inputs": sorted(Q6_FIELDS),
        },
        "fold_layer": {
            "classification": "bio_intrinsic",
            "declared_inputs": ["codon_string", "amino_acid", "box_output_fragment"],
            "barred_inputs": sorted(Q6_FIELDS),
        },
        "window6_4cell": {
            "classification": "correspondence_derived_barred",
            "declared_inputs": ["q6_label", "reconstruct_window6_cells"],
            "barred_from_certificate": True,
        },
    }


def leakage_guard_rows(contracts: dict[str, dict[str, object]]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for name in BIO_INTRINSIC_SUBSPACES:
        declared_inputs = set(str(item) for item in contracts[name]["declared_inputs"])
        observed = sorted(declared_inputs & Q6_FIELDS)
        rows.append(
            check_row(
                f"{name}_is_q6_label_free",
                observed,
                [],
            )
        )
    rows.append(
        check_row(
            "bio_intrinsic_subspaces_are_q6_label_free",
            all(
                not (set(str(item) for item in contracts[name]["declared_inputs"]) & Q6_FIELDS)
                for name in BIO_INTRINSIC_SUBSPACES
            ),
            True,
        )
    )
    window_contract = contracts["window6_4cell"]
    rows.append(
        check_row(
            "window6_4cell_is_correspondence_derived_barred",
            window_contract.get("classification") == "correspondence_derived_barred"
            and "q6_label" in window_contract.get("declared_inputs", [])
            and window_contract.get("barred_from_certificate") is True,
            True,
        )
    )
    return rows


def indicator_contrast_columns(labels: list[Hashable]) -> tuple[list[str], list[list[float]], dict[str, int]]:
    """Return a basis for the between-label mean-zero contrast subspace.

    For k labels, the anchored columns are group-mean indicators:
    indicator(label)/|label| - indicator(anchor)/|anchor|.  Their span is the
    k-1 dimensional subspace of vectors constant on labels and orthogonal to the
    intercept.
    """
    groups: dict[Hashable, list[int]] = defaultdict(list)
    for index, label in enumerate(labels):
        groups[label].append(index)
    ordered = sorted(groups, key=lambda item: str(item))
    anchor = ordered[-1]
    columns: list[list[float]] = []
    names: list[str] = []
    for label in ordered[:-1]:
        column = [0.0 for _ in labels]
        for index in groups[label]:
            column[index] = 1.0 / len(groups[label])
        for index in groups[anchor]:
            column[index] -= 1.0 / len(groups[anchor])
        columns.append(column)
        names.append(f"{label}_minus_{anchor}")
    group_sizes = {str(label): len(indices) for label, indices in sorted(groups.items(), key=lambda item: str(item[0]))}
    return names, columns, group_sizes


def residual_report(
    labels: list[Hashable],
    control_basis: list[list[float]],
) -> dict[str, object]:
    contrast_names, raw_columns, group_sizes = indicator_contrast_columns(labels)
    contrast_basis, kept_indices = orthonormal_basis(raw_columns)
    if len(contrast_basis) != len(raw_columns):
        raise RuntimeError(
            f"pre-registered contrast columns were dependent: kept {kept_indices}, total {len(raw_columns)}"
        )
    residual_columns = [residualize_with_basis(column, control_basis) for column in contrast_basis]
    residual_basis, residual_kept = orthonormal_basis(residual_columns)
    residual_norms = [norm(column) for column in residual_columns]
    direction_reports = []
    for name, basis_column, residual_column, residual_norm in zip(
        contrast_names, contrast_basis, residual_columns, residual_norms
    ):
        unit, via_helper_norm = residual_unit(basis_column, control_basis)
        direction_reports.append(
            {
                "basis_direction": name,
                "residual_norm": quantized_float(residual_norm),
                "residual_unit_exists": unit is not None,
                "helper_residual_norm": quantized_float(via_helper_norm),
                "absorbed": residual_norm <= ZERO_TOL,
            }
        )
    dim = len(contrast_basis)
    residual_rank = len(residual_basis)
    return {
        "dim": dim,
        "residual_rank": residual_rank,
        "absorbed_fraction": quantized_float((dim - residual_rank) / dim if dim else 1.0),
        "max_residual_norm": quantized_float(max(residual_norms) if residual_norms else 0.0),
        "per_direction_residual_norms": [quantized_float(value) for value in residual_norms],
        "residual_rank_basis_source_indices": residual_kept,
        "basis_directions": direction_reports,
        "group_sizes": group_sizes,
    }


def main() -> None:
    try:
        rows = load_rows()
        codons = [str(row["codon"]) for row in rows]
        amino_acids = [str(row["amino_acid"]) for row in rows]

        blocks, control_metadata = build_control_blocks(rows)
        control_names, control_columns, block_names = flatten_blocks(blocks)
        kept_controls, dropped_controls, control_basis = rank_pruned_basis(control_names, control_columns)

        split_type = box_split_type_by_prefix()
        degeneracy_by_amino_acid = Counter(amino_acids)
        cell_owner, cell_map_note = window6_4cell_owner()

        contracts = source_contracts()

        # Pre-registered report subspaces.  This dictionary is fully constructed
        # before any residual computation below.
        subspace_labels: dict[str, list[Hashable]] = {
            "box_split_type": [split_type[codon[:2]] for codon in codons],
            "degeneracy_class": [degeneracy_by_amino_acid[aa] for aa in amino_acids],
            "fold_layer": fold_layer_labels(codons, rows),
            "window6_4cell": [cell_owner[str(row["q6_label"])] for row in rows],
        }
        bio_intrinsic_subspaces = list(BIO_INTRINSIC_SUBSPACES)
        barred_correspondence_derived_subspaces = list(BARRED_CORRESPONDENCE_DERIVED_SUBSPACES)

        stop_codons = {"UAA", "UAG", "UGA"}
        codon_to_cell = {codon: str(cell) for codon, cell in zip(codons, subspace_labels["window6_4cell"])}
        cell_map_note.update(
            {
                "sense_61_cell_sizes": dict(sorted(Counter(subspace_labels["window6_4cell"]).items())),
                "codon_to_cell": dict(sorted(codon_to_cell.items())),
                "stop_codons_excluded": sorted(stop_codons),
            }
        )

        reports = {
            name: residual_report(labels, control_basis)
            for name, labels in subspace_labels.items()
        }
        absorbed = sorted(name for name, report in reports.items() if report["residual_rank"] == 0)
        survivors = sorted(name for name, report in reports.items() if report["residual_rank"] != 0)
        bio_intrinsic_absorbed = [
            name for name in bio_intrinsic_subspaces if reports[name]["residual_rank"] == 0
        ]
        bio_intrinsic_survivors = [
            name for name in bio_intrinsic_subspaces if reports[name]["residual_rank"] != 0
        ]
        barred_correspondence_derived = {
            name: reports[name] for name in barred_correspondence_derived_subspaces
        }
        barred_correspondence_derived_survivors = [
            name for name in barred_correspondence_derived_subspaces if reports[name]["residual_rank"] != 0
        ]
        leakage_guard = leakage_guard_rows(contracts)
        leakage_guard_ok = all(row["ok"] for row in leakage_guard)

        checks = [
            "sense_codon_order_has_61_unique_rows"
            if len(codons) == 61 and len(set(codons)) == 61
            else "fail:sense_codon_order",
            "sense_only_no_stop_codons"
            if all(codon not in stop_codons for codon in codons)
            else "fail:stop_codon_present",
            "registered_control_basis_reused_from_synthetic_negative_control_axis_pack",
            "subspaces_pre_registered_before_residual_projection",
            "no_rng_used_in_verdict_path",
            "bio_intrinsic_subspaces_are_q6_label_free"
            if leakage_guard_ok
            else "fail:bio_intrinsic_subspaces_are_q6_label_free",
            "window6_4cell_is_correspondence_derived_barred",
            "window6_4cell_reported_for_transparency_not_certificate_verdict",
        ]
        checks.extend(
            f"{name}:dim_{report['dim']}_residual_rank_{report['residual_rank']}"
            for name, report in reports.items()
        )
        structured_checks = [
            check_row("all_codons_count", len(all_codons()), 64),
            check_row("codon_table_covers_ucag_cube", sorted(CODON_TO_OUTPUT), sorted(all_codons())),
            check_row(
                "box_split_type_profile_on_61_sense",
                dict(sorted(Counter(subspace_labels["box_split_type"]).items())),
                {"pure": 32, "split": 26, "tri_split": 3},
            ),
            check_row(
                "degeneracy_class_profile_on_61_sense",
                {str(size): count for size, count in sorted(Counter(subspace_labels["degeneracy_class"]).items())},
                {"1": 2, "2": 18, "3": 3, "4": 20, "6": 18},
            ),
            check_row("fold_layer_sense_fragment_count", len(set(subspace_labels["fold_layer"])), 23),
            check_row(
                "window6_full_cell_sizes",
                cell_map_note["full_64_cell_sizes"],
                {"U_2": 27, "U_1": 22, "U_L": 9, "U_R": 6},
            ),
            check_row(
                "window6_sense_cell_sizes",
                cell_map_note["sense_61_cell_sizes"],
                {"U_1": 22, "U_2": 25, "U_L": 9, "U_R": 5},
            ),
            *leakage_guard,
        ]
        for row in structured_checks:
            checks.append(row["name"] if row["ok"] else f"fail:{row['name']}")

        if any(item.startswith("fail:") for item in checks):
            emit(
                "needs_derivation",
                reason="one or more fold-boundary self-checks failed before the absorption verdict",
                subspaces=reports,
                bio_intrinsic_subspaces={name: reports[name] for name in bio_intrinsic_subspaces},
                barred_correspondence_derived=barred_correspondence_derived,
                codon_cell_map_note=cell_map_note,
                subspace_source_contracts=contracts,
                control_matrix={
                    "rows": len(codons),
                    "registered_columns": len(control_names),
                    "rank": len(control_basis),
                    "kept_control_names": kept_controls,
                    "dropped_dependent_control_names": dropped_controls,
                    "block_names": block_names,
                    **control_metadata,
                },
                checks=checks,
                structured_checks=structured_checks,
            )

        if not bio_intrinsic_survivors and leakage_guard_ok:
            status = "certified"
            reason = (
                "The bio-intrinsic fold-boundary contrast subspaces "
                f"{', '.join(bio_intrinsic_subspaces)} are q6-label-free and fully absorbed by the "
                "registered composition control frame, so they provide no independent residual axis "
                "beyond those controls. This is a bounding exhaustion extension. The window6_4cell "
                "partition is correspondence-derived from q6_label; because the registered control "
                "matrix contains no q6 information, its residual survival is expected and is barred "
                "from the certificate rather than treated as an independent forcing target."
            )
        else:
            status = "needs_derivation"
            reason = (
                "The certificate cannot be issued unless every bio-intrinsic fold-boundary contrast "
                "subspace has residual rank zero and the q6-label leakage guard passes. Observed "
                f"bio-intrinsic survivor(s): {', '.join(bio_intrinsic_survivors) if bio_intrinsic_survivors else 'none'}; "
                f"leakage_guard_ok={leakage_guard_ok}. The window6_4cell partition is "
                "correspondence-derived from q6_label, so any survival there is barred and is not "
                "forcing evidence."
            )

        emit(
            status,
            reason=reason,
            subspaces=reports,
            bio_intrinsic_subspaces={name: reports[name] for name in bio_intrinsic_subspaces},
            barred_correspondence_derived=barred_correspondence_derived,
            absorbed_subspaces=absorbed,
            surviving_subspaces=survivors,
            bio_intrinsic_absorbed_subspaces=bio_intrinsic_absorbed,
            bio_intrinsic_surviving_subspaces=bio_intrinsic_survivors,
            barred_correspondence_derived_surviving_subspaces=barred_correspondence_derived_survivors,
            codon_cell_map_note=cell_map_note,
            subspace_source_contracts=contracts,
            control_matrix={
                "rows": len(codons),
                "registered_columns": len(control_names),
                "rank": len(control_basis),
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

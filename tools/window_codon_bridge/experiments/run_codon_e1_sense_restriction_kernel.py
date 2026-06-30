#!/usr/bin/env python3
"""Sense-restricted codon-E1 kernel and positional rank certificate."""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path
from types import ModuleType


EXPERIMENT_ID = "codon_e1_sense_restriction_kernel"
CLAIM_ID = "bridge.genetic_code.codon_e1_sense_restriction_positional_rank"

CHARACTER_ORDER = ("R", "W", "K")
TOL = 1.0e-8


def load_verified_base() -> ModuleType:
    script_dir = Path(__file__).resolve().parent
    if str(script_dir) not in sys.path:
        sys.path.insert(0, str(script_dir))
    import run_bstar_q6_eigenspace_concentration_profile as base

    return base


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status in {"certified", "refuted"} else 2)


def check_row(name: str, ok: bool, **fields: object) -> dict[str, object]:
    row = {"name": name, "ok": bool(ok)}
    row.update(fields)
    return row


def round_float(value: float, digits: int = 12) -> float:
    if not math.isfinite(value):
        return value
    rounded = round(value, digits)
    return 0.0 if rounded == -0.0 else rounded


def chemical_character(character: str, base: str) -> float:
    values = {
        "R": {"A": 1.0, "G": 1.0, "C": -1.0, "U": -1.0},
        "W": {"A": 1.0, "U": 1.0, "C": -1.0, "G": -1.0},
        "K": {"U": 1.0, "G": 1.0, "C": -1.0, "A": -1.0},
    }
    return values[character][base]


def first_order_character_basis(codons: list[str], base: ModuleType) -> list[dict[str, object]]:
    basis: list[dict[str, object]] = []
    for position in range(3):
        for character in CHARACTER_ORDER:
            raw = [chemical_character(character, codon[position]) for codon in codons]
            norm = base.vector_norm(raw)
            basis.append(
                {
                    "key": f"p{position + 1}_{character}",
                    "position": position + 1,
                    "character": character,
                    "vector": [value / norm for value in raw],
                }
            )
    return basis


def columns_to_matrix(columns: list[list[float]]) -> list[list[float]]:
    if not columns:
        return []
    return [[column[row] for column in columns] for row in range(len(columns[0]))]


def linear_combination(columns: list[list[float]], coefficients: list[float]) -> list[float]:
    return [
        sum(coefficient * column[row] for coefficient, column in zip(coefficients, columns))
        for row in range(len(columns[0]))
    ]


def max_abs(vector: list[float]) -> float:
    return max((abs(value) for value in vector), default=0.0)


def build_sense_syn_columns(base: ModuleType) -> tuple[list[dict[str, object]], list[list[float]]]:
    codons = base.codon_order()
    full_index = {codon: idx for idx, codon in enumerate(codons)}
    sense_codons = [codon for codon in codons if base.CODON_TO_AA[codon] != "*"]
    sense_index = {codon: idx for idx, codon in enumerate(sense_codons)}
    families = base.families_by_aa(sense_codons)

    e1_basis = first_order_character_basis(codons, base)
    columns: list[list[float]] = []
    for row in e1_basis:
        vector = row["vector"]
        assert isinstance(vector, list)
        restricted = [vector[full_index[codon]] for codon in sense_codons]
        columns.append(base.project_syn(restricted, sense_codons, families, sense_index))
    return e1_basis, columns


def main() -> None:
    base = load_verified_base()
    e1_basis, columns = build_sense_syn_columns(base)
    matrix = columns_to_matrix(columns)
    rank_m = base.matrix_rank(matrix, TOL)
    dim_ker = len(columns) - rank_m

    kernel_vectors = {
        "e_{1,R}-e_{1,W}+e_{1,K}": [1.0, -1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0],
        "e_{2,W}": [0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0],
        "e_{2,R}-e_{2,K}": [0.0, 0.0, 0.0, 1.0, 0.0, -1.0, 0.0, 0.0, 0.0],
    }
    kernel_residuals = {
        name: linear_combination(columns, coefficients)
        for name, coefficients in kernel_vectors.items()
    }
    kernel_norms = {
        name: round_float(base.vector_norm(residual), 14)
        for name, residual in kernel_residuals.items()
    }
    kernel_max_abs = {
        name: round_float(max_abs(residual), 14)
        for name, residual in kernel_residuals.items()
    }
    kernel_basis_matrix = [
        [coefficients[row] for coefficients in kernel_vectors.values()]
        for row in range(len(columns))
    ]
    kernel_basis_rank = base.matrix_rank(kernel_basis_matrix, TOL)
    kernel_maps_to_zero = all(max_abs(residual) <= TOL for residual in kernel_residuals.values())
    kernel_basis_verified = kernel_maps_to_zero and kernel_basis_rank == 3 and dim_ker == 3 and rank_m == 6

    positional_ranks: dict[str, int] = {}
    for position in range(1, 4):
        position_columns = [
            column
            for row, column in zip(e1_basis, columns)
            if row["position"] == position
        ]
        positional_ranks[f"p{position}"] = base.matrix_rank(columns_to_matrix(position_columns), TOL)

    character_ranks: dict[str, int] = {}
    for character in CHARACTER_ORDER:
        character_columns = [
            column
            for row, column in zip(e1_basis, columns)
            if row["character"] == character
        ]
        character_ranks[character] = base.matrix_rank(columns_to_matrix(character_columns), TOL)

    checks = [
        check_row("dim_E1", len(columns) == 9, observed=len(columns), expected=9),
        check_row("rank_M", rank_m == 6, observed=rank_m, expected=6),
        check_row("dim_ker", dim_ker == 3, observed=dim_ker, expected=3),
        check_row(
            "kernel_basis_maps_to_zero",
            kernel_maps_to_zero,
            max_abs=kernel_max_abs,
            norms=kernel_norms,
            tol=TOL,
        ),
        check_row("kernel_basis_independent", kernel_basis_rank == 3, observed=kernel_basis_rank, expected=3),
        check_row(
            "positional_ranks",
            positional_ranks == {"p1": 2, "p2": 1, "p3": 3},
            observed=positional_ranks,
            expected={"p1": 2, "p2": 1, "p3": 3},
        ),
        check_row(
            "character_ranks_K_full",
            character_ranks.get("K") == 3,
            observed=character_ranks,
            expected_K=3,
        ),
    ]

    status = "certified" if kernel_basis_verified and all(row["ok"] for row in checks) else "refuted"
    if status == "certified":
        reason = (
            "The sense-restricted, synonymous-centered codon-E1 map has kernel exactly spanned by "
            "{e_{1,R}-e_{1,W}+e_{1,K}, e_{2,W}, e_{2,R}-e_{2,K}} with rank M=6 and dim ker=3. "
            "The positional rank profile is (2,1,3), so wobble position 3 retains all three "
            "first-order degrees of freedom while positions 1 and 2 collapse to ranks 2 and 1. "
            f"The per-character ranks are R={character_ranks['R']}, W={character_ranks['W']}, "
            f"K={character_ranks['K']}; chi_K therefore has full first-order rank available, so its "
            "empirical non-enrichment in the E1-localization certificate is not a dimensional artifact."
        )
    else:
        failed = [str(row["name"]) for row in checks if not row["ok"]]
        reason = (
            f"Claim failed for {failed}: rank M={rank_m}, dim ker={dim_ker}, "
            f"kernel residual max norms={kernel_max_abs}, positional ranks={positional_ranks}, "
            f"character ranks={character_ranks}."
        )

    emit(
        status,
        dim_E1=len(columns),
        rank_M=rank_m,
        dim_ker=dim_ker,
        kernel_basis_verified=kernel_basis_verified,
        positional_ranks=positional_ranks,
        character_ranks=character_ranks,
        checks=checks,
        reason=reason,
    )


if __name__ == "__main__":
    main()

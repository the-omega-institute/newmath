#!/usr/bin/env python3
"""Position-by-character localization of B*_Q6 first-order H(3,4) mass."""
from __future__ import annotations

import json
import math
import random
import sys
from pathlib import Path
from types import ModuleType


EXPERIMENT_ID = "bstar_q6_first_order_position_character"
CLAIM_ID = "bridge.genetic_code.bstar_q6_first_order_position_character"

N_NULL = 20000
ALPHA = 0.001
ALPHA_BONFERRONI = ALPHA / 6.0
TOL = 1.0e-8
CHARACTER_ORDER = ("R", "W", "K")
PRIMARY_NULL_SEED = "bstar_q6_e3_spectral_concentration.primary.via.fixed.hash.seed"


def load_verified_base() -> ModuleType:
    # Reuse the verified machinery (H(3,4) graph, exact Krawtchouk projectors, the frozen B*_Q6
    # templates, and the matched-synonymous null) from the committed sibling experiment. Importing it
    # is side-effect-free (it guards execution behind `if __name__ == "__main__"`).
    script_dir = Path(__file__).resolve().parent
    if str(script_dir) not in sys.path:
        sys.path.insert(0, str(script_dir))
    import run_bstar_q6_eigenspace_concentration_profile as base

    return base


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status in {"certified", "coincidence", "refuted", "needs_derivation"} else 2)


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
                    "position": position,
                    "character": character,
                    "vector": [value / norm for value in raw],
                }
            )
    return basis


def outer_sum(vectors: list[list[float]]) -> list[list[float]]:
    size = len(vectors[0]) if vectors else 0
    result = [[0.0 for _ in range(size)] for _ in range(size)]
    for vector in vectors:
        for row, row_value in enumerate(vector):
            out_row = result[row]
            for col, col_value in enumerate(vector):
                out_row[col] += row_value * col_value
    return result


def max_off_diagonal_gram(vectors: list[list[float]], base: ModuleType) -> float:
    max_abs = 0.0
    for left in range(len(vectors)):
        for right in range(left + 1, len(vectors)):
            max_abs = max(max_abs, abs(base.dot(vectors[left], vectors[right])))
    return max_abs


def max_diagonal_gram_defect(vectors: list[list[float]], base: ModuleType) -> float:
    return max(abs(base.dot(vector, vector) - 1.0) for vector in vectors)


def component_masses(q_basis: list[list[float]], e1_basis: list[dict[str, object]], base: ModuleType) -> dict[str, float]:
    if not q_basis:
        return {str(row["key"]): 0.0 for row in e1_basis}
    rank = len(q_basis)
    masses: dict[str, float] = {}
    for row in e1_basis:
        vector = row["vector"]
        assert isinstance(vector, list)
        masses[str(row["key"])] = sum(base.dot(q, vector) ** 2 for q in q_basis) / rank
    return masses


def grouped_masses(masses: dict[str, float]) -> tuple[list[float], list[float]]:
    m_pos = [
        sum(masses[f"p{position}_{character}"] for character in CHARACTER_ORDER)
        for position in range(1, 4)
    ]
    m_chr = [
        sum(masses[f"p{position}_{character}"] for position in range(1, 4))
        for character in CHARACTER_ORDER
    ]
    return m_pos, m_chr


def null_component_values(
    templates: list[dict[str, object]],
    codons: list[str],
    index: dict[str, int],
    e1_basis: list[dict[str, object]],
    base: ModuleType,
    rng: random.Random,
) -> tuple[list[dict[str, float]], list[list[float]], list[list[float]]]:
    component_values: list[dict[str, float]] = []
    position_values: list[list[float]] = []
    character_values: list[list[float]] = []
    for _ in range(N_NULL):
        columns = [base.template_random_vector(template, codons, index, rng) for template in templates]
        q_basis = base.modified_gram_schmidt(columns, base.MGS_TOL)
        masses = component_masses(q_basis, e1_basis, base)
        m_pos, m_chr = grouped_masses(masses)
        component_values.append(masses)
        position_values.append(m_pos)
        character_values.append(m_chr)
    return component_values, position_values, character_values


def by_column(rows: list[list[float]], col: int) -> list[float]:
    return [row[col] for row in rows]


def summarize_group(observed: list[float], null_rows: list[list[float]], base: ModuleType) -> tuple[list[float], list[float], list[float], list[float], list[float]]:
    null_mean = []
    excess = []
    upper_p = []
    lower_p = []
    null_z = []
    for col, observed_value in enumerate(observed):
        values = by_column(null_rows, col)
        center = base.mean(values)
        std = base.sample_std(values, center)
        upper, lower = base.tail_p_values(values, observed_value)
        null_mean.append(center)
        excess_value = observed_value - center
        excess.append(excess_value)
        upper_p.append(upper)
        lower_p.append(lower)
        null_z.append(excess_value / std if std > 0.0 else math.inf)
    return null_mean, excess, upper_p, lower_p, null_z


def failure_payload(base: ModuleType | None, checks: list[dict[str, object]], reason: str, **fields: object) -> None:
    rounder = round_float if base is None else base.round_float
    emit(
        "failed",
        T1_total=fields.get("T1_total"),
        m_component=fields.get("m_component"),
        M_pos=fields.get("M_pos"),
        M_pos_null_mean=None,
        M_pos_excess=None,
        M_pos_upper_p=None,
        M_pos_lower_p=None,
        M_pos_z=None,
        M_chr=fields.get("M_chr"),
        M_chr_null_mean=None,
        M_chr_excess=None,
        M_chr_upper_p=None,
        M_chr_lower_p=None,
        M_chr_z=None,
        alpha_bonferroni=rounder(ALPHA_BONFERRONI, 7),
        n_null=N_NULL,
        carries_excess=[],
        checks=checks,
        reason=reason,
    )


def main() -> None:
    base: ModuleType | None = None
    try:
        base = load_verified_base()
        codons = base.codon_order()
        index = {codon: idx for idx, codon in enumerate(codons)}
        adjacency = base.adjacency_matrix(codons)
        edge_count = int(sum(sum(row) for row in adjacency) // 2)
        families = base.families_by_aa(codons)

        projectors = base.spectral_projectors(adjacency)
        identity = base.identity_matrix(len(codons))
        projector_sum = [[sum(projectors[level][row][col] for level in range(4)) for col in range(64)] for row in range(64)]
        projector_checks: list[dict[str, object]] = []
        ranks = []
        for level, projector in enumerate(projectors):
            rank = base.matrix_rank(projector, base.TOL)
            ranks.append(rank)
            idempotent = base.matrix_multiply(projector, projector)
            projector_checks.extend(
                [
                    check_row(
                        f"rank_E{level}",
                        rank == base.EIGENSPACE_DIMS[level],
                        observed=rank,
                        expected=base.EIGENSPACE_DIMS[level],
                    ),
                    check_row(
                        f"idempotent_E{level}",
                        base.max_abs_matrix_diff(idempotent, projector) <= 1.0e-7,
                        max_abs=base.round_float(base.max_abs_matrix_diff(idempotent, projector), 14),
                        tol=1.0e-7,
                    ),
                    check_row(
                        f"symmetric_E{level}",
                        base.max_abs_symmetric_defect(projector) <= 1.0e-9,
                        max_abs=base.round_float(base.max_abs_symmetric_defect(projector), 14),
                        tol=1.0e-9,
                    ),
                ]
            )

        templates = base.bstar_templates(codons, index, families)
        b_columns = []
        for template in templates:
            column = template["vector"]
            assert isinstance(column, list)
            b_columns.append(column)
        q_b = base.modified_gram_schmidt(b_columns, base.MGS_TOL)

        e1_basis = first_order_character_basis(codons, base)
        e1_vectors = []
        for row in e1_basis:
            vector = row["vector"]
            assert isinstance(vector, list)
            e1_vectors.append(vector)
        e1_outer_sum = outer_sum(e1_vectors)
        e1_projector_diff = base.max_abs_matrix_diff(e1_outer_sum, projectors[1])
        e1_offdiag = max_off_diagonal_gram(e1_vectors, base)
        e1_diag_defect = max_diagonal_gram_defect(e1_vectors, base)

        masses = component_masses(q_b, e1_basis, base)
        m_pos, m_chr = grouped_masses(masses)
        t1_total = sum(masses.values())
        t_profile = base.projector_profile(q_b, projectors)

        non_stop_zero = all(
            abs(template["vector"][index[codon]]) <= base.TOL
            for template in templates
            for codon in families["*"]
        )
        checks = [
            check_row("codon_order_len", len(codons) == 64, observed=len(codons), expected=64),
            check_row("standard_table_covers_codon_order", sorted(base.CODON_TO_AA) == sorted(codons), observed=len(base.CODON_TO_AA), expected=64),
            check_row("hamming_edges", edge_count == 288, observed=edge_count, expected=288),
            check_row("hamming_degree_9", all(sum(row) == 9.0 for row in adjacency), expected=9),
            check_row("projector_sum_identity", base.max_abs_matrix_diff(projector_sum, identity) <= 1.0e-8, max_abs=base.round_float(base.max_abs_matrix_diff(projector_sum, identity), 14), tol=1.0e-8),
            check_row("eigenspace_dims", ranks == list(base.EIGENSPACE_DIMS), observed=ranks, expected=list(base.EIGENSPACE_DIMS)),
            check_row("bstar_template_count", len(templates) == 9, observed=len(templates), expected=9),
            check_row("bstar_stop_coordinates_zero", non_stop_zero, stop_codons=families["*"]),
            check_row("rank_B", len(q_b) == 9, observed=len(q_b), expected=9),
            check_row("T_profile_sum", abs(sum(t_profile) - 1.0) <= 1.0e-8, observed=base.round_float(sum(t_profile), 14), expected=1.0),
            check_row("E1_character_basis_count", len(e1_basis) == 9, observed=len(e1_basis), expected=9),
            check_row("E1_character_basis_unit_norm", e1_diag_defect <= 1.0e-12, max_abs=base.round_float(e1_diag_defect, 14), tol=1.0e-12),
            check_row("E1_character_basis_orthogonal", e1_offdiag <= 1.0e-12, max_abs=base.round_float(e1_offdiag, 14), tol=1.0e-12),
            check_row("E1_character_basis_sums_to_projector", e1_projector_diff <= 1.0e-8, max_abs=base.round_float(e1_projector_diff, 14), tol=1.0e-8),
            check_row("T1_total_matches_E1_projector", abs(t1_total - t_profile[1]) <= 1.0e-8, observed=base.round_float(t1_total, 14), expected=base.round_float(t_profile[1], 14), tol=1.0e-8),
        ]
        checks.extend(projector_checks)

        rounded_masses = {key: base.round_float(masses[key]) for key in masses}
        rounded_m_pos = [base.round_float(value) for value in m_pos]
        rounded_m_chr = [base.round_float(value) for value in m_chr]
        if not all(row["ok"] for row in checks):
            failure_payload(
                base,
                checks,
                "internal projector, codon-table, B*_Q6, or E1 character-basis check failed",
                T1_total=base.round_float(t1_total),
                m_component=rounded_masses,
                M_pos=rounded_m_pos,
                M_chr=rounded_m_chr,
            )

        primary_rng = random.Random(base.stable_seed(PRIMARY_NULL_SEED))
        null_components, null_pos, null_chr = null_component_values(templates, codons, index, e1_basis, base, primary_rng)
        pos_mean, pos_excess, pos_upper, pos_lower, pos_z = summarize_group(m_pos, null_pos, base)
        chr_mean, chr_excess, chr_upper, chr_lower, chr_z = summarize_group(m_chr, null_chr, base)

        carries_excess: list[dict[str, object]] = []
        for idx, excess_value in enumerate(pos_excess):
            if excess_value > 0.0 and pos_upper[idx] <= ALPHA_BONFERRONI:
                carries_excess.append(
                    {
                        "group": f"position{idx + 1}",
                        "D": base.round_float(excess_value),
                        "upper_p": base.round_float(pos_upper[idx]),
                    }
                )
        for idx, character in enumerate(CHARACTER_ORDER):
            if chr_excess[idx] > 0.0 and chr_upper[idx] <= ALPHA_BONFERRONI:
                carries_excess.append(
                    {
                        "group": f"char_{character}",
                        "D": base.round_float(chr_excess[idx]),
                        "upper_p": base.round_float(chr_upper[idx]),
                    }
                )

        status = "certified" if carries_excess else "coincidence"
        winner_text = ", ".join(
            f"{row['group']} (D={row['D']}, upper_p={row['upper_p']})"
            for row in carries_excess
        ) or "none"
        reason = (
            "Scoped spectral-localization verdict for B*_Q6 first-order mass: "
            f"Bonferroni-significant excess carriers are {winner_text}. The matched null preserves each "
            "template's synonymous family/support/norm constraints, so these are excess-over-generic "
            "synonymous contrast effects. This makes no causal, selection, or forcing claim."
        )
        if any(row["group"] == "position3" for row in carries_excess):
            reason += " A position3 carrier is consistent with a wobble-position localization, without asserting a mechanism."

        emit(
            status,
            T1_total=base.round_float(t1_total),
            m_component=rounded_masses,
            M_pos=rounded_m_pos,
            M_pos_null_mean=[base.round_float(value) for value in pos_mean],
            M_pos_excess=[base.round_float(value) for value in pos_excess],
            M_pos_upper_p=[base.round_float(value) for value in pos_upper],
            M_pos_lower_p=[base.round_float(value) for value in pos_lower],
            M_pos_z=[base.round_float(value) for value in pos_z],
            M_chr=rounded_m_chr,
            M_chr_null_mean=[base.round_float(value) for value in chr_mean],
            M_chr_excess=[base.round_float(value) for value in chr_excess],
            M_chr_upper_p=[base.round_float(value) for value in chr_upper],
            M_chr_lower_p=[base.round_float(value) for value in chr_lower],
            M_chr_z=[base.round_float(value) for value in chr_z],
            alpha_bonferroni=base.round_float(ALPHA_BONFERRONI, 7),
            n_null=N_NULL,
            carries_excess=carries_excess,
            checks=checks,
            reason=reason,
        )
    except Exception as exc:
        failure_payload(
            base,
            [check_row("exception_free", False, exception=type(exc).__name__, message=str(exc))],
            "experiment raised before a valid verdict could be computed",
        )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""B*_Q6 residual-basis concentration profile across H(3,4) eigenspaces.

The standard RNA codon table below is NCBI genetic code table 1, encoded
locally so this experiment is self-contained and network-free.  Stop codons
are labeled "*".  The verdict is scoped to per-eigenspace excess or deficit
relative to the same fixed-seed matched synonymous contrast null used by the
E3-only check.
"""
from __future__ import annotations

from collections import defaultdict
from itertools import product
import hashlib
import json
import math
import random
import sys


EXPERIMENT_ID = "bstar_q6_eigenspace_concentration_profile"
CLAIM_ID = "bridge.genetic_code.bstar_q6_eigenspace_concentration_profile"

BASES = ("U", "C", "A", "G")
LAMBDA_VALUES = (9.0, 5.0, 1.0, -3.0)
EIGENSPACE_DIMS = (1, 9, 27, 27)
N_NULL = 20000
ALPHA = 0.001
ALPHA_BONFERRONI = ALPHA / 3.0
TOL = 1.0e-8
MGS_TOL = 1.0e-10
PRIMARY_NULL_SEED = "bstar_q6_e3_spectral_concentration.primary.via.fixed.hash.seed"

CODON_TO_AA = {
    "UUU": "F", "UUC": "F", "UUA": "L", "UUG": "L",
    "UCU": "S", "UCC": "S", "UCA": "S", "UCG": "S",
    "UAU": "Y", "UAC": "Y", "UAA": "*", "UAG": "*",
    "UGU": "C", "UGC": "C", "UGA": "*", "UGG": "W",
    "CUU": "L", "CUC": "L", "CUA": "L", "CUG": "L",
    "CCU": "P", "CCC": "P", "CCA": "P", "CCG": "P",
    "CAU": "H", "CAC": "H", "CAA": "Q", "CAG": "Q",
    "CGU": "R", "CGC": "R", "CGA": "R", "CGG": "R",
    "AUU": "I", "AUC": "I", "AUA": "I", "AUG": "M",
    "ACU": "T", "ACC": "T", "ACA": "T", "ACG": "T",
    "AAU": "N", "AAC": "N", "AAA": "K", "AAG": "K",
    "AGU": "S", "AGC": "S", "AGA": "R", "AGG": "R",
    "GUU": "V", "GUC": "V", "GUA": "V", "GUG": "V",
    "GCU": "A", "GCC": "A", "GCA": "A", "GCG": "A",
    "GAU": "D", "GAC": "D", "GAA": "E", "GAG": "E",
    "GGU": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status in {"certified", "coincidence", "refuted", "needs_derivation"} else 2)


def check_row(name: str, ok: bool, **fields: object) -> dict[str, object]:
    row = {"name": name, "ok": bool(ok)}
    row.update(fields)
    return row


def stable_seed(text: str) -> int:
    return int.from_bytes(hashlib.sha256(text.encode("utf-8")).digest()[:16], "big")


def round_float(value: float, digits: int = 12) -> float:
    if not math.isfinite(value):
        return value
    rounded = round(value, digits)
    return 0.0 if rounded == -0.0 else rounded


def codon_order() -> list[str]:
    return ["".join(parts) for parts in product(BASES, repeat=3)]


def hamming_one(left: str, right: str) -> bool:
    return sum(a != b for a, b in zip(left, right)) == 1


def adjacency_matrix(codons: list[str]) -> list[list[float]]:
    size = len(codons)
    matrix = [[0.0 for _ in range(size)] for _ in range(size)]
    for left in range(size):
        for right in range(left + 1, size):
            if hamming_one(codons[left], codons[right]):
                matrix[left][right] = 1.0
                matrix[right][left] = 1.0
    return matrix


def identity_matrix(size: int) -> list[list[float]]:
    return [[1.0 if row == col else 0.0 for col in range(size)] for row in range(size)]


def shifted_matrix(matrix: list[list[float]], shift: float) -> list[list[float]]:
    size = len(matrix)
    return [
        [matrix[row][col] - (shift if row == col else 0.0) for col in range(size)]
        for row in range(size)
    ]


def matrix_multiply(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    size = len(left)
    result = [[0.0 for _ in range(size)] for _ in range(size)]
    for row in range(size):
        out_row = result[row]
        for mid in range(size):
            factor = left[row][mid]
            if factor == 0.0:
                continue
            right_row = right[mid]
            for col in range(size):
                out_row[col] += factor * right_row[col]
    return result


def matrix_scale(matrix: list[list[float]], scale: float) -> list[list[float]]:
    return [[scale * value for value in row] for row in matrix]


def matrix_rank(matrix: list[list[float]], tol: float) -> int:
    work = [row[:] for row in matrix]
    row_count = len(work)
    col_count = len(work[0]) if row_count else 0
    rank = 0
    for col in range(col_count):
        pivot = None
        pivot_abs = tol
        for row in range(rank, row_count):
            value_abs = abs(work[row][col])
            if value_abs > pivot_abs:
                pivot = row
                pivot_abs = value_abs
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        pivot_value = work[rank][col]
        for idx in range(col, col_count):
            work[rank][idx] /= pivot_value
        for row in range(row_count):
            if row == rank:
                continue
            factor = work[row][col]
            if abs(factor) <= tol:
                continue
            for idx in range(col, col_count):
                work[row][idx] -= factor * work[rank][idx]
        rank += 1
        if rank == row_count:
            break
    return rank


def max_abs_matrix_diff(left: list[list[float]], right: list[list[float]]) -> float:
    return max(abs(a - b) for left_row, right_row in zip(left, right) for a, b in zip(left_row, right_row))


def max_abs_symmetric_defect(matrix: list[list[float]]) -> float:
    size = len(matrix)
    return max(abs(matrix[row][col] - matrix[col][row]) for row in range(size) for col in range(row + 1, size))


def spectral_projectors(adjacency: list[list[float]]) -> list[list[list[float]]]:
    size = len(adjacency)
    projectors = []
    for j, lambda_j in enumerate(LAMBDA_VALUES):
        projector = identity_matrix(size)
        denominator = 1.0
        for k, lambda_k in enumerate(LAMBDA_VALUES):
            if k == j:
                continue
            projector = matrix_multiply(projector, shifted_matrix(adjacency, lambda_k))
            denominator *= lambda_j - lambda_k
        projectors.append(matrix_scale(projector, 1.0 / denominator))
    return projectors


def families_by_aa(codons: list[str]) -> dict[str, list[str]]:
    families: dict[str, list[str]] = defaultdict(list)
    for codon in codons:
        families[CODON_TO_AA[codon]].append(codon)
    return dict(families)


def project_syn(vector: list[float], codons: list[str], families: dict[str, list[str]], index: dict[str, int]) -> list[float]:
    result = vector[:]
    for family_codons in families.values():
        mean = sum(vector[index[codon]] for codon in family_codons) / len(family_codons)
        for codon in family_codons:
            result[index[codon]] -= mean
    return result


def raw_vector(entries: dict[str, float], codons: list[str], index: dict[str, int]) -> list[float]:
    vector = [0.0 for _ in codons]
    for codon, value in entries.items():
        vector[index[codon]] = float(value)
    return vector


def bstar_templates(codons: list[str], index: dict[str, int], families: dict[str, list[str]]) -> list[dict[str, object]]:
    entries_by_name: list[tuple[str, dict[str, float]]] = [
        ("K_AAA", {"AAA": 1.0, "AAG": -1.0}),
        (
            "Arg_AGR",
            {"AGA": 1.0, "AGG": 1.0, "CGU": -0.25, "CGC": -0.25, "CGA": -0.25, "CGG": -0.25},
        ),
        ("Ile_AUA", {"AUA": 1.0, "AUU": -1.0, "AUC": -1.0}),
        (
            "Leu_CUN_vs_UUR",
            {"CUU": 0.25, "CUC": 0.25, "CUA": 0.25, "CUG": 0.25, "UUA": -0.5, "UUG": -0.5},
        ),
        ("Leu_UUA_vs_UUG", {"UUA": 1.0, "UUG": -1.0}),
        ("Ser_UCR_vs_AGY", {"UCA": 0.5, "UCG": 0.5, "AGU": -0.5, "AGC": -0.5}),
        ("Ser_UCA_vs_UCG", {"UCA": 1.0, "UCG": -1.0}),
        ("Thr_ACR_vs_ACY", {"ACA": 0.5, "ACG": 0.5, "ACU": -0.5, "ACC": -0.5}),
    ]

    f3_entries: dict[str, float] = {}
    for aa, family_codons in sorted(families.items(), key=lambda item: min(index[codon] for codon in item[1])):
        if aa == "*" or len(family_codons) == 1:
            continue
        ordered = sorted(family_codons, key=lambda codon: index[codon])
        f3_entries[ordered[0]] = f3_entries.get(ordered[0], 0.0) + 1.0
        f3_entries[ordered[-1]] = f3_entries.get(ordered[-1], 0.0) - 1.0
    entries_by_name.append(("f3_stress", f3_entries))

    templates = []
    for name, entries in entries_by_name:
        raw = raw_vector(entries, codons, index)
        projected = project_syn(raw, codons, families, index)
        support = [codon for codon in codons if abs(entries.get(codon, 0.0)) > 0.0]
        fiber_support: dict[str, list[str]] = defaultdict(list)
        for codon in support:
            fiber_support[CODON_TO_AA[codon]].append(codon)
        groups = [
            sorted(group_codons, key=lambda codon: index[codon])
            for _, group_codons in sorted(fiber_support.items(), key=lambda item: min(index[codon] for codon in item[1]))
        ]
        templates.append(
            {
                "name": name,
                "entries": entries,
                "support": support,
                "fiber_groups": groups,
                "vector": projected,
                "norm": vector_norm(projected),
            }
        )
    return templates


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def vector_norm(vector: list[float]) -> float:
    return math.sqrt(dot(vector, vector))


def modified_gram_schmidt(columns: list[list[float]], tol: float) -> list[list[float]]:
    basis: list[list[float]] = []
    for column in columns:
        working = column[:]
        for q in basis:
            coefficient = dot(q, working)
            if coefficient != 0.0:
                for idx, q_value in enumerate(q):
                    working[idx] -= coefficient * q_value
        norm = vector_norm(working)
        if norm <= tol:
            continue
        basis.append([value / norm for value in working])
    return basis


def base_orthonormal_characters() -> list[dict[str, float]]:
    return [
        {base: 0.5 for base in BASES},
        {"U": 1.0 / math.sqrt(2.0), "C": -1.0 / math.sqrt(2.0), "A": 0.0, "G": 0.0},
        {"U": 1.0 / math.sqrt(6.0), "C": 1.0 / math.sqrt(6.0), "A": -2.0 / math.sqrt(6.0), "G": 0.0},
        {"U": 1.0 / math.sqrt(12.0), "C": 1.0 / math.sqrt(12.0), "A": 1.0 / math.sqrt(12.0), "G": -3.0 / math.sqrt(12.0)},
    ]


def eigenspace_bases(codons: list[str]) -> list[list[list[float]]]:
    base_chars = base_orthonormal_characters()
    bases_by_level: list[list[list[float]]] = [[] for _ in range(4)]
    for labels in product(range(4), repeat=3):
        level = sum(label != 0 for label in labels)
        vector = [
            base_chars[labels[0]][codon[0]]
            * base_chars[labels[1]][codon[1]]
            * base_chars[labels[2]][codon[2]]
            for codon in codons
        ]
        bases_by_level[level].append(vector)
    return bases_by_level


def basis_projection_mass(vector: list[float], basis: list[list[float]]) -> float:
    return sum(dot(vector, basis_vector) ** 2 for basis_vector in basis)


def subspace_profile(q_basis: list[list[float]], bases_by_level: list[list[list[float]]]) -> list[float]:
    if not q_basis:
        return [0.0, 0.0, 0.0, 0.0]
    rank = len(q_basis)
    return [
        sum(basis_projection_mass(q, bases_by_level[level]) for q in q_basis) / rank
        for level in range(4)
    ]


def projector_profile(q_basis: list[list[float]], projectors: list[list[list[float]]]) -> list[float]:
    if not q_basis:
        return [0.0, 0.0, 0.0, 0.0]
    rank = len(q_basis)
    return [
        sum(projector_quadratic(q, projectors[level]) for q in q_basis) / rank
        for level in range(4)
    ]


def projector_quadratic(vector: list[float], projector: list[list[float]]) -> float:
    total = 0.0
    for row, row_values in enumerate(projector):
        row_sum = 0.0
        for col, value in enumerate(row_values):
            row_sum += value * vector[col]
        total += vector[row] * row_sum
    return total


def template_random_vector(
    template: dict[str, object],
    codons: list[str],
    index: dict[str, int],
    rng: random.Random,
) -> list[float]:
    vector = [0.0 for _ in codons]
    groups = template["fiber_groups"]
    assert isinstance(groups, list)
    for group in groups:
        assert isinstance(group, list)
        values = zero_sum_random_values(len(group), rng)
        for codon, value in zip(group, values):
            vector[index[codon]] = value
    return scale_to_norm(vector, float(template["norm"]))


def zero_sum_random_values(count: int, rng: random.Random) -> list[float]:
    if count < 2:
        return [0.0 for _ in range(count)]
    for _ in range(100):
        values = [rng.uniform(-1.0, 1.0) for _ in range(count)]
        mean = sum(values) / count
        centered = [value - mean for value in values]
        if vector_norm(centered) > MGS_TOL:
            return centered
    raise RuntimeError("could not sample a nonzero zero-sum contrast")


def scale_to_norm(vector: list[float], target_norm: float) -> list[float]:
    observed = vector_norm(vector)
    if observed <= MGS_TOL:
        return vector
    scale = target_norm / observed
    return [scale * value for value in vector]


def null_profile_values(
    templates: list[dict[str, object]],
    codons: list[str],
    index: dict[str, int],
    projectors: list[list[list[float]]],
    rng: random.Random,
) -> list[list[float]]:
    values = []
    for _ in range(N_NULL):
        columns = [template_random_vector(template, codons, index, rng) for template in templates]
        q_basis = modified_gram_schmidt(columns, MGS_TOL)
        values.append(projector_profile(q_basis, projectors))
    return values


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def sample_std(values: list[float], center: float) -> float:
    if len(values) < 2:
        return 0.0
    return math.sqrt(sum((value - center) ** 2 for value in values) / (len(values) - 1))


def tail_p_values(values: list[float], observed: float) -> tuple[float, float]:
    upper = (sum(value >= observed for value in values) + 1) / (len(values) + 1)
    lower = (sum(value <= observed for value in values) + 1) / (len(values) + 1)
    return upper, lower


def main() -> None:
    try:
        codons = codon_order()
        index = {codon: idx for idx, codon in enumerate(codons)}
        adjacency = adjacency_matrix(codons)
        edge_count = int(sum(sum(row) for row in adjacency) // 2)
        families = families_by_aa(codons)

        projectors = spectral_projectors(adjacency)
        identity = identity_matrix(len(codons))
        projector_sum = [[sum(projectors[level][row][col] for level in range(4)) for col in range(64)] for row in range(64)]
        projector_checks: list[dict[str, object]] = []
        ranks = []
        for level, projector in enumerate(projectors):
            rank = matrix_rank(projector, TOL)
            ranks.append(rank)
            idempotent = matrix_multiply(projector, projector)
            projector_checks.extend(
                [
                    check_row(
                        f"rank_E{level}",
                        rank == EIGENSPACE_DIMS[level],
                        observed=rank,
                        expected=EIGENSPACE_DIMS[level],
                    ),
                    check_row(
                        f"idempotent_E{level}",
                        max_abs_matrix_diff(idempotent, projector) <= 1.0e-7,
                        max_abs=round_float(max_abs_matrix_diff(idempotent, projector), 14),
                        tol=1.0e-7,
                    ),
                    check_row(
                        f"symmetric_E{level}",
                        max_abs_symmetric_defect(projector) <= 1.0e-9,
                        max_abs=round_float(max_abs_symmetric_defect(projector), 14),
                        tol=1.0e-9,
                    ),
                ]
            )

        templates = bstar_templates(codons, index, families)
        columns = [template["vector"] for template in templates]
        b_columns = []
        for column in columns:
            assert isinstance(column, list)
            b_columns.append(column)
        q_b = modified_gram_schmidt(b_columns, MGS_TOL)
        bases_by_level = eigenspace_bases(codons)
        t_profile = projector_profile(q_b, projectors)
        t_profile_from_basis = subspace_profile(q_b, bases_by_level)

        non_stop_zero = all(
            abs(template["vector"][index[codon]]) <= TOL
            for template in templates
            for codon in families["*"]
        )
        checks = [
            check_row("codon_order_len", len(codons) == 64, observed=len(codons), expected=64),
            check_row("standard_table_covers_codon_order", sorted(CODON_TO_AA) == sorted(codons), observed=len(CODON_TO_AA), expected=64),
            check_row("hamming_edges", edge_count == 288, observed=edge_count, expected=288),
            check_row("hamming_degree_9", all(sum(row) == 9.0 for row in adjacency), expected=9),
            check_row("projector_sum_identity", max_abs_matrix_diff(projector_sum, identity) <= 1.0e-8, max_abs=round_float(max_abs_matrix_diff(projector_sum, identity), 14), tol=1.0e-8),
            check_row("eigenspace_dims", ranks == list(EIGENSPACE_DIMS), observed=ranks, expected=list(EIGENSPACE_DIMS)),
            check_row("bstar_template_count", len(templates) == 9, observed=len(templates), expected=9),
            check_row("bstar_stop_coordinates_zero", non_stop_zero, stop_codons=families["*"]),
            check_row("rank_B", len(q_b) == 9, observed=len(q_b), expected=9),
            check_row("T_profile_sum", abs(sum(t_profile) - 1.0) <= 1.0e-8, observed=round_float(sum(t_profile), 14), expected=1.0),
            check_row(
                "orthonormal_tensor_basis_matches_polynomial_projectors",
                max(abs(left - right) for left, right in zip(t_profile, t_profile_from_basis)) <= 1.0e-8,
                max_abs=round_float(max(abs(left - right) for left, right in zip(t_profile, t_profile_from_basis)), 14),
                tol=1.0e-8,
            ),
        ]
        checks.extend(projector_checks)

        if not all(row["ok"] for row in checks):
            emit(
                "failed",
                eigenvalues=[int(value) for value in LAMBDA_VALUES],
                eigenspace_dims=ranks,
                rank_B=len(q_b),
                T_profile=[round_float(value) for value in t_profile],
                null_mean_profile=None,
                excess_D=None,
                upper_p=None,
                lower_p=None,
                null_z=None,
                alpha_bonferroni=round_float(ALPHA_BONFERRONI, 6),
                n_null=N_NULL,
                concentrated_eigenspaces=[],
                depleted_eigenspaces=[],
                checks=checks,
                reason="internal projector, codon-table, B*_Q6, or trace conservation check failed",
            )

        primary_rng = random.Random(stable_seed(PRIMARY_NULL_SEED))
        null_profiles = null_profile_values(templates, codons, index, projectors, primary_rng)
        null_by_level = [[profile[level] for profile in null_profiles] for level in range(4)]
        null_mean_profile = [mean(values) for values in null_by_level]
        null_std_profile = [sample_std(values, null_mean_profile[level]) for level, values in enumerate(null_by_level)]
        excess_d = [t_profile[level] - null_mean_profile[level] for level in range(4)]
        null_z = [
            excess_d[level] / null_std_profile[level] if null_std_profile[level] > 0.0 else math.inf
            for level in range(4)
        ]
        tail_pairs = [tail_p_values(null_by_level[level], t_profile[level]) for level in range(4)]
        upper_p = [pair[0] for pair in tail_pairs]
        lower_p = [pair[1] for pair in tail_pairs]

        concentrated_eigenspaces = [
            {
                "j": level,
                "lambda": int(LAMBDA_VALUES[level]),
                "D": round_float(excess_d[level]),
                "upper_p": round_float(upper_p[level]),
            }
            for level in range(1, 4)
            if excess_d[level] > 0.0 and upper_p[level] <= ALPHA_BONFERRONI
        ]
        depleted_eigenspaces = [
            {
                "j": level,
                "lambda": int(LAMBDA_VALUES[level]),
                "D": round_float(excess_d[level]),
                "lower_p": round_float(lower_p[level]),
            }
            for level in range(1, 4)
            if excess_d[level] < 0.0 and lower_p[level] <= ALPHA_BONFERRONI
        ]
        home_eigenspaces = [row for row in concentrated_eigenspaces if row["j"] in {1, 2}]

        if home_eigenspaces:
            status = "certified"
        elif not concentrated_eigenspaces and depleted_eigenspaces:
            status = "refuted"
        elif not concentrated_eigenspaces and not depleted_eigenspaces:
            status = "coincidence"
        else:
            status = "needs_derivation"

        concentration_text = ", ".join(
            f"E{row['j']} (lambda={row['lambda']}, D={row['D']}, upper_p={row['upper_p']})"
            for row in concentrated_eigenspaces
        ) or "none"
        depletion_text = ", ".join(
            f"E{row['j']} (lambda={row['lambda']}, D={row['D']}, lower_p={row['lower_p']})"
            for row in depleted_eigenspaces
        ) or "none"
        reason = (
            "Scoped spectral-localization verdict for B*_Q6: concentrated eigenspaces are "
            f"{concentration_text}; depleted eigenspaces are {depletion_text}. The matched null preserves "
            "each template's synonymous family/support/norm constraints, so these are excess-over-generic "
            "synonymous contrast effects. Any E3 depletion re-confirms the prior E3 refutation; this makes "
            "no causal, selection, or forcing-isomorphism claim."
        )

        emit(
            status,
            eigenvalues=[int(value) for value in LAMBDA_VALUES],
            eigenspace_dims=list(ranks),
            rank_B=len(q_b),
            T_profile=[round_float(value) for value in t_profile],
            null_mean_profile=[round_float(value) for value in null_mean_profile],
            excess_D=[round_float(value) for value in excess_d],
            upper_p=[round_float(value) for value in upper_p],
            lower_p=[round_float(value) for value in lower_p],
            null_z=[round_float(value) for value in null_z],
            alpha_bonferroni=round_float(ALPHA_BONFERRONI, 6),
            n_null=N_NULL,
            concentrated_eigenspaces=concentrated_eigenspaces,
            depleted_eigenspaces=depleted_eigenspaces,
            checks=checks,
            reason=reason,
        )
    except Exception as exc:
        emit(
            "failed",
            eigenvalues=[int(value) for value in LAMBDA_VALUES],
            eigenspace_dims=None,
            rank_B=None,
            T_profile=None,
            null_mean_profile=None,
            excess_D=None,
            upper_p=None,
            lower_p=None,
            null_z=None,
            alpha_bonferroni=round_float(ALPHA_BONFERRONI, 6),
            n_null=N_NULL,
            concentrated_eigenspaces=[],
            depleted_eigenspaces=[],
            checks=[check_row("exception_free", False, exception=type(exc).__name__, message=str(exc))],
            reason="experiment raised before a valid verdict could be computed",
        )


if __name__ == "__main__":
    main()

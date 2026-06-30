#!/usr/bin/env python3
"""Held-out cross-organism gate on the certified codon-E1 subspace."""
from __future__ import annotations

from collections import defaultdict
from itertools import product
import hashlib
import json
import math
from pathlib import Path
import random
import sys


EXPERIMENT_ID = "codon_e1_heldout_crossorganism_gate"
CLAIM_ID = "bridge.genetic_code.codon_e1_heldout_crossorganism_conservation"

BASES = ("U", "C", "A", "G")
N_NULL = 20000
N_BOOTSTRAP = 10000
TOL = 1.0e-9
MGS_TOL = 1.0e-10
NULL_SEED = "codon_e1_heldout_crossorganism_gate.global_synonymous_relabel.null"
BOOTSTRAP_SEED = "codon_e1_heldout_crossorganism_gate.cluster_bootstrap"

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
    sys.exit(0 if status in {"certified", "coincidence", "failed"} else 2)


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


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def sample_std(values: list[float], center: float) -> float:
    if len(values) < 2:
        return 0.0
    return math.sqrt(sum((value - center) ** 2 for value in values) / (len(values) - 1))


def percentile(values: list[float], q: float) -> float:
    ordered = sorted(values)
    if not ordered:
        raise ValueError("cannot take percentile of an empty list")
    pos = (len(ordered) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return ordered[lo]
    return ordered[lo] * (hi - pos) + ordered[hi] * (pos - lo)


def codon_order() -> list[str]:
    return ["".join(parts) for parts in product(BASES, repeat=3)]


def sense_codon_order() -> list[str]:
    return [codon for codon in codon_order() if CODON_TO_AA[codon] != "*"]


def families_by_aa(codons: list[str]) -> dict[str, list[str]]:
    families: dict[str, list[str]] = defaultdict(list)
    for codon in codons:
        families[CODON_TO_AA[codon]].append(codon)
    return dict(families)


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


def e1_character_basis(full_codons: list[str]) -> list[list[float]]:
    base_chars = base_orthonormal_characters()
    columns: list[list[float]] = []
    for labels in product(range(4), repeat=3):
        if sum(label != 0 for label in labels) != 1:
            continue
        columns.append(
            [
                base_chars[labels[0]][codon[0]]
                * base_chars[labels[1]][codon[1]]
                * base_chars[labels[2]][codon[2]]
                for codon in full_codons
            ]
        )
    return columns


def project_syn(vector: list[float], families: dict[str, list[str]], index: dict[str, int]) -> list[float]:
    result = vector[:]
    for family_codons in families.values():
        family_mean = sum(vector[index[codon]] for codon in family_codons) / len(family_codons)
        for codon in family_codons:
            result[index[codon]] -= family_mean
    return result


def max_abs_family_mean(vector: list[float], families: dict[str, list[str]], index: dict[str, int]) -> float:
    return max(
        abs(sum(vector[index[codon]] for codon in family_codons) / len(family_codons))
        for family_codons in families.values()
    )


def projector_matrix(q_basis: list[list[float]]) -> list[list[float]]:
    if not q_basis:
        return []
    size = len(q_basis[0])
    matrix = [[0.0 for _ in range(size)] for _ in range(size)]
    for q in q_basis:
        for row, q_row in enumerate(q):
            if q_row == 0.0:
                continue
            out_row = matrix[row]
            for col, q_col in enumerate(q):
                out_row[col] += q_row * q_col
    return matrix


def matrix_vector(matrix: list[list[float]], vector: list[float]) -> list[float]:
    return [sum(value * vector[col] for col, value in enumerate(row)) for row in matrix]


def matrix_multiply(left: list[list[float]], right: list[list[float]]) -> list[list[float]]:
    rows = len(left)
    cols = len(right[0]) if right else 0
    mids = len(right)
    result = [[0.0 for _ in range(cols)] for _ in range(rows)]
    for row in range(rows):
        for mid in range(mids):
            factor = left[row][mid]
            if factor == 0.0:
                continue
            for col in range(cols):
                result[row][col] += factor * right[mid][col]
    return result


def max_abs_matrix_diff(left: list[list[float]], right: list[list[float]]) -> float:
    return max(abs(a - b) for left_row, right_row in zip(left, right) for a, b in zip(left_row, right_row))


def max_abs_symmetric_defect(matrix: list[list[float]]) -> float:
    size = len(matrix)
    return max(abs(matrix[row][col] - matrix[col][row]) for row in range(size) for col in range(row + 1, size))


def projector_quadratic(vector: list[float], projector: list[list[float]]) -> float:
    projected = matrix_vector(projector, vector)
    return dot(vector, projected)


def basis_projector_quadratic(vector: list[float], q_basis: list[list[float]]) -> float:
    return sum(dot(vector, q) ** 2 for q in q_basis)


def build_b1_projector(
    full_codons: list[str],
    sense_codons: list[str],
    families: dict[str, list[str]],
    sense_index: dict[str, int],
) -> tuple[list[list[float]], list[list[float]], int]:
    full_index = {codon: idx for idx, codon in enumerate(full_codons)}
    columns: list[list[float]] = []
    for full_column in e1_character_basis(full_codons):
        restricted = [full_column[full_index[codon]] for codon in sense_codons]
        columns.append(project_syn(restricted, families, sense_index))
    q_basis = modified_gram_schmidt(columns, MGS_TOL)
    return projector_matrix(q_basis), q_basis, len(q_basis)


def panel_path() -> Path:
    return Path(__file__).resolve().parents[1] / "synced" / "codon_e1_heldout_panel.json"


def load_panel() -> dict[str, object]:
    with panel_path().open("r", encoding="utf-8") as handle:
        return json.load(handle)


def organism_residuals(
    panel: dict[str, object],
    sense_codons: list[str],
    families: dict[str, list[str]],
    sense_index: dict[str, int],
) -> tuple[list[dict[str, object]], float]:
    organisms = []
    max_family_mean = 0.0
    for entry in panel["organisms"]:
        assert isinstance(entry, dict)
        counts = entry["codon_counts_rna"]
        assert isinstance(counts, dict)
        total = int(entry["total_sense_codons"])
        if total <= 0:
            raw = [0.0 for _ in sense_codons]
        else:
            raw = [float(counts[codon]) / total for codon in sense_codons]
        residual = project_syn(raw, families, sense_index)
        max_family_mean = max(max_family_mean, max_abs_family_mean(residual, families, sense_index))
        organisms.append(
            {
                "organism_slug": entry["organism_slug"],
                "genus": entry["genus"],
                "total_sense_codons": total,
                "residual": residual,
                "residual_norm_sq": dot(residual, residual),
            }
        )
    return organisms, max_family_mean


def r_value(vector: list[float], norm_sq: float, q_basis: list[list[float]]) -> float:
    if norm_sq <= TOL:
        return math.nan
    return basis_projector_quadratic(vector, q_basis) / norm_sq


def genus_mean_r(
    organisms: list[dict[str, object]],
    q_basis: list[list[float]],
) -> tuple[dict[str, float], dict[str, list[float]]]:
    by_genus: dict[str, list[float]] = defaultdict(list)
    for organism in organisms:
        norm_sq = float(organism["residual_norm_sq"])
        if norm_sq <= TOL:
            continue
        genus = str(organism["genus"])
        by_genus[genus].append(r_value(organism["residual"], norm_sq, q_basis))  # type: ignore[arg-type]
    means = {genus: mean(values) for genus, values in sorted(by_genus.items())}
    return means, dict(by_genus)


def t_heldout_from_genus_means(per_genus: dict[str, float]) -> float:
    return mean(list(per_genus.values()))


def family_permutation(families: dict[str, list[str]], rng: random.Random) -> dict[str, str]:
    permutation: dict[str, str] = {}
    for family_codons in families.values():
        shuffled = family_codons[:]
        rng.shuffle(shuffled)
        for source, target in zip(family_codons, shuffled):
            permutation[source] = target
    return permutation


def apply_permutation(
    vector: list[float],
    permutation: dict[str, str],
    sense_codons: list[str],
    sense_index: dict[str, int],
) -> list[float]:
    out = [0.0 for _ in sense_codons]
    for source, target in permutation.items():
        out[sense_index[target]] = vector[sense_index[source]]
    return out


def relabeled_t(
    organisms: list[dict[str, object]],
    q_basis: list[list[float]],
    permutation: dict[str, str],
    sense_codons: list[str],
    sense_index: dict[str, int],
) -> float:
    relabeled: list[dict[str, object]] = []
    for organism in organisms:
        vector = apply_permutation(organism["residual"], permutation, sense_codons, sense_index)  # type: ignore[arg-type]
        relabeled.append(
            {
                "genus": organism["genus"],
                "residual": vector,
                "residual_norm_sq": dot(vector, vector),
            }
        )
    per_genus, _ = genus_mean_r(relabeled, q_basis)
    return t_heldout_from_genus_means(per_genus)


def null_distribution(
    organisms: list[dict[str, object]],
    q_basis: list[list[float]],
    families: dict[str, list[str]],
    sense_codons: list[str],
    sense_index: dict[str, int],
) -> tuple[list[float], float]:
    rng = random.Random(stable_seed(NULL_SEED))
    values = []
    max_relabel_family_mean = 0.0
    for draw in range(N_NULL):
        permutation = family_permutation(families, rng)
        if draw == 0 and organisms:
            relabeled = apply_permutation(organisms[0]["residual"], permutation, sense_codons, sense_index)  # type: ignore[arg-type]
            max_relabel_family_mean = max_abs_family_mean(relabeled, families, sense_index)
        values.append(relabeled_t(organisms, q_basis, permutation, sense_codons, sense_index))
    return values, max_relabel_family_mean


def bootstrap_lower95_excess(per_genus: dict[str, float], null_mean: float) -> float:
    rng = random.Random(stable_seed(BOOTSTRAP_SEED))
    genera = sorted(per_genus)
    count = len(genera)
    excess_values = []
    for _ in range(N_BOOTSTRAP):
        sampled = [per_genus[rng.choice(genera)] for _ in range(count)]
        excess_values.append(mean(sampled) - null_mean)
    return percentile(excess_values, 0.025)


def main() -> None:
    try:
        full_codons = codon_order()
        sense_codons = sense_codon_order()
        sense_index = {codon: idx for idx, codon in enumerate(sense_codons)}
        families = families_by_aa(sense_codons)

        panel = load_panel()
        organisms_raw = panel["organisms"]
        assert isinstance(organisms_raw, list)
        provenance = panel["provenance"]
        assert isinstance(provenance, dict)
        panel_codons = panel.get("sense_codon_order_rna")
        n_organisms = len(organisms_raw)
        genera = sorted({str(entry["genus"]) for entry in organisms_raw if isinstance(entry, dict)})

        panel_loaded_ok = (
            n_organisms == int(provenance.get("n_organisms", -1))
            and len(genera) == int(provenance.get("n_genera", -1))
            and n_organisms == 29
        )
        dna_to_rna_ok = all(
            isinstance(entry, dict)
            and isinstance(entry.get("codon_counts_rna"), dict)
            and all("T" not in codon and set(codon) <= set(BASES) for codon in entry["codon_counts_rna"])
            for entry in organisms_raw
        )
        codon_count_ok = (
            panel_codons == sense_codons
            and len(sense_codons) == 61
            and all(
                isinstance(entry, dict)
                and sorted(entry["codon_counts_rna"]) == sorted(sense_codons)
                and int(entry["total_sense_codons"]) == sum(int(entry["codon_counts_rna"][codon]) for codon in sense_codons)
                for entry in organisms_raw
            )
        )

        projector, q_basis, rank_b1 = build_b1_projector(full_codons, sense_codons, families, sense_index)
        projector_square = matrix_multiply(projector, projector)
        p_idempotent_defect = max_abs_matrix_diff(projector_square, projector)
        p_symmetric_defect = max_abs_symmetric_defect(projector)
        organisms, max_family_mean = organism_residuals(panel, sense_codons, families, sense_index)
        skipped = [str(item["organism_slug"]) for item in organisms if float(item["residual_norm_sq"]) <= TOL]

        checks = [
            check_row("panel_loaded", panel_loaded_ok, n_organisms=n_organisms, n_genera=len(genera)),
            check_row("dna_to_rna_ok", dna_to_rna_ok),
            check_row("61_sense_codons", codon_count_ok, observed=len(sense_codons), expected=61),
            check_row("B1 rank", rank_b1 > 0, rank_B1=rank_b1),
            check_row(
                "P_B1 idempotent+symmetric",
                p_idempotent_defect <= 1.0e-8 and p_symmetric_defect <= 1.0e-10,
                idempotent_max_abs=round_float(p_idempotent_defect, 14),
                symmetric_max_abs=round_float(p_symmetric_defect, 14),
            ),
            check_row(
                "d_resid4 synonymous-mean-zero",
                max_family_mean < 1.0e-12 and not skipped,
                max_abs_family_mean=round_float(max_family_mean, 14),
                skipped_zero_residual=skipped,
            ),
        ]

        per_genus, _ = genus_mean_r(organisms, q_basis)
        observed_t = t_heldout_from_genus_means(per_genus)
        null_values, max_relabel_family_mean = null_distribution(organisms, q_basis, families, sense_codons, sense_index)
        checks.append(
            check_row(
                "null_global_relabel_preserves_family",
                max_relabel_family_mean < 1.0e-12,
                max_abs_family_mean=round_float(max_relabel_family_mean, 14),
            )
        )

        null_mean = mean(null_values)
        null_std = sample_std(null_values, null_mean)
        null_z = (observed_t - null_mean) / null_std if null_std > 0.0 else math.inf
        one_sided_p = (sum(value >= observed_t for value in null_values) + 1) / (len(null_values) + 1)
        lower95_excess = bootstrap_lower95_excess(per_genus, null_mean)

        if not all(row["ok"] for row in checks):
            status = "failed"
        elif one_sided_p <= 0.01 and lower95_excess > 0.0:
            status = "certified"
        else:
            status = "coincidence"

        reason = (
            "This certifies only that d_resid4 has a conserved codon-E1 component across these "
            "organisms/clades; it does not certify Window6, because the oracle requires a new nonzero "
            "structural map to reopen Window6, not spectral-order matching. The panel is 29 organisms / "
            "18 genera, mostly bacteria, so the scope is limited; no causal or selection claim is made."
        )
        emit(
            status,
            n_organisms=n_organisms,
            n_genera=len(genera),
            rank_B1=rank_b1,
            T_heldout=round_float(observed_t),
            null_mean=round_float(null_mean),
            null_std=round_float(null_std),
            null_z=round_float(null_z),
            one_sided_p=round_float(one_sided_p),
            n_null=N_NULL,
            bootstrap_lower95_excess=round_float(lower95_excess),
            n_bootstrap=N_BOOTSTRAP,
            per_genus_mean_r={genus: round_float(value) for genus, value in per_genus.items()},
            checks=checks,
            reason=reason,
        )
    except Exception as exc:
        emit(
            "failed",
            n_organisms=None,
            n_genera=None,
            rank_B1=None,
            T_heldout=None,
            null_mean=None,
            null_std=None,
            null_z=None,
            one_sided_p=None,
            n_null=N_NULL,
            bootstrap_lower95_excess=None,
            n_bootstrap=N_BOOTSTRAP,
            per_genus_mean_r={},
            checks=[check_row("exception_free", False, exception=type(exc).__name__, message=str(exc))],
            reason="experiment raised before a valid verdict could be computed",
        )


if __name__ == "__main__":
    main()

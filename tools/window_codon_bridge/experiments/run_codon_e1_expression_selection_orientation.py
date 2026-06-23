#!/usr/bin/env python3
"""Codon-E1 expression-selection orientation concordance test.

This is not Window6 forcing and not a causal proof. B1 is frozen from the
standard-code H(3,4) first-order construction; expression data only enter after
the codon space and leave-one-genus directions are fixed.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import random
import sys
from typing import Any

import numpy as np

import _expr_e1_fetch_probe as fetch_probe


EXPERIMENT_ID = "codon_e1_expression_selection_orientation"
CLAIM_ID = "bridge.genetic_code.codon_e1_expression_selection_orientation"
N_PERMUTATIONS = int(os.environ.get("CODON_E1_EXPR_N_PERM", "2000"))
N_BOOTSTRAP = int(os.environ.get("CODON_E1_EXPR_N_BOOT", "400"))
MIN_SPECIES = 5
MIN_GENERA = 5
MIN_MATCHED_GENES = 800
MIN_SENSE_CODONS = 200_000
EPS_ABUNDANCE = 1.0e-6
RIDGE = 1.0e-8
TOL = 1.0e-10
MAX_NEWTON = 60
BETA_TOL = 1.0e-8
GRAD_TOL = 1.0e-6
NULL_SEED = "codon_e1_expression_selection_orientation.matched_null"
BOOTSTRAP_SEED = "codon_e1_expression_selection_orientation.pc1_bootstrap"
PC1_STABILITY_EIGENGAP_MIN = 1.05
PC1_STABILITY_SIGN_MIN = 0.90

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[2]
PANEL_CACHE_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "codon_e1_expression_selection_orientation_panel.json"
)

BASES = ("U", "C", "A", "G")


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status in {"certified", "coincidence"} else (3 if status == "needs_external" else 2))


def stable_seed(text: str) -> int:
    return int.from_bytes(hashlib.sha256(text.encode("utf-8")).digest()[:16], "big")


def round_float(value: float | None, digits: int = 12) -> float | None:
    if value is None:
        return None
    if not math.isfinite(value):
        return value
    out = round(float(value), digits)
    return 0.0 if out == -0.0 else out


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def percentile(values: list[float], q: float) -> float:
    ordered = sorted(values)
    pos = (len(ordered) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return ordered[lo]
    return ordered[lo] * (hi - pos) + ordered[hi] * (pos - lo)


def normal_two_sided_p(z: float) -> float:
    return math.erfc(abs(z) / math.sqrt(2.0))


def codon_order() -> list[str]:
    return ["".join(parts) for parts in __import__("itertools").product(BASES, repeat=3)]


CODON_TO_AA = fetch_probe.ncbi.CODON_TO_AA


def sense_codon_order() -> list[str]:
    return [codon for codon in codon_order() if CODON_TO_AA[codon] != "*"]


def families_by_aa(codons: list[str]) -> dict[str, list[str]]:
    families: dict[str, list[str]] = defaultdict(list)
    for codon in codons:
        families[CODON_TO_AA[codon]].append(codon)
    return dict(families)


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def norm(vector: list[float]) -> float:
    return math.sqrt(dot(vector, vector))


def chemical_character(character: str, base: str) -> int:
    values = {
        "R": {"A": 1, "G": 1, "C": -1, "U": -1},
        "W": {"A": 1, "U": 1, "C": -1, "G": -1},
        "K": {"U": 1, "G": 1, "C": -1, "A": -1},
    }
    return values[character][base]


def project_syn_fraction(vector: list[Fraction], families: dict[str, list[str]], index: dict[str, int]) -> list[Fraction]:
    out = vector[:]
    for family in families.values():
        family_mean = sum(vector[index[codon]] for codon in family) / Fraction(len(family), 1)
        for codon in family:
            out[index[codon]] -= family_mean
    return out


def project_syn_float(vector: list[float], families: dict[str, list[str]], index: dict[str, int]) -> list[float]:
    out = vector[:]
    for family in families.values():
        family_mean = sum(vector[index[codon]] for codon in family) / len(family)
        for codon in family:
            out[index[codon]] -= family_mean
    return out


def fraction_dot(left: list[Fraction], right: list[Fraction]) -> Fraction:
    return sum((a * b for a, b in zip(left, right)), Fraction(0, 1))


def fraction_mgs(columns: list[list[Fraction]]) -> list[list[Fraction]]:
    basis: list[list[Fraction]] = []
    for column in columns:
        working = column[:]
        for q in basis:
            denom = fraction_dot(q, q)
            if denom:
                coeff = fraction_dot(q, working) / denom
                if coeff:
                    working = [value - coeff * q_value for value, q_value in zip(working, q)]
        if any(value != 0 for value in working):
            basis.append(working)
    return basis


def build_b1_basis_exact(
    full_codons: list[str],
    sense_codons: list[str],
    families: dict[str, list[str]],
    sense_index: dict[str, int],
) -> list[list[Fraction]]:
    full_index = {codon: idx for idx, codon in enumerate(full_codons)}
    columns: list[list[Fraction]] = []
    for position in range(3):
        for character in ("R", "W", "K"):
            full = [Fraction(chemical_character(character, codon[position]), 1) for codon in full_codons]
            restricted = [full[full_index[codon]] for codon in sense_codons]
            columns.append(project_syn_fraction(restricted, families, sense_index))
    return fraction_mgs(columns)


def project_onto_fraction_basis(q_basis: list[list[Fraction]], vector: list[float]) -> list[float]:
    out = [0.0 for _ in vector]
    for q in q_basis:
        denom_f = fraction_dot(q, q)
        if denom_f == 0:
            continue
        denom = float(denom_f)
        coeff = sum(float(qv) * value for qv, value in zip(q, vector)) / denom
        if coeff:
            for idx, qv in enumerate(q):
                out[idx] += coeff * float(qv)
    return out


def b1_coordinates(q_basis: list[list[Fraction]], vector: list[float]) -> np.ndarray:
    coords = []
    for q in q_basis:
        denom = float(fraction_dot(q, q))
        coords.append(sum(float(qv) * value for qv, value in zip(q, vector)) / math.sqrt(denom))
    return np.asarray(coords, dtype=float)


def anticodon_to_codons(anticodon: str, mode: str = "tai_penalty") -> dict[str, float]:
    anti = anticodon.upper().replace("T", "U")
    if len(anti) != 3:
        return {}
    first = anti[0]
    if first == "A":
        options = {"U": 1.0}
    elif first == "C":
        options = {"G": 1.0}
    elif first == "G":
        options = {"C": 1.0, "U": 0.5 if mode == "tai_penalty" else 1.0}
    elif first == "U":
        options = {"A": 1.0, "G": 0.5 if mode == "tai_penalty" else 1.0}
    elif first == "I":
        options = {"A": 0.5, "C": 0.5, "U": 0.5}
    else:
        options = {}
    second = {"A": "U", "U": "A", "C": "G", "G": "C"}.get(anti[1])
    third = {"A": "U", "U": "A", "C": "G", "G": "C"}.get(anti[2])
    if not second or not third:
        return {}
    out: dict[str, float] = {}
    for codon3, weight in options.items():
        codon = third + second + codon3
        if CODON_TO_AA.get(codon) not in {None, "*"}:
            out[codon] = float(weight)
    return out


def supply_scores(anticodon_counts: dict[str, int], sense_codons: list[str]) -> dict[str, float]:
    raw = {codon: 0.0 for codon in sense_codons}
    for anticodon, count in anticodon_counts.items():
        for codon, weight in anticodon_to_codons(anticodon).items():
            if codon in raw:
                raw[codon] += int(count) * weight
    return {codon: math.log1p(value) for codon, value in raw.items()}


def load_or_build_panel() -> dict[str, object]:
    if PANEL_CACHE_PATH.exists():
        panel = json.loads(PANEL_CACHE_PATH.read_text(encoding="utf-8"))
        if int(panel.get("n_species", 0)) >= MIN_SPECIES:
            return panel
    probe = fetch_probe.build_fetch_probe(force_refresh=True, min_species=MIN_SPECIES)
    if str(probe.get("status")) != "fetchable":
        emit(
            "needs_external",
            reason=str(probe.get("reason")),
            fetch_probe={
                "n_usable": probe.get("n_usable"),
                "n_usable_genera": probe.get("n_usable_genera"),
                "attempts": probe.get("attempts"),
                "probe_cache_path": probe.get("probe_cache_path"),
                "panel_cache_path": probe.get("panel_cache_path"),
            },
            note="expression-selection orientation test only; not Window6 and not causal proof",
        )
    return json.loads(PANEL_CACHE_PATH.read_text(encoding="utf-8"))


def residualize_expression(organism: dict[str, object]) -> list[dict[str, object]]:
    genes = [dict(row) for row in organism["matched_genes"]]  # type: ignore[index]
    replicons = Counter(str(row.get("replicon", "")) for row in genes)
    kept_replicons = [rep for rep, count in sorted(replicons.items()) if count >= 20]
    columns = []
    y = []
    for row in genes:
        length = max(float(row["length_codons"]), 1.0)
        xs = [1.0, math.log(length), float(row["gc3"]), float(row["gc12"])]
        for rep in kept_replicons[1:]:
            xs.append(1.0 if str(row.get("replicon", "")) == rep else 0.0)
        columns.append(xs)
        y.append(math.log(float(row["abundance_ppm"]) + EPS_ABUNDANCE))
    xmat = np.asarray(columns, dtype=float)
    yvec = np.asarray(y, dtype=float)
    coef, *_ = np.linalg.lstsq(xmat, yvec, rcond=None)
    resid = yvec - xmat @ coef
    sd = float(np.std(resid))
    if sd <= TOL:
        sd = 1.0
    for idx, row in enumerate(genes):
        row["expr_resid"] = float((resid[idx] - float(np.mean(resid))) / sd)
    return genes


def aggregate_species_usage(
    genes: list[dict[str, object]],
    sense_codons: list[str],
    families: dict[str, list[str]],
    sense_index: dict[str, int],
) -> list[float]:
    totals = {codon: 0 for codon in sense_codons}
    total = 0
    for gene in genes:
        counts = gene["codon_counts_rna"]
        assert isinstance(counts, dict)
        for codon, value in counts.items():
            if codon in totals:
                totals[codon] += int(value)
                total += int(value)
    usage = [totals[codon] / max(total, 1) for codon in sense_codons]
    return project_syn_float(usage, families, sense_index)


def pc1_from_vectors(vectors: list[np.ndarray], anchor: np.ndarray) -> tuple[np.ndarray, float, list[float]]:
    if not vectors:
        return anchor.copy(), 0.0, []
    mat = np.vstack(vectors)
    mat = mat - np.mean(mat, axis=0, keepdims=True)
    cov = mat.T @ mat / max(len(vectors), 1)
    vals, vecs = np.linalg.eigh(cov)
    order = np.argsort(vals)[::-1]
    vals = vals[order]
    vec = vecs[:, order[0]]
    if float(np.dot(vec, anchor)) < 0.0:
        vec = -vec
    gap = float(vals[0] / max(vals[1], 1.0e-15)) if len(vals) > 1 and vals[0] > 0.0 else 0.0
    return vec, gap, [float(v) for v in vals]


def pc1_stability(
    species_vectors: dict[str, np.ndarray],
    species_genus: dict[str, str],
    anchor: np.ndarray,
) -> dict[str, object]:
    genera = sorted(set(species_genus.values()))
    rng = random.Random(stable_seed(BOOTSTRAP_SEED))
    gaps = []
    signs = 0
    total = 0
    for _ in range(N_BOOTSTRAP):
        sampled_genera = [rng.choice(genera) for _ in genera]
        vectors = [
            species_vectors[species]
            for genus in sampled_genera
            for species, g in species_genus.items()
            if g == genus
        ]
        vec, gap, _vals = pc1_from_vectors(vectors, anchor)
        gaps.append(gap)
        signs += 1 if float(np.dot(vec, anchor)) >= 0.0 else 0
        total += 1
    return {
        "eigengap": round_float(percentile(gaps, 0.5)),
        "eigengap_lower05": round_float(percentile(gaps, 0.05)),
        "bootstrap_sign_consistency": round_float(signs / max(total, 1)),
        "n_bootstrap": N_BOOTSTRAP,
        "passed": bool(percentile(gaps, 0.5) >= PC1_STABILITY_EIGENGAP_MIN and signs / max(total, 1) >= PC1_STABILITY_SIGN_MIN),
    }


def family_center(values: dict[str, float], families: dict[str, list[str]]) -> dict[str, float]:
    out = dict(values)
    for codons in families.values():
        m = mean([float(values[codon]) for codon in codons])
        for codon in codons:
            out[codon] = float(values[codon]) - m
    return out


def alignment_scores(
    q_basis: list[list[Fraction]],
    v_coords: np.ndarray,
    sense_codons: list[str],
    families: dict[str, list[str]],
    sense_index: dict[str, int],
) -> dict[str, float]:
    raw: dict[str, float] = {}
    for codon in sense_codons:
        one = [0.0 for _ in sense_codons]
        one[sense_index[codon]] = 1.0
        centered = project_syn_float(one, families, sense_index)
        raw[codon] = float(np.dot(b1_coordinates(q_basis, centered), v_coords))
    return family_center(raw, families)


def baseline_offsets(genes: list[dict[str, object]], families: dict[str, list[str]]) -> dict[str, float]:
    totals: Counter[str] = Counter()
    for gene in genes:
        counts = gene["codon_counts_rna"]
        assert isinstance(counts, dict)
        for codon, value in counts.items():
            totals[codon] += int(value)
    offsets: dict[str, float] = {}
    for codons in families.values():
        denom = sum(totals[codon] + 0.5 for codon in codons)
        for codon in codons:
            offsets[codon] = math.log((totals[codon] + 0.5) / denom)
    return offsets


def optimality_scores(genes: list[dict[str, object]], families: dict[str, list[str]]) -> dict[str, float]:
    ordered = sorted(genes, key=lambda row: float(row["expr_resid"]))
    n = len(ordered)
    low = ordered[: max(1, n // 4)]
    high = ordered[-max(1, n // 4) :]
    scores: dict[str, float] = {}
    for codons in families.values():
        high_counts = Counter()
        low_counts = Counter()
        for gene in high:
            counts = gene["codon_counts_rna"]
            assert isinstance(counts, dict)
            for codon in codons:
                high_counts[codon] += int(counts.get(codon, 0))
        for gene in low:
            counts = gene["codon_counts_rna"]
            assert isinstance(counts, dict)
            for codon in codons:
                low_counts[codon] += int(counts.get(codon, 0))
        high_total = sum(high_counts.values()) + 0.5 * len(codons)
        low_total = sum(low_counts.values()) + 0.5 * len(codons)
        for codon in codons:
            scores[codon] = math.log((high_counts[codon] + 0.5) / high_total) - math.log((low_counts[codon] + 0.5) / low_total)
    return family_center(scores, families)


def standardize_feature(values: dict[str, float]) -> dict[str, float]:
    vals = list(values.values())
    m = mean(vals)
    sd = math.sqrt(sum((v - m) ** 2 for v in vals) / max(len(vals), 1))
    if sd <= TOL:
        sd = 1.0
    return {key: (value - m) / sd for key, value in values.items()}


def build_strata(
    organisms: list[dict[str, object]],
    genes_by_species: dict[str, list[dict[str, object]]],
    e1_scores: dict[str, dict[str, float]],
    families: dict[str, list[str]],
    tai_by_species: dict[str, dict[str, float]],
    positive: bool = False,
) -> list[dict[str, object]]:
    strata: list[dict[str, object]] = []
    for org in organisms:
        species = str(org["assembly_accession"])
        genus = str(org["genus"])
        genes = genes_by_species[species]
        offsets = baseline_offsets(genes, families)
        opt_scores = standardize_feature(optimality_scores(genes, families))
        e1 = standardize_feature(e1_scores[species])
        tai = standardize_feature(family_center(tai_by_species[species], families))
        for gene in genes:
            expr = float(gene["expr_resid"])
            counts = gene["codon_counts_rna"]
            assert isinstance(counts, dict)
            for aa, codons in families.items():
                if len(codons) <= 1:
                    continue
                y = np.asarray([int(counts.get(codon, 0)) for codon in codons], dtype=float)
                total = float(np.sum(y))
                if total <= 0.0:
                    continue
                primary = opt_scores if positive else e1
                x = np.asarray(
                    [
                        [
                            expr * primary[codon],
                            1.0 if codon[2] in {"G", "C"} else 0.0,
                            tai[codon],
                            expr * (1.0 if codon[2] in {"G", "C"} else 0.0),
                            expr * tai[codon],
                        ]
                        for codon in codons
                    ],
                    dtype=float,
                )
                strata.append(
                    {
                        "genus": genus,
                        "species": species,
                        "aa": aa,
                        "codons": codons,
                        "codon_indices": [fetch_probe.ncbi.sense_codon_order_rna().index(codon) for codon in codons],
                        "counts": y,
                        "x": x,
                        "offset": np.asarray([offsets[codon] for codon in codons], dtype=float),
                        "gene_gc3": float(gene["gc3"]),
                        "gene_length": float(gene["length_codons"]),
                        "expr_rank": expr,
                        "expr": expr,
                    }
                )
    by_genus = Counter(str(row["genus"]) for row in strata)
    for row in strata:
        row["weight"] = 1.0 / max(by_genus[str(row["genus"])], 1)
    return strata


def prepare_design(strata: list[dict[str, object]], species_order: list[str]) -> dict[str, np.ndarray | list[str] | int]:
    starts: list[int] = []
    lengths: list[int] = []
    counts: list[float] = []
    offsets: list[float] = []
    weights: list[float] = []
    genus_ids: list[int] = []
    species_ids: list[int] = []
    codon_ids: list[int] = []
    exprs: list[float] = []
    x_rows: list[list[float]] = []
    genus_order = sorted({str(row["genus"]) for row in strata})
    genus_index = {genus: idx for idx, genus in enumerate(genus_order)}
    species_index = {species: idx for idx, species in enumerate(species_order)}
    cursor = 0
    for row in strata:
        x = row["x"]
        y = row["counts"]
        off = row["offset"]
        codon_indices = row["codon_indices"]
        assert isinstance(x, np.ndarray) and isinstance(y, np.ndarray) and isinstance(off, np.ndarray)
        assert isinstance(codon_indices, list)
        n = len(y)
        starts.append(cursor)
        lengths.append(n)
        cursor += n
        counts.extend(float(v) for v in y)
        offsets.extend(float(v) for v in off)
        weights.extend([float(row["weight"])] * n)
        genus_ids.extend([genus_index[str(row["genus"])]] * n)
        species_ids.extend([species_index[str(row["species"])]] * n)
        codon_ids.extend(int(v) for v in codon_indices)
        exprs.extend([float(row["expr"])] * n)
        x_rows.extend(x.tolist())
    group_totals = np.add.reduceat(np.asarray(counts, dtype=float), np.asarray(starts, dtype=int))
    alt_group_totals = np.repeat(group_totals, np.asarray(lengths, dtype=int))
    return {
        "x": np.asarray(x_rows, dtype=float),
        "counts": np.asarray(counts, dtype=float),
        "offset": np.asarray(offsets, dtype=float),
        "weight": np.asarray(weights, dtype=float),
        "genus_id": np.asarray(genus_ids, dtype=int),
        "species_id": np.asarray(species_ids, dtype=int),
        "codon_id": np.asarray(codon_ids, dtype=int),
        "expr": np.asarray(exprs, dtype=float),
        "starts": np.asarray(starts, dtype=int),
        "lengths": np.asarray(lengths, dtype=int),
        "group_total_by_alt": alt_group_totals,
        "n_groups": len(starts),
        "n_genera": len(genus_order),
        "genus_order": genus_order,
    }


def fit_design(
    design: dict[str, np.ndarray | list[str] | int],
    start: np.ndarray | None = None,
    x0_override: np.ndarray | None = None,
) -> dict[str, object]:
    x = np.asarray(design["x"], dtype=float).copy()
    if x0_override is not None:
        x[:, 0] = x0_override
    counts = np.asarray(design["counts"], dtype=float)
    offset = np.asarray(design["offset"], dtype=float)
    weight = np.asarray(design["weight"], dtype=float)
    starts = np.asarray(design["starts"], dtype=int)
    lengths = np.asarray(design["lengths"], dtype=int)
    group_total = np.asarray(design["group_total_by_alt"], dtype=float)
    genus_id = np.asarray(design["genus_id"], dtype=int)
    n_genera = int(design["n_genera"])
    p = x.shape[1]
    beta = np.zeros(p, dtype=float) if start is None else start.astype(float).copy()
    group_index = np.repeat(np.arange(int(design["n_groups"]), dtype=int), lengths)

    for _ in range(MAX_NEWTON):
        eta = offset + x @ beta
        group_max = np.maximum.reduceat(eta, starts)
        exp_eta = np.exp(eta - group_max[group_index])
        denom = np.add.reduceat(exp_eta, starts)
        probs = exp_eta / denom[group_index]
        resid = counts - group_total * probs
        grad = x.T @ (weight * resid)
        wx = weight * group_total * probs
        info = x.T @ (x * wx[:, None])
        xbar = np.zeros((int(design["n_groups"]), p), dtype=float)
        for col in range(p):
            xbar[:, col] = np.add.reduceat(probs * x[:, col], starts)
        group_weight_total = np.add.reduceat(weight * group_total * probs, starts)
        info -= xbar.T @ (xbar * group_weight_total[:, None])
        info += RIDGE * np.eye(p)
        try:
            step = np.linalg.solve(info, grad)
        except np.linalg.LinAlgError:
            step = np.linalg.pinv(info) @ grad
        beta += step
        if float(np.max(np.abs(step))) < BETA_TOL or float(np.max(np.abs(grad))) < GRAD_TOL:
            break

    eta = offset + x @ beta
    group_max = np.maximum.reduceat(eta, starts)
    exp_eta = np.exp(eta - group_max[group_index])
    denom = np.add.reduceat(exp_eta, starts)
    probs = exp_eta / denom[group_index]
    resid = counts - group_total * probs
    grad = x.T @ (weight * resid)
    wx = weight * group_total * probs
    info = x.T @ (x * wx[:, None])
    xbar = np.zeros((int(design["n_groups"]), p), dtype=float)
    for col in range(p):
        xbar[:, col] = np.add.reduceat(probs * x[:, col], starts)
    group_weight_total = np.add.reduceat(weight * group_total * probs, starts)
    info -= xbar.T @ (xbar * group_weight_total[:, None])
    info += RIDGE * np.eye(p)
    inv_info = np.linalg.pinv(info)
    scores = np.zeros((n_genera, p), dtype=float)
    for col in range(p):
        scores[:, col] = np.bincount(genus_id, weights=weight * resid * x[:, col], minlength=n_genera)
    meat = scores.T @ scores
    robust = inv_info @ meat @ inv_info
    se = np.sqrt(np.maximum(np.diag(robust), 0.0))
    z = float(beta[0] / se[0]) if se[0] > 0.0 else math.inf
    lse = group_max + np.log(denom)
    loglik = float(np.sum(weight * (counts * eta - group_total * probs * lse[group_index])))
    return {
        "beta": beta,
        "se": se,
        "z": z,
        "p": normal_two_sided_p(z),
        "ci": (float(beta[0] - 1.96 * se[0]), float(beta[0] + 1.96 * se[0])),
        "loglik": loglik,
        "max_abs_grad": float(np.max(np.abs(grad))),
        "n_strata": int(design["n_groups"]),
        "n_clusters": n_genera,
    }


def logsumexp(values: np.ndarray) -> float:
    m = float(np.max(values))
    return m + math.log(float(np.sum(np.exp(values - m))))


def fit_conditional_logit(strata: list[dict[str, object]], start: np.ndarray | None = None) -> dict[str, object]:
    p = 5
    beta = np.zeros(p, dtype=float) if start is None else start.astype(float).copy()
    for _ in range(MAX_NEWTON):
        grad = np.zeros(p, dtype=float)
        info = np.zeros((p, p), dtype=float)
        for row in strata:
            x = row["x"]
            counts = row["counts"]
            offset = row["offset"]
            weight = float(row["weight"])
            total = float(np.sum(counts))
            eta = offset + x @ beta
            probs = np.exp(eta - logsumexp(eta))
            xbar = probs @ x
            grad += weight * (counts @ x - total * xbar)
            centered = x - xbar
            info += weight * total * (centered.T @ (centered * probs[:, None]))
        info = info + RIDGE * np.eye(p)
        try:
            step = np.linalg.solve(info, grad)
        except np.linalg.LinAlgError:
            step = np.linalg.pinv(info) @ grad
        beta += step
        if float(np.max(np.abs(step))) < BETA_TOL or float(np.max(np.abs(grad))) < GRAD_TOL:
            break

    grad = np.zeros(p, dtype=float)
    info = np.zeros((p, p), dtype=float)
    cluster_scores: dict[str, np.ndarray] = defaultdict(lambda: np.zeros(p, dtype=float))
    loglik = 0.0
    for row in strata:
        x = row["x"]
        counts = row["counts"]
        offset = row["offset"]
        weight = float(row["weight"])
        total = float(np.sum(counts))
        eta = offset + x @ beta
        lse = logsumexp(eta)
        probs = np.exp(eta - lse)
        xbar = probs @ x
        score = weight * (counts @ x - total * xbar)
        grad += score
        cluster_scores[str(row["genus"])] += score
        centered = x - xbar
        info += weight * total * (centered.T @ (centered * probs[:, None]))
        loglik += weight * float(counts @ eta - total * lse)
    info = info + RIDGE * np.eye(p)
    inv_info = np.linalg.pinv(info)
    meat = np.zeros((p, p), dtype=float)
    for score in cluster_scores.values():
        meat += np.outer(score, score)
    robust = inv_info @ meat @ inv_info
    se = np.sqrt(np.maximum(np.diag(robust), 0.0))
    z = float(beta[0] / se[0]) if se[0] > 0.0 else math.inf
    return {
        "beta": beta,
        "se": se,
        "z": z,
        "p": normal_two_sided_p(z),
        "ci": (float(beta[0] - 1.96 * se[0]), float(beta[0] + 1.96 * se[0])),
        "loglik": loglik,
        "max_abs_grad": float(np.max(np.abs(grad))),
        "n_strata": len(strata),
        "n_clusters": len(cluster_scores),
    }


def permute_e1_scores(
    e1_scores: dict[str, dict[str, float]],
    families: dict[str, list[str]],
    rng: random.Random,
) -> dict[str, dict[str, float]]:
    out: dict[str, dict[str, float]] = {}
    for species, scores in e1_scores.items():
        shuffled_scores = dict(scores)
        for codons in families.values():
            by_gc: dict[str, list[str]] = defaultdict(list)
            for codon in codons:
                by_gc["GC" if codon[2] in {"G", "C"} else "AU"].append(codon)
            for group in by_gc.values():
                values = [shuffled_scores[codon] for codon in group]
                rng.shuffle(values)
                for codon, value in zip(group, values):
                    shuffled_scores[codon] = value
        out[species] = shuffled_scores
    return out


def matched_null(
    design: dict[str, np.ndarray | list[str] | int],
    e1_scores: dict[str, dict[str, float]],
    species_order: list[str],
    sense_codons: list[str],
    families: dict[str, list[str]],
    observed_beta: float,
    start: np.ndarray,
) -> tuple[float, dict[str, object]]:
    rng = random.Random(stable_seed(NULL_SEED))
    species_id = np.asarray(design["species_id"], dtype=int)
    codon_id = np.asarray(design["codon_id"], dtype=int)
    expr = np.asarray(design["expr"], dtype=float)
    values = []
    for _ in range(N_PERMUTATIONS):
        perm_scores = permute_e1_scores(e1_scores, families, rng)
        per_species = []
        for species in species_order:
            vals = standardize_feature(perm_scores[species])
            per_species.append(np.asarray([vals[codon] for codon in sense_codons], dtype=float))
        score_matrix = np.vstack(per_species)
        x0 = expr * score_matrix[species_id, codon_id]
        fit = fit_design(design, start=start, x0_override=x0)
        values.append(float(fit["beta"][0]))
    p = (sum(value >= observed_beta for value in values) + 1) / (len(values) + 1)
    return p, {
        "n_permutations": N_PERMUTATIONS,
        "seed": stable_seed(NULL_SEED),
        "mean": round_float(mean(values)),
        "q95": round_float(percentile(values, 0.95)),
        "q99": round_float(percentile(values, 0.99)),
    }


def per_genus_beta(strata: list[dict[str, object]], species_order: list[str]) -> dict[str, float]:
    out: dict[str, float] = {}
    for genus in sorted({str(row["genus"]) for row in strata}):
        count = max(sum(str(r["genus"]) == genus for r in strata), 1)
        subset = [dict(row, weight=1.0 / count) for row in strata if str(row["genus"]) == genus]
        if subset:
            out[genus] = float(fit_design(prepare_design(subset, species_order))["beta"][0])
    return out


def main() -> None:
    full_codons = codon_order()
    sense_codons = sense_codon_order()
    sense_index = {codon: idx for idx, codon in enumerate(sense_codons)}
    families = families_by_aa(sense_codons)
    q_basis = build_b1_basis_exact(full_codons, sense_codons, families, sense_index)
    rank_b1 = len(q_basis)

    panel = load_or_build_panel()
    organisms = [row for row in panel.get("organisms", []) if isinstance(row, dict)]
    usable = [
        org
        for org in organisms
        if int(org.get("match_meta", {}).get("n_matched_genes", 0)) >= MIN_MATCHED_GENES
        and int(org.get("match_meta", {}).get("total_sense_codons", 0)) >= MIN_SENSE_CODONS
    ]
    n_genera = len({str(org["genus"]) for org in usable})
    if len(usable) < MIN_SPECIES or n_genera < MIN_GENERA:
        emit(
            "needs_external",
            reason="yield audit did not produce enough matched species/genera above threshold",
            fetch_probe={
                "panel_cache_path": str(PANEL_CACHE_PATH),
                "n_species": len(usable),
                "n_genera": n_genera,
                "attempts": json.loads(fetch_probe.PROBE_CACHE_PATH.read_text(encoding="utf-8")).get("attempts")
                if fetch_probe.PROBE_CACHE_PATH.exists()
                else None,
            },
            note="expression-selection orientation test only; not Window6 and not causal proof",
        )

    genes_by_species: dict[str, list[dict[str, object]]] = {}
    species_vectors: dict[str, np.ndarray] = {}
    species_genus: dict[str, str] = {}
    tai_by_species: dict[str, dict[str, float]] = {}
    for org in usable:
        species = str(org["assembly_accession"])
        genes = residualize_expression(org)
        genes_by_species[species] = genes
        residual = aggregate_species_usage(genes, sense_codons, families, sense_index)
        species_vectors[species] = b1_coordinates(q_basis, project_onto_fraction_basis(q_basis, residual))
        species_genus[species] = str(org["genus"])
        anticodons = org["trna_anticodon_counts_rna"]
        assert isinstance(anticodons, dict)
        tai_by_species[species] = supply_scores({str(k): int(v) for k, v in anticodons.items()}, sense_codons)

    anchor = np.mean(np.vstack(list(species_vectors.values())), axis=0)
    anchor_norm = float(np.linalg.norm(anchor))
    if anchor_norm <= TOL:
        anchor = np.ones(rank_b1, dtype=float) / math.sqrt(rank_b1)
    else:
        anchor = anchor / anchor_norm
    stability = pc1_stability(species_vectors, species_genus, anchor)

    e1_scores: dict[str, dict[str, float]] = {}
    pc1_by_species: dict[str, dict[str, object]] = {}
    for org in usable:
        species = str(org["assembly_accession"])
        genus = str(org["genus"])
        training = [vec for sp, vec in species_vectors.items() if species_genus[sp] != genus]
        v, gap, vals = pc1_from_vectors(training, anchor)
        e1_scores[species] = alignment_scores(q_basis, v, sense_codons, families, sense_index)
        pc1_by_species[species] = {
            "heldout_genus": genus,
            "eigengap": round_float(gap),
            "eigenvalues": [round_float(value) for value in vals],
            "n_training_species": len(training),
            "anchor_dot": round_float(float(np.dot(v, anchor))),
        }

    strata = build_strata(usable, genes_by_species, e1_scores, families, tai_by_species)
    species_order = [str(org["assembly_accession"]) for org in usable]
    design = prepare_design(strata, species_order)
    fit = fit_design(design)
    positive_strata = build_strata(usable, genes_by_species, e1_scores, families, tai_by_species, positive=True)
    positive_design = prepare_design(positive_strata, species_order)
    positive_fit = fit_design(positive_design)
    p_null, null_meta = matched_null(
        design,
        e1_scores,
        species_order,
        sense_codons,
        families,
        float(fit["beta"][0]),
        np.asarray(fit["beta"], dtype=float),
    )

    beta = float(fit["beta"][0])
    p = float(fit["p"])
    ci = fit["ci"]
    assert isinstance(ci, tuple)
    positive_passed = float(positive_fit["beta"][0]) > 0.0 and float(positive_fit["p"]) <= 0.01
    controls_ok = True
    pc1_ok = bool(stability["passed"])
    significant = beta > 0.0 and p <= 0.01 and p_null <= 0.01 and ci[0] > 0.0
    if positive_passed and significant and controls_ok and pc1_ok:
        status = "certified"
    elif positive_passed and beta > 0.0 and p <= 0.01 and (p_null > 0.01 or ci[0] <= 0.0):
        status = "coincidence"
    else:
        status = "refuted"

    controls = [
        "species_by_codon baseline offsets within amino-acid family",
        "expression residualized on log_CDS_length, GC3, GC12, and replicon indicators",
        "codon GC3 main effect",
        "tRNA/tAI-style supply main effect",
        "expression_by_GC3 interaction",
        "expression_by_tRNA_supply interaction",
        "genus-cluster equal weighting",
    ]
    per_genus = per_genus_beta(strata, species_order)
    yield_audit = [
        {
            "assembly_accession": org["assembly_accession"],
            "organism": org["organism"],
            "genus": org["genus"],
            "taxid": org["taxid"],
            "matched_gene_count": int(org["match_meta"]["n_matched_genes"]),
            "sense_codon_count": int(org["match_meta"]["total_sense_codons"]),
            "match_method_counts": org["match_meta"]["match_method_counts"],
        }
        for org in usable
    ]
    emit(
        status,
        beta_e1xexpr=round_float(beta),
        p=round_float(p),
        ci=[round_float(float(ci[0])), round_float(float(ci[1]))],
        robust_se=round_float(float(fit["se"][0])),
        p_matched_null=round_float(p_null),
        matched_null=null_meta,
        positive_control={
            "beta_synonymous_usage_bias_xexpr": round_float(float(positive_fit["beta"][0])),
            "p": round_float(float(positive_fit["p"])),
            "ci": [
                round_float(float(positive_fit["ci"][0])),  # type: ignore[index]
                round_float(float(positive_fit["ci"][1])),  # type: ignore[index]
            ],
            "passed": bool(positive_passed),
        },
        pc1_stability=stability,
        pc1_leave_one_genus=pc1_by_species,
        per_genus={genus: round_float(value) for genus, value in per_genus.items()},
        n_species=len(usable),
        n_genus=n_genera,
        n_matched_genes_total=sum(int(org["match_meta"]["n_matched_genes"]) for org in usable),
        n_sense_codons_total=sum(int(org["match_meta"]["total_sense_codons"]) for org in usable),
        rank_B1=rank_b1,
        controls_included=controls,
        yield_audit=yield_audit,
        preprocessing={
            "epsilon_abundance": EPS_ABUNDANCE,
            "null_seed": stable_seed(NULL_SEED),
            "bootstrap_seed": stable_seed(BOOTSTRAP_SEED),
            "B1_construction": "exact Fraction first-order R/W/K H(3,4) characters, sense restriction, synonymous mean removal; projected to float coordinates for PC1 and logits",
            "PC1_anchor": "all-panel mean B1-projected species usage vector; used only to fix PC1 sign",
        },
        model={
            "type": "aggregated conditional multinomial logit on species, amino-acid-family, gene choice sets",
            "primary_coefficient": "expression_residual times leave-one-genus E1 codon-alignment score",
            "n_strata": fit["n_strata"],
            "n_clusters": fit["n_clusters"],
            "max_abs_grad": round_float(float(fit["max_abs_grad"])),
        },
        panel_cache_path=str(PANEL_CACHE_PATH),
        generated_at=now_iso(),
        note="codon-E1 selection-mechanism candidate test: expression-selection orientation concordance only; not Window6 and not causal proof",
    )


if __name__ == "__main__":
    main()

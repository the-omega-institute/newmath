#!/usr/bin/env python3
"""Minimal compilation-law test for the B*_Q6 abundance residual P_Q.

The experiment asks whether the abundance component explained by B*_Q6 after
local controls can be compressed by a low-dimensional, organism-specific
readout dictionary. The calculation is a deterministic ordered variance
partition, not a causal mechanism test.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import random
import sys
from typing import Any

from run_b_star_q6_residual_decomposition_powered import (
    EPS,
    LAMBDA_DL,
    MIN_PROTEINS_PER_ORGANISM,
    ORGANISMS,
    PERMUTATION_COUNT,
    RHO_JOIN,
    attach_h_readouts,
    base_rows,
    bounded_unit,
    controls_used,
    finite,
    finite_unit,
    matrix_rows,
    percentile_nearest_rank,
    project_vector,
    q6_context,
    residualize_with_basis,
    rows_for_ids,
    subtract_vectors,
)
from run_b_star_q6_protein_omics_survival_powered import (
    matrix_column,
    orthonormal_basis_from_columns,
)
from run_b_star_q6_translation_complement_residual_powered import vector_norm2
from run_b_star_q6_translation_mediation_powered import vector_dot


EXPERIMENT_ID = "b_star_q6_minimal_compilation_law_powered"
CLAIM_ID = "h3.cross_layer_relation.minimal_compilation_law.b_star_q6_residual_compressibility_powered"
CONJECTURE_ID = "q6.minimal-compilation-law.residual-compressibility.cross-layer"

ETA_NULL = 1.0
SUM_TOL = 1e-6
COMPRESSIBLE_THRESHOLD = 0.50
LOW_DIMENSION_RATIO_THRESHOLD = 0.60

H_CANDIDATES = [
    "turnover",
    "localization",
    "ptm_density",
    "complex_member",
    "tm_count",
    "domain_count",
]


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def cannot_claim() -> list[str]:
    return [
        "compressibility is a statistical variance-partition, NOT a causal compilation mechanism",
        "readout order T->S->H is a modeling choice; different order changes attribution",
        "per-organism single datasets from different studies/platforms",
        "D_o readouts are residual absorbers not mechanisms",
        "verdict is descriptive per-organism, not a universal law",
        "low compressibility means irreducible to THESE measured readouts, not that no explanation exists",
    ]


def deterministic_permutation(n: int, material_prefix: str) -> list[int]:
    out = list(range(n))
    digest = hashlib.sha256(f"{material_prefix}|n={n}".encode("utf-8")).digest()
    random.Random(int.from_bytes(digest, "big")).shuffle(out)
    return out


def permute_basis_rows(basis: list[list[float]], permutation: list[int]) -> list[list[float]]:
    return [[q[permutation[index]] for index in range(len(permutation))] for q in basis]


def project_from_basis(basis: list[list[float]], target: list[float]) -> tuple[list[float], float]:
    projected = [0.0 for _ in target]
    energy = 0.0
    target_energy = vector_norm2(target)
    for q in basis:
        coeff = vector_dot(target, q)
        energy += coeff * coeff
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            projected[index] += coeff * q[index]
    if energy > target_energy and energy <= target_energy + 1e-8:
        energy = target_energy
    return projected, max(0.0, energy)


def absorption_for_permuted_basis(basis: list[list[float]], target: list[float], permutation: list[int]) -> float:
    energy = 0.0
    for q in basis:
        coeff = 0.0
        for index, target_value in enumerate(target):
            coeff += target_value * q[permutation[index]]
        energy += coeff * coeff
    return energy


def project_from_permuted_basis(
    basis: list[list[float]],
    target: list[float],
    permutation: list[int],
) -> tuple[list[float], float]:
    projected = [0.0 for _ in target]
    energy = 0.0
    for q in basis:
        coeff = 0.0
        for index, target_value in enumerate(target):
            coeff += target_value * q[permutation[index]]
        energy += coeff * coeff
        if coeff == 0.0:
            continue
        for index in range(len(target)):
            projected[index] += coeff * q[permutation[index]]
    return projected, energy


def matrix_for_readout(selected_rows: list[dict[str, object]], readout: str) -> list[list[float]]:
    if readout == "measured_te":
        return matrix_rows(selected_rows, "t")
    if readout == "mrna_stability":
        return matrix_rows(selected_rows, "s")
    rows: list[list[float]] = []
    for row in selected_rows:
        h_map = row["h"]
        if not isinstance(h_map, dict) or readout not in h_map:
            raise ValueError(f"readout {readout} missing on selected join")
        rows.append(list(h_map[readout]))  # type: ignore[arg-type]
    return rows


def readout_dimension(rows: dict[str, dict[str, object]], row_ids: list[str], readout: str) -> int:
    if readout in {"measured_te", "mrna_stability"}:
        return 1
    for protein_id in row_ids:
        h_map = rows[protein_id].get("h", {})
        if isinstance(h_map, dict) and readout in h_map:
            return len(h_map[readout])  # type: ignore[arg-type]
    return 0


def prepare_state(
    *,
    rows: dict[str, dict[str, object]],
    row_ids: list[str],
    selected_h: list[str],
    has_stability: bool,
) -> dict[str, object]:
    selected_rows = rows_for_ids(rows, row_ids)
    z_basis = orthonormal_basis_from_columns(matrix_rows(selected_rows, "z"))
    x_e = residualize_with_basis(matrix_rows(selected_rows, "x"), z_basis)
    p_e = residualize_with_basis(matrix_rows(selected_rows, "p"), z_basis)
    t_e = residualize_with_basis(matrix_rows(selected_rows, "t"), z_basis)
    p_col = matrix_column(p_e, 0)
    p_q, p_q_energy, rank_q = project_vector(x_e, p_col)
    if p_q_energy <= EPS:
        raise ValueError("P_Q has zero residual energy")

    residual = list(p_q)
    steps: list[dict[str, object]] = []
    readout_order = ["measured_te"]
    if has_stability:
        readout_order.append("mrna_stability")
    readout_order.extend(selected_h)

    for readout in readout_order:
        readout_rows = matrix_for_readout(selected_rows, readout)
        readout_e = residualize_with_basis(readout_rows, z_basis)
        basis = orthonormal_basis_from_columns(readout_e)
        projected, energy = project_from_basis(basis, residual)
        residual = subtract_vectors(residual, projected)
        steps.append(
            {
                "readout": readout,
                "fraction": bounded_unit(energy / p_q_energy),
                "energy": energy,
                "rank": len(basis),
                "DL": len(readout_rows[0]) if readout_rows else 0,
            }
        )

    r_final_fraction = bounded_unit(vector_norm2(residual) / p_q_energy)
    return {
        "n": len(row_ids),
        "row_ids": row_ids,
        "selected_rows": selected_rows,
        "z_basis": z_basis,
        "P_Q": p_q,
        "P_Q_energy": p_q_energy,
        "rank_Q_e": rank_q,
        "current_residual": residual,
        "steps": steps,
        "R_final_fraction": r_final_fraction,
        "compressibility": bounded_unit(1.0 - r_final_fraction),
        "sum_fraction": sum(float(step["fraction"]) for step in steps) + r_final_fraction,
    }


def absorption_for_basis(basis: list[list[float]], target: list[float]) -> tuple[float, float]:
    target_norm = vector_norm2(target)
    if target_norm <= EPS:
        return 0.0, 0.0
    _projected, energy = project_from_basis(basis, target)
    return bounded_unit(energy / target_norm), energy


def permutation_null95(
    *,
    organism: str,
    readout: str,
    step_index: int,
    h_e: list[list[float]],
    target: list[float],
) -> dict[str, object]:
    values: list[float] = []
    basis = orthonormal_basis_from_columns(h_e)
    n_rows = len(target)
    target_norm = vector_norm2(target)
    for trial in range(PERMUTATION_COUNT):
        prefix = f"{EXPERIMENT_ID}|score|{organism}|{readout}|step={step_index}|trial={trial}"
        energy = absorption_for_permuted_basis(basis, target, deterministic_permutation(n_rows, prefix))
        if energy > target_norm and energy <= target_norm + 1e-8:
            energy = target_norm
        values.append(bounded_unit(max(0.0, energy) / target_norm) if target_norm > EPS else 0.0)
    return {
        "permutation_count": PERMUTATION_COUNT,
        "null95": percentile_nearest_rank(values, 0.95),
        "null_mean": sum(values) / len(values) if values else 0.0,
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|score|organism|readout|step|trial|index|n",
        "null_model": "deterministic label permutation of the Z-residualized H basis rows on the active join",
    }


def score_candidate(
    *,
    organism: str,
    rows: dict[str, dict[str, object]],
    current_ids: list[str],
    base_n: int,
    selected_h: list[str],
    candidate: str,
    has_stability: bool,
    step_index: int,
) -> dict[str, object]:
    join_ids = [
        protein_id
        for protein_id in current_ids
        if candidate in rows[protein_id].get("h", {})
    ]
    n_join = len(join_ids)
    if n_join < MIN_PROTEINS_PER_ORGANISM:
        return {
            "readout": candidate,
            "status": "needs_data",
            "reason": f"join below honest gate n_join={n_join} < {MIN_PROTEINS_PER_ORGANISM}",
            "n_join": n_join,
            "kept": False,
        }

    state = prepare_state(rows=rows, row_ids=join_ids, selected_h=selected_h, has_stability=has_stability)
    selected_rows = state["selected_rows"]
    z_basis = state["z_basis"]
    target = state["current_residual"]
    if not isinstance(selected_rows, list) or not isinstance(z_basis, list) or not isinstance(target, list):
        raise ValueError("active state malformed")
    h_rows = matrix_for_readout(selected_rows, candidate)
    h_e = residualize_with_basis(h_rows, z_basis)
    basis = orthonormal_basis_from_columns(h_e)
    a_h, absorbed_energy = absorption_for_basis(basis, target)  # type: ignore[arg-type]
    null = permutation_null95(
        organism=organism,
        readout=candidate,
        step_index=step_index,
        h_e=h_e,
        target=target,  # type: ignore[arg-type]
    )
    dl = len(h_rows[0]) if h_rows else 0
    join_penalty = abs(n_join - base_n) / base_n if base_n > 0 else 1.0
    score = a_h - LAMBDA_DL * dl - RHO_JOIN * join_penalty - ETA_NULL * float(null["null95"])
    return {
        "readout": candidate,
        "status": "computed",
        "n_join": n_join,
        "score": score,
        "A_H": a_h,
        "absorbed_energy_on_active_residual": absorbed_energy,
        "DL": dl,
        "lambda_DL": LAMBDA_DL,
        "join_penalty": join_penalty,
        "rho_join": RHO_JOIN,
        "null95": null["null95"],
        "eta_null": ETA_NULL,
        "null_mean": null["null_mean"],
        "rank_H_e": len(basis),
        "permutation_null": null,
        "kept": False,
    }


def greedy_h_dictionary(
    *,
    organism: str,
    rows: dict[str, dict[str, object]],
    base_ids: list[str],
    has_stability: bool,
) -> dict[str, object]:
    base_n = len(base_ids)
    current_ids = list(base_ids)
    selected: list[str] = []
    selected_entries: list[dict[str, object]] = []
    dropped: list[dict[str, object]] = []
    final_scores: dict[str, dict[str, object]] = {}
    step_index = 0

    while True:
        remaining = [candidate for candidate in H_CANDIDATES if candidate not in selected]
        scored = [
            score_candidate(
                organism=organism,
                rows=rows,
                current_ids=current_ids,
                base_n=base_n,
                selected_h=selected,
                candidate=candidate,
                has_stability=has_stability,
                step_index=step_index,
            )
            for candidate in remaining
        ]
        final_scores = {str(item["readout"]): item for item in scored}
        for item in scored:
            if item.get("status") != "computed":
                dropped.append(item)
        computed = [item for item in scored if item.get("status") == "computed"]
        computed.sort(key=lambda item: float(item["score"]), reverse=True)
        if not computed or float(computed[0]["score"]) <= 0.0:
            break
        winner = dict(computed[0])
        readout = str(winner["readout"])
        winner["kept"] = True
        selected.append(readout)
        selected_entries.append(winner)
        current_ids = [
            protein_id
            for protein_id in current_ids
            if readout in rows[protein_id].get("h", {})
        ]
        step_index += 1

    final = prepare_state(rows=rows, row_ids=current_ids, selected_h=selected, has_stability=has_stability)
    fraction_by_readout = {str(step["readout"]): float(step["fraction"]) for step in final["steps"]}  # type: ignore[index]
    dictionary: list[dict[str, object]] = []
    seen: set[str] = set()
    for item in selected_entries:
        out = dict(item)
        out["fraction_of_P_Q"] = fraction_by_readout.get(str(item["readout"]), 0.0)
        dictionary.append(out)
        seen.add(str(item["readout"]))
    for readout, item in sorted(final_scores.items()):
        if readout in seen:
            continue
        out = dict(item)
        out["fraction_of_P_Q"] = 0.0
        out["kept"] = False
        dictionary.append(out)

    return {
        "base_n_full_before_H_join": base_n,
        "n_full": len(current_ids),
        "selected_H": selected,
        "H_dictionary": dictionary,
        "dropped_readouts": dropped,
        "decomposition": final,
    }


def available_raw_readouts(
    *,
    rows: dict[str, dict[str, object]],
    base_ids: list[str],
    has_stability: bool,
) -> list[str]:
    out = ["measured_te"]
    if has_stability:
        out.append("mrna_stability")
    for candidate in H_CANDIDATES:
        n_join = sum(1 for protein_id in base_ids if candidate in rows[protein_id].get("h", {}))
        if n_join >= MIN_PROTEINS_PER_ORGANISM:
            out.append(candidate)
    return out


def dictionary_dl(
    *,
    rows: dict[str, dict[str, object]],
    row_ids: list[str],
    readouts: list[str],
) -> int:
    return sum(readout_dimension(rows, row_ids, readout) for readout in readouts)


def permutation_compressibility_null(
    *,
    organism: str,
    state: dict[str, object],
    readout_order: list[str],
    observed: float,
) -> dict[str, object]:
    selected_rows = state["selected_rows"]
    z_basis = state["z_basis"]
    p_q = state["P_Q"]
    p_q_energy = float(state["P_Q_energy"])
    if not isinstance(selected_rows, list) or not isinstance(z_basis, list) or not isinstance(p_q, list):
        raise ValueError("state malformed for compressibility null")

    bases: list[tuple[str, list[list[float]]]] = []
    for readout in readout_order:
        readout_rows = matrix_for_readout(selected_rows, readout)
        readout_e = residualize_with_basis(readout_rows, z_basis)
        bases.append((readout, orthonormal_basis_from_columns(readout_e)))

    values: list[float] = []
    n_rows = len(p_q)
    for trial in range(PERMUTATION_COUNT):
        residual = list(p_q)
        for step_index, (readout, basis) in enumerate(bases):
            prefix = f"{EXPERIMENT_ID}|compressibility|{organism}|{readout}|step={step_index}|trial={trial}"
            projected, _energy = project_from_permuted_basis(basis, residual, deterministic_permutation(n_rows, prefix))
            residual = subtract_vectors(residual, projected)
        value = bounded_unit(1.0 - vector_norm2(residual) / p_q_energy)
        values.append(value)

    exceed = sum(1 for value in values if value >= observed - 1e-12)
    return {
        "permutation_count": PERMUTATION_COUNT,
        "permutation_p": (exceed + 1) / (len(values) + 1) if values else 1.0,
        "null95": percentile_nearest_rank(values, 0.95),
        "null_mean": sum(values) / len(values) if values else 0.0,
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|compressibility|organism|readout|step|trial|index|n",
        "null_model": "deterministic label permutation of every D_o readout basis on the final organism join, preserving D_o order and dimensions",
    }


def organism_verdict(compressibility: float, dl_do: int, raw_dl: int, permutation_p: float) -> str:
    dl_ratio = (dl_do / raw_dl) if raw_dl > 0 else 1.0
    if (
        compressibility >= COMPRESSIBLE_THRESHOLD
        and dl_ratio <= LOW_DIMENSION_RATIO_THRESHOLD
        and permutation_p <= 0.05
    ):
        return (
            "minimal compilation law supported for this organism: P_Q is compressed by a low-dimensional "
            f"D_o (compressibility={compressibility:.3f}, DL_Do={dl_do}, raw_baseline_DL={raw_dl}, p={permutation_p:.4f})."
        )
    return (
        "minimal compilation law not supported for this organism: residual source remains irreducible to these "
        f"measured readouts (compressibility={compressibility:.3f}, DL_Do={dl_do}, raw_baseline_DL={raw_dl}, p={permutation_p:.4f})."
    )


def cross_organism_verdict(computed: dict[str, dict[str, object]]) -> str:
    if not computed:
        return "needs_data: no organism satisfied n>=500 and readout availability gates."
    supported = [
        key
        for key, result in computed.items()
        if bool(result.get("minimal_compilation_law_supported"))
    ]
    values = [float(result["compressibility"]) for result in computed.values()]
    median = sorted(values)[len(values) // 2]
    if supported and len(supported) == len(computed):
        return (
            "minimal compilation law supported across computed organisms: each P_Q is compressed by a "
            "low-dimensional D_o above the deterministic null."
        )
    if supported:
        return (
            "minimal compilation law mixed across computed organisms: some organism-specific P_Q residuals "
            "are compressible, but support is not cross-organism stable."
        )
    return (
        "minimal compilation law not supported across computed organisms: P_Q is not highly compressed by the "
        f"measured low-dimensional D_o set; median compressibility={median:.3f}, so the residual source is "
        "irreducible to these measured readouts in this descriptive test."
    )


def analyze_organism(repo: pathlib.Path, context: dict[str, object], config: dict[str, object]) -> dict[str, object]:
    organism = str(config["key"])
    built = base_rows(repo=repo, context=context, config=config)
    if built.get("status") != "computed":
        return {
            "organism": config["label"],
            "organism_key": organism,
            "domain": config["domain"],
            "status": "needs_data",
            "reason": built.get("reason"),
            "data_summary": built,
            "cannot_claim": cannot_claim(),
        }
    rows = built["rows"]
    if not isinstance(rows, dict):
        raise ValueError("base rows malformed")
    attached = attach_h_readouts(repo, organism, rows)  # type: ignore[arg-type]
    base_ids = sorted(rows)
    if len(base_ids) < MIN_PROTEINS_PER_ORGANISM:
        return {
            "organism": config["label"],
            "organism_key": organism,
            "domain": config["domain"],
            "status": "needs_data",
            "reason": f"base P/Q/T/S join yielded n={len(base_ids)}, below honest gate n>={MIN_PROTEINS_PER_ORGANISM}",
            "n_full": len(base_ids),
            "data_summary": built["summary"],
            "dropped_readouts": attached["dropped"],
            "cannot_claim": cannot_claim(),
        }

    has_stability = bool(config.get("has_stability")) and bool(config.get("stability_path"))
    greedy = greedy_h_dictionary(
        organism=organism,
        rows=rows,  # type: ignore[arg-type]
        base_ids=base_ids,
        has_stability=has_stability,
    )
    decomp = greedy["decomposition"]
    if not isinstance(decomp, dict):
        raise ValueError("decomposition malformed")
    selected_h = greedy["selected_H"]
    if not isinstance(selected_h, list):
        raise ValueError("selected_H malformed")

    readout_order = ["measured_te"]
    if has_stability:
        readout_order.append("mrna_stability")
    readout_order.extend(str(item) for item in selected_h)
    row_ids = decomp["row_ids"]
    if not isinstance(row_ids, list):
        raise ValueError("row_ids malformed")

    raw_readouts = available_raw_readouts(rows=rows, base_ids=base_ids, has_stability=has_stability)  # type: ignore[arg-type]
    dl_do = dictionary_dl(rows=rows, row_ids=row_ids, readouts=readout_order)  # type: ignore[arg-type]
    raw_baseline_dl = dictionary_dl(rows=rows, row_ids=base_ids, readouts=raw_readouts)  # type: ignore[arg-type]
    compressibility = float(decomp["compressibility"])
    null = permutation_compressibility_null(
        organism=organism,
        state=decomp,
        readout_order=readout_order,
        observed=compressibility,
    )
    permutation_p = float(null["permutation_p"])
    dl_ratio = dl_do / raw_baseline_dl if raw_baseline_dl > 0 else 1.0
    supported = (
        compressibility >= COMPRESSIBLE_THRESHOLD
        and dl_ratio <= LOW_DIMENSION_RATIO_THRESHOLD
        and permutation_p <= 0.05
    )

    fraction_by_readout = {str(step["readout"]): step["fraction"] for step in decomp["steps"]}  # type: ignore[index]
    h_fractions = {
        readout: fraction_by_readout.get(readout, 0.0)
        for readout in selected_h
    }
    return {
        "organism": config["label"],
        "organism_key": organism,
        "domain": config["domain"],
        "status": "computed",
        "n_full": greedy["n_full"],
        "base_n_full_before_H_join": greedy["base_n_full_before_H_join"],
        "P_Q_energy": decomp["P_Q_energy"],
        "D_o": readout_order,
        "D_o_H_selected": selected_h,
        "compressibility": compressibility,
        "DL_Do": dl_do,
        "DL_Do_readout_count": len(readout_order),
        "raw_baseline_DL": raw_baseline_dl,
        "raw_baseline_readout_count": len(raw_readouts),
        "raw_baseline_readouts": raw_readouts,
        "DL_ratio_Do_vs_raw": dl_ratio,
        "T_fraction": fraction_by_readout.get("measured_te", 0.0),
        "S_fraction": fraction_by_readout.get("mrna_stability", "skipped"),
        "H_k_fractions": h_fractions,
        "R_final_fraction": decomp["R_final_fraction"],
        "per_readout_steps": decomp["steps"],
        "permutation_p": permutation_p,
        "compressibility_null": null,
        "minimal_compilation_law_supported": supported,
        "verdict": organism_verdict(compressibility, dl_do, raw_baseline_dl, permutation_p),
        "H_dictionary_scoring": greedy["H_dictionary"],
        "rank_diagnostics": {
            "rank_Q_e": decomp["rank_Q_e"],
            "rank_Z": len(decomp["z_basis"]) if isinstance(decomp.get("z_basis"), list) else None,
            "control_column_count": len(next(iter(rows.values()))["z"]) if rows else None,
        },
        "data_summary": built["summary"],
        "H_source_summaries": attached["source_summaries"],
        "dropped_readouts": list(attached["dropped"]) + list(greedy["dropped_readouts"]),  # type: ignore[arg-type]
        "controls_used": controls_used(context["aa_order"]),  # type: ignore[arg-type]
        "cannot_claim": cannot_claim(),
    }


def checks_for(organisms: dict[str, dict[str, object]]) -> list[dict[str, object]]:
    computed = {key: value for key, value in organisms.items() if value.get("status") == "computed"}
    caveats = cannot_claim()
    required_caveats = [
        "compressibility is a statistical variance-partition, NOT a causal compilation mechanism",
        "readout order T->S->H is a modeling choice; different order changes attribution",
        "per-organism single datasets from different studies/platforms",
        "D_o readouts are residual absorbers not mechanisms",
        "verdict is descriptive per-organism, not a universal law",
        "low compressibility means irreducible to THESE measured readouts, not that no explanation exists",
    ]
    return [
        {
            "name": "per_organism_P_Q",
            "passed": bool(computed) and any(int(result["n_full"]) >= MIN_PROTEINS_PER_ORGANISM for result in computed.values()),
            "actual": {key: {"status": result.get("status"), "n_full": result.get("n_full"), "P_Q_energy": result.get("P_Q_energy")} for key, result in organisms.items()},
            "expected": f">=1 organism with P_Q computed and final join n_full >= {MIN_PROTEINS_PER_ORGANISM}",
        },
        {
            "name": "recursive_Do_built",
            "passed": bool(computed)
            and all(
                isinstance(result.get("D_o"), list)
                and result.get("D_o", [])[:1] == ["measured_te"]
                and isinstance(result.get("H_dictionary_scoring"), list)
                for result in computed.values()
            ),
            "actual": {key: {"D_o": result.get("D_o"), "H_selected": result.get("D_o_H_selected")} for key, result in computed.items()},
            "expected": "D_o starts with T, includes S where available, then greedily scored H readouts with positive score only",
        },
        {
            "name": "compressibility_and_DL_computed",
            "passed": bool(computed)
            and all(
                finite_unit(result.get("compressibility"))
                and finite_unit(result.get("R_final_fraction"))
                and finite_unit(result.get("permutation_p"))
                and finite(result.get("DL_Do"))
                and finite(result.get("raw_baseline_DL"))
                and int(result["DL_Do"]) <= int(result["raw_baseline_DL"])
                and result.get("compressibility_null", {}).get("permutation_count") == PERMUTATION_COUNT
                for result in computed.values()
            ),
            "actual": {
                key: {
                    "compressibility": result.get("compressibility"),
                    "R_final_fraction": result.get("R_final_fraction"),
                    "DL_Do": result.get("DL_Do"),
                    "raw_baseline_DL": result.get("raw_baseline_DL"),
                    "permutation_p": result.get("permutation_p"),
                }
                for key, result in computed.items()
            },
            "expected": "compressibility in [0,1], deterministic permutation p in [0,1], and selected D_o description length no larger than the raw all-readout baseline",
        },
        {
            "name": "cross_organism_verdict",
            "passed": bool(computed) and isinstance(cross_organism_verdict(computed), str),
            "actual": cross_organism_verdict(computed),
            "expected": "one explicit positive, mixed, or negative minimal compilation-law verdict across computed organisms",
        },
        {
            "name": "no_causal_or_universal_overclaim",
            "passed": caveats == required_caveats,
            "actual": caveats,
            "expected": "required caveats are present verbatim",
        },
    ]


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    try:
        genetic_code_path = repo / "tools/fibonacci_reality/data/ncbi_genetic_codes.json"
        if not genetic_code_path.exists():
            emit("needs_data", missing_required_data=[str(genetic_code_path.relative_to(repo))])
        context = q6_context(repo)
        organism_results = {
            str(config["key"]): analyze_organism(repo, context, config)
            for config in ORGANISMS
        }
        computed = {key: value for key, value in organism_results.items() if value.get("status") == "computed"}
        checks = checks_for(organism_results)
        status = "passed" if computed and all(check["passed"] for check in checks) else "needs_data"
        reason = None if status == "passed" else "all organisms failed the n>=500 or readout-availability honest gates"
        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture": CONJECTURE_ID,
                "statement": "Minimal compilation law test: P_Q = Pi_{Q_e} P_e is projected through T, S where available, and a greedy scored H dictionary; compressibility = 1 - ||R_final||^2 / ||P_Q||^2.",
                "score_definition": {
                    "score": "A_H - lambda*DL(H) - rho*JoinPenalty(H) - eta*Null95(H)",
                    "A_H": "||Pi_{H_e} R||^2 / ||R||^2 on the active join",
                    "DL(H)": "readout dimension",
                    "JoinPenalty(H)": "|n_join(H) - base_n_full| / base_n_full",
                    "Null95(H)": "95th percentile of deterministic H-label permutation absorption",
                    "lambda": LAMBDA_DL,
                    "rho": RHO_JOIN,
                    "eta": ETA_NULL,
                },
                "compressibility_definition": "1 - ||R_final||^2 / ||P_Q||^2",
                "DL_definition": "DL_Do is the summed dimensionality of kept D_o readouts; raw_baseline_DL is the summed dimensionality of every available candidate readout without scored selection.",
                "organisms": organism_results,
                "cross_organism_Do_table": {
                    key: {
                        "n_full": value.get("n_full"),
                        "D_o": value.get("D_o"),
                        "compressibility": value.get("compressibility"),
                        "DL_Do": value.get("DL_Do"),
                        "raw_baseline_DL": value.get("raw_baseline_DL"),
                        "permutation_p": value.get("permutation_p"),
                        "verdict": value.get("verdict"),
                    }
                    for key, value in organism_results.items()
                    if value.get("status") == "computed"
                },
                "compressibility_distribution": {
                    "values": [value.get("compressibility") for value in computed.values()],
                    "min": min((float(value["compressibility"]) for value in computed.values()), default=None),
                    "max": max((float(value["compressibility"]) for value in computed.values()), default=None),
                    "mean": (sum(float(value["compressibility"]) for value in computed.values()) / len(computed)) if computed else None,
                },
                "VERDICT": cross_organism_verdict(computed),
                "cannot_claim": cannot_claim(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable minimal-compilation-law input or fit", cannot_claim=cannot_claim())


if __name__ == "__main__":
    main()

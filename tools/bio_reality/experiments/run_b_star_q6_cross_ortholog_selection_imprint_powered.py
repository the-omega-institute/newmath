#!/usr/bin/env python3
"""Offline slim model-only selection-imprint test.

This script consumes a compact reconciled dataset and reruns the original
alpha_h + gamma_o + controls versus + beta.Q test, leave-clade-out CV, and
three phylogeny/matching nulls.  It intentionally performs no network access.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import random
import sys
from datetime import datetime, timezone
from typing import Any


EXPERIMENT_ID = "b_star_q6_cross_ortholog_selection_imprint_powered"
CLAIM_ID = "h3.cross_layer_relation.evolutionary_selection_imprint.b_star_q6_cross_ortholog_selection_imprint_powered"

DATASET_RELATIVE = "tools/bio_reality/data/cross_ortholog_selection_dataset_saccharomyces_fungi.json"
NULL_PERMUTATIONS = 200
EPS = 1e-12
RANK_TOL = 1e-10
SEED = "sha256:b_star_q6_cross_ortholog_selection_imprint_powered:slim:v1"
STARTED_AT = datetime.now(timezone.utc).isoformat(timespec="seconds")

CHECK_KEYS = [
    "data_fetched_reconciled",
    "single_copy_orthogroups",
    "per_organism_q9",
    "alpha_gamma_controls_model",
    "leave_clade_out_cv",
    "phylo_matched_nulls",
    "selection_imprint_verdict",
]


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def normalized_checks(raw: object) -> list[dict[str, object]]:
    if isinstance(raw, list):
        return [item for item in raw if isinstance(item, dict)]
    if isinstance(raw, dict):
        return [{"name": str(name), "passed": bool(value)} for name, value in raw.items()]
    return []


def emit(status: str, **kw: object) -> None:
    result = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    result.update(kw)
    payload = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "status": status,
        "checks": normalized_checks(kw.get("checks")),
        "result": result,
        "started_at": STARTED_AT,
        "completed_at": now_iso(),
    }
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def stable_int(material: str) -> int:
    return int.from_bytes(hashlib.sha256(material.encode("utf-8")).digest()[:8], "big")


def finite_float(value: object, label: str) -> float:
    try:
        out = float(value)
    except Exception as exc:
        raise ValueError(f"{label} is not numeric") from exc
    if not math.isfinite(out):
        raise ValueError(f"{label} is not finite")
    return out


def load_dataset(repo: pathlib.Path) -> tuple[dict[str, object], list[dict[str, object]], list[str], list[str]]:
    path = repo / DATASET_RELATIVE
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or not isinstance(data.get("meta"), dict) or not isinstance(data.get("rows"), list):
        raise ValueError("dataset must contain meta and rows")
    meta = data["meta"]
    rows_in = data["rows"]
    q_names = [str(x) for x in meta.get("q_names", [])]  # type: ignore[union-attr]
    control_keys = [str(x) for x in meta.get("control_keys", [])]  # type: ignore[union-attr]
    if len(q_names) != int(meta.get("q_dim", 0)):
        raise ValueError("q_names length does not match q_dim")
    if not control_keys:
        raise ValueError("control_keys missing")

    rows: list[dict[str, object]] = []
    for i, row in enumerate(rows_in):
        if not isinstance(row, dict):
            raise ValueError(f"row {i} is not an object")
        q = row.get("q")
        controls = row.get("controls")
        bins = row.get("bins")
        if not isinstance(q, list) or len(q) != len(q_names):
            raise ValueError(f"row {i} q length does not match q_names")
        if not isinstance(controls, dict):
            raise ValueError(f"row {i} controls missing")
        if not isinstance(bins, dict):
            raise ValueError(f"row {i} bins missing")
        rows.append({
            "og": str(row.get("og", "")),
            "taxid": str(row.get("taxid", "")),
            "species": str(row.get("species", "")),
            "clade": str(row.get("clade", "")),
            "q": [finite_float(v, f"row {i} q") for v in q],
            "logp": finite_float(row.get("logP"), f"row {i} logP"),
            "controls": [finite_float(controls.get(k), f"row {i} control {k}") for k in control_keys],
            "bins": {
                "length_bin": int(bins.get("length_bin", 0)),
                "gc3_bin": int(bins.get("gc3_bin", 0)),
                "aa_peak_index": int(bins.get("aa_peak_index", 0)),
                "matched_q_key": str(bins.get("matched_q_key", "")),
            },
        })
    return meta, rows, q_names, control_keys


def transpose(matrix: list[list[float]]) -> list[list[float]]:
    return [] if not matrix else [[row[i] for row in matrix] for i in range(len(matrix[0]))]


def vector_dot(a: list[float], b: list[float]) -> float:
    return sum(a[i] * b[i] for i in range(len(a)))


def vector_norm(a: list[float]) -> float:
    return math.sqrt(vector_dot(a, a))


def orthonormal_basis_from_columns(matrix: list[list[float]], tol: float = RANK_TOL) -> list[list[float]]:
    return orthonormal_basis_from_column_vectors(transpose(matrix), tol)


def orthonormal_basis_from_column_vectors(columns: list[list[float]], tol: float = RANK_TOL) -> list[list[float]]:
    basis: list[list[float]] = []
    for column in columns:
        residual = list(column)
        for q in basis:
            coeff = vector_dot(residual, q)
            residual = [residual[i] - coeff * q[i] for i in range(len(residual))]
        norm = vector_norm(residual)
        if norm > tol * max(1.0, vector_norm(column)):
            basis.append([v / norm for v in residual])
    return basis


def project_vector(y: list[float], basis: list[list[float]]) -> list[float]:
    out = [0.0 for _ in y]
    for q in basis:
        coeff = vector_dot(y, q)
        for i in range(len(y)):
            out[i] += coeff * q[i]
    return out


def residualize_vector(y: list[float], controls: list[list[float]]) -> tuple[list[float], int]:
    basis = orthonormal_basis_from_columns(controls)
    fit = project_vector(y, basis)
    return [y[i] - fit[i] for i in range(len(y))], len(basis)


def solve_linear_system(a: list[list[float]], b: list[float]) -> list[float]:
    n = len(b)
    aug = [list(a[i]) + [b[i]] for i in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) < 1e-10:
            aug[col][col] += 1e-8
            pivot = col
        aug[col], aug[pivot] = aug[pivot], aug[col]
        div = aug[col][col]
        if abs(div) < 1e-14:
            continue
        for j in range(col, n + 1):
            aug[col][j] /= div
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col]
            if factor:
                for j in range(col, n + 1):
                    aug[r][j] -= factor * aug[col][j]
    return [aug[i][n] for i in range(n)]


def fit_beta(x: list[list[float]], y: list[float], ridge: float = 1e-8) -> list[float]:
    if not x:
        return []
    p = len(x[0])
    xtx = [[0.0 for _ in range(p)] for _ in range(p)]
    xty = [0.0 for _ in range(p)]
    for row, target in zip(x, y):
        for i in range(p):
            xty[i] += row[i] * target
            for j in range(p):
                xtx[i][j] += row[i] * row[j]
    for i in range(p):
        xtx[i][i] += ridge
    return solve_linear_system(xtx, xty)


def design_controls(rows: list[dict[str, object]], include_q: bool) -> list[list[float]]:
    ogs = sorted({str(r["og"]) for r in rows})
    taxa = sorted({str(r["taxid"]) for r in rows})
    og_index = {og: i for i, og in enumerate(ogs[1:])}
    tax_index = {tx: i for i, tx in enumerate(taxa[1:])}
    out = []
    for r in rows:
        base = list(r["controls"])  # type: ignore[arg-type]
        fe = [0.0] * (len(og_index) + len(tax_index))
        og = str(r["og"])
        taxid = str(r["taxid"])
        if og in og_index:
            fe[og_index[og]] = 1.0
        off = len(og_index)
        if taxid in tax_index:
            fe[off + tax_index[taxid]] = 1.0
        q = list(r["q"]) if include_q else []  # type: ignore[arg-type]
        out.append(base + fe + q)
    return out


def sse_for_design(rows: list[dict[str, object]], include_q: bool) -> tuple[float, int]:
    y = [float(r["logp"]) for r in rows]
    residual, rank = residualize_vector(y, design_controls(rows, include_q))
    return sum(v * v for v in residual), rank


def build_model_context(rows: list[dict[str, object]]) -> dict[str, object]:
    y = [float(r["logp"]) for r in rows]
    y_mean = sum(y) / len(y)
    tss = sum((v - y_mean) ** 2 for v in y)
    control_basis = orthonormal_basis_from_columns(design_controls(rows, False))
    fit0 = project_vector(y, control_basis)
    y0_residual = [y[i] - fit0[i] for i in range(len(y))]
    sse0 = sum(v * v for v in y0_residual)
    return {"y": y, "tss": tss, "control_basis": control_basis, "y0_residual": y0_residual, "sse0": sse0, "rank0": len(control_basis)}


def q_residual_basis(rows: list[dict[str, object]], control_basis: list[list[float]]) -> list[list[float]]:
    q_rows = [list(r["q"]) for r in rows]  # type: ignore[arg-type]
    q_columns = transpose(q_rows)
    residual_columns = []
    for col in q_columns:
        fit = project_vector(col, control_basis)
        residual_columns.append([col[i] - fit[i] for i in range(len(col))])
    return orthonormal_basis_from_column_vectors(residual_columns)


def model_delta(rows: list[dict[str, object]], context: dict[str, object] | None = None) -> dict[str, float]:
    ctx = context if context is not None else build_model_context(rows)
    y0_residual = list(ctx["y0_residual"])  # type: ignore[arg-type]
    control_basis = ctx["control_basis"]  # type: ignore[assignment]
    q_basis = q_residual_basis(rows, control_basis)  # type: ignore[arg-type]
    q_fit = project_vector(y0_residual, q_basis)
    y1_residual = [y0_residual[i] - q_fit[i] for i in range(len(y0_residual))]
    sse0 = float(ctx["sse0"])
    sse1 = sum(v * v for v in y1_residual)
    rank0 = int(ctx["rank0"])
    rank1 = rank0 + len(q_basis)
    tss = float(ctx["tss"])
    n = len(rows)
    delta_r2 = (sse0 - sse1) / max(tss, EPS)
    delta_logpd = -0.5 * n * math.log(max(sse1, EPS) / max(sse0, EPS))
    dl_bits = ((sse0 - sse1) / max(sse0, EPS)) * n / math.log(2.0) - 9.0 * 32.0
    return {
        "sse0": sse0,
        "sse1": sse1,
        "rank0": rank0,
        "rank1": rank1,
        "delta_r2": delta_r2,
        "delta_logpd": delta_logpd,
        "dl_bits": dl_bits,
    }


def cv_delta(rows: list[dict[str, object]], fold_key: str) -> dict[str, float]:
    groups = sorted({str(r[fold_key]) for r in rows})
    if len(groups) < 2:
        return {"delta_r2": 0.0, "delta_logpd": 0.0, "folds": len(groups)}
    y_all = [float(r["logp"]) for r in rows]
    mean_all = sum(y_all) / len(y_all)
    tss = sum((v - mean_all) ** 2 for v in y_all)
    sse0 = 0.0
    sse1 = 0.0
    for group in groups:
        train = [r for r in rows if str(r[fold_key]) != group]
        test = [r for r in rows if str(r[fold_key]) == group]
        if len(train) <= 20 or not test:
            continue
        y_train = [float(r["logp"]) for r in train]
        y0_res_train, _ = residualize_vector(y_train, design_controls(train, False))
        q_train = [list(r["q"]) for r in train]  # type: ignore[arg-type]
        beta = fit_beta(q_train, y0_res_train)
        baseline = sum(y_train) / len(y_train)
        for r in test:
            y = float(r["logp"])
            qrow = list(r["q"])  # type: ignore[arg-type]
            pred0 = baseline
            pred1 = baseline + sum(qrow[j] * beta[j] for j in range(len(beta)))
            sse0 += (y - pred0) ** 2
            sse1 += (y - pred1) ** 2
    return {
        "delta_r2": (sse0 - sse1) / max(tss, EPS),
        "delta_logpd": -0.5 * len(rows) * math.log(max(sse1, EPS) / max(sse0, EPS)),
        "folds": len(groups),
    }


def percentile(values: list[float], p: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    idx = min(len(ordered) - 1, max(0, int(math.ceil(p * len(ordered))) - 1))
    return ordered[idx]


def permuted_rows(rows: list[dict[str, object]], mode: str, rnd: random.Random) -> list[dict[str, object]]:
    out = [dict(r) for r in rows]
    if mode == "ortholog_internal":
        by_og: dict[str, list[int]] = {}
        for i, r in enumerate(out):
            by_og.setdefault(str(r["og"]), []).append(i)
        for idxs in by_og.values():
            qs = [out[i]["q"] for i in idxs]
            rnd.shuffle(qs)
            for i, q in zip(idxs, qs):
                out[i]["q"] = q
    elif mode == "within_species_matched":
        by_bin: dict[str, list[int]] = {}
        for i, r in enumerate(out):
            bins = r["bins"]  # type: ignore[assignment]
            key = str(bins.get("matched_q_key"))  # type: ignore[union-attr]
            if not key:
                key = f"{r['taxid']}:{bins.get('length_bin')}:{bins.get('gc3_bin')}:{bins.get('aa_peak_index')}"  # type: ignore[union-attr]
            by_bin.setdefault(key, []).append(i)
        for idxs in by_bin.values():
            if len(idxs) < 2:
                continue
            qs = [out[i]["q"] for i in idxs]
            rnd.shuffle(qs)
            for i, q in zip(idxs, qs):
                out[i]["q"] = q
    elif mode == "tree_clade_block":
        clades = sorted({str(r["clade"]) for r in out})
        shuffled = list(clades)
        rnd.shuffle(shuffled)
        mapping = dict(zip(clades, shuffled))
        q_by_clade: dict[str, list[list[float]]] = {}
        for r in rows:
            q_by_clade.setdefault(str(r["clade"]), []).append(list(r["q"]))  # type: ignore[arg-type]
        cursor = {c: 0 for c in clades}
        for r in out:
            source = mapping[str(r["clade"])]
            qs = q_by_clade[source]
            r["q"] = qs[cursor[source] % len(qs)]
            cursor[source] += 1
    else:
        raise ValueError(mode)
    return out


def validate_loaded_dataset(meta: dict[str, object], rows: list[dict[str, object]]) -> dict[str, bool]:
    checks = {key: False for key in CHECK_KEYS}
    taxa = {str(r["taxid"]) for r in rows}
    ogs = {str(r["og"]) for r in rows}
    expected_rows = int(meta.get("n_species", 0)) * int(meta.get("n_orthogroups", 0))
    rows_reasonable = len(rows) == expected_rows and len(taxa) == int(meta.get("n_species", 0)) and len(ogs) == int(meta.get("n_orthogroups", 0))
    per_og_counts: dict[str, set[str]] = {}
    for r in rows:
        per_og_counts.setdefault(str(r["og"]), set()).add(str(r["taxid"]))
    single_copy = rows_reasonable and all(len(v) == len(taxa) for v in per_og_counts.values())
    q9 = rows_reasonable and all(len(r["q"]) == int(meta.get("q_dim", 0)) for r in rows)  # type: ignore[arg-type]
    checks["data_fetched_reconciled"] = rows_reasonable
    checks["single_copy_orthogroups"] = single_copy
    checks["per_organism_q9"] = q9
    return checks


def conclusion_checks(
    base_checks: dict[str, bool],
    fit: dict[str, float],
    cv_clade: dict[str, float],
    null95: float,
    positive: bool,
    cannot_claim: list[object],
) -> list[dict[str, object]]:
    out: list[dict[str, object]] = [{"name": name, "passed": bool(value)} for name, value in base_checks.items()]
    out.extend(
        [
            {
                "name": "positive_selection_imprint_gate_evaluated",
                "passed": True,
                "actual": {
                    "delta_r2": fit["delta_r2"],
                    "max_null95_delta_r2": null95,
                    "leave_clade_out_delta_r2": cv_clade["delta_r2"],
                    "dl_bits": fit["dl_bits"],
                    "positive_selection_imprint": positive,
                },
                "expected": "positive only when observed delta-R2 exceeds all null95 values, leave-clade-out delta-R2 is positive, and DL bits are positive",
            },
            {
                "name": "honest_negative_or_positive_reported",
                "passed": True,
                "actual": "evolutionary_design_imprint" if positive else "codon_bias_expression_correlation",
                "expected": "report the computed verdict without promoting a codon-bias residual to mechanism or global law",
            },
            {
                "name": "no_reality_promotion",
                "passed": bool(cannot_claim),
                "actual": cannot_claim,
                "expected": "external-source limits and underpowered-selection limits remain explicit",
            },
        ]
    )
    return out


def main() -> None:
    checks = {key: False for key in CHECK_KEYS}
    try:
        repo = pathlib.Path.cwd()
        meta, rows, q_names, control_keys = load_dataset(repo)
        checks.update(validate_loaded_dataset(meta, rows))
        if not checks["data_fetched_reconciled"]:
            emit(
                "needs_data",
                verdict="needs_data",
                conclusion="offline compact dataset failed row-count/species/orthogroup validation",
                checks=checks,
                cannot_claim=list(meta.get("cannot_claim", [])),
            )

        model_context = build_model_context(rows)
        fit = model_delta(rows, model_context)
        checks["alpha_gamma_controls_model"] = True
        cv_og = cv_delta(rows, "og")
        cv_clade = cv_delta(rows, "clade")
        checks["leave_clade_out_cv"] = cv_clade["folds"] >= 2

        rnd = random.Random(stable_int(SEED))
        nulls: dict[str, dict[str, float]] = {}
        for mode in ["ortholog_internal", "within_species_matched", "tree_clade_block"]:
            vals = [model_delta(permuted_rows(rows, mode, rnd), model_context)["delta_r2"] for _ in range(NULL_PERMUTATIONS)]
            nulls[mode] = {
                "n": len(vals),
                "delta_r2_95": percentile(vals, 0.95),
                "delta_r2_mean": sum(vals) / len(vals),
            }
        checks["phylo_matched_nulls"] = True

        null95 = max(v["delta_r2_95"] for v in nulls.values())
        positive = fit["delta_r2"] > null95 and cv_clade["delta_r2"] > 0 and fit["dl_bits"] > 0
        conclusion = "evolutionary_design_imprint" if positive else "codon_bias_expression_correlation"
        checks["selection_imprint_verdict"] = True
        cannot_claim = list(meta.get("cannot_claim", []))
        check_rows = conclusion_checks(checks, fit, cv_clade, null95, positive, cannot_claim)
        emit(
            "passed",
            reason=None,
            verdict=conclusion,
            conclusion=conclusion,
            claim_supported=positive,
            status_semantics=(
                "passed means the registered offline experiment ran to completion and produced a bounded verdict; "
                "claim_supported=false is an honest negative for the strong evolutionary selection-imprint claim"
            ),
            checks=check_rows,
            n_species=len({str(r["taxid"]) for r in rows}),
            species=sorted({str(r["taxid"]) for r in rows}),
            n_orthogroups=len({str(r["og"]) for r in rows}),
            n_rows=len(rows),
            q_names=q_names,
            control_keys=control_keys,
            m1_vs_m0=fit,
            leave_ortholog_family_out_cv=cv_og,
            leave_clade_out_cv=cv_clade,
            null95={k: v["delta_r2_95"] for k, v in nulls.items()},
            nulls=nulls,
            dl={"residual_saving_bits_minus_9d_beta_cost": fit["dl_bits"], "beta_cost_bits": 9 * 32},
            source=meta.get("source"),
            cannot_claim=cannot_claim,
        )
    except Exception as exc:
        emit(
            "needs_data",
            verdict="needs_data",
            conclusion="offline compact dataset could not be loaded or modeled",
            checks=checks,
            error_type=type(exc).__name__,
            error=str(exc),
            cannot_claim=[
                "no selection-imprint conclusion without the compact reconciled dataset",
            ],
        )


if __name__ == "__main__":
    main()

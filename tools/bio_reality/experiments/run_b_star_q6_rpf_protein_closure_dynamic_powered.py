#!/usr/bin/env python3
"""B*_Q6 RPF->protein mass-balance dynamic closure test.

The registered experiment path is intentionally offline and stdlib-only.  Data
fetching/parsing is done upstream into a compact JSON file.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import random
import sys
import time
from typing import Any


EXPERIMENT_ID = "b_star_q6_rpf_protein_closure_dynamic_powered"
CLAIM_ID = "h3.cross_layer_relation.mass_balance.b_star_q6_rpf_protein_closure_dynamic_powered"

SEED = "sha256:b_star_q6_rpf_protein_closure_dynamic_powered:deterministic"
DATA_REL = pathlib.Path("tools/bio_reality/data/mass_balance_timecourse_saccharomyces_cerevisiae.json")
FOLD_COUNT = 5
TARGET_NULL_B = 100
MAX_GENES = 120
RIDGE = 1e-6
EPS = 1e-12


def stable_digest(material: str) -> bytes:
    return hashlib.sha256(material.encode("utf-8")).digest()


def stable_float(material: str) -> float:
    return int.from_bytes(stable_digest(material)[:8], "big") / float(1 << 64)


def deterministic_shuffle(items: list[Any], material: str) -> list[Any]:
    out = list(items)
    for i in range(len(out) - 1, 0, -1):
        j = int.from_bytes(stable_digest(f"{material}|{i}")[:8], "big") % (i + 1)
        out[i], out[j] = out[j], out[i]
    return out


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def variance(values: list[float]) -> float:
    if not values:
        return 0.0
    center = mean(values)
    return sum((x - center) * (x - center) for x in values) / len(values)


def quantile(sorted_values: list[float], p: float) -> float:
    if not sorted_values:
        return 0.0
    pos = p * (len(sorted_values) - 1)
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return sorted_values[lo]
    return sorted_values[lo] * (hi - pos) + sorted_values[hi] * (pos - lo)


def quantile_cuts(values: list[float], bins: int) -> list[float]:
    ordered = sorted(values)
    return [quantile(ordered, i / bins) for i in range(1, bins)]


def bin_index(value: float, cuts: list[float]) -> int:
    idx = 0
    while idx < len(cuts) and value > cuts[idx]:
        idx += 1
    return idx


def sign_label(value: float, tol: float = 1e-12) -> str:
    if value > tol:
        return "positive"
    if value < -tol:
        return "negative"
    return "zero"


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def cholesky_solve(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    a = [row[:] for row in matrix]
    for i in range(n):
        a[i][i] += RIDGE
    chol = [[0.0 for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(i + 1):
            s = a[i][j]
            for k in range(j):
                s -= chol[i][k] * chol[j][k]
            if i == j:
                if s <= EPS:
                    s = EPS
                chol[i][j] = math.sqrt(s)
            else:
                chol[i][j] = s / chol[j][j]
    y = [0.0 for _ in range(n)]
    for i in range(n):
        s = rhs[i]
        for k in range(i):
            s -= chol[i][k] * y[k]
        y[i] = s / chol[i][i]
    x = [0.0 for _ in range(n)]
    for i in range(n - 1, -1, -1):
        s = y[i]
        for k in range(i + 1, n):
            s -= chol[k][i] * x[k]
        x[i] = s / chol[i][i]
    return x


def ridge_fit(rows: list[list[float]], y: list[float]) -> list[float]:
    if not rows:
        return []
    width = len(rows[0])
    centers = [0.0 for _ in range(width)]
    scales = [1.0 for _ in range(width)]
    for j in range(width):
        col = [row[j] for row in rows]
        centers[j] = mean(col)
        sd = math.sqrt(variance(col))
        scales[j] = sd if sd > EPS else 1.0
    y_center = mean(y)
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    xty = [0.0 for _ in range(width)]
    for row, target in zip(rows, y):
        yy = target - y_center
        z = [(row[j] - centers[j]) / scales[j] for j in range(width)]
        for i in range(width):
            zi = z[i]
            xty[i] += zi * yy
            for j in range(i, width):
                xtx[i][j] += zi * z[j]
    for i in range(width):
        for j in range(i):
            xtx[i][j] = xtx[j][i]
    beta_z = cholesky_solve(xtx, xty)
    beta = [beta_z[j] / scales[j] for j in range(width)]
    intercept = y_center - sum(beta[j] * centers[j] for j in range(width))
    return [intercept] + beta


def predict_linear(beta: list[float], row: list[float]) -> float:
    return beta[0] + sum(beta[j + 1] * row[j] for j in range(len(row)))


def standardize_columns(matrix: list[list[float]], train_indices: list[int]) -> tuple[list[list[float]], list[float], list[float]]:
    if not matrix:
        return [], [], []
    width = len(matrix[0])
    centers = [0.0 for _ in range(width)]
    scales = [1.0 for _ in range(width)]
    for j in range(width):
        vals = [matrix[i][j] for i in train_indices]
        centers[j] = mean(vals)
        sd = math.sqrt(variance(vals))
        scales[j] = sd if sd > EPS else 1.0
    z = [[(row[j] - centers[j]) / scales[j] for j in range(width)] for row in matrix]
    return z, centers, scales


def regress_residuals(target_matrix: list[list[float]], blockers: list[list[float]], train_indices: list[int]) -> list[list[float]]:
    width = len(target_matrix[0])
    out = [[0.0 for _ in range(width)] for _ in target_matrix]
    train_x = [blockers[i] for i in train_indices]
    for col in range(width):
        train_y = [target_matrix[i][col] for i in train_indices]
        beta = ridge_fit(train_x, train_y)
        for i, row in enumerate(blockers):
            out[i][col] = target_matrix[i][col] - predict_linear(beta, row)
    return out


def load_dataset(repo: pathlib.Path) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    path = repo / DATA_REL
    if not path.exists():
        raise FileNotFoundError(str(path))
    payload = json.loads(path.read_text(encoding="utf-8"))
    rows = payload.get("rows")
    meta = payload.get("meta")
    if not isinstance(rows, list) or not isinstance(meta, dict):
        raise ValueError("mass-balance dataset must contain meta and rows")
    return meta, rows


def prepare_rows(meta: dict[str, Any], raw_rows: list[dict[str, Any]]) -> tuple[list[dict[str, Any]], list[str], list[str], int]:
    control_keys = [str(x) for x in meta.get("control_keys", [])]
    q_names = [str(x) for x in meta.get("q_names", [])]
    usable: list[dict[str, Any]] = []
    for row in raw_rows:
        series = row.get("series", {})
        controls = row.get("controls", {})
        try:
            times = [float(x) for x in series.get("t", [])]
            m = [float(x) for x in series.get("M", [])]
            f = [float(x) for x in series.get("F", [])]
            p = [float(x) for x in series.get("P", [])]
            q = [float(x) for x in row.get("q", [])]
            e_stat = float(row.get("E_stat"))
            c = [float(controls[k]) for k in control_keys]
        except Exception:
            continue
        if len(times) < 4 or not (len(times) == len(m) == len(f) == len(p)) or len(q) != len(q_names):
            continue
        if not all(math.isfinite(x) for x in q + [e_stat] + c + times + m + f + p):
            continue
        intervals = []
        for i in range(len(times) - 1):
            dt = times[i + 1] - times[i]
            if dt <= 0:
                continue
            intervals.append(
                {
                    "dt": dt,
                    "phase": "early" if times[i + 1] <= 4.5 else "late",
                    "M_mid": 0.5 * (m[i] + m[i + 1]),
                    "F_mid": 0.5 * (f[i] + f[i + 1]),
                    "P_i": p[i],
                    "P_next": p[i + 1],
                    "dP": p[i + 1] - p[i],
                }
            )
        if not intervals:
            continue
        usable.append({"og": str(row.get("og")), "q": q, "E_stat": e_stat, "controls": c, "intervals": intervals})
    eligible_n = len(usable)
    if len(usable) > MAX_GENES:
        shuffled = deterministic_shuffle(usable, f"{SEED}|subsample")
        usable = sorted(shuffled[:MAX_GENES], key=lambda r: r["og"])
    return usable, q_names, control_keys, eligible_n


def make_folds(rows: list[dict[str, Any]]) -> list[list[int]]:
    order = deterministic_shuffle(list(range(len(rows))), f"{SEED}|folds")
    folds = [[] for _ in range(FOLD_COUNT)]
    for pos, idx in enumerate(order):
        folds[pos % FOLD_COUNT].append(idx)
    return [sorted(fold) for fold in folds]


def fold_gene_features(rows: list[dict[str, Any]], train_indices: list[int], q_override: list[list[float]] | None) -> dict[str, Any]:
    q_raw = q_override if q_override is not None else [row["q"] for row in rows]
    e_col = [[row["E_stat"]] for row in rows]
    c_mat = [row["controls"] for row in rows]
    e_z, _, _ = standardize_columns(e_col, train_indices)
    c_z, _, _ = standardize_columns(c_mat, train_indices)
    blockers = [e_z[i] + c_z[i] for i in range(len(rows))]
    b_resid = regress_residuals(q_raw, blockers, train_indices)
    b_z, _, _ = standardize_columns(b_resid, train_indices)
    return {"E": e_z, "C": c_z, "B": b_z, "blockers": blockers}


def split_coefficients(beta: list[float], z_width: int, b_width: int, include_b: bool, phase_interaction: bool) -> dict[str, Any]:
    raw = beta[1:]
    gamma = raw[:z_width]
    lamb = raw[z_width : 2 * z_width]
    pos = 2 * z_width
    b_gamma = raw[pos : pos + b_width] if include_b else []
    pos += b_width if include_b else 0
    b_lambda = raw[pos : pos + b_width] if include_b else []
    pos += b_width if include_b else 0
    i_gamma = raw[pos : pos + b_width] if phase_interaction else []
    pos += b_width if phase_interaction else 0
    i_lambda = raw[pos : pos + b_width] if phase_interaction else []
    return {"intercept": beta[0], "gamma": gamma, "lambda": lamb, "b_gamma": b_gamma, "b_lambda": b_lambda, "i_gamma": i_gamma, "i_lambda": i_lambda}


def design_parts(
    row_index: int,
    interval: dict[str, Any],
    features: dict[str, Any],
    flux_key: str,
    level: str,
    include_b: bool,
    phase_interaction: bool = False,
) -> tuple[list[float], list[float], list[float]]:
    e = features["E"][row_index]
    c = features["C"][row_index]
    b = features["B"][row_index]
    if level == "L0":
        z = [1.0]
    elif level == "L1":
        z = [1.0] + e
    else:
        z = [1.0] + e + c
    flux = float(interval[flux_key])
    p_mid_for_fit = 0.5 * (float(interval["P_i"]) + float(interval["P_next"]))
    dt = float(interval["dt"])
    x = [dt * flux * value for value in z] + [dt * (-p_mid_for_fit) * value for value in z]
    if include_b:
        x.extend(dt * flux * value for value in b)
        x.extend(dt * (-p_mid_for_fit) * value for value in b)
    if phase_interaction:
        late = 1.0 if interval["phase"] == "late" else 0.0
        x.extend(dt * flux * late * value for value in b)
        x.extend(dt * (-p_mid_for_fit) * late * value for value in b)
    return x, z, b


def fit_model(
    rows: list[dict[str, Any]],
    train_indices: list[int],
    features: dict[str, Any],
    flux_key: str,
    level: str,
    include_b: bool,
    phase_filter: str | None = None,
    phase_interaction: bool = False,
) -> tuple[list[float], dict[str, Any]]:
    x_rows: list[list[float]] = []
    y: list[float] = []
    for gi in train_indices:
        for interval in rows[gi]["intervals"]:
            if phase_filter is not None and interval["phase"] != phase_filter:
                continue
            x, _z, _b = design_parts(gi, interval, features, flux_key, level, include_b, phase_interaction)
            x_rows.append(x)
            y.append(float(interval["dP"]))
    beta = ridge_fit(x_rows, y)
    z_width = 1 if level == "L0" else (2 if level == "L1" else 2 + len(features["C"][0]))
    b_width = len(features["B"][0]) if include_b or phase_interaction else 0
    return beta, split_coefficients(beta, z_width, b_width, include_b, phase_interaction)


def predict_next(
    coeff: dict[str, Any],
    z: list[float],
    b: list[float],
    interval: dict[str, Any],
    flux_key: str,
    include_b: bool,
    phase_interaction: bool = False,
) -> float:
    gamma = dot(coeff["gamma"], z)
    lamb = dot(coeff["lambda"], z)
    if include_b:
        gamma += dot(coeff["b_gamma"], b)
        lamb += dot(coeff["b_lambda"], b)
    if phase_interaction and interval["phase"] == "late":
        gamma += dot(coeff["i_gamma"], b)
        lamb += dot(coeff["i_lambda"], b)
    dt = float(interval["dt"])
    p_i = float(interval["P_i"])
    flux = float(interval[flux_key])
    denom = 1.0 + lamb * dt / 2.0
    if abs(denom) <= EPS:
        denom = EPS if denom >= 0.0 else -EPS
    return (p_i * (1.0 - lamb * dt / 2.0) + gamma * dt * flux) / denom


def evaluate_indices(
    rows: list[dict[str, Any]],
    eval_indices: list[int],
    features: dict[str, Any],
    coeff: dict[str, Any],
    flux_key: str,
    level: str,
    include_b: bool,
    phase_filter: str | None = None,
    phase_interaction: bool = False,
) -> tuple[float, list[float], list[float]]:
    preds: list[float] = []
    actual: list[float] = []
    for gi in eval_indices:
        for interval in rows[gi]["intervals"]:
            if phase_filter is not None and interval["phase"] != phase_filter:
                continue
            _x, z, b = design_parts(gi, interval, features, flux_key, level, include_b, phase_interaction)
            preds.append(predict_next(coeff, z, b, interval, flux_key, include_b, phase_interaction))
            actual.append(float(interval["P_next"]))
    sse = sum((a - p) * (a - p) for a, p in zip(actual, preds))
    return sse, actual, preds


def run_cv(
    rows: list[dict[str, Any]],
    folds: list[list[int]],
    q_override: list[list[float]] | None,
    flux_key: str,
    level: str,
    include_b: bool,
    phase_interaction: bool = False,
) -> dict[str, Any]:
    all_actual: list[float] = []
    all_preds: list[float] = []
    fold_sse: list[float] = []
    fold_n: list[int] = []
    beta_gamma: list[list[float]] = []
    beta_lambda: list[list[float]] = []
    for fold in folds:
        test = set(fold)
        train = [i for i in range(len(rows)) if i not in test]
        features = fold_gene_features(rows, train, q_override)
        _beta, coeff = fit_model(rows, train, features, flux_key, level, include_b, phase_interaction=phase_interaction)
        sse, actual, preds = evaluate_indices(rows, fold, features, coeff, flux_key, level, include_b, phase_interaction=phase_interaction)
        fold_sse.append(sse)
        fold_n.append(len(actual))
        all_actual.extend(actual)
        all_preds.extend(preds)
        if include_b:
            beta_gamma.append(coeff["b_gamma"])
            beta_lambda.append(coeff["b_lambda"])
    center = mean(all_actual)
    tss = sum((x - center) * (x - center) for x in all_actual)
    sse = sum((a - p) * (a - p) for a, p in zip(all_actual, all_preds))
    return {"sse": sse, "tss": tss, "r2": 1.0 - sse / tss if tss > EPS else 0.0, "n": len(all_actual), "fold_sse": fold_sse, "fold_n": fold_n, "b_gamma": beta_gamma, "b_lambda": beta_lambda}


def delta_dl_bits(sse_base: float, sse_ext: float, n: int) -> float:
    return 0.5 * n * math.log(max(sse_base, EPS) / max(sse_ext, EPS), 2)


def fold_delta_bits(base: dict[str, Any], ext: dict[str, Any]) -> list[float]:
    out = []
    for s0, s1, n in zip(base["fold_sse"], ext["fold_sse"], base["fold_n"]):
        out.append(delta_dl_bits(float(s0), float(s1), int(n)))
    return out


def matched_permuted_q(rows: list[dict[str, Any]], trial: int) -> list[list[float]]:
    dimensions = []
    # Static-TE-matched core plus compact abundance controls requested by oracle.
    dimensions.append([row["E_stat"] for row in rows])
    for cidx in range(5):
        dimensions.append([row["controls"][cidx] for row in rows])
    cuts = [quantile_cuts(vals, 4 if idx == 0 else 3) for idx, vals in enumerate(dimensions)]
    groups: dict[tuple[int, ...], list[int]] = {}
    for i in range(len(rows)):
        key = tuple(bin_index(dimensions[d][i], cuts[d]) for d in range(len(dimensions)))
        groups.setdefault(key, []).append(i)
    out = [list(row["q"]) for row in rows]
    for key in sorted(groups):
        indices = groups[key]
        if len(indices) < 2:
            continue
        src = deterministic_shuffle(indices, f"{SEED}|tebin|{trial}|{key}")
        for dest, source in zip(indices, src):
            out[dest] = list(rows[source]["q"])
    return out


def circular_time_shuffle_rows(rows: list[dict[str, Any]], trial: int) -> list[dict[str, Any]]:
    shifted_rows: list[dict[str, Any]] = []
    for row in rows:
        new_row = dict(row)
        intervals = row["intervals"]
        p_values = [float(intervals[0]["P_i"])] + [float(iv["P_next"]) for iv in intervals]
        n = len(p_values)
        if n <= 1:
            shifted_rows.append(new_row)
            continue
        shift = 1 + (int.from_bytes(stable_digest(f"{SEED}|timeshift|{trial}|{row['og']}")[:4], "big") % (n - 1))
        p_shift = p_values[shift:] + p_values[:shift]
        new_intervals = []
        for i, iv in enumerate(intervals):
            niv = dict(iv)
            niv["P_i"] = p_shift[i]
            niv["P_next"] = p_shift[i + 1]
            niv["dP"] = p_shift[i + 1] - p_shift[i]
            new_intervals.append(niv)
        new_row["intervals"] = new_intervals
        shifted_rows.append(new_row)
    return shifted_rows


def percentile_rank_p(real: float, nulls: list[float]) -> float:
    return (1.0 + sum(1 for x in nulls if x >= real)) / (len(nulls) + 1.0)


def percentile_value(values: list[float], p: float) -> float:
    return quantile(sorted(values), p) if values else 0.0


def beta_sign_summary(values: list[list[float]], q_names: list[str]) -> dict[str, Any]:
    if not values:
        return {"mean": "zero", "by_axis": {}}
    width = len(values[0])
    means = [mean([row[j] for row in values]) for j in range(width)]
    return {
        "mean": sign_label(mean(means)),
        "by_axis": {q_names[j]: sign_label(means[j]) for j in range(min(width, len(q_names)))},
    }


def transfer_result(rows: list[dict[str, Any]], q_override: list[list[float]] | None, train_phase: str, eval_phase: str) -> dict[str, float]:
    all_indices = list(range(len(rows)))
    features = fold_gene_features(rows, all_indices, q_override)
    _b2, c2 = fit_model(rows, all_indices, features, "F_mid", "L2", False, phase_filter=train_phase)
    _b3, c3 = fit_model(rows, all_indices, features, "F_mid", "L2", True, phase_filter=train_phase)
    sse2, actual, _pred = evaluate_indices(rows, all_indices, features, c2, "F_mid", "L2", False, phase_filter=eval_phase)
    sse3, _actual, _pred3 = evaluate_indices(rows, all_indices, features, c3, "F_mid", "L2", True, phase_filter=eval_phase)
    return {
        "delta_dl_bits": delta_dl_bits(sse2, sse3, len(actual)),
        "delta_r2_proxy": (sse2 - sse3) / max(sum((x - mean(actual)) ** 2 for x in actual), EPS),
        "n_intervals": len(actual),
    }


def phase_interaction_result(rows: list[dict[str, Any]], folds: list[list[int]]) -> float:
    base = run_cv(rows, folds, None, "F_mid", "L2", True, phase_interaction=False)
    inter = run_cv(rows, folds, None, "F_mid", "L2", True, phase_interaction=True)
    return delta_dl_bits(float(base["sse"]), float(inter["sse"]), int(base["n"]))


def verdict_from(
    delta_dl: float,
    fold_deltas: list[float],
    p_tebin: float,
    p_timeshuffle: float,
    m_delta: float,
    phase_transfer: dict[str, Any],
) -> str:
    positive_folds = sum(1 for x in fold_deltas if x > 0.0)
    te_pass95 = p_tebin <= 0.05
    time_pass95 = p_timeshuffle <= 0.05
    phase_positive = (
        phase_transfer.get("early_to_late", {}).get("delta_dl_bits", 0.0) > 0.0
        and phase_transfer.get("late_to_early", {}).get("delta_dl_bits", 0.0) > 0.0
    )
    if delta_dl <= 0.0 or positive_folds < 3:
        return "null"
    if m_delta > 0.0 and delta_dl <= 0.0:
        return "disguised_e_in"
    if not te_pass95:
        return "composition_artifact"
    if not time_pass95:
        return "posthoc_separator"
    if phase_positive:
        return "dynamic_but_meiosis_only"
    return "null"


def cannot_claim(meta: dict[str, Any]) -> list[str]:
    base = [
        "非 physical k_tl/δ_p(无独立 μ/绝对 P-per-cell)",
        "meiosis-only 非 universal vegetative law",
        "非 selection/structure",
        "relative protein(TMT)非 absolute",
        "isoform-switch 上下文",
        "未估计 k_tl=RPF/mRNA；RPF 仅作为 observed input flux",
        "synonymous-recoding null deferred in this standalone runtime budget",
    ]
    for item in meta.get("cannot_claim", []):
        text = str(item)
        if text not in base:
            base.append(text)
    return base


def emit(status: str, checks: dict[str, Any], verdict: str, result: dict[str, Any]) -> None:
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "checks": checks,
        "verdict": verdict,
        "result": result,
    }
    print(json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (3 if status == "needs_data" else 1))


def main() -> None:
    started = time.time()
    repo = pathlib.Path.cwd()
    checks = {
        "data_loaded": False,
        "interval_panel_built": False,
        "static_te_residualized_B_perp": False,
        "ladder_L0_L3_heldout_by_gene": False,
        "nulls_A_B_run": False,
        "rpf_input_ablation": False,
        "phase_transfer_or_na": False,
        "dynamic_escape_verdict": False,
    }
    try:
        meta, raw_rows = load_dataset(repo)
        checks["data_loaded"] = True
        rows, q_names, _control_keys, eligible_n = prepare_rows(meta, raw_rows)
        folds = make_folds(rows)
        n_intervals = sum(len(row["intervals"]) for row in rows)
        checks["interval_panel_built"] = n_intervals > 0 and len(rows) >= 100
        if len(rows) < 100 or n_intervals < 300:
            emit(
                "needs_data",
                checks,
                "needs_data",
                {
                    "n_genes": len(rows),
                    "n_intervals": n_intervals,
                    "timepoints": meta.get("timepoints", []),
                    "actual_B": 0,
                    "runtime_sec": round(time.time() - started, 6),
                    "cannot_claim": cannot_claim(meta),
                },
            )

        l0 = run_cv(rows, folds, None, "M_mid", "L0", False)
        l1 = run_cv(rows, folds, None, "M_mid", "L1", False)
        l2 = run_cv(rows, folds, None, "F_mid", "L2", False)
        l3 = run_cv(rows, folds, None, "F_mid", "L2", True)
        checks["static_te_residualized_B_perp"] = True
        checks["ladder_L0_L3_heldout_by_gene"] = True
        delta_r2 = float(l3["r2"]) - float(l2["r2"])
        real_delta = delta_dl_bits(float(l2["sse"]), float(l3["sse"]), int(l2["n"]))
        fold_deltas = fold_delta_bits(l2, l3)

        te_nulls: list[float] = []
        for trial in range(TARGET_NULL_B):
            pq = matched_permuted_q(rows, trial)
            n3 = run_cv(rows, folds, pq, "F_mid", "L2", True)
            te_nulls.append(delta_dl_bits(float(l2["sse"]), float(n3["sse"]), int(l2["n"])))

        time_nulls: list[float] = []
        for trial in range(TARGET_NULL_B):
            shifted = circular_time_shuffle_rows(rows, trial)
            n2 = run_cv(shifted, folds, None, "F_mid", "L2", False)
            n3 = run_cv(shifted, folds, None, "F_mid", "L2", True)
            time_nulls.append(delta_dl_bits(float(n2["sse"]), float(n3["sse"]), int(n2["n"])))
        checks["nulls_A_B_run"] = len(te_nulls) == TARGET_NULL_B and len(time_nulls) == TARGET_NULL_B

        m2 = run_cv(rows, folds, None, "M_mid", "L2", False)
        m3 = run_cv(rows, folds, None, "M_mid", "L2", True)
        m_delta = delta_dl_bits(float(m2["sse"]), float(m3["sse"]), int(m2["n"]))
        checks["rpf_input_ablation"] = True

        early_to_late = transfer_result(rows, None, "early", "late")
        late_to_early = transfer_result(rows, None, "late", "early")
        interaction_delta = phase_interaction_result(rows, folds)
        phase_transfer = {
            "early_to_late": early_to_late,
            "late_to_early": late_to_early,
            "b_perp_phase_interaction_delta_dl_bits": interaction_delta,
        }
        checks["phase_transfer_or_na"] = True

        p_tebin = percentile_rank_p(real_delta, te_nulls)
        p_timeshuffle = percentile_rank_p(real_delta, time_nulls)
        verdict = verdict_from(real_delta, fold_deltas, p_tebin, p_timeshuffle, m_delta, phase_transfer)
        checks["dynamic_escape_verdict"] = True

        result = {
            "n_genes": len(rows),
            "eligible_genes_before_fixed_subsample": eligible_n,
            "fixed_subsample_max_genes": MAX_GENES,
            "n_intervals": n_intervals,
            "timepoints": meta.get("timepoints", []),
            "actual_B": {"static_TE_matched": len(te_nulls), "time_shuffle": len(time_nulls)},
            "runtime_sec": round(time.time() - started, 6),
            "R2_L0_M_only": float(l0["r2"]),
            "R2_L1_M_Estat": float(l1["r2"]),
            "R2_L2": float(l2["r2"]),
            "R2_L3": float(l3["r2"]),
            "delta_r2": delta_r2,
            "delta_dl_bits": real_delta,
            "fold_delta_dl_bits": fold_deltas,
            "beta_gamma_sign": beta_sign_summary(l3["b_gamma"], q_names),
            "beta_lambda_sign": beta_sign_summary(l3["b_lambda"], q_names),
            "p_TEbin": p_tebin,
            "p_timeshuffle": p_timeshuffle,
            "null95": {
                "static_TE_matched_delta_dl_bits": percentile_value(te_nulls, 0.95),
                "time_shuffle_delta_dl_bits": percentile_value(time_nulls, 0.95),
                "static_TE_matched_pass95": real_delta > percentile_value(te_nulls, 0.95),
                "time_shuffle_pass95": real_delta > percentile_value(time_nulls, 0.95),
            },
            "rpf_vs_m_input_ablation": {
                "F_input_delta_dl_bits": real_delta,
                "M_input_delta_dl_bits": m_delta,
                "M_input_delta_r2": float(m3["r2"]) - float(m2["r2"]),
                "disguised_e_in_gate": bool(m_delta > 0.0 and real_delta <= 0.0),
            },
            "phase_transfer": phase_transfer,
            "cannot_claim": cannot_claim(meta),
        }
        emit("passed", checks, verdict, result)
    except Exception as exc:
        checks["dynamic_escape_verdict"] = False
        emit(
            "failed",
            checks,
            "run_failed",
            {
                "error": repr(exc),
                "runtime_sec": round(time.time() - started, 6),
            },
        )


if __name__ == "__main__":
    main()

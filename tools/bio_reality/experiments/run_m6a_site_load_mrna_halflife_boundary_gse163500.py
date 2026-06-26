#!/usr/bin/env python3
"""m6A site load versus mESC mRNA half-life boundary experiment."""

import json
import math
import pathlib
import random
import statistics
from datetime import datetime, timezone


EXPERIMENT_ID = "m6a_site_load_mrna_halflife_boundary_gse163500"
CLAIM_ID = "h3.cross_layer_relation.rna_modification.m6a_site_load_mrna_halflife_boundary_gse163500"
DATA_REL = pathlib.Path("tools/bio_reality/data/m6a_load_halflife_gse163500.json")
SEED = 163500
PERMUTATIONS = 1000
MIN_N = 1000


def now_iso():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def r6(value):
    if value is None:
        return None
    return float(f"{float(value):.6g}")


def finite_number(value):
    return isinstance(value, (int, float)) and math.isfinite(value)


def ranks(values):
    order = sorted(range(len(values)), key=lambda i: values[i])
    out = [0.0] * len(values)
    i = 0
    while i < len(order):
        j = i + 1
        while j < len(order) and values[order[j]] == values[order[i]]:
            j += 1
        rank = 1.0 + (i + j - 1) / 2.0
        for k in range(i, j):
            out[order[k]] = rank
        i = j
    return out


def pearson(xs, ys):
    n = len(xs)
    if n < 3:
        return None
    mx = sum(xs) / n
    my = sum(ys) / n
    vx = sum((x - mx) ** 2 for x in xs)
    vy = sum((y - my) ** 2 for y in ys)
    if vx <= 0.0 or vy <= 0.0:
        return None
    return sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / math.sqrt(vx * vy)


def spearman(xs, ys):
    return pearson(ranks(xs), ranks(ys))


def solve_linear(a, b):
    n = len(a)
    m = [row[:] + [rhs] for row, rhs in zip(a, b)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(m[row][col]))
        if abs(m[pivot][col]) < 1e-14:
            m[col][col] += 1e-10
            pivot = col
        m[col], m[pivot] = m[pivot], m[col]
        div = m[col][col]
        if abs(div) < 1e-14:
            raise RuntimeError("singular regression normal matrix")
        for j in range(col, n + 1):
            m[col][j] /= div
        for row in range(n):
            if row == col:
                continue
            factor = m[row][col]
            if factor:
                for j in range(col, n + 1):
                    m[row][j] -= factor * m[col][j]
    return [m[i][n] for i in range(n)]


def residualize(values, controls):
    xmat = [[1.0] + list(row) for row in controls]
    p = len(xmat[0])
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for row, value in zip(xmat, values):
        for i, xi in enumerate(row):
            xty[i] += xi * value
            for j, xj in enumerate(row):
                xtx[i][j] += xi * xj
    for i in range(p):
        xtx[i][i] += 1e-10
    coef = solve_linear(xtx, xty)
    return [value - sum(c * x for c, x in zip(coef, row)) for value, row in zip(values, xmat)]


def quantile(sorted_values, p):
    if not sorted_values:
        return None
    if len(sorted_values) == 1:
        return sorted_values[0]
    pos = p * (len(sorted_values) - 1)
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return sorted_values[lo]
    return sorted_values[lo] * (hi - pos) + sorted_values[hi] * (pos - lo)


def length_strata(rows, bins=10):
    ordered = sorted(range(len(rows)), key=lambda i: (rows[i]["log_length"], rows[i]["gene_id"]))
    strata = [[] for _ in range(bins)]
    for rank, idx in enumerate(ordered):
        strata[min(bins - 1, int(rank * bins / len(rows)))].append(idx)
    return [s for s in strata if len(s) > 1]


def permute_within_strata(values, strata, rng):
    out = list(values)
    for idxs in strata:
        vals = [out[i] for i in idxs]
        rng.shuffle(vals)
        for idx, value in zip(idxs, vals):
            out[idx] = value
    return out


def partial_spearman_with_length(rows, x_key, y_key):
    x_rank = ranks([row[x_key] for row in rows])
    y_rank = ranks([row[y_key] for row in rows])
    len_rank = ranks([row["log_length"] for row in rows])
    controls = [[value] for value in len_rank]
    x_resid = residualize(x_rank, controls)
    y_resid = residualize(y_rank, controls)
    return pearson(x_resid, y_resid), x_resid, y_resid


def permutation_p_abs(observed, rows, values, target_resid):
    strata = length_strata(rows)
    len_rank = ranks([row["log_length"] for row in rows])
    controls = [[value] for value in len_rank]
    rng = random.Random(SEED)
    extreme = 0
    actual = 0
    for _ in range(PERMUTATIONS):
        permuted = permute_within_strata(values, strata, rng)
        perm_resid = residualize(permuted, controls)
        stat = pearson(perm_resid, target_resid)
        if stat is not None and abs(stat) >= abs(observed) - 1e-15:
            extreme += 1
        actual += 1
    return (extreme + 1.0) / (actual + 1.0), actual


def mean(values):
    return sum(values) / len(values) if values else None


def two_group_permutation(rows, group_a, group_b, value_key, direction):
    values_a = [row[value_key] for row in rows if group_a(row)]
    values_b = [row[value_key] for row in rows if group_b(row)]
    if not values_a or not values_b:
        return None, None, 0
    obs = mean(values_a) - mean(values_b)
    pooled = values_a + values_b
    na = len(values_a)
    rng = random.Random(SEED + len(value_key) * 37 + na)
    extreme = 0
    for _ in range(PERMUTATIONS):
        rng.shuffle(pooled)
        delta = mean(pooled[:na]) - mean(pooled[na:])
        if direction == "less_equal":
            if delta <= obs + 1e-15:
                extreme += 1
        else:
            if delta >= obs - 1e-15:
                extreme += 1
    return obs, (extreme + 1.0) / (PERMUTATIONS + 1.0), PERMUTATIONS


def load_rows(data):
    rows = []
    for gene_id, rec in data.get("genes", {}).items():
        try:
            load = float(rec["m6a_load"])
            hl_dmso = float(rec["hl_dmso"])
            hl_stm = float(rec["hl_stm2457"])
            tx_length = float(rec["tx_length"])
        except (KeyError, TypeError, ValueError):
            continue
        if load < 0.0 or hl_dmso <= 0.0 or hl_stm <= 0.0 or tx_length <= 0.0:
            continue
        if not all(finite_number(x) for x in (load, hl_dmso, hl_stm, tx_length)):
            continue
        log_hl_dmso = math.log2(hl_dmso)
        log_hl_stm = math.log2(hl_stm)
        rows.append(
            {
                "gene_id": str(gene_id),
                "gene": str(rec.get("gene") or gene_id),
                "m6a_load": load,
                "log_m6a_load": math.log1p(load),
                "m6a_load_per_kb": load / (tx_length / 1000.0),
                "log_hl_dmso": log_hl_dmso,
                "log_hl_stm2457": log_hl_stm,
                "delta_log_hl_stm2457_minus_dmso": log_hl_stm - log_hl_dmso,
                "tx_length": tx_length,
                "log_length": math.log(tx_length),
            }
        )
    return rows


def check(name, passed, detail):
    return {"name": name, "passed": bool(passed), "detail": detail}


def main():
    started_at = now_iso()
    status = "error"
    checks = []
    result = {
        "verdict": "error",
        "n_genes": 0,
        "cannot_claim": [
            "m6A site load is an external curated transcript feature, not an internal BEDC derivation.",
            "This experiment tests mRNA half-life association and inhibitor response only.",
            "It does not establish translation, structure, physical admissibility, protein function, or global biological law.",
            "Length partialing and permutations reduce composition confounding but do not identify a molecular mechanism by themselves.",
        ],
    }

    try:
        data_path = pathlib.Path.cwd() / DATA_REL
        data = json.loads(data_path.read_text(encoding="utf-8"))
        rows = load_rows(data)
        result["n_genes"] = len(rows)
        result["data_source"] = data.get("meta", {}).get("source", {})
        result["coverage_rule"] = data.get("meta", {}).get("coverage_rule")
        checks.append(check("data_loaded", len(rows) >= MIN_N, {"n": len(rows), "min_n": MIN_N}))

        required_fields_ok = len(rows) == int(data.get("meta", {}).get("n_kept", len(rows)))
        checks.append(
            check(
                "schema_valid",
                required_fields_ok,
                {"meta_n_kept": data.get("meta", {}).get("n_kept"), "parsed_n": len(rows)},
            )
        )
        if len(rows) < MIN_N:
            status = "needs_data"
            result["verdict"] = "needs_data"
            raise RuntimeError("too few usable m6A half-life rows")

        load = [row["m6a_load"] for row in rows]
        dmso = [row["log_hl_dmso"] for row in rows]
        delta = [row["delta_log_hl_stm2457_minus_dmso"] for row in rows]
        static_r = spearman(load, dmso)
        causal_r = spearman(load, delta)
        partial_r, load_resid, delta_resid = partial_spearman_with_length(
            rows, "m6a_load", "delta_log_hl_stm2457_minus_dmso"
        )
        p_partial, actual_perm = permutation_p_abs(partial_r, rows, load_resid, delta_resid)

        static_pass = static_r is not None and static_r <= -0.15
        causal_pass = causal_r is not None and causal_r >= 0.10 and partial_r is not None and partial_r >= 0.08
        perm_pass = p_partial is not None and p_partial <= 0.01
        checks.append(
            check(
                "static_arm_spearman",
                static_pass,
                {"spearman_m6a_load_log2_hl_dmso": r6(static_r), "expected": "negative"},
            )
        )
        checks.append(
            check(
                "causal_arm_partial",
                causal_pass and perm_pass,
                {
                    "spearman_m6a_load_delta_log2_hl": r6(causal_r),
                    "length_partial_spearman": r6(partial_r),
                    "partial_permutation_p_two_sided": r6(p_partial),
                    "actual_permutations": actual_perm,
                    "expected": "positive after transcript-length partialing",
                },
            )
        )

        positives = sorted(row["m6a_load"] for row in rows if row["m6a_load"] > 0.0)
        q1 = quantile(positives, 0.25)
        q3 = quantile(positives, 0.75)
        zero = lambda row: row["m6a_load"] == 0.0
        low = lambda row: 0.0 < row["m6a_load"] <= q1
        mid = lambda row: q1 < row["m6a_load"] <= q3
        high = lambda row: row["m6a_load"] > q3
        bin_specs = [("zero", zero), ("low_positive", low), ("middle_positive", mid), ("high_positive", high)]
        bins = []
        for label, pred in bin_specs:
            subset = [row for row in rows if pred(row)]
            bins.append(
                {
                    "bin": label,
                    "n": len(subset),
                    "mean_log2_hl_dmso": r6(mean([row["log_hl_dmso"] for row in subset])),
                    "mean_delta_log2_hl_stm2457_minus_dmso": r6(
                        mean([row["delta_log_hl_stm2457_minus_dmso"] for row in subset])
                    ),
                    "mean_tx_length": r6(mean([row["tx_length"] for row in subset])),
                }
            )
        dmso_means = [item["mean_log2_hl_dmso"] for item in bins]
        delta_means = [item["mean_delta_log2_hl_stm2457_minus_dmso"] for item in bins]
        dose_pass = all(a >= b for a, b in zip(dmso_means, dmso_means[1:])) and all(
            a <= b for a, b in zip(delta_means, delta_means[1:])
        )
        checks.append(
            check(
                "dose_response_bins",
                dose_pass,
                {"positive_load_q1": r6(q1), "positive_load_q3": r6(q3), "bins": bins},
            )
        )

        dmso_high_zero, p_dmso, n_perm_dmso = two_group_permutation(
            rows, high, zero, "log_hl_dmso", "less_equal"
        )
        delta_high_zero, p_delta, n_perm_delta = two_group_permutation(
            rows, high, zero, "delta_log_hl_stm2457_minus_dmso", "greater_equal"
        )
        high_zero_pass = (
            dmso_high_zero is not None
            and dmso_high_zero < 0.0
            and p_dmso is not None
            and p_dmso <= 0.01
            and delta_high_zero is not None
            and delta_high_zero > 0.0
            and p_delta is not None
            and p_delta <= 0.01
        )
        checks.append(
            check(
                "hi_vs_zero_permutation",
                high_zero_pass,
                {
                    "high_minus_zero_log2_hl_dmso": r6(dmso_high_zero),
                    "dmso_p_less_equal": r6(p_dmso),
                    "high_minus_zero_delta_log2_hl": r6(delta_high_zero),
                    "delta_p_greater_equal": r6(p_delta),
                    "actual_permutations": min(n_perm_dmso, n_perm_delta),
                },
            )
        )

        confounded = (not causal_pass) and static_pass and dose_pass
        crosses = static_pass and causal_pass and perm_pass and dose_pass and high_zero_pass
        if crosses:
            verdict = "crosses_boundary"
        elif confounded:
            verdict = "confounded_by_composition"
        else:
            verdict = "does_not_cross"
        result.update(
            {
                "verdict": verdict,
                "static_spearman_m6a_load_log2_hl_dmso": r6(static_r),
                "causal_spearman_m6a_load_delta_log2_hl": r6(causal_r),
                "length_partial_spearman_m6a_load_delta_log2_hl": r6(partial_r),
                "partial_permutation_p_two_sided": r6(p_partial),
                "dose_response_bins": bins,
                "high_vs_zero": {
                    "high_minus_zero_log2_hl_dmso": r6(dmso_high_zero),
                    "dmso_p_less_equal": r6(p_dmso),
                    "high_minus_zero_delta_log2_hl": r6(delta_high_zero),
                    "delta_p_greater_equal": r6(p_delta),
                },
                "status_semantics": (
                    "passed means the external m6A/half-life dataset supports the pre-registered "
                    "boundary statistic; it is not a mechanism or function claim"
                ),
            }
        )
        checks.append(
            check(
                "boundary_verdict",
                crosses,
                {"verdict": verdict, "accepted_positive_verdict": "crosses_boundary"},
            )
        )
        status = "passed" if all(item["passed"] for item in checks) else "failed"
    except Exception as exc:
        if status == "error":
            result["verdict"] = "error"
        result["error"] = str(exc)

    completed_at = now_iso()
    payload = {
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "status": status,
        "checks": checks,
        "result": result,
        "started_at": started_at,
        "completed_at": completed_at,
    }
    print(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    raise SystemExit(0 if status == "passed" else (3 if status == "needs_data" else 1))


if __name__ == "__main__":
    main()

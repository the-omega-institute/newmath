#!/usr/bin/env python3
"""B*_Q6 condition-coupled execution candidate test: yeast SD versus YEPD."""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import random
import sys
from typing import Any

from run_b_star_q6_protein_omics_survival_powered import standard_amino_acids
from run_b_star_q6_translation_survival_powered import fibers_for, project_syn, q_vectors, standard_code


EXPERIMENT_ID = "b_star_q6_condition_interaction_sd_yepd_powered"
CLAIM_ID = "h3.cross_layer_relation.condition_coupled_execution.b_star_q6_sd_yepd_interaction_powered"

ORGANISM = "saccharomyces_cerevisiae"
NCBI_TAXID = "4932"
FOLD_COUNT = 5
NULL_B = 300
PUBLISHABLE_NULL_B = 1000
AA_PC_COUNT = 5
RIDGE_LAMBDA = 1.0
TINY_RIDGE = 1e-8
RANK_TOL = 1e-10
EPS = 1e-12


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def numeric(value: object, field: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{field} must be numeric")
    out = float(value)
    if not math.isfinite(out):
        raise ValueError(f"{field} must be finite")
    return out


def strip_taxid(protein_id: str) -> str:
    prefix = f"{NCBI_TAXID}."
    return protein_id[len(prefix) :] if protein_id.startswith(prefix) else protein_id


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def vector_dot(left: list[float], right: list[float]) -> float:
    return sum(left[i] * right[i] for i in range(len(left)))


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def stdev(values: list[float]) -> float:
    if not values:
        return 1.0
    mu = mean(values)
    var = sum((value - mu) ** 2 for value in values) / len(values)
    return math.sqrt(var) if var > EPS else 1.0


def zscore(values: list[float]) -> list[float]:
    mu = mean(values)
    sd = stdev(values)
    return [(value - mu) / sd for value in values]


def average_rank_z(values_by_gene: dict[str, float], genes: list[str]) -> dict[str, float]:
    pairs = sorted((values_by_gene[gene], gene) for gene in genes)
    ranks: dict[str, float] = {}
    i = 0
    while i < len(pairs):
        j = i + 1
        while j < len(pairs) and pairs[j][0] == pairs[i][0]:
            j += 1
        avg_rank = 0.5 * (i + 1 + j)
        for k in range(i, j):
            ranks[pairs[k][1]] = avg_rank
        i = j
    ranked = [ranks[gene] for gene in genes]
    ranked_z = zscore(ranked)
    return {gene: ranked_z[index] for index, gene in enumerate(genes)}


def percentile95(values: list[float]) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    index = int(math.ceil(0.95 * len(ordered))) - 1
    return ordered[max(0, min(index, len(ordered) - 1))]


def transpose(matrix: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    return [[row[col] for row in matrix] for col in range(len(matrix[0]))]


def matmul_vec(matrix: list[list[float]], coeff: list[float]) -> list[float]:
    return [sum(row[j] * coeff[j] for j in range(len(coeff))) for row in matrix]


def design_xtx_xty(design: list[list[float]], y: list[float]) -> tuple[list[list[float]], list[float]]:
    width = len(design[0])
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    xty = [0.0 for _ in range(width)]
    for row, value in zip(design, y):
        for i in range(width):
            xty[i] += row[i] * value
            ri = row[i]
            for j in range(width):
                xtx[i][j] += ri * row[j]
    return xtx, xty


def solve_linear(matrix: list[list[float]], rhs: list[float], tol: float = RANK_TOL) -> list[float]:
    n = len(rhs)
    aug = [list(matrix[i]) + [rhs[i]] for i in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= tol:
            aug[col][col] += TINY_RIDGE
            pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
            if abs(aug[pivot][col]) <= tol:
                raise ValueError("linear solve is rank deficient")
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        scale = aug[col][col]
        for item in range(col, n + 1):
            aug[col][item] /= scale
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor == 0.0:
                continue
            for item in range(col, n + 1):
                aug[row][item] -= factor * aug[col][item]
    return [aug[row][n] for row in range(n)]


def ridge_fit(design: list[list[float]], y: list[float], lam: float) -> tuple[list[float], float]:
    xtx, xty = design_xtx_xty(design, y)
    for i in range(len(xtx)):
        xtx[i][i] += 0.0 if i == 0 else lam
    beta = solve_linear(xtx, xty)
    pred = matmul_vec(design, beta)
    sse = sum((obs - fit) ** 2 for obs, fit in zip(y, pred))
    return beta, max(sse / max(1, len(y)), EPS)


def ols_coefficients(design: list[list[float]], y: list[float]) -> list[float]:
    xtx, xty = design_xtx_xty(design, y)
    for i in range(len(xtx)):
        xtx[i][i] += TINY_RIDGE
    return solve_linear(xtx, xty)


def residualize_q(
    c_train: list[list[float]],
    c_test: list[list[float]],
    q_train: list[list[float]],
    q_test: list[list[float]],
) -> tuple[list[list[float]], list[list[float]]]:
    q_width = len(q_train[0])
    c_width = len(c_train[0])
    xtx = [[0.0 for _ in range(c_width)] for _ in range(c_width)]
    for row in c_train:
        for i in range(c_width):
            ri = row[i]
            for j in range(c_width):
                xtx[i][j] += ri * row[j]
    for i in range(c_width):
        xtx[i][i] += TINY_RIDGE
    beta_by_q = []
    for j in range(q_width):
        rhs = [0.0 for _ in range(c_width)]
        for row, qrow in zip(c_train, q_train):
            value = qrow[j]
            for k in range(c_width):
                rhs[k] += row[k] * value
        beta_by_q.append(solve_linear(xtx, rhs))
    fitted_train = [[sum(c_train[i][k] * beta_by_q[j][k] for k in range(len(c_train[0]))) for j in range(q_width)] for i in range(len(c_train))]
    fitted_test = [[sum(c_test[i][k] * beta_by_q[j][k] for k in range(len(c_test[0]))) for j in range(q_width)] for i in range(len(c_test))]
    resid_train = [[q_train[i][j] - fitted_train[i][j] for j in range(q_width)] for i in range(len(q_train))]
    resid_test = [[q_test[i][j] - fitted_test[i][j] for j in range(q_width)] for i in range(len(q_test))]
    for j in range(q_width):
        col = [row[j] for row in resid_train]
        mu = mean(col)
        sd = stdev(col)
        for row in resid_train:
            row[j] = (row[j] - mu) / sd
        for row in resid_test:
            row[j] = (row[j] - mu) / sd
    return resid_train, resid_test


def covariance_matrix(centered_rows: list[list[float]]) -> list[list[float]]:
    width = len(centered_rows[0])
    cov = [[0.0 for _ in range(width)] for _ in range(width)]
    denom = max(1, len(centered_rows) - 1)
    for row in centered_rows:
        for i in range(width):
            for j in range(width):
                cov[i][j] += row[i] * row[j] / denom
    return cov


def mat_vec_square(matrix: list[list[float]], vec: list[float]) -> list[float]:
    return [sum(matrix[i][j] * vec[j] for j in range(len(vec))) for i in range(len(matrix))]


def top_pca_components(train_rows: list[list[float]], count: int) -> tuple[list[float], list[list[float]]]:
    width = len(train_rows[0])
    center = [mean([row[j] for row in train_rows]) for j in range(width)]
    centered = [[row[j] - center[j] for j in range(width)] for row in train_rows]
    cov = covariance_matrix(centered)
    components: list[list[float]] = []
    for comp_index in range(count):
        vec = [0.0 for _ in range(width)]
        vec[comp_index % width] = 1.0
        for prev in components:
            coeff = vector_dot(vec, prev)
            vec = [vec[i] - coeff * prev[i] for i in range(width)]
        norm = math.sqrt(vector_dot(vec, vec))
        if norm <= EPS:
            vec = [1.0 / math.sqrt(width) for _ in range(width)]
        else:
            vec = [value / norm for value in vec]
        for _ in range(80):
            nxt = mat_vec_square(cov, vec)
            for prev in components:
                coeff = vector_dot(nxt, prev)
                nxt = [nxt[i] - coeff * prev[i] for i in range(width)]
            norm = math.sqrt(vector_dot(nxt, nxt))
            if norm <= EPS:
                break
            vec = [value / norm for value in nxt]
        components.append(vec)
        eigen = vector_dot(vec, mat_vec_square(cov, vec))
        for i in range(width):
            for j in range(width):
                cov[i][j] -= eigen * vec[i] * vec[j]
    return center, components


def project_pcs(row: list[float], center: list[float], components: list[list[float]]) -> list[float]:
    centered = [row[i] - center[i] for i in range(len(row))]
    return [vector_dot(centered, comp) for comp in components]


def quantile_bins(values: list[float], bin_count: int) -> list[int]:
    ordered = sorted((value, index) for index, value in enumerate(values))
    out = [0 for _ in values]
    for rank, (_, index) in enumerate(ordered):
        out[index] = min(bin_count - 1, int(rank * bin_count / max(1, len(values))))
    return out


def deterministic_fold(gene: str) -> int:
    digest = hashlib.sha256(f"{EXPERIMENT_ID}|fold|{gene}".encode("utf-8")).digest()
    return int.from_bytes(digest[:4], "big") % FOLD_COUNT


def seeded_rng(label: str, b: int) -> random.Random:
    digest = hashlib.sha256(f"{EXPERIMENT_ID}|{label}|{b}".encode("utf-8")).digest()
    return random.Random(int.from_bytes(digest[:8], "big"))


class FoldContext:
    def __init__(
        self,
        train_idx: list[int],
        test_idx: list[int],
        c_train: list[list[float]],
        c_test: list[list[float]],
    ) -> None:
        self.train_idx = train_idx
        self.test_idx = test_idx
        self.c_train = c_train
        self.c_test = c_test


def build_fold_contexts(rows: list[dict[str, Any]], extra_slots: list[str] | None = None) -> list[FoldContext]:
    extra_slots = extra_slots or []
    contexts: list[FoldContext] = []
    for fold in range(FOLD_COUNT):
        train_idx = [i for i, row in enumerate(rows) if row["fold"] != fold]
        test_idx = [i for i, row in enumerate(rows) if row["fold"] == fold]
        aa_train = [rows[i]["aa_comp"] for i in train_idx]
        aa_center, aa_components = top_pca_components(aa_train, AA_PC_COUNT)
        raw_scalar_names = ["log_len", "gc3", "plddt", "plddt_missing", "baseline_log10"] + extra_slots
        scalar_means: dict[str, float] = {}
        scalar_sds: dict[str, float] = {}
        for name in raw_scalar_names:
            values = [rows[i][name] for i in train_idx]
            scalar_means[name] = mean(values)
            scalar_sds[name] = stdev(values)

        def c_row(i: int) -> list[float]:
            row = rows[i]
            features = project_pcs(row["aa_comp"], aa_center, aa_components)
            features += [(row[name] - scalar_means[name]) / scalar_sds[name] for name in raw_scalar_names]
            return [1.0] + features

        contexts.append(
            FoldContext(
                train_idx=train_idx,
                test_idx=test_idx,
                c_train=[c_row(i) for i in train_idx],
                c_test=[c_row(i) for i in test_idx],
            )
        )
    return contexts


class EvalFold:
    def __init__(self, ctx: FoldContext, y: list[float], lam: float) -> None:
        self.ctx = ctx
        self.y_train = [y[i] for i in ctx.train_idx]
        self.y_test = [y[i] for i in ctx.test_idx]
        self.b0, self.sig0 = ridge_fit(ctx.c_train, self.y_train, lam)
        self.p0 = matmul_vec(ctx.c_test, self.b0)
        self.train_mean = mean(self.y_train)
        self.sse0 = 0.0
        self.sst = 0.0
        self.logpd0 = 0.0
        for obs, pred0 in zip(self.y_test, self.p0):
            e0 = obs - pred0
            self.sse0 += e0 * e0
            self.sst += (obs - self.train_mean) ** 2
            self.logpd0 += -0.5 * (math.log(2.0 * math.pi * self.sig0) + (e0 * e0) / self.sig0)


class EvalContext:
    def __init__(self, y: list[float], contexts: list[FoldContext], lam: float = RIDGE_LAMBDA) -> None:
        self.y = y
        self.contexts = contexts
        self.lam = lam
        self.folds = [EvalFold(ctx, y, lam) for ctx in contexts]


def evaluate_prepared(eval_ctx: EvalContext, q_matrix: list[list[float]]) -> dict[str, float]:
    total_sse0 = 0.0
    total_sse1 = 0.0
    total_sst = 0.0
    total_logpd0 = 0.0
    total_logpd1 = 0.0
    n_test_total = 0
    for fold in eval_ctx.folds:
        ctx = fold.ctx
        q_train = [q_matrix[i] for i in ctx.train_idx]
        q_test = [q_matrix[i] for i in ctx.test_idx]
        qr_train, qr_test = residualize_q(ctx.c_train, ctx.c_test, q_train, q_test)
        x1_train = [ctx.c_train[i] + qr_train[i] for i in range(len(ctx.c_train))]
        x1_test = [ctx.c_test[i] + qr_test[i] for i in range(len(ctx.c_test))]
        b1, sig1 = ridge_fit(x1_train, fold.y_train, eval_ctx.lam)
        p1 = matmul_vec(x1_test, b1)
        total_sse0 += fold.sse0
        total_sst += fold.sst
        total_logpd0 += fold.logpd0
        for obs, pred1 in zip(fold.y_test, p1):
            e1 = obs - pred1
            total_sse1 += e1 * e1
            total_logpd1 += -0.5 * (math.log(2.0 * math.pi * sig1) + (e1 * e1) / sig1)
            n_test_total += 1
    r2_m0 = 1.0 - total_sse0 / max(total_sst, EPS)
    r2_m1 = 1.0 - total_sse1 / max(total_sst, EPS)
    saving_nats = 0.5 * n_test_total * math.log(max(total_sse0, EPS) / max(total_sse1, EPS))
    dl_cost = 0.5 * (9 + 1) * math.log(max(2, n_test_total))
    return {
        "r2_m0": r2_m0,
        "r2_m1": r2_m1,
        "delta_r2": r2_m1 - r2_m0,
        "sse_m0": total_sse0,
        "sse_m1": total_sse1,
        "delta_logpd": total_logpd1 - total_logpd0,
        "n_test": float(n_test_total),
        "residual_code_saving_nats": saving_nats,
        "q_lambda_encoding_cost_nats": dl_cost,
        "description_length_drop_nats": saving_nats - dl_cost,
    }


def evaluate_model(
    rows: list[dict[str, Any]],
    y: list[float],
    q_matrix: list[list[float]],
    contexts: list[FoldContext],
    lam: float = RIDGE_LAMBDA,
) -> dict[str, float]:
    return evaluate_prepared(EvalContext(y, contexts, lam), q_matrix)


def load_abundance(path: pathlib.Path, key: str) -> dict[str, float]:
    payload = load_json(path)
    raw = payload.get("protein_abundance")
    if not isinstance(raw, dict):
        raise ValueError(f"{path} lacks protein_abundance")
    out: dict[str, float] = {}
    for protein_id, value in raw.items():
        abundance = numeric(value, f"{key}.{protein_id}")
        if abundance > 0.0:
            out[strip_taxid(str(protein_id))] = abundance
    return out


def load_structural_order(path: pathlib.Path) -> dict[str, float]:
    payload = load_json(path)
    proteins = payload.get("proteins")
    if not isinstance(proteins, list):
        raise ValueError("structural-order payload lacks proteins")
    out: dict[str, float] = {}
    for row in proteins:
        if isinstance(row, dict) and isinstance(row.get("protein_id"), str):
            out[strip_taxid(row["protein_id"])] = numeric(row.get("structural_order"), "structural_order")
    return out


def load_m2_slots(repo: pathlib.Path) -> dict[str, dict[str, float]]:
    te_payload = load_json(repo / "tools/bio_reality/data/ribosome_te_saccharomyces_cerevisiae.json")
    hl_payload = load_json(repo / "tools/bio_reality/data/mrna_half_life_saccharomyces_cerevisiae_neymotin.json")
    turnover_payload = load_json(repo / "tools/bio_reality/data/protein_turnover_saccharomyces_cerevisiae.json")
    te: dict[str, float] = {}
    for row in te_payload.get("genes", []):
        if isinstance(row, dict) and isinstance(row.get("protein_id"), str):
            val = numeric(row.get("te"), "te")
            if val > 0.0:
                te[strip_taxid(row["protein_id"])] = math.log(val)
    half_life: dict[str, float] = {}
    for row in hl_payload.get("records", []):
        if isinstance(row, dict) and isinstance(row.get("Syst"), str):
            val = numeric(row.get("thalf"), "thalf")
            if val > 0.0:
                half_life[row["Syst"]] = math.log(val)
    turnover: dict[str, float] = {}
    for protein_id, value in turnover_payload.get("protein_turnover", {}).items():
        val = numeric(value, "protein_turnover")
        if val > 0.0:
            turnover[strip_taxid(str(protein_id))] = math.log(val)
    return {"log_te": te, "log_mrna_half_life": half_life, "log_protein_half_life": turnover}


def codon_counts_from_ordered(codons_dna: list[str], sense_codons: list[str]) -> dict[str, int]:
    counts = {codon: 0 for codon in sense_codons}
    for raw in codons_dna:
        codon = dna_to_rna(str(raw))
        if codon in counts:
            counts[codon] += 1
    return counts


def effective_number(counts: dict[str, int], code: dict[str, str], fibers: dict[str, list[str]]) -> float:
    total = sum(counts.values())
    if total <= 0:
        return 0.0
    weighted = 0.0
    for aa, fiber in fibers.items():
        n_aa = sum(counts.get(codon, 0) for codon in fiber)
        if n_aa <= 0:
            continue
        homozygosity = sum((counts.get(codon, 0) / n_aa) ** 2 for codon in fiber)
        if homozygosity > EPS:
            weighted += (n_aa / total) * (1.0 / homozygosity)
    return weighted


def build_rows(repo: pathlib.Path) -> tuple[list[dict[str, Any]], list[str], list[str], dict[str, dict[str, float]]]:
    sd = load_abundance(repo / "tools/bio_reality/data/proteomics_abundance_saccharomyces_cerevisiae_sd.json", "SD")
    yepd = load_abundance(repo / "tools/bio_reality/data/proteomics_abundance_saccharomyces_cerevisiae_yepd.json", "YEPD")
    baseline = load_abundance(repo / "tools/bio_reality/data/proteomics_abundance_saccharomyces_cerevisiae.json", "integrated")
    structural = load_structural_order(repo / "tools/bio_reality/data/structural_order_saccharomyces_cerevisiae.json")
    m2_slots = load_m2_slots(repo)

    code = standard_code(repo)
    sense_codons = [codon for codon in sorted(code) if code[codon] != "*"]
    fibers = fibers_for(code, sense_codons)
    aa_order = standard_amino_acids(code, sense_codons)
    q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(sense_codons).items()}
    q_names = list(q_projected)
    if len(q_names) != 9:
        raise ValueError("B*_Q6 coordinate count is not 9")

    cds_payload = load_json(repo / "tools/bio_reality/data/cds_ordered_sequences_saccharomyces_cerevisiae.json")
    cds_records = cds_payload.get("cds")
    if not isinstance(cds_records, list):
        raise ValueError("ordered CDS payload lacks cds")
    cds_by_gene = {str(row["gene_id"]): row for row in cds_records if isinstance(row, dict) and isinstance(row.get("gene_id"), str)}
    genes = sorted(set(sd) & set(yepd) & set(baseline) & set(cds_by_gene))
    sd_rank = average_rank_z(sd, genes)
    yepd_rank = average_rank_z(yepd, genes)
    delta_log_raw = [math.log(sd[gene]) - math.log(yepd[gene]) for gene in genes]
    delta_log_z = dict(zip(genes, zscore(delta_log_raw)))
    mean_rank = {gene: 0.5 * (sd_rank[gene] + yepd_rank[gene]) for gene in genes}

    rows: list[dict[str, Any]] = []
    for gene in genes:
        record = cds_by_gene[gene]
        codons_dna = record.get("codons")
        if not isinstance(codons_dna, list):
            continue
        counts = codon_counts_from_ordered(codons_dna, sense_codons)
        total = sum(counts.values())
        if total <= 0:
            continue
        aa_counts = {aa: 0 for aa in aa_order}
        for codon in sense_codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        if aa_total <= 0:
            continue
        freqs = {codon: counts[codon] / total for codon in sense_codons}
        q_row = []
        for name in q_names:
            qvec = q_projected[name]
            denom = math.sqrt(sum(qvec[codon] * qvec[codon] for codon in sense_codons))
            q_row.append(sum(freqs[codon] * qvec[codon] for codon in sense_codons) / denom)
        gc3 = sum(counts[codon] for codon in sense_codons if codon[2] in {"G", "C"}) / total
        plddt_missing = 0.0 if gene in structural else 1.0
        row = {
            "gene": gene,
            "fold": deterministic_fold(gene),
            "sd_abundance": sd[gene],
            "yepd_abundance": yepd[gene],
            "sd_rank_z": sd_rank[gene],
            "yepd_rank_z": yepd_rank[gene],
            "delta_rank_signed": sd_rank[gene] - yepd_rank[gene],
            "delta_log_signed": delta_log_z[gene],
            "abs_delta_rank": abs(sd_rank[gene] - yepd_rank[gene]),
            "mean_rank": mean_rank[gene],
            "baseline_log10": math.log10(baseline[gene]),
            "log_len": math.log(total),
            "aa_comp": [aa_counts[aa] / aa_total for aa in aa_order],
            "gc3": gc3,
            "plddt": structural.get(gene, 0.0),
            "plddt_missing": plddt_missing,
            "q": q_row,
            "codon_counts": counts,
            "aa_counts": aa_counts,
            "sense_total": total,
            "enc_proxy": effective_number(counts, code, fibers),
        }
        complete_m2 = True
        for slot_name, slot_map in m2_slots.items():
            if gene in slot_map:
                row[slot_name] = slot_map[gene]
                row[f"{slot_name}_missing"] = 0.0
            else:
                row[slot_name] = 0.0
                row[f"{slot_name}_missing"] = 1.0
                complete_m2 = False
        row["complete_m2"] = complete_m2
        rows.append(row)
    return rows, q_names, aa_order, m2_slots


def q_matrix(rows: list[dict[str, Any]]) -> list[list[float]]:
    return [list(row["q"]) for row in rows]


def target(rows: list[dict[str, Any]], name: str) -> list[float]:
    return [float(row[name]) for row in rows]


def shuffled_within_bins(values: list[list[float]], keys: list[tuple[int, ...]], rng: random.Random) -> list[list[float]]:
    buckets: dict[tuple[int, ...], list[int]] = {}
    for index, key in enumerate(keys):
        buckets.setdefault(key, []).append(index)
    out = [list(row) for row in values]
    for key, indices in buckets.items():
        if len(indices) <= 1:
            continue
        source = indices[:]
        rng.shuffle(source)
        for dest, src in zip(indices, source):
            out[dest] = list(values[src])
    return out


def matched_bin_keys(rows: list[dict[str, Any]]) -> list[tuple[int, ...]]:
    aa_center, aa_components = top_pca_components([row["aa_comp"] for row in rows], 1)
    aa_pc1 = [project_pcs(row["aa_comp"], aa_center, aa_components)[0] for row in rows]
    cols = [
        [row["log_len"] for row in rows],
        aa_pc1,
        [row["gc3"] for row in rows],
        [row["mean_rank"] for row in rows],
        [row["baseline_log10"] for row in rows],
    ]
    binned = [quantile_bins(col, 4) for col in cols]
    keys = [tuple(binned[col][i] for col in range(len(binned))) for i in range(len(rows))]
    bucket_sizes: dict[tuple[int, ...], int] = {}
    for key in keys:
        bucket_sizes[key] = bucket_sizes.get(key, 0) + 1
    relaxed: list[tuple[int, ...]] = []
    for key in keys:
        if bucket_sizes[key] >= 3:
            relaxed.append(key)
        else:
            relaxed.append(key[:4])
    return relaxed


def sample_multinomial(total: int, weights: list[float], rng: random.Random) -> list[int]:
    if total <= 0:
        return [0 for _ in weights]
    positive = [max(0.0, weight) for weight in weights]
    if sum(positive) <= 0.0:
        positive = [1.0 for _ in weights]
    probs = [weight / sum(positive) for weight in positive]
    counts = [0 for _ in weights]
    cumulative: list[float] = []
    running = 0.0
    for prob in probs:
        running += prob
        cumulative.append(running)
    cumulative[-1] = 1.0
    for _ in range(total):
        u = rng.random()
        for index, boundary in enumerate(cumulative):
            if u <= boundary:
                counts[index] += 1
                break
    return counts


def sample_multinomial_fast(population: list[str], weights: list[float], total: int, rng: random.Random) -> dict[str, int]:
    if total <= 0:
        return {}
    if len(population) == 1:
        return {population[0]: total}
    positive = [max(0.0, weight) for weight in weights]
    if sum(positive) <= 0.0:
        positive = [1.0 for _ in population]
    total_weight = sum(positive)
    expected = [total * weight / total_weight for weight in positive]
    base = [int(math.floor(value)) for value in expected]
    remainder = total - sum(base)
    counts = {codon: count for codon, count in zip(population, base) if count}
    if remainder > 0:
        fractional = [value - math.floor(value) for value in expected]
        if sum(fractional) <= EPS:
            fractional = positive
        picked = rng.choices(population, weights=fractional, k=remainder)
        for codon in picked:
            counts[codon] = counts.get(codon, 0) + 1
    return counts


def build_recoder_context(rows: list[dict[str, Any]], q_names: list[str], repo: pathlib.Path) -> dict[str, Any]:
    code = standard_code(repo)
    sense_codons = [codon for codon in sorted(code) if code[codon] != "*"]
    fibers = fibers_for(code, sense_codons)
    q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(sense_codons).items()}
    pooled = {codon: 1.0 for codon in sense_codons}
    for row in rows:
        for codon, count in row["codon_counts"].items():
            pooled[codon] += count
    fiber_parts = {}
    for aa, fiber in fibers.items():
        gc_codons = [codon for codon in fiber if codon[2] in {"G", "C"}]
        at_codons = [codon for codon in fiber if codon[2] not in {"G", "C"}]
        fiber_parts[aa] = {
            "fiber": fiber,
            "gc_codons": gc_codons,
            "gc_weights": [pooled[codon] for codon in gc_codons],
            "at_codons": at_codons,
            "at_weights": [pooled[codon] for codon in at_codons],
            "fiber_weights": [pooled[codon] for codon in fiber],
        }
    q_arrays = [
        {
            "name": name,
            "denom": math.sqrt(sum(q_projected[name][codon] * q_projected[name][codon] for codon in sense_codons)),
            "weights": q_projected[name],
        }
        for name in q_names
    ]
    row_specs = []
    for row in rows:
        tasks = []
        original_counts = row["codon_counts"]
        for aa, fiber in fibers.items():
            parts = fiber_parts[aa]
            n_gc = sum(original_counts[codon] for codon in fiber if codon[2] in {"G", "C"})
            n_at = sum(original_counts[codon] for codon in fiber if codon[2] not in {"G", "C"})
            if n_gc:
                if parts["gc_codons"]:
                    tasks.append((parts["gc_codons"], parts["gc_weights"], n_gc))
                else:
                    tasks.append((parts["fiber"], parts["fiber_weights"], n_gc))
            if n_at:
                if parts["at_codons"]:
                    tasks.append((parts["at_codons"], parts["at_weights"], n_at))
                else:
                    tasks.append((parts["fiber"], parts["fiber_weights"], n_at))
        row_specs.append(
            {
                "tasks": tasks,
                "sense_total": row["sense_total"],
                "gc3": row["gc3"],
                "enc_proxy": row["enc_proxy"],
            }
        )
    return {
        "code": code,
        "sense_codons": sense_codons,
        "fibers": fibers,
        "fiber_parts": fiber_parts,
        "q_arrays": q_arrays,
        "row_specs": row_specs,
    }


def synonymous_recoded_q(
    rows: list[dict[str, Any]],
    recoder: dict[str, Any],
    rng: random.Random,
) -> tuple[list[list[float]], dict[str, float]]:
    code = recoder["code"]
    sense_codons = recoder["sense_codons"]
    fibers = recoder["fibers"]
    q_arrays = recoder["q_arrays"]
    row_specs = recoder["row_specs"]
    gc3_abs_diffs: list[float] = []
    enc_rel_diffs: list[float] = []
    out: list[list[float]] = []
    for spec in row_specs:
        new_counts: dict[str, int] = {}
        for population, weights, total_for_task in spec["tasks"]:
            sampled_map = sample_multinomial_fast(population, weights, total_for_task, rng)
            for codon, count in sampled_map.items():
                new_counts[codon] = new_counts.get(codon, 0) + count
        total = spec["sense_total"]
        gc3_abs_diffs.append(0.0)
        enc_new = effective_number(new_counts, code, fibers)
        enc_old = spec["enc_proxy"]
        if enc_old > EPS:
            enc_rel_diffs.append(abs(enc_new - enc_old) / enc_old)
        q_row: list[float] = []
        for q_item in q_arrays:
            qvec = q_item["weights"]
            q_row.append(sum(count * qvec[codon] for codon, count in new_counts.items()) / total / q_item["denom"])
        out.append(q_row)
    return out, {
        "mean_abs_gc3_error": mean(gc3_abs_diffs),
        "p95_abs_gc3_error": percentile95(gc3_abs_diffs) or 0.0,
        "mean_relative_enc_proxy_error": mean(enc_rel_diffs),
        "p95_relative_enc_proxy_error": percentile95(enc_rel_diffs) or 0.0,
    }


def null_summary(values: list[dict[str, float]]) -> dict[str, object]:
    return {
        "actual_B": len(values),
        "publishable_B": PUBLISHABLE_NULL_B,
        "delta_r2_null95": percentile95([v["delta_r2"] for v in values]),
        "delta_logpd_null95": percentile95([v["delta_logpd"] for v in values]),
        "description_length_drop_null95": percentile95([v["description_length_drop_nats"] for v in values]),
        "max_delta_r2_seen": max((v["delta_r2"] for v in values), default=None),
        "max_delta_logpd_seen": max((v["delta_logpd"] for v in values), default=None),
    }


def run_nulls(
    rows: list[dict[str, Any]],
    q_obs: list[list[float]],
    y_signed: list[float],
    contexts: list[FoldContext],
    q_names: list[str],
    repo: pathlib.Path,
) -> dict[str, object]:
    sign_results: list[dict[str, float]] = []
    matched_results: list[dict[str, float]] = []
    recoded_results: list[dict[str, float]] = []
    matched_keys = matched_bin_keys(rows)
    recoder = build_recoder_context(rows, q_names, repo)
    eval_ctx = EvalContext(y_signed, contexts)
    recoding_diagnostics: list[dict[str, float]] = []
    for b in range(NULL_B):
        rng = seeded_rng("condition_sign_flip_null", b)
        y_flip = [(-value if rng.random() < 0.5 else value) for value in y_signed]
        sign_results.append(evaluate_prepared(EvalContext(y_flip, contexts), q_obs))

        rng = seeded_rng("matched_q_permutation_null", b)
        q_perm = shuffled_within_bins(q_obs, matched_keys, rng)
        matched_results.append(evaluate_prepared(eval_ctx, q_perm))

        rng = seeded_rng("synonymous_recoding_null", b)
        q_recoded, diag = synonymous_recoded_q(rows, recoder, rng)
        recoding_diagnostics.append(diag)
        recoded_results.append(evaluate_prepared(eval_ctx, q_recoded))
    return {
        "condition_sign_flip": {
            **null_summary(sign_results),
            "null_model": "per-gene deterministic random sign flip of signed rank-normalized DeltaP",
        },
        "matched_q_permutation": {
            **null_summary(matched_results),
            "null_model": "Q rows permuted within length / aa-PC1 / GC3 / mean-rank-abundance / integrated-baseline bins",
        },
        "synonymous_recoding": {
            **null_summary(recoded_results),
            "null_model": "amino-acid sequence preserved; per-amino-acid GC3-ending counts preserved exactly; ENC proxy monitored",
            "constraint_diagnostics_mean_over_nulls": {
                "mean_abs_gc3_error": mean([d["mean_abs_gc3_error"] for d in recoding_diagnostics]),
                "p95_abs_gc3_error": mean([d["p95_abs_gc3_error"] for d in recoding_diagnostics]),
                "mean_relative_enc_proxy_error": mean([d["mean_relative_enc_proxy_error"] for d in recoding_diagnostics]),
                "p95_relative_enc_proxy_error": mean([d["p95_relative_enc_proxy_error"] for d in recoding_diagnostics]),
            },
        },
        "replicate_placebo": {
            "actual_B": 0,
            "null95": None,
            "replicate_placebo": "unavailable",
            "reason": "SD/YEPD wrappers expose endpoint condition abundance only, not same-condition replicate abundance columns",
        },
    }


def gate_against_nulls(observed: dict[str, float], nulls: dict[str, object]) -> dict[str, object]:
    applicable = ["condition_sign_flip", "matched_q_permutation", "synonymous_recoding"]
    per_null: dict[str, object] = {}
    all_pass = True
    for name in applicable:
        row = nulls[name]
        if not isinstance(row, dict):
            raise ValueError("null summary malformed")
        r2_95 = float(row["delta_r2_null95"])
        logpd_95 = float(row["delta_logpd_null95"])
        passed = observed["delta_r2"] > r2_95 and observed["delta_logpd"] > logpd_95
        per_null[name] = {
            "delta_r2_above_null95": observed["delta_r2"] > r2_95,
            "delta_logpd_above_null95": observed["delta_logpd"] > logpd_95,
            "joint_pass": passed,
        }
        all_pass = all_pass and passed
    return {"all_applicable_null95_pass": all_pass, "per_null": per_null}


def main() -> None:
    repo = pathlib.Path.cwd()
    try:
        required = [
            "tools/bio_reality/data/proteomics_abundance_saccharomyces_cerevisiae_sd.json",
            "tools/bio_reality/data/proteomics_abundance_saccharomyces_cerevisiae_yepd.json",
            "tools/bio_reality/data/proteomics_abundance_saccharomyces_cerevisiae.json",
            "tools/bio_reality/data/cds_ordered_sequences_saccharomyces_cerevisiae.json",
            "tools/bio_reality/data/structural_order_saccharomyces_cerevisiae.json",
            "tools/bio_reality/data/ribosome_te_saccharomyces_cerevisiae.json",
            "tools/bio_reality/data/mrna_half_life_saccharomyces_cerevisiae_neymotin.json",
            "tools/bio_reality/data/protein_turnover_saccharomyces_cerevisiae.json",
            "tools/bio_reality/data/ncbi_genetic_codes.json",
        ]
        missing = [path for path in required if not (repo / path).exists()]
        if missing:
            emit("needs_data", checks=[], missing_required_data=missing)

        rows, q_names, aa_order, m2_slot_maps = build_rows(repo)
        if len(rows) < 500:
            emit("needs_data", checks=[], reason="SD/YEPD/CDS shared join below n>=500", n_genes=len(rows))

        q_obs = q_matrix(rows)
        y_signed = target(rows, "delta_rank_signed")
        contexts = build_fold_contexts(rows)
        observed = evaluate_model(rows, y_signed, q_obs, contexts)
        y_log = target(rows, "delta_log_signed")
        log_ratio_sensitivity = evaluate_model(rows, y_log, q_obs, contexts)
        y_abs = zscore(target(rows, "abs_delta_rank"))
        abs_delta_side = evaluate_model(rows, y_abs, q_obs, contexts)
        y_mean = zscore(target(rows, "mean_rank"))
        mean_p_side = evaluate_model(rows, y_mean, q_obs, contexts)

        rows_with_mean_control = [dict(row, mean_rank_control=row["mean_rank"]) for row in rows]
        mean_control_contexts = build_fold_contexts(rows_with_mean_control, ["mean_rank_control"])
        signed_with_mean_control = evaluate_model(rows_with_mean_control, y_signed, q_obs, mean_control_contexts)

        m2_rows = [row for row in rows if row["complete_m2"]]
        m2_q = q_matrix(m2_rows)
        m2_y = target(m2_rows, "delta_rank_signed")
        m2_contexts_c = build_fold_contexts(m2_rows)
        m2_contexts_slots = build_fold_contexts(
            m2_rows,
            ["log_te", "log_mrna_half_life", "log_protein_half_life"],
        )
        m2_without_slots_same_subset = evaluate_model(m2_rows, m2_y, m2_q, m2_contexts_c)
        m2_with_slots = evaluate_model(m2_rows, m2_y, m2_q, m2_contexts_slots)

        nulls = run_nulls(rows, q_obs, y_signed, contexts, q_names, repo)
        null_gate = gate_against_nulls(observed, nulls)
        dl_gate = observed["description_length_drop_nats"] > 0.0
        positive = bool(null_gate["all_applicable_null95_pass"]) and dl_gate
        verdict = "condition_coupled_execution_positive" if positive else "no_compressible_q_interaction"

        fold_sizes = {str(fold): sum(1 for row in rows if row["fold"] == fold) for fold in range(FOLD_COUNT)}
        controls_used = [
            "intercept",
            "log CDS sense-codon length",
            f"{AA_PC_COUNT} train-fold PCA coordinates from 20 amino-acid composition proportions: " + ",".join(aa_order),
            "GC3 from ordered CDS codons",
            "mean pLDDT structural-order proxy with missingness indicator",
            "integrated PaxDb log10 baseline abundance; wrapper has dataset-level coverage/score but no per-gene reliability score",
        ]
        checks = [
            {
                "name": "delta_p_constructed_signed",
                "passed": all(math.isfinite(value) for value in y_signed) and abs(mean(y_signed)) < 1e-9,
                "actual": {
                    "construction": "DeltaP_g = z_rank(P_SD) - z_rank(P_YEPD)",
                    "n_genes": len(rows),
                    "target_mean": mean(y_signed),
                    "target_sd": stdev(y_signed),
                    "log_ratio_sensitivity_target": "zscore(log(P_SD)-log(P_YEPD))",
                },
                "expected": "signed rank-normalized DeltaP, not abs(DeltaP) and not mean abundance",
            },
            {
                "name": "controls_C_assembled",
                "passed": len(rows) >= 500 and len(q_names) == 9,
                "actual": {
                    "controls_used": controls_used,
                    "fold_sizes": fold_sizes,
                    "structural_order_missing_n": sum(int(row["plddt_missing"]) for row in rows),
                    "m2_complete_case_n": len(m2_rows),
                },
                "expected": "C includes log length, aa-comp PCs, GC3, structural order, and integrated baseline abundance/reliability provenance",
            },
            {
                "name": "q9_residualized_train_only",
                "passed": len(q_names) == 9,
                "actual": {
                    "coordinates": q_names,
                    "residualization": "for each fold, Q~C is fit on train genes only; held-out Q residuals use the train-fit coefficients and train residual scaling",
                    "ridge_lambda": RIDGE_LAMBDA,
                },
                "expected": "pre-registered 9D B*_Q6; no new Q dimensions and no leakage from held-out folds",
            },
            {
                "name": "heldout_gene_folds_m1_vs_m0",
                "passed": all(size > 0 for size in fold_sizes.values()) and math.isfinite(observed["delta_r2"]) and math.isfinite(observed["delta_logpd"]),
                "actual": observed,
                "expected": "5 held-out gene-level folds comparing M0:DeltaP~C to M1:DeltaP~C+Q",
            },
            {
                "name": "description_length_drop",
                "passed": math.isfinite(observed["description_length_drop_nats"]),
                "actual": {
                    "dl_gate_passed": dl_gate,
                    "residual_code_saving_nats": observed["residual_code_saving_nats"],
                    "q9_plus_lambda_encoding_cost_nats": observed["q_lambda_encoding_cost_nats"],
                    "description_length_drop_nats": observed["description_length_drop_nats"],
                },
                "expected": "DL gate passes only if residual code saving exceeds 9D Q plus lambda encoding cost",
            },
            {
                "name": "four_class_nulls",
                "passed": all(isinstance(nulls[name], dict) and int(nulls[name]["actual_B"]) == NULL_B for name in ["condition_sign_flip", "matched_q_permutation", "synonymous_recoding"])
                and nulls["replicate_placebo"]["replicate_placebo"] == "unavailable",
                "actual": nulls,
                "expected": "condition sign-flip, matched-Q permutation, synonymous-recoding, and replicate placebo skip-if-unavailable are reported separately",
            },
            {
                "name": "anti_vacuity_signed_only",
                "passed": True,
                "actual": {
                    "main_target": "signed rank-normalized DeltaP only",
                    "not_used_for_main_conclusion": ["abs_delta_rank", "mean_rank", "GO/stress/high-P/low-P subgroups"],
                    "abs_delta_only_side_evidence": abs_delta_side,
                    "mean_p_side_evidence": mean_p_side,
                    "signed_delta_with_endpoint_mean_rank_extra_control_side_evidence": signed_with_mean_control,
                },
                "expected": "no post-hoc subgroup separator; |DeltaP| and mean-P are side evidence only",
            },
            {
                "name": "condition_interaction_verdict",
                "passed": True,
                "actual": {
                    "verdict": verdict,
                    "positive_gate": {
                        "heldout_delta_r2_and_delta_logpd_above_all_applicable_null95": null_gate["all_applicable_null95_pass"],
                        "description_length_drop": dl_gate,
                        "per_null": null_gate["per_null"],
                    },
                },
                "expected": "POSITIVE only if M1 held-out gains exceed null95 for every applicable null class and DL drops; otherwise NEGATIVE without over-claim",
            },
        ]
        payload = {
            "organism": ORGANISM,
            "n_genes": len(rows),
            "fold_count": FOLD_COUNT,
            "actual_B": NULL_B,
            "publishable_null_B": PUBLISHABLE_NULL_B,
            "rank_normalized_signed_delta_main": observed,
            "rank_vs_log_ratio_sensitivity": log_ratio_sensitivity,
            "nulls": nulls,
            "null_gate": null_gate,
            "description_length": {
                "before_nats": 0.5 * observed["n_test"] * (1.0 + math.log(2.0 * math.pi * max(observed["sse_m0"] / observed["n_test"], EPS))),
                "after_residual_nats": 0.5 * observed["n_test"] * (1.0 + math.log(2.0 * math.pi * max(observed["sse_m1"] / observed["n_test"], EPS))),
                "q9_plus_lambda_encoding_cost_nats": observed["q_lambda_encoding_cost_nats"],
                "drop_after_cost_nats": observed["description_length_drop_nats"],
                "dl_gate_passed": dl_gate,
            },
            "mean_P_control_side_evidence": {
                "q_predicts_mean_rank_target": mean_p_side,
                "signed_delta_with_endpoint_mean_rank_extra_control": signed_with_mean_control,
                "mean_rank_not_in_main_C": True,
            },
            "abs_delta_only_side_evidence": abs_delta_side,
            "m2_absorption_result": {
                "n_complete_case_genes": len(m2_rows),
                "without_observed_rate_slots_same_subset": m2_without_slots_same_subset,
                "with_observed_rate_slots_log_TE_log_mRNA_half_life_log_protein_half_life": m2_with_slots,
                "interpretation": "M2 is optional/proxy absorption only; slots are not matched condition-specific rate-function identifiers",
            },
            "final_conclusion": verdict,
            "conclusion_text": (
                "同一 synonymous DNA 残差在 SD/YEPD 环境切换下给出 held-out、超 null、DL 下降的 directional condition-coupled execution candidate。"
                if positive
                else "SD/YEPD 两 endpoint 条件中未得到可压缩、超 null 且 DL 下降的 signed Q-interaction；这不否定静态 Q->P，也不否定其它条件下 execution。"
            ),
            "cannot_claim": [
                "endpoint condition-specific GFP/PaxDb abundance readout only; not absolute calibrated per-cell protein quantity",
                "no same-condition mRNA+RPF+turnover panel, so cannot identify whether k_tl*M, delta_m, delta_p, or growth dilution mu changed",
                "condition-coupled execution candidate is a statistical held-out compression claim, not a causal rate-function localization",
                "replicate placebo is unavailable because wrappers do not expose same-condition replicate abundance columns",
            ],
        }
        emit("passed", checks=checks, payload=payload)
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="condition interaction experiment could not be computed")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""ProteinGym DMS loss test for edge-hiding code robustness.

The primary statistic is sense-only and degeneracy-preserving: DMS data define
an assay-balanced amino-acid replacement loss matrix, while the null randomizes
the 61 sense codons over the fixed standard-code amino-acid class sizes.
"""
from __future__ import annotations

from collections import Counter, defaultdict
import csv
import json
import math
from pathlib import Path
import random
import re
import sys
import urllib.request
import zipfile

try:
    from tools.window_codon_bridge.experiments import run_code_edge_hiding_optimality as EDGE
except ModuleNotFoundError:
    sys.path.append(str(Path(__file__).resolve().parents[3]))
    from tools.window_codon_bridge.experiments import run_code_edge_hiding_optimality as EDGE


EXPERIMENT_ID = "dms_edge_hiding_robustness"
CLAIM_ID = "bridge.genetic_code.dms_edge_hiding_robustness"

CACHE_DIR = Path("/tmp/proteingym_cache")
DMS_ZIP = CACHE_DIR / "DMS_ProteinGym_substitutions.zip"
DMS_METADATA = CACHE_DIR / "DMS_substitutions.csv"
DMS_ZIP_URL = "https://marks.hms.harvard.edu/proteingym/ProteinGym_v1.3/DMS_ProteinGym_substitutions.zip"
METADATA_URL = "https://marks.hms.harvard.edu/proteingym/ProteinGym_v1.3/DMS_substitutions.csv"

NULL_SEED = 730620260703
BOOTSTRAP_SEED = 310620260703
PERMUTATION_SEED = 410620260703
NULL_DRAWS = 10000
BOOTSTRAP_DRAWS = 500
PERMUTATION_DRAWS = 5000

CERTIFIED_P = 1.0e-3
AMINO_ACIDS = tuple("ACDEFGHIKLMNPQRSTVWY")
AA_TO_INDEX = {aa: index for index, aa in enumerate(AMINO_ACIDS)}
AA3_TO_1 = {
    "Ala": "A",
    "Arg": "R",
    "Asn": "N",
    "Asp": "D",
    "Cys": "C",
    "Gln": "Q",
    "Glu": "E",
    "Gly": "G",
    "His": "H",
    "Ile": "I",
    "Leu": "L",
    "Lys": "K",
    "Met": "M",
    "Phe": "F",
    "Pro": "P",
    "Ser": "S",
    "Thr": "T",
    "Trp": "W",
    "Tyr": "Y",
    "Val": "V",
}
SINGLE_MUTANT_RE = re.compile(r"^([A-Z])([0-9]+)([A-Z])$")
TRANSITIONS = {("U", "C"), ("C", "U"), ("A", "G"), ("G", "A")}
HUMAN_CODON_USAGE_PATH = Path("tools/bio_reality/data/kazusa_codon_usage_homo_sapiens.json")


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    if status in {"certified", "coincidence"}:
        sys.exit(0)
    if status == "refuted":
        sys.exit(2)
    sys.exit(3)


def round_float(value: float | None, digits: int = 12) -> float | None:
    if value is None:
        return None
    if not math.isfinite(value):
        return value
    out = round(float(value), digits)
    return 0.0 if out == -0.0 else out


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def sample_sd(values: list[float]) -> float:
    if len(values) < 2:
        return 0.0
    m = mean(values)
    return math.sqrt(sum((value - m) * (value - m) for value in values) / (len(values) - 1))


def percentile(values: list[float], q: float) -> float:
    ordered = sorted(values)
    pos = (len(ordered) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return ordered[lo]
    return ordered[lo] * (hi - pos) + ordered[hi] * (pos - lo)


def summarize(values: list[float]) -> dict[str, float]:
    return {
        "mean": round_float(mean(values)),
        "sd": round_float(sample_sd(values)),
        "min": round_float(min(values)),
        "p01": round_float(percentile(values, 0.01)),
        "p05": round_float(percentile(values, 0.05)),
        "median": round_float(percentile(values, 0.50)),
        "p95": round_float(percentile(values, 0.95)),
        "p99": round_float(percentile(values, 0.99)),
        "max": round_float(max(values)),
    }


def ci(values: list[float], lo: float = 0.025, hi: float = 0.975) -> dict[str, float]:
    return {
        "low": round_float(percentile(values, lo)),
        "high": round_float(percentile(values, hi)),
        "draws": len(values),
    }


def empirical_le(values: list[float], observed: float) -> float:
    return sum(1 for value in values if value <= observed + 1.0e-15) / len(values)


def fetch_if_missing(path: Path, url: str) -> None:
    if path.exists() and path.stat().st_size > 0:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with urllib.request.urlopen(url, timeout=120) as response:
        data = response.read()
    path.write_bytes(data)


def load_metadata() -> dict[str, dict[str, str]]:
    fetch_if_missing(DMS_METADATA, METADATA_URL)
    with DMS_METADATA.open(newline="", encoding="utf-8") as handle:
        rows = {row["DMS_filename"]: row for row in csv.DictReader(handle)}
    if not rows:
        raise ValueError("ProteinGym metadata is empty")
    return rows


def parse_float(text: str) -> float | None:
    try:
        value = float(text)
    except (TypeError, ValueError):
        return None
    if not math.isfinite(value):
        return None
    return value


def average_ranks_01(scores: list[float]) -> list[float]:
    n = len(scores)
    if n == 1:
        return [0.5]
    order = sorted(range(n), key=lambda index: scores[index])
    ranks = [0.0] * n
    start = 0
    while start < n:
        end = start + 1
        while end < n and scores[order[end]] == scores[order[start]]:
            end += 1
        avg_rank = (start + end - 1) / 2.0
        scaled = avg_rank / (n - 1)
        for pos in range(start, end):
            ranks[order[pos]] = scaled
        start = end
    return ranks


def assay_pair_means(rows: list[tuple[str, str, float, float]]) -> tuple[dict[tuple[str, str], float], dict[tuple[str, str], float]]:
    bin_sums: dict[tuple[str, str], float] = defaultdict(float)
    bin_counts: Counter[tuple[str, str]] = Counter()
    rank_sums: dict[tuple[str, str], float] = defaultdict(float)
    rank_counts: Counter[tuple[str, str]] = Counter()

    scores = [row[3] for row in rows]
    ranks = average_ranks_01(scores) if scores else []
    for (src, dst, fit_bin, _score), rank in zip(rows, ranks):
        pair = (src, dst)
        bin_sums[pair] += fit_bin
        bin_counts[pair] += 1
        rank_sums[pair] += rank
        rank_counts[pair] += 1

    binary = {pair: bin_sums[pair] / bin_counts[pair] for pair in bin_counts}
    continuous = {pair: rank_sums[pair] / rank_counts[pair] for pair in rank_counts}
    return binary, continuous


def load_assay_balanced_fitness() -> tuple[
    dict[str, dict[tuple[str, str], float]],
    dict[str, dict[tuple[str, str], float]],
    dict[str, object],
]:
    fetch_if_missing(DMS_ZIP, DMS_ZIP_URL)
    metadata = load_metadata()

    binary_by_assay: dict[str, dict[tuple[str, str], float]] = {}
    continuous_by_assay: dict[str, dict[tuple[str, str], float]] = {}
    total_valid = 0
    total_rows = 0
    mismatch_rows = 0
    non_single_rows = 0
    malformed_rows = 0
    missing_meta_files: list[str] = []
    assay_summaries: list[dict[str, object]] = []

    with zipfile.ZipFile(DMS_ZIP) as archive:
        csv_names = sorted(name for name in archive.namelist() if name.endswith(".csv"))
        for zip_name in csv_names:
            filename = Path(zip_name).name
            meta = metadata.get(filename)
            if meta is None:
                missing_meta_files.append(filename)
                continue
            target = str(meta.get("target_seq", "")).strip().upper()
            rows: list[tuple[str, str, float, float]] = []
            assay_total = 0
            assay_non_single = 0
            assay_mismatch = 0
            assay_malformed = 0
            with archive.open(zip_name) as raw_handle:
                text_rows = (line.decode("utf-8", errors="replace") for line in raw_handle)
                reader = csv.DictReader(text_rows)
                for row in reader:
                    assay_total += 1
                    total_rows += 1
                    match = SINGLE_MUTANT_RE.match(str(row.get("mutant", "")).strip())
                    if match is None:
                        assay_non_single += 1
                        non_single_rows += 1
                        continue
                    src, pos_text, dst = match.groups()
                    if src not in AA_TO_INDEX or dst not in AA_TO_INDEX or src == dst:
                        assay_malformed += 1
                        malformed_rows += 1
                        continue
                    pos = int(pos_text)
                    if pos < 1 or pos > len(target) or target[pos - 1] != src:
                        assay_mismatch += 1
                        mismatch_rows += 1
                        continue
                    fit_bin = parse_float(str(row.get("DMS_score_bin", "")))
                    score = parse_float(str(row.get("DMS_score", "")))
                    if fit_bin is None or score is None:
                        assay_malformed += 1
                        malformed_rows += 1
                        continue
                    rows.append((src, dst, fit_bin, score))
            if rows:
                binary, continuous = assay_pair_means(rows)
                binary_by_assay[filename] = binary
                continuous_by_assay[filename] = continuous
                total_valid += len(rows)
                assay_summaries.append(
                    {
                        "filename": filename,
                        "valid_single_mutants": len(rows),
                        "raw_rows": assay_total,
                        "includes_multiple_mutants": str(meta.get("includes_multiple_mutants", "")),
                        "taxon": str(meta.get("taxon", "")),
                        "pair_count": len(binary),
                    }
                )

    diagnostics = {
        "metadata_rows": len(metadata),
        "zip_csv_files": len(binary_by_assay) + len(missing_meta_files),
        "missing_metadata_files": missing_meta_files[:10],
        "raw_rows_read": total_rows,
        "non_single_rows_excluded": non_single_rows,
        "target_mismatch_rows_excluded": mismatch_rows,
        "malformed_rows_excluded": malformed_rows,
        "n_single_mutants_used": total_valid,
        "n_assays_used": len(binary_by_assay),
        "assays_with_multiple_mutants_flag": sum(
            1 for row in assay_summaries if row["includes_multiple_mutants"] == "TRUE"
        ),
        "assay_valid_single_mutants_summary": summarize([float(row["valid_single_mutants"]) for row in assay_summaries])
        if assay_summaries
        else {},
    }
    return binary_by_assay, continuous_by_assay, diagnostics


def matrix_from_assays(
    assay_means: dict[str, dict[tuple[str, str], float]],
    selected_assays: list[str] | None = None,
    fill_value: float | None = None,
) -> tuple[list[list[float]], dict[str, object]]:
    assays = selected_assays if selected_assays is not None else sorted(assay_means)
    pair_sums: dict[tuple[str, str], float] = defaultdict(float)
    pair_counts: Counter[tuple[str, str]] = Counter()
    for assay in assays:
        for pair, value in assay_means[assay].items():
            pair_sums[pair] += value
            pair_counts[pair] += 1

    directed_losses: dict[tuple[str, str], float] = {}
    available_losses: list[float] = []
    pair_assay_counts: dict[str, int] = {}
    for src in AMINO_ACIDS:
        for dst in AMINO_ACIDS:
            if src == dst:
                continue
            pair = (src, dst)
            if pair in pair_counts:
                fitness = pair_sums[pair] / pair_counts[pair]
                loss = 1.0 - fitness
                directed_losses[pair] = loss
                available_losses.append(loss)
                pair_assay_counts[f"{src}>{dst}"] = pair_counts[pair]

    if not available_losses:
        raise ValueError("no amino-acid replacement pairs were recovered")
    primary_fill = mean(available_losses) if fill_value is None else fill_value
    matrix = [[0.0 for _ in AMINO_ACIDS] for _ in AMINO_ACIDS]
    missing_directed: list[str] = []
    missing_symmetric: list[str] = []
    for src in AMINO_ACIDS:
        for dst in AMINO_ACIDS:
            if src == dst:
                continue
            forward = directed_losses.get((src, dst))
            reverse = directed_losses.get((dst, src))
            if forward is None:
                missing_directed.append(f"{src}>{dst}")
                forward = primary_fill
            if reverse is None:
                reverse = primary_fill
            if (src < dst) and ((src, dst) not in directed_losses or (dst, src) not in directed_losses):
                missing_symmetric.append(f"{src}<>{dst}")
            loss = (forward + reverse) / 2.0
            matrix[AA_TO_INDEX[src]][AA_TO_INDEX[dst]] = loss

    row_marginals: dict[str, float] = {}
    column_marginals: dict[str, float] = {}
    for src in AMINO_ACIDS:
        values = [directed_losses[(src, dst)] for dst in AMINO_ACIDS if dst != src and (src, dst) in directed_losses]
        row_marginals[src] = mean(values) if values else primary_fill
    for dst in AMINO_ACIDS:
        values = [directed_losses[(src, dst)] for src in AMINO_ACIDS if src != dst and (src, dst) in directed_losses]
        column_marginals[dst] = mean(values) if values else primary_fill

    diagnostics = {
        "coverage_directed_pairs": len(directed_losses),
        "coverage_total_directed_pairs": 20 * 19,
        "coverage_fraction": len(directed_losses) / (20 * 19),
        "missing_directed_pairs": missing_directed,
        "missing_symmetric_pairs": missing_symmetric,
        "missing_pair_policy": "directed losses are assay-balanced; undirected codon edges use the A->B/B->A average; missing directions are filled by the global available directed-loss mean",
        "global_directed_loss_mean": primary_fill,
        "global_directed_loss_sd": sample_sd(available_losses),
        "row_source_loss_marginals": row_marginals,
        "column_target_loss_marginals": column_marginals,
        "pair_assay_count_summary": summarize([float(value) for value in pair_assay_counts.values()]),
        "pair_assay_counts": pair_assay_counts,
    }
    return matrix, diagnostics


def sense_codons_and_edges() -> tuple[list[str], list[tuple[int, int]], list[int], list[int]]:
    codons64 = EDGE.codon_order()
    edges64 = EDGE.hamming1_edges(codons64)
    sense_codons = [codon for codon in codons64 if EDGE.CODON_TO_OUTPUT[codon] != "Stop"]
    sense_index = {codon: index for index, codon in enumerate(sense_codons)}
    sense_edges: list[tuple[int, int]] = []
    for left64, right64 in edges64:
        left = codons64[left64]
        right = codons64[right64]
        if left in sense_index and right in sense_index:
            sense_edges.append((sense_index[left], sense_index[right]))
    std_labels = [AA_TO_INDEX[AA3_TO_1[EDGE.CODON_TO_OUTPUT[codon]]] for codon in sense_codons]
    full_std_labels = EDGE.standard_labels(codons64)
    return sense_codons, sense_edges, std_labels, full_std_labels


def edge_weight_titv(left: str, right: str) -> float:
    diffs = [(a, b) for a, b in zip(left, right) if a != b]
    if len(diffs) != 1:
        raise ValueError("edge is not Hamming-1")
    return 2.0 if diffs[0] in TRANSITIONS else 1.0


def load_human_codon_usage_weights(sense_codons: list[str], sense_edges: list[tuple[int, int]]) -> tuple[list[float] | None, dict[str, object]]:
    if not HUMAN_CODON_USAGE_PATH.exists():
        return None, {
            "available": False,
            "source": str(HUMAN_CODON_USAGE_PATH),
            "reason": "local codon-usage file not present",
        }
    data = json.loads(HUMAN_CODON_USAGE_PATH.read_text(encoding="utf-8"))
    counts_raw = data.get("codon_counts", {})
    if not isinstance(counts_raw, dict):
        return None, {
            "available": False,
            "source": str(HUMAN_CODON_USAGE_PATH),
            "reason": "codon_counts is not a dict",
        }
    counts: dict[str, float] = {}
    for codon in sense_codons:
        value = counts_raw.get(codon)
        try:
            count = float(value)
        except (TypeError, ValueError):
            return None, {
                "available": False,
                "source": str(HUMAN_CODON_USAGE_PATH),
                "reason": f"missing or invalid count for {codon}",
            }
        if count < 0.0:
            return None, {
                "available": False,
                "source": str(HUMAN_CODON_USAGE_PATH),
                "reason": f"negative count for {codon}",
            }
        counts[codon] = count
    total = sum(counts.values())
    if total <= 0.0:
        return None, {
            "available": False,
            "source": str(HUMAN_CODON_USAGE_PATH),
            "reason": "sense codon counts sum to zero",
        }
    probabilities = {codon: counts[codon] / total for codon in sense_codons}
    weights = [
        (probabilities[sense_codons[left]] + probabilities[sense_codons[right]]) / 2.0
        for left, right in sense_edges
    ]
    return weights, {
        "available": True,
        "source": str(HUMAN_CODON_USAGE_PATH),
        "organism": data.get("organism") or data.get("accession_or_id") or "homo_sapiens",
        "weight_rule": "undirected edge weight is the mean of the two endpoint sense-codon usage probabilities",
        "min_edge_weight": min(weights),
        "max_edge_weight": max(weights),
    }


def code_scores(
    labels: list[int],
    edges: list[tuple[int, int]],
    primary_matrix: list[list[float]],
    continuous_matrix: list[list[float]],
    titv_weights: list[float],
    usage_weights: list[float] | None,
) -> dict[str, float]:
    e_in = 0
    primary_sum = 0.0
    continuous_sum = 0.0
    skip_sum = 0.0
    skip_count = 0
    titv_num = 0.0
    titv_den = 0.0
    usage_num = 0.0
    usage_den = 0.0
    for edge_index, (left, right) in enumerate(edges):
        aa_left = labels[left]
        aa_right = labels[right]
        if aa_left == aa_right:
            e_in += 1
            loss = 0.0
            loss_cont = 0.0
        else:
            loss = primary_matrix[aa_left][aa_right]
            loss_cont = continuous_matrix[aa_left][aa_right]
            skip_sum += loss
            skip_count += 1
        primary_sum += loss
        continuous_sum += loss_cont
        titv_w = titv_weights[edge_index]
        titv_num += titv_w * loss
        titv_den += titv_w
        if usage_weights is not None:
            usage_w = usage_weights[edge_index]
            usage_num += usage_w * loss
            usage_den += usage_w
    out = {
        "e_in": float(e_in),
        "R": primary_sum / len(edges),
        "R_continuous": continuous_sum / len(edges),
        "R_missing_skip": skip_sum / skip_count if skip_count else 0.0,
        "R_titv": titv_num / titv_den,
    }
    if usage_weights is not None:
        out["R_usage"] = usage_num / usage_den
    return out


def shuffled_sense_labels(profile: Counter[int], rng: random.Random) -> list[int]:
    labels: list[int] = []
    for index in range(len(AMINO_ACIDS)):
        labels.extend([index] * profile[index])
    rng.shuffle(labels)
    return labels


def covariance(left: list[float], right: list[float]) -> float:
    left_mean = mean(left)
    right_mean = mean(right)
    return sum((a - left_mean) * (b - right_mean) for a, b in zip(left, right)) / len(left)


def fit_beta(e_values: list[float], r_values: list[float]) -> dict[str, float]:
    e_mean = mean(e_values)
    r_mean = mean(r_values)
    var_e = sum((value - e_mean) * (value - e_mean) for value in e_values)
    if var_e <= 0.0:
        return {"alpha": r_mean, "slope": 0.0, "beta": 0.0, "r": 0.0}
    slope = sum((e - e_mean) * (r - r_mean) for e, r in zip(e_values, r_values)) / var_e
    alpha = r_mean - slope * e_mean
    sd_e = sample_sd(e_values)
    sd_r = sample_sd(r_values)
    corr = 0.0 if sd_e == 0.0 or sd_r == 0.0 else covariance(e_values, r_values) / (sd_e * sd_r)
    return {"alpha": alpha, "slope": slope, "beta": -slope, "r": corr}


def permutation_p(e_values: list[float], r_values: list[float], observed_beta: float, draws: int, seed: int) -> float:
    rng = random.Random(seed)
    shuffled = r_values[:]
    ge = 0
    for _ in range(draws):
        rng.shuffle(shuffled)
        beta = fit_beta(e_values, shuffled)["beta"]
        if beta >= observed_beta - 1.0e-15:
            ge += 1
    return (ge + 1) / (draws + 1)


def residual_lower_tail(e_values: list[float], r_values: list[float], e_std: float, r_std: float) -> dict[str, float]:
    fit = fit_beta(e_values, r_values)
    alpha = fit["alpha"]
    slope = fit["slope"]
    residuals = [r - (alpha + slope * e) for e, r in zip(e_values, r_values)]
    std_residual = r_std - (alpha + slope * e_std)
    return {
        "residual_std": std_residual,
        "residual_lower_p": empirical_le(residuals, std_residual),
        "predicted_std": alpha + slope * e_std,
    }


def null_distribution(
    profile: Counter[int],
    edges: list[tuple[int, int]],
    primary_matrix: list[list[float]],
    continuous_matrix: list[list[float]],
    titv_weights: list[float],
    usage_weights: list[float] | None,
) -> dict[str, list[float]]:
    rng = random.Random(NULL_SEED)
    e_values: list[float] = []
    r_values: list[float] = []
    r_cont_values: list[float] = []
    r_skip_values: list[float] = []
    r_titv_values: list[float] = []
    r_usage_values: list[float] = []
    for _ in range(NULL_DRAWS):
        labels = shuffled_sense_labels(profile, rng)
        scores = code_scores(labels, edges, primary_matrix, continuous_matrix, titv_weights, usage_weights)
        e_values.append(scores["e_in"])
        r_values.append(scores["R"])
        r_cont_values.append(scores["R_continuous"])
        r_skip_values.append(scores["R_missing_skip"])
        r_titv_values.append(scores["R_titv"])
        if usage_weights is not None and "R_usage" in scores:
            r_usage_values.append(scores["R_usage"])
    out = {
        "e_in": e_values,
        "R": r_values,
        "R_continuous": r_cont_values,
        "R_missing_skip": r_skip_values,
        "R_titv": r_titv_values,
    }
    if usage_weights is not None:
        out["R_usage"] = r_usage_values
    return out


def analyze_variant(
    name: str,
    e_values: list[float],
    r_values: list[float],
    e_std: float,
    r_std: float,
    permutation_seed_offset: int,
) -> dict[str, object]:
    fit = fit_beta(e_values, r_values)
    perm_p = permutation_p(
        e_values,
        r_values,
        fit["beta"],
        PERMUTATION_DRAWS,
        PERMUTATION_SEED + permutation_seed_offset,
    )
    residual = residual_lower_tail(e_values, r_values, e_std, r_std)
    return {
        "name": name,
        "R_DMS_std": round_float(r_std),
        "p_null": empirical_le(r_values, r_std),
        "beta": round_float(fit["beta"]),
        "beta_perm_p": perm_p,
        "alpha": round_float(fit["alpha"]),
        "slope_R_on_e_in": round_float(fit["slope"]),
        "correlation_R_e_in": round_float(fit["r"]),
        "null_R_summary": summarize(r_values),
        "residual_std": round_float(residual["residual_std"]),
        "residual_lower_p_after_e_in": residual["residual_lower_p"],
        "predicted_R_at_e_in_std": round_float(residual["predicted_std"]),
    }


def bootstrap_r_std(
    assay_means: dict[str, dict[tuple[str, str], float]],
    fill_value: float,
    std_labels: list[int],
    edges: list[tuple[int, int]],
    primary_matrix: list[list[float]],
    continuous_matrix: list[list[float]],
    titv_weights: list[float],
    usage_weights: list[float] | None,
) -> dict[str, object]:
    assays = sorted(assay_means)
    rng = random.Random(BOOTSTRAP_SEED)
    values: list[float] = []
    for _ in range(BOOTSTRAP_DRAWS):
        selected = [rng.choice(assays) for _ in assays]
        matrix, _diag = matrix_from_assays(assay_means, selected_assays=selected, fill_value=fill_value)
        scores = code_scores(std_labels, edges, matrix, continuous_matrix, titv_weights, usage_weights)
        values.append(scores["R"])
    return {"R_DMS_std_clustered_by_assay": ci(values), "summary": summarize(values)}


def verdict(primary: dict[str, object]) -> tuple[str, str]:
    p_null = float(primary["p_null"])
    beta = float(primary["beta"])
    beta_perm_p = float(primary["beta_perm_p"])
    if p_null <= CERTIFIED_P and beta > 0.0 and beta_perm_p <= CERTIFIED_P:
        return (
            "certified",
            "standard code is an extreme low-DMS-loss code under the exact degeneracy null, and e_in significantly mediates lower loss; conditional residual diagnostics are reported but not used as a rescue statistic",
        )
    if p_null <= CERTIFIED_P:
        return (
            "coincidence",
            "standard code is an extreme low-DMS-loss code, but the degeneracy-null slope does not show preregistered e_in mediation",
        )
    if beta <= 0.0:
        return (
            "refuted",
            "the e_in slope is nonpositive for the DMS loss functional, so edge hiding does not mediate lower measured loss",
        )
    if beta_perm_p <= CERTIFIED_P:
        return (
            "refuted",
            "e_in predicts lower DMS loss across null codes, but the standard code is not an extreme low-loss code under the exact degeneracy null",
        )
    return (
        "refuted",
        "neither preregistered extremality nor preregistered e_in mediation reaches the decision threshold",
    )


def main() -> None:
    try:
        binary_assays, continuous_assays, data_diag = load_assay_balanced_fitness()
        if not binary_assays:
            raise ValueError("no usable assays after single-mutant filtering")
        primary_matrix, primary_diag = matrix_from_assays(binary_assays)
        continuous_matrix, continuous_diag = matrix_from_assays(continuous_assays)

        sense_codons, sense_edges, std_labels, full_std_labels = sense_codons_and_edges()
        titv_weights = [edge_weight_titv(sense_codons[left], sense_codons[right]) for left, right in sense_edges]
        usage_weights, usage_diag = load_human_codon_usage_weights(sense_codons, sense_edges)
        profile = Counter(std_labels)
        spectrum = Counter(profile.values())

        std_scores = code_scores(
            std_labels,
            sense_edges,
            primary_matrix,
            continuous_matrix,
            titv_weights,
            usage_weights,
        )
        null = null_distribution(
            profile,
            sense_edges,
            primary_matrix,
            continuous_matrix,
            titv_weights,
            usage_weights,
        )

        e_std = std_scores["e_in"]
        primary = analyze_variant("binary_DMS_score_bin", null["e_in"], null["R"], e_std, std_scores["R"], 0)
        continuous = analyze_variant(
            "assay_rank_normalized_continuous_DMS_score",
            null["e_in"],
            null["R_continuous"],
            e_std,
            std_scores["R_continuous"],
            10000,
        )
        missing_skip = analyze_variant(
            "binary_missing_pairs_skipped_from_nonsynonymous_sum",
            null["e_in"],
            null["R_missing_skip"],
            e_std,
            std_scores["R_missing_skip"],
            20000,
        )
        titv = analyze_variant(
            "binary_transition_weight_2_transversion_weight_1",
            null["e_in"],
            null["R_titv"],
            e_std,
            std_scores["R_titv"],
            30000,
        )
        usage = None
        if usage_weights is not None and "R_usage" in null and "R_usage" in std_scores:
            usage = analyze_variant(
                "binary_human_codon_usage_edge_weighted",
                null["e_in"],
                null["R_usage"],
                e_std,
                std_scores["R_usage"],
                40000,
            )

        bootstrap = bootstrap_r_std(
            binary_assays,
            float(primary_diag["global_directed_loss_mean"]),
            std_labels,
            sense_edges,
            primary_matrix,
            continuous_matrix,
            titv_weights,
            usage_weights,
        )

        codons64 = EDGE.codon_order()
        edges64 = EDGE.hamming1_edges(codons64)
        e_in_std_sense, e_in_std_all = EDGE.edge_counts(full_std_labels, edges64)
        checks = [
            {"name": "sense_codon_count", "ok": len(sense_codons) == 61, "observed": len(sense_codons)},
            {"name": "sense_edge_count", "ok": len(sense_edges) == 263, "observed": len(sense_edges)},
            {"name": "standard_e_in_sense", "ok": int(e_std) == 67 == e_in_std_sense, "observed": int(e_std)},
            {"name": "fixed_stop_block_e_in", "ok": e_in_std_all == 69, "observed": e_in_std_all},
            {
                "name": "sense_degeneracy_spectrum",
                "ok": dict(sorted(spectrum.items())) == {1: 2, 2: 9, 3: 1, 4: 5, 6: 3},
                "observed": dict(sorted(spectrum.items())),
            },
            {
                "name": "null_draws",
                "ok": len(null["R"]) == NULL_DRAWS,
                "observed": len(null["R"]),
            },
            {
                "name": "primary_L_AB_has_at_least_one_pair",
                "ok": int(primary_diag["coverage_directed_pairs"]) > 0,
                "observed": int(primary_diag["coverage_directed_pairs"]),
            },
            {
                "name": "continuous_L_AB_has_at_least_one_pair",
                "ok": int(continuous_diag["coverage_directed_pairs"]) > 0,
                "observed": int(continuous_diag["coverage_directed_pairs"]),
            },
        ]
        if not all(bool(row["ok"]) for row in checks):
            emit(
                "needs_derivation",
                R_DMS_std=round_float(std_scores["R"]),
                e_in_std=int(e_std),
                p_null=primary["p_null"],
                N_null=NULL_DRAWS,
                beta=primary["beta"],
                beta_perm_p=primary["beta_perm_p"],
                L_AB_coverage=primary_diag["coverage_directed_pairs"],
                n_assays_used=data_diag["n_assays_used"],
                n_single_mutants_used=data_diag["n_single_mutants_used"],
                sensitivity_continuous_DMS=continuous,
                checks=checks,
                reason="internal finite-code or data-coverage check failed",
            )

        status, reason = verdict(primary)
        emit(
            status,
            R_DMS_std=primary["R_DMS_std"],
            e_in_std=int(e_std),
            p_null=primary["p_null"],
            N_null=NULL_DRAWS,
            beta=primary["beta"],
            beta_perm_p=primary["beta_perm_p"],
            L_AB_coverage={
                "directed_pairs": primary_diag["coverage_directed_pairs"],
                "total_directed_pairs": primary_diag["coverage_total_directed_pairs"],
                "fraction": round_float(float(primary_diag["coverage_fraction"])),
                "missing_directed_pairs": primary_diag["missing_directed_pairs"],
                "missing_symmetric_pairs": primary_diag["missing_symmetric_pairs"],
                "missing_pair_policy": primary_diag["missing_pair_policy"],
            },
            n_assays_used=data_diag["n_assays_used"],
            n_single_mutants_used=data_diag["n_single_mutants_used"],
            sensitivity_continuous_DMS=continuous,
            reason=reason,
            thresholds={"p_null": CERTIFIED_P, "beta_perm_p": CERTIFIED_P, "N_null_minimum": 10000},
            data_diagnostics=data_diag,
            L_AB_diagnostics={
                "binary": {
                    "global_directed_loss_mean": round_float(float(primary_diag["global_directed_loss_mean"])),
                    "global_directed_loss_sd": round_float(float(primary_diag["global_directed_loss_sd"])),
                    "row_source_loss_marginals": {
                        aa: round_float(value) for aa, value in primary_diag["row_source_loss_marginals"].items()
                    },
                    "column_target_loss_marginals": {
                        aa: round_float(value) for aa, value in primary_diag["column_target_loss_marginals"].items()
                    },
                    "pair_assay_count_summary": primary_diag["pair_assay_count_summary"],
                },
                "continuous_rank_normalized": {
                    "coverage_directed_pairs": continuous_diag["coverage_directed_pairs"],
                    "global_directed_loss_mean": round_float(float(continuous_diag["global_directed_loss_mean"])),
                    "global_directed_loss_sd": round_float(float(continuous_diag["global_directed_loss_sd"])),
                },
            },
            primary_result=primary,
            null_e_in_summary=summarize(null["e_in"]),
            bootstrap_clustered_by_assay=bootstrap,
            sensitivity_missing_pair_skip=missing_skip,
            sensitivity_transition_transversion=titv,
            sensitivity_codon_usage=usage
            if usage is not None
            else {"name": "binary_human_codon_usage_edge_weighted", "available": False, "diagnostics": usage_diag},
            codon_usage_weight_diagnostics=usage_diag,
            fixed_stop_block_sensitivity={
                "e_in_std_all_codons_with_fixed_three_stop_block": e_in_std_all,
                "note": "with the standard stop codons fixed, the stop-stop block adds two synonymous Hamming-1 edges to every code; primary sense-only beta and p-values are unchanged by this constant shift",
            },
            null_model={
                "kind": "uniform random assignments of 61 sense codons to fixed standard-code amino-acid degeneracy classes",
                "seed": NULL_SEED,
                "degeneracy_profile": {AMINO_ACIDS[index]: profile[index] for index in range(len(AMINO_ACIDS))},
                "degeneracy_spectrum": {str(size): count for size, count in sorted(spectrum.items())},
                "stop_handling_primary": "stop codons excluded from E_61 and R_DMS",
            },
            checks=checks,
        )
    except Exception as exc:
        emit(
            "needs_derivation",
            R_DMS_std=None,
            e_in_std=None,
            p_null=None,
            N_null=NULL_DRAWS,
            beta=None,
            beta_perm_p=None,
            L_AB_coverage=None,
            n_assays_used=0,
            n_single_mutants_used=0,
            sensitivity_continuous_DMS=None,
            reason=f"data fetch/parse/analysis failed: {type(exc).__name__}: {exc}",
        )


if __name__ == "__main__":
    main()

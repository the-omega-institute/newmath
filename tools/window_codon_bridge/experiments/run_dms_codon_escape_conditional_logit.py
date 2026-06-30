#!/usr/bin/env python3
"""DMS codon-escape allocation test with absorbed conditional-choice logits."""
from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import json
import math
from pathlib import Path
import random
import sys
from typing import Iterable


EXPERIMENT_ID = "dms_codon_escape_conditional_logit"
CLAIM_ID = "bridge.genetic_code.dms_codon_escape_conditional_allocation"

N_BOOTSTRAP = 2000
BOOTSTRAP_SEED = "dms_codon_escape_conditional_logit.cluster_score_bootstrap"
PANEL_PATH = Path(__file__).resolve().parents[1] / "synced" / "dms_codon_escape_panel.json"

PARAM_NAMES = ("h", "comp", "rscu", "gc3")
MAX_NEWTON = 80
BETA_TOL = 1.0e-9
GRAD_TOL = 1.0e-7
ALPHA_TOL = 1.0e-10
ALPHA_MAX_ITER = 10000

GENETIC_CODE = {
    "UUU": "F",
    "UUC": "F",
    "UUA": "L",
    "UUG": "L",
    "UCU": "S",
    "UCC": "S",
    "UCA": "S",
    "UCG": "S",
    "UAU": "Y",
    "UAC": "Y",
    "UAA": "*",
    "UAG": "*",
    "UGU": "C",
    "UGC": "C",
    "UGA": "*",
    "UGG": "W",
    "CUU": "L",
    "CUC": "L",
    "CUA": "L",
    "CUG": "L",
    "CCU": "P",
    "CCC": "P",
    "CCA": "P",
    "CCG": "P",
    "CAU": "H",
    "CAC": "H",
    "CAA": "Q",
    "CAG": "Q",
    "CGU": "R",
    "CGC": "R",
    "CGA": "R",
    "CGG": "R",
    "AUU": "I",
    "AUC": "I",
    "AUA": "I",
    "AUG": "M",
    "ACU": "T",
    "ACC": "T",
    "ACA": "T",
    "ACG": "T",
    "AAU": "N",
    "AAC": "N",
    "AAA": "K",
    "AAG": "K",
    "AGU": "S",
    "AGC": "S",
    "AGA": "R",
    "AGG": "R",
    "GUU": "V",
    "GUC": "V",
    "GUA": "V",
    "GUG": "V",
    "GCU": "A",
    "GCC": "A",
    "GCA": "A",
    "GCG": "A",
    "GAU": "D",
    "GAC": "D",
    "GAA": "E",
    "GAG": "E",
    "GGU": "G",
    "GGC": "G",
    "GGA": "G",
    "GGG": "G",
}


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status in {"certified", "coincidence", "needs_derivation"} else 2)


def stable_seed(text: str) -> int:
    return int.from_bytes(hashlib.sha256(text.encode("utf-8")).digest()[:16], "big")


def round_float(value: float | None, digits: int = 12) -> float | None:
    if value is None:
        return None
    if not math.isfinite(value):
        return value
    rounded = round(value, digits)
    return 0.0 if rounded == -0.0 else rounded


def mean(values: Iterable[float]) -> float:
    vals = list(values)
    return sum(vals) / len(vals)


def percentile(values: list[float], q: float) -> float:
    ordered = sorted(values)
    pos = (len(ordered) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return ordered[lo]
    return ordered[lo] * (hi - pos) + ordered[hi] * (pos - lo)


def normal_sf(z: float) -> float:
    return 0.5 * math.erfc(z / math.sqrt(2.0))


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def hamming(left: str, right: str) -> int:
    return sum(a != b for a, b in zip(left, right))


def synonymous_codons() -> dict[str, list[str]]:
    by_aa: dict[str, list[str]] = defaultdict(list)
    for codon, aa in sorted(GENETIC_CODE.items()):
        if aa != "*":
            by_aa[aa].append(codon)
    return {aa: codons for aa, codons in by_aa.items() if len(codons) > 1}


SYNONYMOUS = synonymous_codons()


def codon_features(codon: str, aa: str, rscu: float) -> list[float]:
    h = sum(1 for other in SYNONYMOUS[aa] if other != codon and hamming(codon, other) == 1)
    comp = sum(base in {"G", "C"} for base in codon) / 3.0
    gc3 = 1.0 if codon[2] in {"G", "C"} else 0.0
    return [float(h), comp, float(rscu), gc3]


def load_panel() -> tuple[dict[str, object], list[dict[str, object]]]:
    with PANEL_PATH.open(encoding="utf-8") as handle:
        panel = json.load(handle)
    sites = panel.get("sites")
    provenance = panel.get("provenance")
    if not isinstance(provenance, dict) or not isinstance(sites, list):
        raise ValueError("panel must be a dict containing provenance and sites")
    return provenance, sites


def native_optimality(site: dict[str, object]) -> float:
    if "optimality_o" in site:
        return float(site["optimality_o"])
    if "o" in site:
        return float(site["o"])
    raise ValueError("site is missing optimality_o/o")


def compute_rscu_proxy(sites: list[dict[str, object]]) -> dict[tuple[str, str, str], float]:
    counts: Counter[tuple[str, str, str]] = Counter()
    totals: Counter[tuple[str, str]] = Counter()
    for site in sites:
        organism = str(site["organism"])
        aa = str(site["amino_acid"])
        codon = str(site["native_codon_rna"])
        if aa not in {"L", "R", "S"}:
            raise ValueError(f"unexpected amino acid in DMS panel: {aa}")
        counts[(organism, aa, codon)] += 1
        totals[(organism, aa)] += 1

    rscu: dict[tuple[str, str, str], float] = {}
    for organism, aa in totals:
        expected = totals[(organism, aa)] / float(len(SYNONYMOUS[aa]))
        for codon in SYNONYMOUS[aa]:
            rscu[(organism, aa, codon)] = counts[(organism, aa, codon)] / expected
    return rscu


def validate_panel(sites: list[dict[str, object]], rscu: dict[tuple[str, str, str], float]) -> None:
    for site in sites:
        aa = str(site["amino_acid"])
        codon = str(site["native_codon_rna"])
        organism = str(site["organism"])
        if aa not in {"L", "R", "S"}:
            raise ValueError(f"panel contains unsupported amino acid {aa}")
        if codon not in SYNONYMOUS[aa]:
            raise ValueError(f"native codon {codon} is not synonymous for {aa}")
        panel_h = float(site["h"])
        derived_h = codon_features(codon, aa, rscu[(organism, aa, codon)])[0]
        if abs(panel_h - derived_h) > 1.0e-9:
            raise ValueError(f"panel h mismatch for {aa}/{codon}: {panel_h} != {derived_h}")
        native_rscu = native_optimality(site)
        proxy_rscu = rscu[(organism, aa, codon)]
        if native_rscu < 0.0 or proxy_rscu < 0.0:
            raise ValueError("RSCU values must be nonnegative")


def build_strata(sites: list[dict[str, object]], rscu: dict[tuple[str, str, str], float]) -> list[dict[str, object]]:
    grouped: dict[tuple[str, str], list[dict[str, object]]] = defaultdict(list)
    for site in sites:
        grouped[(str(site["organism"]), str(site["amino_acid"]))].append(site)

    strata: list[dict[str, object]] = []
    for (organism, aa), rows in sorted(grouped.items()):
        counts = Counter(str(row["native_codon_rna"]) for row in rows)
        active_codons = [codon for codon in SYNONYMOUS[aa] if counts[codon] > 0]
        codon_to_idx = {codon: idx for idx, codon in enumerate(active_codons)}
        features = [codon_features(codon, aa, rscu[(organism, aa, codon)]) for codon in active_codons]
        strata.append(
            {
                "organism": organism,
                "aa": aa,
                "rows": rows,
                "codons": active_codons,
                "counts": [float(counts[codon]) for codon in active_codons],
                "chosen": [codon_to_idx[str(row["native_codon_rna"])] for row in rows],
                "I": [float(row["I"]) for row in rows],
                "features": features,
                "proteins": [str(row["uniprot"]) for row in rows],
            }
        )
    return strata


def logsumexp(values: list[float]) -> float:
    m = max(values)
    return m + math.log(sum(math.exp(value - m) for value in values))


def probabilities_for_stratum(stratum: dict[str, object], beta: list[float], alpha: list[float]) -> list[list[float]]:
    features = stratum["features"]  # type: ignore[assignment]
    I_values = stratum["I"]  # type: ignore[assignment]
    probs: list[list[float]] = []
    eta = [dot(beta, feat) for feat in features]  # type: ignore[arg-type]
    for site_I in I_values:  # type: ignore[union-attr]
        logits = [alpha[j] + float(site_I) * eta[j] for j in range(len(alpha))]
        denom = logsumexp(logits)
        probs.append([math.exp(value - denom) for value in logits])
    return probs


def calibrate_alpha(stratum: dict[str, object], beta: list[float]) -> tuple[list[float], bool]:
    counts = stratum["counts"]  # type: ignore[assignment]
    k = len(counts)  # type: ignore[arg-type]
    if k == 1:
        return [0.0], True
    alpha = [0.0 for _ in range(k)]
    converged = False
    for _ in range(ALPHA_MAX_ITER):
        probs = probabilities_for_stratum(stratum, beta, alpha)
        predicted = [sum(row[j] for row in probs) for j in range(k)]
        max_step = 0.0
        for j in range(k):
            step = math.log(float(counts[j]) / predicted[j])  # type: ignore[index]
            alpha[j] += step
            max_step = max(max_step, abs(step))
        center = mean(alpha)
        alpha = [value - center for value in alpha]
        if max_step < ALPHA_TOL:
            converged = True
            break
    return alpha, converged


def solve_linear(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    aug = [row[:] + [rhs[i]] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) < 1.0e-14:
            raise ValueError("singular linear system")
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        scale = aug[col][col]
        for j in range(col, n + 1):
            aug[col][j] /= scale
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor == 0.0:
                continue
            for j in range(col, n + 1):
                aug[row][j] -= factor * aug[col][j]
    return [aug[i][n] for i in range(n)]


def inverse_matrix(matrix: list[list[float]]) -> list[list[float]]:
    n = len(matrix)
    columns = []
    for idx in range(n):
        rhs = [0.0 for _ in range(n)]
        rhs[idx] = 1.0
        columns.append(solve_linear(matrix, rhs))
    return [[columns[col][row] for col in range(n)] for row in range(n)]


def fit_at_beta(strata: list[dict[str, object]], beta: list[float]) -> dict[str, object]:
    p = len(beta)
    loglik = 0.0
    gradient = [0.0 for _ in range(p)]
    info = [[0.0 for _ in range(p)] for _ in range(p)]
    protein_scores: defaultdict[str, list[float]] = defaultdict(lambda: [0.0 for _ in range(p)])
    all_alpha_converged = True

    for stratum in strata:
        alpha, alpha_converged = calibrate_alpha(stratum, beta)
        all_alpha_converged = all_alpha_converged and alpha_converged
        probs = probabilities_for_stratum(stratum, beta, alpha)
        features = stratum["features"]  # type: ignore[assignment]
        chosen = stratum["chosen"]  # type: ignore[assignment]
        I_values = stratum["I"]  # type: ignore[assignment]
        proteins = stratum["proteins"]  # type: ignore[assignment]
        k = len(alpha)
        q = max(0, k - 1)
        I_bb = [[0.0 for _ in range(p)] for _ in range(p)]
        I_ba = [[0.0 for _ in range(q)] for _ in range(p)]
        I_aa = [[0.0 for _ in range(q)] for _ in range(q)]

        eta = [dot(beta, feat) for feat in features]  # type: ignore[arg-type]
        stratum_beta_scores: defaultdict[str, list[float]] = defaultdict(lambda: [0.0 for _ in range(p)])
        stratum_alpha_scores: defaultdict[str, list[float]] = defaultdict(lambda: [0.0 for _ in range(q)])

        for row_idx, site_I_raw in enumerate(I_values):  # type: ignore[union-attr]
            site_I = float(site_I_raw)
            selected = int(chosen[row_idx])  # type: ignore[index]
            pr = probs[row_idx]
            expected_x = [0.0 for _ in range(p)]
            for j in range(k):
                for a in range(p):
                    expected_x[a] += pr[j] * features[j][a]  # type: ignore[index]

            site_score = [site_I * (features[selected][a] - expected_x[a]) for a in range(p)]  # type: ignore[index]
            protein = str(proteins[row_idx])  # type: ignore[index]
            for a in range(p):
                gradient[a] += site_score[a]
                stratum_beta_scores[protein][a] += site_score[a]

            if q:
                for r in range(q):
                    stratum_alpha_scores[protein][r] += (1.0 if selected == r else 0.0) - pr[r]

            logits = [alpha[j] + site_I * eta[j] for j in range(k)]
            loglik += logits[selected] - logsumexp(logits)

            for j in range(k):
                diff_x = [site_I * (features[j][a] - expected_x[a]) for a in range(p)]  # type: ignore[index]
                for a in range(p):
                    for b in range(p):
                        I_bb[a][b] += pr[j] * diff_x[a] * diff_x[b]

            if q:
                expected_alpha = [pr[j] for j in range(q)]
                for j in range(k):
                    diff_alpha = [(1.0 if j == r else 0.0) - expected_alpha[r] for r in range(q)]
                    diff_x = [site_I * (features[j][a] - expected_x[a]) for a in range(p)]  # type: ignore[index]
                    for a in range(p):
                        for r in range(q):
                            I_ba[a][r] += pr[j] * diff_x[a] * diff_alpha[r]
                    for r in range(q):
                        for s in range(q):
                            I_aa[r][s] += pr[j] * diff_alpha[r] * diff_alpha[s]

        if q:
            try:
                solved = [solve_linear(I_aa, I_ba[a]) for a in range(p)]
                for a in range(p):
                    for b in range(p):
                        info[a][b] += I_bb[a][b] - sum(I_ba[b][r] * solved[a][r] for r in range(q))
                for protein, beta_score in stratum_beta_scores.items():
                    alpha_score = stratum_alpha_scores[protein]
                    nuisance_projection = [
                        sum(solved[a][r] * alpha_score[r] for r in range(q)) for a in range(p)
                    ]
                    for a in range(p):
                        protein_scores[protein][a] += beta_score[a] - nuisance_projection[a]
            except ValueError:
                all_alpha_converged = False
        else:
            for a in range(p):
                for b in range(p):
                    info[a][b] += I_bb[a][b]
            for protein, beta_score in stratum_beta_scores.items():
                for a in range(p):
                    protein_scores[protein][a] += beta_score[a]

    return {
        "loglik": loglik,
        "gradient": gradient,
        "info": info,
        "protein_scores": dict(protein_scores),
        "alpha_converged": all_alpha_converged,
    }


def fit_model(strata: list[dict[str, object]]) -> dict[str, object]:
    beta = [0.0 for _ in PARAM_NAMES]
    current = fit_at_beta(strata, beta)
    converged = False

    for _ in range(MAX_NEWTON):
        gradient = current["gradient"]  # type: ignore[assignment]
        info = current["info"]  # type: ignore[assignment]
        max_grad = max(abs(value) for value in gradient)  # type: ignore[arg-type]
        if max_grad < GRAD_TOL:
            converged = True
            break
        try:
            step = solve_linear(info, gradient)  # type: ignore[arg-type]
        except ValueError:
            break
        step_norm = max(abs(value) for value in step)
        if step_norm < BETA_TOL:
            converged = True
            break

        old_loglik = float(current["loglik"])
        accepted = False
        scale = 1.0
        for _ in range(40):
            candidate_beta = [b + scale * s for b, s in zip(beta, step)]
            candidate = fit_at_beta(strata, candidate_beta)
            if float(candidate["loglik"]) >= old_loglik - 1.0e-9:
                beta = candidate_beta
                current = candidate
                accepted = True
                break
            scale *= 0.5
        if not accepted:
            break

    final = fit_at_beta(strata, beta)
    final["beta"] = beta
    final["converged"] = converged and bool(final["alpha_converged"])
    return final


def correlation(left: list[float], right: list[float]) -> float:
    left_mean = mean(left)
    right_mean = mean(right)
    num = sum((a - left_mean) * (b - right_mean) for a, b in zip(left, right))
    left_ss = sum((a - left_mean) ** 2 for a in left)
    right_ss = sum((b - right_mean) ** 2 for b in right)
    if left_ss <= 0.0 or right_ss <= 0.0:
        return 0.0
    return num / math.sqrt(left_ss * right_ss)


def collinearity_diagnostics(
    sites: list[dict[str, object]], rscu: dict[tuple[str, str, str], float]
) -> dict[str, float]:
    h_values: list[float] = []
    comp_values: list[float] = []
    rscu_values: list[float] = []
    gc3_values: list[float] = []
    strata_sizes = Counter((str(site["organism"]), str(site["amino_acid"])) for site in sites)
    for (organism, aa), n_sites in sorted(strata_sizes.items()):
        for codon in SYNONYMOUS[aa]:
            feat = codon_features(codon, aa, rscu[(organism, aa, codon)])
            h_values.extend([feat[0]] * n_sites)
            comp_values.extend([feat[1]] * n_sites)
            rscu_values.extend([feat[2]] * n_sites)
            gc3_values.extend([feat[3]] * n_sites)
    return {
        "h_comp": correlation(h_values, comp_values),
        "h_rscu": correlation(h_values, rscu_values),
        "h_gc3": correlation(h_values, gc3_values),
    }


def cluster_score_bootstrap_lower95(
    protein_scores: dict[str, list[float]],
    covariance: list[list[float]],
    beta_hat: list[float],
) -> float:
    proteins = sorted(protein_scores)
    rng = random.Random(stable_seed(BOOTSTRAP_SEED))
    draws: list[float] = []
    for _ in range(N_BOOTSTRAP):
        score = [0.0 for _ in PARAM_NAMES]
        for _ in proteins:
            selected = proteins[rng.randrange(len(proteins))]
            selected_score = protein_scores[selected]
            for j in range(len(score)):
                score[j] += selected_score[j]
        delta = [sum(covariance[row][col] * score[col] for col in range(len(score))) for row in range(len(score))]
        draws.append(beta_hat[0] + delta[0])
    return percentile(draws, 0.05)


def make_checks() -> list[str]:
    return [
        "reads_only_committed_synced_dms_panel",
        "standard_code_synonymous_choice_sets_for_L_R_S",
        "native_h_cross_checked_against_standard_code",
        "alternative_specific_intercepts_absorbed_by_organism_x_amino_acid_x_codon",
        "zero_observed_codons_have_minus_infinity_absorbed_intercept_in_profile_likelihood",
        "rscu_for_alternatives_recomputed_from_panel_native_codons_by_organism_x_amino_acid_usage_proxy",
        "composition_controls_include_total_GC_fraction_and_GC3_indicator",
        "primary_test_is_one_sided_beta_h_greater_than_zero",
        "cluster_bootstrap_uses_protein_cluster_score_resampling",
        "no_panel_registry_paper_state_or_other_experiment_modified",
    ]


def main() -> None:
    provenance, sites = load_panel()
    rscu = compute_rscu_proxy(sites)
    validate_panel(sites, rscu)
    strata = build_strata(sites, rscu)
    fit = fit_model(strata)
    beta = fit["beta"]  # type: ignore[assignment]
    converged = bool(fit["converged"])
    info = fit["info"]  # type: ignore[assignment]
    collin = collinearity_diagnostics(sites, rscu)
    proteins = sorted({str(site["uniprot"]) for site in sites})
    by_aa = Counter(str(site["amino_acid"]) for site in sites)

    beta_h_se: float | None = None
    beta_h_wald_p: float | None = None
    lower95: float | None = None
    covariance: list[list[float]] | None = None
    try:
        covariance = inverse_matrix(info)  # type: ignore[arg-type]
        beta_h_se = math.sqrt(max(0.0, covariance[0][0]))
        z = beta[0] / beta_h_se if beta_h_se and beta_h_se > 0.0 else 0.0
        beta_h_wald_p = normal_sf(z)
        lower95 = cluster_score_bootstrap_lower95(fit["protein_scores"], covariance, beta)  # type: ignore[arg-type]
    except (ValueError, ZeroDivisionError):
        converged = False

    collinearity_tripped = abs(collin["h_comp"]) > 0.95
    if collinearity_tripped or not converged or beta_h_wald_p is None or lower95 is None:
        status = "needs_derivation"
        interpretation = "conditional codon-choice logit could not support an identified beta_h verdict"
    elif beta[0] > 0.0 and beta_h_wald_p <= 0.01 and lower95 > 0.0:
        status = "certified"
        interpretation = (
            "DMS-intolerant sites preferentially use high-escape codons BEYOND the "
            "preregistered composition + optimality model"
        )
    else:
        status = "coincidence"
        interpretation = (
            "no detectable edge-hiding allocation signal beyond composition/optimality; "
            "the certified BC7 edge-hiding remains a static code-table extremality with "
            "no detected functional codon-allocation signature in DMS data"
        )

    reason = (
        f"beta_h={round_float(beta[0])}, p={round_float(beta_h_wald_p)}, "
        f"bootstrap_lower95={round_float(lower95)}, n_proteins={len(proteins)}, "
        f"n_sites={len(sites)}, collinearity h_comp={round_float(collin['h_comp'])}, "
        f"h_rscu={round_float(collin['h_rscu'])}. {interpretation}. "
        "The model absorbs organism x amino-acid x codon baselines and tests only "
        "I-by-codon-covariate slopes. RSCU for alternative codons is recomputed from "
        "the committed panel's organism-level native codon counts as a usage proxy. "
        "This does not certify that h is causal or that edge-hiding is functional: h "
        "is deterministic codon identity, ProteinGym is amino-acid-substitution "
        "fitness, and a within-site randomized synonymous-recoding experiment would "
        "be needed for causal wording. tAI/decoding-accuracy (tRNA) plus "
        "dinucleotide/DeltaMFE are documented sensitivity extensions not included "
        "here; given the null marginal result, they are not expected to change this "
        "verdict."
    )

    emit(
        status,
        n_proteins=len(proteins),
        n_sites=len(sites),
        by_aa={aa: by_aa.get(aa, 0) for aa in ("L", "R", "S")},
        beta_h=round_float(beta[0]),
        beta_h_se=round_float(beta_h_se),
        beta_h_wald_p=round_float(beta_h_wald_p),
        beta_h_bootstrap_lower95=round_float(lower95),
        beta_g_comp=round_float(beta[1]),
        beta_r_rscu=round_float(beta[2]),
        beta_gc3=round_float(beta[3]),
        collinearity={key: round_float(value) for key, value in collin.items()},
        loglik=round_float(float(fit["loglik"])),
        converged=converged,
        n_bootstrap=N_BOOTSTRAP,
        checks=make_checks(),
        reason=reason,
    )


if __name__ == "__main__":
    main()

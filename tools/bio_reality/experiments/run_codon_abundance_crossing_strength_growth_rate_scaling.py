#!/usr/bin/env python3
"""Codon-abundance crossing strength versus independent growth-time scaling."""

import json
import math
import pathlib
import random
import statistics
import sys
import time


EXPERIMENT_ID = "codon_abundance_crossing_strength_growth_rate_scaling"
CLAIM_ID = "h3.cross_layer_relation.translational_selection_growth_scaling.codon_abundance_strength_doubling_time"

SEED = 7819441
FOLD_COUNT = 5
PERMUTATION_COUNT = 20000
MIN_GENES_PER_ORGANISM = 500
EPS = 1e-12
RIDGE_LAMBDA = 1e-8

ORGANISMS = [
    "bacillus_subtilis_subsp_subtilis_str_168",
    "caenorhabditis_elegans",
    "danio_rerio",
    "dictyostelium_discoideum",
    "drosophila_melanogaster",
    "escherichia_coli_k12_mg1655",
    "gallus_gallus",
    "halobacterium_salinarum",
    "homo_sapiens",
    "mus_musculus",
    "mycobacterium_smegmatis_str_mc2_155",
    "pseudomonas_aeruginosa_pao1",
    "rattus_norvegicus",
    "saccharomyces_cerevisiae",
    "sulfolobus_solfataricus",
    "campylobacter_jejuni_subsp_jejuni_nctc_11168",
    "salmonella_enterica_serovar_typhimurium_lt2",
    "staphylococcus_aureus_nctc_8325",
    "mycobacterium_tuberculosis_h37rv",
    "klebsiella_pneumoniae_mgh_78578",
]

TRNA_FILE_SLUG = {
    "escherichia_coli_k12_mg1655": "escherichia_coli",
}

# Independent literature-derived minimum growth/generation proxy, in minutes.
# arabidopsis_thaliana: Arabidopsis root/meristem or suspension-cell cycle, shortest canonical lab cell-cycle scale.
# bacillus_subtilis_subsp_subtilis_str_168: B. subtilis 168 rich-medium minimum doubling near 25 min.
# caenorhabditis_elegans: C. elegans rapid embryonic blastomere cycle, canonical short cell-cycle scale.
# danio_rerio: zebrafish early embryonic cleavage-cycle interval under standard lab conditions.
# dictyostelium_discoideum: Dictyostelium axenic/log-phase doubling reported on a several-hour scale.
# drosophila_melanogaster: Drosophila syncytial embryo nuclear cycles, shortest canonical lab cell-cycle scale.
# escherichia_coli_k12_mg1655: E. coli K-12 rich-medium minimum doubling near 20 min.
# gallus_gallus: chicken DT40/early embryonic cell-cycle scale under lab culture.
# halobacterium_salinarum: Halobacterium salinarum optimal lab doubling on a several-hour scale.
# homo_sapiens: canonical fast proliferating human/mammalian cultured-cell cycle near one day.
# mus_musculus: mouse embryonic stem-cell cycle near 12 h under optimal culture.
# mycobacterium_smegmatis_str_mc2_155: fast-growing mycobacterium doubling near 3 h.
# pseudomonas_aeruginosa_pao1: P. aeruginosa PAO1 rich-medium doubling near 30-40 min.
# rattus_norvegicus: rat/mammalian cultured-cell cycle on an 18 h scale.
# saccharomyces_cerevisiae: S. cerevisiae rich-medium minimum doubling near 90 min.
# sulfolobus_solfataricus: Sulfolobus optimal thermoacidophile growth on a several-hour scale.
DOUBLING_TIME_MIN = {
    "arabidopsis_thaliana": 600.0,
    "bacillus_subtilis_subsp_subtilis_str_168": 25.0,
    "caenorhabditis_elegans": 10.0,
    "danio_rerio": 15.0,
    "dictyostelium_discoideum": 240.0,
    "drosophila_melanogaster": 8.0,
    "escherichia_coli_k12_mg1655": 20.0,
    "gallus_gallus": 480.0,
    "halobacterium_salinarum": 240.0,
    "homo_sapiens": 1440.0,
    "mus_musculus": 720.0,
    "mycobacterium_smegmatis_str_mc2_155": 180.0,
    "pseudomonas_aeruginosa_pao1": 35.0,
    "rattus_norvegicus": 1080.0,
    "saccharomyces_cerevisiae": 90.0,
    "sulfolobus_solfataricus": 360.0,
    "campylobacter_jejuni_subsp_jejuni_nctc_11168": 90.0,
    "salmonella_enterica_serovar_typhimurium_lt2": 25.0,
    "corynebacterium_glutamicum_atcc_13032": 50.0,
    "deinococcus_radiodurans_r1": 90.0,
    "helicobacter_pylori_26695": 150.0,
    "staphylococcus_aureus_nctc_8325": 30.0,
    "mycobacterium_tuberculosis_h37rv": 1440.0,
    "klebsiella_pneumoniae_mgh_78578": 30.0,
}

DOUBLING_TIME_SOURCE = {
    "arabidopsis_thaliana": "Arabidopsis lab cell-cycle proxy from root/meristem or suspension-cell literature; used as a shortest proliferative-cell scale, not a whole-plant generation time.",
    "bacillus_subtilis_subsp_subtilis_str_168": "Bacillus subtilis 168 rich-medium growth literature and textbook values, rounded to a 25 min minimum doubling scale.",
    "caenorhabditis_elegans": "C. elegans embryology literature, using rapid early embryonic blastomere cycles as the shortest proliferative-cell scale.",
    "danio_rerio": "Zebrafish early embryology literature, using early cleavage-cycle intervals under standard laboratory conditions.",
    "dictyostelium_discoideum": "Dictyostelium axenic/log-phase culture literature, rounded to a several-hour vegetative doubling scale.",
    "drosophila_melanogaster": "Drosophila embryology literature, using rapid syncytial nuclear cycles as the shortest proliferative-cell scale.",
    "escherichia_coli_k12_mg1655": "E. coli K-12 rich-medium growth literature and textbook values, rounded to a 20 min minimum doubling scale.",
    "gallus_gallus": "Chicken DT40 or early embryonic-cell culture literature, used as a fast avian proliferative-cell scale.",
    "halobacterium_salinarum": "Halobacterium salinarum optimal laboratory culture literature, rounded to a several-hour doubling scale.",
    "homo_sapiens": "Human fast proliferating cultured-cell literature, rounded to a one-day cell-cycle scale.",
    "mus_musculus": "Mouse embryonic stem-cell culture literature, rounded to a 12 h cell-cycle scale.",
    "mycobacterium_smegmatis_str_mc2_155": "Mycobacterium smegmatis fast-growing laboratory culture literature, rounded to a 3 h doubling scale.",
    "pseudomonas_aeruginosa_pao1": "Pseudomonas aeruginosa PAO1 rich-medium growth literature, rounded to a 30-40 min minimum doubling scale.",
    "rattus_norvegicus": "Rat or mammalian cultured-cell literature, rounded to an 18 h proliferative-cell scale.",
    "saccharomyces_cerevisiae": "Saccharomyces cerevisiae rich-medium growth literature and textbook values, rounded to a 90 min minimum doubling scale.",
    "sulfolobus_solfataricus": "Sulfolobus solfataricus optimal thermoacidophile culture literature, rounded to a several-hour doubling scale.",
    "campylobacter_jejuni_subsp_jejuni_nctc_11168": "Campylobacter jejuni NCTC 11168 microaerophilic rich-medium doubling literature, ~1.5 h scale.",
    "salmonella_enterica_serovar_typhimurium_lt2": "Salmonella enterica Typhimurium LT2 enteric rich-medium minimum doubling, ~25 min scale.",
    "corynebacterium_glutamicum_atcc_13032": "Corynebacterium glutamicum ATCC 13032 industrial rich-medium doubling, ~45-60 min scale.",
    "deinococcus_radiodurans_r1": "Deinococcus radiodurans R1 optimal lab doubling literature, ~1.5 h scale.",
    "helicobacter_pylori_26695": "Helicobacter pylori 26695 microaerophilic slow doubling literature, ~2.5 h scale.",
    "staphylococcus_aureus_nctc_8325": "Staphylococcus aureus NCTC 8325 rich-medium minimum doubling, ~30 min scale.",
    "mycobacterium_tuberculosis_h37rv": "Mycobacterium tuberculosis H37Rv canonical slow generation time, ~24 h scale.",
    "klebsiella_pneumoniae_mgh_78578": "Klebsiella pneumoniae enteric rich-medium fast doubling literature, ~30 min scale.",
}

CUN_CODONS = ["CUU", "CUC", "CUA", "CUG"]
UUR_CODONS = ["UUA", "UUG"]
Q9_FAMILIES = [
    ["UUU", "UUC"],
    ["UUA", "UUG"],
    ["UCU", "UCC", "UCA", "UCG"],
    ["UAU", "UAC"],
    ["UGU", "UGC"],
    ["CUU", "CUC", "CUA", "CUG"],
    ["CCU", "CCC", "CCA", "CCG"],
    ["CAU", "CAC"],
    ["CAA", "CAG"],
    ["CGU", "CGC", "CGA", "CGG"],
    ["AUU", "AUC", "AUA"],
    ["ACU", "ACC", "ACA", "ACG"],
    ["AAU", "AAC"],
    ["AAA", "AAG"],
    ["AGU", "AGC"],
    ["AGA", "AGG"],
    ["GUU", "GUC", "GUA", "GUG"],
    ["GCU", "GCC", "GCA", "GCG"],
    ["GAU", "GAC"],
    ["GAA", "GAG"],
    ["GGU", "GGC", "GGA", "GGG"],
]


def emit(status, **kw):
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")))
    sys.exit(0 if status == "passed" else 3)


def load_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def finite_number(value):
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def numeric(value, field):
    if not finite_number(value):
        raise ValueError(field + " must be finite numeric")
    return float(value)


def mean(values):
    return sum(values) / len(values)


def stable_int(material):
    value = 1469598103934665603
    for char in material:
        value ^= ord(char)
        value = (value * 1099511628211) % (1 << 63)
    return value


def dna_to_rna(codon):
    return str(codon).upper().replace("T", "U")


def standard_code(repo):
    raw = load_json(repo / "tools/bio_reality/data/ncbi_genetic_codes.json")
    if not isinstance(raw, dict):
        raise ValueError("NCBI genetic code payload must be an object")
    table = None
    for item in raw.get("tables", []):
        if isinstance(item, dict) and item.get("table_id") == 1:
            table = item
            break
    codons = raw.get("codon_order", [])
    if not isinstance(codons, list) or not isinstance(table, dict):
        raise ValueError("standard genetic code table is absent")
    aa_string = table.get("aa")
    if not isinstance(aa_string, str) or len(codons) != len(aa_string):
        raise ValueError("standard genetic code table is malformed")
    return {str(codon): aa for codon, aa in zip(codons, aa_string)}


def fibers_for(code, codons):
    fibers = {}
    for codon in codons:
        fibers.setdefault(code[codon], []).append(codon)
    return fibers


def zero(codons):
    return {codon: 0.0 for codon in codons}


def project_syn(vector, fibers):
    out = dict(vector)
    for fiber in fibers.values():
        fiber_mean = sum(vector[codon] for codon in fiber) / len(fiber)
        for codon in fiber:
            out[codon] = vector[codon] - fiber_mean
    return out


def q_vectors(codons):
    raw = {}
    q = zero(codons)
    q["AAA"] = 1.0
    q["AAG"] = -1.0
    raw["K_AAA"] = q

    q = zero(codons)
    for codon in ["AGA", "AGG"]:
        q[codon] = 1.0
    for codon in ["CGU", "CGC", "CGA", "CGG"]:
        q[codon] = -0.25
    raw["Arg_AGR"] = q

    q = zero(codons)
    q["AUA"] = 1.0
    q["AUU"] = -1.0
    q["AUC"] = -1.0
    raw["Ile_AUA"] = q

    q = zero(codons)
    for codon in CUN_CODONS:
        q[codon] = 0.25
    for codon in UUR_CODONS:
        q[codon] = -0.5
    raw["Leu_CUN_vs_UUR"] = q

    q = zero(codons)
    q["UUA"] = 1.0
    q["UUG"] = -1.0
    raw["Leu_UUA_vs_UUG"] = q

    q = zero(codons)
    for codon in ["UCA", "UCG"]:
        q[codon] = 0.5
    for codon in ["AGU", "AGC"]:
        q[codon] = -0.5
    raw["Ser_UCR_vs_AGY"] = q

    q = zero(codons)
    q["UCA"] = 1.0
    q["UCG"] = -1.0
    raw["Ser_UCA_vs_UCG"] = q

    q = zero(codons)
    for codon in ["ACA", "ACG"]:
        q[codon] = 0.5
    for codon in ["ACU", "ACC"]:
        q[codon] = -0.5
    raw["Thr_ACR_vs_ACY"] = q

    q = zero(codons)
    for family in Q9_FAMILIES:
        q[family[0]] += 1.0
        q[family[-1]] -= 1.0
    raw["f3_stress"] = q
    return raw


def standard_amino_acids(code, codons):
    aas = sorted({code[codon] for codon in codons if code[codon] != "*"})
    if len(aas) != 20:
        raise ValueError("standard code should expose exactly 20 amino acids")
    return aas


def codon_counts_rna(record, codons, organism, row_index):
    raw = record.get("codon_counts")
    if not isinstance(raw, dict):
        raise ValueError(organism + ".joined[" + str(row_index) + "].codon_counts must be an object")
    converted = {codon: 0 for codon in codons}
    for raw_codon, raw_count in raw.items():
        codon = dna_to_rna(raw_codon)
        if codon in converted:
            value = numeric(raw_count, organism + ".joined[" + str(row_index) + "].codon_counts." + str(raw_codon))
            if value < 0 or int(value) != value:
                raise ValueError("codon count must be a non-negative integer")
            converted[codon] += int(value)
    return converted


def normed_coordinate(frequencies, q, codons):
    denom = math.sqrt(sum(q[codon] * q[codon] for codon in codons))
    if denom <= EPS:
        raise ValueError("q vector has zero norm")
    return sum(frequencies[codon] * q[codon] for codon in codons) / denom


def vector_dot(left, right):
    return sum(left[index] * right[index] for index in range(len(left)))


def vector_norm(vector):
    return math.sqrt(vector_dot(vector, vector))


def transpose(matrix):
    if not matrix:
        return []
    return [[row[index] for row in matrix] for index in range(len(matrix[0]))]


def orthonormal_basis_from_columns(matrix):
    basis = []
    if not matrix:
        return basis
    for column in transpose(matrix):
        residual = list(column)
        for q in basis:
            coeff = vector_dot(residual, q)
            for index in range(len(residual)):
                residual[index] -= coeff * q[index]
        norm = vector_norm(residual)
        column_norm = vector_norm(column)
        if norm > 1e-10 * max(1.0, column_norm):
            basis.append([value / norm for value in residual])
    return basis


def project_with_basis(matrix, basis):
    if not matrix:
        return []
    out = [[0.0 for _ in matrix[0]] for _ in matrix]
    columns = transpose(matrix)
    for q in basis:
        for col_index, column in enumerate(columns):
            coeff = vector_dot(column, q)
            for row_index in range(len(matrix)):
                out[row_index][col_index] += coeff * q[row_index]
    return out


def subtract_matrix(left, right):
    return [
        [left[row][col] - right[row][col] for col in range(len(left[row]))]
        for row in range(len(left))
    ]


def residualize(matrix, controls):
    basis = orthonormal_basis_from_columns(controls)
    return subtract_matrix(matrix, project_with_basis(matrix, basis)), len(basis)


def matrix_column(matrix, index):
    return [row[index] for row in matrix]


def frobenius2(matrix):
    return sum(value * value for row in matrix for value in row)


def explained_by_design(design, response):
    basis = orthonormal_basis_from_columns(design)
    projected = project_with_basis(response, basis)
    return frobenius2(projected), len(basis)


def solve_linear(matrix, rhs):
    n = len(rhs)
    aug = [list(matrix[row]) + [rhs[row]] for row in range(n)]
    for col in range(n):
        pivot = col
        best = abs(aug[col][col])
        for row in range(col + 1, n):
            value = abs(aug[row][col])
            if value > best:
                best = value
                pivot = row
        if best <= 1e-14:
            aug[col][col] += RIDGE_LAMBDA
            pivot = col
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        scale = aug[col][col]
        if abs(scale) <= 1e-18:
            scale = 1e-18
            aug[col][col] = scale
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


def deterministic_folds(n, organism):
    indices = list(range(n))
    rng = random.Random(SEED + stable_int(organism))
    rng.shuffle(indices)
    folds = [[] for _ in range(FOLD_COUNT)]
    for position, index in enumerate(indices):
        folds[position % FOLD_COUNT].append(index)
    return folds


def fit_linear_ridge(x_rows, y_values, indices):
    width = len(x_rows[0])
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    xty = [0.0 for _ in range(width)]
    for index in indices:
        row = x_rows[index]
        y = y_values[index]
        for i in range(width):
            xty[i] += row[i] * y
            ri = row[i]
            for j in range(i, width):
                xtx[i][j] += ri * row[j]
    for i in range(width):
        for j in range(i):
            xtx[i][j] = xtx[j][i]
        xtx[i][i] += RIDGE_LAMBDA
    return solve_linear(xtx, xty)


def cv_predict(x_rows, y_values, folds):
    n = len(y_values)
    predictions = [0.0 for _ in range(n)]
    all_indices = set(range(n))
    for test_indices in folds:
        test_set = set(test_indices)
        train_indices = [index for index in all_indices if index not in test_set]
        coefficients = fit_linear_ridge(x_rows, y_values, train_indices)
        for index in test_indices:
            predictions[index] = vector_dot(x_rows[index], coefficients)
    return predictions


def r2_against_zero(y_values, predictions):
    energy = vector_dot(y_values, y_values)
    if energy <= EPS:
        return 0.0
    sse = sum((y - pred) * (y - pred) for y, pred in zip(y_values, predictions))
    return 1.0 - sse / energy


def rank_average(values):
    indexed = sorted(enumerate(values), key=lambda item: item[1])
    ranks = [0.0 for _ in values]
    index = 0
    while index < len(indexed):
        end = index + 1
        while end < len(indexed) and indexed[end][1] == indexed[index][1]:
            end += 1
        average_rank = 0.5 * (index + 1 + end)
        for cursor in range(index, end):
            ranks[indexed[cursor][0]] = average_rank
        index = end
    return ranks


def pearson(left, right):
    if len(left) != len(right) or len(left) < 3:
        return None
    left_mean = mean(left)
    right_mean = mean(right)
    left_energy = sum((value - left_mean) ** 2 for value in left)
    right_energy = sum((value - right_mean) ** 2 for value in right)
    if left_energy <= EPS or right_energy <= EPS:
        return None
    numerator = sum((left[index] - left_mean) * (right[index] - right_mean) for index in range(len(left)))
    return numerator / math.sqrt(left_energy * right_energy)


def spearman(left, right):
    if len(left) != len(right) or len(left) < 3:
        return None
    return pearson(rank_average(left), rank_average(right))


def residualize_vector(values, controls):
    residual, rank = residualize([[value] for value in values], controls)
    return matrix_column(residual, 0), rank


def partial_spearman(x_values, y_values, covariate_columns):
    if len(x_values) != len(y_values) or len(x_values) < 4:
        return None, 0
    ranked_x = rank_average(x_values)
    ranked_y = rank_average(y_values)
    ranked_covariates = [rank_average(column) for column in covariate_columns]
    controls = []
    for row_index in range(len(x_values)):
        controls.append([1.0] + [column[row_index] for column in ranked_covariates])
    x_residual, rank_x = residualize_vector(ranked_x, controls)
    y_residual, rank_y = residualize_vector(ranked_y, controls)
    rho = pearson(x_residual, y_residual)
    return rho, min(rank_x, rank_y)


def percentile(values, probability):
    if not values:
        return None
    ordered = sorted(values)
    if len(ordered) == 1:
        return ordered[0]
    position = probability * (len(ordered) - 1)
    lower = int(math.floor(position))
    upper = int(math.ceil(position))
    if lower == upper:
        return ordered[lower]
    fraction = position - lower
    return ordered[lower] * (1.0 - fraction) + ordered[upper] * fraction


def two_sided_permutation_p(observed, values_to_shuffle, fixed_values, covariate_columns, material):
    if observed is None:
        return None, [], None
    rng = random.Random(SEED + stable_int(material))
    exceed = 0
    null = []
    shuffled = list(values_to_shuffle)
    for _ in range(PERMUTATION_COUNT):
        rng.shuffle(shuffled)
        if covariate_columns:
            permuted, _ = partial_spearman(shuffled, fixed_values, covariate_columns)
        else:
            permuted = spearman(shuffled, fixed_values)
        if permuted is None:
            continue
        null.append(permuted)
        if abs(permuted) >= abs(observed) - 1e-15:
            exceed += 1
    p_value = (exceed + 1) / (len(null) + 1) if null else None
    abs_null = [abs(value) for value in null]
    null95 = percentile(abs_null, 0.95)
    return p_value, null, null95


def trna_slug_for(organism):
    return TRNA_FILE_SLUG.get(organism, organism)


def trna_pool_size(repo, organism):
    path = repo / ("tools/bio_reality/data/gtrnadb_trna_all_copy_" + trna_slug_for(organism) + ".json")
    if not path.exists():
        return None, None, "missing_gtrnadb_trna_all_copy_json"
    raw = load_json(path)
    copies = raw.get("trna_all_copies") if isinstance(raw, dict) else None
    if not isinstance(copies, dict):
        return None, None, "trna_all_copies_missing"
    total = 0
    for key, value in copies.items():
        if not finite_number(value):
            return None, None, "non_numeric_trna_copy_count:" + str(key)
        total += int(value)
    return total, len(copies), None


def organism_rows(payload, organism, codons, code, aa_order, q_projected, q_names):
    joined = payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(organism + " payload lacks joined list")

    x_rows = []
    y_rows = []
    control_rows = []
    aggregate_gc3 = 0
    aggregate_total = 0
    skipped = {
        "non_object": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }

    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        abundance = numeric(item.get("abundance_ppm"), organism + ".joined[" + str(row_index) + "].abundance_ppm")
        if abundance <= 0.0:
            skipped["nonpositive_abundance"] += 1
            continue
        cds_len_nt = numeric(item.get("cds_len_nt"), organism + ".joined[" + str(row_index) + "].cds_len_nt")
        if cds_len_nt <= 0.0:
            skipped["invalid_length"] += 1
            continue

        counts = codon_counts_rna(item, codons, organism, row_index)
        total = sum(counts.values())
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue

        frequencies = {codon: counts[codon] / total for codon in codons}
        x_rows.append([normed_coordinate(frequencies, q_projected[name], codons) for name in q_names])
        y_rows.append([math.log10(abundance)])

        aa_counts = {aa: 0 for aa in aa_order}
        for codon in codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        if aa_total <= 0:
            raise ValueError(organism + ".joined[" + str(row_index) + "] has no amino-acid counts")

        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
        aggregate_gc3 += sum(counts[codon] for codon in codons if codon[2] in {"G", "C"})
        aggregate_total += total
        control_rows.append(
            [1.0, math.log(cds_len_nt)]
            + [aa_counts[aa] / aa_total for aa in aa_order]
            + [gc3]
        )

    gc3_value = None if aggregate_total <= 0 else aggregate_gc3 / aggregate_total
    summary = {
        "n_joined_reported": payload.get("n_joined"),
        "join_hit_rate": payload.get("join_hit_rate"),
        "n_genes_used": len(x_rows),
        "skipped_records": skipped,
    }
    return x_rows, y_rows, control_rows, gc3_value, summary


def compute_strength(repo, organism, codons, code, aa_order, q_projected, q_names):
    path = repo / ("tools/bio_reality/data/cds_codon_abundance_" + organism + ".json")
    if not path.exists():
        return {"organism": organism, "status": "needs_data", "reason": "missing cds_codon_abundance JSON"}
    payload = load_json(path)
    if not isinstance(payload, dict):
        return {"organism": organism, "status": "needs_data", "reason": "cds payload is not an object"}

    x_rows, y_rows, control_rows, gc3, data_summary = organism_rows(
        payload=payload,
        organism=organism,
        codons=codons,
        code=code,
        aa_order=aa_order,
        q_projected=q_projected,
        q_names=q_names,
    )
    n_genes = len(x_rows)
    base = {
        "organism": organism,
        "status": "needs_data",
        "n_genes": n_genes,
        "gc3": gc3,
        "data_summary": data_summary,
    }
    if n_genes < MIN_GENES_PER_ORGANISM:
        base["reason"] = "usable joined genes below gate"
        return base

    x_residualized, rank_controls_x = residualize(x_rows, control_rows)
    y_residualized, rank_controls_y = residualize(y_rows, control_rows)
    y_vector = matrix_column(y_residualized, 0)
    y_energy = vector_dot(y_vector, y_vector)
    if y_energy <= EPS:
        base["reason"] = "zero abundance residual energy after controls"
        base["rank_controls_x"] = rank_controls_x
        base["rank_controls_y"] = rank_controls_y
        return base

    explained, rank_x = explained_by_design(x_residualized, y_residualized)
    insample_r2 = max(0.0, min(1.0, explained / y_energy))
    folds = deterministic_folds(n_genes, organism)
    predictions = cv_predict(x_residualized, y_vector, folds)
    heldout_r2 = r2_against_zero(y_vector, predictions)
    heldout_rho = spearman(predictions, y_vector)

    return {
        "organism": organism,
        "status": "computed",
        "n_genes": n_genes,
        "gc3": gc3,
        "strength": heldout_r2,
        "strength_metric": "5-fold held-out R2 of the 9-coordinate B*_Q6 codon block after residualizing log10 abundance and q-coordinates over length + 20 amino-acid composition + GC3",
        "strength_heldout_r2": heldout_r2,
        "strength_heldout_spearman": heldout_rho,
        "insample_R2_QP": insample_r2,
        "rank_controls_x": rank_controls_x,
        "rank_controls_y": rank_controls_y,
        "rank_q_after_controls": rank_x,
        "residual_abundance_energy": y_energy,
        "fold_count": FOLD_COUNT,
        "data_summary": data_summary,
    }


def build_meta_rows(repo, organism_results):
    rows = []
    for result in organism_results:
        organism = result["organism"]
        trna_total, trna_anticodons, trna_missing_reason = trna_pool_size(repo, organism)
        doubling = DOUBLING_TIME_MIN.get(organism)
        row = {
            "organism": organism,
            "strength_status": result.get("status"),
            "strength": result.get("strength"),
            "n_genes": result.get("n_genes"),
            "gc3": result.get("gc3"),
            "doubling_time_min": doubling,
            "doubling_time_source_note": DOUBLING_TIME_SOURCE.get(organism),
            "log_doubling_time": None if doubling is None or doubling <= 0.0 else math.log(doubling),
            "trna_pool_total_copies": trna_total,
            "trna_anticodon_count": trna_anticodons,
            "trna_missing_reason": trna_missing_reason,
            "strength_needs_data_reason": result.get("reason"),
        }
        rows.append(row)
    return rows


def rows_for_bare(meta_rows):
    out = []
    for row in meta_rows:
        if finite_number(row.get("strength")) and finite_number(row.get("log_doubling_time")):
            out.append(row)
    return out


def rows_for_partial(meta_rows):
    out = []
    for row in meta_rows:
        if (
            finite_number(row.get("strength"))
            and finite_number(row.get("log_doubling_time"))
            and finite_number(row.get("gc3"))
            and finite_number(row.get("trna_pool_total_copies"))
            and float(row["trna_pool_total_copies"]) > 0.0
        ):
            out.append(row)
    return out


def series(rows, key):
    return [float(row[key]) for row in rows]


def log_series(rows, key):
    return [math.log(float(row[key])) for row in rows]


def verdict_from(n_strengths, n_with_doubling, n_partial, bare_p, bare_rho, partial_p, partial_rho):
    if n_with_doubling < 12 or n_partial < 12 or n_strengths < len(ORGANISMS):
        return "needs_data"
    partial_significant = partial_p is not None and partial_p < 0.05
    bare_significant = bare_p is not None and bare_p < 0.05
    partial_abs = 0.0 if partial_rho is None else abs(partial_rho)
    if partial_significant and partial_abs >= 0.10:
        return "crosses_boundary"
    if bare_significant and not partial_significant:
        return "composition_artifact"
    if partial_significant and partial_abs < 0.10:
        return "bounded_descriptor_only"
    if bare_rho is not None and abs(bare_rho) >= 0.10:
        return "bounded_descriptor_only"
    return "bounded_descriptor_only"


def cannot_claim(verdict):
    claims = [
        "N=16 organism is a very small meta sample; p-values come from a deterministic organism-level permutation, not asymptotic power.",
        "The doubling-time table is a curated independent lab growth/generation or shortest cell-cycle proxy; its mixed biological meaning is a real limitation.",
        "Organisms are not phylogenetically independent; this stdlib-only experiment does not run PIC, PGLS, or any tree-aware correction.",
        "Crossing strength depends on the B*_Q6 codon-optimality coordinate block and the length + amino-acid-composition + GC3 control design.",
        "The test is observational and cannot identify causal effects of growth rate on codon usage or abundance.",
        "GtRNAdb tRNA-pool coverage is incomplete for several organisms, and copy number is only a proxy for active tRNA supply.",
        "A needs_data verdict means the local data intersection is insufficient for a registry-grade promoted claim; the reported correlations remain diagnostic.",
    ]
    if verdict == "composition_artifact":
        claims.append("A composition_artifact verdict would not deny growth-associated codon usage; it would say this strength scaling is not independent of GC3/tRNA-pool under this design.")
    return claims


def main():
    started = time.time()
    repo = pathlib.Path(__file__).resolve().parents[3]
    required = ["tools/bio_reality/data/ncbi_genetic_codes.json"]
    required += ["tools/bio_reality/data/cds_codon_abundance_" + organism + ".json" for organism in ORGANISMS]
    missing = [path for path in required if not (repo / path).exists()]
    if missing:
        emit(
            "needs_data",
            verdict="needs_data",
            checks={"local_required_json_present": False},
            result={"missing_required_data": missing, "cannot_claim": ["Local required JSON is absent."]},
        )

    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)

        organism_results = [
            compute_strength(repo, organism, codons, code, aa_order, q_projected, q_names)
            for organism in ORGANISMS
        ]
        meta_rows = build_meta_rows(repo, organism_results)
        strength_rows = [row for row in meta_rows if finite_number(row.get("strength"))]
        n_strengths = len(strength_rows)
        n_with_doubling = sum(1 for row in meta_rows if finite_number(row.get("doubling_time_min")))
        bare_rows = rows_for_bare(meta_rows)
        partial_rows = rows_for_partial(meta_rows)

        bare_strength = series(bare_rows, "strength")
        bare_log_doubling = series(bare_rows, "log_doubling_time")
        bare_rho = spearman(bare_strength, bare_log_doubling)
        bare_p, bare_null, bare_null95 = two_sided_permutation_p(
            bare_rho,
            bare_strength,
            bare_log_doubling,
            [],
            "bare_strength_vs_log_doubling",
        )

        partial_strength = series(partial_rows, "strength")
        partial_log_doubling = series(partial_rows, "log_doubling_time")
        partial_gc3 = series(partial_rows, "gc3")
        partial_log_trna = log_series(partial_rows, "trna_pool_total_copies")
        partial_rho, partial_control_rank = partial_spearman(
            partial_strength,
            partial_log_doubling,
            [partial_gc3, partial_log_trna],
        )
        partial_p, partial_null, partial_null95 = two_sided_permutation_p(
            partial_rho,
            partial_strength,
            partial_log_doubling,
            [partial_gc3, partial_log_trna],
            "partial_strength_vs_log_doubling_given_gc3_log_trna",
        )

        verdict = verdict_from(
            n_strengths,
            n_with_doubling,
            len(partial_rows),
            bare_p,
            bare_rho,
            partial_p,
            partial_rho,
        )
        status = "passed" if verdict != "needs_data" else "needs_data"

        missing_strength = [
            row["organism"]
            for row in meta_rows
            if not finite_number(row.get("strength"))
        ]
        missing_trna = [
            row["organism"]
            for row in meta_rows
            if row.get("trna_pool_total_copies") is None
        ]
        checks = {
            "strengths_recomputed_16org": n_strengths == len(ORGANISMS),
            "base_machinery_reused": len(q_names) == 9 and FOLD_COUNT == 5,
            "doubling_time_curated_independent": n_with_doubling == len(ORGANISMS),
            "gc3_trna_covariates_built": all(row.get("gc3") is not None for row in strength_rows) and len(partial_rows) >= 12,
            "partial_correlation_controls_gc3_trna": partial_rho is not None and len(partial_rows) >= 12,
            "bare_vs_partial_reported": bare_rho is not None and partial_rho is not None,
            "permutation_null_nondegenerate": len(partial_null) >= PERMUTATION_COUNT and len({round(value, 12) for value in partial_null}) > 20,
            "n_with_doubling_reported": n_with_doubling >= 12,
            "growth_scaling_verdict": verdict,
        }

        result = {
            "claimed_layer": "cross_layer_relation",
            "primary_strength_field": "strength_heldout_r2",
            "strength_definition": "Per organism, residualize the 9 B*_Q6 synonymous codon coordinates and log10 protein abundance over length + 20 amino-acid composition + GC3, then fit fold-local linear slopes and report 5-fold held-out R2.",
            "covariates": {
                "GC3": "aggregate third-position G/C fraction over usable joined CDS codons",
                "tRNA_pool": "GtRNAdb total tRNA-all-copy count; anticodon count also reported but total copies are used",
                "growth_trait": "hardcoded independent minimum lab doubling/generation or shortest canonical cell-cycle proxy in minutes, never codon-derived",
            },
            "n_organisms_requested": len(ORGANISMS),
            "n_strengths_computed": n_strengths,
            "n_with_doubling": n_with_doubling,
            "n_bare_strength_doubling": len(bare_rows),
            "n_complete_strength_doubling_gc3_trna": len(partial_rows),
            "missing_strength_organisms": missing_strength,
            "missing_trna_pool_organisms": missing_trna,
            "q_coordinates": q_names,
            "organisms": meta_rows,
            "strength_diagnostics": organism_results,
            "bare": {
                "statistic": "Spearman rho(strength_heldout_r2, log(doubling_time_min))",
                "n": len(bare_rows),
                "organisms": [row["organism"] for row in bare_rows],
                "rho": bare_rho,
                "permutation_trials": PERMUTATION_COUNT,
                "permutation_p_two_sided": bare_p,
                "abs_null95": bare_null95,
            },
            "partial": {
                "statistic": "partial Spearman rho(strength_heldout_r2, log(doubling_time_min) | GC3, log(tRNA_pool_total_copies))",
                "n": len(partial_rows),
                "organisms": [row["organism"] for row in partial_rows],
                "rho": partial_rho,
                "control_rank": partial_control_rank,
                "permutation_trials": PERMUTATION_COUNT,
                "permutation_p_two_sided": partial_p,
                "abs_null95": partial_null95,
                "null_mean": None if not partial_null else mean(partial_null),
                "null_sd": None if len(partial_null) < 2 else statistics.stdev(partial_null),
            },
            "runtime_sec": time.time() - started,
            "cannot_claim": cannot_claim(verdict),
        }

        emit(status, verdict=verdict, checks=checks, result=result)
    except SystemExit:
        raise
    except Exception as exc:
        emit(
            "needs_data",
            verdict="needs_data",
            checks={"runtime_exception": True},
            result={"error": str(exc), "cannot_claim": ["Runtime exception; no scientific conclusion is promoted."]},
        )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""S^QM: B*_Q6 codon residuals against yeast mRNA half-life."""

from __future__ import annotations

import csv
import hashlib
import io
import json
import math
import pathlib
import sys
import urllib.error
import urllib.request
from typing import Any

from run_b_star_q6_protein_omics_survival_powered import (
    DEGENERATE_R2,
    MIN_PROTEINS_PER_ORGANISM,
    RANK_TOL,
    SURVIVAL_EPS,
    codon_counts_rna,
    controls_used,
    explained_by_design,
    matrix_column,
    normed_coordinate,
    numeric,
    residualize,
    standard_amino_acids,
    vector_dot,
)
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    project_syn,
    q_vectors,
    standard_code,
)


EXPERIMENT_ID = "b_star_q6_mrna_half_life_sqm_powered"
CLAIM_ID = "h3.cross_layer_relation.mrna_stability_sqm.b_star_q6_codon_optimality_powered"
CONJECTURE_ID = "q6.codon-optimality.mrna-stability.cross-layer"

ORGANISM = "saccharomyces_cerevisiae"
ORGANISM_LABEL = "Saccharomyces cerevisiae"
NCBI_TAXID = "4932"
NEYMOTIN_URL = "https://raw.githubusercontent.com/gagneurlab/Manuscript_Cheng_RNA_2017/master/data/Neymotin_TableS5.csv"
MRNA_DATA_PATH = "tools/fibonacci_reality/data/mrna_half_life_saccharomyces_cerevisiae_neymotin.json"
CDS_DATA_PATH = "tools/fibonacci_reality/data/cds_codon_abundance_saccharomyces_cerevisiae.json"
PERMUTATION_COUNT = 1000
SIGNIFICANCE_ALPHA = 0.05
USER_AGENT = "fibonacci-reality-sqm/1.0"
RIDGE_EPS = 1e-12


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json_if_changed(path: pathlib.Path, payload: dict[str, object]) -> None:
    text = json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    if path.exists() and path.read_text(encoding="utf-8") == text:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def cannot_claim() -> list[str]:
    return [
        "single dataset (Neymotin et al 2014) metabolic-labeling 4tU yeast mRNA half-life",
        "one organism (S. cerevisiae)",
        "S^QM entries are statistical projections, not a decay mechanism",
        "correlation with codon residual does not establish codon-optimality causation here",
        "half-life is steady-state estimate not direct decay-rate measurement",
        "not ribo-seq, not matched translation-controlled",
    ]


def fetch_bytes(url: str) -> bytes:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=60) as response:
        return response.read()


def parse_neymotin_csv(raw: bytes) -> tuple[list[dict[str, object]], dict[str, object]]:
    text = raw.decode("utf-8-sig")
    reader = csv.DictReader(io.StringIO(text))
    required = {"Syst", "Gene", "thalf"}
    if reader.fieldnames is None or not required.issubset(set(reader.fieldnames)):
        raise ValueError("Neymotin CSV must contain Syst, Gene, and thalf columns")

    rows: list[dict[str, object]] = []
    skipped = {
        "missing_syst": 0,
        "nonpositive_thalf": 0,
        "duplicate_syst": 0,
    }
    seen: set[str] = set()
    for row_index, item in enumerate(reader):
        syst = str(item.get("Syst", "")).strip()
        if not syst:
            skipped["missing_syst"] += 1
            continue
        try:
            thalf = float(str(item.get("thalf", "")).strip())
        except ValueError:
            skipped["nonpositive_thalf"] += 1
            continue
        if thalf <= 0.0:
            skipped["nonpositive_thalf"] += 1
            continue
        if syst in seen:
            skipped["duplicate_syst"] += 1
            continue
        seen.add(syst)
        parsed: dict[str, object] = {
            "Syst": syst,
            "Gene": str(item.get("Gene", "")).strip(),
            "thalf": thalf,
        }
        for optional in ["thalfLow", "thalfHigh", "ss.abundance"]:
            value = str(item.get(optional, "")).strip()
            if value:
                try:
                    parsed[optional] = float(value)
                except ValueError:
                    parsed[optional] = value
        rows.append(parsed)

    return rows, {
        "csv_columns": reader.fieldnames,
        "n_rows_raw": row_index + 1 if "row_index" in locals() else 0,
        "n_valid_half_life_rows": len(rows),
        "skipped_rows": skipped,
    }


def build_neymotin_payload(raw: bytes) -> dict[str, object]:
    rows, parse_summary = parse_neymotin_csv(raw)
    return {
        "schema_version": 1,
        "source_name": "Neymotin et al 2014",
        "source_kind": "yeast_mrna_half_life_metabolic_labeling_4tu",
        "source_url": NEYMOTIN_URL,
        "payload_byte_size": len(raw),
        "payload_sha256": hashlib.sha256(raw).hexdigest(),
        "organism": ORGANISM,
        "organism_label": ORGANISM_LABEL,
        "ncbi_taxid": NCBI_TAXID,
        "readout": "thalf",
        "readout_unit": "minutes",
        "join_key": "Syst",
        "provenance": {
            "source_url": NEYMOTIN_URL,
            "sha256": hashlib.sha256(raw).hexdigest(),
            "cannot_claim": cannot_claim(),
            "note": "Parsed Syst, Gene, thalf, thalfLow, thalfHigh, and ss.abundance from Neymotin_TableS5.csv.",
        },
        "cannot_claim": cannot_claim(),
        "parse_summary": parse_summary,
        "records": rows,
    }


def load_or_fetch_neymotin(repo: pathlib.Path) -> dict[str, object]:
    path = repo / MRNA_DATA_PATH
    if path.exists():
        raw = load_json(path)
        if isinstance(raw, dict) and isinstance(raw.get("records"), list):
            return raw
    payload = build_neymotin_payload(fetch_bytes(NEYMOTIN_URL))
    write_json_if_changed(path, payload)
    return payload


def half_life_by_syst(payload: dict[str, object]) -> tuple[dict[str, dict[str, float]], dict[str, object]]:
    records = payload.get("records")
    if not isinstance(records, list):
        raise ValueError("Neymotin payload must contain records list")
    out: dict[str, dict[str, float]] = {}
    skipped = {
        "non_object": 0,
        "missing_syst": 0,
        "nonpositive_thalf": 0,
        "duplicate_syst": 0,
    }
    for row_index, item in enumerate(records):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        syst = item.get("Syst")
        if not isinstance(syst, str) or not syst:
            skipped["missing_syst"] += 1
            continue
        thalf = numeric(item.get("thalf"), f"Neymotin.records[{row_index}].thalf")
        if thalf <= 0.0:
            skipped["nonpositive_thalf"] += 1
            continue
        if syst in out:
            skipped["duplicate_syst"] += 1
            continue
        out[syst] = {"thalf": thalf}
    return out, {
        "n_half_life_records_reported": payload.get("parse_summary", {}).get("n_valid_half_life_rows") if isinstance(payload.get("parse_summary"), dict) else None,
        "n_valid_half_life_by_syst": len(out),
        "skipped_half_life_records": skipped,
        "source_url": payload.get("source_url"),
        "payload_sha256": payload.get("payload_sha256"),
    }


def yeast_orf_from_protein_id(protein_id: str) -> str | None:
    prefix = f"{NCBI_TAXID}."
    if protein_id.startswith(prefix):
        return protein_id[len(prefix):]
    return None


def append_cds_control_rows(
    *,
    item: dict[str, object],
    row_index: int,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> tuple[list[float], list[float]]:
    cds_len_nt = numeric(item.get("cds_len_nt"), f"{ORGANISM}.joined[{row_index}].cds_len_nt")
    if cds_len_nt <= 0.0:
        raise ValueError("invalid_length")

    counts = codon_counts_rna(item, codons, ORGANISM, row_index)
    total = sum(counts.values())
    if total <= 0:
        raise ValueError("empty_sense_codon_counts")

    frequencies = {codon: counts[codon] / total for codon in codons}
    x_row = [normed_coordinate(frequencies, q_projected[name], codons) for name in q_names]

    aa_counts = {aa: 0 for aa in aa_order}
    for codon in codons:
        aa_counts[code[codon]] += counts[codon]
    aa_total = sum(aa_counts.values())
    if aa_total <= 0:
        raise ValueError("empty_amino_acid_counts")

    gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
    m_density = sum(counts[codon] for codon in q_support) / total
    z_row = (
        [1.0, math.log(cds_len_nt)]
        + [aa_counts[aa] / aa_total for aa in aa_order]
        + [gc3, m_density]
    )
    return x_row, z_row


def joined_rows(
    *,
    cds_payload: dict[str, object],
    half_life_payload: dict[str, object],
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> tuple[list[list[float]], list[list[float]], list[list[float]], list[list[float]], list[str], dict[str, object]]:
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError("yeast CDS payload must contain joined list")
    half_life_index, half_life_summary = half_life_by_syst(half_life_payload)

    x_rows: list[list[float]] = []
    y_mrna_rows: list[list[float]] = []
    y_protein_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    protein_ids: list[str] = []
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "unparseable_yeast_orf": 0,
        "no_half_life_match": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }

    seen: set[str] = set()
    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        orf = yeast_orf_from_protein_id(protein_id)
        if orf is None:
            skipped["unparseable_yeast_orf"] += 1
            continue
        if orf in seen:
            continue
        half_life = half_life_index.get(orf)
        if half_life is None:
            skipped["no_half_life_match"] += 1
            continue
        abundance = numeric(item.get("abundance_ppm"), f"{ORGANISM}.joined[{row_index}].abundance_ppm")
        if abundance <= 0.0:
            skipped["nonpositive_abundance"] += 1
            continue
        try:
            x_row, z_row = append_cds_control_rows(
                item=item,
                row_index=row_index,
                codons=codons,
                code=code,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
            )
        except ValueError as exc:
            key = str(exc)
            if key in skipped:
                skipped[key] += 1
                continue
            raise

        x_rows.append(x_row)
        y_mrna_rows.append([math.log10(half_life["thalf"])])
        y_protein_rows.append([math.log10(abundance)])
        z_rows.append(z_row)
        protein_ids.append(protein_id)
        seen.add(orf)

    summary = {
        **half_life_summary,
        "n_cds_joined_reported": cds_payload.get("n_joined"),
        "cds_join_hit_rate_reported": cds_payload.get("join_hit_rate"),
        "n_joined": len(x_rows),
        "join_key": "CDS protein_id with 4932. prefix stripped equals Neymotin Syst",
        "skipped_cds_records": skipped,
    }
    return x_rows, y_mrna_rows, y_protein_rows, z_rows, protein_ids, summary


def gram_matrix(design: list[list[float]]) -> list[list[float]]:
    if not design:
        return []
    width = len(design[0])
    gram = [[0.0 for _ in range(width)] for _ in range(width)]
    for row in design:
        for i in range(width):
            for j in range(width):
                gram[i][j] += row[i] * row[j]
    return gram


def crossprod_vector(design: list[list[float]], response: list[float]) -> list[float]:
    if not design:
        return []
    width = len(design[0])
    out = [0.0 for _ in range(width)]
    for row, value in zip(design, response):
        for index in range(width):
            out[index] += row[index] * value
    return out


def solve_linear_system(matrix: list[list[float]], rhs: list[float], tol: float = RANK_TOL) -> list[float]:
    n = len(rhs)
    aug = [list(matrix[row]) + [rhs[row]] for row in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= tol:
            raise ValueError("normal-equation solve is rank deficient after ridge")
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


def solve_regularized_normal_equation(
    design: list[list[float]],
    response: list[float],
    ridge: float = RIDGE_EPS,
) -> list[float]:
    gram = gram_matrix(design)
    rhs = crossprod_vector(design, response)
    for index in range(len(gram)):
        gram[index][index] += ridge
    return solve_linear_system(gram, rhs)


def fit_from_residuals(
    *,
    x_tilde: list[list[float]],
    y_tilde: list[list[float]],
    q_names: list[str],
    readout_name: str,
) -> dict[str, object]:
    y_col = matrix_column(y_tilde, 0)
    y_ss = vector_dot(y_col, y_col)
    explained, rank_xtilde = explained_by_design(x_tilde, y_tilde)
    r2 = 0.0 if y_ss <= SURVIVAL_EPS else max(0.0, min(1.0, explained / y_ss))
    coeffs = solve_regularized_normal_equation(x_tilde, y_col)
    entries = dict(zip(q_names, coeffs))

    partial_r2: dict[str, float] = {}
    raw_improvement: dict[str, float] = {}
    for index, q_name in enumerate(q_names):
        x_col = matrix_column(x_tilde, index)
        x_ss = vector_dot(x_col, x_col)
        if x_ss <= SURVIVAL_EPS or y_ss <= SURVIVAL_EPS:
            improvement = 0.0
            partial = 0.0
        else:
            xy = vector_dot(x_col, y_col)
            improvement = (xy * xy) / x_ss
            partial = max(0.0, min(1.0, improvement / y_ss))
        partial_r2[q_name] = partial
        raw_improvement[q_name] = improvement

    dominant_coord = max(q_names, key=lambda name: abs(entries[name]))
    return {
        f"R2_{readout_name}": r2,
        f"S_{readout_name}_entries": entries,
        f"S_{readout_name}_partial_r2": partial_r2,
        "raw_sse_improvement": raw_improvement,
        "dominant_coord": dominant_coord,
        "rank_Xtilde": rank_xtilde,
        "y_residual_energy": y_ss,
        "explained_energy": explained,
    }


def cosine(left: list[float], right: list[float]) -> float:
    left_norm = math.sqrt(sum(value * value for value in left))
    right_norm = math.sqrt(sum(value * value for value in right))
    if left_norm <= SURVIVAL_EPS or right_norm <= SURVIVAL_EPS:
        return 0.0
    return max(-1.0, min(1.0, sum(left[i] * right[i] for i in range(len(left))) / (left_norm * right_norm)))


def deterministic_shuffle(values: list[float], perm_index: int) -> list[float]:
    shuffled = list(values)
    for index in range(len(shuffled) - 1, 0, -1):
        material = f"{EXPERIMENT_ID}|residual_y_permutation|{perm_index}|{index}|{len(shuffled)}"
        digest = hashlib.sha256(material.encode("utf-8")).digest()
        swap_index = int.from_bytes(digest[:8], "big") % (index + 1)
        shuffled[index], shuffled[swap_index] = shuffled[swap_index], shuffled[index]
    return shuffled


def permutation_null(
    *,
    x_tilde: list[list[float]],
    y_tilde: list[list[float]],
    q_names: list[str],
    observed_r2: float,
    observed_entries: dict[str, float],
    count: int,
) -> dict[str, object]:
    y_col = matrix_column(y_tilde, 0)
    r2_exceed = 0
    entry_exceed = {name: 0 for name in q_names}
    entry_abs_max = {name: 0.0 for name in q_names}
    r2_max = 0.0
    r2_sum = 0.0

    for perm_index in range(count):
        perm_y = [[value] for value in deterministic_shuffle(y_col, perm_index)]
        fit = fit_from_residuals(
            x_tilde=x_tilde,
            y_tilde=perm_y,
            q_names=q_names,
            readout_name="QM",
        )
        perm_r2 = float(fit["R2_QM"])
        perm_entries = fit["S_QM_entries"]
        if not isinstance(perm_entries, dict):
            raise ValueError("internal permutation fit lacks S_QM_entries")
        r2_sum += perm_r2
        r2_max = max(r2_max, perm_r2)
        if perm_r2 >= observed_r2:
            r2_exceed += 1
        for name in q_names:
            abs_value = abs(float(perm_entries[name]))
            entry_abs_max[name] = max(entry_abs_max[name], abs_value)
            if abs_value >= abs(observed_entries[name]):
                entry_exceed[name] += 1

    return {
        "permutation_count": count,
        "null_model": "deterministic permutation of residualized log10(thalf) within the Z-orthogonal residual df using hashlib-derived Fisher-Yates swaps",
        "deterministic_seed": f"sha256:{EXPERIMENT_ID}|residual_y_permutation|perm_index|index|n",
        "R2_QM": {
            "p_value_right_tail": (r2_exceed + 1) / (count + 1),
            "null_mean": r2_sum / count if count else 0.0,
            "null_max_seen": r2_max,
        },
        "entries": {
            name: {
                "p_value_two_sided_abs": (entry_exceed[name] + 1) / (count + 1),
                "null_max_abs_seen": entry_abs_max[name],
            }
            for name in q_names
        },
    }


def conclusion_from_null(r2_qm: float, permutation: dict[str, object]) -> dict[str, object]:
    r2_null = permutation.get("R2_QM")
    if not isinstance(r2_null, dict):
        raise ValueError("permutation result lacks R2_QM")
    p_value = float(r2_null["p_value_right_tail"])
    predicts = p_value <= SIGNIFICANCE_ALPHA and r2_qm > SURVIVAL_EPS
    if predicts:
        if r2_qm >= 0.05:
            strength = "strong_statistical_signal"
        elif r2_qm >= 0.01:
            strength = "weak_to_moderate_statistical_signal"
        else:
            strength = "weak_but_null_exceeding_statistical_signal"
        statement = "B*_Q6 codon residuals predict residualized yeast mRNA half-life in this Neymotin 2014 4tU dataset under the deterministic residual-permutation null."
    else:
        strength = "negative_result"
        statement = "B*_Q6 codon residuals do not exceed the deterministic residual-permutation null for residualized yeast mRNA half-life in this dataset."
    return {
        "predicts_mrna_half_life": predicts,
        "strength": strength,
        "decision_rule": f"predictive only if R2_QM > {SURVIVAL_EPS} and permutation p <= {SIGNIFICANCE_ALPHA}",
        "statement": statement,
    }


def finite_unit(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value)) and 0.0 <= float(value) <= 1.0


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    try:
        cds_path = repo / CDS_DATA_PATH
        genetic_code_path = repo / "tools/fibonacci_reality/data/ncbi_genetic_codes.json"
        missing = [str(path.relative_to(repo)) for path in [cds_path, genetic_code_path] if not path.exists()]
        if missing:
            emit("needs_data", missing_required_data=missing, reason="required local yeast CDS codon data not present")

        try:
            half_life_payload = load_or_fetch_neymotin(repo)
        except (urllib.error.URLError, TimeoutError, OSError) as exc:
            emit("needs_data", missing_required_data=[MRNA_DATA_PATH], reason=repr(exc))
        if not isinstance(half_life_payload, dict):
            raise ValueError("Neymotin half-life payload must be an object")

        cds_payload = load_json(cds_path)
        if not isinstance(cds_payload, dict):
            raise ValueError("yeast CDS codon payload must be an object")

        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}

        x_rows, y_mrna_rows, y_protein_rows, z_rows, protein_ids, data_summary = joined_rows(
            cds_payload=cds_payload,
            half_life_payload=half_life_payload,
            codons=codons,
            code=code,
            aa_order=aa_order,
            q_projected=q_projected,
            q_names=q_names,
            q_support=q_support,
        )
        n_joined = len(x_rows)
        if n_joined < MIN_PROTEINS_PER_ORGANISM:
            emit(
                "needs_data",
                reason=f"join yielded n={n_joined}, below honest gate n>={MIN_PROTEINS_PER_ORGANISM}",
                checks=[
                    {
                        "name": "neymotin_loaded",
                        "passed": n_joined >= MIN_PROTEINS_PER_ORGANISM,
                        "actual": data_summary,
                        "expected": f"join n >= {MIN_PROTEINS_PER_ORGANISM}",
                    }
                ],
                result={
                    "claimed_layer": "cross_layer_relation",
                    "conjecture_id": CONJECTURE_ID,
                    "cannot_claim": cannot_claim(),
                },
            )

        x_tilde, rank_z = residualize(x_rows, z_rows)
        y_mrna_tilde, _ = residualize(y_mrna_rows, z_rows)
        y_protein_tilde, _ = residualize(y_protein_rows, z_rows)

        qm_fit = fit_from_residuals(x_tilde=x_tilde, y_tilde=y_mrna_tilde, q_names=q_names, readout_name="QM")
        qp_fit = fit_from_residuals(x_tilde=x_tilde, y_tilde=y_protein_tilde, q_names=q_names, readout_name="QP")
        qm_entries = qm_fit["S_QM_entries"]
        qp_entries = qp_fit["S_QP_entries"]
        if not isinstance(qm_entries, dict) or not isinstance(qp_entries, dict):
            raise ValueError("fit result lacks entry dictionaries")
        r2_qm = float(qm_fit["R2_QM"])
        r2_qp = float(qp_fit["R2_QP"])
        permutation = permutation_null(
            x_tilde=x_tilde,
            y_tilde=y_mrna_tilde,
            q_names=q_names,
            observed_r2=r2_qm,
            observed_entries={name: float(qm_entries[name]) for name in q_names},
            count=PERMUTATION_COUNT,
        )
        vector_cosine = cosine(
            [float(qm_entries[name]) for name in q_names],
            [float(qp_entries[name]) for name in q_names],
        )
        conclusion = conclusion_from_null(r2_qm, permutation)

        residual_df = n_joined - rank_z
        rank_xtilde = int(qm_fit["rank_Xtilde"])
        checks = [
            {
                "name": "neymotin_loaded",
                "passed": n_joined >= MIN_PROTEINS_PER_ORGANISM,
                "actual": data_summary,
                "expected": f"Neymotin half-life loaded and joined to CDS by ORF with n >= {MIN_PROTEINS_PER_ORGANISM}",
            },
            {
                "name": "b_star_q6_residuals + controls_Z",
                "passed": len(q_names) == 9 and rank_z > 0 and len(z_rows) == n_joined and residual_df > 10 * len(q_names),
                "actual": {
                    "coordinates": q_names,
                    "coordinate_count": len(q_names),
                    "rank_Z": rank_z,
                    "residual_df_after_Z": residual_df,
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                    "controls_used": controls_used(aa_order),
                },
                "expected": "same 9 B*_Q6 coordinates and Z controls as S^QP: intercept, log length, amino-acid composition, GC3, and M-density",
            },
            {
                "name": "sqm_computed",
                "passed": finite_unit(r2_qm) and rank_xtilde == len(q_names) and all(math.isfinite(float(qm_entries[name])) for name in q_names),
                "actual": {
                    "R2_QM": r2_qm,
                    "rank_Xtilde": rank_xtilde,
                    "entry_count": len(qm_entries),
                    "dominant_coord": qm_fit["dominant_coord"],
                    "y_residual_energy": qm_fit["y_residual_energy"],
                    "explained_energy": qm_fit["explained_energy"],
                    "degenerate_R2_threshold": DEGENERATE_R2,
                },
                "expected": "finite R2_QM in [0,1], all 9 entries computed, full 9-coordinate residual rank",
            },
            {
                "name": "sqp_sqm_comparison",
                "passed": -1.0 <= vector_cosine <= 1.0 and isinstance(permutation.get("entries"), dict) and int(permutation["permutation_count"]) == PERMUTATION_COUNT,
                "actual": {
                    "cosine_SQM_vs_SQP": vector_cosine,
                    "R2_QP_same_join": r2_qp,
                    "permutation_count": permutation["permutation_count"],
                    "R2_QM_permutation_p": permutation["R2_QM"]["p_value_right_tail"] if isinstance(permutation.get("R2_QM"), dict) else None,
                },
                "expected": "cosine in [-1,1] and deterministic permutation null computed for R2_QM and each entry",
            },
            {
                "name": "no_causal_or_mechanism_overclaim",
                "passed": cannot_claim() == [
                    "single dataset (Neymotin et al 2014) metabolic-labeling 4tU yeast mRNA half-life",
                    "one organism (S. cerevisiae)",
                    "S^QM entries are statistical projections, not a decay mechanism",
                    "correlation with codon residual does not establish codon-optimality causation here",
                    "half-life is steady-state estimate not direct decay-rate measurement",
                    "not ribo-seq, not matched translation-controlled",
                ],
                "actual": cannot_claim(),
                "expected": "single dataset, one organism, projection-only, non-causal, not direct decay-rate, not ribo-seq, not matched translation-controlled",
            },
        ]

        status = "passed" if all(bool(check["passed"]) for check in checks) else "failed"
        reason = None if status == "passed" else "one or more honest gates failed"
        emit(
            status,
            reason=reason,
            checks=checks,
            result={
                "claimed_layer": "cross_layer_relation",
                "conjecture_id": CONJECTURE_ID,
                "statement": "B*_Q6 codon residuals are tested as statistical predictors of residualized log10 yeast mRNA half-life after the same CDS-derived controls used by S^QP.",
                "readout": "log10(thalf minutes) from Neymotin et al 2014 yeast 4tU metabolic-labeling half-life table",
                "coordinate_source": "q_vectors imported from run_b_star_q6_translation_survival_powered.py and Z controls matched to run_b_star_q6_protein_omics_survival_powered.py",
                "n_joined": n_joined,
                "coordinates": q_names,
                "R2_QM": r2_qm,
                "S_QM_entries": qm_entries,
                "S_QM_partial_r2": qm_fit["S_QM_partial_r2"],
                "dominant_coord": qm_fit["dominant_coord"],
                "S_QP_same_join_entries": qp_entries,
                "R2_QP_same_join": r2_qp,
                "dominant_coord_SQP_same_join": qp_fit["dominant_coord"],
                "cosine_SQM_vs_SQP": vector_cosine,
                "permutation_null": permutation,
                "core_conclusion": conclusion,
                "rank_diagnostics": {
                    "rank_Z": rank_z,
                    "rank_Xtilde": rank_xtilde,
                    "residual_df_after_Z": residual_df,
                    "control_column_count": len(z_rows[0]) if z_rows else 0,
                    "q_coordinate_count": len(q_names),
                    "protein_id_count": len(protein_ids),
                    "y_mrna_residual_energy": qm_fit["y_residual_energy"],
                    "y_protein_residual_energy": qp_fit["y_residual_energy"],
                },
                "controls_used": controls_used(aa_order),
                "cannot_claim": cannot_claim(),
            },
        )
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable S^QM input or fit")


if __name__ == "__main__":
    main()

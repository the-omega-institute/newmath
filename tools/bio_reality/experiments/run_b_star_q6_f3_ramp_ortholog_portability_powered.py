#!/usr/bin/env python3
"""5'-ramp f3 portability test across OrthoDB yeast/E. coli orthogroups.

This is an observational cross-domain portability audit.  It does not claim
causality, and with two species the orthogroup fixed-effect design has low
power and is sensitive to cross-domain orthology coverage.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from typing import Any


EXPERIMENT_ID = "b_star_q6_f3_ramp_ortholog_portability_powered"
CLAIM_ID = "h3.cross_layer_relation.f3_ramp_ortholog_portability.b_star_q6_powered"

WORK_DIR = pathlib.Path("/tmp/routeZ2-exp")
OUT_DIR = WORK_DIR / "out"
ORTHOTABLE_PATH = OUT_DIR / "orthotable.json"
DATA_DIR = pathlib.Path("/Users/lexa/Desktop/lexa/omega/newmath/tools/bio_reality/data")

YEAST = "saccharomyces_cerevisiae"
ECOLI = "escherichia_coli_k12_mg1655"
YEAST_TAXID = "4932"
ECOLI_TAXIDS = ["511145", "83333"]
ECOLI_ORTHODB_TAXID = "83333"
SPECIES = [YEAST, ECOLI]

MIN_1TO1_ORTHOGROUPS = 120
MIN_JOINED_ORTHOGROUPS = 120
MAX_ORTHODB_REQUESTS = 600
MAX_FETCH_SECONDS = 600.0
SCRIPT_WALL_SECONDS = 720.0
REQUEST_TIMEOUT = 8.0
RAMP_CODONS = 50
ALPHA = 0.05
EPS = 1e-12
SEED = f"sha256:{hashlib.sha256(EXPERIMENT_ID.encode('utf-8')).hexdigest()}"

STOP_CODONS = {"UAA", "UAG", "UGA"}
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


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def finite_numeric(value: object) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value))


def numeric(value: object, field: str) -> float:
    if not finite_numeric(value):
        raise ValueError(f"{field} must be finite numeric")
    return float(value)


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def standard_code() -> dict[str, str]:
    raw = load_json(DATA_DIR / "ncbi_genetic_codes.json")
    if not isinstance(raw, dict):
        raise ValueError("ncbi_genetic_codes payload is not an object")
    codon_order = raw.get("codon_order")
    tables = raw.get("tables")
    if not isinstance(codon_order, list) or not isinstance(tables, list):
        raise ValueError("ncbi_genetic_codes payload is malformed")
    table = next((item for item in tables if isinstance(item, dict) and item.get("table_id") == 1), None)
    if not isinstance(table, dict) or not isinstance(table.get("aa"), str):
        raise ValueError("standard genetic-code table missing")
    aa = str(table["aa"])
    if len(codon_order) != len(aa):
        raise ValueError("codon_order and aa string length mismatch")
    return {dna_to_rna(str(codon)): aa[index] for index, codon in enumerate(codon_order)}


def sense_codons(code: dict[str, str]) -> list[str]:
    return sorted(codon for codon, aa in code.items() if aa != "*")


def standard_amino_acids(code: dict[str, str], codons: list[str]) -> list[str]:
    aas = sorted({code[codon] for codon in codons})
    if len(aas) != 20:
        raise ValueError(f"expected 20 amino acids, got {len(aas)}")
    return aas


def fibers_for(code: dict[str, str], codons: list[str]) -> dict[str, list[str]]:
    fibers: dict[str, list[str]] = {}
    for codon in codons:
        fibers.setdefault(code[codon], []).append(codon)
    return fibers


def project_syn(vector: dict[str, float], fibers: dict[str, list[str]]) -> dict[str, float]:
    out = dict(vector)
    for fiber in fibers.values():
        center = sum(vector[codon] for codon in fiber) / len(fiber)
        for codon in fiber:
            out[codon] = vector[codon] - center
    return out


def f3_projected(codons: list[str], fibers: dict[str, list[str]]) -> dict[str, float]:
    q = {codon: 0.0 for codon in codons}
    for family in Q9_FAMILIES:
        q[family[0]] += 1.0
        q[family[-1]] -= 1.0
    return project_syn(q, fibers)


def codon_counts_rna(record: dict[str, object], codons: list[str], organism: str, row_index: int) -> dict[str, int]:
    raw = record.get("codon_counts")
    if not isinstance(raw, dict):
        raise ValueError(f"{organism}.joined[{row_index}].codon_counts must be object")
    converted = {codon: 0 for codon in codons}
    for raw_codon, raw_count in raw.items():
        codon = dna_to_rna(str(raw_codon))
        if codon in converted:
            value = numeric(raw_count, f"{organism}.joined[{row_index}].codon_counts.{raw_codon}")
            if value < 0.0 or int(value) != value:
                raise ValueError("codon count must be nonnegative integer")
            converted[codon] += int(value)
    return converted


def parse_gene_from_header(header: str) -> str | None:
    match = re.search(r"\[gene=([^\]]+)\]", header)
    return match.group(1) if match else None


def parse_ncbi_protein_id(header: str) -> str | None:
    match = re.search(r"\[protein_id=([^\]]+)\]", header)
    return match.group(1) if match else None


def canonical_key(organism: str, item: dict[str, object]) -> str | None:
    match_id = item.get("cds_match_id")
    if organism == YEAST:
        if isinstance(match_id, str) and match_id:
            return match_id.upper()
        protein_id = item.get("protein_id")
        if isinstance(protein_id, str) and "." in protein_id:
            return protein_id.split(".", 1)[1].upper()
        return None
    if organism == ECOLI:
        if isinstance(match_id, str) and match_id.startswith("b"):
            return match_id
        protein_id = item.get("protein_id")
        if isinstance(protein_id, str) and "." in protein_id:
            suffix = protein_id.split(".", 1)[1]
            return suffix if suffix.startswith("b") else None
        return None
    raise ValueError(f"unsupported organism {organism}")


def ordered_cds_index(organism: str) -> dict[str, list[str]]:
    payload = load_json(DATA_DIR / f"cds_ordered_sequences_{organism}.json")
    if not isinstance(payload, dict) or not isinstance(payload.get("cds"), list):
        raise ValueError(f"{organism} ordered CDS payload malformed")
    out: dict[str, list[str]] = {}
    for item in payload["cds"]:
        if not isinstance(item, dict):
            continue
        gene_id = item.get("gene_id")
        codons = item.get("codons")
        if isinstance(gene_id, str) and isinstance(codons, list):
            out[gene_id.upper() if organism == YEAST else gene_id] = [dna_to_rna(str(c)) for c in codons]
    return out


def te_index(organism: str) -> tuple[dict[str, dict[str, float]], dict[str, dict[str, float]], dict[str, object]]:
    payload = load_json(DATA_DIR / f"ribosome_te_{organism}.json")
    if not isinstance(payload, dict) or not isinstance(payload.get("genes"), list):
        raise ValueError(f"{organism} TE payload malformed")
    by_protein: dict[str, dict[str, float]] = {}
    by_gene: dict[str, dict[str, float]] = {}
    skipped = {"non_object": 0, "missing_id": 0, "nonpositive": 0, "duplicate_protein": 0}
    for row_index, item in enumerate(payload["genes"]):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        gene_key = item.get("gene_key")
        if not isinstance(protein_id, str) or not isinstance(gene_key, str):
            skipped["missing_id"] += 1
            continue
        te = numeric(item.get("te"), f"{organism}.TE[{row_index}].te")
        mrna = numeric(item.get("mrna"), f"{organism}.TE[{row_index}].mrna")
        footprint = numeric(item.get("footprint"), f"{organism}.TE[{row_index}].footprint")
        if te <= 0.0 or mrna <= 0.0 or footprint <= 0.0:
            skipped["nonpositive"] += 1
            continue
        record = {"te": te, "mrna": mrna, "footprint": footprint}
        if protein_id in by_protein:
            skipped["duplicate_protein"] += 1
        else:
            by_protein[protein_id] = record
        by_gene[gene_key.upper() if organism == YEAST else gene_key] = record
    return by_protein, by_gene, {"n_valid_by_protein": len(by_protein), "n_valid_by_gene": len(by_gene), "skipped": skipped}


def structural_index(organism: str) -> tuple[dict[str, float], dict[str, object]]:
    payload = load_json(DATA_DIR / f"structural_order_{organism}.json")
    if not isinstance(payload, dict) or not isinstance(payload.get("proteins"), list):
        raise ValueError(f"{organism} structural payload malformed")
    by_protein: dict[str, float] = {}
    skipped = {"non_object": 0, "missing_protein_id": 0, "invalid": 0, "duplicate": 0}
    for row_index, item in enumerate(payload["proteins"]):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        value = numeric(item.get("structural_order"), f"{organism}.structural[{row_index}]")
        if value < 0.0 or value > 100.0:
            skipped["invalid"] += 1
            continue
        if protein_id in by_protein:
            skipped["duplicate"] += 1
        else:
            by_protein[protein_id] = value
    return by_protein, {"n_valid": len(by_protein), "skipped": skipped}


def yeast_half_life_index() -> tuple[dict[str, float], dict[str, object]]:
    payload = load_json(DATA_DIR / "mrna_half_life_saccharomyces_cerevisiae_neymotin.json")
    if not isinstance(payload, dict) or not isinstance(payload.get("records"), list):
        raise ValueError("yeast half-life payload malformed")
    out: dict[str, float] = {}
    skipped = {"non_object": 0, "missing_syst": 0, "nonpositive": 0}
    for row_index, item in enumerate(payload["records"]):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        syst = item.get("Syst")
        if not isinstance(syst, str) or not syst:
            skipped["missing_syst"] += 1
            continue
        value = numeric(item.get("thalf"), f"yeast.halflife[{row_index}]")
        if value <= 0.0:
            skipped["nonpositive"] += 1
            continue
        out[syst.upper()] = math.log10(value)
    return out, {"n_valid": len(out), "skipped": skipped, "transform": "log10(thalf_minutes)"}


def ecoli_half_life_index() -> tuple[dict[str, float], dict[str, object]]:
    payload = load_json(DATA_DIR / "mrna_half_life_escherichia_coli_esquerre.json")
    if not isinstance(payload, dict) or not isinstance(payload.get("records"), list):
        raise ValueError("E.coli half-life payload malformed")
    target_growth = str(payload.get("primary_readout_growth_rate_h_inv") or "0.40")
    out: dict[str, float] = {}
    skipped = {"non_object": 0, "missing_gene": 0, "missing_growth_rate": 0, "nonpositive": 0}
    for row_index, item in enumerate(payload["records"]):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        gene_id = item.get("GeneId")
        values = item.get("half_life_minutes_by_growth_rate_h_inv")
        if not isinstance(gene_id, str) or not gene_id:
            skipped["missing_gene"] += 1
            continue
        if not isinstance(values, dict) or target_growth not in values:
            skipped["missing_growth_rate"] += 1
            continue
        value = numeric(values[target_growth], f"ecoli.halflife[{row_index}]")
        if value <= 0.0:
            skipped["nonpositive"] += 1
            continue
        out[gene_id] = math.log10(value)
    return out, {"n_valid": len(out), "growth_rate_h_inv": target_growth, "skipped": skipped, "transform": "log10(thalf_minutes)"}


def localization_index() -> tuple[dict[str, float], dict[str, object]]:
    payload = load_json(DATA_DIR / "subcellular_localization_saccharomyces_cerevisiae.json")
    proteins = payload.get("proteins") if isinstance(payload, dict) else None
    if not isinstance(proteins, dict):
        raise ValueError("yeast localization payload malformed")
    out: dict[str, float] = {}
    skipped = {"non_object": 0, "missing_categories": 0}
    for protein_id, item in proteins.items():
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        cats = item.get("categories")
        if not isinstance(cats, list) or not cats:
            skipped["missing_categories"] += 1
            continue
        # Coarse numeric negative control: membrane/secretory compartment flag.
        labels = {str(cat) for cat in cats}
        out[str(protein_id)] = 1.0 if labels & {"Membrane", "Cell_membrane", "Endoplasmic_reticulum", "Golgi", "Vacuole"} else 0.0
    return out, {"n_valid": len(out), "readout": "yeast-only coarse membrane/secretory localization flag", "skipped": skipped}


def reverse_complement_rna(seq: str) -> str:
    comp = {"A": "U", "U": "A", "C": "G", "G": "C", "T": "A"}
    return "".join(comp.get(base, "N") for base in reversed(seq.upper().replace("T", "U")))


def anticodon_copy_index(organism: str) -> tuple[dict[str, float], dict[str, object]]:
    trna_name = "gtrnadb_trna_all_copy_saccharomyces_cerevisiae" if organism == YEAST else "gtrnadb_trna_all_copy_escherichia_coli"
    payload = load_json(DATA_DIR / f"{trna_name}.json")
    raw = payload.get("trna_all_copies") if isinstance(payload, dict) else None
    if not isinstance(raw, dict):
        raise ValueError(f"{organism} GtRNAdb tRNA copy payload malformed")
    anticodon_copies = {dna_to_rna(str(k)): float(v) for k, v in raw.items() if finite_numeric(v) and float(v) > 0.0}
    codon_copy: dict[str, float] = {}
    for anticodon, count in anticodon_copies.items():
        codon = reverse_complement_rna(anticodon)
        codon_copy[codon] = codon_copy.get(codon, 0.0) + count
    return codon_copy, {
        "n_anticodons": len(anticodon_copies),
        "n_exact_complement_codons": len(codon_copy),
        "definition": "log1p exact reverse-complement anticodon copy proxy; no wobble constants imported",
    }


def ramp_counts(codon_sequence: list[str], codons: list[str]) -> dict[str, int]:
    counts = {codon: 0 for codon in codons}
    seen = 0
    for codon in codon_sequence:
        rna = dna_to_rna(codon)
        if rna in STOP_CODONS:
            continue
        if rna in counts:
            counts[rna] += 1
            seen += 1
        if seen >= RAMP_CODONS:
            break
    return counts


def row_controls(
    counts: dict[str, int],
    ramp: dict[str, int],
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    cds_len_nt: float,
    trna_proxy: float,
) -> list[float]:
    total = sum(counts.values())
    ramp_total = sum(ramp.values())
    if total <= 0 or ramp_total <= 0:
        raise ValueError("empty codon counts")
    aa_counts = {aa: 0 for aa in aa_order}
    for codon in codons:
        aa_counts[code[codon]] += counts[codon]
    aa_total = sum(aa_counts.values())
    if aa_total <= 0:
        raise ValueError("empty amino-acid counts")
    gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
    ramp_gc3 = sum(ramp[codon] for codon in codons if codon[2] in {"G", "C"}) / ramp_total
    return [1.0, math.log(cds_len_nt), math.log(total), gc3, ramp_gc3, trna_proxy] + [aa_counts[aa] / aa_total for aa in aa_order]


def build_species_features(
    organism: str,
    code: dict[str, str],
    codons: list[str],
    aa_order: list[str],
    f3: dict[str, float],
) -> tuple[dict[str, dict[str, object]], dict[str, object]]:
    cds_payload = load_json(DATA_DIR / f"cds_codon_abundance_{organism}.json")
    if not isinstance(cds_payload, dict) or not isinstance(cds_payload.get("joined"), list):
        raise ValueError(f"{organism} CDS abundance payload malformed")
    ordered = ordered_cds_index(organism)
    te_by_protein, te_by_gene, te_summary = te_index(organism)
    structural_by_protein, structural_summary = structural_index(organism)
    half_life_by_gene, half_life_summary = yeast_half_life_index() if organism == YEAST else ecoli_half_life_index()
    loc_by_protein: dict[str, float] = {}
    loc_summary: dict[str, object] = {"available": False, "reason": "E.coli localization unavailable locally"} if organism == ECOLI else {}
    if organism == YEAST:
        loc_by_protein, loc_summary = localization_index()
        loc_summary = {"available": True, **loc_summary}
    codon_trna_copy, trna_summary = anticodon_copy_index(organism)

    f3_norm = math.sqrt(sum(f3[codon] * f3[codon] for codon in codons))
    if f3_norm <= EPS:
        raise ValueError("projected f3 vector has zero norm")

    rows: dict[str, dict[str, object]] = {}
    raw_x: list[float] = []
    controls: list[list[float]] = []
    skipped = {
        "non_object": 0,
        "missing_key": 0,
        "duplicate_key": 0,
        "missing_ordered_cds": 0,
        "short_or_empty_ramp": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_counts": 0,
    }
    for row_index, item in enumerate(cds_payload["joined"]):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        key = canonical_key(organism, item)
        if key is None:
            skipped["missing_key"] += 1
            continue
        if key in rows:
            skipped["duplicate_key"] += 1
            continue
        codon_sequence = ordered.get(key.upper() if organism == YEAST else key)
        if codon_sequence is None:
            skipped["missing_ordered_cds"] += 1
            continue
        abundance = numeric(item.get("abundance_ppm"), f"{organism}.joined[{row_index}].abundance_ppm")
        if abundance <= 0.0:
            skipped["nonpositive_abundance"] += 1
            continue
        cds_len_nt = numeric(item.get("cds_len_nt"), f"{organism}.joined[{row_index}].cds_len_nt")
        if cds_len_nt <= 0.0:
            skipped["invalid_length"] += 1
            continue
        counts = codon_counts_rna(item, codons, organism, row_index)
        total = sum(counts.values())
        ramp = ramp_counts(codon_sequence, codons)
        ramp_total = sum(ramp.values())
        if total <= 0:
            skipped["empty_counts"] += 1
            continue
        if ramp_total <= 0:
            skipped["short_or_empty_ramp"] += 1
            continue
        ramp_freq = {codon: ramp[codon] / ramp_total for codon in codons}
        x = sum(ramp_freq[codon] * f3[codon] for codon in codons) / f3_norm
        trna_proxy = sum((counts[codon] / total) * math.log1p(codon_trna_copy.get(codon, 0.0)) for codon in codons)
        z = row_controls(counts, ramp, codons, code, aa_order, cds_len_nt, trna_proxy)

        protein_id = item.get("protein_id")
        if not isinstance(protein_id, str):
            skipped["missing_key"] += 1
            continue
        gene_symbol = parse_gene_from_header(str(item.get("cds_header", ""))) or str(item.get("paxdb_gene_name") or "")
        ncbi_protein_id = parse_ncbi_protein_id(str(item.get("cds_header", "")))
        te_record = te_by_protein.get(protein_id) or te_by_gene.get(key.upper() if organism == YEAST else key)
        y: dict[str, float] = {"abundance": math.log10(abundance)}
        if te_record is not None:
            y["TE"] = math.log10(te_record["te"])
        if protein_id in structural_by_protein:
            y["structural_order"] = structural_by_protein[protein_id]
        if key in half_life_by_gene:
            y["half_life"] = half_life_by_gene[key]
        if protein_id in loc_by_protein:
            y["localization"] = loc_by_protein[protein_id]

        aliases = sorted(
            {
                key,
                key.upper(),
                protein_id,
                protein_id.split(".", 1)[-1],
                gene_symbol,
                gene_symbol.upper(),
                str(item.get("paxdb_gene_name") or ""),
                str(item.get("paxdb_gene_name") or "").upper(),
                ncbi_protein_id or "",
            }
            - {""}
        )
        rows[key] = {
            "organism": organism,
            "key": key,
            "protein_id": protein_id,
            "gene_symbol": gene_symbol,
            "aliases": aliases,
            "f3_ramp_raw": x,
            "controls": z,
            "y": y,
        }
        raw_x.append(x)
        controls.append(z)

    x_resid, rank = residualize_vector(raw_x, controls)
    for row, residual in zip(rows.values(), x_resid):
        row["f3_ramp_residual"] = residual

    summary = {
        "n_cds_joined_reported": cds_payload.get("n_joined"),
        "n_feature_rows": len(rows),
        "ramp_codons": RAMP_CODONS,
        "residual_controls": ["intercept", "log_cds_len_nt", "log_sense_codons", "GC3", "ramp_GC3", "exact_complement_tRNA_proxy", "20_aa_composition"],
        "rank_f3_residual_controls": rank,
        "te_summary": te_summary,
        "structural_summary": structural_summary,
        "half_life_summary": half_life_summary,
        "localization_summary": loc_summary,
        "trna_summary": trna_summary,
        "skipped": skipped,
    }
    return rows, summary


def transpose(matrix: list[list[float]]) -> list[list[float]]:
    if not matrix:
        return []
    return [[row[index] for row in matrix] for index in range(len(matrix[0]))]


def dot(left: list[float], right: list[float]) -> float:
    return sum(left[index] * right[index] for index in range(len(left)))


def norm(vector: list[float]) -> float:
    return math.sqrt(dot(vector, vector))


def orthonormal_basis_from_columns(matrix: list[list[float]], tol: float = 1e-10) -> list[list[float]]:
    basis: list[list[float]] = []
    if not matrix:
        return basis
    for column in transpose(matrix):
        residual = list(column)
        for q in basis:
            coeff = dot(residual, q)
            residual = [residual[index] - coeff * q[index] for index in range(len(residual))]
        nrm = norm(residual)
        if nrm > tol * max(1.0, norm(column)):
            basis.append([value / nrm for value in residual])
    return basis


def residualize_vector(values: list[float], controls: list[list[float]]) -> tuple[list[float], int]:
    if len(values) != len(controls):
        raise ValueError("values/control length mismatch")
    basis = orthonormal_basis_from_columns(controls)
    out = list(values)
    for q in basis:
        coeff = dot(out, q)
        out = [out[index] - coeff * q[index] for index in range(len(out))]
    return out, len(basis)


def solve_linear_system(matrix: list[list[float]], rhs: list[float]) -> tuple[list[float], int]:
    n = len(rhs)
    if n == 0:
        return [], 0
    trace = sum(abs(matrix[i][i]) for i in range(n))
    base_ridge = max(EPS, trace * 1e-12 / max(1, n))
    for ridge_step in range(8):
        ridge = 0.0 if ridge_step == 0 else base_ridge * (100.0 ** (ridge_step - 1))
        aug = [[matrix[i][j] + (ridge if i == j else 0.0) for j in range(n)] + [rhs[i]] for i in range(n)]
        ok = True
        for col in range(n):
            pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
            if abs(aug[pivot][col]) <= max(EPS, trace * 1e-14):
                ok = False
                break
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
        if ok:
            return [aug[i][n] for i in range(n)], ridge_step
    return [0.0 for _ in range(n)], 8


def normal_cdf(value: float) -> float:
    return 0.5 * (1.0 + math.erf(value / math.sqrt(2.0)))


def ols_fit(x_rows: list[list[float]], y: list[float]) -> dict[str, object]:
    n = len(y)
    p = len(x_rows[0]) if x_rows else 0
    if n <= p or p == 0:
        return {"status": "needs_data", "reason": f"not enough degrees of freedom n={n}, p={p}", "n": n, "p": p}
    xtx = [[0.0 for _ in range(p)] for _ in range(p)]
    xty = [0.0 for _ in range(p)]
    for row, target in zip(x_rows, y):
        for i in range(p):
            xty[i] += row[i] * target
            for j in range(p):
                xtx[i][j] += row[i] * row[j]
    beta, ridge_step = solve_linear_system(xtx, xty)
    residuals = [target - dot(row, beta) for row, target in zip(x_rows, y)]
    sse = sum(value * value for value in residuals)
    y_mean = sum(y) / n
    sst = sum((value - y_mean) ** 2 for value in y)
    df = n - p
    sigma2 = sse / df if df > 0 else 0.0
    inv = invert_symmetric(xtx)
    se = [math.sqrt(max(0.0, sigma2 * inv[i][i])) if inv else None for i in range(p)]
    t_values = [None if se[i] is None or se[i] <= EPS else beta[i] / se[i] for i in range(p)]
    p_values = [None if t is None else 2.0 * (1.0 - normal_cdf(abs(t))) for t in t_values]
    return {
        "status": "computed",
        "n": n,
        "p": p,
        "df": df,
        "beta": beta,
        "se": se,
        "t": t_values,
        "p_value_normal_approx": p_values,
        "r2": None if sst <= EPS else 1.0 - sse / sst,
        "ridge_step": ridge_step,
    }


def invert_symmetric(matrix: list[list[float]]) -> list[list[float]] | None:
    n = len(matrix)
    if n == 0:
        return []
    trace = sum(abs(matrix[i][i]) for i in range(n))
    ridge = max(EPS, trace * 1e-12 / max(1, n))
    for attempt in range(8):
        add = 0.0 if attempt == 0 else ridge * (100.0 ** (attempt - 1))
        aug: list[list[float]] = []
        for row in range(n):
            left = [matrix[row][col] + (add if row == col else 0.0) for col in range(n)]
            right = [0.0 for _ in range(n)]
            right[row] = 1.0
            aug.append(left + right)
        ok = True
        for col in range(n):
            pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
            if abs(aug[pivot][col]) <= max(EPS, trace * 1e-14):
                ok = False
                break
            if pivot != col:
                aug[col], aug[pivot] = aug[pivot], aug[col]
            scale = aug[col][col]
            for j in range(2 * n):
                aug[col][j] /= scale
            for row in range(n):
                if row == col:
                    continue
                factor = aug[row][col]
                if factor == 0.0:
                    continue
                for j in range(2 * n):
                    aug[row][j] -= factor * aug[col][j]
        if ok:
            return [row[n:] for row in aug]
    return None


class OrthoDBClient:
    def __init__(self) -> None:
        self.request_count = 0
        self.started = time.monotonic()
        self.failures: list[dict[str, object]] = []
        self.rate_limited = False
        self.stopped_reason: str | None = None

    def get(self, endpoint: str, params: dict[str, str]) -> dict[str, object] | None:
        if self.request_count >= MAX_ORTHODB_REQUESTS:
            self.stopped_reason = "request_limit"
            return None
        if time.monotonic() - self.started > MAX_FETCH_SECONDS:
            self.stopped_reason = "fetch_wall_time_limit"
            return None
        url = "https://data.orthodb.org/current/" + endpoint + "?" + urllib.parse.urlencode(params)
        self.request_count += 1
        for attempt in range(2):
            try:
                req = urllib.request.Request(url, headers={"User-Agent": "bio_reality_codex_ortholog_portability/1.0"})
                with urllib.request.urlopen(req, timeout=REQUEST_TIMEOUT) as response:
                    raw = response.read()
                payload = json.loads(raw.decode("utf-8"))
                if not isinstance(payload, dict):
                    self.failures.append({"url": url, "error": "non_object_payload"})
                    return None
                return payload
            except urllib.error.HTTPError as exc:
                if exc.code in {429, 500, 502, 503, 504}:
                    if exc.code == 429:
                        self.rate_limited = True
                    time.sleep(0.35 * (attempt + 1))
                    continue
                self.failures.append({"url": url, "error": f"HTTPError:{exc.code}"})
                return None
            except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as exc:
                time.sleep(0.35 * (attempt + 1))
                if attempt == 1:
                    self.failures.append({"url": url, "error": type(exc).__name__})
                    return None
        return None


def candidate_terms(rows: dict[str, dict[str, object]], organism: str, limit: int) -> list[tuple[str, str]]:
    items = list(rows.values())
    # Deterministic order: high local data coverage first, then stable hash to avoid abundance-only ranking.
    def score(row: dict[str, object]) -> tuple[int, int]:
        y = row.get("y")
        coverage = len(y) if isinstance(y, dict) else 0
        material = f"{SEED}|orthodb_candidate|{organism}|{row.get('key')}"
        h = int.from_bytes(hashlib.sha256(material.encode("utf-8")).digest()[:8], "big")
        return (-coverage, h)

    out: list[tuple[str, str]] = []
    seen: set[str] = set()
    for row in sorted(items, key=score):
        aliases = row.get("aliases")
        if not isinstance(aliases, list):
            continue
        for alias in aliases:
            text = str(alias)
            if organism == ECOLI and text.startswith("511145."):
                continue
            if text and text not in seen:
                out.append((str(row["key"]), text))
                seen.add(text)
                break
        if len(out) >= limit:
            break
    return out


def extract_og_ids(search_payload: dict[str, object]) -> list[str]:
    ids: list[str] = []
    data = search_payload.get("data")
    if isinstance(data, list):
        ids.extend(str(item) for item in data if isinstance(item, str))
    bigdata = search_payload.get("bigdata")
    if isinstance(bigdata, list):
        for item in bigdata:
            if isinstance(item, dict) and isinstance(item.get("id"), str):
                ids.append(str(item["id"]))
    out: list[str] = []
    seen: set[str] = set()
    for og in ids:
        if og not in seen:
            seen.add(og)
            out.append(og)
    return out


def orthodb_member_keys(payload: dict[str, object]) -> tuple[list[str], list[str], dict[str, object]]:
    data = payload.get("data")
    yeast_hits: list[str] = []
    ecoli_hits: list[str] = []
    organism_counts: dict[str, int] = {}
    if not isinstance(data, list):
        return yeast_hits, ecoli_hits, {"n_organism_blocks": 0, "organism_counts": organism_counts}
    for block in data:
        if not isinstance(block, dict):
            continue
        organism = block.get("organism")
        org_id = ""
        org_name = ""
        if isinstance(organism, dict):
            org_id = str(organism.get("id") or "")
            org_name = str(organism.get("name") or "")
        genes = block.get("genes")
        if not isinstance(genes, list):
            continue
        organism_counts[org_id or org_name] = len(genes)
        target = None
        if org_id.startswith("4932_") or org_name == "Saccharomyces cerevisiae":
            target = yeast_hits
        elif org_id.startswith("83333_") or org_id.startswith("511145_") or "Escherichia coli K-12" in org_name:
            target = ecoli_hits
        if target is None:
            continue
        for gene in genes:
            if not isinstance(gene, dict):
                continue
            gene_id = gene.get("gene_id")
            if isinstance(gene_id, dict):
                gid = gene_id.get("id")
                if isinstance(gid, str):
                    target.append(gid.upper() if target is yeast_hits else gid)
            desc = gene.get("description")
            if isinstance(desc, str):
                target.append(desc.upper() if target is yeast_hits else desc)
            coords = gene.get("genomic_coordinates")
            if isinstance(coords, dict):
                protein_id = coords.get("protein_id")
                if isinstance(protein_id, str):
                    target.append(protein_id)
    return yeast_hits, ecoli_hits, {"n_organism_blocks": len(data), "organism_counts": organism_counts}


def match_member(member_aliases: list[str], rows: dict[str, dict[str, object]], organism: str) -> str | None:
    alias_to_key: dict[str, str] = {}
    for key, row in rows.items():
        aliases = row.get("aliases")
        if isinstance(aliases, list):
            for alias in aliases:
                alias_to_key[str(alias).upper() if organism == YEAST else str(alias)] = key
                alias_to_key[str(alias).lower()] = key
    for alias in member_aliases:
        candidates = [alias, alias.upper(), alias.lower()]
        for cand in candidates:
            if cand in alias_to_key:
                return alias_to_key[cand]
    return None


def build_orthotable(
    yeast_rows: dict[str, dict[str, object]],
    ecoli_rows: dict[str, dict[str, object]],
) -> tuple[list[dict[str, object]], dict[str, object]]:
    client = OrthoDBClient()
    # One search plus one orthologs request per candidate is the dominant cost.
    max_candidates = min(260, (MAX_ORTHODB_REQUESTS - 20) // 2)
    candidates = candidate_terms(yeast_rows, YEAST, max_candidates)
    orthotable: list[dict[str, object]] = []
    seen_og: set[str] = set()
    seen_pair: set[tuple[str, str]] = set()
    stats: dict[str, object] = {
        "candidate_species": YEAST,
        "candidate_count": len(candidates),
        "search_with_species": True,
        "requested_level_policy": "first try level=1 cellular/LUCA per task, then unlevelled OrthoDB REST search because current level=1 may return no cross-domain hits",
        "search_no_hit": 0,
        "search_level1_no_hit": 0,
        "orthologs_no_data": 0,
        "og_seen": 0,
        "og_duplicate": 0,
        "not_1to1_local_exact": 0,
        "examples": [],
    }

    for source_key, term in candidates:
        if client.stopped_reason is not None or client.request_count >= MAX_ORTHODB_REQUESTS - 2:
            break
        level_payload = client.get("search", {"query": term, "species": YEAST_TAXID, "level": "1"})
        level_ids = extract_og_ids(level_payload) if isinstance(level_payload, dict) else []
        if not level_ids:
            stats["search_level1_no_hit"] = int(stats["search_level1_no_hit"]) + 1
        search_payload = level_payload if level_ids else client.get("search", {"query": term, "species": YEAST_TAXID})
        og_ids = extract_og_ids(search_payload) if isinstance(search_payload, dict) else []
        if not og_ids:
            stats["search_no_hit"] = int(stats["search_no_hit"]) + 1
            continue
        for og_id in og_ids[:3]:
            if client.stopped_reason is not None or client.request_count >= MAX_ORTHODB_REQUESTS:
                break
            if og_id in seen_og:
                stats["og_duplicate"] = int(stats["og_duplicate"]) + 1
                continue
            seen_og.add(og_id)
            stats["og_seen"] = int(stats["og_seen"]) + 1
            ortho_payload = client.get("orthologs", {"id": og_id, "species": f"{YEAST_TAXID},{ECOLI_ORTHODB_TAXID}"})
            if not isinstance(ortho_payload, dict) or not isinstance(ortho_payload.get("data"), list):
                stats["orthologs_no_data"] = int(stats["orthologs_no_data"]) + 1
                continue
            yeast_aliases, ecoli_aliases, member_summary = orthodb_member_keys(ortho_payload)
            yeast_key = match_member(yeast_aliases, yeast_rows, YEAST)
            ecoli_key = match_member(ecoli_aliases, ecoli_rows, ECOLI)
            pair = (yeast_key or "", ecoli_key or "")
            if yeast_key is None or ecoli_key is None or pair in seen_pair:
                stats["not_1to1_local_exact"] = int(stats["not_1to1_local_exact"]) + 1
                continue
            seen_pair.add(pair)
            orthotable.append(
                {
                    "orthogroup_id": og_id,
                    "yeast_gene": yeast_key,
                    "ecoli_gene": ecoli_key,
                    "source_query_key": source_key,
                    "source_query_term": term,
                    "member_summary": member_summary,
                }
            )
            examples = stats["examples"]
            if isinstance(examples, list) and len(examples) < 5:
                examples.append({"og": og_id, "yeast": yeast_key, "ecoli": ecoli_key, "term": term})
            break
        if len(orthotable) >= MIN_1TO1_ORTHOGROUPS:
            # Keep fetching a little beyond the gate would spend requests for marginal power;
            # stop once the fixed minimum is satisfied.
            break

    stats.update(
        {
            "request_count": client.request_count,
            "request_limit": MAX_ORTHODB_REQUESTS,
            "fetch_seconds": time.monotonic() - client.started,
            "rate_limited": client.rate_limited,
            "stopped_reason": client.stopped_reason,
            "failure_count": len(client.failures),
            "failure_examples": client.failures[:5],
            "n_1to1_orthogroups": len(orthotable),
        }
    )
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    ORTHOTABLE_PATH.write_text(
        json.dumps(
            {
                "experiment_id": EXPERIMENT_ID,
                "claim_id": CLAIM_ID,
                "seed": SEED,
                "built_at_unix": int(time.time()),
                "species": {
                    "yeast": {"organism": YEAST, "taxid": YEAST_TAXID},
                    "ecoli": {"organism": ECOLI, "taxid_used_for_orthodb": ECOLI_ORTHODB_TAXID, "local_taxid_aliases": ECOLI_TAXIDS},
                },
                "orthogroups": orthotable,
                "fetch_stats": stats,
            },
            sort_keys=False,
            indent=2,
        ),
        encoding="utf-8",
    )
    return orthotable, stats


def within_orthogroup_model(
    orthotable: list[dict[str, object]],
    yeast_rows: dict[str, dict[str, object]],
    ecoli_rows: dict[str, dict[str, object]],
    readout: str,
    include_controls: bool = True,
) -> dict[str, object]:
    pairs: list[dict[str, object]] = []
    for og in orthotable:
        y_key = og.get("yeast_gene")
        e_key = og.get("ecoli_gene")
        if not isinstance(y_key, str) or not isinstance(e_key, str):
            continue
        yr = yeast_rows.get(y_key)
        er = ecoli_rows.get(e_key)
        if yr is None or er is None:
            continue
        yy = yr.get("y")
        ey = er.get("y")
        if not isinstance(yy, dict) or not isinstance(ey, dict):
            continue
        if readout not in yy or readout not in ey:
            continue
        pairs.append({"og": og["orthogroup_id"], "yeast": yr, "ecoli": er, "y_yeast": float(yy[readout]), "y_ecoli": float(ey[readout])})

    if len(pairs) < MIN_JOINED_ORTHOGROUPS:
        return {"status": "needs_data", "readout": readout, "n_pairs": len(pairs), "reason": f"joined orthogroup/readout pairs below {MIN_JOINED_ORTHOGROUPS}"}

    x_rows: list[list[float]] = []
    y_vec: list[float] = []
    for pair in pairs:
        yr = pair["yeast"]
        er = pair["ecoli"]
        if not isinstance(yr, dict) or not isinstance(er, dict):
            continue
        x_y = float(yr["f3_ramp_residual"])
        x_e = float(er["f3_ramp_residual"])
        y_y = float(pair["y_yeast"])
        y_e = float(pair["y_ecoli"])
        dx = x_y - x_e
        dy = y_y - y_e
        # Two-species within-OG transform.  Species FE is a constant across
        # pair differences; intercept absorbs yeast-minus-E.coli mean.
        row = [1.0, dx]
        if include_controls:
            z_y = yr.get("controls")
            z_e = er.get("controls")
            if not isinstance(z_y, list) or not isinstance(z_e, list) or len(z_y) != len(z_e):
                continue
            # Drop duplicated intercept control; species intercept already present.
            row.extend(float(z_y[index]) - float(z_e[index]) for index in range(1, len(z_y)))
        x_rows.append(row)
        y_vec.append(dy)

    fit = ols_fit(x_rows, y_vec)
    if fit.get("status") != "computed":
        return {"status": "needs_data", "readout": readout, "n_pairs": len(pairs), "reason": fit.get("reason"), "fit": fit}
    beta = fit["beta"]
    p_value = fit["p_value_normal_approx"]
    se = fit["se"]
    t_values = fit["t"]
    return {
        "status": "computed",
        "readout": readout,
        "n_pairs": len(pairs),
        "n_model_rows": len(y_vec),
        "model": "two-species within-orthogroup difference OLS; intercept absorbs species FE, beta[1] is f3-ramp residual difference",
        "beta_f3_ramp": beta[1] if isinstance(beta, list) and len(beta) > 1 else None,
        "se_f3_ramp": se[1] if isinstance(se, list) and len(se) > 1 else None,
        "t_f3_ramp": t_values[1] if isinstance(t_values, list) and len(t_values) > 1 else None,
        "p_f3_ramp_normal_approx": p_value[1] if isinstance(p_value, list) and len(p_value) > 1 else None,
        "significant_alpha_0_05": isinstance(p_value, list) and len(p_value) > 1 and isinstance(p_value[1], float) and p_value[1] < ALPHA,
        "fit": {k: v for k, v in fit.items() if k not in {"beta", "se", "t", "p_value_normal_approx"}},
    }


def within_single_species_negative_control(
    orthotable: list[dict[str, object]],
    rows: dict[str, dict[str, object]],
    gene_field: str,
    readout: str,
) -> dict[str, object]:
    x: list[float] = []
    y: list[float] = []
    z: list[list[float]] = []
    for og in orthotable:
        key = og.get(gene_field)
        if not isinstance(key, str):
            continue
        row = rows.get(key)
        if row is None:
            continue
        yy = row.get("y")
        if not isinstance(yy, dict) or readout not in yy:
            continue
        controls = row.get("controls")
        if not isinstance(controls, list):
            continue
        x.append(float(row["f3_ramp_residual"]))
        y.append(float(yy[readout]))
        z.append([1.0] + [float(v) for v in controls[1:]])
    if len(y) < MIN_JOINED_ORTHOGROUPS:
        return {"status": "skipped", "readout": readout, "n": len(y), "reason": "single-species localization control below gate or unavailable"}
    x_resid, rank_x = residualize_vector(x, z)
    y_resid, rank_y = residualize_vector(y, z)
    fit = ols_fit([[1.0, value] for value in x_resid], y_resid)
    if fit.get("status") != "computed":
        return {"status": "needs_data", "readout": readout, "n": len(y), "reason": fit.get("reason")}
    beta = fit["beta"]
    p_value = fit["p_value_normal_approx"]
    return {
        "status": "computed",
        "readout": readout,
        "species": YEAST,
        "n": len(y),
        "model": "yeast-only residual OLS because E.coli localization is unavailable locally; not an orthogroup FE test",
        "beta_f3_ramp": beta[1] if isinstance(beta, list) and len(beta) > 1 else None,
        "p_f3_ramp_normal_approx": p_value[1] if isinstance(p_value, list) and len(p_value) > 1 else None,
        "significant_alpha_0_05": isinstance(p_value, list) and len(p_value) > 1 and isinstance(p_value[1], float) and p_value[1] < ALPHA,
        "rank_residualize_x": rank_x,
        "rank_residualize_y": rank_y,
    }


def verdict(models: dict[str, dict[str, object]]) -> str:
    positive = [models[name] for name in ["abundance", "TE", "structural_order"] if models.get(name, {}).get("status") == "computed"]
    if len(positive) < 3:
        return "species_specific_or_confounded"
    pos_ok = all(
        isinstance(item.get("beta_f3_ramp"), float)
        and float(item["beta_f3_ramp"]) > 0.0
        and item.get("significant_alpha_0_05") is True
        for item in positive
    )
    half = models.get("half_life", {})
    loc = models.get("localization", {})
    null_ok = half.get("status") == "computed" and half.get("significant_alpha_0_05") is False
    if loc.get("status") == "computed":
        null_ok = null_ok and loc.get("significant_alpha_0_05") is False
    # Localization may be skipped because E.coli has no local data; do not let
    # that create a positive portability call by itself.
    if pos_ok and null_ok and loc.get("status") == "computed":
        return "portable_conserved_layer"
    return "species_specific_or_confounded"


def main() -> None:
    started = time.monotonic()
    try:
        missing = [
            path.name
            for path in [
                DATA_DIR / "ncbi_genetic_codes.json",
                DATA_DIR / f"cds_codon_abundance_{YEAST}.json",
                DATA_DIR / f"cds_codon_abundance_{ECOLI}.json",
                DATA_DIR / f"cds_ordered_sequences_{YEAST}.json",
                DATA_DIR / f"cds_ordered_sequences_{ECOLI}.json",
                DATA_DIR / f"ribosome_te_{YEAST}.json",
                DATA_DIR / f"ribosome_te_{ECOLI}.json",
                DATA_DIR / f"structural_order_{YEAST}.json",
                DATA_DIR / f"structural_order_{ECOLI}.json",
                DATA_DIR / "mrna_half_life_saccharomyces_cerevisiae_neymotin.json",
                DATA_DIR / "mrna_half_life_escherichia_coli_esquerre.json",
                DATA_DIR / "subcellular_localization_saccharomyces_cerevisiae.json",
                DATA_DIR / "gtrnadb_trna_all_copy_saccharomyces_cerevisiae.json",
                DATA_DIR / "gtrnadb_trna_all_copy_escherichia_coli.json",
            ]
            if not path.exists()
        ]
        if missing:
            emit(
                "needs_data",
                reason="required local yeast/E.coli CDS, TE, structural, half-life, localization, tRNA, or genetic-code data missing",
                missing_required_data=missing,
                checks=[
                    {"name": "orthotable_built", "passed": False},
                    {"name": "f3_ramp_ortholog_fixed_effect", "passed": False},
                    {"name": "portability_verdict", "passed": False},
                ],
            )

        code = standard_code()
        codons = sense_codons(code)
        aa_order = standard_amino_acids(code, codons)
        fibers = fibers_for(code, codons)
        f3 = f3_projected(codons, fibers)

        yeast_rows, yeast_summary = build_species_features(YEAST, code, codons, aa_order, f3)
        ecoli_rows, ecoli_summary = build_species_features(ECOLI, code, codons, aa_order, f3)
        if time.monotonic() - started > SCRIPT_WALL_SECONDS:
            emit("needs_external", reason="wall-time exceeded before OrthoDB fetch", n_orthogroups=0)

        orthotable, fetch_stats = build_orthotable(yeast_rows, ecoli_rows)
        n_orthogroups = len(orthotable)
        if n_orthogroups < MIN_1TO1_ORTHOGROUPS:
            emit(
                "needs_external",
                reason="OrthoDB fetch produced too few exact local 1:1 yeast↔E.coli orthogroups for powered FE model",
                n_orthogroups=n_orthogroups,
                min_1to1_orthogroups=MIN_1TO1_ORTHOGROUPS,
                orthotable_path=str(ORTHOTABLE_PATH),
                orthodb_fetch=fetch_stats,
                species_feature_summary={YEAST: yeast_summary, ECOLI: ecoli_summary},
                checks=[
                    {"name": "orthotable_built", "passed": False, "actual": n_orthogroups, "expected": f">= {MIN_1TO1_ORTHOGROUPS} exact local 1:1 orthogroups"},
                    {"name": "f3_ramp_ortholog_fixed_effect", "passed": False},
                    {"name": "portability_verdict", "passed": False},
                ],
                caveats=[
                    "current OrthoDB search with level=1 was attempted and counted; if it returns no cross-domain OGs, unlevelled current OrthoDB REST search is used only to look for exact local pair recovery",
                    "2-species yeast/E.coli fixed-effect design is low power even when orthogroup count passes",
                ],
                seed=SEED,
            )

        models = {
            "abundance": within_orthogroup_model(orthotable, yeast_rows, ecoli_rows, "abundance"),
            "TE": within_orthogroup_model(orthotable, yeast_rows, ecoli_rows, "TE"),
            "structural_order": within_orthogroup_model(orthotable, yeast_rows, ecoli_rows, "structural_order"),
            "half_life": within_orthogroup_model(orthotable, yeast_rows, ecoli_rows, "half_life"),
            "localization": within_single_species_negative_control(orthotable, yeast_rows, "yeast_gene", "localization"),
        }
        insufficient = {name: model for name, model in models.items() if model.get("status") == "needs_data"}
        if any(name in insufficient for name in ["abundance", "TE", "structural_order", "half_life"]):
            emit(
                "needs_data",
                reason="orthogroup table built but phenotype join was insufficient for required FE readouts",
                n_orthogroups=n_orthogroups,
                min_joined_orthogroups=MIN_JOINED_ORTHOGROUPS,
                models=models,
                orthodb_fetch=fetch_stats,
                orthotable_path=str(ORTHOTABLE_PATH),
                checks=[
                    {"name": "orthotable_built", "passed": True, "actual": n_orthogroups},
                    {"name": "f3_ramp_ortholog_fixed_effect", "passed": False, "actual": insufficient},
                    {"name": "portability_verdict", "passed": False},
                ],
                seed=SEED,
            )

        final_verdict = verdict(models)
        positive_ok = all(
            models[name].get("status") == "computed"
            and isinstance(models[name].get("beta_f3_ramp"), float)
            and float(models[name]["beta_f3_ramp"]) > 0.0
            and models[name].get("significant_alpha_0_05") is True
            for name in ["abundance", "TE", "structural_order"]
        )
        half_null = models["half_life"].get("status") == "computed" and models["half_life"].get("significant_alpha_0_05") is False
        loc_null = models["localization"].get("status") == "computed" and models["localization"].get("significant_alpha_0_05") is False
        checks = [
            {"name": "orthotable_built", "passed": n_orthogroups >= MIN_1TO1_ORTHOGROUPS, "actual": n_orthogroups, "expected": f">= {MIN_1TO1_ORTHOGROUPS}"},
            {"name": "f3_ramp_ortholog_fixed_effect", "passed": positive_ok, "actual": {name: models[name] for name in ["abundance", "TE", "structural_order"]}},
            {
                "name": "portability_verdict",
                "passed": final_verdict == "portable_conserved_layer",
                "actual": final_verdict,
                "negative_controls": {"half_life_null": half_null, "localization_null": loc_null, "localization_status": models["localization"].get("status")},
            },
        ]
        emit(
            "passed",
            n_orthogroups=n_orthogroups,
            orthotable_path=str(ORTHOTABLE_PATH),
            models=models,
            verdict=final_verdict,
            checks=checks,
            orthodb_fetch=fetch_stats,
            species_feature_summary={YEAST: yeast_summary, ECOLI: ecoli_summary},
            method={
                "f3_ramp": "projected synonymous f3_stress coordinate on first 50 sense codons",
                "f3_residual": "species-specific residualization against aa composition, GC3/ramp_GC3, length, and exact-complement tRNA-copy proxy",
                "fixed_effect": "two-species within-orthogroup difference model; intercept absorbs species fixed effect after orthogroup differencing",
                "p_value": "large-sample normal approximation from OLS standard error; standard-library only",
            },
            caveats=[
                "observational association only; not causal",
                "two species means no leave-one-species-out validation and low power",
                "localization negative control is yeast-only because local E.coli localization data are absent",
                "OrthoDB exact local 1:1 mapping is conservative and may undercount remote homologs not represented by local strain IDs",
            ],
            seed=SEED,
            wall_seconds=time.monotonic() - started,
        )
    except Exception as exc:
        emit(
            "failed",
            reason="invalid or unreadable input, OrthoDB response, or FE fit construction failed",
            error=f"{type(exc).__name__}: {exc}",
            checks=[
                {"name": "orthotable_built", "passed": False},
                {"name": "f3_ramp_ortholog_fixed_effect", "passed": False},
                {"name": "portability_verdict", "passed": False},
            ],
            seed=SEED,
        )


if __name__ == "__main__":
    main()

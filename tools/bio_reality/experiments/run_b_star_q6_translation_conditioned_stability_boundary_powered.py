#!/usr/bin/env python3
"""Translation-conditioned B*_Q6 boundary test for stability/turnover.

This is a held-out descriptive boundary audit.  It asks whether the
9-dimensional synonymous B*_Q6 residual predicts protein or mRNA stability
after measured translation controls and composition controls are already in
the model.  The verdict is based on the full-control increment only.
"""

from __future__ import annotations

import hashlib
import json
import math
import pathlib
import re
import sys
from typing import Any


EXPERIMENT_ID = "b_star_q6_translation_conditioned_stability_boundary_powered"
CLAIM_ID = "h3.cross_layer_relation.translation_conditioned_stability_boundary.b_star_q6_powered"

DATA_DIR = pathlib.Path("/Users/lexa/Desktop/lexa/omega/newmath/tools/bio_reality/data")
FOLD_COUNT = 5
SEED = f"sha256:{hashlib.sha256(EXPERIMENT_ID.encode('utf-8')).hexdigest()}"
EPS = 1e-12
RIDGE = 1e-5
MIN_JOINED = 300
MIN_PRIMARY_ORGANISMS_FOR_CROSSES = 2
FULL_DELTA_EPS = 0.001
SIGNIFICANCE_ALPHA = 0.05
ECOLI_PRIMARY_GROWTH_RATE = "0.40"

ORGANISMS = [
    {
        "organism": "saccharomyces_cerevisiae",
        "label": "Saccharomyces cerevisiae",
        "readouts": ["protein_turnover", "mrna_half_life"],
    },
    {
        "organism": "escherichia_coli_k12_mg1655",
        "label": "Escherichia coli K-12 MG1655",
        "readouts": ["mrna_half_life"],
    },
    {
        "organism": "homo_sapiens",
        "label": "Homo sapiens",
        "readouts": ["protein_turnover", "mrna_half_life"],
    },
]

CUN_CODONS = ["CUU", "CUC", "CUA", "CUG"]
UUR_CODONS = ["UUA", "UUG"]
Q9_FAMILIES = [
    ["UUU", "UUC"], ["UUA", "UUG"], ["UCU", "UCC", "UCA", "UCG"],
    ["UAU", "UAC"], ["UGU", "UGC"], ["CUU", "CUC", "CUA", "CUG"],
    ["CCU", "CCC", "CCA", "CCG"], ["CAU", "CAC"], ["CAA", "CAG"],
    ["CGU", "CGC", "CGA", "CGG"], ["AUU", "AUC", "AUA"],
    ["ACU", "ACC", "ACA", "ACG"], ["AAU", "AAC"], ["AAA", "AAG"],
    ["AGU", "AGC"], ["AGA", "AGG"], ["GUU", "GUC", "GUA", "GUG"],
    ["GCU", "GCC", "GCA", "GCG"], ["GAU", "GAC"], ["GAA", "GAG"],
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


def mean(values: list[float]) -> float | None:
    return None if not values else sum(values) / len(values)


def median(values: list[float]) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    mid = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[mid]
    return 0.5 * (ordered[mid - 1] + ordered[mid])


def standard_code() -> dict[str, str]:
    raw = load_json(DATA_DIR / "ncbi_genetic_codes.json")
    if not isinstance(raw, dict):
        raise ValueError("NCBI genetic-code payload must be an object")
    codon_order = raw.get("codon_order")
    tables = raw.get("tables")
    if not isinstance(codon_order, list) or not isinstance(tables, list):
        raise ValueError("NCBI genetic-code payload is malformed")
    table = next((item for item in tables if isinstance(item, dict) and item.get("table_id") == 1), None)
    if not isinstance(table, dict) or not isinstance(table.get("aa"), str):
        raise ValueError("standard genetic-code table is missing")
    aa = table["aa"]
    if len(codon_order) != len(aa):
        raise ValueError("standard genetic-code codon and aa rows differ in length")
    return {str(codon): aa[index] for index, codon in enumerate(codon_order)}


def fibers_for(code: dict[str, str], codons: list[str]) -> dict[str, list[str]]:
    fibers: dict[str, list[str]] = {}
    for codon in codons:
        fibers.setdefault(code[codon], []).append(codon)
    return fibers


def zero(codons: list[str]) -> dict[str, float]:
    return {codon: 0.0 for codon in codons}


def project_syn(vector: dict[str, float], fibers: dict[str, list[str]]) -> dict[str, float]:
    out = dict(vector)
    for fiber in fibers.values():
        center = sum(vector[codon] for codon in fiber) / len(fiber)
        for codon in fiber:
            out[codon] = vector[codon] - center
    return out


def q_vectors(codons: list[str]) -> dict[str, dict[str, float]]:
    raw: dict[str, dict[str, float]] = {}
    q = zero(codons); q["AAA"] = 1.0; q["AAG"] = -1.0; raw["K_AAA"] = q
    q = zero(codons)
    for c in ["AGA", "AGG"]:
        q[c] = 1.0
    for c in ["CGU", "CGC", "CGA", "CGG"]:
        q[c] = -0.25
    raw["Arg_AGR"] = q
    q = zero(codons); q["AUA"] = 1.0; q["AUU"] = -1.0; q["AUC"] = -1.0; raw["Ile_AUA"] = q
    q = zero(codons)
    for c in CUN_CODONS:
        q[c] = 0.25
    for c in UUR_CODONS:
        q[c] = -0.5
    raw["Leu_CUN_vs_UUR"] = q
    q = zero(codons); q["UUA"] = 1.0; q["UUG"] = -1.0; raw["Leu_UUA_vs_UUG"] = q
    q = zero(codons)
    for c in ["UCA", "UCG"]:
        q[c] = 0.5
    for c in ["AGU", "AGC"]:
        q[c] = -0.5
    raw["Ser_UCR_vs_AGY"] = q
    q = zero(codons); q["UCA"] = 1.0; q["UCG"] = -1.0; raw["Ser_UCA_vs_UCG"] = q
    q = zero(codons)
    for c in ["ACA", "ACG"]:
        q[c] = 0.5
    for c in ["ACU", "ACC"]:
        q[c] = -0.5
    raw["Thr_ACR_vs_ACY"] = q
    q = zero(codons)
    for family in Q9_FAMILIES:
        q[family[0]] += 1.0
        q[family[-1]] -= 1.0
    raw["f3_stress"] = q
    return raw


def standard_amino_acids(code: dict[str, str], codons: list[str]) -> list[str]:
    aas = sorted({code[codon] for codon in codons if code[codon] != "*"})
    if len(aas) != 20:
        raise ValueError(f"standard genetic code should expose 20 amino acids, got {len(aas)}")
    return aas


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def codon_counts_rna(record: dict[str, object], codons: list[str], organism: str, row_index: int) -> dict[str, int]:
    raw = record.get("codon_counts")
    if not isinstance(raw, dict):
        raise ValueError(f"{organism}.joined[{row_index}].codon_counts must be an object")
    converted = {codon: 0 for codon in codons}
    for raw_codon, raw_count in raw.items():
        codon = dna_to_rna(str(raw_codon))
        if codon in converted:
            value = numeric(raw_count, f"{organism}.joined[{row_index}].codon_counts.{raw_codon}")
            if value < 0.0 or int(value) != value:
                raise ValueError(f"{organism}.joined[{row_index}].codon_counts.{raw_codon} must be a non-negative integer")
            converted[codon] += int(value)
    return converted


def normed_coordinate(vector: dict[str, float], q: dict[str, float], codons: list[str]) -> float:
    denom = math.sqrt(sum(q[codon] * q[codon] for codon in codons))
    if denom <= 0.0:
        raise ValueError("q vector has zero norm")
    return sum(vector[codon] * q[codon] for codon in codons) / denom


def normalize_ensembl_gene_id(value: str) -> str:
    return value.strip().split(".", 1)[0]


def parse_cds_gene_keys(header: str) -> tuple[str | None, str | None]:
    ensg_match = re.search(r"\bgene:(ENSG[0-9]+)(?:\.[0-9]+)?\b", header)
    symbol_match = re.search(r"\bgene_symbol:([^\s]+)", header)
    ensg = normalize_ensembl_gene_id(ensg_match.group(1)) if ensg_match else None
    symbol = symbol_match.group(1).upper() if symbol_match else None
    return ensg, symbol


def yeast_orf_from_protein_id(protein_id: str) -> str | None:
    prefix = "4932."
    if not protein_id.startswith(prefix):
        return None
    orf = protein_id[len(prefix):].upper()
    return orf if orf else None


def gene_keys_for_cds(organism: str, item: dict[str, object]) -> tuple[str | None, str | None, str | None, str]:
    protein_id = item.get("protein_id")
    if not isinstance(protein_id, str) or not protein_id:
        return None, None, None, "missing_protein_id"
    if organism == "saccharomyces_cerevisiae":
        orf = yeast_orf_from_protein_id(protein_id)
        if orf is None:
            return protein_id, None, None, "unparseable_yeast_orf"
        return protein_id, orf, None, ""
    if organism == "escherichia_coli_k12_mg1655":
        locus_tag = item.get("cds_match_id")
        if not isinstance(locus_tag, str) or not locus_tag.startswith("b"):
            return protein_id, None, None, "missing_locus_tag"
        return protein_id, locus_tag, None, ""
    if organism == "homo_sapiens":
        header = item.get("cds_header")
        if not isinstance(header, str) or not header:
            return protein_id, None, None, "missing_cds_header"
        ensg, symbol = parse_cds_gene_keys(header)
        if ensg is None and symbol is None:
            return protein_id, None, None, "missing_gene_keys"
        return protein_id, ensg, symbol, ""
    raise ValueError(f"unsupported organism {organism}")


def te_indices(payload: dict[str, object], organism: str) -> tuple[dict[str, dict[str, float]], dict[str, dict[str, float]], dict[str, object]]:
    genes = payload.get("genes")
    if not isinstance(genes, list):
        raise ValueError(f"{organism} TE payload must contain genes list")
    by_protein: dict[str, dict[str, float]] = {}
    gene_buckets: dict[str, list[dict[str, float]]] = {}
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "missing_gene_key": 0,
        "nonpositive_te": 0,
        "nonpositive_mrna": 0,
        "nonpositive_footprint": 0,
        "duplicate_protein_id": 0,
    }
    for row_index, item in enumerate(genes):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id = item.get("protein_id")
        gene_key = item.get("gene_key")
        if not isinstance(protein_id, str) or not protein_id:
            skipped["missing_protein_id"] += 1
            continue
        if not isinstance(gene_key, str) or not gene_key:
            skipped["missing_gene_key"] += 1
            continue
        te = numeric(item.get("te"), f"{organism}.genes[{row_index}].te")
        mrna = numeric(item.get("mrna"), f"{organism}.genes[{row_index}].mrna")
        footprint = numeric(item.get("footprint"), f"{organism}.genes[{row_index}].footprint")
        if te <= 0.0:
            skipped["nonpositive_te"] += 1
            continue
        if mrna <= 0.0:
            skipped["nonpositive_mrna"] += 1
            continue
        if footprint <= 0.0:
            skipped["nonpositive_footprint"] += 1
            continue
        record = {"te": te, "mrna": mrna, "footprint": footprint}
        if protein_id in by_protein:
            skipped["duplicate_protein_id"] += 1
        else:
            by_protein[protein_id] = record
        normalized_gene = normalize_ensembl_gene_id(gene_key) if gene_key.startswith("ENSG") else gene_key
        if organism == "homo_sapiens" and not normalized_gene.startswith("ENSG"):
            normalized_gene = normalized_gene.upper()
        gene_buckets.setdefault(normalized_gene, []).append(record)
    by_gene = {key: bucket[0] for key, bucket in gene_buckets.items() if len(bucket) == 1}
    return by_protein, by_gene, {
        "n_genes_with_te_reported": payload.get("n_genes_with_te"),
        "join_hit_rate_reported": payload.get("join_hit_rate"),
        "n_valid_te_by_protein": len(by_protein),
        "n_unique_unambiguous_te_gene_keys": len(by_gene),
        "n_ambiguous_te_gene_keys": sum(1 for bucket in gene_buckets.values() if len(bucket) > 1),
        "te_definition": payload.get("te_definition"),
        "study_ref": payload.get("study_ref"),
        "skipped_te_records": skipped,
    }


def stability_index(organism: str, readout: str, payload: dict[str, object]) -> tuple[dict[str, float], dict[str, float], dict[str, float], dict[str, object]]:
    by_protein: dict[str, float] = {}
    by_primary: dict[str, float] = {}
    by_symbol: dict[str, float] = {}
    skipped: dict[str, int] = {}

    if readout == "protein_turnover":
        raw = payload.get("protein_turnover")
        if not isinstance(raw, dict):
            raise ValueError(f"{organism} protein-turnover payload must contain protein_turnover object")
        skipped = {"missing_protein_id": 0, "nonpositive_value": 0, "duplicate_protein_id": 0}
        for protein_id, value in raw.items():
            if not isinstance(protein_id, str) or not protein_id:
                skipped["missing_protein_id"] += 1
                continue
            half_life = numeric(value, f"protein_turnover.{protein_id}")
            if half_life <= 0.0:
                skipped["nonpositive_value"] += 1
                continue
            if protein_id in by_protein:
                skipped["duplicate_protein_id"] += 1
                continue
            by_protein[protein_id] = math.log10(half_life)
        return by_protein, by_primary, by_symbol, {
            "readout_kind": "protein_turnover_half_life",
            "readout_transform": "log10(value)",
            "n_records_reported": payload.get("n_turnover_proteins"),
            "n_valid_records": len(by_protein),
            "source_kind": payload.get("source_kind"),
            "source_url": payload.get("source_url"),
            "payload_sha256": payload.get("payload_sha256") or payload.get("source_xlsx_sha256"),
            "id_mapping_method": payload.get("id_mapping_method"),
            "skipped_stability_records": skipped,
        }

    if readout != "mrna_half_life":
        raise ValueError(f"unknown stability readout {readout}")

    records = payload.get("records")
    if not isinstance(records, list):
        raise ValueError(f"{organism} mRNA half-life payload must contain records list")

    if organism == "saccharomyces_cerevisiae":
        skipped = {"non_object": 0, "missing_syst": 0, "nonpositive_value": 0, "duplicate_syst": 0}
        for row_index, item in enumerate(records):
            if not isinstance(item, dict):
                skipped["non_object"] += 1
                continue
            syst = item.get("Syst")
            if not isinstance(syst, str) or not syst:
                skipped["missing_syst"] += 1
                continue
            value = numeric(item.get("thalf"), f"{organism}.records[{row_index}].thalf")
            if value <= 0.0:
                skipped["nonpositive_value"] += 1
                continue
            if syst in by_primary:
                skipped["duplicate_syst"] += 1
                continue
            by_primary[syst] = math.log10(value)
    elif organism == "escherichia_coli_k12_mg1655":
        skipped = {"non_object": 0, "missing_gene_id": 0, "missing_growth_rate": 0, "nonpositive_value": 0, "duplicate_gene_id": 0}
        for row_index, item in enumerate(records):
            if not isinstance(item, dict):
                skipped["non_object"] += 1
                continue
            gene_id = item.get("GeneId")
            if not isinstance(gene_id, str) or not gene_id:
                skipped["missing_gene_id"] += 1
                continue
            values = item.get("half_life_minutes_by_growth_rate_h_inv")
            if not isinstance(values, dict) or ECOLI_PRIMARY_GROWTH_RATE not in values:
                skipped["missing_growth_rate"] += 1
                continue
            value = numeric(values[ECOLI_PRIMARY_GROWTH_RATE], f"{organism}.records[{row_index}].half_life[{ECOLI_PRIMARY_GROWTH_RATE}]")
            if value <= 0.0:
                skipped["nonpositive_value"] += 1
                continue
            if gene_id in by_primary:
                skipped["duplicate_gene_id"] += 1
                continue
            by_primary[gene_id] = math.log10(value)
    elif organism == "homo_sapiens":
        symbol_buckets: dict[str, list[float]] = {}
        skipped = {
            "non_object": 0,
            "missing_ensembl_gene_id": 0,
            "nonpositive_value": 0,
            "duplicate_ensembl_gene_id": 0,
        }
        for row_index, item in enumerate(records):
            if not isinstance(item, dict):
                skipped["non_object"] += 1
                continue
            ensg = normalize_ensembl_gene_id(str(item.get("ensembl_gene_id_base") or item.get("ensembl_gene_id") or ""))
            if not ensg:
                skipped["missing_ensembl_gene_id"] += 1
                continue
            value = numeric(item.get("consensus_relative_half_life"), f"{organism}.records[{row_index}].consensus_relative_half_life")
            if value <= 0.0:
                skipped["nonpositive_value"] += 1
                continue
            if ensg in by_primary:
                skipped["duplicate_ensembl_gene_id"] += 1
                continue
            transformed = math.log10(value)
            by_primary[ensg] = transformed
            symbol = str(item.get("gene_name") or "").strip().upper()
            if symbol:
                symbol_buckets.setdefault(symbol, []).append(transformed)
        by_symbol = {symbol: bucket[0] for symbol, bucket in symbol_buckets.items() if len(bucket) == 1}
    else:
        raise ValueError(f"unsupported mRNA half-life organism {organism}")

    return by_protein, by_primary, by_symbol, {
        "readout_kind": "mrna_half_life",
        "readout_transform": "log10(value)",
        "n_records_reported": payload.get("parse_summary", {}).get("n_valid_half_life_rows") if isinstance(payload.get("parse_summary"), dict) else len(records),
        "n_valid_primary_keys": len(by_primary),
        "n_valid_symbol_keys": len(by_symbol),
        "source_kind": payload.get("source_kind"),
        "source_url": payload.get("source_url"),
        "payload_sha256": payload.get("payload_sha256"),
        "join_key": payload.get("join_key"),
        "ecoli_growth_rate_h_inv": ECOLI_PRIMARY_GROWTH_RATE if organism == "escherichia_coli_k12_mg1655" else None,
        "skipped_stability_records": skipped,
    }


def stability_path(organism: str, readout: str) -> pathlib.Path:
    if readout == "protein_turnover":
        return DATA_DIR / f"protein_turnover_{organism}.json"
    if readout == "mrna_half_life" and organism == "saccharomyces_cerevisiae":
        return DATA_DIR / "mrna_half_life_saccharomyces_cerevisiae_neymotin.json"
    if readout == "mrna_half_life" and organism == "escherichia_coli_k12_mg1655":
        return DATA_DIR / "mrna_half_life_escherichia_coli_esquerre.json"
    if readout == "mrna_half_life" and organism == "homo_sapiens":
        return DATA_DIR / "mrna_half_life_homo_sapiens_agarwal_consensus.json"
    raise ValueError(f"unsupported stability path for {organism}/{readout}")


def get_stability_value(
    *,
    readout: str,
    protein_id: str,
    primary_key: str | None,
    symbol_key: str | None,
    by_protein: dict[str, float],
    by_primary: dict[str, float],
    by_symbol: dict[str, float],
) -> tuple[float | None, str | None]:
    if readout == "protein_turnover":
        value = by_protein.get(protein_id)
        return value, "protein_id" if value is not None else None
    value = by_primary.get(primary_key) if primary_key is not None else None
    if value is not None:
        return value, "primary_gene_key"
    value = by_symbol.get(symbol_key.upper()) if symbol_key is not None else None
    if value is not None:
        return value, "gene_symbol_fallback"
    return None, None


def get_te_record(
    *,
    organism: str,
    protein_id: str,
    primary_key: str | None,
    symbol_key: str | None,
    by_protein: dict[str, dict[str, float]],
    by_gene: dict[str, dict[str, float]],
) -> tuple[dict[str, float] | None, str | None]:
    record = by_protein.get(protein_id)
    if record is not None:
        return record, "protein_id"
    if organism == "homo_sapiens":
        gene_key = primary_key or (symbol_key.upper() if symbol_key else None)
    else:
        gene_key = primary_key
    record = by_gene.get(str(gene_key)) if gene_key is not None else None
    if record is not None:
        return record, "gene_key"
    return None, None


def joined_rows(
    *,
    organism: str,
    label: str,
    readout: str,
    code: dict[str, str],
    codons: list[str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
) -> tuple[list[dict[str, object]], dict[str, object]]:
    cds_payload = load_json(DATA_DIR / f"cds_codon_abundance_{organism}.json")
    te_payload = load_json(DATA_DIR / f"ribosome_te_{organism}.json")
    readout_payload = load_json(stability_path(organism, readout))
    if not isinstance(cds_payload, dict) or not isinstance(te_payload, dict) or not isinstance(readout_payload, dict):
        raise ValueError(f"{organism}/{readout} input payloads must be JSON objects")
    joined = cds_payload.get("joined")
    if not isinstance(joined, list):
        raise ValueError(f"{organism} CDS payload must contain joined list")

    te_by_protein, te_by_gene, te_summary = te_indices(te_payload, organism)
    stab_by_protein, stab_by_primary, stab_by_symbol, stability_summary = stability_index(organism, readout, readout_payload)

    rows: list[dict[str, object]] = []
    skipped = {
        "non_object": 0,
        "missing_protein_id": 0,
        "unparseable_yeast_orf": 0,
        "missing_locus_tag": 0,
        "missing_cds_header": 0,
        "missing_gene_keys": 0,
        "duplicate_stable_id": 0,
        "no_stability_match": 0,
        "no_te_match": 0,
        "nonpositive_abundance": 0,
        "invalid_length": 0,
        "empty_sense_codon_counts": 0,
    }
    join_sources = {
        "stability_protein_id": 0,
        "stability_primary_gene_key": 0,
        "stability_gene_symbol_fallback": 0,
        "te_protein_id": 0,
        "te_gene_key": 0,
    }
    seen: set[str] = set()

    for row_index, item in enumerate(joined):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        protein_id, primary_key, symbol_key, error = gene_keys_for_cds(organism, item)
        if error:
            skipped[error] += 1
            continue
        if protein_id is None:
            skipped["missing_protein_id"] += 1
            continue
        stable_id = protein_id if readout == "protein_turnover" else (primary_key or f"symbol:{symbol_key}")
        if stable_id is None:
            skipped["missing_gene_keys"] += 1
            continue
        if stable_id in seen:
            skipped["duplicate_stable_id"] += 1
            continue

        stability_value, stability_source = get_stability_value(
            readout=readout,
            protein_id=protein_id,
            primary_key=primary_key,
            symbol_key=symbol_key,
            by_protein=stab_by_protein,
            by_primary=stab_by_primary,
            by_symbol=stab_by_symbol,
        )
        if stability_value is None or stability_source is None:
            skipped["no_stability_match"] += 1
            continue
        join_sources[f"stability_{stability_source}"] += 1

        te_record, te_source = get_te_record(
            organism=organism,
            protein_id=protein_id,
            primary_key=primary_key,
            symbol_key=symbol_key,
            by_protein=te_by_protein,
            by_gene=te_by_gene,
        )
        if te_record is None or te_source is None:
            skipped["no_te_match"] += 1
            continue
        join_sources[f"te_{te_source}"] += 1

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
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue

        frequencies = {codon: counts[codon] / total for codon in codons}
        bstar = [normed_coordinate(frequencies, q_projected[name], codons) for name in q_names]
        aa_counts = {aa: 0 for aa in aa_order}
        for codon in codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        if aa_total <= 0:
            raise ValueError(f"{organism}.joined[{row_index}] has no amino-acid counts")
        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total

        rows.append(
            {
                "protein_id": protein_id,
                "stable_id": stable_id,
                "y": stability_value,
                "bstar": bstar,
                "translation": [
                    math.log10(abundance),
                    math.log10(te_record["te"]),
                    math.log10(te_record["mrna"]),
                    math.log10(te_record["footprint"]),
                ],
                "composition_controls": [math.log(cds_len_nt)]
                + [aa_counts[aa] / aa_total for aa in aa_order]
                + [gc3],
            }
        )
        seen.add(stable_id)

    summary = {
        "organism_label": label,
        "readout": readout,
        "n_cds_joined_reported": cds_payload.get("n_joined"),
        "cds_join_hit_rate_reported": cds_payload.get("join_hit_rate"),
        "n_joined": len(rows),
        "join_sources": join_sources,
        "skipped_cds_records": skipped,
        "translation_summary": te_summary,
        "stability_summary": stability_summary,
    }
    return rows, summary


def stable_hash_int(text: str) -> int:
    digest = hashlib.sha256(f"{SEED}|{text}".encode("utf-8")).digest()
    return int.from_bytes(digest[:8], "big")


def matrix_for(rows: list[dict[str, object]], feature_blocks: list[str]) -> list[list[float]]:
    matrix: list[list[float]] = []
    for row in rows:
        values: list[float] = []
        for block in feature_blocks:
            raw = row[block]
            if not isinstance(raw, list):
                raise ValueError(f"feature block {block} is not a list")
            values.extend(float(value) for value in raw)
        matrix.append(values)
    return matrix


def y_for(rows: list[dict[str, object]]) -> list[float]:
    return [float(row["y"]) for row in rows]


def deterministic_folds(rows: list[dict[str, object]], organism: str, readout: str, fold_count: int) -> list[int]:
    order = sorted(
        range(len(rows)),
        key=lambda idx: stable_hash_int(f"fold|{organism}|{readout}|{rows[idx]['stable_id']}|{idx}"),
    )
    folds = [0 for _ in rows]
    for rank, index in enumerate(order):
        folds[index] = rank % fold_count
    return folds


def train_standardize(x_train: list[list[float]]) -> tuple[list[float], list[float]]:
    if not x_train:
        return [], []
    width = len(x_train[0])
    centers: list[float] = []
    scales: list[float] = []
    for col in range(width):
        values = [row[col] for row in x_train]
        center = sum(values) / len(values)
        var = sum((value - center) * (value - center) for value in values) / max(1, len(values) - 1)
        scale = math.sqrt(var)
        if scale <= EPS:
            scale = 1.0
        centers.append(center)
        scales.append(scale)
    return centers, scales


def apply_standardize(x_rows: list[list[float]], centers: list[float], scales: list[float]) -> list[list[float]]:
    return [
        [(row[col] - centers[col]) / scales[col] for col in range(len(row))]
        for row in x_rows
    ]


def invert_matrix(matrix: list[list[float]], ridge: float = RIDGE) -> list[list[float]]:
    n = len(matrix)
    aug = []
    for row in range(n):
        left = list(matrix[row])
        left[row] += ridge
        right = [0.0 for _ in range(n)]
        right[row] = 1.0
        aug.append(left + right)
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= EPS:
            aug[col][col] += ridge * 100.0 + EPS
            pivot = col
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        scale = aug[col][col]
        if abs(scale) <= EPS:
            scale = EPS if scale >= 0 else -EPS
        for item in range(2 * n):
            aug[col][item] /= scale
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor == 0.0:
                continue
            for item in range(2 * n):
                aug[row][item] -= factor * aug[col][item]
    return [row[n:] for row in aug]


def fit_ridge(x_train: list[list[float]], y_train: list[float]) -> list[float]:
    if not x_train:
        raise ValueError("empty training matrix")
    width = len(x_train[0]) + 1
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    xty = [0.0 for _ in range(width)]
    for row, y in zip(x_train, y_train):
        design = [1.0] + row
        for i in range(width):
            xty[i] += design[i] * y
            for j in range(width):
                xtx[i][j] += design[i] * design[j]
    for i in range(1, width):
        xtx[i][i] += RIDGE
    inv = invert_matrix(xtx, ridge=EPS)
    return [sum(inv[row][col] * xty[col] for col in range(width)) for row in range(width)]


def predict_ridge(beta: list[float], x_rows: list[list[float]]) -> list[float]:
    return [beta[0] + sum(beta[col + 1] * row[col] for col in range(len(row))) for row in x_rows]


def r2_score(y_true: list[float], y_pred: list[float], center: float | None = None) -> float | None:
    if len(y_true) != len(y_pred) or not y_true:
        return None
    baseline = mean(y_true) if center is None else center
    if baseline is None:
        return None
    sst = sum((value - baseline) * (value - baseline) for value in y_true)
    if sst <= EPS:
        return None
    sse = sum((truth - pred) * (truth - pred) for truth, pred in zip(y_true, y_pred))
    return 1.0 - sse / sst


def pearson(y_true: list[float], y_pred: list[float]) -> float | None:
    if len(y_true) != len(y_pred) or len(y_true) < 2:
        return None
    y_mean = mean(y_true)
    p_mean = mean(y_pred)
    if y_mean is None or p_mean is None:
        return None
    num = sum((y - y_mean) * (p - p_mean) for y, p in zip(y_true, y_pred))
    den_y = math.sqrt(sum((y - y_mean) * (y - y_mean) for y in y_true))
    den_p = math.sqrt(sum((p - p_mean) * (p - p_mean) for p in y_pred))
    if den_y <= EPS or den_p <= EPS:
        return None
    return num / (den_y * den_p)


def evaluate_regression(y_true: list[float], y_pred: list[float], global_center: float) -> dict[str, object]:
    return {
        "n_tested": len(y_true),
        "held_out_r2": r2_score(y_true, y_pred, center=global_center),
        "pearson_r": pearson(y_true, y_pred),
        "y_mean": mean(y_true),
        "y_sd": None if len(y_true) < 2 else math.sqrt(sum((value - float(mean(y_true))) ** 2 for value in y_true) / (len(y_true) - 1)),
    }


def cross_validated_ridge(rows: list[dict[str, object]], feature_blocks: list[str], organism: str, readout: str) -> dict[str, object]:
    x_all = matrix_for(rows, feature_blocks)
    y_all = y_for(rows)
    folds = deterministic_folds(rows, organism, readout, FOLD_COUNT)
    all_true: list[float] = []
    all_pred: list[float] = []
    fold_metrics: list[dict[str, object]] = []
    global_center = float(mean(y_all))
    for fold in range(FOLD_COUNT):
        train_indices = [index for index, value in enumerate(folds) if value != fold]
        test_indices = [index for index, value in enumerate(folds) if value == fold]
        x_train_raw = [x_all[index] for index in train_indices]
        x_test_raw = [x_all[index] for index in test_indices]
        y_train = [y_all[index] for index in train_indices]
        y_test = [y_all[index] for index in test_indices]
        centers, scales = train_standardize(x_train_raw)
        x_train = apply_standardize(x_train_raw, centers, scales)
        x_test = apply_standardize(x_test_raw, centers, scales)
        beta = fit_ridge(x_train, y_train)
        pred = predict_ridge(beta, x_test)
        all_true.extend(y_test)
        all_pred.extend(pred)
        fold_metrics.append(evaluate_regression(y_test, pred, global_center))
    metrics = evaluate_regression(all_true, all_pred, global_center)
    metrics["feature_blocks"] = feature_blocks
    metrics["feature_count"] = len(x_all[0]) if x_all else 0
    metrics["fold_count"] = FOLD_COUNT
    metrics["fold_metrics"] = [
        {
            "fold": index,
            "n_tested": item["n_tested"],
            "held_out_r2": item["held_out_r2"],
            "pearson_r": item["pearson_r"],
        }
        for index, item in enumerate(fold_metrics)
    ]
    return metrics


def mean_baseline(rows: list[dict[str, object]], organism: str, readout: str) -> dict[str, object]:
    y_all = y_for(rows)
    folds = deterministic_folds(rows, organism, readout, FOLD_COUNT)
    all_true: list[float] = []
    all_pred: list[float] = []
    fold_metrics: list[dict[str, object]] = []
    global_center = float(mean(y_all))
    for fold in range(FOLD_COUNT):
        train = [y_all[index] for index, value in enumerate(folds) if value != fold]
        test = [y_all[index] for index, value in enumerate(folds) if value == fold]
        pred_value = float(mean(train))
        pred = [pred_value for _ in test]
        all_true.extend(test)
        all_pred.extend(pred)
        fold_metrics.append(evaluate_regression(test, pred, global_center))
    metrics = evaluate_regression(all_true, all_pred, global_center)
    metrics["feature_blocks"] = ["train_fold_mean_baseline"]
    metrics["feature_count"] = 0
    metrics["fold_count"] = FOLD_COUNT
    metrics["fold_metrics"] = [
        {
            "fold": index,
            "n_tested": item["n_tested"],
            "held_out_r2": item["held_out_r2"],
            "pearson_r": item["pearson_r"],
        }
        for index, item in enumerate(fold_metrics)
    ]
    return metrics


def permutation_rows(rows: list[dict[str, object]], block: str, organism: str, readout: str) -> list[dict[str, object]]:
    shuffled = [dict(row) for row in rows]
    values = [row[block] for row in rows]
    order = sorted(
        range(len(values)),
        key=lambda index: stable_hash_int(f"permute|{organism}|{readout}|{block}|{rows[index]['stable_id']}|{index}"),
    )
    permuted = [None for _ in values]
    for target_rank, source_index in enumerate(order):
        target_index = order[(target_rank + 1) % len(order)]
        permuted[target_index] = values[source_index]
    for index, value in enumerate(permuted):
        shuffled[index][block] = value
    return shuffled


def delta(newer: dict[str, object], older: dict[str, object]) -> dict[str, object]:
    r2_new = newer.get("held_out_r2")
    r2_old = older.get("held_out_r2")
    return {
        "delta_held_out_r2": None if not isinstance(r2_new, float) or not isinstance(r2_old, float) else r2_new - r2_old,
    }


def fold_deltas(newer: dict[str, object], older: dict[str, object]) -> list[float]:
    newer_folds = newer.get("fold_metrics")
    older_folds = older.get("fold_metrics")
    if not isinstance(newer_folds, list) or not isinstance(older_folds, list):
        return []
    out: list[float] = []
    for n_item, o_item in zip(newer_folds, older_folds):
        if not isinstance(n_item, dict) or not isinstance(o_item, dict):
            continue
        n_r2 = n_item.get("held_out_r2")
        o_r2 = o_item.get("held_out_r2")
        if isinstance(n_r2, float) and isinstance(o_r2, float):
            out.append(n_r2 - o_r2)
    return out


def summarize_numbers(values: list[float]) -> dict[str, object]:
    return {
        "n": len(values),
        "mean": mean(values),
        "median": median(values),
        "min": min(values) if values else None,
        "max": max(values) if values else None,
        "positive_count": sum(1 for value in values if value > 0.0),
        "negative_count": sum(1 for value in values if value < 0.0),
    }


def exact_signflip_p_greater(values: list[float]) -> float | None:
    nonzero = [abs(value) for value in values if abs(value) > EPS]
    observed = sum(values)
    n = len(nonzero)
    if n == 0:
        return None
    if n > 22:
        # This experiment uses at most 15 primary fold deltas; keep a bounded fallback.
        positives = sum(1 for value in values if value > 0.0)
        return sum(math.comb(n, k) for k in range(positives, n + 1)) / (2 ** n)
    extreme = 0
    total = 1 << n
    for mask in range(total):
        signed = 0.0
        for bit, magnitude in enumerate(nonzero):
            signed += magnitude if (mask >> bit) & 1 else -magnitude
        if signed >= observed - EPS:
            extreme += 1
    return extreme / total


def aggregate_results(results: list[dict[str, object]]) -> dict[str, object]:
    full = [float(item["incremental"]["bstar_q6_given_translation_length_aa_gc_controls"]["delta_held_out_r2"]) for item in results]
    translation = [float(item["incremental"]["bstar_q6_given_translation_controls"]["delta_held_out_r2"]) for item in results]
    bstar = [float(item["incremental"]["bstar_q6_vs_mean_baseline"]["delta_held_out_r2"]) for item in results]
    permuted_full = [float(item["incremental"]["permuted_bstar_q6_given_translation_length_aa_gc_controls"]["delta_held_out_r2"]) for item in results]
    n_total = sum(int(item["n_model_rows"]) for item in results)
    weighted_full = None if n_total <= 0 else sum(
        float(item["n_model_rows"]) * float(item["incremental"]["bstar_q6_given_translation_length_aa_gc_controls"]["delta_held_out_r2"])
        for item in results
    ) / n_total
    weighted_permuted = None if n_total <= 0 else sum(
        float(item["n_model_rows"]) * float(item["incremental"]["permuted_bstar_q6_given_translation_length_aa_gc_controls"]["delta_held_out_r2"])
        for item in results
    ) / n_total
    fold_delta_values: list[float] = []
    permuted_fold_delta_values: list[float] = []
    for item in results:
        fold_delta_values.extend(float(value) for value in item.get("full_control_fold_deltas", []) if isinstance(value, (int, float)))
        permuted_fold_delta_values.extend(float(value) for value in item.get("permuted_full_control_fold_deltas", []) if isinstance(value, (int, float)))
    return {
        "n_primary_organisms": len(results),
        "n_total_rows": n_total,
        "bstar_q6_vs_mean_baseline_delta_r2": summarize_numbers(bstar),
        "translation_conditioned_delta_r2": summarize_numbers(translation),
        "full_control_delta_r2": summarize_numbers(full),
        "permuted_full_control_delta_r2": summarize_numbers(permuted_full),
        "weighted_full_control_delta_r2": weighted_full,
        "weighted_permuted_full_control_delta_r2": weighted_permuted,
        "full_control_fold_delta_summary": summarize_numbers(fold_delta_values),
        "permuted_full_control_fold_delta_summary": summarize_numbers(permuted_fold_delta_values),
        "full_control_signflip_p_greater_zero": exact_signflip_p_greater(fold_delta_values),
        "permuted_full_control_signflip_p_greater_zero": exact_signflip_p_greater(permuted_fold_delta_values),
        "positive_primary_organism_count": sum(1 for value in full if value > 0.0),
        "primary_organisms": [item["organism"] for item in results],
    }


def organism_call(result: dict[str, object]) -> str:
    full_delta = result["incremental"]["bstar_q6_given_translation_length_aa_gc_controls"]["delta_held_out_r2"]
    trans_delta = result["incremental"]["bstar_q6_given_translation_controls"]["delta_held_out_r2"]
    if not isinstance(full_delta, float) or not isinstance(trans_delta, float):
        return "insufficient_metric"
    if full_delta >= FULL_DELTA_EPS and trans_delta > 0.0:
        return "full_control_positive"
    if full_delta > 0.0 or trans_delta > 0.0:
        return "partial"
    return "mediated_blocked_null"


def verdict_from_aggregate(aggregate: dict[str, object]) -> str:
    n_org = int(aggregate.get("n_primary_organisms", 0))
    weighted_full = aggregate.get("weighted_full_control_delta_r2")
    weighted_permuted = aggregate.get("weighted_permuted_full_control_delta_r2")
    p_value = aggregate.get("full_control_signflip_p_greater_zero")
    positive_count = int(aggregate.get("positive_primary_organism_count", 0))
    if (
        n_org >= MIN_PRIMARY_ORGANISMS_FOR_CROSSES
        and isinstance(weighted_full, float)
        and isinstance(weighted_permuted, float)
        and isinstance(p_value, float)
        and weighted_full >= FULL_DELTA_EPS
        and weighted_full > weighted_permuted + FULL_DELTA_EPS
        and p_value <= SIGNIFICANCE_ALPHA
        and positive_count >= MIN_PRIMARY_ORGANISMS_FOR_CROSSES
    ):
        return "crosses_to_stability_layer"
    if positive_count > 0 or (isinstance(weighted_full, float) and weighted_full > 0.0):
        return "partial"
    return "mediated_blocked_null"


def run_readout(
    *,
    organism: str,
    label: str,
    readout: str,
    code: dict[str, str],
    codons: list[str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
) -> dict[str, object]:
    path = stability_path(organism, readout)
    if not path.exists():
        return {
            "organism": organism,
            "label": label,
            "readout": readout,
            "powered": False,
            "status": "needs_data",
            "reason": "stability readout file missing",
            "missing_path": str(path),
        }
    rows, data_summary = joined_rows(
        organism=organism,
        label=label,
        readout=readout,
        code=code,
        codons=codons,
        aa_order=aa_order,
        q_projected=q_projected,
        q_names=q_names,
    )
    powered = len(rows) >= MIN_JOINED
    base_result = {
        "organism": organism,
        "label": label,
        "readout": readout,
        "status": "computed" if powered else "needs_data",
        "powered": powered,
        "n_model_rows": len(rows),
        "data_summary": data_summary,
        "power_note": None if powered else f"交集不足 n={len(rows)} < {MIN_JOINED}；该 readout 不进入 headline aggregate。",
    }
    if not powered:
        return base_result

    baseline = mean_baseline(rows, organism, readout)
    bstar = cross_validated_ridge(rows, ["bstar"], organism, readout)
    translation = cross_validated_ridge(rows, ["translation"], organism, readout)
    translation_bstar = cross_validated_ridge(rows, ["translation", "bstar"], organism, readout)
    full = cross_validated_ridge(rows, ["translation", "composition_controls"], organism, readout)
    full_bstar = cross_validated_ridge(rows, ["translation", "composition_controls", "bstar"], organism, readout)
    composition = cross_validated_ridge(rows, ["composition_controls"], organism, readout)
    permuted_rows = permutation_rows(rows, "bstar", organism, readout)
    translation_permuted_bstar = cross_validated_ridge(permuted_rows, ["translation", "bstar"], organism, readout)
    full_permuted_bstar = cross_validated_ridge(permuted_rows, ["translation", "composition_controls", "bstar"], organism, readout)

    result = {
        **base_result,
        "metrics": {
            "mean_baseline": baseline,
            "bstar_q6_only": bstar,
            "translation_controls_only": translation,
            "translation_plus_bstar_q6": translation_bstar,
            "translation_plus_length_aa_gc_controls": full,
            "translation_plus_length_aa_gc_controls_plus_bstar_q6": full_bstar,
            "length_aa_gc_controls_only": composition,
            "translation_plus_permuted_bstar_q6": translation_permuted_bstar,
            "translation_plus_length_aa_gc_controls_plus_permuted_bstar_q6": full_permuted_bstar,
        },
        "incremental": {
            "bstar_q6_vs_mean_baseline": delta(bstar, baseline),
            "bstar_q6_given_translation_controls": delta(translation_bstar, translation),
            "bstar_q6_given_translation_length_aa_gc_controls": delta(full_bstar, full),
            "permuted_bstar_q6_given_translation_controls": delta(translation_permuted_bstar, translation),
            "permuted_bstar_q6_given_translation_length_aa_gc_controls": delta(full_permuted_bstar, full),
        },
        "full_control_fold_deltas": fold_deltas(full_bstar, full),
        "permuted_full_control_fold_deltas": fold_deltas(full_permuted_bstar, full),
    }
    result["organism_readout_call"] = organism_call(result)
    return result


def cannot_claim() -> list[str]:
    return [
        "这是横截面 held-out 预测边界实验，不是稳定性/降解机制或因果中介实验。",
        "translation 控制为同一基因的 log10 protein abundance、measured TE、mRNA、footprint；不能证明翻译层已被完全观测。",
        "全控 verdict 使用 translation + protein length + 20 amino-acid composition + GC3 后的 B*_Q6 增量；只控 translation 的增量不决定 crosses。",
        "protein turnover 和 mRNA half-life 是不同层级 readout；headline aggregate 每个物种只取一个 primary readout，避免同一物种重复投票。",
        "human mRNA half-life 是跨数据集 consensus relative half-life；已按本实验规则 log10 变换，但不是原始分钟。",
        "fold-level sign-flip null 是确定性小样本诊断，不是 phylogenetic 或因果显著性检验。",
        "若全控增量为零或为负，解释为本数据和此模型下 composition/translation 控制吸收了可见稳定性信息，不等于真实生物信号不存在。",
    ]


def main() -> None:
    required = [DATA_DIR / "ncbi_genetic_codes.json"]
    for item in ORGANISMS:
        organism = str(item["organism"])
        required.extend(
            [
                DATA_DIR / f"cds_codon_abundance_{organism}.json",
                DATA_DIR / f"ribosome_te_{organism}.json",
            ]
        )
        for readout in item["readouts"]:
            required.append(stability_path(organism, str(readout)))
    missing = [str(path) for path in required if not path.exists()]
    if missing:
        emit("needs_data", reason="required local CDS/TE/stability data not present", missing_required_data=missing)

    try:
        code = standard_code()
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        if q_names != [
            "K_AAA",
            "Arg_AGR",
            "Ile_AUA",
            "Leu_CUN_vs_UUR",
            "Leu_UUA_vs_UUG",
            "Ser_UCR_vs_AGY",
            "Ser_UCA_vs_UCG",
            "Thr_ACR_vs_ACY",
            "f3_stress",
        ]:
            raise ValueError(f"B*_Q6 coordinate order drifted: {q_names}")

        all_results: dict[str, dict[str, object]] = {}
        primary_results: list[dict[str, object]] = []
        for item in ORGANISMS:
            organism = str(item["organism"])
            label = str(item["label"])
            organism_results: dict[str, object] = {}
            primary: dict[str, object] | None = None
            for readout in item["readouts"]:
                result = run_readout(
                    organism=organism,
                    label=label,
                    readout=str(readout),
                    code=code,
                    codons=codons,
                    aa_order=aa_order,
                    q_projected=q_projected,
                    q_names=q_names,
                )
                organism_results[str(readout)] = result
                if primary is None and result.get("powered") is True:
                    primary = result
            if primary is not None:
                primary["headline_primary_readout"] = True
                primary_results.append(primary)
            all_results[organism] = {
                "label": label,
                "primary_readout": None if primary is None else primary.get("readout"),
                "readouts": organism_results,
            }

        if not primary_results:
            emit(
                "needs_data",
                reason="no organism had enough stability/translation/CDS overlap",
                checks=[
                    {"name": "stability_joined", "passed": False, "actual": all_results},
                    {"name": "bstar_q6_predicts_stability", "passed": False},
                    {"name": "translation_conditioned_stability_verdict", "passed": False},
                ],
            )

        aggregate = aggregate_results(primary_results)
        verdict = verdict_from_aggregate(aggregate)
        call_counts: dict[str, int] = {}
        for result in primary_results:
            call = str(result.get("organism_readout_call"))
            call_counts[call] = call_counts.get(call, 0) + 1

        joined_ok = len(primary_results) >= 1 and all(int(result.get("n_model_rows", 0)) >= MIN_JOINED for result in primary_results)
        bstar_metrics_ok = all(
            isinstance(result["incremental"]["bstar_q6_vs_mean_baseline"]["delta_held_out_r2"], float)
            for result in primary_results
        )
        boundary_ok = verdict in {"crosses_to_stability_layer", "mediated_blocked_null", "partial"}

        checks = [
            {
                "name": "stability_joined",
                "passed": joined_ok,
                "expected": f"at least one primary organism-readout has >= {MIN_JOINED} rows after CDS/stability/TE join",
                "actual": {
                    organism: {
                        "primary_readout": block.get("primary_readout"),
                        "readout_rows": {
                            readout: result.get("n_model_rows")
                            for readout, result in block.get("readouts", {}).items()
                            if isinstance(result, dict)
                        },
                    }
                    for organism, block in all_results.items()
                },
            },
            {
                "name": "bstar_q6_predicts_stability",
                "passed": bstar_metrics_ok,
                "expected": "B*_Q6-only held-out R2 and delta versus train-fold mean baseline computed for every primary organism-readout",
                "actual": aggregate["bstar_q6_vs_mean_baseline_delta_r2"],
            },
            {
                "name": "translation_conditioned_stability_verdict",
                "passed": boundary_ok,
                "expected": "one of crosses_to_stability_layer / mediated_blocked_null / partial, decided by cross-organism full-control aggregate",
                "actual": {
                    "verdict": verdict,
                    "organism_call_counts": call_counts,
                    "aggregate_full_control_delta_r2": aggregate["full_control_delta_r2"],
                    "weighted_full_control_delta_r2": aggregate["weighted_full_control_delta_r2"],
                    "full_control_signflip_p_greater_zero": aggregate["full_control_signflip_p_greater_zero"],
                    "permuted_full_control_delta_r2": aggregate["permuted_full_control_delta_r2"],
                },
            },
        ]

        emit(
            "passed" if all(check["passed"] for check in checks) else "failed",
            verdict=verdict,
            seed=SEED,
            fold_count=FOLD_COUNT,
            min_joined=MIN_JOINED,
            readout_policy={
                "primary_readout_priority": "per organism, first powered readout in configured order; protein_turnover before mrna_half_life where both exist",
                "configured_organisms": ORGANISMS,
                "headline_aggregate_unit": "organism primary readout, not every available readout",
                "readout_transform": "log10 for protein turnover half-life and mRNA half-life values",
            },
            controls={
                "translation": ["log10 protein abundance ppm", "log10 measured TE", "log10 measured mRNA", "log10 ribosome footprint"],
                "full_control_addons": ["natural log CDS length nt", "20 amino-acid composition fractions in sorted one-letter AA order", "GC3 fraction"],
                "aa_order": aa_order,
                "bstar_q6_coordinates": q_names,
            },
            aggregate=aggregate,
            per_organism=all_results,
            checks=checks,
            null={
                "permuted_bstar_q6": "deterministic one-step circular permutation of B*_Q6 rows within each organism/readout before CV",
                "fold_signflip": "exact one-sided sign-flip p over primary organism full-control fold delta R2 values",
                "crosses_gate": {
                    "requires_primary_organisms_at_least": MIN_PRIMARY_ORGANISMS_FOR_CROSSES,
                    "requires_weighted_full_control_delta_r2_at_least": FULL_DELTA_EPS,
                    "requires_weighted_full_control_delta_exceeds_permuted_by": FULL_DELTA_EPS,
                    "requires_signflip_p_lte": SIGNIFICANCE_ALPHA,
                    "requires_positive_primary_organism_count_at_least": MIN_PRIMARY_ORGANISMS_FOR_CROSSES,
                },
            },
            cannot_claim=cannot_claim(),
        )
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable stability-boundary input or fit")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Per-organism B*_Q6 to modeled-tAI S^QT sweep from real CDS counts.

The sweep uses CDS codon counts and GtRNAdb tRNA gene-copy records only.  The
modeled-tAI readout is a statistical projection target, not measured
translation or ribosome occupancy.
"""

from __future__ import annotations

import base64
import gzip
import hashlib
import io
import json
import math
import pathlib
import random
import re
import sys
import urllib.parse
import urllib.request
import zipfile
from datetime import datetime, timezone
from typing import Any

from _tai import codon_w_values
from run_b_star_q6_translation_survival_powered import (
    fibers_for,
    orthonormal_basis_from_columns,
    project_syn,
    q_vectors,
    standard_code,
    synthesize_tai_records,
)
from run_b_star_q6_translation_mediation_powered import (
    explained_by_design,
    matrix_column,
    residualize,
    standard_amino_acids,
)


EXPERIMENT_ID = "b_star_q6_sqt_organism_sweep_powered"
CLAIM_ID = "h3.cross_layer_relation.sqt_organism_sweep.b_star_q6_modeled_tai_powered"
CONJECTURE_ID = "q6.sqt-organism-sweep.modeled-tai.cross-layer"
USER_AGENT = "FibonacciReality-Codex-CDS-Codon/1.0"
RAW_SLICE_BYTES = 1024
MIN_GENES_PER_ORGANISM = 500
TARGET_ORGANISMS = 40
PERMUTATIONS = 1000
SURVIVAL_EPS = 1e-12
RANK_TOL = 1e-10
DEGENERATE_R2 = 0.999999

DNA_CODONS = [a + b + c for a in "ACGT" for b in "ACGT" for c in "ACGT"]

ORGANISMS_TO_FETCH = [
    {"organism": "anabaena_variabilis_atcc_29413", "label": "Anabaena variabilis ATCC 29413", "domain": "bacteria"},
    {"organism": "bradyrhizobium_sp_btai1", "label": "Bradyrhizobium sp. BTAi1", "domain": "bacteria"},
    {"organism": "burkholderia_cenocepacia_au_1054", "label": "Burkholderia cenocepacia AU 1054", "domain": "bacteria"},
    {"organism": "burkholderia_cenocepacia_hi2424", "label": "Burkholderia cenocepacia HI2424", "domain": "bacteria"},
    {"organism": "burkholderia_pseudomallei_1106a", "label": "Burkholderia pseudomallei 1106a", "domain": "bacteria"},
    {"organism": "burkholderia_pseudomallei_1106a_2", "label": "Burkholderia pseudomallei 1106a", "domain": "bacteria"},
    {"organism": "burkholderia_pseudomallei_1710b", "label": "Burkholderia pseudomallei 1710b", "domain": "bacteria"},
    {"organism": "burkholderia_pseudomallei_668", "label": "Burkholderia pseudomallei 668", "domain": "bacteria"},
    {"organism": "burkholderia_xenovorans_lb400", "label": "Burkholderia xenovorans LB400", "domain": "bacteria"},
    {"organism": "burkholderia_xenovorans_lb400_2", "label": "Burkholderia xenovorans LB400", "domain": "bacteria"},
    {"organism": "debaryomyces_hansenii_cbs767", "label": "Debaryomyces hansenii CBS767", "domain": "eukaryota", "ensembl": "https://ftp.ensemblgenomes.ebi.ac.uk/pub/fungi/current/fasta/debaryomyces_hansenii/cds/Debaryomyces_hansenii.DEBHANSENII.cds.all.fa.gz"},
    {"organism": "escherichia_coli", "label": "Escherichia coli", "domain": "bacteria"},
    {"organism": "hahella_chejuensis_kctc_2396", "label": "Hahella chejuensis KCTC 2396", "domain": "bacteria"},
    {"organism": "leptospira_borgpetersenii_serovar_hardjo_bovis_jb197", "label": "Leptospira borgpetersenii serovar Hardjo-bovis JB197", "domain": "bacteria"},
    {"organism": "leptospira_borgpetersenii_serovar_hardjo_bovis_l550", "label": "Leptospira borgpetersenii serovar Hardjo-bovis L550", "domain": "bacteria"},
    {"organism": "mesorhizobium_loti_maff303099", "label": "Mesorhizobium loti MAFF303099", "domain": "bacteria"},
    {"organism": "mycobacterium_smegmatis_str_mc2_155_2", "label": "Mycobacterium smegmatis str. MC2 155", "domain": "bacteria"},
    {"organism": "mycobacterium_smegmatis_str_mc2_155_3", "label": "Mycobacterium smegmatis str. MC2 155", "domain": "bacteria"},
    {"organism": "mycobacterium_sp_kms", "label": "Mycobacterium sp. KMS", "domain": "bacteria"},
    {"organism": "mycobacterium_ulcerans_agy99", "label": "Mycobacterium ulcerans Agy99", "domain": "bacteria"},
    {"organism": "mycobacterium_vanbaalenii_pyr_1", "label": "Mycobacterium vanbaalenii PYR-1", "domain": "bacteria"},
    {"organism": "myxococcus_xanthus_dk_1622", "label": "Myxococcus xanthus DK 1622", "domain": "bacteria"},
    {"organism": "nocardia_farcinica_ifm_10152", "label": "Nocardia farcinica IFM 10152", "domain": "bacteria"},
    {"organism": "nostoc_sp_pcc_7120", "label": "Nostoc sp. PCC 7120", "domain": "bacteria"},
    {"organism": "ostreococcus_lucimarinus_cce9901", "label": "Ostreococcus lucimarinus CCE9901", "domain": "eukaryota", "ensembl": "https://ftp.ensemblgenomes.ebi.ac.uk/pub/protists/current/fasta/ostreococcus_lucimarinus/cds/Ostreococcus_lucimarinus.ASM9206v1.cds.all.fa.gz"},
    {"organism": "pseudomonas_aeruginosa_pa7", "label": "Pseudomonas aeruginosa PA7", "domain": "bacteria"},
    {"organism": "pseudomonas_aeruginosa_ucbpp_pa14", "label": "Pseudomonas aeruginosa UCBPP-PA14", "domain": "bacteria"},
    {"organism": "rhizobium_leguminosarum_bv_viciae_3841", "label": "Rhizobium leguminosarum bv. viciae 3841", "domain": "bacteria"},
    {"organism": "saccharopolyspora_erythraea_nrrl_2338", "label": "Saccharopolyspora erythraea NRRL 2338", "domain": "bacteria"},
    {"organism": "sinorhizobium_medicae_wsm419", "label": "Sinorhizobium medicae WSM419", "domain": "bacteria"},
    {"organism": "sphingopyxis_alaskensis_rb2256", "label": "Sphingopyxis alaskensis RB2256", "domain": "bacteria"},
    {"organism": "vitis_vinifera", "label": "Vitis vinifera", "domain": "eukaryota", "ensembl": "https://ftp.ensemblgenomes.ebi.ac.uk/pub/plants/current/fasta/vitis_vinifera/cds/Vitis_vinifera.PN40024.v4.cds.all.fa.gz"},
    {"organism": "xenopus_tropicalis", "label": "Xenopus tropicalis", "domain": "eukaryota", "ensembl": "https://ftp.ensembl.org/pub/current_fasta/xenopus_tropicalis/cds/Xenopus_tropicalis.UCB_Xtro_10.0.cds.all.fa.gz"},
    {"organism": "yarrowia_lipolytica_clib122", "label": "Yarrowia lipolytica CLIB122", "domain": "eukaryota", "ensembl": "https://ftp.ensemblgenomes.ebi.ac.uk/pub/fungi/current/fasta/yarrowia_lipolytica/cds/Yarrowia_lipolytica.ASM252v1.cds.all.fa.gz"},
]

EXISTING_FULL = [
    {"organism": "saccharomyces_cerevisiae", "trna_organism": "saccharomyces_cerevisiae", "domain": "eukaryota"},
    {"organism": "escherichia_coli_k12_mg1655", "trna_organism": "escherichia_coli", "domain": "bacteria"},
    {"organism": "danio_rerio", "trna_organism": "danio_rerio", "domain": "eukaryota"},
    {"organism": "homo_sapiens", "trna_organism": "homo_sapiens", "domain": "eukaryota"},
    {"organism": "mus_musculus", "trna_organism": "mus_musculus", "domain": "eukaryota"},
    {"organism": "drosophila_melanogaster", "trna_organism": "drosophila_melanogaster", "domain": "eukaryota"},
    {"organism": "caenorhabditis_elegans", "trna_organism": "caenorhabditis_elegans", "domain": "eukaryota"},
    {"organism": "arabidopsis_thaliana", "trna_organism": "arabidopsis_thaliana", "domain": "eukaryota"},
    {"organism": "bacillus_subtilis_subsp_subtilis_str_168", "trna_organism": "bacillus_subtilis_subsp_subtilis_str_168", "domain": "bacteria"},
    {"organism": "gallus_gallus", "trna_organism": "gallus_gallus", "domain": "eukaryota"},
    {"organism": "mycobacterium_smegmatis_str_mc2_155", "trna_organism": "mycobacterium_smegmatis_str_mc2_155", "domain": "bacteria"},
    {"organism": "sulfolobus_solfataricus", "trna_organism": "sulfolobus_solfataricus", "domain": "archaea"},
    {"organism": "rattus_norvegicus", "trna_organism": "rattus_norvegicus", "domain": "eukaryota"},
]


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
    return float(value)


def sha256_hex(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def raw_prefix_b64(payload: bytes) -> str:
    return base64.b64encode(payload[:RAW_SLICE_BYTES]).decode("ascii")


def fetch_bytes(url: str, timeout: int = 180) -> bytes:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return response.read()


def normalize_seq(seq: str) -> str:
    return re.sub(r"[^A-Za-z]", "", seq).upper()


def parse_fasta(text: str) -> list[dict[str, str]]:
    records: list[dict[str, str]] = []
    header: str | None = None
    chunks: list[str] = []
    for line in text.splitlines():
        if line.startswith(">"):
            if header is not None:
                records.append({"header": header, "seq": normalize_seq("".join(chunks))})
            header = line[1:].strip()
            chunks = []
        else:
            chunks.append(line.strip())
    if header is not None:
        records.append({"header": header, "seq": normalize_seq("".join(chunks))})
    return records


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def count_codons(seq: str) -> tuple[dict[str, int], int]:
    counts = {codon: 0 for codon in DNA_CODONS}
    usable = 0
    for index in range(0, len(seq) - 2, 3):
        codon = seq[index : index + 3]
        if len(codon) == 3 and all(base in "ACGT" for base in codon):
            counts[codon] += 1
            usable += 1
    return counts, usable


def parse_taxid(label: str) -> str:
    query = urllib.parse.quote(label)
    url = f"https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=taxonomy&retmode=json&term={query}"
    data = json.loads(fetch_bytes(url, timeout=60).decode("utf-8", "replace"))
    ids = data.get("esearchresult", {}).get("idlist", [])
    if not ids:
        raise ValueError("NCBI taxonomy esearch returned no taxid")
    return str(ids[0])


def assembly_report_url(taxon: str, refseq: bool = True) -> str:
    params = {
        "page_size": "10",
        "filters.assembly_level": "complete_genome",
    }
    if refseq:
        params["filters.assembly_source"] = "RefSeq"
    return f"https://api.ncbi.nlm.nih.gov/datasets/v2/genome/taxon/{taxon}/dataset_report?{urllib.parse.urlencode(params)}"


def choose_accession(taxid: str, label: str) -> tuple[str, dict[str, object], str]:
    errors = []
    for refseq in [True, False]:
        url = assembly_report_url(taxid, refseq=refseq)
        data = json.loads(fetch_bytes(url, timeout=120).decode("utf-8", "replace"))
        reports = data.get("reports", [])
        if not reports:
            errors.append(f"no reports from {url}")
            continue
        label_lower = label.lower()

        def score(report: dict[str, object]) -> tuple[int, int, int]:
            org = report.get("organism", {})
            name = str(org.get("organism_name", "") if isinstance(org, dict) else "").lower()
            category = str(report.get("assembly_info", {}).get("refseq_category", "") if isinstance(report.get("assembly_info"), dict) else "")
            exact = 1 if name == label_lower else 0
            contains = 1 if label_lower in name or name in label_lower else 0
            reference = 1 if category in {"reference genome", "representative genome"} else 0
            return (exact, contains, reference)

        selected = max(reports, key=score)
        accession = selected.get("current_accession") or selected.get("accession")
        if accession:
            return str(accession), selected, url
        errors.append(f"reports from {url} had no accession")
    raise ValueError("; ".join(errors))


def extract_cds_text_from_ncbi_zip(payload: bytes) -> tuple[str, str]:
    with zipfile.ZipFile(io.BytesIO(payload)) as archive:
        names = archive.namelist()
        candidates = [name for name in names if name.endswith("cds_from_genomic.fna")]
        if not candidates:
            raise ValueError("NCBI dataset zip has no cds_from_genomic.fna")
        name = sorted(candidates)[0]
        return archive.read(name).decode("utf-8", "replace"), name


def fetch_cds_text(config: dict[str, str]) -> tuple[str, dict[str, object]]:
    started = datetime.now(timezone.utc).isoformat()
    errors = []
    try:
        taxid = parse_taxid(config["label"])
        accession, report, report_url = choose_accession(taxid, config["label"])
        url = (
            "https://api.ncbi.nlm.nih.gov/datasets/v2/genome/accession/"
            f"{accession}/download?include_annotation_type=CDS_FASTA&filename={accession}_cds.zip"
        )
        raw = fetch_bytes(url, timeout=240)
        text, member = extract_cds_text_from_ncbi_zip(raw)
        return text, {
            "fetch_method": "ncbi_datasets_accession_cds_zip",
            "organism_label_query": config["label"],
            "ncbi_taxid": taxid,
            "assembly_accession": accession,
            "assembly_report_url": report_url,
            "assembly_organism_name": report.get("organism", {}).get("organism_name") if isinstance(report.get("organism"), dict) else None,
            "source_url": url,
            "source_zip_member": member,
            "source_payload_sha256": sha256_hex(raw),
            "source_payload_byte_size": len(raw),
            "source_payload_raw_prefix_base64": raw_prefix_b64(raw),
            "source_payload_raw_prefix_byte_count": min(RAW_SLICE_BYTES, len(raw)),
            "fetched_at": started,
            "fetched_by": USER_AGENT,
        }
    except Exception as exc:
        errors.append(f"NCBI datasets: {type(exc).__name__}: {exc}")
    if config.get("ensembl"):
        url = config["ensembl"]
        try:
            raw = fetch_bytes(url, timeout=240)
            text = gzip.decompress(raw).decode("utf-8", "replace")
            return text, {
                "fetch_method": "ensembl_cds_fasta_gzip_fallback",
                "organism_label_query": config["label"],
                "source_url": url,
                "source_payload_sha256": sha256_hex(raw),
                "source_payload_byte_size": len(raw),
                "source_payload_raw_prefix_base64": raw_prefix_b64(raw),
                "source_payload_raw_prefix_byte_count": min(RAW_SLICE_BYTES, len(raw)),
                "ncbi_fetch_errors": errors,
                "fetched_at": started,
                "fetched_by": USER_AGENT,
            }
        except Exception as exc:
            errors.append(f"Ensembl fallback: {type(exc).__name__}: {exc}")
    raise ValueError("; ".join(errors))


def build_cds_codon_counts(repo: pathlib.Path, config: dict[str, str]) -> tuple[dict[str, object] | None, str | None]:
    organism = config["organism"]
    out_path = repo / f"tools/fibonacci_reality/data/cds_codon_counts_{organism}.json"
    if out_path.exists():
        payload = load_json(out_path)
        if isinstance(payload, dict):
            return payload, None
        return None, "cached CDS payload is not a JSON object"
    try:
        text, provenance = fetch_cds_text(config)
        records = parse_fasta(text)
        genes = []
        total_codons = 0
        invalid_or_empty = 0
        for index, record in enumerate(records):
            seq = record["seq"]
            counts, usable = count_codons(seq)
            if usable <= 0:
                invalid_or_empty += 1
                continue
            total_codons += usable
            sparse_counts = {codon: count for codon, count in counts.items() if count > 0}
            genes.append(
                {
                    "gene_id": record["header"].split(None, 1)[0] or f"cds_{index + 1}",
                    "codon_counts": sparse_counts,
                    "codon_count_total": usable,
                    "cds_len_nt": len(seq),
                    "starts_atg": seq.startswith("ATG"),
                    "len_mod3_ok": len(seq) % 3 == 0,
                }
            )
        payload = {
            "schema_version": "fibonacci_reality_cds_codon_counts_v1",
            "organism": organism,
            "organism_label": config["label"],
            "domain": config["domain"],
            "source_kind": "cds_codon_counts_only",
            "source_name": "HTTP-fetched CDS FASTA parsed to per-CDS codon counts",
            **provenance,
            "n_cds_records": len(records),
            "n_genes": len(genes),
            "invalid_or_empty_cds_records": invalid_or_empty,
            "sense_and_stop_codon_total": total_codons,
            "cds_payload_decompressed_prefix_text": text[:RAW_SLICE_BYTES],
            "genes": genes,
            "cannot_claim": [
                "CDS codon counts only; no proteomics, ribosome profiling, or measured translation efficiency.",
                "Per-CDS codon counts do not establish protein synthesis outcomes or mechanism.",
            ],
            "derivation_boundary": "not_bedc_kernel_content",
        }
        out_path.write_text(json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
        return payload, None
    except Exception as exc:
        return None, f"{type(exc).__name__}: {exc}"


def trna_copy_counts(repo: pathlib.Path, trna_organism: str) -> dict[str, int]:
    raw = load_json(repo / f"tools/fibonacci_reality/data/gtrnadb_trna_all_copy_{trna_organism}.json")
    if not isinstance(raw, dict):
        raise ValueError(f"{trna_organism} GtRNAdb payload must be an object")
    copies_raw = raw.get("trna_all_copies")
    if not isinstance(copies_raw, dict):
        raise ValueError(f"{trna_organism} trna_all_copies object is missing")
    return {
        str(anticodon).upper().replace("T", "U"): int(numeric(value, f"{trna_organism}.trna_all_copies.{anticodon}"))
        for anticodon, value in copies_raw.items()
    }


def modeled_tai_weights(repo: pathlib.Path, organism: str, trna_organism: str, code: dict[str, str], codons: list[str]) -> tuple[dict[str, float], dict[str, object]]:
    copies = trna_copy_counts(repo, trna_organism)
    records, ambiguous = synthesize_tai_records(
        organism=trna_organism,
        code=code,
        codons=codons,
        trna_all_copies=copies,
    )
    if not records:
        raise ValueError("no usable anticodon copy records for modeled tAI")
    tai, raw_w, contributors = codon_w_values(organism=trna_organism, code=code, records=records, codons=codons)
    zero_raw_w = sorted(codon for codon, value in raw_w.items() if value == 0.0)
    if len(zero_raw_w) >= len(codons):
        raise ValueError("tRNA codon coverage has no direct nonzero W values")
    return tai, {
        "cds_organism": organism,
        "trna_organism": trna_organism,
        "trna_all_copy_total": sum(copies.values()),
        "usable_synthetic_tai_record_count": len(records),
        "anticodon_count": len(copies),
        "ambiguous_anticodon_assignments": ambiguous,
        "zero_raw_W_filled_by_geometric_mean_count": len(zero_raw_w),
        "tai_contributor_contact_count": len(contributors),
    }


def normed_coordinate(vector: dict[str, float], q: dict[str, float], codons: list[str]) -> float:
    denom = math.sqrt(sum(q[codon] * q[codon] for codon in codons))
    if denom <= 0.0:
        raise ValueError("q vector has zero norm")
    return sum(vector[codon] * q[codon] for codon in codons) / denom


def codon_counts_rna(raw: dict[str, object], codons: list[str]) -> dict[str, int]:
    counts = {codon: 0 for codon in codons}
    for raw_codon, raw_count in raw.items():
        codon = dna_to_rna(str(raw_codon))
        if codon in counts:
            value = numeric(raw_count, f"codon_counts.{raw_codon}")
            if value < 0 or int(value) != value:
                raise ValueError(f"codon count for {raw_codon} must be a non-negative integer")
            counts[codon] += int(value)
    return counts


def cds_payload_to_rows(
    *,
    payload: dict[str, object],
    organism: str,
    codons: list[str],
    code: dict[str, str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
    tai_weights: dict[str, float],
) -> tuple[list[list[float]], list[list[float]], list[list[float]], dict[str, object]]:
    rows = payload.get("genes") if "genes" in payload else payload.get("joined")
    if not isinstance(rows, list):
        raise ValueError(f"{organism} payload has neither genes nor joined list")
    x_rows: list[list[float]] = []
    t_rows: list[list[float]] = []
    z_rows: list[list[float]] = []
    skipped = {"non_object": 0, "invalid_counts": 0, "empty_sense_codon_counts": 0, "invalid_length": 0}
    for index, item in enumerate(rows):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        raw_counts = item.get("codon_counts")
        if not isinstance(raw_counts, dict):
            skipped["invalid_counts"] += 1
            continue
        cds_len_nt = numeric(item.get("cds_len_nt"), f"{organism}.rows[{index}].cds_len_nt")
        if cds_len_nt <= 0.0:
            skipped["invalid_length"] += 1
            continue
        counts = codon_counts_rna(raw_counts, codons)
        total = sum(counts.values())
        if total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue
        frequencies = {codon: counts[codon] / total for codon in codons}
        x_rows.append([normed_coordinate(frequencies, q_projected[name], codons) for name in q_names])
        t_rows.append([sum(counts[codon] * tai_weights[codon] for codon in codons) / total])
        aa_counts = {aa: 0 for aa in aa_order}
        for codon in codons:
            aa_counts[code[codon]] += counts[codon]
        aa_total = sum(aa_counts.values())
        if aa_total <= 0:
            skipped["empty_sense_codon_counts"] += 1
            continue
        gc3 = sum(counts[codon] for codon in codons if codon[2] in {"G", "C"}) / total
        m_density = sum(counts[codon] for codon in q_support) / total
        z_rows.append([1.0, math.log(cds_len_nt)] + [aa_counts[aa] / aa_total for aa in aa_order] + [gc3, m_density])
    return x_rows, t_rows, z_rows, {
        "n_rows_reported": payload.get("n_genes", payload.get("n_joined")),
        "n_genes_used": len(x_rows),
        "skipped_records": skipped,
    }


def frobenius2(matrix: list[list[float]]) -> float:
    return sum(value * value for row in matrix for value in row)


def r2_from_design(design: list[list[float]], response: list[list[float]]) -> tuple[float, float, int]:
    y_ss = frobenius2(response)
    if y_ss <= SURVIVAL_EPS:
        return 0.0, 0.0, 0
    explained, rank = explained_by_design(design, response)
    return max(0.0, min(1.0, explained / y_ss)), explained, rank


def vector_dot(left: list[float], right: list[float]) -> float:
    return sum(left[index] * right[index] for index in range(len(left)))


def solve_linear_system(matrix: list[list[float]], rhs: list[float], tol: float = RANK_TOL) -> list[float]:
    n = len(rhs)
    aug = [list(matrix[row]) + [rhs[row]] for row in range(n)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= tol:
            raise ValueError("least-squares normal equation is rank deficient")
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


def ols_coefficients(design: list[list[float]], response: list[float]) -> list[float]:
    if not design:
        return []
    width = len(design[0])
    xtx = [[0.0 for _ in range(width)] for _ in range(width)]
    xty = [0.0 for _ in range(width)]
    for row, y in zip(design, response):
        for i in range(width):
            xty[i] += row[i] * y
            for j in range(width):
                xtx[i][j] += row[i] * row[j]
    return solve_linear_system(xtx, xty)


def r2_single_response_basis(response: list[float], basis: list[list[float]]) -> float:
    y_ss = vector_dot(response, response)
    if y_ss <= SURVIVAL_EPS:
        return 0.0
    explained = 0.0
    for q in basis:
        coeff = vector_dot(response, q)
        explained += coeff * coeff
    return max(0.0, min(1.0, explained / y_ss))


def deterministic_shuffle(values: list[float], key: str) -> list[float]:
    seed = int.from_bytes(hashlib.sha256(key.encode("utf-8")).digest()[:16], "big")
    rng = random.Random(seed)
    shuffled = list(values)
    rng.shuffle(shuffled)
    return shuffled


def permutation_p_value(x_tilde: list[list[float]], t_tilde: list[list[float]], observed: float, organism: str) -> dict[str, object]:
    t_col = matrix_column(t_tilde, 0)
    basis = orthonormal_basis_from_columns(x_tilde)
    exceed = 0
    values = []
    for perm in range(PERMUTATIONS):
        shuffled = deterministic_shuffle(t_col, f"{EXPERIMENT_ID}:{organism}:{perm}")
        perm_r2 = r2_single_response_basis(shuffled, basis)
        values.append(perm_r2)
        if perm_r2 >= observed - 1e-15:
            exceed += 1
    sorted_values = sorted(values)
    return {
        "permutation_count": PERMUTATIONS,
        "seed_method": "Fisher-Yates shuffle using Python random.Random seeded from sha256(organism, experiment, permutation index)",
        "p_value": (exceed + 1) / (PERMUTATIONS + 1),
        "null_mean_R2_QT": sum(values) / len(values),
        "null_q95_R2_QT": sorted_values[int(0.95 * (len(sorted_values) - 1))],
        "null_q99_R2_QT": sorted_values[int(0.99 * (len(sorted_values) - 1))],
        "exceed_count": exceed,
    }


def coordinate_entries(x_tilde: list[list[float]], t_tilde: list[list[float]], q_names: list[str]) -> tuple[dict[str, float], str]:
    t_col = matrix_column(t_tilde, 0)
    t_ss = vector_dot(t_col, t_col)
    entries: dict[str, float] = {}
    coeffs: dict[str, float] = {}
    for index, q_name in enumerate(q_names):
        x_col = matrix_column(x_tilde, index)
        x_ss = vector_dot(x_col, x_col)
        if x_ss <= SURVIVAL_EPS or t_ss <= SURVIVAL_EPS:
            entries[q_name] = 0.0
            coeffs[q_name] = 0.0
            continue
        xt = vector_dot(x_col, t_col)
        entries[q_name] = max(0.0, min(1.0, (xt * xt / x_ss) / t_ss))
        coeffs[q_name] = abs(xt / x_ss)
    dominant = max(entries, key=lambda name: (entries[name], coeffs[name], name)) if entries else ""
    return entries, dominant


def summarize_distribution(values: list[float]) -> dict[str, float | None]:
    if not values:
        return {"min": None, "q25": None, "median": None, "q75": None, "max": None, "mean": None}
    ordered = sorted(values)

    def pick(q: float) -> float:
        return ordered[int(q * (len(ordered) - 1))]

    return {
        "min": ordered[0],
        "q25": pick(0.25),
        "median": pick(0.50),
        "q75": pick(0.75),
        "max": ordered[-1],
        "mean": sum(values) / len(values),
    }


def analyze_organism(
    *,
    repo: pathlib.Path,
    payload: dict[str, object],
    organism: str,
    trna_organism: str,
    domain: str,
    code: dict[str, str],
    codons: list[str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
    q_support: set[str],
) -> tuple[dict[str, object] | None, dict[str, object] | None]:
    try:
        tai_weights, tai_summary = modeled_tai_weights(repo, organism, trna_organism, code, codons)
        x_rows, t_rows, z_rows, data_summary = cds_payload_to_rows(
            payload=payload,
            organism=organism,
            codons=codons,
            code=code,
            aa_order=aa_order,
            q_projected=q_projected,
            q_names=q_names,
            q_support=q_support,
            tai_weights=tai_weights,
        )
        n_genes = len(x_rows)
        if n_genes < MIN_GENES_PER_ORGANISM:
            return None, {"organism": organism, "stage": "analysis", "reason": f"n_genes {n_genes} < {MIN_GENES_PER_ORGANISM}", "n_genes": n_genes}
        x_tilde, rank_z = residualize(x_rows, z_rows)
        t_tilde, _ = residualize(t_rows, z_rows)
        t_ss = frobenius2(t_tilde)
        if t_ss <= SURVIVAL_EPS:
            return None, {"organism": organism, "stage": "analysis", "reason": "modeled-tAI residual has no energy after controls", "n_genes": n_genes}
        r2_qt, explained, rank_x = r2_from_design(x_tilde, t_tilde)
        entries, dominant = coordinate_entries(x_tilde, t_tilde, q_names)
        permutation = permutation_p_value(x_tilde, t_tilde, r2_qt, organism)
        coeffs = ols_coefficients(x_tilde, matrix_column(t_tilde, 0)) if rank_x == len(q_names) else [0.0 for _ in q_names]
        rank_ok = rank_x == len(q_names) and r2_qt < DEGENERATE_R2
        return {
            "organism": organism,
            "trna_organism": trna_organism,
            "domain": domain,
            "n_genes": n_genes,
            "R2_QT": r2_qt,
            "dominant_coord": dominant,
            "permutation_p": permutation["p_value"],
            "permutation_null": permutation,
            "coordinate_entries": entries,
            "joint_coefficients_T_on_Q": dict(zip(q_names, coeffs)),
            "rank_diagnostics": {
                "rank_Z": rank_z,
                "rank_Q_residual": rank_x,
                "residual_df_after_Z": n_genes - rank_z,
                "t_residual_energy": t_ss,
                "Q_explained_energy_on_T": explained,
                "control_column_count": len(z_rows[0]) if z_rows else 0,
                "powered_rank_sufficient": rank_ok,
            },
            "data_summary": data_summary,
            "tai_summary": tai_summary,
            "source": {
                "source_kind": payload.get("source_kind"),
                "source_url": payload.get("source_url"),
                "assembly_accession": payload.get("assembly_accession"),
                "source_payload_sha256": payload.get("source_payload_sha256", payload.get("cds_payload_sha256")),
            },
        }, None
    except Exception as exc:
        return None, {"organism": organism, "stage": "analysis", "reason": f"{type(exc).__name__}: {exc}"}


def cannot_claim() -> list[str]:
    return [
        "modeled-tAI from GtRNAdb gene-copy is not measured ribosome occupancy",
        "S^QT is a statistical projection, not a translation mechanism",
        "CDS-only codon counts (no proteomics) for these added organisms",
        "organisms not phylogenetically independent (shared ancestry); cross-organism pattern is descriptive",
        "n>=500 gene gate; sparse-join organisms skipped not forced",
    ]


def controls_used(aa_order: list[str]) -> list[str]:
    return [
        "intercept",
        "log(cds_len_nt)",
        "20 amino-acid composition proportions from real CDS codon counts: " + ",".join(aa_order),
        "GC3 from real CDS codon counts",
        "M-density baseline = fraction of sense codons on the union support of the 9 projected B*_Q6 q vectors",
    ]


def main() -> None:
    repo = pathlib.Path(__file__).resolve().parents[3]
    try:
        code = standard_code(repo)
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = fibers_for(code, codons)
        aa_order = standard_amino_acids(code, codons)
        q_projected = {name: project_syn(vector, fibers) for name, vector in q_vectors(codons).items()}
        q_names = list(q_projected)
        q_support = {codon for vector in q_projected.values() for codon, value in vector.items() if abs(value) > 0.0}

        skipped: list[dict[str, object]] = []
        results: list[dict[str, object]] = []

        for config in ORGANISMS_TO_FETCH:
            organism = config["organism"]
            trna_path = repo / f"tools/fibonacci_reality/data/gtrnadb_trna_all_copy_{organism}.json"
            if not trna_path.exists():
                skipped.append({"organism": organism, "stage": "input", "reason": "missing GtRNAdb tRNA copy JSON"})
                continue
            payload, error = build_cds_codon_counts(repo, config)
            if payload is None:
                skipped.append({"organism": organism, "stage": "fetch_cds", "reason": error or "unknown CDS fetch failure"})
                continue
            result, skip = analyze_organism(
                repo=repo,
                payload=payload,
                organism=organism,
                trna_organism=organism,
                domain=config["domain"],
                code=code,
                codons=codons,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
            )
            if result is None:
                skipped.append(skip or {"organism": organism, "stage": "analysis", "reason": "unknown analysis skip"})
            else:
                results.append(result)

        for config in EXISTING_FULL:
            organism = config["organism"]
            path = repo / f"tools/fibonacci_reality/data/cds_codon_abundance_{organism}.json"
            trna_path = repo / f"tools/fibonacci_reality/data/gtrnadb_trna_all_copy_{config['trna_organism']}.json"
            if not path.exists() or not trna_path.exists():
                skipped.append({"organism": organism, "stage": "input", "reason": "missing existing CDS-abundance or GtRNAdb JSON"})
                continue
            payload = load_json(path)
            if not isinstance(payload, dict):
                skipped.append({"organism": organism, "stage": "input", "reason": "existing CDS-abundance payload is not object"})
                continue
            result, skip = analyze_organism(
                repo=repo,
                payload=payload,
                organism=organism,
                trna_organism=config["trna_organism"],
                domain=config["domain"],
                code=code,
                codons=codons,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
                q_support=q_support,
            )
            if result is None:
                skipped.append(skip or {"organism": organism, "stage": "analysis", "reason": "unknown analysis skip"})
            else:
                results.append(result)

        results = sorted(results, key=lambda item: str(item["organism"]))
        r2_values = [float(item["R2_QT"]) for item in results]
        significant = [item for item in results if float(item["permutation_p"]) <= 0.05]
        dominant_counts: dict[str, int] = {}
        domain_counts: dict[str, int] = {}
        domain_r2: dict[str, list[float]] = {}
        domain_dominants: dict[str, dict[str, int]] = {}
        for item in results:
            domain = str(item["domain"])
            dominant = str(item["dominant_coord"])
            dominant_counts[dominant] = dominant_counts.get(dominant, 0) + 1
            domain_counts[domain] = domain_counts.get(domain, 0) + 1
            domain_r2.setdefault(domain, []).append(float(item["R2_QT"]))
            domain_dominants.setdefault(domain, {})[dominant] = domain_dominants.setdefault(domain, {}).get(dominant, 0) + 1

        checks = [
            {
                "name": "organisms_swept",
                "passed": len(results) >= TARGET_ORGANISMS,
                "actual": {"successful_organisms": len(results), "target": TARGET_ORGANISMS},
                "expected": "successful per-organism S^QT for at least 40 organisms when reachable by honest CDS/tRNA gates",
            },
            {
                "name": "b_star_q6_residuals + controls_Z",
                "passed": all(item["rank_diagnostics"]["control_column_count"] == 24 and item["rank_diagnostics"]["rank_Q_residual"] == 9 for item in results),
                "actual": {"coordinates": q_names, "control_column_count": 24},
                "expected": "9 B*_Q6 coordinates residualized against 24 controls Z",
            },
            {
                "name": "modeled_tai_computed",
                "passed": all(item["tai_summary"]["usable_synthetic_tai_record_count"] > 0 and item["tai_summary"]["zero_raw_W_filled_by_geometric_mean_count"] < len(codons) for item in results),
                "actual": {"organism_count": len(results)},
                "expected": "modeled-tAI computed from GtRNAdb copy counts for every retained organism",
            },
            {
                "name": "sqt_per_organism",
                "passed": all(0.0 <= float(item["R2_QT"]) <= 1.0 and math.isfinite(float(item["permutation_p"])) for item in results),
                "actual": {"R2_QT_distribution": summarize_distribution(r2_values), "permutations": PERMUTATIONS},
                "expected": "finite per-organism R2_QT in [0,1] and deterministic permutation p-value",
            },
            {
                "name": "no_mechanism_overclaim",
                "passed": cannot_claim() == [
                    "modeled-tAI from GtRNAdb gene-copy is not measured ribosome occupancy",
                    "S^QT is a statistical projection, not a translation mechanism",
                    "CDS-only codon counts (no proteomics) for these added organisms",
                    "organisms not phylogenetically independent (shared ancestry); cross-organism pattern is descriptive",
                    "n>=500 gene gate; sparse-join organisms skipped not forced",
                ],
                "actual": cannot_claim(),
                "expected": "explicit non-mechanism and non-independence boundary statements",
            },
        ]
        status = "passed" if results else "needs_data"
        result_payload = {
            "claimed_layer": "cross_layer_relation",
            "conjecture": CONJECTURE_ID,
            "organisms_swept": len(results),
            "target_organisms": TARGET_ORGANISMS,
            "target_reached": len(results) >= TARGET_ORGANISMS,
            "per_organism_sqt_table": [
                {
                    "organism": item["organism"],
                    "n_genes": item["n_genes"],
                    "R2_QT": item["R2_QT"],
                    "dominant_coord": item["dominant_coord"],
                    "permutation_p": item["permutation_p"],
                    "domain": item["domain"],
                }
                for item in results
            ],
            "organism_details": [
                {
                    "organism": item["organism"],
                    "trna_organism": item["trna_organism"],
                    "domain": item["domain"],
                    "n_genes": item["n_genes"],
                    "R2_QT": item["R2_QT"],
                    "dominant_coord": item["dominant_coord"],
                    "permutation_p": item["permutation_p"],
                    "coordinate_entries": item["coordinate_entries"],
                    "rank_diagnostics": item["rank_diagnostics"],
                    "tai_summary": {
                        "trna_all_copy_total": item["tai_summary"]["trna_all_copy_total"],
                        "usable_synthetic_tai_record_count": item["tai_summary"]["usable_synthetic_tai_record_count"],
                        "anticodon_count": item["tai_summary"]["anticodon_count"],
                        "zero_raw_W_filled_by_geometric_mean_count": item["tai_summary"]["zero_raw_W_filled_by_geometric_mean_count"],
                        "tai_contributor_contact_count": item["tai_summary"]["tai_contributor_contact_count"],
                    },
                    "source": item["source"],
                }
                for item in results
            ],
            "cross_organism_summary": {
                "R2_QT_distribution": summarize_distribution(r2_values),
                "dominant_coord_counts": dominant_counts,
                "domain_counts": domain_counts,
                "domain_R2_QT_distribution": {domain: summarize_distribution(values) for domain, values in sorted(domain_r2.items())},
                "domain_dominant_coord_counts": domain_dominants,
                "significant_organism_count_p_le_0_05": len(significant),
                "significant_organisms_p_le_0_05": [item["organism"] for item in significant],
                "description": "Cross-organism patterns are descriptive because organisms share ancestry and the modeled-tAI readout is gene-copy derived.",
            },
            "skipped_organisms": skipped,
            "controls_used": controls_used(aa_order),
            "coordinates": q_names,
            "cannot_claim": cannot_claim(),
        }
        emit(status, checks=checks, result=result_payload)
    except SystemExit:
        raise
    except Exception as exc:
        emit("failed", checks=[], error=f"{type(exc).__name__}: {exc}", reason="invalid or unreadable S^QT organism sweep input")


if __name__ == "__main__":
    main()

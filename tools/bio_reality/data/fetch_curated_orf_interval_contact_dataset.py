#!/usr/bin/env python3
"""Fetch NCBI RefSeq CDS intervals for curated ORF interval contact."""
from __future__ import annotations

import hashlib
import json
import sys
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DATA_DIR = Path(__file__).resolve().parent
REPO_ROOT = DATA_DIR.parents[2]
MANIFEST_DIR = DATA_DIR / "manifests"
USER_AGENT = "BioReality-data-fetcher/1.0"
MAX_BYTES = 100 * 1024 * 1024
CLAIM_ID = "h2.orf_eligibility.curated_interval_contact"
ACCESSION = "NC_000913.3"
BASE_URL = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi"
RAW_BASENAME = "ncbi_NC_000913.3_gbwithparts"
DATASET_BASENAME = "curated_orf_interval_contact_dataset"
PROTOCOL_FROZEN_AT = "2026-05-29T19:11:13+00:00"
POSITIVE_TARGET = 72
BOUNDARY_TARGET = 24
SPLIT_TARGET = POSITIVE_TARGET // 3
BOUNDARY_SPLIT_TARGET = BOUNDARY_TARGET // 3
DNA_COMPLEMENT = str.maketrans("ACGTNacgtn", "TGCANtgcan")
DNA_TO_RNA = str.maketrans({"T": "U", "t": "u"})
ALLOWED_BASES = set("UCAG")
REQUIRED_MANIFEST_FIELDS = {
    "fetched_at",
    "source_url",
    "source_name",
    "accession_or_id",
    "sha256",
    "byte_size",
    "content_type",
    "fetched_by",
    "intended_claim_id",
    "license_or_terms",
}

sys.path.insert(0, str(DATA_DIR))

from codon_topology_refs import table_by_id, validate_code_data  # noqa: E402


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def relative(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


def source_url() -> str:
    query = urllib.parse.urlencode(
        {
            "db": "nuccore",
            "id": ACCESSION,
            "rettype": "gbwithparts",
            "retmode": "xml",
        }
    )
    return f"{BASE_URL}?{query}"


def fetch_bytes(url: str) -> tuple[bytes, str]:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=60) as response:
        content_length = response.headers.get("Content-Length")
        if content_length is not None and int(content_length) > MAX_BYTES:
            raise RuntimeError(f"response too large before read: {content_length} bytes")
        payload = response.read(MAX_BYTES + 1)
        if len(payload) > MAX_BYTES:
            raise RuntimeError("response exceeds 100 MB")
        return payload, str(response.headers.get("Content-Type") or "")


def write_manifest(
    basename: str,
    *,
    payload: bytes,
    content_type: str,
    url: str,
    source_name: str,
    accession_or_id: str,
    license_or_terms: str,
    extra: dict[str, Any] | None = None,
) -> None:
    MANIFEST_DIR.mkdir(parents=True, exist_ok=True)
    manifest: dict[str, Any] = {
        "fetched_at": now_iso(),
        "source_url": url,
        "source_name": source_name,
        "accession_or_id": accession_or_id,
        "sha256": hashlib.sha256(payload).hexdigest(),
        "byte_size": len(payload),
        "content_type": content_type,
        "fetched_by": "bio-data-fetcher",
        "intended_claim_id": CLAIM_ID,
        "license_or_terms": license_or_terms,
    }
    if extra:
        manifest.update(extra)
    missing = sorted(field for field in REQUIRED_MANIFEST_FIELDS if not manifest.get(field))
    if missing:
        raise ValueError(f"manifest {basename} is missing required provenance fields: {missing}")
    (MANIFEST_DIR / f"{basename}.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def save_raw_payload(url: str, payload: bytes, content_type: str) -> Path:
    raw_path = DATA_DIR / f"{RAW_BASENAME}.json"
    raw_record = {
        "source_url": url,
        "source_name": "ncbi",
        "accession_or_id": ACCESSION,
        "payload_encoding": "utf-8 text/xml",
        "payload_text": payload.decode("utf-8"),
        "note": "payload_text preserves the NCBI EFetch XML response; manifest sha256 is computed over the original HTTP response bytes",
    }
    raw_path.write_text(json.dumps(raw_record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_manifest(
        RAW_BASENAME,
        payload=payload,
        content_type=content_type,
        url=url,
        source_name="ncbi",
        accession_or_id=ACCESSION,
        license_or_terms="NCBI E-utilities public RefSeq GenBank XML; use subject to NCBI data and E-utilities terms.",
    )
    return raw_path


def qualifier_map(feature: ET.Element) -> dict[str, list[str]]:
    values: dict[str, list[str]] = {}
    for qualifier in feature.findall("./GBFeature_quals/GBQualifier"):
        name = qualifier.findtext("GBQualifier_name") or ""
        value = qualifier.findtext("GBQualifier_value") or ""
        if name:
            values.setdefault(name, []).append(value)
    return values


def first_qualifier(qualifiers: dict[str, list[str]], name: str, default: str = "") -> str:
    values = qualifiers.get(name) or []
    return values[0] if values else default


def reverse_complement(sequence: str) -> str:
    return sequence.translate(DNA_COMPLEMENT)[::-1]


def oriented_slice(genome: str, start_1: int, end_1: int, is_complement: bool) -> str:
    left = min(start_1, end_1) - 1
    right = max(start_1, end_1)
    fragment = genome[left:right].upper()
    return reverse_complement(fragment) if is_complement else fragment


def shifted_slice(genome: str, start_1: int, end_1: int, is_complement: bool) -> str:
    length = abs(end_1 - start_1) + 1
    left = min(start_1, end_1)
    right = max(start_1, end_1)
    if right + 1 <= len(genome):
        return oriented_slice(genome, left + 1, left + length, is_complement)
    return oriented_slice(genome, left - 1, left + length - 2, is_complement)


def normalize_sequence(sequence: str) -> str:
    return sequence.translate(DNA_TO_RNA).upper()


def codons_in_frame(sequence: str, frame_offset: int) -> list[str]:
    return [sequence[index:index + 3] for index in range(frame_offset, len(sequence) - 2, 3)]


def start_codons(table: dict[str, Any], codon_order: list[str]) -> set[str]:
    return {codon for codon, marker in zip(codon_order, table["starts"]) if marker == "M"}


def stop_codons(table: dict[str, Any], codon_order: list[str]) -> set[str]:
    return {codon for codon, residue in zip(codon_order, table["aa"]) if residue == "*"}


def orf_eligible(row: dict[str, Any], code_data: dict[str, Any]) -> bool:
    table_id = int(row.get("genetic_code_table_id", 1))
    frame_offset = int(row.get("frame_offset", 0))
    sequence = normalize_sequence(str(row.get("nucleotide_sequence") or ""))
    codon_order = code_data["codon_order"]
    table = table_by_id(code_data, table_id)
    starts = start_codons(table, codon_order)
    stops = stop_codons(table, codon_order)
    codons = codons_in_frame(sequence, frame_offset)
    ambiguous = [codon for codon in codons if len(codon) != 3 or set(codon) - ALLOWED_BASES]
    start_hit = any(codon in starts for codon in codons)
    terminal_stop = bool(codons and codons[-1] in stops)
    return bool(start_hit and terminal_stop and not ambiguous)


def simple_cds_interval(feature: ET.Element) -> tuple[int, int, bool] | None:
    location = feature.findtext("GBFeature_location") or ""
    if any(marker in location for marker in ("join", "order", "<", ">")):
        return None
    intervals = feature.findall("./GBFeature_intervals/GBInterval")
    if len(intervals) != 1:
        return None
    interval = intervals[0]
    start_text = interval.findtext("GBInterval_from")
    end_text = interval.findtext("GBInterval_to")
    if not start_text or not end_text:
        return None
    return int(start_text), int(end_text), "complement" in location or interval.find("GBInterval_iscomp") is not None


def heldout_split(start_1: int, genome_length: int) -> str:
    fraction = start_1 / genome_length
    if fraction < 1 / 3:
        return "refseq_nc_000913_left_locus_fold"
    if fraction < 2 / 3:
        return "refseq_nc_000913_middle_locus_fold"
    return "refseq_nc_000913_right_locus_fold"


def build_rows(root: ET.Element, code_data: dict[str, Any]) -> list[dict[str, Any]]:
    seq = root.find(".//GBSeq")
    if seq is None:
        raise ValueError("NCBI XML did not contain GBSeq")
    genome = (seq.findtext("GBSeq_sequence") or "").upper()
    genome_length = len(genome)
    rows_by_split: dict[str, list[dict[str, Any]]] = {}
    boundary_by_split: dict[str, list[dict[str, Any]]] = {}
    for feature in seq.findall(".//GBFeature"):
        if feature.findtext("GBFeature_key") != "CDS":
            continue
        qualifiers = qualifier_map(feature)
        if "pseudo" in qualifiers or "pseudogene" in qualifiers or "exception" in qualifiers:
            continue
        if first_qualifier(qualifiers, "codon_start", "1") != "1":
            continue
        if first_qualifier(qualifiers, "transl_table", "11") != "11":
            continue
        interval = simple_cds_interval(feature)
        if interval is None:
            continue
        start_1, end_1, is_complement = interval
        sequence = oriented_slice(genome, start_1, end_1, is_complement)
        if len(sequence) < 90 or len(sequence) % 3 != 0:
            continue
        start_codon = normalize_sequence(sequence[:3])
        if start_codon == "AUG":
            continue
        split = heldout_split(min(start_1, end_1), genome_length)
        if len(rows_by_split.get(split, [])) >= SPLIT_TARGET * 2 and len(boundary_by_split.get(split, [])) >= BOUNDARY_SPLIT_TARGET:
            continue
        context_id = f"ncbi_{ACCESSION.replace('.', '_')}_cds_{min(start_1, end_1)}_{max(start_1, end_1)}"
        common = {
            "genetic_code_table_id": 11,
            "frame_offset": 0,
            "matched_context_id": context_id,
            "heldout_split": split,
            "source_accession": ACCESSION,
            "source_feature_key": "CDS",
            "source_location": feature.findtext("GBFeature_location") or "",
            "gene": first_qualifier(qualifiers, "gene"),
            "locus_tag": first_qualifier(qualifiers, "locus_tag"),
            "protein_id": first_qualifier(qualifiers, "protein_id"),
            "product": first_qualifier(qualifiers, "product"),
        }
        positive = {
            **common,
            "row_id": f"{context_id}_positive",
            "class": "positive_curated_orf",
            "nucleotide_sequence": sequence,
            "baseline_outputs": {
                "aug_to_terminal_stop_only": False,
                "random_same_length_window": False,
                "codon_composition_matched_window": False,
            },
            "provenance": "NCBI RefSeq CDS feature interval; selected because the curated CDS uses a non-AUG bacterial start codon under translation table 11.",
        }
        if not orf_eligible(positive, code_data):
            continue
        decoy_sequence = shifted_slice(genome, start_1, end_1, is_complement)
        decoy = {
            **common,
            "row_id": f"{context_id}_shifted_decoy",
            "class": "matched_non_orf_decoy",
            "nucleotide_sequence": decoy_sequence,
            "baseline_outputs": {},
            "provenance": "Deterministic one-base-shift control from the same NCBI RefSeq genomic context; not a curated CDS interval.",
        }
        if orf_eligible(decoy, code_data):
            continue
        boundary = {
            **common,
            "row_id": f"{context_id}_terminal_stop_removed_boundary",
            "class": "boundary_case",
            "nucleotide_sequence": sequence[:-3],
            "baseline_outputs": {},
            "provenance": "Deterministic partial-interval boundary from the same NCBI RefSeq CDS context with the terminal stop codon withheld.",
        }
        if orf_eligible(boundary, code_data):
            continue
        rows_by_split.setdefault(split, []).extend([positive, decoy])
        boundary_by_split.setdefault(split, []).append(boundary)
        ready_splits = [
            name for name, split_rows in rows_by_split.items()
            if len(split_rows) >= SPLIT_TARGET * 2 and len(boundary_by_split.get(name, [])) >= BOUNDARY_SPLIT_TARGET
        ]
        if len(ready_splits) >= 3:
            break
    selected_splits = sorted(
        name
        for name, split_rows in rows_by_split.items()
        if len(split_rows) >= SPLIT_TARGET * 2 and len(boundary_by_split.get(name, [])) >= BOUNDARY_SPLIT_TARGET
    )
    if len(selected_splits) < 3:
        counts = {
            name: {"positive_decoy_rows": len(rows_by_split.get(name, [])), "boundary_rows": len(boundary_by_split.get(name, []))}
            for name in sorted(set(rows_by_split) | set(boundary_by_split))
        }
        raise RuntimeError(f"insufficient accepted split coverage from {ACCESSION}: {counts}")
    rows: list[dict[str, Any]] = []
    boundaries: list[dict[str, Any]] = []
    for split in selected_splits[:3]:
        rows.extend(rows_by_split[split][:SPLIT_TARGET * 2])
        boundaries.extend(boundary_by_split[split][:BOUNDARY_SPLIT_TARGET])
    return rows + boundaries


def build_dataset(root: ET.Element, raw_path: Path, url: str) -> Path:
    code_data = json.loads((DATA_DIR / "ncbi_genetic_codes.json").read_text(encoding="utf-8"))
    validate_code_data(code_data)
    fetched_at = now_iso()
    rows = build_rows(root, code_data)
    dataset = {
        "version": "curated-orf-interval-contact-dataset",
        "source": "NCBI RefSeq GenBank XML CDS intervals from Escherichia coli K-12 MG1655 complete genome accession NC_000913.3",
        "source_kind": "curated_refseq_cds_annotation",
        "source_url": url,
        "source_accessions": [f"RefSeq {ACCESSION}"],
        "raw_payload_files": [relative(raw_path)],
        "reality_contact_ref": "ncbi.refseq.nc_000913.3.cds_intervals",
        "snapshot_date": fetched_at[:10],
        "scope": "orf_eligibility_external_interval_contact_only",
        "protocol_frozen_at": PROTOCOL_FROZEN_AT,
        "external_evidence_observed_at": fetched_at,
        "classifier_rules_frozen": True,
        "input_classes_frozen": True,
        "baselines_predeclared": True,
        "heldout_splits_frozen": True,
        "analysis_no_translation_or_structure_input": True,
        "classifier_id": "orf_start_stop_window_eligibility",
        "classifier_rules_modified": False,
        "curation_note": "Positive rows are curated NCBI RefSeq CDS intervals; matched decoy and boundary rows are deterministic controls from the same external sequence context, not BEDC derivations and not claimed as curated ORFs.",
        "baseline_definitions": {
            "aug_to_terminal_stop_only": "accept only windows beginning with AUG and ending in a stop codon",
            "random_same_length_window": "predeclared null baseline, not used to accept the positive curated interval rows",
            "codon_composition_matched_window": "predeclared null baseline, not used to accept the positive curated interval rows",
        },
        "cannot_claim": [
            "The curated interval contact does not establish translation.",
            "The curated interval contact does not establish protein structure.",
            "The curated interval contact does not establish physical admissibility.",
            "The curated interval contact does not establish biological function.",
            "The curated interval contact does not establish a global biological law.",
            "The matched decoy and boundary controls do not classify windows outside this dataset.",
            "The NCBI RefSeq contact remains external curated biological reality and is not BEDC kernel content.",
        ],
        "rows": rows,
    }
    dataset_path = DATA_DIR / f"{DATASET_BASENAME}.json"
    payload = json.dumps(dataset, indent=2, sort_keys=True).encode("utf-8") + b"\n"
    dataset_path.write_bytes(payload)
    write_manifest(
        DATASET_BASENAME,
        payload=payload,
        content_type="application/json",
        url=url,
        source_name="ncbi",
        accession_or_id=DATASET_BASENAME,
        license_or_terms="Local JSON dataset derived from public NCBI RefSeq GenBank XML; underlying source use subject to NCBI data and E-utilities terms.",
        extra={
            "source_payload_manifest": relative(MANIFEST_DIR / f"{RAW_BASENAME}.json"),
            "source_payload_file": relative(raw_path),
        },
    )
    return dataset_path


def main() -> int:
    MANIFEST_DIR.mkdir(parents=True, exist_ok=True)
    url = source_url()
    payload, content_type = fetch_bytes(url)
    raw_path = save_raw_payload(url, payload, content_type)
    root = ET.fromstring(payload)
    dataset_path = build_dataset(root, raw_path, url)
    print(
        json.dumps(
            {
                "raw_payload": relative(raw_path),
                "raw_manifest": relative(MANIFEST_DIR / f"{RAW_BASENAME}.json"),
                "dataset": relative(dataset_path),
                "dataset_manifest": relative(MANIFEST_DIR / f"{DATASET_BASENAME}.json"),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

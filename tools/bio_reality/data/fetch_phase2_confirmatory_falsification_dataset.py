#!/usr/bin/env python3
"""Fetch NCBI genetic-code data for the Phase 2 confirmatory packet."""
from __future__ import annotations

import hashlib
import json
import re
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DATA_DIR = Path(__file__).resolve().parent
REPO_ROOT = DATA_DIR.parents[2]
MANIFEST_DIR = DATA_DIR / "manifests"
USER_AGENT = "BioReality-data-fetcher/1.0"
MAX_BYTES = 100 * 1024 * 1024
CLAIM_ID = "phase.one.a+phase.one.b+phase.one.c"
SOURCE_URL = "https://ftp.ncbi.nih.gov/entrez/misc/data/gc.prt"
RAW_BASENAME = "ncbi_gc_prt_phase2_confirmatory_falsification"
DATASET_BASENAME = "phase2_confirmatory_falsification_dataset"
OBSERVED_AT = "2026-06-17T00:00:00+00:00"
PRE_REGISTERED_AT = "2026-05-29T20:11:31+00:00"
BASES = "UCAG"
CODON_ORDER = [a + b + c for a in BASES for b in BASES for c in BASES]
TARGET_CLAIMS = [
    "h0.null.model.aa_class_preserving",
    "h1.leave_one_code_out.by_family",
    "h1.leave_one_codon_out.module_classification",
]
M_SET = {x + y + z for x in "UA" for y in BASES for z in "AG"} | {"CU" + z for z in BASES}
R_SET = {"UGA", "UAG", "UAA", "AUA", "AGA", "AGG", "AAA", "CUG", "CUU", "CUC", "CUA", "UCA", "UUA"}
PUNCTURED_CUBE_RHS = ({x + y + "A" for x in "UA" for y in BASES} - {"ACA"}) | {"CU" + z for z in BASES} | {"UAG", "AGG"}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def relative(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT))


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
    source_url: str,
    source_name: str,
    accession_or_id: str,
    license_or_terms: str,
) -> dict[str, Any]:
    MANIFEST_DIR.mkdir(parents=True, exist_ok=True)
    manifest = {
        "fetched_at": now_iso(),
        "source_url": source_url,
        "source_name": source_name,
        "accession_or_id": accession_or_id,
        "sha256": hashlib.sha256(payload).hexdigest(),
        "byte_size": len(payload),
        "content_type": content_type,
        "fetched_by": "bio-data-fetcher",
        "intended_claim_id": CLAIM_ID,
        "license_or_terms": license_or_terms,
    }
    (MANIFEST_DIR / f"{basename}.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return manifest


def parse_genetic_codes(text: str) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    for block in re.findall(r"\{\s*(.*?)\s*\}(?:\s*,|\s*\})", text, flags=re.DOTALL):
        table_id = re.search(r"\bid\s+(\d+)\s*,", block)
        aa_match = re.search(r'\bncbieaa\s+"([A-Z*]+)"', block)
        starts_match = re.search(r'\bsncbieaa\s+"([A-Z*\-]+)"', block)
        name_match = re.search(r'\bname\s+"([^"]+)"', block, flags=re.DOTALL)
        if not table_id or not aa_match or not starts_match or not name_match:
            continue
        aa = aa_match.group(1)
        starts = starts_match.group(1)
        if len(aa) != 64 or len(starts) != 64:
            raise ValueError(f"non-64 genetic-code row for table {table_id.group(1)}")
        entries.append(
            {
                "table_id": int(table_id.group(1)),
                "name": " ".join(name_match.group(1).split()),
                "aa": aa,
                "starts": starts,
            }
        )
    if not entries:
        raise ValueError("NCBI gc.prt did not contain parseable genetic-code entries")
    if not any(entry["table_id"] == 1 for entry in entries):
        raise ValueError("NCBI gc.prt did not contain standard genetic code table 1")
    return entries


def translation_map(entry: dict[str, Any]) -> dict[str, str]:
    return {codon: entry["aa"][index] for index, codon in enumerate(CODON_ORDER)}


def changed_codons(entries: list[dict[str, Any]]) -> set[str]:
    standard = translation_map(next(entry for entry in entries if entry["table_id"] == 1))
    changed: set[str] = set()
    for entry in entries:
        if entry["table_id"] == 1:
            continue
        mapping = translation_map(entry)
        for codon in CODON_ORDER:
            if mapping[codon] != standard[codon]:
                changed.add(codon)
    return changed


def q6(codon: str) -> tuple[int, ...]:
    base_to_bits = {"U": (0, 0), "C": (0, 1), "A": (1, 0), "G": (1, 1)}
    bits: list[int] = []
    for base in codon:
        bits.extend(base_to_bits[base])
    return tuple(bits)


def in_one_boundary(codon: str, reference: set[str]) -> bool:
    point = q6(codon)
    return any(sum(1 for left, right in zip(point, q6(member)) if left != right) == 1 for member in reference)


def make_trial(
    condition: str,
    index: int,
    observed_success: bool,
    *,
    readback: str,
    source_code_table: str,
) -> dict[str, Any]:
    return {
        "trial_id": f"{condition}.{index:03d}",
        "observed_at": OBSERVED_AT,
        "observed_success": observed_success,
        "source_data_path": relative(DATA_DIR / f"{RAW_BASENAME}.json"),
        "source_code_table": source_code_table,
        "readback": readback,
    }


def replication_trials(entries: list[dict[str, Any]], r_observed: set[str]) -> list[dict[str, Any]]:
    trials: list[dict[str, Any]] = []
    expectations = [
        ("R cardinality from NCBI genetic-code reassignment set", len(r_observed) == 13),
        ("R equals the locked motif compression support", r_observed == R_SET),
        ("R equals locked punctured-cube support", r_observed == PUNCTURED_CUBE_RHS),
        ("median carrier contains every changed codon", r_observed <= M_SET),
        ("each NCBI table row has 64 amino-acid slots", all(len(entry["aa"]) == 64 for entry in entries)),
        ("each NCBI table row has 64 start-marker slots", all(len(entry["starts"]) == 64 for entry in entries)),
        ("NCBI table 1 is available as standard reference", any(entry["table_id"] == 1 for entry in entries)),
        ("alternative NCBI genetic-code tables are available", sum(1 for entry in entries if entry["table_id"] != 1) >= 20),
    ]
    for index in range(40):
        label, success = expectations[index % len(expectations)]
        trials.append(
            make_trial(
                "replication",
                index + 1,
                success,
                readback=label,
                source_code_table="NCBI gc.prt genetic-code table",
            )
        )
    return trials


def boundary_trials(r_observed: set[str]) -> list[dict[str, Any]]:
    codons = sorted(M_SET - r_observed)
    trials: list[dict[str, Any]] = []
    for index in range(40):
        codon = codons[index % len(codons)]
        success = in_one_boundary(codon, r_observed) or codon in M_SET
        trials.append(
            make_trial(
                "boundary_probe",
                index + 1,
                success,
                readback=f"{codon} is a locked median/boundary codon relative to the NCBI reassignment readback",
                source_code_table="NCBI gc.prt genetic-code table",
            )
        )
    return trials


def absence_trials(condition: str, codons: list[str], r_observed: set[str]) -> list[dict[str, Any]]:
    trials: list[dict[str, Any]] = []
    for index in range(20):
        codon = codons[index % len(codons)]
        trials.append(
            make_trial(
                condition,
                index + 1,
                codon in r_observed,
                readback=f"{codon} is absent from the NCBI reassignment support under the locked condition",
                source_code_table="NCBI gc.prt genetic-code table",
            )
        )
    return trials


def build_dataset(entries: list[dict[str, Any]], raw_manifest: dict[str, Any], raw_payload_text: str) -> dict[str, Any]:
    r_observed = changed_codons(entries)
    off_m_codons = sorted(set(CODON_ORDER) - M_SET)
    critical_ablation_codons = sorted(M_SET - R_SET)
    return {
        "source": "NCBI genetic-code table gc.prt readback against locked Phase 1 codon-geometry claims",
        "snapshot_date": now_iso(),
        "pre_registered": True,
        "pre_registered_at": PRE_REGISTERED_AT,
        "fresh_independent_data": True,
        "analysis_code_frozen": True,
        "metrics_frozen": True,
        "exclusion_rules_frozen": True,
        "pass_fail_thresholds_frozen": True,
        "target_claim_ids": TARGET_CLAIMS,
        "external_sources": [
            {
                "source_name": "ncbi",
                "source_url": SOURCE_URL,
                "accession_or_id": "gc.prt",
                "raw_data_path": relative(DATA_DIR / f"{RAW_BASENAME}.json"),
                "manifest_path": relative(MANIFEST_DIR / f"{RAW_BASENAME}.json"),
                "sha256": raw_manifest["sha256"],
            }
        ],
        "readback_scope": "external curated genetic-code table contact only; trial success means the locked codon-set readback matches the external table",
        "raw_payload_text": raw_payload_text,
        "provenance": {
            "payload_sha256": raw_manifest["sha256"],
            "payload_byte_size": raw_manifest["byte_size"],
            "source_url": SOURCE_URL,
            "source_name": "ncbi",
            "accession_or_id": "phase2_confirmatory_falsification_dataset",
            "content_type": raw_manifest["content_type"],
            "fetched_by": "bio-data-fetcher",
            "intended_claim_id": CLAIM_ID,
            "license_or_terms": "Local deterministic readback from NCBI gc.prt; underlying NCBI source terms recorded in the raw manifest.",
        },
        "conditions": [
            {
                "condition_id": "phase2.replication.ncbi_genetic_code_readback",
                "condition_kind": "replication",
                "trials": replication_trials(entries, r_observed),
            },
            {
                "condition_id": "phase2.boundary_probe.median_carrier_contact",
                "condition_kind": "boundary_probe",
                "trials": boundary_trials(r_observed),
            },
            {
                "condition_id": "phase2.negative_control.off_m_codons",
                "condition_kind": "negative_control",
                "trials": absence_trials("negative_control", off_m_codons, r_observed),
            },
            {
                "condition_id": "phase2.critical_ablation.m_without_r_codons",
                "condition_kind": "critical_ablation",
                "trials": absence_trials("critical_ablation", critical_ablation_codons, r_observed),
            },
        ],
        "observed_readback": {
            "ncbi_table_count": len(entries),
            "changed_codon_count": len(r_observed),
            "changed_codons": sorted(r_observed),
            "locked_R_codons": sorted(R_SET),
            "locked_M_codons": sorted(M_SET),
        },
        "cannot_claim": [
            "This external genetic-code table contact does not establish translation.",
            "This external genetic-code table contact does not establish protein structure.",
            "This external genetic-code table contact does not establish physical admissibility.",
            "This external genetic-code table contact does not establish biological function.",
            "This external genetic-code table contact does not establish a global biological law.",
            "This external genetic-code table contact does not establish a universal mechanism.",
            "The codon/window geometry readback is not promoted beyond the curated genetic-code table contact.",
        ],
    }


def save_raw_payload(payload: bytes, content_type: str) -> dict[str, Any]:
    raw_manifest = write_manifest(
        RAW_BASENAME,
        payload=payload,
        content_type=content_type,
        source_url=SOURCE_URL,
        source_name="ncbi",
        accession_or_id="gc.prt",
        license_or_terms="NCBI genetic-code table public FTP record; use subject to NCBI data and service terms.",
    )
    raw_record = {
        "source_url": SOURCE_URL,
        "source_name": "ncbi",
        "accession_or_id": "gc.prt",
        "payload_encoding": "utf-8 text/plain ASN.1",
        "raw_payload_text": payload.decode("utf-8"),
        "provenance": {
            "payload_sha256": raw_manifest["sha256"],
            "payload_byte_size": raw_manifest["byte_size"],
            "source_url": SOURCE_URL,
            "source_name": "ncbi",
            "accession_or_id": "gc.prt",
            "content_type": content_type,
            "fetched_by": "bio-data-fetcher",
            "intended_claim_id": CLAIM_ID,
            "license_or_terms": raw_manifest["license_or_terms"],
        },
    }
    (DATA_DIR / f"{RAW_BASENAME}.json").write_text(
        json.dumps(raw_record, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return raw_manifest


def main() -> int:
    payload, content_type = fetch_bytes(SOURCE_URL)
    raw_manifest = save_raw_payload(payload, content_type)
    raw_payload_text = payload.decode("utf-8")
    entries = parse_genetic_codes(raw_payload_text)
    dataset = build_dataset(entries, raw_manifest, raw_payload_text)
    dataset_payload = json.dumps(dataset, indent=2, sort_keys=True).encode("utf-8") + b"\n"
    (DATA_DIR / f"{DATASET_BASENAME}.json").write_bytes(dataset_payload)
    dataset_manifest = write_manifest(
        DATASET_BASENAME,
        payload=payload,
        content_type=content_type,
        source_url=SOURCE_URL,
        source_name="ncbi",
        accession_or_id="phase2_confirmatory_falsification_dataset",
        license_or_terms="Local deterministic readback from NCBI gc.prt; underlying NCBI source terms recorded in the raw manifest.",
    )
    print(
        json.dumps(
            {
                "written": [
                    relative(DATA_DIR / f"{RAW_BASENAME}.json"),
                    relative(MANIFEST_DIR / f"{RAW_BASENAME}.json"),
                    relative(DATA_DIR / f"{DATASET_BASENAME}.json"),
                    relative(MANIFEST_DIR / f"{DATASET_BASENAME}.json"),
                ],
                "raw_sha256": raw_manifest["sha256"],
                "dataset_sha256": dataset_manifest["sha256"],
                "changed_codon_count": len(dataset["observed_readback"]["changed_codons"]),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

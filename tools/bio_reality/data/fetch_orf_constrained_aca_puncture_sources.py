#!/usr/bin/env python3
"""Fetch public metadata for the ORF-constrained ACA puncture challenge."""
from __future__ import annotations

import hashlib
import json
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DATA_DIR = Path(__file__).resolve().parent
REPO_ROOT = DATA_DIR.parents[2]
MANIFEST_DIR = DATA_DIR / "manifests"
USER_AGENT = "BioReality-data-fetcher/1.0"
MAX_BYTES = 100 * 1024 * 1024
CLAIM_ID = "h2.external.aca_puncture_orf_validated"
DATASET_BASENAME = "orf_constrained_aca_puncture_challenge_dataset"
DOI = "10.64898/2026.05.03.722492"

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

SOURCES = [
    {
        "basename": "biorxiv_orf_constrained_aca_puncture_10.64898_2026.05.03.722492",
        "source_name": "biorxiv",
        "accession_or_id": DOI,
        "source_url": f"https://api.biorxiv.org/details/biorxiv/{DOI}",
        "license_or_terms": "bioRxiv API metadata for a CC-BY preprint record; source record reports license=cc_by.",
    },
    {
        "basename": "ebi_orf_constrained_aca_puncture_10.64898_2026.05.03.722492",
        "source_name": "ebi",
        "accession_or_id": DOI,
        "source_url": f"https://www.ebi.ac.uk/europepmc/webservices/rest/search?query=DOI:{DOI}&format=json",
        "license_or_terms": "Europe PMC REST metadata; use subject to Europe PMC web-service terms.",
    },
    {
        "basename": "crossref_orf_constrained_aca_puncture_10.64898_2026.05.03.722492",
        "source_name": "other",
        "accession_or_id": DOI,
        "source_url": f"https://api.crossref.org/works/{DOI}",
        "license_or_terms": "Crossref REST metadata; use subject to Crossref API terms.",
    },
]


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
    manifest_path = MANIFEST_DIR / f"{basename}.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    stored = json.loads(manifest_path.read_text(encoding="utf-8"))
    if stored["byte_size"] != len(payload) or stored["sha256"] != hashlib.sha256(payload).hexdigest():
        raise RuntimeError(f"manifest payload digest mismatch for {basename}")


def write_raw_payload(source: dict[str, str]) -> Path:
    payload, content_type = fetch_bytes(source["source_url"])
    raw_path = DATA_DIR / f"{source['basename']}.json"
    raw_path.write_bytes(payload)
    write_manifest(
        source["basename"],
        payload=payload,
        content_type=content_type,
        url=source["source_url"],
        source_name=source["source_name"],
        accession_or_id=source["accession_or_id"],
        license_or_terms=source["license_or_terms"],
    )
    return raw_path


def load_json(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    return data if isinstance(data, dict) else {}


def biorxiv_record(data: dict[str, Any]) -> dict[str, Any]:
    collection = data.get("collection")
    if isinstance(collection, list) and collection and isinstance(collection[0], dict):
        return collection[0]
    return {}


def build_dataset(raw_paths: list[Path]) -> Path:
    raw_by_name = {path.stem: load_json(path) for path in raw_paths}
    biorxiv = raw_by_name.get(SOURCES[0]["basename"], {})
    europepmc = raw_by_name.get(SOURCES[1]["basename"], {})
    crossref = raw_by_name.get(SOURCES[2]["basename"], {})
    record = biorxiv_record(biorxiv)
    source_date = str(record.get("date") or "2026-05-04")
    source_urls = [source["source_url"] for source in SOURCES]
    raw_files = [relative(path) for path in raw_paths]

    dataset = {
        "source": "public metadata contact for ORF-constrained ACA puncture challenge; no window-level audit tables were available from the public REST endpoints queried",
        "snapshot_date": now_iso(),
        "protocol_frozen_at": "2026-05-31T03:08:04+00:00",
        "prospective_holdout_observed_at": f"{source_date}T00:00:00+00:00",
        "r13_frozen_before_external_evidence": False,
        "m13_frozen_before_external_evidence": False,
        "orf_classifier_frozen_before_external_evidence": False,
        "thresholds_preregistered": False,
        "analysis_no_geometry_input": True,
        "reassignment_inference_methods": [
            "external preprint metadata reports ACA-to-Asp reassignment predicted in RAAP-2 Acidimicrobiales",
            "external preprint metadata reports multiple alignments of highly conserved proteins",
            "external preprint metadata reports tRNAUGU identity-element evidence",
        ],
        "geometry_inputs_used": [],
        "prospective_holdout_geometry_inputs_used": [],
        "orf_eligible_aca_windows": [],
        "matched_control_pairs": [],
        "conserved_alignment_columns": [],
        "species_qc": [],
        "trna_candidates": [],
        "high_gc_control_passed": False,
        "phylogenetic_coherence_passed": False,
        "metadata_contacts": {
            "biorxiv": record,
            "europepmc": europepmc,
            "crossref": crossref,
        },
        "raw_external_files": raw_files,
        "source_urls": source_urls,
        "unresolved_required_audit_tables": [
            "externally supplied RAAP-2 / Acidimicrobiales nucleotide windows or assemblies plus nearest standard-code outgroups",
            "species-level ORF-eligible ACA codon count and ACA-to-Asp call table",
            "matched ORF-eligible, ORF-ineligible, shuffled, M-minus-R, off-M, and nearest-outgroup controls",
            "conserved alignment column table with Asp-vs-Thr residues",
            "contamination, completeness, binning, high-GC, and phylogenetic-coherence audit table",
            "tRNAUGU and aaRS annotation table sufficient to audit Thr identity loss and Asp identity support",
        ],
        "cannot_claim": [
            "The metadata contact does not establish translation realization.",
            "The metadata contact does not establish protein structure.",
            "The metadata contact does not establish physical admissibility.",
            "The metadata contact does not establish biological function.",
            "The metadata contact does not establish a global biological law.",
        ],
    }
    dataset_path = DATA_DIR / f"{DATASET_BASENAME}.json"
    payload = json.dumps(dataset, indent=2, sort_keys=True).encode("utf-8") + b"\n"
    dataset_path.write_bytes(payload)
    write_manifest(
        DATASET_BASENAME,
        payload=payload,
        content_type="application/json",
        url=SOURCES[0]["source_url"],
        source_name="other",
        accession_or_id=DATASET_BASENAME,
        license_or_terms="Local aggregation of public metadata records; underlying source terms recorded in per-source manifests.",
        extra={"source_urls": source_urls},
    )
    return dataset_path


def main() -> int:
    MANIFEST_DIR.mkdir(parents=True, exist_ok=True)
    raw_paths = [write_raw_payload(source) for source in SOURCES]
    dataset_path = build_dataset(raw_paths)
    print(json.dumps({"raw": [relative(path) for path in raw_paths], "dataset": relative(dataset_path)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

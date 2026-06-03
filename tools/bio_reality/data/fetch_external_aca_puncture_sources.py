#!/usr/bin/env python3
"""Fetch public metadata for the external ACA puncture challenge."""
from __future__ import annotations

import hashlib
import json
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DATA_DIR = Path(__file__).resolve().parent
MANIFEST_DIR = DATA_DIR / "manifests"
USER_AGENT = "BioReality-data-fetcher/1.0"
MAX_BYTES = 100 * 1024 * 1024
CLAIM_ID = "h2.external.aca_puncture_fill_in"

SOURCES = [
    {
        "basename": "biorxiv_10.64898_2026.05.03.722492",
        "source_name": "biorxiv",
        "accession_or_id": "10.64898/2026.05.03.722492",
        "source_url": "https://api.biorxiv.org/details/biorxiv/10.64898/2026.05.03.722492",
        "license_or_terms": "bioRxiv API metadata for a CC-BY preprint record; source record reports license=cc_by.",
    },
    {
        "basename": "ebi_europepmc_10.64898_2026.05.03.722492",
        "source_name": "ebi",
        "accession_or_id": "10.64898/2026.05.03.722492",
        "source_url": "https://www.ebi.ac.uk/europepmc/webservices/rest/search?query=DOI:10.64898/2026.05.03.722492&format=json",
        "license_or_terms": "Europe PMC REST metadata; use subject to Europe PMC web-service terms.",
    },
    {
        "basename": "crossref_10.64898_2026.05.03.722492",
        "source_name": "other",
        "accession_or_id": "10.64898/2026.05.03.722492",
        "source_url": "https://api.crossref.org/works/10.64898/2026.05.03.722492",
        "license_or_terms": "Crossref REST metadata; use subject to Crossref API terms.",
    },
]


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


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


def write_raw_and_manifest(source: dict[str, str]) -> dict[str, Any]:
    payload, content_type = fetch_bytes(source["source_url"])
    basename = source["basename"]
    raw_path = DATA_DIR / f"{basename}.json"
    manifest_path = MANIFEST_DIR / f"{basename}.json"
    raw_path.write_bytes(payload)
    manifest = {
        "fetched_at": now_iso(),
        "source_url": source["source_url"],
        "source_name": source["source_name"],
        "accession_or_id": source["accession_or_id"],
        "sha256": hashlib.sha256(payload).hexdigest(),
        "byte_size": len(payload),
        "content_type": content_type,
        "fetched_by": "bio-data-fetcher",
        "intended_claim_id": CLAIM_ID,
        "license_or_terms": source["license_or_terms"],
    }
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return {"path": str(raw_path.relative_to(DATA_DIR.parents[2])), "manifest": str(manifest_path.relative_to(DATA_DIR.parents[2]))}


def load_json(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    return data if isinstance(data, dict) else {}


def build_dataset() -> None:
    biorxiv = load_json(DATA_DIR / "biorxiv_10.64898_2026.05.03.722492.json")
    europepmc = load_json(DATA_DIR / "ebi_europepmc_10.64898_2026.05.03.722492.json")
    crossref = load_json(DATA_DIR / "crossref_10.64898_2026.05.03.722492.json")
    collection = biorxiv.get("collection") if isinstance(biorxiv.get("collection"), list) else []
    record = collection[0] if collection and isinstance(collection[0], dict) else {}

    dataset = {
        "source": "public metadata cross-check for DOI 10.64898/2026.05.03.722492",
        "snapshot_date": now_iso(),
        "protocol_frozen_at": "2026-05-29T19:11:13+00:00",
        "external_evidence_observed_at": str(record.get("date") or "2026-05-04") + "T00:00:00+00:00",
        "r13_frozen_before_external_evidence": False,
        "m13_frozen_before_external_evidence": False,
        "thresholds_preregistered": False,
        "analysis_no_geometry_input": True,
        "reassignment_inference_methods": [
            "external source abstract reports multiple alignments of highly conserved proteins",
            "external source abstract reports tRNAUGU identity-element evidence",
        ],
        "geometry_inputs_used": [],
        "species": [],
        "conserved_alignment_columns": [],
        "trna_candidates": [],
        "high_gc_control_passed": False,
        "phylogenetic_coherence_passed": False,
        "metadata_contacts": {
            "biorxiv": record,
            "europepmc": europepmc,
            "crossref": crossref,
        },
        "unresolved_required_audit_tables": [
            "species-level ACA codon count and ACA-to-Asp call table",
            "conserved alignment column table with Asp-vs-Thr residues",
            "contamination, completeness, binning, high-GC, and phylogenetic-coherence audit table",
            "tRNAUGU candidate identity-element table",
        ],
        "cannot_claim": [
            "The metadata contact does not establish translation realization.",
            "The metadata contact does not establish protein structure.",
            "The metadata contact does not establish physical admissibility.",
            "The metadata contact does not establish biological function.",
            "The metadata contact does not establish a global biological law.",
        ],
    }
    dataset_path = DATA_DIR / "external_aca_puncture_challenge_dataset.json"
    payload = json.dumps(dataset, indent=2, sort_keys=True).encode("utf-8") + b"\n"
    dataset_path.write_bytes(payload)
    manifest = {
        "fetched_at": now_iso(),
        "source_url": SOURCES[0]["source_url"],
        "source_urls": [source["source_url"] for source in SOURCES],
        "source_name": "other",
        "accession_or_id": "external_aca_puncture_challenge_dataset",
        "sha256": hashlib.sha256(payload).hexdigest(),
        "byte_size": len(payload),
        "content_type": "application/json",
        "fetched_by": "bio-data-fetcher",
        "intended_claim_id": CLAIM_ID,
        "license_or_terms": "Local aggregation of public metadata records; underlying source terms recorded in per-source manifests.",
    }
    (MANIFEST_DIR / "external_aca_puncture_challenge_dataset.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def main() -> int:
    MANIFEST_DIR.mkdir(parents=True, exist_ok=True)
    written = [write_raw_and_manifest(source) for source in SOURCES]
    build_dataset()
    print(json.dumps({"written": written, "dataset": "tools/bio_reality/data/external_aca_puncture_challenge_dataset.json"}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Check BioReality data manifests against embedded payload provenance."""

from __future__ import annotations

import json
import pathlib
import sys


DATA_DIR = pathlib.Path(__file__).resolve().parent
MANIFEST_DIR = DATA_DIR / "manifests"


def main() -> int:
    failures: list[str] = []
    for manifest_path in sorted(MANIFEST_DIR.glob("*.json")):
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        data_path = DATA_DIR / manifest_path.name
        if not data_path.exists():
            failures.append(f"{manifest_path}: missing data file {data_path.name}")
            continue
        payload = json.loads(data_path.read_text(encoding="utf-8"))
        provenance = payload.get("provenance") if isinstance(payload, dict) else None
        if not isinstance(provenance, dict):
            failures.append(f"{data_path}: missing provenance object")
            continue
        checks = {
            "sha256": provenance.get("payload_sha256"),
            "byte_size": provenance.get("payload_byte_size"),
            "source_url": provenance.get("source_url"),
            "source_name": provenance.get("source_name"),
            "accession_or_id": provenance.get("accession_or_id"),
            "content_type": provenance.get("content_type"),
            "fetched_by": "bio-data-fetcher",
            "intended_claim_id": provenance.get("intended_claim_id"),
            "license_or_terms": provenance.get("license_or_terms"),
        }
        for key, expected in checks.items():
            if manifest.get(key) != expected:
                failures.append(f"{manifest_path}: {key} mismatch")
    if failures:
        for failure in failures:
            print(failure, file=sys.stderr)
        return 1
    print(json.dumps({"status": "passed", "checked_manifests": len(list(MANIFEST_DIR.glob("*.json")))}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Check BioReality data manifests against embedded payload provenance."""

from __future__ import annotations

import json
import pathlib
import sys
import base64
import hashlib


DATA_DIR = pathlib.Path(__file__).resolve().parent
MANIFEST_DIR = DATA_DIR / "manifests"


def main() -> int:
    failures: list[str] = []
    required_manifest_fields = {
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
    for manifest_path in sorted(MANIFEST_DIR.glob("*.json")):
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        missing = sorted(required_manifest_fields.difference(manifest))
        if missing:
            failures.append(f"{manifest_path}: missing manifest field(s): {', '.join(missing)}")
        data_path = DATA_DIR / manifest_path.name
        if not data_path.exists():
            failures.append(f"{manifest_path}: missing data file {data_path.name}")
            continue
        payload = json.loads(data_path.read_text(encoding="utf-8"))
        provenance = payload.get("provenance") if isinstance(payload, dict) else None
        if not isinstance(provenance, dict):
            failures.append(f"{data_path}: missing provenance object")
            continue
        raw_payload_text = payload.get("raw_payload_text")
        has_raw_payload = False
        if isinstance(raw_payload_text, str):
            has_raw_payload = True
            raw_bytes = raw_payload_text.encode("utf-8")
            raw_sha = hashlib.sha256(raw_bytes).hexdigest()
            if manifest.get("sha256") != raw_sha:
                failures.append(f"{manifest_path}: sha256 does not match raw_payload_text")
            if manifest.get("byte_size") != len(raw_bytes):
                failures.append(f"{manifest_path}: byte_size does not match raw_payload_text")
        provenance_raw_base64 = provenance.get("raw_payload_base64")
        if isinstance(provenance_raw_base64, str):
            has_raw_payload = True
            raw_bytes = base64.b64decode(provenance_raw_base64.encode("ascii"), validate=True)
            raw_sha = hashlib.sha256(raw_bytes).hexdigest()
            if manifest.get("sha256") != raw_sha:
                failures.append(f"{manifest_path}: sha256 does not match raw_payload_base64")
            if manifest.get("byte_size") != len(raw_bytes):
                failures.append(f"{manifest_path}: byte_size does not match raw_payload_base64")
        if not has_raw_payload:
            failures.append(f"{data_path}: missing raw payload field for manifest replay")
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

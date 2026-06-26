#!/usr/bin/env python3
"""Fetch Gallus gallus UniProt reviewed feature data for BioReality."""

from __future__ import annotations

import csv
import datetime as dt
import hashlib
import json
import math
import pathlib
import re
import sys
import urllib.parse
import urllib.request


DATA_DIR = pathlib.Path(__file__).resolve().parent
MANIFEST_DIR = DATA_DIR / "manifests"
USER_AGENT = "BioReality-data-fetcher/1.0"
MAX_BYTES = 100 * 1024 * 1024
CLAIM_ID = "h3.cross_layer_relation.h_candidate_ranking_table.b_star_q6_non_translation_residual_powered"
ORGANISM = "gallus_gallus"
TAXID = "9031"
CANDIDATES = ["ptm_density", "domain_count", "tm_count", "complex_member"]
COMPLEX_PATTERNS = ["complex", "component of", "omplex", "heteromer", "homodimer", "oligomer"]
SOURCE_URL = (
    "https://rest.uniprot.org/uniprotkb/search?"
    + urllib.parse.urlencode(
        {
            "query": "organism_id:9031 AND reviewed:true",
            "fields": "accession,xref_string,ft_mod_res,ft_domain,ft_transmem,cc_subunit,length",
            "format": "tsv",
            "size": "500",
        }
    )
)


class FetchFailure(Exception):
    pass


def now_iso() -> str:
    return dt.datetime.now(dt.UTC).replace(microsecond=0).isoformat()


def fetch_page(url: str) -> tuple[bytes, str, str | None]:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=60) as response:
        content_length = response.headers.get("Content-Length")
        if content_length is not None and int(content_length) > MAX_BYTES:
            raise FetchFailure(f"response too large before read: {content_length} bytes")
        payload = response.read(MAX_BYTES + 1)
        if len(payload) > MAX_BYTES:
            raise FetchFailure("response exceeds 100 MB")
        status = int(getattr(response, "status", 200))
        if status != 200:
            raise FetchFailure(f"HTTP status {status}")
        next_url = None
        for link in response.headers.get_all("Link") or []:
            match = re.search(r"<([^>]+)>;\s*rel=\"next\"", str(link))
            if match:
                next_url = match.group(1)
                break
        return payload, str(response.headers.get("Content-Type") or ""), next_url


def fetch_uniprot_payload(url: str) -> tuple[bytes, str]:
    current: str | None = url
    page_index = 0
    lines: list[bytes] = []
    content_type = ""
    while current:
        payload, content_type, current = fetch_page(current)
        page_lines = payload.splitlines()
        if page_index == 0:
            lines.extend(page_lines)
        else:
            lines.extend(page_lines[1:])
        page_index += 1
        if sum(len(line) + 1 for line in lines) > MAX_BYTES:
            raise FetchFailure("combined response exceeds 100 MB")
    if not lines:
        raise FetchFailure("empty UniProt payload")
    return b"\n".join(lines) + b"\n", content_type


def first_present(row: dict[str, str], keys: list[str]) -> str:
    for key in keys:
        value = row.get(key)
        if value:
            return value
    return ""


def first_string_key(value: str) -> str:
    for part in re.split(r"[;\s]+", value.strip()):
        if part:
            return part
    return ""


def parse_float(value: str) -> float | None:
    try:
        out = float(value.strip().replace(",", ""))
    except ValueError:
        return None
    return out if math.isfinite(out) else None


def count_feature_mentions(text: str, token: str) -> int:
    if not text.strip():
        return 0
    return text.upper().count(token.upper())


def complex_member_from_subunit(text: str) -> int:
    lowered = text.lower()
    return 1 if any(pattern in lowered for pattern in COMPLEX_PATTERNS) else 0


def mean(values: list[float]) -> float | None:
    return sum(values) / len(values) if values else None


def percentile_nearest_rank(values: list[float], p: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(p * len(ordered)) - 1))
    return ordered[index]


def distribution_summary(values: list[float]) -> dict[str, object]:
    if not values:
        return {"n": 0}
    ordered = sorted(values)
    return {
        "n": len(values),
        "min": ordered[0],
        "mean": mean(values),
        "median": percentile_nearest_rank(values, 0.5),
        "p95": percentile_nearest_rank(values, 0.95),
        "max": ordered[-1],
        "nonzero_count": sum(1 for value in values if value != 0.0),
    }


def parse_uniprot_tsv(payload: bytes) -> dict[str, object]:
    text = payload.decode("utf-8")
    reader = csv.DictReader(text.splitlines(), delimiter="\t")
    proteins: dict[str, dict[str, object]] = {}
    skipped = {
        "missing_string": 0,
        "missing_or_invalid_length": 0,
        "duplicate_string_first_key": 0,
    }
    for row in reader:
        string_key = first_string_key(first_present(row, ["STRING", "Cross-reference (STRING)", "String"]))
        if not string_key:
            skipped["missing_string"] += 1
            continue
        length = parse_float(first_present(row, ["Length", "length"]))
        if length is None or length <= 0.0:
            skipped["missing_or_invalid_length"] += 1
            continue
        mod_res = first_present(row, ["Modified residue", "Modified residue [FT]", "FT_MOD_RES", "MOD_RES"])
        domain = first_present(row, ["Domain [FT]", "Domain", "FT_DOMAIN", "DOMAIN"])
        transmem = first_present(row, ["Transmembrane", "Transmembrane [FT]", "FT_TRANSMEM", "TRANSMEM"])
        subunit = first_present(row, ["Subunit structure [CC]", "Subunit", "CC_SUBUNIT", "Subunit structure"])
        features = {
            "ptm_density": count_feature_mentions(mod_res, "MOD_RES") / length,
            "domain_count": float(count_feature_mentions(domain, "DOMAIN")),
            "tm_count": float(count_feature_mentions(transmem, "TRANSMEM")),
            "complex_member": float(complex_member_from_subunit(subunit)),
        }
        if string_key in proteins:
            skipped["duplicate_string_first_key"] += 1
            old_features = proteins[string_key].get("features")
            if isinstance(old_features, dict):
                features = {
                    "ptm_density": max(float(old_features.get("ptm_density", 0.0)), features["ptm_density"]),
                    "domain_count": max(float(old_features.get("domain_count", 0.0)), features["domain_count"]),
                    "tm_count": max(float(old_features.get("tm_count", 0.0)), features["tm_count"]),
                    "complex_member": max(float(old_features.get("complex_member", 0.0)), features["complex_member"]),
                }
        proteins[string_key] = {
            "uniprot_accession": first_present(row, ["Entry", "Accession"]),
            "string_id": string_key,
            "length": length,
            "features": features,
            "raw_feature_counts": {
                "mod_res_count": int(round(features["ptm_density"] * length)),
                "domain_count": int(features["domain_count"]),
                "tm_count": int(features["tm_count"]),
                "complex_member": int(features["complex_member"]),
            },
        }
    values_by_candidate = {name: [] for name in CANDIDATES}
    for record in proteins.values():
        features = record.get("features")
        if isinstance(features, dict):
            for name in CANDIDATES:
                value = features.get(name)
                if isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(float(value)):
                    values_by_candidate[name].append(float(value))
    return {
        "organism": ORGANISM,
        "ncbi_taxid": TAXID,
        "schema_version": 1,
        "source_kind": "UniProtKB reviewed protein features",
        "proteins": proteins,
        "n_uniprot_rows": max(0, len(text.splitlines()) - 1),
        "n_string_feature_records": len(proteins),
        "feature_distribution_summary": {name: distribution_summary(values) for name, values in values_by_candidate.items()},
        "skipped_records": skipped,
        "feature_parse_policy": {
            "ptm_density": "count of MOD_RES feature mentions divided by UniProt length",
            "domain_count": "count of DOMAIN feature mentions",
            "tm_count": "count of TRANSMEM feature mentions",
            "complex_member": "1 when UniProt SUBUNIT text contains complex/component/heteromer/homodimer/oligomer keyword, else 0",
            "note": "coarse fetchable annotations only; absent annotation is encoded as zero, not as biological absence",
        },
    }


def write_json(path: pathlib.Path, payload: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    fetched_at = now_iso()
    raw, content_type = fetch_uniprot_payload(SOURCE_URL)
    sha = hashlib.sha256(raw).hexdigest()
    parsed = parse_uniprot_tsv(raw)
    parsed["provenance"] = {
        "source_url": SOURCE_URL,
        "downloaded_url": SOURCE_URL,
        "source_name": "uniprot",
        "accession_or_id": "taxonomy_9031_reviewed_features",
        "fetch_method": "paged_search",
        "source_kind": "UniProtKB reviewed protein features",
        "fetched_at": fetched_at,
        "payload_sha256": sha,
        "payload_byte_size": len(raw),
        "content_type": content_type,
        "fetch_user_agent": USER_AGENT,
        "intended_claim_id": CLAIM_ID,
        "license_or_terms": "UniProt data retrieved through UniProt REST; cite UniProt and follow UniProt website terms.",
        "derivation_boundary": "not_bedc_kernel_content",
    }
    parsed["cannot_claim"] = [
        "UniProt reviewed feature annotations are curated external protein metadata, not translation rates.",
        "Feature counts do not establish structure, physical admissibility, function, mechanism, phenotype, or a global biological law.",
        "Absent annotation is encoded as zero for this finite readout and is not biological absence.",
    ]
    parsed["derivation_boundary"] = "not_bedc_kernel_content"
    raw_text = raw.decode("utf-8", "replace")
    parsed["raw_payload_text"] = raw_text
    parsed["raw_payload_note"] = "full UniProt TSV response reconstructed from REST pages; sha256 is over this UTF-8 byte stream"

    out_path = DATA_DIR / "uniprot_protein_features_gallus_gallus.json"
    write_json(out_path, parsed)
    manifest = {
        "fetched_at": fetched_at,
        "source_url": SOURCE_URL,
        "source_name": "uniprot",
        "accession_or_id": "taxonomy_9031_reviewed_features",
        "sha256": sha,
        "byte_size": len(raw),
        "content_type": content_type,
        "fetched_by": "bio-data-fetcher",
        "intended_claim_id": CLAIM_ID,
        "license_or_terms": "UniProt data retrieved through UniProt REST; cite UniProt and follow UniProt website terms.",
    }
    write_json(MANIFEST_DIR / "uniprot_protein_features_gallus_gallus.json", manifest)
    print(json.dumps({"wrote": str(out_path), "manifest": str(MANIFEST_DIR / "uniprot_protein_features_gallus_gallus.json"), "sha256": sha, "byte_size": len(raw), "n_string_feature_records": parsed["n_string_feature_records"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"fetch_uniprot_gallus_features failed: {exc}", file=sys.stderr)
        raise SystemExit(1)

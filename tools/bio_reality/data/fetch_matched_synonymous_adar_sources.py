#!/usr/bin/env python3
"""Probe public metadata sources for matched synonymous ADAR editing data."""
from __future__ import annotations

import hashlib
import json
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DATA_DIR = Path(__file__).resolve().parent
REPO_ROOT = DATA_DIR.parents[2]
DIAGNOSIS_DIR = REPO_ROOT / "tools/bio_reality/state/proposed_data_sources"
USER_AGENT = "BioReality-data-fetcher/1.0"
MAX_BYTES = 100 * 1024 * 1024
CLAIM_ID = "bio-Plan.direction.new-frontier.ADAR-mediated-editing-bridge"
EXPERIMENT_ID = "matched-synonymous-ADAR-A-to-I-editing-loss-rescue"
MISSING_DATASET = "tools/bio_reality/data/matched_synonymous_adar_a_to_i_editing_loss_rescue.json"

QUERY = (
    '"ADAR" "A-to-I" "editing" "catalytic-dead" '
    '"rescue" "matched synonymous"'
)
SOURCES = [
    {
        "label": "Europe PMC ADAR matched synonymous loss/rescue query",
        "source_name": "ebi",
        "source_url": (
            "https://www.ebi.ac.uk/europepmc/webservices/rest/search?"
            + urllib.parse.urlencode({"query": QUERY, "format": "json", "pageSize": "5"})
        ),
    },
    {
        "label": "NCBI PubMed ADAR matched synonymous loss/rescue query",
        "source_name": "ncbi",
        "source_url": (
            "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?"
            + urllib.parse.urlencode({"db": "pubmed", "term": QUERY, "retmode": "json", "retmax": "5"})
        ),
    },
    {
        "label": "bioRxiv ADAR matched synonymous loss/rescue query",
        "source_name": "biorxiv",
        "source_url": (
            "https://www.ebi.ac.uk/europepmc/webservices/rest/search?"
            + urllib.parse.urlencode({"query": QUERY + " SRC:PPR", "format": "json", "pageSize": "5"})
        ),
    },
]

REQUIRED_ROW_LEVEL_COLUMNS = [
    "q_plus/q_minus matched synonymous partition fixed before outcome measurement",
    "site-specific A-to-I editing fractions under ADAR-present condition",
    "site-specific A-to-I editing fractions under ADAR loss or catalytic inhibition",
    "wild-type ADAR rescue editing fractions",
    "catalytic-dead or binding-defective ADAR rescue editing fractions",
    "local ADAR occupancy for the same Q+/Q- matched pairs",
    "structure/composition control rows that do not restore the ADAR substrate",
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


def summarize_json(payload: bytes) -> dict[str, Any]:
    try:
        parsed = json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        return {"parse_error": str(exc)}
    summary: dict[str, Any] = {"root_type": type(parsed).__name__}
    if isinstance(parsed, dict):
        result_list = parsed.get("resultList")
        if isinstance(result_list, dict) and isinstance(result_list.get("result"), list):
            records = result_list["result"]
            summary["record_count"] = len(records)
            summary["records"] = [
                {
                    "id": record.get("id"),
                    "doi": record.get("doi"),
                    "title": record.get("title"),
                    "journal": record.get("journalTitle"),
                    "pub_year": record.get("pubYear"),
                    "has_full_text": record.get("hasFullText"),
                    "has_supplement": record.get("hasSuppl"),
                    "has_tm_accessions": record.get("hasTMAccessionNumbers"),
                }
                for record in records[:5]
                if isinstance(record, dict)
            ]
        esearch = parsed.get("esearchresult")
        if isinstance(esearch, dict):
            summary["count"] = esearch.get("count")
            summary["ids"] = esearch.get("idlist")
    return summary


def write_diagnosis(rows: list[dict[str, Any]]) -> Path:
    DIAGNOSIS_DIR.mkdir(parents=True, exist_ok=True)
    path = DIAGNOSIS_DIR / f"{CLAIM_ID}.md"
    lines = [
        f"# {CLAIM_ID} data-source diagnosis",
        "",
        f"Claim: `{CLAIM_ID}`",
        f"Experiment: `{EXPERIMENT_ID}`",
        f"Missing required data: `{MISSING_DATASET}`",
        "",
        "The experiment requires a row-level matched synonymous ADAR A-to-I RNA-editing loss/rescue dataset.",
        "The required JSON must contain matched Q+/Q- coding-region variant pairs, freeze/preregistration flags, ADAR-present editing fractions, ADAR-loss or catalytic-inhibition fractions, wild-type rescue fractions, catalytic-dead or binding-defective rescue fractions, local ADAR occupancy, and structure/composition controls.",
        "",
        "Public machine-readable sources checked with `urllib.request`, `timeout=60`, and `User-Agent: BioReality-data-fetcher/1.0`:",
        "",
    ]
    for row in rows:
        lines.append(f"- {row['label']}: `{row['source_url']}`")
        if row.get("status") == "fetched":
            lines.append(
                "  "
                + json.dumps(
                    {
                        "status": row["status"],
                        "source_name": row["source_name"],
                        "content_type": row["content_type"],
                        "byte_size": row["byte_size"],
                        "sha256": row["sha256"],
                        "summary": row["summary"],
                    },
                    sort_keys=True,
                )
            )
        else:
            lines.append(f"  status: {row.get('status')} error: {row.get('error')}")
    lines.extend(
        [
            "",
            "Blocking condition:",
            "",
            "The reachable public metadata endpoints do not expose the row-level assay table needed by the current experiment contract. Search records and abstracts are not enough to populate matched variant pairs, perturbation conditions, rescue fractions, or occupancy values. Writing `matched_synonymous_adar_a_to_i_editing_loss_rescue.json` from those contacts would fabricate the assay dataset.",
            "",
            "Required future source shape:",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in REQUIRED_ROW_LEVEL_COLUMNS)
    lines.extend(
        [
            "",
            "Boundary discipline:",
            "",
            "- The internal codon-coordinate may be used only as a frozen design axis.",
            "- Do not promote codon/window geometry to translation realization, protein structure, physical admissibility, biological function, or global biological law.",
            "- Keep external curated reality in data/provenance artifacts; do not write it into BEDC kernel prose.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")
    return path


def main() -> int:
    rows: list[dict[str, Any]] = []
    for source in SOURCES:
        row = dict(source)
        try:
            payload, content_type = fetch_bytes(source["source_url"])
            row.update(
                {
                    "status": "fetched",
                    "content_type": content_type,
                    "byte_size": len(payload),
                    "sha256": hashlib.sha256(payload).hexdigest(),
                    "summary": summarize_json(payload),
                }
            )
        except Exception as exc:
            row.update({"status": "fetch_failed", "error": repr(exc)})
        rows.append(row)
    diagnosis_path = write_diagnosis(rows)
    print(
        json.dumps(
            {
                "status": "needs_data",
                "claim_id": CLAIM_ID,
                "experiment_id": EXPERIMENT_ID,
                "missing_required_data": MISSING_DATASET,
                "diagnosis": str(diagnosis_path.relative_to(REPO_ROOT)),
                "fetched_at": now_iso(),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 2


if __name__ == "__main__":
    raise SystemExit(main())

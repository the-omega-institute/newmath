#!/usr/bin/env python3
"""Fetch PAXdb protein abundance payloads for the BioReality organism panel.

This script is intentionally stdlib-only. It writes only data artifacts under
this directory, and it refuses to emit an organism abundance file unless the
protein abundance map was parsed from a successful HTTP response.
"""

from __future__ import annotations

import datetime as _dt
import hashlib
import html.parser
import json
import pathlib
import re
import sys
import urllib.error
import urllib.parse
import urllib.request


DATA_DIR = pathlib.Path(__file__).resolve().parent
CAMPAIGN_MANIFEST = DATA_DIR / "multi_organism_campaign_manifest.json"
PAXDB_DATASETS_URL = "https://pax-db.org/downloads/latest/datasets/"
USER_AGENT = "bio-data-fetcher/1.0"
RAW_TEXT_LIMIT_BYTES = 1024 * 1024
NEARBY_MODEL_TARGETS = [
    {
        "organism": "escherichia_coli_k12_mg1655",
        "organism_label": "Escherichia coli K-12 substr. MG1655",
        "ncbi_taxid": "511145",
        "target_relation": "nearby_model_species",
        "nearby_for_codon_organisms": ["escherichia_coli"],
        "nearby_boundary": "not counted as exact codon/proteomics overlap for the 40-organism panel",
    },
    {
        "organism": "pseudomonas_aeruginosa_pao1",
        "organism_label": "Pseudomonas aeruginosa PAO1",
        "ncbi_taxid": "208964",
        "target_relation": "nearby_model_species",
        "nearby_for_codon_organisms": [
            "pseudomonas_aeruginosa_pa7",
            "pseudomonas_aeruginosa_ucbpp_pa14",
        ],
        "nearby_boundary": "not counted as exact codon/proteomics overlap for the 40-organism panel",
    },
]


class LinkParser(html.parser.HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.hrefs: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag != "a":
            return
        attr = dict(attrs)
        href = attr.get("href")
        if href:
            self.hrefs.append(href)


def now_utc() -> str:
    return _dt.datetime.now(_dt.UTC).replace(microsecond=0).isoformat()


def fetch_bytes(url: str) -> dict[str, object]:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=60) as response:
        body = response.read()
        return {
            "url": url,
            "http_status": int(response.status),
            "content_type": response.headers.get("content-type"),
            "payload_byte_size": len(body),
            "payload_sha256": hashlib.sha256(body).hexdigest(),
            "raw_bytes": body,
        }


def decode_text(raw: bytes) -> str:
    return raw.decode("utf-8", "replace")


def raw_text_slice(raw: bytes) -> tuple[str, str]:
    if len(raw) <= RAW_TEXT_LIMIT_BYTES:
        return decode_text(raw), "full_raw_payload"
    prefix = raw[:RAW_TEXT_LIMIT_BYTES]
    return decode_text(prefix), f"deterministic_prefix_{RAW_TEXT_LIMIT_BYTES}_bytes"


def parse_links(raw: bytes) -> list[str]:
    parser = LinkParser()
    parser.feed(decode_text(raw))
    return parser.hrefs


def parse_abundance_payload(raw: bytes) -> dict[str, float]:
    text = decode_text(raw)
    abundance: dict[str, float] = {}
    header_seen = False
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("#"):
            header_columns = stripped.lstrip("#").strip().split()
            if header_columns[:3] == [
                "gene_name",
                "string_external_id",
                "abundance",
            ]:
                header_seen = True
            continue
        parts = stripped.split()
        if len(parts) < 3:
            continue
        gene_name, string_external_id, abundance_text = parts[:3]
        try:
            value = float(abundance_text)
        except ValueError:
            continue
        protein_id = string_external_id or gene_name
        if not protein_id:
            continue
        abundance[protein_id] = value
    if not header_seen:
        raise ValueError("PAXdb abundance header not found")
    if not abundance:
        raise ValueError("no protein abundance rows parsed")
    return abundance


def parse_paxdb_metadata(raw: bytes) -> dict[str, object]:
    text = decode_text(raw)
    metadata: dict[str, object] = {}
    for line in text.splitlines():
        if not line.startswith("#") or ":" not in line:
            continue
        key, value = line[1:].split(":", 1)
        key = key.strip()
        value = value.strip()
        if key in {"id", "name", "score", "coverage", "description", "organ", "integrated", "publication_year", "filename"}:
            if key == "integrated":
                metadata[f"paxdb_{key}"] = value.lower() == "true"
            elif key == "coverage":
                try:
                    metadata[f"paxdb_{key}"] = int(value)
                except ValueError:
                    metadata[f"paxdb_{key}"] = value
            else:
                metadata[f"paxdb_{key}"] = value
    return metadata


def classify_source_kind(filename: str) -> str:
    if filename.endswith("-integrated.txt"):
        return "paxdb_integrated_abundance"
    return "paxdb_abundance_dataset"


def choose_candidate_file(taxid: str, files: list[str]) -> tuple[str | None, str]:
    text_files = sorted(f for f in files if f.endswith(".txt"))
    if not text_files:
        return None, "no txt abundance files in PAXdb taxid directory"
    whole = f"{taxid}-WHOLE_ORGANISM-integrated.txt"
    if whole in text_files:
        return whole, "preferred WHOLE_ORGANISM integrated PAXdb dataset"
    integrated = sorted(f for f in text_files if f.endswith("-integrated.txt"))
    if integrated:
        return integrated[0], "first lexical integrated PAXdb dataset; no WHOLE_ORGANISM integrated dataset present"
    return text_files[0], "first lexical PAXdb txt dataset; no integrated dataset present"


def organism_filename(slug: str) -> pathlib.Path:
    return DATA_DIR / f"proteomics_abundance_{slug}.json"


def load_codon_targets() -> list[dict[str, object]]:
    with CAMPAIGN_MANIFEST.open() as handle:
        manifest = json.load(handle)
    targets: list[dict[str, object]] = []
    for entry in manifest.get("successes", []):
        slug = str(entry.get("organism", ""))
        label = str(entry.get("organism_label", ""))
        taxid = str(entry.get("kazusa_taxid", ""))
        if slug and label and taxid:
            targets.append(
                {
                    "organism": slug,
                    "organism_label": label,
                    "ncbi_taxid": taxid,
                    "target_relation": "exact_codon_manifest_taxid",
                    "nearby_for_codon_organisms": [],
                }
            )
    return targets


def write_json(path: pathlib.Path, payload: dict[str, object]) -> None:
    with path.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, ensure_ascii=False, indent=2, sort_keys=True)
        handle.write("\n")


def main() -> int:
    fetched_at = now_utc()
    codon_targets = load_codon_targets()
    targets = codon_targets + NEARBY_MODEL_TARGETS
    successes: list[dict[str, object]] = []
    failures: list[dict[str, object]] = []
    taxid_contacts: dict[str, dict[str, object]] = {}
    abundance_payload_contacts: dict[str, dict[str, object]] = {}

    try:
        index_contact = fetch_bytes(PAXDB_DATASETS_URL)
    except (urllib.error.URLError, TimeoutError, OSError) as exc:
        manifest = {
            "fetched_at": fetched_at,
            "fetched_by": "bio-data-fetcher",
            "source_name": "PAXdb",
            "paxdb_dataset_index_url": PAXDB_DATASETS_URL,
            "success_count": 0,
            "failure_count": len(targets),
            "failures": [
                {
                    "organism": t["organism"],
                    "organism_label": t["organism_label"],
                    "ncbi_taxid": t["ncbi_taxid"],
                    "target_relation": t.get("target_relation"),
                    "stage": "paxdb_index_fetch",
                    "reason": repr(exc),
                }
                for t in targets
            ],
            "overlap_with_codon_manifest": [],
            "raw_payload_policy": "Only successful organism abundance files contain raw_payload_text and payload_sha256 from HTTP bytes.",
            "derivation_boundary": "not_bedc_kernel_content",
        }
        write_json(DATA_DIR / "proteomics_campaign_manifest.json", manifest)
        print("PAXdb index fetch failed; wrote 0-success manifest.", file=sys.stderr)
        return 1

    index_hrefs = parse_links(index_contact["raw_bytes"])  # type: ignore[index]
    available_taxids = {
        href.strip("/")
        for href in index_hrefs
        if re.fullmatch(r"\d+/", href)
    }
    index_text, index_payload_note = raw_text_slice(index_contact["raw_bytes"])  # type: ignore[index]
    index_contact_public = {
        k: v
        for k, v in index_contact.items()
        if k != "raw_bytes"
    }
    index_contact_public["raw_payload_text"] = index_text
    index_contact_public["payload_note"] = index_payload_note
    index_contact_public["fetched_at"] = fetched_at

    for target in targets:
        slug = target["organism"]
        label = target["organism_label"]
        taxid = target["ncbi_taxid"]
        if taxid not in available_taxids:
            failures.append(
                {
                    "organism": slug,
                    "organism_label": label,
                    "ncbi_taxid": taxid,
                    "target_relation": target.get("target_relation"),
                    "stage": "paxdb_taxid_index",
                    "reason": "NCBI taxid absent from PAXdb latest datasets index",
                }
            )
            continue

        taxid_url = urllib.parse.urljoin(PAXDB_DATASETS_URL, f"{taxid}/")
        try:
            taxid_contact = fetch_bytes(taxid_url)
        except (urllib.error.URLError, TimeoutError, OSError) as exc:
            failures.append(
                {
                    "organism": slug,
                    "organism_label": label,
                    "ncbi_taxid": taxid,
                    "target_relation": target.get("target_relation"),
                    "stage": "paxdb_taxid_directory_fetch",
                    "reason": repr(exc),
                    "url": taxid_url,
                }
            )
            continue

        taxid_text, taxid_payload_note = raw_text_slice(taxid_contact["raw_bytes"])  # type: ignore[index]
        taxid_contacts.setdefault(
            taxid,
            {
                **{k: v for k, v in taxid_contact.items() if k != "raw_bytes"},
                "raw_payload_text": taxid_text,
                "payload_note": taxid_payload_note,
                "fetched_at": fetched_at,
            },
        )

        files = [href for href in parse_links(taxid_contact["raw_bytes"]) if href.endswith(".txt")]  # type: ignore[index]
        filename, selection_reason = choose_candidate_file(taxid, files)
        if filename is None:
            failures.append(
                {
                    "organism": slug,
                    "organism_label": label,
                    "ncbi_taxid": taxid,
                    "target_relation": target.get("target_relation"),
                    "stage": "paxdb_file_selection",
                    "reason": selection_reason,
                    "url": taxid_url,
                }
            )
            continue

        file_url = urllib.parse.urljoin(taxid_url, filename)
        try:
            payload_contact = fetch_bytes(file_url)
        except (urllib.error.URLError, TimeoutError, OSError) as exc:
            failures.append(
                {
                    "organism": slug,
                    "organism_label": label,
                    "ncbi_taxid": taxid,
                    "target_relation": target.get("target_relation"),
                    "stage": "paxdb_abundance_fetch",
                    "reason": repr(exc),
                    "url": file_url,
                    "selected_file": filename,
                }
            )
            continue

        raw = payload_contact["raw_bytes"]  # type: ignore[index]
        if not raw:
            failures.append(
                {
                    "organism": slug,
                    "organism_label": label,
                    "ncbi_taxid": taxid,
                    "target_relation": target.get("target_relation"),
                    "stage": "paxdb_abundance_fetch",
                    "reason": "empty HTTP response body",
                    "url": file_url,
                    "selected_file": filename,
                }
            )
            continue

        try:
            protein_abundance = parse_abundance_payload(raw)  # type: ignore[arg-type]
        except ValueError as exc:
            failures.append(
                {
                    "organism": slug,
                    "organism_label": label,
                    "ncbi_taxid": taxid,
                    "target_relation": target.get("target_relation"),
                    "stage": "paxdb_abundance_parse",
                    "reason": str(exc),
                    "url": file_url,
                    "selected_file": filename,
                }
            )
            continue

        paxdb_metadata = parse_paxdb_metadata(raw)  # type: ignore[arg-type]
        paxdb_organ = str(paxdb_metadata.get("paxdb_organ", "unknown"))
        paxdb_integrated = bool(paxdb_metadata.get("paxdb_integrated", False))
        if paxdb_organ == "WHOLE_ORGANISM":
            contact_scope = "measured protein abundance (mass-spec integrated), organism-level"
        elif paxdb_integrated:
            contact_scope = f"measured protein abundance (mass-spec integrated), PAXdb organ={paxdb_organ}"
        else:
            contact_scope = f"measured protein abundance (mass-spec dataset), PAXdb organ={paxdb_organ}"

        raw_payload_text, raw_payload_note = raw_text_slice(raw)  # type: ignore[arg-type]
        payload_sha256 = str(payload_contact["payload_sha256"])
        payload_public = {
            k: v
            for k, v in payload_contact.items()
            if k != "raw_bytes"
        }
        payload_public["raw_payload_text"] = raw_payload_text
        payload_public["payload_note"] = raw_payload_note
        payload_public["fetched_at"] = fetched_at
        abundance_payload_contacts[f"{slug}:{filename}"] = payload_public

        out_file = organism_filename(slug)
        organism_payload = {
            "schema_version": 1,
            "organism": slug,
            "organism_label": label,
            "ncbi_taxid": taxid,
            "source_name": "PAXdb",
            "source_url": file_url,
            "source_dataset_file": filename,
            "source_dataset_selection_reason": selection_reason,
            "target_relation": target.get("target_relation"),
            "nearby_for_codon_organisms": target.get("nearby_for_codon_organisms", []),
            "nearby_boundary": target.get("nearby_boundary"),
            "source_kind": classify_source_kind(filename),
            **paxdb_metadata,
            "fetched_at": fetched_at,
            "fetched_by": "bio-data-fetcher",
            "abundance_granularity": "per_protein",
            "protein_abundance": protein_abundance,
            "raw_payload_text": raw_payload_text,
            "raw_payload_note": raw_payload_note,
            "payload_byte_size": payload_contact["payload_byte_size"],
            "payload_sha256": payload_sha256,
            "n_proteins": len(protein_abundance),
            "reality_contact_scope": contact_scope,
            "cannot_claim": [
                "abundance 是 measured proteomics 但非 per-cell absolute; 不直接给 translation rate; 不证 mechanism",
            ],
            "derivation_boundary": "not_bedc_kernel_content",
        }
        write_json(out_file, organism_payload)

        successes.append(
            {
                "organism": slug,
                "organism_label": label,
                "ncbi_taxid": taxid,
                "target_relation": target.get("target_relation"),
                "nearby_for_codon_organisms": target.get("nearby_for_codon_organisms", []),
                "nearby_boundary": target.get("nearby_boundary"),
                "file": str(out_file.relative_to(DATA_DIR.parent.parent.parent)),
                "source_url": file_url,
                "source_dataset_file": filename,
                "source_kind": classify_source_kind(filename),
                "paxdb_organ": paxdb_organ,
                "paxdb_integrated": paxdb_integrated,
                "paxdb_coverage": paxdb_metadata.get("paxdb_coverage"),
                "granularity": "per_protein",
                "n_proteins": len(protein_abundance),
                "payload_sha256": payload_sha256,
                "payload_byte_size": payload_contact["payload_byte_size"],
            }
        )

    success_slugs = {str(item["organism"]) for item in successes}
    overlap = [
        {
            "organism": target["organism"],
            "organism_label": target["organism_label"],
            "ncbi_taxid": target["ncbi_taxid"],
            "proteomics_file": str(organism_filename(target["organism"]).relative_to(DATA_DIR.parent.parent.parent)),
        }
        for target in codon_targets
        if target["organism"] in success_slugs
    ]
    nearby_successes = [
        item
        for item in successes
        if item.get("target_relation") == "nearby_model_species"
    ]
    unique_success_taxids = sorted({str(item["ncbi_taxid"]) for item in successes})

    manifest = {
        "schema_version": 1,
        "fetched_at": fetched_at,
        "fetched_by": "bio-data-fetcher",
        "source_name": "PAXdb",
        "paxdb_dataset_index_url": PAXDB_DATASETS_URL,
        "paxdb_dataset_index_contact": index_contact_public,
        "paxdb_available_taxid_count": len(available_taxids),
        "paxdb_taxid_directory_contacts": taxid_contacts,
        "success_count": len(successes),
        "success_unique_taxid_count": len(unique_success_taxids),
        "success_unique_taxids": unique_success_taxids,
        "exact_codon_manifest_success_count": len([item for item in successes if item.get("target_relation") == "exact_codon_manifest_taxid"]),
        "nearby_model_success_count": len(nearby_successes),
        "nearby_model_successes": nearby_successes,
        "failure_count": len(failures),
        "successes": successes,
        "failures": failures,
        "overlap_with_codon_manifest": overlap,
        "overlap_count": len(overlap),
        "overlap_unique_taxid_count": len({item["ncbi_taxid"] for item in overlap}),
        "raw_payload_policy": (
            "Each successful proteomics_abundance_<org>.json stores raw_payload_text "
            "as the full HTTP body when <= 1 MiB, otherwise the deterministic first "
            "1 MiB slice; payload_sha256 is always sha256 over the complete raw bytes."
        ),
        "abundance_payload_contacts": abundance_payload_contacts,
        "cannot_claim": [
            "PAXdb abundance is measured or integrated proteomics abundance, not per-cell absolute abundance.",
            "The campaign does not claim translation rate or mechanistic mediation.",
            "The campaign does not claim any BEDC kernel content.",
        ],
        "derivation_boundary": "not_bedc_kernel_content",
    }
    write_json(DATA_DIR / "proteomics_campaign_manifest.json", manifest)

    print(f"success_count={len(successes)}")
    print(f"overlap_count={len(overlap)}")
    print(f"success_unique_taxid_count={len(unique_success_taxids)}")
    for item in successes[:3]:
        print(f"sample {item['organism']} taxid={item['ncbi_taxid']} n_proteins={item['n_proteins']} file={item['source_dataset_file']}")
    failure_reasons: dict[str, int] = {}
    for failure in failures:
        reason = str(failure["reason"])
        failure_reasons[reason] = failure_reasons.get(reason, 0) + 1
    for reason, count in sorted(failure_reasons.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"failure_reason count={count}: {reason}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

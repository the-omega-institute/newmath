#!/usr/bin/env python3
"""Fetch the Koren 2018 C-terminal GPS supplementary table."""
from __future__ import annotations

import base64
import hashlib
import json
import pathlib
import re
import urllib.request
import zipfile
from datetime import datetime, timezone
from io import BytesIO
from typing import Any
from xml.etree import ElementTree


DATA_DIR = pathlib.Path(__file__).resolve().parent
MANIFEST_DIR = DATA_DIR / "manifests"
OUT_PATH = DATA_DIR / "degron_cterminal_crossdataset_koren2018.json"
MANIFEST_PATH = MANIFEST_DIR / "degron_cterminal_crossdataset_koren2018.json"
SOURCE_URL = "https://ars.els-cdn.com/content/image/1-s2.0-S009286741830521X-mmc7.xlsx"
SOURCE_NAME = "other"
ACCESSION_OR_ID = "1-s2.0-S009286741830521X-mmc7.xlsx"
CLAIM_ID = "h3.cross_layer_relation.protein_degron_stability.degron_cterminal_crossdataset_koren2018"
USER_AGENT = "BioReality-data-fetcher/1.0"
MAX_BYTES = 100 * 1024 * 1024
AA = "ACDEFGHIKLMNPQRSTVWY"
DESTABILIZING_END = set("WFYGAC")
STABILIZING_END = set("DEK")
NS = {"x": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}
REL_NS = {"r": "http://schemas.openxmlformats.org/package/2006/relationships"}


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def fetch_bytes(url: str) -> tuple[bytes, str]:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=60) as response:
        length = response.headers.get("Content-Length")
        if length is not None and int(length) > MAX_BYTES:
            raise RuntimeError(f"response exceeds 100 MB before read: {length}")
        payload = response.read(MAX_BYTES + 1)
        if len(payload) > MAX_BYTES:
            raise RuntimeError("response exceeds 100 MB")
        return payload, str(response.headers.get("Content-Type") or "server did not provide Content-Type")


def parse_shared_strings(zf: zipfile.ZipFile) -> list[str]:
    root = ElementTree.fromstring(zf.read("xl/sharedStrings.xml"))
    values: list[str] = []
    for item in root.findall("x:si", NS):
        parts = [node.text or "" for node in item.findall(".//x:t", NS)]
        values.append("".join(parts))
    return values


def sheet_path_by_name(zf: zipfile.ZipFile, sheet_name: str) -> str:
    workbook = ElementTree.fromstring(zf.read("xl/workbook.xml"))
    rels = ElementTree.fromstring(zf.read("xl/_rels/workbook.xml.rels"))
    rid_to_target = {
        rel.attrib["Id"]: rel.attrib["Target"]
        for rel in rels.findall("r:Relationship", REL_NS)
    }
    for sheet in workbook.findall(".//x:sheet", NS):
        if sheet.attrib.get("name") == sheet_name:
            rid = sheet.attrib["{http://schemas.openxmlformats.org/officeDocument/2006/relationships}id"]
            target = rid_to_target[rid]
            return "xl/" + target.lstrip("/")
    raise ValueError(f"sheet not found: {sheet_name}")


def cell_ref_col(ref: str) -> str:
    match = re.match(r"([A-Z]+)", ref)
    if not match:
        raise ValueError(f"bad cell reference: {ref}")
    return match.group(1)


def cell_value(cell: ElementTree.Element, shared_strings: list[str]) -> Any:
    value_node = cell.find("x:v", NS)
    if value_node is None:
        return ""
    raw = value_node.text or ""
    if cell.attrib.get("t") == "s":
        return shared_strings[int(raw)]
    try:
        return float(raw)
    except ValueError:
        return raw


def rows_from_sheet(zf: zipfile.ZipFile, sheet_path: str, shared_strings: list[str]) -> list[dict[str, Any]]:
    root = ElementTree.fromstring(zf.read(sheet_path))
    rows: list[dict[str, Any]] = []
    for row in root.findall(".//x:sheetData/x:row", NS):
        values = {
            cell_ref_col(cell.attrib["r"]): cell_value(cell, shared_strings)
            for cell in row.findall("x:c", NS)
            if "r" in cell.attrib
        }
        if values:
            rows.append(values)
    return rows


def frozen_score(end_residue: str) -> int:
    if end_residue in DESTABILIZING_END:
        return -1
    if end_residue in STABILIZING_END:
        return 1
    return 0


def internal_composition(peptide: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for residue in peptide[:-1]:
        if residue in AA:
            counts[residue] = counts.get(residue, 0) + 1
    return counts


def parse_payload(payload: bytes) -> dict[str, Any]:
    with zipfile.ZipFile(BytesIO(payload)) as zf:
        shared_strings = parse_shared_strings(zf)
        sheet_name = "Table S7A. C-terminal screen "
        rows = rows_from_sheet(zf, sheet_path_by_name(zf, sheet_name), shared_strings)

    header_row_index = None
    header: dict[str, str] = {}
    for index, row in enumerate(rows, start=1):
        normalized = {col: str(value) for col, value in row.items()}
        if normalized.get("H") == "PSI" and "Peptide amino acid sequence" in normalized.get("L", ""):
            header_row_index = index
            header = normalized
            break
    if header_row_index is None:
        raise ValueError("could not locate Koren2018 Table S7A header row")

    peptides: list[dict[str, Any]] = []
    for row in rows[header_row_index:]:
        peptide = str(row.get("L", "")).strip().upper()
        if peptide.endswith("*"):
            peptide = peptide[:-1]
        if len(peptide) != 23 or any(residue not in AA for residue in peptide):
            continue
        psi_raw = row.get("H")
        if psi_raw in ("", None):
            continue
        psi = float(psi_raw)
        end = peptide[-1]
        peptides.append(
            {
                "cend_score": frozen_score(end),
                "cterm23": peptide,
                "end_residue": end,
                "internal_aa_comp": internal_composition(peptide),
                "psi": round(psi, 6),
            }
        )
    if len(peptides) < 20000:
        raise ValueError(f"too few parsed peptide rows: {len(peptides)}")

    return {
        "meta": {
            "experiment_id": "degron_cterminal_crossdataset_koren2018",
            "source": SOURCE_URL,
            "sheet": sheet_name,
            "header_row": header_row_index,
            "header_H": header.get("H"),
            "header_L": header.get("L"),
            "n": len(peptides),
            "internal_composition": "AA counts in first 22 residues of the 23-mer; terminal residue excluded.",
            "leakage_guard": "PSI is measured GPS-FACS output; frozen C-end sequence rule is computed without fitting on Koren2018.",
            "frozen_rule": {
                "score_direction": "stability_signed",
                "destabilizing_terminal_residues_score_minus_1": sorted(DESTABILIZING_END),
                "stabilizing_terminal_residues_score_plus_1": sorted(STABILIZING_END),
                "other_terminal_residues_score_0": True,
                "fit_on_koren2018": False,
            },
        },
        "peptides": peptides,
    }


def provenance(payload: bytes, content_type: str) -> dict[str, Any]:
    return {
        "source_url": SOURCE_URL,
        "source_name": SOURCE_NAME,
        "accession_or_id": ACCESSION_OR_ID,
        "payload_sha256": hashlib.sha256(payload).hexdigest(),
        "payload_byte_size": len(payload),
        "content_type": content_type,
        "fetched_by": "bio-data-fetcher",
        "intended_claim_id": CLAIM_ID,
        "license_or_terms": "Elsevier-hosted Cell supplementary data; used here as source-provenanced public supplementary research data.",
        "raw_payload_encoding": "base64",
        "raw_payload_base64": base64.b64encode(payload).decode("ascii"),
    }


def write_manifest(payload: bytes, content_type: str) -> None:
    MANIFEST_DIR.mkdir(parents=True, exist_ok=True)
    manifest = {
        "fetched_at": utc_now(),
        "source_url": SOURCE_URL,
        "source_name": SOURCE_NAME,
        "accession_or_id": ACCESSION_OR_ID,
        "sha256": hashlib.sha256(payload).hexdigest(),
        "byte_size": len(payload),
        "content_type": content_type,
        "fetched_by": "bio-data-fetcher",
        "intended_claim_id": CLAIM_ID,
        "license_or_terms": "Elsevier-hosted Cell supplementary data; used here as source-provenanced public supplementary research data.",
    }
    MANIFEST_PATH.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    payload, content_type = fetch_bytes(SOURCE_URL)
    data = parse_payload(payload)
    data["provenance"] = provenance(payload, content_type)
    OUT_PATH.write_text(json.dumps(data, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    write_manifest(payload, content_type)
    print(json.dumps({"status": "fetched", "data_path": str(OUT_PATH), "manifest_path": str(MANIFEST_PATH), "n": len(data["peptides"])}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

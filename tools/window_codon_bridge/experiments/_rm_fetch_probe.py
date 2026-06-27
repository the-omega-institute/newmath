#!/usr/bin/env python3
"""Fetch carrier and plasmid availability inputs for the RM motif gate."""
from __future__ import annotations

from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import statistics
import time
from typing import Any
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
import zipfile

try:
    from ._asd_fetch_probe import (
        ASD_CACHE_DIR,
        FETCH_TIMEOUT,
        NCBI_DELAY_SECONDS,
        SUMMARY_TIMEOUT,
        assembly_summary_for_accession,
        cached_assembly_file,
        load_gtdb_taxonomy,
        ncbi_url,
        safe_name,
    )
except ImportError:  # pragma: no cover - direct script execution
    from _asd_fetch_probe import (  # type: ignore
        ASD_CACHE_DIR,
        FETCH_TIMEOUT,
        NCBI_DELAY_SECONDS,
        SUMMARY_TIMEOUT,
        assembly_summary_for_accession,
        cached_assembly_file,
        load_gtdb_taxonomy,
        ncbi_url,
        safe_name,
    )


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[2]
RM_CACHE_DIR = REPO_ROOT / "tools" / "window_codon_bridge" / "synced" / "rm_genomes"
USER_AGENT = "rm-motif-escape-predata-gate"
REBASE_ALLENZ_URL = "http://rebase.neb.com/rebase/link_allenz"
BLOW2016_DIR = RM_CACHE_DIR / "blow2016"
BLOW2016_S4_PATH = BLOW2016_DIR / "S4_motifs.xlsx"
BLOW2016_S5_PATH = BLOW2016_DIR / "S5_persite.xlsx"
XLSX_NS = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
XLSX_REL_NS = "{http://schemas.openxmlformats.org/package/2006/relationships}"
XLSX_OFFICE_REL_NS = "{http://schemas.openxmlformats.org/officeDocument/2006/relationships}"

IUPAC_ALPHABET = set("ACGTRYSWKMBDHVN")
IUPAC_DEGENERACY = {
    "A": 1,
    "C": 1,
    "G": 1,
    "T": 1,
    "R": 2,
    "Y": 2,
    "S": 2,
    "W": 2,
    "K": 2,
    "M": 2,
    "B": 3,
    "D": 3,
    "H": 3,
    "V": 3,
    "N": 4,
}
RC_TABLE = str.maketrans("ACGTRYSWKMBDHVN", "TGCAYRSWMKVHDBN")


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def deadline_expired(deadline: float | None) -> bool:
    return deadline is not None and time.monotonic() >= deadline


def fetch_bytes_with_backoff(
    url: str,
    timeout: int = FETCH_TIMEOUT,
    attempts: int = 4,
    deadline: float | None = None,
) -> tuple[bytes, dict[str, object]]:
    last_error = "fetch_failed"
    for attempt in range(1, attempts + 1):
        if deadline_expired(deadline):
            return b"", {
                "url": url,
                "reachable": False,
                "blocked": True,
                "error": "fetch_deadline_exceeded",
                "attempts": attempt - 1,
            }
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                payload = response.read()
                return payload, {
                    "url": url,
                    "reachable": True,
                    "http_status": int(getattr(response, "status", 200)),
                    "byte_size": len(payload),
                    "sha256": sha256_bytes(payload),
                    "attempts": attempt,
                }
        except urllib.error.HTTPError as exc:
            last_error = f"HTTPError:{exc.code}"
            if exc.code not in {429, 500, 502, 503, 504}:
                break
            retry_after = exc.headers.get("Retry-After") if exc.headers else None
            try:
                delay = float(retry_after) if retry_after else min(45.0, NCBI_DELAY_SECONDS * (2 ** attempt))
            except ValueError:
                delay = min(45.0, NCBI_DELAY_SECONDS * (2 ** attempt))
        except urllib.error.URLError as exc:
            last_error = f"URLError:{exc.reason}"
            delay = min(30.0, NCBI_DELAY_SECONDS * (2 ** attempt))
        except TimeoutError:
            last_error = "TimeoutError"
            delay = min(30.0, NCBI_DELAY_SECONDS * (2 ** attempt))
        time.sleep(delay)
    return b"", {"url": url, "reachable": False, "blocked": True, "error": last_error, "attempts": attempts}


def cached_rm_url(url: str, filename: str, deadline: float | None = None) -> tuple[str, dict[str, object]]:
    RM_CACHE_DIR.mkdir(parents=True, exist_ok=True)
    cache_path = RM_CACHE_DIR / filename
    if cache_path.exists() and cache_path.stat().st_size > 0:
        payload = cache_path.read_bytes()
        return payload.decode("utf-8", "replace"), {
            "url": url,
            "on_disk_cache_hit": True,
            "cache_path": str(cache_path),
            "byte_size": len(payload),
            "sha256": sha256_bytes(payload),
        }
    payload, contact = fetch_bytes_with_backoff(url, timeout=FETCH_TIMEOUT, attempts=4, deadline=deadline)
    if not payload:
        return "", contact
    cache_path.write_bytes(payload)
    return payload.decode("utf-8", "replace"), {**contact, "on_disk_cache_hit": False, "cache_path": str(cache_path)}


def reverse_complement_motif(motif: str) -> str:
    return motif.translate(RC_TABLE)[::-1]


def canonical_motif(motif: str) -> str:
    rc = reverse_complement_motif(motif)
    return motif if motif <= rc else rc


def motif_degeneracy(motif: str) -> int:
    value = 1
    for base in motif:
        value *= IUPAC_DEGENERACY.get(base, 0)
    return value


def normalize_recognition(raw: str) -> str | None:
    value = raw.upper().strip()
    if not value or value == "?":
        return None
    value = value.replace("^", "").replace("_", "").replace(" ", "")
    value = re.sub(r"\([^)]*\)", "", value)
    value = value.replace("/", "")
    if not value or any(ch not in IUPAC_ALPHABET for ch in value):
        return None
    return value


def xlsx_col_index(cell_ref: str) -> int:
    letters = re.sub(r"[^A-Za-z]", "", cell_ref)
    value = 0
    for ch in letters.upper():
        value = value * 26 + (ord(ch) - ord("A") + 1)
    return value - 1


def xlsx_shared_strings(zf: zipfile.ZipFile) -> list[str]:
    if "xl/sharedStrings.xml" not in zf.namelist():
        return []
    root = ET.fromstring(zf.read("xl/sharedStrings.xml"))
    strings = []
    for item in root.findall(XLSX_NS + "si"):
        strings.append("".join(node.text or "" for node in item.iter(XLSX_NS + "t")))
    return strings


def xlsx_sheet_path(zf: zipfile.ZipFile, sheet_name: str) -> str:
    workbook = ET.fromstring(zf.read("xl/workbook.xml"))
    rels = ET.fromstring(zf.read("xl/_rels/workbook.xml.rels"))
    rel_targets = {
        rel.attrib.get("Id", ""): rel.attrib.get("Target", "")
        for rel in rels.findall(XLSX_REL_NS + "Relationship")
    }
    for sheet in workbook.findall(".//" + XLSX_NS + "sheet"):
        if sheet.attrib.get("name") != sheet_name:
            continue
        rel_id = sheet.attrib.get(XLSX_OFFICE_REL_NS + "id", "")
        target = rel_targets.get(rel_id, "")
        if not target:
            break
        return "xl/" + target.lstrip("/")
    raise ValueError(f"sheet not found in xlsx: {sheet_name}")


def read_xlsx_rows(path: Path, sheet_name: str) -> list[list[str]]:
    with zipfile.ZipFile(path) as zf:
        shared = xlsx_shared_strings(zf)
        sheet_path = xlsx_sheet_path(zf, sheet_name)
        root = ET.fromstring(zf.read(sheet_path))
        rows = []
        for row in root.findall(".//" + XLSX_NS + "row"):
            values: dict[int, str] = {}
            for cell in row.findall(XLSX_NS + "c"):
                ref = cell.attrib.get("r", "")
                if not ref:
                    continue
                index = xlsx_col_index(ref)
                cell_type = cell.attrib.get("t", "")
                value_node = cell.find(XLSX_NS + "v")
                inline_node = cell.find(XLSX_NS + "is")
                value = ""
                if value_node is not None and value_node.text is not None:
                    value = value_node.text
                    if cell_type == "s":
                        try:
                            value = shared[int(value)]
                        except (IndexError, ValueError):
                            value = ""
                elif inline_node is not None:
                    value = "".join(node.text or "" for node in inline_node.iter(XLSX_NS + "t"))
                values[index] = value.strip()
            if values:
                max_index = max(values)
                rows.append([values.get(index, "") for index in range(max_index + 1)])
        return rows


def is_methyltransferase_name(name: str) -> bool:
    return bool(re.match(r"^(M|MTase)\.", name.strip(), re.I))


def is_restriction_like_name(name: str) -> bool:
    return not bool(re.match(r"^(M|S|V|C|H|N)\.", name.strip(), re.I))


def parse_rebase_allenz(text: str) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    blocks = re.split(r"\n(?=<1>)", text)
    for block in blocks:
        fields: dict[int, str] = {}
        for match in re.finditer(r"(?m)^<(\d+)>(.*)$", block):
            fields[int(match.group(1))] = match.group(2).strip()
        enzyme = fields.get(1, "")
        organism = fields.get(3, "")
        motif_raw = fields.get(5, "")
        motif = normalize_recognition(motif_raw)
        if not enzyme or not organism or motif is None:
            continue
        role = "methyltransferase" if is_methyltransferase_name(enzyme) else "restriction" if is_restriction_like_name(enzyme) else "other"
        rows.append(
            {
                "enzyme_name": enzyme,
                "prototype": fields.get(2, ""),
                "rebase_organism": organism,
                "source": fields.get(4, ""),
                "motif_raw": motif_raw,
                "motif_clean": motif,
                "motif_canonical": canonical_motif(motif),
                "motif_len": len(motif),
                "degeneracy": motif_degeneracy(motif),
                "palindrome_flag": motif == reverse_complement_motif(motif),
                "system_type": "Type II flatfile",
                "role": role,
                "reference_ids": fields.get(8, ""),
            }
        )
    return rows


def load_rebase_carriers(deadline: float | None = None) -> tuple[list[dict[str, object]], dict[str, object]]:
    text, contact = cached_rm_url(REBASE_ALLENZ_URL, "rebase_link_allenz.txt", deadline=deadline)
    if not text:
        return [], {"selected_source": REBASE_ALLENZ_URL, "source_kind": "allenz_flatfile", "contact": contact, "error": "rebase_fetch_failed"}
    rows = parse_rebase_allenz(text)
    return rows, {
        "selected_source": REBASE_ALLENZ_URL,
        "source_kind": "allenz_flatfile",
        "contact": contact,
        "n_raw_rebase_rows": len(rows),
        "note": "REBASE allenz provides organism-level host names, recognition sequence, and enzyme identity; assembly accession is not present.",
    }


def parse_blow2016_s4(path: Path = BLOW2016_S4_PATH) -> tuple[list[dict[str, object]], dict[str, object]]:
    if not path.exists():
        return [], {"selected_source": str(path), "source_kind": "blow2016_s4_xlsx", "error": "s4_xlsx_missing"}
    rows = read_xlsx_rows(path, "Table S4 - Motifs")
    data_rows = []
    skip = Counter()
    for row in rows[2:]:
        if len(row) < 10:
            skip["short_row"] += 1
            continue
        organism = row[0].strip()
        specificity = row[7].strip()
        motif = normalize_recognition(specificity)
        if not organism or motif is None:
            skip["missing_organism_or_motif"] += 1
            continue
        data_rows.append(
            {
                "blow_organism": organism,
                "rebase_organism": organism,
                "img_genome_id": row[1].strip() if len(row) > 1 else "",
                "rebase_org_number": row[2].strip() if len(row) > 2 else "",
                "gene_locus_tag": row[3].strip() if len(row) > 3 else "",
                "mtase_name": row[4].strip() if len(row) > 4 else "",
                "enzyme_name": row[4].strip() if len(row) > 4 else "",
                "system_type": row[5].strip() if len(row) > 5 else "",
                "modtype": row[6].strip() if len(row) > 6 else "",
                "motif_raw": specificity,
                "motif_clean": motif,
                "motif_canonical": canonical_motif(motif),
                "motif_len": len(motif),
                "degeneracy": motif_degeneracy(motif),
                "palindrome_flag": motif == reverse_complement_motif(motif),
                "detected_percent": row[8].strip() if len(row) > 8 else "",
                "mtase_match": row[9].strip() if len(row) > 9 else "",
                "rebase_cognate_re_names": row[10].strip() if len(row) > 10 else "",
            }
        )
    return data_rows, {
        "selected_source": str(path),
        "source_kind": "blow2016_s4_xlsx",
        "sheet": "Table S4 - Motifs",
        "n_xlsx_rows": len(rows),
        "n_raw_blow_rows": len(data_rows),
        "parse_skip_counts": dict(skip),
        "note": "Blow et al. 2016 PLOS Genetics Table S4 gives organism, MTase identity, type, modification class, motif, and match evidence.",
    }


def load_blow_carriers(deadline: float | None = None) -> tuple[list[dict[str, object]], dict[str, object]]:
    del deadline
    return parse_blow2016_s4()


def tier_a_blow_groups(rows: list[dict[str, object]]) -> tuple[list[dict[str, object]], dict[str, object]]:
    grouped: dict[tuple[str, str], list[dict[str, object]]] = defaultdict(list)
    skip = Counter()
    tier_a_4_8_hosts = set()
    tier_a_5_8_hosts = set()
    n_tier_a_raw_rows = 0
    for row in rows:
        system_type = str(row.get("system_type") or "").strip()
        mtase_match = str(row.get("mtase_match") or "")
        motif = str(row.get("motif_clean") or "")
        motif_len = int(row.get("motif_len") or 0)
        if system_type != "II":
            skip["type_not_II"] += 1
            continue
        if "match" not in mtase_match.lower():
            skip["mtase_not_matched"] += 1
            continue
        if motif_len < 4 or motif_len > 8:
            skip["motif_length_outside_4_8"] += 1
            continue
        if motif_degeneracy(motif) <= 0:
            skip["unparseable_iupac"] += 1
            continue
        if motif_degeneracy(motif) > 128:
            skip["extreme_degeneracy"] += 1
            continue
        organism = str(row["blow_organism"]).strip()
        key = (organism, str(row["motif_canonical"]))
        grouped[key].append(row)
        n_tier_a_raw_rows += 1
        tier_a_4_8_hosts.add(organism)
        if motif_len >= 5:
            tier_a_5_8_hosts.add(organism)

    carrier_rows: list[dict[str, object]] = []
    for (organism, motif), members in grouped.items():
        first = members[0]
        mtase_names = sorted({str(member.get("mtase_name") or "") for member in members if member.get("mtase_name")})
        carrier_rows.append(
            {
                "host_accession": "",
                "gtdb_family": "",
                "gtdb_genus": "",
                "blow_organism": organism,
                "rebase_organism": organism,
                "rm_system_id": "|".join(mtase_names[:8]),
                "mtase_name": mtase_names[0] if mtase_names else "",
                "enzyme_names": mtase_names,
                "motif_raw": str(first.get("motif_raw") or ""),
                "motif_canonical": motif,
                "motif_len": int(first.get("motif_len") or len(motif)),
                "degeneracy": motif_degeneracy(motif),
                "palindrome_flag": bool(first.get("palindrome_flag")),
                "system_type": "II",
                "type": "II",
                "modtype": str(first.get("modtype") or ""),
                "evidence_tier": "A",
                "match_mode": "unmapped",
                "source": "blow2016_s4",
                "rebase_org_number": str(first.get("rebase_org_number") or ""),
                "img_genome_id": str(first.get("img_genome_id") or ""),
                "gene_locus_tags": sorted({str(member.get("gene_locus_tag") or "") for member in members if member.get("gene_locus_tag")}),
                "mtase_match": str(first.get("mtase_match") or ""),
            }
        )
    carrier_rows.sort(key=lambda row: (str(row["blow_organism"]).lower(), str(row["motif_canonical"])))
    return carrier_rows, {
        "skip_counts": dict(skip),
        "n_tier_a_raw_rows_before_rc_merge": n_tier_a_raw_rows,
        "n_tier_a_unmapped": len(carrier_rows),
        "n_tier_a_4_8_hosts": len(tier_a_4_8_hosts),
        "n_tier_a_5_8_hosts": len(tier_a_5_8_hosts),
        "oracle_tier": "Type II + MTase match contains Match + canonical motif length 4-8 bp",
        "sensitivity_5_8_note": "The 5-8 bp host count is reported but the retained oracle carrier uses 4-8 bp.",
    }


def tier_a_rebase_groups(rows: list[dict[str, object]]) -> tuple[list[dict[str, object]], dict[str, object]]:
    grouped: dict[tuple[str, str], list[dict[str, object]]] = defaultdict(list)
    skip = Counter()
    for row in rows:
        motif_len = int(row.get("motif_len") or 0)
        motif = str(row.get("motif_clean") or "")
        if motif_len < 4 or motif_len > 8:
            skip["motif_length_outside_4_8"] += 1
            continue
        if motif_degeneracy(motif) <= 0:
            skip["unparseable_iupac"] += 1
            continue
        if motif_degeneracy(motif) > 128:
            skip["extreme_degeneracy"] += 1
            continue
        key = (str(row["rebase_organism"]).strip(), str(row["motif_canonical"]))
        grouped[key].append(row)
    carrier_rows: list[dict[str, object]] = []
    for (organism, motif), members in grouped.items():
        roles = {str(member.get("role") or "") for member in members}
        if "restriction" not in roles:
            skip["methyltransferase_or_nonrestriction_only"] += 1
            continue
        first = members[0]
        evidence_tier = "paired_restriction_modification" if "methyltransferase" in roles else "restriction_observed"
        enzymes = sorted({str(member.get("enzyme_name") or "") for member in members if member.get("enzyme_name")})
        carrier_rows.append(
            {
                "host_accession": "",
                "gtdb_family": "",
                "gtdb_genus": "",
                "rebase_organism": organism,
                "rm_system_id": "|".join(enzymes[:8]),
                "enzyme_names": enzymes,
                "motif_raw": str(first.get("motif_raw") or ""),
                "motif_canonical": motif,
                "motif_len": int(first.get("motif_len") or len(motif)),
                "degeneracy": motif_degeneracy(motif),
                "palindrome_flag": bool(first.get("palindrome_flag")),
                "system_type": str(first.get("system_type") or "Type II flatfile"),
                "evidence_tier": evidence_tier,
                "match_mode": "unmapped",
            }
        )
    carrier_rows.sort(key=lambda row: (str(row["rebase_organism"]).lower(), str(row["motif_canonical"])))
    return carrier_rows, {"skip_counts": dict(skip), "n_tier_a_unmapped": len(carrier_rows)}


def cached_json(path: Path) -> Any | None:
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=True, sort_keys=True), encoding="utf-8")


def esearch_assembly_ids(term: str, retmax: int, deadline: float | None = None) -> tuple[list[str], dict[str, object]]:
    url = ncbi_url("esearch", {"db": "assembly", "term": term, "retmax": retmax, "sort": "relevance"})
    payload, contact = fetch_bytes_with_backoff(url, timeout=SUMMARY_TIMEOUT, attempts=2, deadline=deadline)
    if not payload:
        return [], {"search": contact, "error": "assembly_search_failed", "term": term}
    try:
        root = ET.fromstring(payload.decode("utf-8", "replace"))
    except ET.ParseError as exc:
        return [], {"search": contact, "parse_error": str(exc), "term": term}
    ids = [node.text.strip() for node in root.findall(".//Id") if node.text and node.text.strip()]
    return ids, {"search": contact, "term": term, "n_ids": len(ids)}


def esummary_assembly_id(assembly_id: str, deadline: float | None = None) -> tuple[dict[str, object] | None, dict[str, object]]:
    time.sleep(NCBI_DELAY_SECONDS)
    url = ncbi_url("esummary", {"db": "assembly", "id": assembly_id, "report": "full"})
    payload, contact = fetch_bytes_with_backoff(url, timeout=SUMMARY_TIMEOUT, attempts=2, deadline=deadline)
    if not payload:
        return None, {"summary": contact, "error": "assembly_summary_failed", "assembly_id": assembly_id}
    try:
        root = ET.fromstring(payload.decode("utf-8", "replace"))
    except ET.ParseError as exc:
        return None, {"summary": contact, "parse_error": str(exc), "assembly_id": assembly_id}
    node = root.find(".//DocumentSummary")
    if node is None:
        return None, {"summary": contact, "error": "document_summary_not_found", "assembly_id": assembly_id}
    ftp = node.findtext("FtpPath_RefSeq") or node.findtext("FtpPath_GenBank") or ""
    row = {
        "assembly_accession": node.findtext("AssemblyAccession") or "",
        "organism": node.findtext("Organism") or "",
        "species_name": node.findtext("SpeciesName") or node.findtext("Organism") or "",
        "taxid": node.findtext("Taxid") or "",
        "ftp_path": ftp,
        "assembly_status": node.findtext("AssemblyStatus") or "",
        "refseq_category": node.findtext("RefSeq_category") or "",
    }
    if not row["assembly_accession"] or not ftp:
        return None, {"summary": contact, "error": "assembly_accession_or_ftp_missing", "assembly_id": assembly_id}
    return row, {"summary": contact, "assembly_id": assembly_id}


def assembly_summary_for_organism(organism: str, deadline: float | None = None) -> tuple[dict[str, object] | None, dict[str, object]]:
    RM_CACHE_DIR.mkdir(parents=True, exist_ok=True)
    cache_path = RM_CACHE_DIR / f"{safe_name(organism)}_organism_assembly_summary.json"
    cached = cached_json(cache_path)
    if isinstance(cached, dict) and cached.get("row"):
        return cached["row"], {"on_disk_cache_hit": True, "cache_path": str(cache_path), "match_mode": cached.get("match_mode", "organism_search")}
    terms = [
        f'"{organism}"[Organism] AND latest[filter] AND (complete genome[filter] OR chromosome level[filter])',
        f'"{organism}"[All Fields] AND latest[filter] AND (complete genome[filter] OR chromosome level[filter])',
        f'"{organism}"[All Fields] AND latest[filter]',
        f"{organism}[All Fields]",
        organism,
    ]
    contacts: list[dict[str, object]] = []
    for index, term in enumerate(terms):
        if deadline_expired(deadline):
            break
        ids, contact = esearch_assembly_ids(term, retmax=5, deadline=deadline)
        contacts.append(contact)
        if not ids:
            continue
        for assembly_id in ids:
            row, summary_contact = esummary_assembly_id(assembly_id, deadline=deadline)
            contacts.append(summary_contact)
            if not row:
                continue
            match_mode = "organism_exact_name_search" if index == 0 else "organism_text_search"
            payload = {"row": row, "match_mode": match_mode, "queried_organism": organism}
            write_json(cache_path, payload)
            return row, {"on_disk_cache_hit": False, "cache_path": str(cache_path), "match_mode": match_mode, "contacts": contacts}
    write_json(cache_path, {"row": None, "match_mode": "unmapped", "queried_organism": organism, "contacts": contacts})
    return None, {"on_disk_cache_hit": False, "cache_path": str(cache_path), "match_mode": "unmapped", "contacts": contacts, "error": "organism_mapping_failed"}


def load_blow_s5_nc_crosswalk(path: Path = BLOW2016_S5_PATH) -> tuple[dict[str, str], dict[str, object]]:
    if not path.exists():
        return {}, {"selected_source": str(path), "source_kind": "blow2016_s5_xlsx", "error": "s5_xlsx_missing"}
    rows = read_xlsx_rows(path, "S5 Table")
    crosswalk: dict[str, str] = {}
    scaffold_counts = Counter()
    for row in rows[1:]:
        if len(row) <= 4:
            continue
        organism = row[0].strip()
        scaffold = row[4].strip()
        match = re.search(r"\b(NC_\d+(?:\.\d+)?)\b", scaffold)
        if not organism or not match:
            continue
        accession = match.group(1)
        scaffold_counts[organism] += 1
        crosswalk.setdefault(organism, accession)
    return crosswalk, {
        "selected_source": str(path),
        "source_kind": "blow2016_s5_xlsx",
        "sheet": "S5 Table",
        "n_xlsx_rows": len(rows),
        "n_organisms_with_nc_accession": len(crosswalk),
        "n_nc_scaffold_rows": sum(scaffold_counts.values()),
    }


def gtdb_lookup_from_rows(limit_genera: int = 200000, deadline: float | None = None) -> tuple[dict[str, dict[str, str]], dict[str, object]]:
    lookup: dict[str, dict[str, str]] = {}
    contacts = {}
    for domain in ("Bacteria", "Archaea"):
        rows, contact = load_gtdb_taxonomy(domain, limit_genera=limit_genera, deadline=deadline)
        contacts[domain] = contact
        for row in rows:
            accession = str(row.get("assembly_accession") or "")
            if accession:
                lookup[accession] = {
                    "domain": str(row.get("domain") or domain),
                    "gtdb_genus": str(row.get("gtdb_genus") or row.get("genus") or ""),
                    "gtdb_family": str(row.get("family") or ""),
                    "gtdb_order": str(row.get("order") or ""),
                }
    return lookup, {"contacts": contacts, "n_gtdb_accessions": len(lookup)}


def infer_family_genus(assembly_row: dict[str, object], gtdb_lookup: dict[str, dict[str, str]]) -> dict[str, str]:
    accession = str(assembly_row.get("assembly_accession") or "")
    if accession in gtdb_lookup:
        return gtdb_lookup[accession]
    organism = str(assembly_row.get("organism") or assembly_row.get("species_name") or "")
    genus = organism.split()[0] if organism.split() else ""
    return {"domain": "", "gtdb_genus": genus, "gtdb_family": f"unmapped_family:{genus}" if genus else "", "gtdb_order": ""}


def map_carriers_to_assemblies(
    carrier_rows: list[dict[str, object]],
    host_limit: int | None = None,
    deadline: float | None = None,
) -> tuple[list[dict[str, object]], dict[str, object]]:
    gtdb_lookup, gtdb_meta = gtdb_lookup_from_rows(deadline=deadline)
    blow_crosswalk, blow_crosswalk_meta = load_blow_s5_nc_crosswalk()
    by_organism: dict[str, list[dict[str, object]]] = defaultdict(list)
    for row in carrier_rows:
        by_organism[str(row["rebase_organism"])].append(row)
    organisms = sorted(by_organism)
    if host_limit is not None and host_limit > 0:
        organisms = organisms[:host_limit]
    mapped: list[dict[str, object]] = []
    mapping_counts = Counter()
    for organism in organisms:
        if deadline_expired(deadline):
            mapping_counts["deadline_skipped"] += 1
            break
        s5_accession = blow_crosswalk.get(organism, "")
        if s5_accession:
            assembly_row, contact = assembly_summary_for_accession(s5_accession, deadline=deadline)
            if contact.get("error"):
                fallback_row, fallback_contact = assembly_summary_for_organism(organism, deadline=deadline)
                if fallback_row:
                    assembly_row = fallback_row
                    contact = fallback_contact
                else:
                    contact = {**contact, "match_mode": "unmapped", "s5_nc_accession": s5_accession, "fallback": fallback_contact}
            else:
                contact = {**contact, "match_mode": "assembly_exact_s5_nc_accession", "s5_nc_accession": s5_accession}
        else:
            assembly_row, contact = assembly_summary_for_organism(organism, deadline=deadline)
        if not assembly_row:
            mapping_counts["unmapped"] += 1
            continue
        accession = str(assembly_row.get("assembly_accession") or "")
        tax = infer_family_genus(assembly_row, gtdb_lookup)
        match_mode = str(contact.get("match_mode") or "organism_search")
        mapping_counts[match_mode] += 1
        for row in by_organism[organism]:
            item = dict(row)
            item["host_accession"] = accession
            item["host_organism"] = str(assembly_row.get("organism") or "")
            item["host_ftp_path"] = str(assembly_row.get("ftp_path") or "")
            item["host_assembly_status"] = str(assembly_row.get("assembly_status") or "")
            item["gtdb_family"] = tax.get("gtdb_family", "")
            item["gtdb_genus"] = tax.get("gtdb_genus", "")
            item["match_mode"] = match_mode
            if s5_accession:
                item["blow_s5_nc_accession"] = s5_accession
            mapped.append(item)
    return mapped, {
        "n_organisms_considered": len(organisms),
        "n_mapped_carrier_rows": len(mapped),
        "n_mapped_hosts": len({row["host_accession"] for row in mapped}),
        "mapping_counts": dict(mapping_counts),
        "gtdb": gtdb_meta,
        "blow_s5_crosswalk": blow_crosswalk_meta,
    }


def parse_fasta_full(text: str) -> list[tuple[str, str]]:
    records: list[tuple[str, str]] = []
    header = ""
    chunks: list[str] = []
    for line in text.splitlines():
        if line.startswith(">"):
            if header:
                records.append((header, "".join(chunks).upper()))
            header = line[1:].strip()
            chunks = []
        else:
            chunks.append(re.sub(r"[^A-Za-z]", "", line))
    if header:
        records.append((header, "".join(chunks).upper()))
    return records


def is_plasmid_header(header: str) -> bool:
    lower = header.lower()
    return "plasmid" in lower or re.search(r"\bplasmid[:_\s-]", lower) is not None


def plasmid_inventory_for_host(
    accession: str,
    ftp_path: str,
    deadline: float | None = None,
) -> tuple[dict[str, object], dict[str, object]]:
    cache_path = RM_CACHE_DIR / f"{safe_name(accession)}_plasmid_inventory.json"
    cached = cached_json(cache_path)
    if isinstance(cached, dict) and cached.get("host_accession") == accession:
        return cached, {"on_disk_cache_hit": True, "cache_path": str(cache_path)}
    text, contact = cached_assembly_file(ftp_path, "genomic.fna.gz", accession, deadline=deadline)
    if not text:
        row = {
            "host_accession": accession,
            "target_type": "plasmid",
            "num_targets": 0,
            "total_target_bp": 0,
            "median_target_len": 0,
            "target_accessions": [],
            "error": "genomic_fna_fetch_failed",
        }
        write_json(cache_path, row)
        return row, {"fetch": contact, "cache_path": str(cache_path)}
    lengths = []
    target_accessions = []
    for header, seq in parse_fasta_full(text):
        if not is_plasmid_header(header):
            continue
        clean = re.sub(r"[^ACGT]", "", seq.upper())
        if not clean:
            continue
        lengths.append(len(clean))
        target_accessions.append(header.split()[0])
    row = {
        "host_accession": accession,
        "target_type": "plasmid",
        "num_targets": len(lengths),
        "total_target_bp": sum(lengths),
        "median_target_len": statistics.median(lengths) if lengths else 0,
        "target_accessions": target_accessions[:50],
    }
    write_json(cache_path, row)
    return row, {"fetch": contact, "cache_path": str(cache_path)}


def plasmid_target_inventory(
    mapped_carriers: list[dict[str, object]],
    deadline: float | None = None,
) -> tuple[list[dict[str, object]], dict[str, object]]:
    hosts: dict[str, str] = {}
    for row in mapped_carriers:
        accession = str(row.get("host_accession") or "")
        ftp_path = str(row.get("host_ftp_path") or "")
        if accession and ftp_path:
            hosts[accession] = ftp_path
    inventory = []
    errors = Counter()
    for accession, ftp_path in sorted(hosts.items()):
        if deadline_expired(deadline):
            errors["deadline_skipped"] += 1
            break
        row, _contact = plasmid_inventory_for_host(accession, ftp_path, deadline=deadline)
        if row.get("error"):
            errors[str(row["error"])] += 1
        inventory.append(row)
    return inventory, {"n_hosts_checked": len(inventory), "errors": dict(errors), "assembly_cache_dir": str(ASD_CACHE_DIR)}


def carrier_rows_by_host(mapped_carriers: list[dict[str, object]]) -> dict[str, list[dict[str, object]]]:
    by_host: dict[str, list[dict[str, object]]] = defaultdict(list)
    for row in mapped_carriers:
        accession = str(row.get("host_accession") or "")
        if accession:
            by_host[accession].append(row)
    return by_host


def host_inventory_map(inventory: list[dict[str, object]]) -> dict[str, dict[str, object]]:
    return {str(row.get("host_accession") or ""): row for row in inventory if row.get("host_accession")}

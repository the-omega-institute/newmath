#!/usr/bin/env python3
"""Fetch and parse genomes for the ASD-shadow exclusion pilot."""
from __future__ import annotations

from collections import Counter, defaultdict
from datetime import datetime, timezone
import gzip
import hashlib
import json
import os
from pathlib import Path
import random
import re
import time
from typing import Any
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET


EXPERIMENT_ID = "asd_shadow_exclusion_fetch_probe"
USER_AGENT = "asd-shadow-exclusion-pilot"
NCBI_DELAY_SECONDS = float(os.environ.get("ASD_NCBI_DELAY_SECONDS", "0.34"))
FETCH_TIMEOUT = int(os.environ.get("ASD_FETCH_TIMEOUT", "45"))
SUMMARY_TIMEOUT = int(os.environ.get("ASD_SUMMARY_TIMEOUT", "20"))
DEFAULT_FETCH_DEADLINE_SECONDS = float(os.environ.get("ASD_FETCH_DEADLINE_SECONDS", "120"))

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[2]
ASD_CACHE_DIR = REPO_ROOT / "tools" / "window_codon_bridge" / "synced" / "asd_genomes"
KFU_CACHE_DIR = REPO_ROOT / "tools" / "window_codon_bridge" / "synced" / "codon_e1_known_force_union_genomes"

GTDB_URLS = {
    "Bacteria": "https://data.gtdb.ecogenomic.org/releases/latest/bac120_taxonomy.tsv.gz",
    "Archaea": "https://data.gtdb.ecogenomic.org/releases/latest/ar53_taxonomy.tsv.gz",
}

BASES_DNA = set("ACGT")
BASES_RNA = set("ACGU")

CODON_TO_AA = {
    "UUU": "F", "UUC": "F", "UUA": "L", "UUG": "L",
    "UCU": "S", "UCC": "S", "UCA": "S", "UCG": "S",
    "UAU": "Y", "UAC": "Y", "UAA": "*", "UAG": "*",
    "UGU": "C", "UGC": "C", "UGA": "*", "UGG": "W",
    "CUU": "L", "CUC": "L", "CUA": "L", "CUG": "L",
    "CCU": "P", "CCC": "P", "CCA": "P", "CCG": "P",
    "CAU": "H", "CAC": "H", "CAA": "Q", "CAG": "Q",
    "CGU": "R", "CGC": "R", "CGA": "R", "CGG": "R",
    "AUU": "I", "AUC": "I", "AUA": "I", "AUG": "M",
    "ACU": "T", "ACC": "C", "ACA": "T", "ACG": "T",
    "AAU": "N", "AAC": "N", "AAA": "K", "AAG": "K",
    "AGU": "S", "AGC": "S", "AGA": "R", "AGG": "R",
    "GUU": "V", "GUC": "V", "GUA": "V", "GUG": "V",
    "GCU": "A", "GCC": "A", "GCA": "A", "GCG": "A",
    "GAU": "D", "GAC": "D", "GAA": "E", "GAG": "E",
    "GGU": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}
CODON_TO_AA["ACC"] = "T"

ROSTER_BACTERIA = (
    ("GCF_000005845.2", "Escherichia coli str. K-12 substr. MG1655", "escherichia"),
    ("GCF_000195955.2", "Bacillus subtilis subsp. subtilis str. 168", "bacillus"),
    ("GCF_000009045.1", "Streptococcus pneumoniae TIGR4", "streptococcus"),
    ("GCF_000006765.1", "Pseudomonas aeruginosa PAO1", "pseudomonas"),
    ("GCF_000195995.1", "Mycobacterium tuberculosis H37Rv", "mycobacterium"),
    ("GCF_000006745.1", "Vibrio cholerae O1 biovar El Tor str. N16961", "vibrio"),
    ("GCF_000008725.1", "Borrelia burgdorferi B31", "borrelia"),
    ("GCF_000007125.1", "Brucella abortus bv. 1 str. 9-941", "brucella"),
    ("GCF_000008805.1", "Chlamydia trachomatis D/UW-3/CX", "chlamydia"),
    ("GCF_000006945.2", "Salmonella enterica subsp. enterica serovar Typhimurium LT2", "salmonella"),
    ("GCF_000013425.1", "Staphylococcus aureus subsp. aureus NCTC 8325", "staphylococcus"),
    ("GCF_000196095.1", "Helicobacter pylori 26695", "helicobacter"),
    ("GCF_000008525.1", "Caulobacter vibrioides CB15", "caulobacter"),
    ("GCF_000009725.1", "Lactococcus lactis subsp. lactis Il1403", "lactococcus"),
    ("GCF_000006905.1", "Synechocystis sp. PCC 6803", "synechocystis"),
    ("GCF_000009425.1", "Clostridioides difficile 630", "clostridioides"),
    ("GCF_000006885.1", "Thermotoga maritima MSB8", "thermotoga"),
    ("GCF_000011965.2", "Bacteroides thetaiotaomicron VPI-5482", "bacteroides"),
)

ROSTER_ARCHAEA = (
    ("GCF_000007305.1", "Pyrococcus furiosus DSM 3638", "pyrococcus"),
    ("GCF_000091665.1", "Methanocaldococcus jannaschii DSM 2661", "methanocaldococcus"),
    ("GCF_000008265.1", "Picrophilus oshimae DSM 9789", "picrophilus"),
    ("GCF_000012285.1", "Sulfolobus acidocaldarius DSM 639", "sulfolobus"),
    ("GCF_000006805.1", "Halobacterium salinarum NRC-1", "halobacterium"),
    ("GCF_000025685.1", "Haloferax volcanii DS2", "haloferax"),
    ("GCF_000009965.1", "Thermococcus kodakarensis KOD1", "thermococcus"),
    ("GCF_000008665.1", "Archaeoglobus fulgidus DSM 4304", "archaeoglobus"),
    ("GCF_000011585.1", "Methanococcus maripaludis S2", "methanococcus"),
    ("GCF_000007225.1", "Pyrobaculum aerophilum str. IM2", "pyrobaculum"),
)

FAMILY_HINTS = {
    "escherichia": ("Enterobacterales", "Enterobacteriaceae"),
    "salmonella": ("Enterobacterales", "Enterobacteriaceae"),
    "bacillus": ("Bacillales", "Bacillaceae"),
    "staphylococcus": ("Bacillales", "Staphylococcaceae"),
    "streptococcus": ("Lactobacillales", "Streptococcaceae"),
    "lactococcus": ("Lactobacillales", "Streptococcaceae"),
    "pseudomonas": ("Pseudomonadales", "Pseudomonadaceae"),
    "vibrio": ("Vibrionales", "Vibrionaceae"),
    "mycobacterium": ("Mycobacteriales", "Mycobacteriaceae"),
    "borrelia": ("Borreliaceae", "Borreliaceae"),
    "brucella": ("Hyphomicrobiales", "Brucellaceae"),
    "chlamydia": ("Chlamydiales", "Chlamydiaceae"),
    "helicobacter": ("Campylobacterales", "Helicobacteraceae"),
    "caulobacter": ("Caulobacterales", "Caulobacteraceae"),
    "synechocystis": ("Synechococcales", "Merismopediaceae"),
    "clostridioides": ("Eubacteriales", "Peptostreptococcaceae"),
    "thermotoga": ("Thermotogales", "Thermotogaceae"),
    "bacteroides": ("Bacteroidales", "Bacteroidaceae"),
    "pyrococcus": ("Thermococcales", "Thermococcaceae"),
    "thermococcus": ("Thermococcales", "Thermococcaceae"),
    "methanocaldococcus": ("Methanococcales", "Methanocaldococcaceae"),
    "methanococcus": ("Methanococcales", "Methanococcaceae"),
    "picrophilus": ("Thermoplasmatales", "Picrophilaceae"),
    "sulfolobus": ("Sulfolobales", "Sulfolobaceae"),
    "halobacterium": ("Halobacteriales", "Halobacteriaceae"),
    "haloferax": ("Halobacteriales", "Haloferacaceae"),
    "archaeoglobus": ("Archaeoglobales", "Archaeoglobaceae"),
    "pyrobaculum": ("Thermoproteales", "Thermoproteaceae"),
}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def deadline_expired(deadline: float | None) -> bool:
    return deadline is not None and time.monotonic() >= deadline


def safe_name(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", value.strip())[:180]


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def fetch_bytes(url: str, timeout: int = FETCH_TIMEOUT, attempts: int = 4, deadline: float | None = None) -> tuple[bytes, dict[str, object]]:
    last_error = "fetch_failed"
    for attempt in range(1, attempts + 1):
        if deadline_expired(deadline):
            return b"", {"url": url, "reachable": False, "blocked": True, "error": "fetch_deadline_exceeded", "attempts": attempt - 1}
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
        except Exception as exc:  # pragma: no cover - network boundary
            last_error = f"{type(exc).__name__}:{exc}"
            delay = min(30.0, NCBI_DELAY_SECONDS * (2 ** attempt))
        time.sleep(delay)
    return b"", {"url": url, "reachable": False, "blocked": True, "error": last_error, "attempts": attempts}


def fetch_text(url: str, timeout: int = FETCH_TIMEOUT, attempts: int = 4, deadline: float | None = None) -> tuple[str, dict[str, object]]:
    payload, contact = fetch_bytes(url, timeout=timeout, attempts=attempts, deadline=deadline)
    if not payload:
        return "", contact
    return payload.decode("utf-8", "replace"), contact


def cached_url_bytes(url: str, cache_path: Path, timeout: int = FETCH_TIMEOUT, attempts: int = 4, deadline: float | None = None) -> tuple[bytes, dict[str, object]]:
    cache_path.parent.mkdir(parents=True, exist_ok=True)
    if cache_path.exists() and cache_path.stat().st_size > 0:
        payload = cache_path.read_bytes()
        return payload, {
            "url": url,
            "reachable": True,
            "on_disk_cache_hit": True,
            "byte_size": len(payload),
            "sha256": sha256_bytes(payload),
            "cache_path": str(cache_path),
        }
    payload, contact = fetch_bytes(url, timeout=timeout, attempts=attempts, deadline=deadline)
    if payload:
        cache_path.write_bytes(payload)
        contact = {**contact, "on_disk_cache_hit": False, "cache_path": str(cache_path)}
    return payload, contact


def ncbi_url(endpoint: str, params: dict[str, object]) -> str:
    return f"https://eutils.ncbi.nlm.nih.gov/entrez/eutils/{endpoint}.fcgi?{urllib.parse.urlencode(params)}"


def https_ftp_path(ftp_path: str) -> str:
    return "https://" + ftp_path[len("ftp://") :] if ftp_path.startswith("ftp://") else ftp_path


def strip_gtdb_accession(accession: str) -> str:
    value = accession.strip()
    if value.startswith(("RS_", "GB_")):
        value = value[3:]
    return value


def parse_taxonomy_line(raw: str) -> dict[str, str]:
    ranks = {}
    for item in raw.split(";"):
        if "__" not in item:
            continue
        prefix, name = item.split("__", 1)
        key = {
            "d": "domain",
            "p": "phylum",
            "c": "class",
            "o": "order",
            "f": "family",
            "g": "genus",
            "s": "species",
        }.get(prefix)
        if key:
            ranks[key] = name
    return ranks


def load_gtdb_taxonomy(domain: str, limit_genera: int, deadline: float | None = None) -> tuple[list[dict[str, object]], dict[str, object]]:
    if limit_genera <= 0:
        return [], {"skipped": True, "reason": "zero_limit"}
    url = GTDB_URLS[domain]
    cache_path = ASD_CACHE_DIR / f"{domain.lower()}_taxonomy.tsv.gz"
    payload, contact = cached_url_bytes(url, cache_path, timeout=60, attempts=2, deadline=deadline)
    if not payload:
        return [], contact
    try:
        text = gzip.decompress(payload).decode("utf-8", "replace")
    except Exception as exc:
        return [], {**contact, "decompress_error": f"{type(exc).__name__}:{exc}"}
    rows: list[dict[str, object]] = []
    seen_genera: set[str] = set()
    for line in text.splitlines():
        if not line.strip():
            continue
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        accession = strip_gtdb_accession(parts[0])
        ranks = parse_taxonomy_line(parts[1])
        genus = str(ranks.get("genus") or "").strip()
        if not accession or not genus or genus in seen_genera:
            continue
        if not accession.startswith(("GCF_", "GCA_")):
            continue
        seen_genera.add(genus)
        rows.append(
            {
                "assembly_accession": accession,
                "domain": domain,
                "genus": genus.lower(),
                "gtdb_genus": genus,
                "family": ranks.get("family") or "",
                "order": ranks.get("order") or "",
                "source": "gtdb_taxonomy",
            }
        )
        if len(rows) >= limit_genera:
            break
    return rows, {**contact, "n_rows": len(rows), "n_taxonomy_lines": len(text.splitlines())}


def roster_rows(domain: str, limit: int) -> list[dict[str, object]]:
    roster = ROSTER_BACTERIA if domain == "Bacteria" else ROSTER_ARCHAEA
    rows = []
    for accession, organism, genus in roster[:limit]:
        order, family = FAMILY_HINTS.get(genus, ("", ""))
        rows.append(
            {
                "assembly_accession": accession,
                "organism": organism,
                "domain": domain,
                "genus": genus,
                "family": family,
                "order": order,
                "source": "curated_refseq_roster",
            }
        )
    return rows


def assembly_summary_for_accession(accession: str, deadline: float | None = None) -> tuple[dict[str, object] | None, dict[str, object]]:
    cached = ASD_CACHE_DIR / f"{safe_name(accession)}_assembly_summary.json"
    if cached.exists():
        try:
            payload = json.loads(cached.read_text(encoding="utf-8"))
            if isinstance(payload, dict) and payload.get("ftp_path"):
                return payload, {"on_disk_cache_hit": True, "cache_path": str(cached)}
        except json.JSONDecodeError:
            pass
    search_url = ncbi_url("esearch", {"db": "assembly", "term": accession, "retmax": 1})
    text, search_contact = fetch_text(search_url, timeout=SUMMARY_TIMEOUT, attempts=2, deadline=deadline)
    if not text:
        return None, {"search": search_contact, "error": "assembly_search_failed"}
    try:
        root = ET.fromstring(text)
    except ET.ParseError as exc:
        return None, {"search": search_contact, "parse_error": str(exc)}
    assembly_id = root.findtext(".//Id")
    if not assembly_id:
        return None, {"search": search_contact, "error": "assembly_id_not_found"}
    time.sleep(NCBI_DELAY_SECONDS)
    summary_url = ncbi_url("esummary", {"db": "assembly", "id": assembly_id, "report": "full"})
    text, summary_contact = fetch_text(summary_url, timeout=SUMMARY_TIMEOUT, attempts=2, deadline=deadline)
    if not text:
        return None, {"search": search_contact, "summary": summary_contact, "error": "assembly_summary_failed"}
    try:
        root = ET.fromstring(text)
    except ET.ParseError as exc:
        return None, {"search": search_contact, "summary": summary_contact, "parse_error": str(exc)}
    node = root.find(".//DocumentSummary")
    if node is None:
        return None, {"search": search_contact, "summary": summary_contact, "error": "document_summary_not_found"}
    ftp = node.findtext("FtpPath_RefSeq") or node.findtext("FtpPath_GenBank") or ""
    if not ftp:
        return None, {"search": search_contact, "summary": summary_contact, "error": "assembly_ftp_not_found"}
    row = {
        "assembly_accession": node.findtext("AssemblyAccession") or accession,
        "organism": node.findtext("Organism") or "",
        "species_name": node.findtext("SpeciesName") or node.findtext("Organism") or "",
        "taxid": node.findtext("Taxid") or "",
        "ftp_path": ftp,
        "assembly_status": node.findtext("AssemblyStatus") or "",
        "refseq_category": node.findtext("RefSeq_category") or "",
    }
    cached.parent.mkdir(parents=True, exist_ok=True)
    cached.write_text(json.dumps(row, ensure_ascii=True, sort_keys=True), encoding="utf-8")
    return row, {"search": search_contact, "summary": summary_contact, "on_disk_cache_hit": False, "cache_path": str(cached)}


def cached_assembly_file(ftp_path: str, suffix: str, cache_key: str, deadline: float | None = None) -> tuple[str, dict[str, object]]:
    base = https_ftp_path(ftp_path).rstrip("/")
    stem = base.rsplit("/", 1)[-1]
    url = f"{base}/{stem}_{suffix}"
    cache_path = ASD_CACHE_DIR / f"{safe_name(cache_key)}_{suffix}"
    if not cache_path.exists():
        kfu_path = KFU_CACHE_DIR / f"{safe_name(cache_key)}_{suffix}"
        if kfu_path.exists() and kfu_path.stat().st_size > 0:
            payload = kfu_path.read_bytes()
            source = {
                "url": url,
                "reachable": True,
                "borrowed_cache_hit": True,
                "byte_size": len(payload),
                "sha256": sha256_bytes(payload),
                "cache_path": str(kfu_path),
            }
        else:
            payload, source = cached_url_bytes(url, cache_path, timeout=FETCH_TIMEOUT, attempts=3, deadline=deadline)
            time.sleep(NCBI_DELAY_SECONDS)
    else:
        payload = cache_path.read_bytes()
        source = {
            "url": url,
            "reachable": True,
            "on_disk_cache_hit": True,
            "byte_size": len(payload),
            "sha256": sha256_bytes(payload),
            "cache_path": str(cache_path),
        }
    if not payload:
        return "", source
    try:
        text = gzip.decompress(payload).decode("utf-8", "replace") if suffix.endswith(".gz") else payload.decode("utf-8", "replace")
    except Exception as exc:
        return "", {**source, "decompress_error": f"{type(exc).__name__}:{exc}"}
    return text, {**source, "decompressed_chars": len(text)}


def parse_fasta_records(text: str) -> dict[str, str]:
    records: dict[str, str] = {}
    header = ""
    chunks: list[str] = []
    for line in text.splitlines():
        if line.startswith(">"):
            if header:
                records[header.split()[0]] = "".join(chunks).upper()
            header = line[1:].strip()
            chunks = []
        else:
            chunks.append(re.sub(r"[^A-Za-z]", "", line))
    if header:
        records[header.split()[0]] = "".join(chunks).upper()
    return records


def parse_gff_attributes(raw: str) -> dict[str, str]:
    attrs = {}
    for part in raw.split(";"):
        if "=" not in part:
            continue
        key, value = part.split("=", 1)
        attrs[urllib.parse.unquote(key)] = urllib.parse.unquote(value)
    return attrs


def reverse_complement_dna(seq: str) -> str:
    return seq.translate(str.maketrans("ACGTacgt", "TGCAtgca"))[::-1].upper()


def dna_to_rna(seq: str) -> str:
    return seq.upper().replace("T", "U")


def parse_origin(lines: list[str]) -> str:
    chunks: list[str] = []
    in_origin = False
    for line in lines:
        if line.startswith("ORIGIN"):
            in_origin = True
            continue
        if in_origin:
            if line.startswith("//"):
                break
            chunks.append(re.sub(r"[^A-Za-z]", "", line).upper())
    return "".join(chunks)


def parse_features(lines: list[str]) -> list[dict[str, object]]:
    features: list[dict[str, object]] = []
    current: dict[str, object] | None = None
    in_features = False
    current_qualifier: str | None = None
    for line in lines:
        if line.startswith("FEATURES"):
            in_features = True
            continue
        if in_features and line.startswith("ORIGIN"):
            break
        if not in_features:
            continue
        key = line[5:21].strip() if len(line) >= 21 else ""
        text = line[21:].rstrip() if len(line) >= 21 else line.rstrip()
        if key:
            if current is not None:
                features.append(current)
            current = {"key": key, "location": text.strip(), "qualifiers": {}}
            current_qualifier = None
            continue
        if current is None:
            continue
        stripped = text.strip()
        if not stripped:
            continue
        if stripped.startswith("/"):
            current_qualifier = None
            body = stripped[1:]
            qualifiers = current["qualifiers"]
            assert isinstance(qualifiers, dict)
            if "=" in body:
                name, value = body.split("=", 1)
                value = value.strip().strip('"')
                qualifiers.setdefault(name, []).append(value)
                if stripped.count('"') == 1:
                    current_qualifier = name
            else:
                qualifiers.setdefault(body, []).append(True)
        elif current_qualifier:
            qualifiers = current["qualifiers"]
            assert isinstance(qualifiers, dict)
            values = qualifiers[current_qualifier]
            assert isinstance(values, list)
            values[-1] = str(values[-1]) + stripped.strip('"')
            if stripped.endswith('"'):
                current_qualifier = None
        elif current.get("location"):
            current["location"] = str(current["location"]) + stripped
    if current is not None:
        features.append(current)
    return features


def parse_location(location: str) -> tuple[str, list[tuple[int, int]]] | None:
    location = location.replace(" ", "")
    strand = "+"
    if location.startswith("complement(") and location.endswith(")"):
        strand = "-"
        location = location[len("complement(") : -1]
    if location.startswith("join(") and location.endswith(")"):
        location = location[len("join(") : -1]
    parts: list[tuple[int, int]] = []
    for item in location.split(","):
        item = item.replace("<", "").replace(">", "")
        match = re.match(r"^(\d+)\.\.(\d+)$", item)
        if match:
            start = int(match.group(1)) - 1
            end = int(match.group(2))
            if 0 <= start < end:
                parts.append((start, end))
            continue
        match = re.match(r"^(\d+)$", item)
        if match:
            start = int(match.group(1)) - 1
            parts.append((start, start + 1))
            continue
        return None
    return (strand, parts) if parts else None


def sequence_from_segments(genome: str, strand: str, segments: list[tuple[int, int]]) -> str:
    seq = "".join(genome[start:end] for start, end in segments)
    return seq.upper() if strand == "+" else reverse_complement_dna(seq)


def product_text(qualifiers: dict[str, list[Any]]) -> str:
    values = []
    for key in ("product", "gene", "note", "locus_tag"):
        for value in qualifiers.get(key, []):
            values.append(str(value))
    return " ".join(values)


def is_excluded_product(product: str) -> bool:
    lower = product.lower()
    return any(token in lower for token in ("putative", "fragment", "pseudogene", "pseudo", "associated", "methyltransferase"))


def is_heg_product(product: str, length_nt: int) -> bool:
    lower = product.lower()
    return 150 <= length_nt <= 1500 and "ribosomal protein" in lower and not is_excluded_product(lower)


def intact_cds_sequence(seq: str) -> tuple[str | None, str | None]:
    seq = re.sub(r"[^A-Za-z]", "", seq).upper()
    if len(seq) < 90 or len(seq) % 3 != 0:
        return None, "bad_length"
    if any(base not in BASES_DNA for base in seq):
        return None, "ambiguous"
    codons = [seq[i : i + 3] for i in range(0, len(seq), 3)]
    stop_codons = {codon.replace("U", "T") for codon, aa in CODON_TO_AA.items() if aa == "*"}
    if codons and codons[-1] in stop_codons:
        codons = codons[:-1]
    if not codons or any(codon in stop_codons for codon in codons):
        return None, "internal_stop"
    trimmed = "".join(codons)
    return trimmed, None


def sequence_metrics(seq_rna: str) -> dict[str, float]:
    if not seq_rna:
        return {"gc": 0.0, "gc3": 0.0}
    gc = sum(1 for base in seq_rna if base in "GC") / len(seq_rna)
    codons = [seq_rna[i : i + 3] for i in range(0, len(seq_rna) - 2, 3)]
    gc3 = sum(1 for codon in codons if codon[2] in "GC") / len(codons) if codons else 0.0
    return {"gc": gc, "gc3": gc3}


def parse_genbank_payload(text: str) -> tuple[list[dict[str, object]], list[dict[str, object]], dict[str, object]]:
    lines = text.splitlines()
    genome = parse_origin(lines)
    features = parse_features(lines)
    cds_records: list[dict[str, object]] = []
    rrna_records: list[dict[str, object]] = []
    skipped: Counter[str] = Counter()
    transl_tables: Counter[int] = Counter()
    for feature in features:
        key = str(feature.get("key") or "")
        qualifiers = feature.get("qualifiers")
        if not isinstance(qualifiers, dict):
            continue
        loc = parse_location(str(feature.get("location") or ""))
        if loc is None:
            if key in {"CDS", "rRNA"}:
                skipped["bad_location"] += 1
            continue
        strand, segments = loc
        seq_dna = sequence_from_segments(genome, strand, segments)
        prod = product_text(qualifiers)
        if key == "rRNA":
            if "16S" not in prod and "small subunit" not in prod.lower():
                continue
            clean = re.sub(r"[^ACGT]", "N", seq_dna.upper())
            if 1200 <= len(clean) <= 1700 and "N" not in clean:
                rrna_records.append(
                    {
                        "sequence_rna": dna_to_rna(clean),
                        "product": prod,
                        "strand": strand,
                        "length_nt": len(clean),
                    }
                )
            else:
                skipped["rrna_length_or_ambiguous"] += 1
        elif key == "CDS":
            if "pseudo" in qualifiers or "pseudogene" in qualifiers:
                skipped["pseudo"] += 1
                continue
            table_values = qualifiers.get("transl_table", [])
            try:
                table = int(table_values[0]) if table_values else 11
            except (TypeError, ValueError):
                table = 11
            transl_tables[table] += 1
            intact, reason = intact_cds_sequence(seq_dna)
            if intact is None:
                skipped[str(reason)] += 1
                continue
            seq_rna = dna_to_rna(intact)
            metrics = sequence_metrics(seq_rna)
            cds_records.append(
                {
                    "sequence_rna": seq_rna,
                    "product": prod,
                    "strand": strand,
                    "length_nt": len(seq_rna),
                    "gc": metrics["gc"],
                    "gc3": metrics["gc3"],
                    "transl_table": table,
                    "is_heg": is_heg_product(prod, len(seq_rna)),
                }
            )
    meta = {
        "genome_length": len(genome),
        "n_features": len(features),
        "n_features_cds": sum(1 for f in features if f.get("key") == "CDS"),
        "n_complete_cds": len(cds_records),
        "n_16s_rrna": len(rrna_records),
        "transl_table_counts": dict(sorted(transl_tables.items())),
        "skipped": dict(sorted(skipped.items())),
        "source_parser": "genomic.gbff",
    }
    return cds_records, rrna_records, meta


def parse_gff_payload(gff_text: str, fna_text: str) -> tuple[list[dict[str, object]], list[dict[str, object]], dict[str, object]]:
    contigs = parse_fasta_records(fna_text)
    cds_records: list[dict[str, object]] = []
    rrna_records: list[dict[str, object]] = []
    skipped: Counter[str] = Counter()
    transl_tables: Counter[int] = Counter()
    for line in gff_text.splitlines():
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) < 9:
            continue
        seqid, _, feature, start_s, end_s, _, strand, _, attr_raw = fields[:9]
        if feature not in {"CDS", "rRNA", "region"}:
            continue
        seq = contigs.get(seqid)
        if not seq:
            skipped["missing_contig"] += 1
            continue
        try:
            start = int(start_s) - 1
            end = int(end_s)
        except ValueError:
            skipped["bad_coordinate"] += 1
            continue
        attrs = parse_gff_attributes(attr_raw)
        prod = " ".join(str(attrs.get(key, "")) for key in ("product", "Name", "gene", "Note"))
        if feature == "rRNA":
            if "16S" not in prod and "small subunit" not in prod.lower():
                continue
            piece = seq[start:end].upper()
            if strand == "-":
                piece = reverse_complement_dna(piece)
            if 1200 <= len(piece) <= 1700 and set(piece) <= BASES_DNA:
                rrna_records.append({"sequence_rna": dna_to_rna(piece), "product": prod, "strand": strand, "length_nt": len(piece)})
        elif feature == "CDS":
            if "pseudo" in attrs or "pseudogene" in prod.lower():
                skipped["pseudo"] += 1
                continue
            try:
                table = int(attrs.get("transl_table", "11"))
            except ValueError:
                table = 11
            transl_tables[table] += 1
            piece = seq[start:end].upper()
            if strand == "-":
                piece = reverse_complement_dna(piece)
            intact, reason = intact_cds_sequence(piece)
            if intact is None:
                skipped[str(reason)] += 1
                continue
            seq_rna = dna_to_rna(intact)
            metrics = sequence_metrics(seq_rna)
            cds_records.append(
                {
                    "sequence_rna": seq_rna,
                    "product": prod,
                    "strand": strand if strand in {"+", "-"} else "+",
                    "length_nt": len(seq_rna),
                    "gc": metrics["gc"],
                    "gc3": metrics["gc3"],
                    "transl_table": table,
                    "is_heg": is_heg_product(prod, len(seq_rna)),
                }
            )
    meta = {
        "n_contigs": len(contigs),
        "n_complete_cds": len(cds_records),
        "n_16s_rrna": len(rrna_records),
        "transl_table_counts": dict(sorted(transl_tables.items())),
        "skipped": dict(sorted(skipped.items())),
        "source_parser": "genomic.gff+genomic.fna",
    }
    return cds_records, rrna_records, meta


def parsed_cache_path(accession: str) -> Path:
    return ASD_CACHE_DIR / f"{safe_name(accession)}_parsed_asd.json"


def load_parsed_cache(accession: str) -> dict[str, object] | None:
    path = parsed_cache_path(accession)
    if not path.exists():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    if isinstance(payload, dict) and payload.get("cds_records") and payload.get("rrna_records"):
        payload["parsed_cache_hit"] = True
        return payload
    return None


def save_parsed_cache(accession: str, payload: dict[str, object]) -> None:
    path = parsed_cache_path(accession)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")), encoding="utf-8")


def classify_drop(cds_records: list[dict[str, object]], rrna_records: list[dict[str, object]], meta: dict[str, object]) -> str | None:
    if len(rrna_records) < 1:
        return "no_complete_16s_rrna"
    if len(cds_records) < 800:
        return "fewer_than_800_intact_cds"
    if sum(int(row.get("length_nt", 0)) for row in cds_records) < 500_000:
        return "cds_total_length_below_0_5mb"
    table_counts = Counter(int(row.get("transl_table", 11)) for row in cds_records)
    if not table_counts or table_counts.most_common(1)[0][0] != 11:
        return "dominant_translation_table_not_11"
    if len([row for row in cds_records if row.get("is_heg")]) < 10:
        return "too_few_ribosomal_protein_cds"
    return None


def fetch_one(row: dict[str, object], deadline: float | None = None) -> tuple[dict[str, object] | None, dict[str, object]]:
    accession = str(row.get("assembly_accession") or "")
    cached = load_parsed_cache(accession)
    if cached is not None:
        merged = {**cached, **{k: v for k, v in row.items() if k not in cached}}
        return merged, {"assembly_accession": accession, "ok": True, "parsed_cache_hit": True}
    summary, summary_contact = assembly_summary_for_accession(accession, deadline=deadline)
    if summary is None:
        return None, {"assembly_accession": accession, "ok": False, "error": "assembly_summary_unavailable", "contact": summary_contact}
    ftp_path = str(summary.get("ftp_path") or "")
    cache_key = str(summary.get("assembly_accession") or accession)
    gff_text, gff_contact = cached_assembly_file(ftp_path, "genomic.gff.gz", cache_key, deadline=deadline)
    fna_text, fna_contact = cached_assembly_file(ftp_path, "genomic.fna.gz", cache_key, deadline=deadline)
    gbff_text, gbff_contact = cached_assembly_file(ftp_path, "genomic.gbff.gz", cache_key, deadline=deadline)

    cds_records: list[dict[str, object]] = []
    rrna_records: list[dict[str, object]] = []
    parse_meta: dict[str, object] = {}
    if gff_text and fna_text:
        cds_records, rrna_records, parse_meta = parse_gff_payload(gff_text, fna_text)
    if (len(rrna_records) < 1 or len(cds_records) < 800) and gbff_text:
        cds_records, rrna_records, parse_meta = parse_genbank_payload(gbff_text)

    drop_reason = classify_drop(cds_records, rrna_records, parse_meta)
    payload: dict[str, object] = {
        "assembly_accession": cache_key,
        "organism": summary.get("organism") or row.get("organism") or "",
        "domain": row.get("domain") or "",
        "genus": str(row.get("genus") or "").lower(),
        "family": row.get("family") or "",
        "order": row.get("order") or "",
        "source": row.get("source") or "",
        "taxid": summary.get("taxid") or "",
        "ftp_path": ftp_path,
        "cds_records": cds_records,
        "rrna_records": rrna_records,
        "parse_meta": parse_meta,
        "drop_reason": drop_reason,
        "contacts": {
            "summary": summary_contact,
            "genomic_gff": gff_contact,
            "genomic_fna": fna_contact,
            "genomic_gbff": gbff_contact,
        },
    }
    if drop_reason is None:
        save_parsed_cache(cache_key, payload)
    return (payload if drop_reason is None else None), {
        "assembly_accession": cache_key,
        "organism": payload["organism"],
        "domain": payload["domain"],
        "genus": payload["genus"],
        "source": payload["source"],
        "ok": drop_reason is None,
        "drop_reason": drop_reason,
        "n_complete_cds": len(cds_records),
        "n_16s_rrna": len(rrna_records),
        "n_heg": len([record for record in cds_records if record.get("is_heg")]),
        "contacts": {
            "summary": {k: summary_contact.get(k) for k in ("on_disk_cache_hit", "error")},
            "gff": {k: gff_contact.get(k) for k in ("on_disk_cache_hit", "borrowed_cache_hit", "reachable", "error")},
            "fna": {k: fna_contact.get(k) for k in ("on_disk_cache_hit", "borrowed_cache_hit", "reachable", "error")},
            "gbff": {k: gbff_contact.get(k) for k in ("on_disk_cache_hit", "borrowed_cache_hit", "reachable", "error")},
        },
    }


def fetch_organism_by_accession(accession: str, organism_name: str, deadline: float | None = None) -> tuple[dict[str, object] | None, dict[str, object]]:
    """Fetch a fixed accession through the same assembly and parser path as panel rows."""
    row = {
        "assembly_accession": accession,
        "organism": organism_name,
        "domain": "Bacteria",
        "genus": organism_name.split()[0].lower() if organism_name.split() else "",
        "source": "fixed_positive_control",
    }
    organism, contact = fetch_one(row, deadline=deadline)
    if organism is not None:
        organism = dict(organism)
        if organism_name and not organism.get("organism"):
            organism["organism"] = organism_name
        organism["source"] = "fixed_positive_control"
    return organism, {**contact, "forced_accession_fetch": True}


def candidate_rows(target_bacteria: int, target_archaea: int, deadline: float | None = None) -> tuple[list[dict[str, object]], dict[str, object]]:
    contacts: dict[str, object] = {}
    bac, bac_contact = load_gtdb_taxonomy("Bacteria", target_bacteria * 3, deadline=deadline)
    arc, arc_contact = load_gtdb_taxonomy("Archaea", target_archaea * 3, deadline=deadline)
    contacts["gtdb_bacteria"] = bac_contact
    contacts["gtdb_archaea"] = arc_contact
    rows = bac[: target_bacteria * 2] + arc[: target_archaea * 2]
    if target_bacteria > 0 and len(bac) < target_bacteria:
        rows.extend(roster_rows("Bacteria", target_bacteria * 2))
    if target_archaea > 0 and len(arc) < target_archaea:
        rows.extend(roster_rows("Archaea", target_archaea * 2))

    seen: set[str] = set()
    unique = []
    for row in rows:
        accession = str(row.get("assembly_accession") or "")
        if not accession or accession in seen:
            continue
        seen.add(accession)
        unique.append(row)
    return unique, contacts


def fetch_panel(
    target_bacteria: int = 50,
    target_archaea: int = 10,
    max_attempts: int | None = None,
    seed: str = "asd_shadow_exclusion.fetch_panel",
    deadline_seconds: float | None = DEFAULT_FETCH_DEADLINE_SECONDS,
) -> tuple[list[dict[str, object]], dict[str, object]]:
    start = time.monotonic()
    deadline = start + deadline_seconds if deadline_seconds is not None and deadline_seconds > 0 else None
    ASD_CACHE_DIR.mkdir(parents=True, exist_ok=True)
    rows, source_contacts = candidate_rows(target_bacteria, target_archaea, deadline=deadline)
    rng = random.Random(int.from_bytes(hashlib.sha256(seed.encode("utf-8")).digest()[:16], "big"))
    gtdb_rows = [row for row in rows if row.get("source") == "gtdb_taxonomy"]
    roster = [row for row in rows if row.get("source") != "gtdb_taxonomy"]
    rng.shuffle(gtdb_rows)
    rows = gtdb_rows + roster
    if max_attempts is None:
        max_attempts = max(target_bacteria + target_archaea, min(len(rows), (target_bacteria + target_archaea) * 3))
    organisms: list[dict[str, object]] = []
    attempts: list[dict[str, object]] = []
    accepted_by_domain = Counter()
    attempted = 0
    for row in rows:
        if attempted >= max_attempts:
            break
        if deadline_expired(deadline):
            attempts.append({"ok": False, "error": "fetch_deadline_exceeded"})
            break
        domain = str(row.get("domain") or "")
        if domain == "Bacteria" and accepted_by_domain["Bacteria"] >= target_bacteria:
            continue
        if domain == "Archaea" and accepted_by_domain["Archaea"] >= target_archaea:
            continue
        attempted += 1
        organism, contact = fetch_one(row, deadline=deadline)
        attempts.append(contact)
        if organism is not None:
            organisms.append(organism)
            accepted_by_domain[str(organism.get("domain") or domain)] += 1
        if accepted_by_domain["Bacteria"] >= target_bacteria and accepted_by_domain["Archaea"] >= target_archaea:
            break
    elapsed = time.monotonic() - start
    ok_attempts = sum(1 for item in attempts if item.get("ok"))
    meta = {
        "experiment_id": EXPERIMENT_ID,
        "created_at": now_iso(),
        "target_bacteria": target_bacteria,
        "target_archaea": target_archaea,
        "max_attempts": max_attempts,
        "n_attempts": len(attempts),
        "n_organisms": len(organisms),
        "accepted_by_domain": dict(accepted_by_domain),
        "fetch_success_rate": ok_attempts / len(attempts) if attempts else 0.0,
        "elapsed_seconds": elapsed,
        "cache_dir": str(ASD_CACHE_DIR),
        "source_contacts": source_contacts,
        "attempts": attempts,
    }
    return organisms, meta


if __name__ == "__main__":
    target_b = int(os.environ.get("ASD_TARGET_BACTERIA", "50"))
    target_a = int(os.environ.get("ASD_TARGET_ARCHAEA", "10"))
    max_attempts = int(os.environ.get("ASD_MAX_FETCH_ATTEMPTS", str(max(12, target_b + target_a))))
    organisms, meta = fetch_panel(target_bacteria=target_b, target_archaea=target_a, max_attempts=max_attempts)
    print(json.dumps({"organisms": len(organisms), "meta": meta}, ensure_ascii=True, sort_keys=False, separators=(",", ":")))

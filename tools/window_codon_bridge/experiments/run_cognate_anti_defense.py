#!/usr/bin/env python3
"""Cognate anti-defense payload enrichment experiment."""
from __future__ import annotations

import csv
import gzip
import json
import math
import os
import random
import re
import statistics
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request


SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.abspath(os.path.join(SCRIPT_DIR, "..", "..", ".."))
SYNCED_DIR = os.path.join(REPO_ROOT, "tools", "window_codon_bridge", "synced")
CACHE_DIR = os.path.join(SYNCED_DIR, "cognate_anti_defense")
REF_DIR = os.path.join(REPO_ROOT, "_q2ref")
FLINDERS_PATH = os.path.join(SYNCED_DIR, "rm_genomes", "flinders_prophage", "host_prophages.tsv")
SEED_MAPPING_PATH = os.path.join(REF_DIR, "seed_family_mapping.tsv")
DBAPIS_URL = "https://pro.unl.edu/dbAPIS/download_file.php?file=dbAPIS.hmm"
PADS_URL_TEMPLATE = (
    "https://ngdc.cncb.ac.cn/padsarsenal/download/information/"
    "PADS_Arsenal_Bacteria_{class_name}_v1_2019.09.09.csv"
)
GTDB_URLS = (
    ("Bacteria", "https://data.gtdb.ecogenomic.org/releases/latest/bac120_taxonomy.tsv.gz"),
    ("Archaea", "https://data.gtdb.ecogenomic.org/releases/latest/ar53_taxonomy.tsv.gz"),
)
DEFAULT_CLASSES = ("RM", "BREX", "GABIJA", "THOERIS", "TA")
USER_AGENT = "cognate-anti-defense-payload"
FETCH_TIMEOUT = 60
NCBI_DELAY_SECONDS = 0.34
MIN_MATCHED_PAIRS = 3
SUPPORT_MEDIAN_MARGIN = 0.0
ANTI_MEDIAN_MARGIN = -0.05
COMPOSITION_TOLERANCE = 0.0


def now_seconds() -> float:
    return time.time()


def deadline_from_env() -> float | None:
    raw = os.environ.get("CAD_FETCH_DEADLINE_SECONDS", "3000").strip()
    try:
        seconds = float(raw)
    except ValueError:
        seconds = 3000.0
    return time.monotonic() + seconds if seconds > 0 else None


def deadline_expired(deadline: float | None) -> bool:
    return deadline is not None and time.monotonic() >= deadline


def safe_name(value: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9_.-]+", "_", value.strip())
    return cleaned[:180] or "item"


def ensure_dir(path: str) -> None:
    os.makedirs(path, exist_ok=True)


def fetch_bytes(url: str, deadline: float | None = None, attempts: int = 4, timeout: int = FETCH_TIMEOUT) -> tuple[bytes, dict[str, object]]:
    last_error = "fetch_failed"
    for attempt in range(1, attempts + 1):
        if deadline_expired(deadline):
            return b"", {"url": url, "ok": False, "error": "fetch_deadline_exceeded", "attempts": attempt - 1}
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                payload = response.read()
                return payload, {
                    "url": url,
                    "ok": True,
                    "http_status": int(getattr(response, "status", 200)),
                    "byte_size": len(payload),
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
        except Exception as exc:
            last_error = f"{type(exc).__name__}:{exc}"
            delay = min(30.0, NCBI_DELAY_SECONDS * (2 ** attempt))
        time.sleep(delay)
    return b"", {"url": url, "ok": False, "error": last_error, "attempts": attempts}


def cached_bytes(url: str, cache_path: str, deadline: float | None = None, attempts: int = 4) -> tuple[bytes, dict[str, object]]:
    ensure_dir(os.path.dirname(cache_path))
    if os.path.exists(cache_path) and os.path.getsize(cache_path) > 0:
        payload = open(cache_path, "rb").read()
        return payload, {
            "url": url,
            "ok": True,
            "on_disk_cache_hit": True,
            "cache_path": cache_path,
            "byte_size": len(payload),
        }
    payload, contact = fetch_bytes(url, deadline=deadline, attempts=attempts)
    if payload:
        with open(cache_path, "wb") as handle:
            handle.write(payload)
        contact = dict(contact)
        contact.update({"on_disk_cache_hit": False, "cache_path": cache_path})
    return payload, contact


def decode_payload(payload: bytes, source_name: str) -> str:
    if source_name.endswith(".gz"):
        return gzip.decompress(payload).decode("utf-8", "replace")
    return payload.decode("utf-8", "replace")


def accession_core(accession: str) -> str:
    match = re.search(r"\b(?:GC[AF])_(\d{9})(?:\.\d+)?\b", accession)
    return match.group(1) if match else ""


def accession_version(accession: str) -> str:
    match = re.search(r"\b((?:GC[AF])_\d{9}\.\d+)\b", accession)
    return match.group(1) if match else accession.strip()


def accession_keys(value: str) -> set[str]:
    keys: set[str] = set()
    for match in re.finditer(r"\b((?:GC[AF])_\d{9}(?:\.\d+)?)\b", value):
        accession = match.group(1)
        keys.add(accession)
        core = accession_core(accession)
        if core:
            keys.add("core:" + core)
    return keys


def normalize_organism(value: str) -> str:
    value = value.lower()
    value = re.sub(r"\[[^\]]*\]", " ", value)
    value = re.sub(r"\b(strain|str\.|substr\.|subsp\.|isolate|complete genome|chromosome)\b", " ", value)
    value = re.sub(r"[^a-z0-9]+", " ", value)
    return " ".join(value.split())


def normalize_class(raw: str) -> str | None:
    text = raw.strip().lower()
    if not text:
        return None
    compact = re.sub(r"[^a-z0-9]+", " ", text)
    if "gabija" in compact:
        return "GABIJA"
    if "thoeris" in compact:
        return "THOERIS"
    if re.search(r"\bbrex\b", compact):
        return "BREX"
    if re.search(r"\bta\b", compact) or "toxin antitoxin" in compact or "toxin antitoxin" in compact.replace("-", " "):
        return "TA"
    if "restriction modification" in compact or "restriction-modification" in text:
        return "RM"
    if re.search(r"\brestriction\b", compact) and "modification" in compact:
        return "RM"
    if re.search(r"\br m\b", compact):
        return "RM"
    return None


def parse_class_list() -> list[str]:
    raw = os.environ.get("CAD_CLASSES", ",".join(DEFAULT_CLASSES))
    classes = []
    for item in raw.split(","):
        label = normalize_class(item) or item.strip().upper()
        if label and label not in classes:
            classes.append(label)
    return classes or list(DEFAULT_CLASSES)


def parse_host_limit() -> int | None:
    raw = os.environ.get("CAD_HOST_LIMIT", "").strip()
    if not raw:
        return None
    try:
        value = int(raw)
    except ValueError:
        return None
    return value if value > 0 else None


def load_flinders_rows(host_limit: int | None = None) -> tuple[list[dict[str, object]], dict[str, object]]:
    if not os.path.exists(FLINDERS_PATH):
        raise RuntimeError(f"missing Flinders host prophage table: {FLINDERS_PATH}")
    rows: list[dict[str, object]] = []
    with open(FLINDERS_PATH, "r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        for row in reader:
            host = accession_version(str(row.get("host_assembly") or ""))
            if not host:
                continue
            try:
                start = int(str(row.get("start") or "0"))
                stop = int(str(row.get("stop") or "0"))
            except ValueError:
                continue
            rows.append(
                {
                    "host_assembly": host,
                    "flinders_genomeid": str(row.get("flinders_genomeid") or ""),
                    "contig": str(row.get("contig") or ""),
                    "start": min(start, stop),
                    "stop": max(start, stop),
                    "length": abs(stop - start) + 1,
                    "match_mode": str(row.get("match_mode") or ""),
                }
            )
    hosts = sorted({str(row["host_assembly"]) for row in rows})
    if host_limit is not None:
        keep = set(hosts[:host_limit])
        rows = [row for row in rows if row["host_assembly"] in keep]
        hosts = hosts[:host_limit]
    return rows, {
        "path": FLINDERS_PATH,
        "n_hosts": len(hosts),
        "n_regions": len(rows),
        "host_limit": host_limit,
    }


def ncbi_base_for_accession(accession: str) -> str:
    core = accession_core(accession)
    if len(core) != 9:
        raise RuntimeError(f"bad GCF accession for NCBI path: {accession}")
    return f"https://ftp.ncbi.nlm.nih.gov/genomes/all/GCF/{core[0:3]}/{core[3:6]}/{core[6:9]}/"


def find_ncbi_assembly_url(accession: str, deadline: float | None = None) -> tuple[str, dict[str, object]]:
    base = ncbi_base_for_accession(accession)
    cache_path = os.path.join(CACHE_DIR, "ncbi_index", safe_name(accession) + ".html")
    payload, contact = cached_bytes(base, cache_path, deadline=deadline, attempts=3)
    if not payload:
        return "", contact
    text = payload.decode("utf-8", "replace")
    prefix = re.escape(accession) + r"_"
    names = []
    for match in re.finditer(r'href="([^"]+/)"', text):
        name = urllib.parse.unquote(match.group(1)).strip("/")
        if re.match(prefix, name):
            names.append(name)
    if not names:
        return "", {**contact, "error": "assembly_directory_not_found", "base_url": base}
    names.sort()
    return base + names[-1] + "/", {**contact, "base_url": base, "assembly_dir": names[-1]}


def cached_ncbi_file(assembly_url: str, accession: str, suffix: str, deadline: float | None = None) -> tuple[str, dict[str, object]]:
    stem = assembly_url.rstrip("/").rsplit("/", 1)[-1]
    url = assembly_url.rstrip("/") + "/" + stem + "_" + suffix
    cache_path = os.path.join(CACHE_DIR, "ncbi_assemblies", safe_name(accession) + "_" + suffix)
    payload, contact = cached_bytes(url, cache_path, deadline=deadline, attempts=3)
    if not payload:
        return "", contact
    try:
        return decode_payload(payload, suffix), {**contact, "decompressed_chars": len(decode_payload(payload, suffix))}
    except Exception as exc:
        return "", {**contact, "error": f"decompress_failed:{type(exc).__name__}:{exc}"}


def parse_gff_attributes(raw: str) -> dict[str, str]:
    attrs: dict[str, str] = {}
    for part in raw.split(";"):
        if "=" not in part:
            continue
        key, value = part.split("=", 1)
        attrs[urllib.parse.unquote(key)] = urllib.parse.unquote(value)
    return attrs


def parse_gff_cds(gff_text: str) -> tuple[list[dict[str, object]], dict[str, object]]:
    records: list[dict[str, object]] = []
    skipped: dict[str, int] = {}
    for line in gff_text.splitlines():
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 9 or parts[2] != "CDS":
            continue
        try:
            start = int(parts[3])
            end = int(parts[4])
        except ValueError:
            skipped["bad_coordinate"] = skipped.get("bad_coordinate", 0) + 1
            continue
        attrs = parse_gff_attributes(parts[8])
        protein_id = attrs.get("protein_id") or attrs.get("Name") or attrs.get("ID") or ""
        if not protein_id:
            skipped["missing_protein_id"] = skipped.get("missing_protein_id", 0) + 1
            continue
        records.append(
            {
                "protein_id": protein_id,
                "contig": parts[0],
                "start": min(start, end),
                "end": max(start, end),
                "strand": parts[6],
            }
        )
    return records, {"n_cds": len(records), "skipped": skipped}


def parse_fasta_records(text: str) -> dict[str, tuple[str, str]]:
    records: dict[str, tuple[str, str]] = {}
    header = ""
    chunks: list[str] = []
    for line in text.splitlines():
        if line.startswith(">"):
            if header:
                key = header.split()[0]
                records[key] = (header, "".join(chunks).upper())
            header = line[1:].strip()
            chunks = []
        else:
            chunks.append(re.sub(r"[^A-Za-z*]", "", line))
    if header:
        key = header.split()[0]
        records[key] = (header, "".join(chunks).upper())
    return records


def overlap_bp(a_start: int, a_end: int, b_start: int, b_end: int) -> int:
    return max(0, min(a_end, b_end) - max(a_start, b_start) + 1)


def is_prophage_cds(cds: dict[str, object], regions: list[dict[str, object]], min_fraction: float) -> bool:
    contig = str(cds.get("contig") or "")
    start = int(cds.get("start") or 0)
    end = int(cds.get("end") or 0)
    length = max(1, end - start + 1)
    for region in regions:
        if str(region.get("contig") or "") != contig:
            continue
        region_start = int(region.get("start") or 0)
        region_stop = int(region.get("stop") or 0)
        if overlap_bp(start, end, region_start, region_stop) / length >= min_fraction:
            return True
    return False


def partition_cds_by_prophage(
    cds_records: list[dict[str, object]],
    regions: list[dict[str, object]],
    min_fraction: float,
) -> tuple[set[str], set[str], dict[str, object]]:
    prophage: set[str] = set()
    chromosome: set[str] = set()
    for cds in cds_records:
        protein_id = str(cds.get("protein_id") or "")
        if not protein_id:
            continue
        if is_prophage_cds(cds, regions, min_fraction):
            prophage.add(protein_id)
        else:
            chromosome.add(protein_id)
    return prophage, chromosome, {"n_prophage_cds": len(prophage), "n_chromosome_cds": len(chromosome)}


def write_subset_fasta(records: dict[str, tuple[str, str]], protein_ids: set[str], path: str) -> int:
    ensure_dir(os.path.dirname(path))
    written = 0
    with open(path, "w", encoding="utf-8") as handle:
        for protein_id in sorted(protein_ids):
            item = records.get(protein_id)
            if item is None:
                continue
            header, seq = item
            handle.write(">" + header + "\n")
            for index in range(0, len(seq), 60):
                handle.write(seq[index : index + 60] + "\n")
            written += 1
    return written


def load_seed_family_map(classes: list[str]) -> tuple[dict[str, str], dict[str, object]]:
    if not os.path.exists(SEED_MAPPING_PATH):
        raise RuntimeError(f"missing seed family mapping: {SEED_MAPPING_PATH}")
    family_to_class: dict[str, str] = {}
    raw_systems: dict[str, str] = {}
    counts: dict[str, int] = {}
    with open(SEED_MAPPING_PATH, "r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        fields = reader.fieldnames or []
        family_col = "family_ID" if "family_ID" in fields else fields[0]
        system_col = ""
        for field in fields:
            if "inhibited_defense_system" in field and "clan_" not in field:
                system_col = field
                break
        if not system_col and len(fields) >= 3:
            system_col = fields[2]
        for row in reader:
            family = str(row.get(family_col) or "").strip()
            system = str(row.get(system_col) or "").strip()
            label = normalize_class(system)
            if family:
                raw_systems.setdefault(family, system)
            if family and label in classes:
                family_to_class[family] = label
                counts[label] = counts.get(label, 0) + 1
    return family_to_class, {
        "path": SEED_MAPPING_PATH,
        "n_mapped_families": len(family_to_class),
        "n_raw_families": len(raw_systems),
        "mapped_counts_by_class": counts,
    }


def parse_hmm_tblout(path: str) -> dict[str, dict[str, object]]:
    hits: dict[str, dict[str, object]] = {}
    if not os.path.exists(path):
        return hits
    with open(path, "r", encoding="utf-8", errors="replace") as handle:
        for line in handle:
            if not line.strip() or line.startswith("#"):
                continue
            parts = line.split()
            if len(parts) < 6:
                continue
            target = parts[0]
            query = parts[2]
            try:
                evalue = float(parts[4])
                score = float(parts[5])
            except ValueError:
                continue
            previous = hits.get(target)
            if previous is None or score > float(previous.get("score") or -1e300):
                hits[target] = {"family": query, "evalue": evalue, "score": score}
    return hits


def run_hmmsearch(fasta_path: str, tblout_path: str, hmm_path: str, hmmsearch_bin: str, evalue: str) -> dict[str, object]:
    if not os.path.exists(fasta_path) or os.path.getsize(fasta_path) == 0:
        open(tblout_path, "w", encoding="utf-8").close()
        return {"skipped": True, "reason": "empty_fasta", "tblout": tblout_path}
    base_cmd = [hmmsearch_bin, "--tblout", tblout_path, "--noali", "--cut_ga", hmm_path, fasta_path]
    first = subprocess.run(base_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if first.returncode == 0:
        return {"ok": True, "mode": "cut_ga", "tblout": tblout_path, "stderr_tail": first.stderr[-800:]}
    fallback_cmd = [hmmsearch_bin, "--tblout", tblout_path, "--noali", "-E", evalue, hmm_path, fasta_path]
    second = subprocess.run(fallback_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if second.returncode != 0:
        raise RuntimeError(
            "hmmsearch failed: "
            + (second.stderr[-1000:] or first.stderr[-1000:] or f"returncode={second.returncode}")
        )
    return {
        "ok": True,
        "mode": "evalue",
        "evalue": evalue,
        "tblout": tblout_path,
        "cut_ga_error_tail": first.stderr[-800:],
        "stderr_tail": second.stderr[-800:],
    }


def load_or_fetch_hmm(deadline: float | None) -> tuple[str, dict[str, object]]:
    cache_path = os.path.join(CACHE_DIR, "dbapis", "dbAPIS.hmm")
    payload, contact = cached_bytes(DBAPIS_URL, cache_path, deadline=deadline, attempts=3)
    if not payload:
        raise RuntimeError("dbAPIS HMM fetch failed")
    return cache_path, contact


def count_hits_by_class(hits: dict[str, dict[str, object]], family_to_class: dict[str, str]) -> tuple[dict[str, int], int]:
    counts: dict[str, int] = {}
    non_mappable = 0
    for hit in hits.values():
        family = str(hit.get("family") or "")
        label = family_to_class.get(family)
        if label:
            counts[label] = counts.get(label, 0) + 1
        else:
            non_mappable += 1
    return counts, non_mappable


def y_score(anti_count: int, load: int) -> float:
    return math.log2((anti_count + 0.5) / (load + 1.0))


def median(values: list[float]) -> float:
    return float(statistics.median(values)) if values else 0.0


def family_weighted_median(items: list[tuple[float, str]]) -> float:
    if not items:
        return 0.0
    family_values: dict[str, list[float]] = {}
    for value, family in items:
        family_values.setdefault(family or "unmapped", []).append(value)
    weighted: list[tuple[float, float]] = []
    for family, values in family_values.items():
        weight = 1.0 / max(1, len(values))
        for value in values:
            weighted.append((value, weight))
    weighted.sort(key=lambda item: item[0])
    total = sum(weight for _value, weight in weighted)
    cursor = 0.0
    for value, weight in weighted:
        cursor += weight
        if cursor >= total / 2.0:
            return float(value)
    return float(weighted[-1][0])


def bootstrap_family_weighted_median(
    rows: list[dict[str, object]],
    key: str,
    family_key: str,
    n: int,
    seed: int = 104729,
) -> dict[str, object]:
    values = [(float(row.get(key) or 0.0), str(row.get(family_key) or "unmapped")) for row in rows]
    observed = family_weighted_median(values)
    families = sorted({family for _value, family in values})
    if not values or not families or n <= 0:
        return {"observed": observed, "n": 0, "p_positive": None, "ci": [observed, observed]}
    by_family: dict[str, list[float]] = {}
    for value, family in values:
        by_family.setdefault(family, []).append(value)
    rng = random.Random(seed)
    boot = []
    for _ in range(n):
        sampled: list[tuple[float, str]] = []
        for _slot in families:
            family = rng.choice(families)
            for value in by_family[family]:
                sampled.append((value, family))
        boot.append(family_weighted_median(sampled))
    boot.sort()
    low = boot[int(0.025 * (len(boot) - 1))]
    high = boot[int(0.975 * (len(boot) - 1))]
    p_positive = sum(1 for value in boot if value > 0.0) / len(boot)
    return {"observed": observed, "n": n, "p_positive": p_positive, "ci": [low, high]}


def gtdb_strip_accession(accession: str) -> str:
    value = accession.strip()
    if value.startswith(("RS_", "GB_")):
        value = value[3:]
    return value


def parse_taxonomy_line(raw: str) -> dict[str, str]:
    ranks: dict[str, str] = {}
    for item in raw.split(";"):
        if "__" not in item:
            continue
        prefix, name = item.split("__", 1)
        key = {"d": "domain", "p": "phylum", "c": "class", "o": "order", "f": "family", "g": "genus", "s": "species"}.get(prefix)
        if key:
            ranks[key] = name
    return ranks


def load_gtdb_lookup(hosts: set[str], deadline: float | None) -> tuple[dict[str, dict[str, str]], dict[str, object]]:
    lookup: dict[str, dict[str, str]] = {}
    contacts: dict[str, object] = {}
    host_keys = set(hosts)
    host_keys.update("core:" + accession_core(host) for host in hosts if accession_core(host))
    for domain, url in GTDB_URLS:
        cache_path = os.path.join(CACHE_DIR, "gtdb", domain.lower() + "_taxonomy.tsv.gz")
        payload, contact = cached_bytes(url, cache_path, deadline=deadline, attempts=2)
        contacts[domain] = contact
        if not payload:
            continue
        try:
            text = gzip.decompress(payload).decode("utf-8", "replace")
        except Exception as exc:
            contacts[domain] = {**contact, "error": f"decompress_failed:{type(exc).__name__}:{exc}"}
            continue
        scanned = 0
        matched = 0
        for line in text.splitlines():
            if not line.strip():
                continue
            scanned += 1
            parts = line.split("\t")
            if len(parts) < 2:
                continue
            accession = gtdb_strip_accession(parts[0])
            core = accession_core(accession)
            keys = {accession}
            if core:
                keys.add("core:" + core)
            if not keys.intersection(host_keys):
                continue
            ranks = parse_taxonomy_line(parts[1])
            tax = {
                "domain": domain,
                "gtdb_family": ranks.get("family") or "",
                "gtdb_genus": ranks.get("genus") or "",
                "gtdb_order": ranks.get("order") or "",
            }
            for key in keys:
                lookup[key] = tax
            matched += 1
        contacts[domain] = {**contacts[domain], "n_lines": scanned, "n_matched_hosts": matched}
    return lookup, {"contacts": contacts, "n_lookup_keys": len(lookup)}


def infer_taxonomy(host: str, gtdb_lookup: dict[str, dict[str, str]]) -> dict[str, str]:
    core = accession_core(host)
    return gtdb_lookup.get(host) or gtdb_lookup.get("core:" + core) or {
        "domain": "",
        "gtdb_family": "unmapped_family",
        "gtdb_genus": "",
        "gtdb_order": "",
    }


def load_pads_carriers(
    classes: list[str],
    hosts: set[str],
    host_organisms: dict[str, str],
    deadline: float | None,
) -> tuple[dict[str, set[str]], dict[str, object]]:
    carrier: dict[str, set[str]] = {host: set() for host in hosts}
    host_key_to_host: dict[str, str] = {}
    for host in hosts:
        for key in accession_keys(host):
            host_key_to_host[key] = host
    organism_to_hosts: dict[str, set[str]] = {}
    for host, organism in host_organisms.items():
        norm = normalize_organism(organism)
        if norm:
            organism_to_hosts.setdefault(norm, set()).add(host)
    contacts: dict[str, object] = {}
    matches_by_class: dict[str, int] = {}
    for class_name in classes:
        url = PADS_URL_TEMPLATE.format(class_name=class_name)
        cache_path = os.path.join(CACHE_DIR, "pads", f"PADS_Arsenal_Bacteria_{class_name}.csv")
        payload, contact = cached_bytes(url, cache_path, deadline=deadline, attempts=3)
        contacts[class_name] = contact
        if not payload:
            continue
        text = payload.decode("utf-8", "replace")
        reader = csv.DictReader(text.splitlines())
        fields = reader.fieldnames or []
        matched_rows = 0
        for row in reader:
            cells = [str(row.get(field) or "") for field in fields]
            row_text = " ".join(cells)
            matched_hosts: set[str] = set()
            for key in accession_keys(row_text):
                if key in host_key_to_host:
                    matched_hosts.add(host_key_to_host[key])
            if not matched_hosts:
                for cell in cells:
                    norm = normalize_organism(cell)
                    if norm in organism_to_hosts:
                        matched_hosts.update(organism_to_hosts[norm])
            for host in matched_hosts:
                carrier.setdefault(host, set()).add(class_name)
                matched_rows += 1
        matches_by_class[class_name] = matched_rows
        contacts[class_name] = {**contacts[class_name], "header": fields[:30], "matched_rows": matched_rows}
    return carrier, {"contacts": contacts, "matches_by_class": matches_by_class}


def parse_organism_from_gff(gff_text: str) -> str:
    for line in gff_text.splitlines():
        if line.startswith("#!organism "):
            return line[len("#!organism ") :].strip()
        if line.startswith("##species "):
            return line[len("##species ") :].strip()
    return ""


def prepare_host_payloads(
    flinders_rows: list[dict[str, object]],
    classes: list[str],
    family_to_class: dict[str, str],
    deadline: float | None,
) -> tuple[list[dict[str, object]], dict[str, object]]:
    overlap_min = float(os.environ.get("CAD_OVERLAP_MIN", "0.8"))
    hmmsearch_bin = os.environ.get("CAD_HMMSEARCH", "hmmsearch")
    evalue = os.environ.get("CAD_EVALUE", "1e-5")
    hmm_path, hmm_contact = load_or_fetch_hmm(deadline)
    regions_by_host: dict[str, list[dict[str, object]]] = {}
    for row in flinders_rows:
        regions_by_host.setdefault(str(row["host_assembly"]), []).append(row)
    rows: list[dict[str, object]] = []
    contacts: dict[str, object] = {"dbapis_hmm": hmm_contact}
    for host, regions in sorted(regions_by_host.items()):
        if deadline_expired(deadline):
            contacts["deadline_skipped_after_host"] = host
            break
        assembly_url, index_contact = find_ncbi_assembly_url(host, deadline=deadline)
        contacts.setdefault("ncbi_index", {})[host] = index_contact
        if not assembly_url:
            rows.append({"host": host, "ok": False, "error": "assembly_directory_not_found"})
            continue
        gff_text, gff_contact = cached_ncbi_file(assembly_url, host, "genomic.gff.gz", deadline=deadline)
        faa_text, faa_contact = cached_ncbi_file(assembly_url, host, "protein.faa.gz", deadline=deadline)
        contacts.setdefault("ncbi_files", {})[host] = {"gff": gff_contact, "faa": faa_contact}
        if not gff_text or not faa_text:
            rows.append({"host": host, "ok": False, "error": "assembly_file_fetch_failed"})
            continue
        cds, gff_meta = parse_gff_cds(gff_text)
        proteins = parse_fasta_records(faa_text)
        prophage_ids, chromosome_ids, partition_meta = partition_cds_by_prophage(cds, regions, overlap_min)
        subset_dir = os.path.join(CACHE_DIR, "fasta_subsets")
        tblout_dir = os.path.join(CACHE_DIR, "hmm_tblout")
        os.makedirs(subset_dir, exist_ok=True)
        os.makedirs(tblout_dir, exist_ok=True)
        prophage_fasta = os.path.join(subset_dir, safe_name(host) + "_prophage.faa")
        chromosome_fasta = os.path.join(subset_dir, safe_name(host) + "_chromosome.faa")
        prophage_written = write_subset_fasta(proteins, prophage_ids, prophage_fasta)
        chromosome_written = write_subset_fasta(proteins, chromosome_ids, chromosome_fasta)
        prophage_tblout = os.path.join(tblout_dir, safe_name(host) + "_prophage.tblout")
        chromosome_tblout = os.path.join(tblout_dir, safe_name(host) + "_chromosome.tblout")
        prophage_hmm = run_hmmsearch(prophage_fasta, prophage_tblout, hmm_path, hmmsearch_bin, evalue)
        chromosome_hmm = run_hmmsearch(chromosome_fasta, chromosome_tblout, hmm_path, hmmsearch_bin, evalue)
        prophage_hits = parse_hmm_tblout(prophage_tblout)
        chromosome_hits = parse_hmm_tblout(chromosome_tblout)
        prophage_counts, prophage_non_mappable = count_hits_by_class(prophage_hits, family_to_class)
        chromosome_counts, chromosome_non_mappable = count_hits_by_class(chromosome_hits, family_to_class)
        row: dict[str, object] = {
            "host": host,
            "ok": True,
            "organism": parse_organism_from_gff(gff_text),
            "prophage_protein_count": prophage_written,
            "chromosome_protein_count": chromosome_written,
            "prophage_counts": {class_name: prophage_counts.get(class_name, 0) for class_name in classes},
            "chromosome_counts": {class_name: chromosome_counts.get(class_name, 0) for class_name in classes},
            "non_mappable_prophage_hits": prophage_non_mappable,
            "non_mappable_chromosome_hits": chromosome_non_mappable,
            "n_prophage_hits": len(prophage_hits),
            "n_chromosome_hits": len(chromosome_hits),
            "n_regions": len(regions),
            "gff_meta": gff_meta,
            "partition_meta": partition_meta,
            "hmmsearch": {"prophage": prophage_hmm, "chromosome": chromosome_hmm},
        }
        rows.append(row)
    return rows, contacts


def matched_controls(
    rows: list[dict[str, object]],
    host: str,
    class_name: str,
    carrier: dict[str, set[str]],
    family: str,
    load: int,
) -> list[dict[str, object]]:
    target_burden = len(carrier.get(host, set()))
    candidates = [
        row
        for row in rows
        if row.get("ok")
        and str(row.get("host")) != host
        and class_name not in carrier.get(str(row.get("host")), set())
        and int(row.get("prophage_protein_count") or 0) > 0
    ]
    same_family = [row for row in candidates if str(row.get("gtdb_family") or "") == family]
    burden_matched = [row for row in same_family if abs(len(carrier.get(str(row.get("host")), set())) - target_burden) <= 1]
    pool = burden_matched or same_family or candidates
    pool.sort(
        key=lambda row: (
            abs(len(carrier.get(str(row.get("host")), set())) - target_burden),
            abs(math.log2((int(row.get("prophage_protein_count") or 0) + 1.0) / (load + 1.0))),
        )
    )
    return pool[: max(3, min(8, len(pool)))]


def compute_nulls(rows: list[dict[str, object]], classes: list[str], carrier: dict[str, set[str]]) -> tuple[list[dict[str, object]], dict[str, object]]:
    class_rows: list[dict[str, object]] = []
    own_beats_swap = 0
    swap_total = 0
    chrom_beats = 0
    chrom_total = 0
    necessity_by_class: dict[str, list[float]] = {class_name: [] for class_name in classes}
    host_lookup = {str(row.get("host")): row for row in rows if row.get("ok")}
    for row in rows:
        if not row.get("ok"):
            continue
        host = str(row.get("host"))
        family = str(row.get("gtdb_family") or "unmapped_family")
        load = int(row.get("prophage_protein_count") or 0)
        chrom_load = int(row.get("chromosome_protein_count") or 0)
        prophage_counts = row.get("prophage_counts") if isinstance(row.get("prophage_counts"), dict) else {}
        chromosome_counts = row.get("chromosome_counts") if isinstance(row.get("chromosome_counts"), dict) else {}
        carried = carrier.get(host, set())
        class_n: dict[str, float] = {}
        for class_name in classes:
            count = int(prophage_counts.get(class_name, 0)) if isinstance(prophage_counts, dict) else 0
            y = y_score(count, load)
            controls = matched_controls(rows, host, class_name, carrier, family, load)
            control_y = []
            for control in controls:
                control_counts = control.get("prophage_counts") if isinstance(control.get("prophage_counts"), dict) else {}
                control_y.append(y_score(int(control_counts.get(class_name, 0)), int(control.get("prophage_protein_count") or 0)))
            n_value = y - median(control_y) if control_y else 0.0
            class_n[class_name] = n_value
            if class_name in carried and controls:
                necessity_by_class[class_name].append(n_value)
        other_controls = matched_controls(rows, host, "NON_COGNATE_OTHER", carrier, family, load)
        other_y = []
        for control in other_controls:
            other_y.append(
                y_score(
                    int(control.get("non_mappable_prophage_hits") or 0),
                    int(control.get("prophage_protein_count") or 0),
                )
            )
        class_n["NON_COGNATE_OTHER"] = (
            y_score(int(row.get("non_mappable_prophage_hits") or 0), load) - median(other_y) if other_y else 0.0
        )
        for class_name in classes:
            if class_name not in carried:
                continue
            decoys = [class_n[other] for other in classes if other not in carried and other in class_n]
            decoys.append(class_n["NON_COGNATE_OTHER"])
            n_value = class_n[class_name]
            d_value = n_value - median(decoys) if decoys else n_value
            count = int(prophage_counts.get(class_name, 0)) if isinstance(prophage_counts, dict) else 0
            chrom_count = int(chromosome_counts.get(class_name, 0)) if isinstance(chromosome_counts, dict) else 0
            chrom_delta = y_score(count, load) - y_score(chrom_count, chrom_load)
            if chrom_delta > 0:
                chrom_beats += 1
            chrom_total += 1
            swap_values = []
            for other in rows:
                if not other.get("ok") or str(other.get("host")) == host:
                    continue
                if str(other.get("gtdb_family") or "unmapped_family") != family:
                    continue
                other_host = str(other.get("host"))
                for swapped_class in carrier.get(other_host, set()):
                    if swapped_class == class_name:
                        continue
                    swap_values.append(class_n.get(swapped_class, 0.0))
            swapped = median(swap_values)
            own_minus_swapped = n_value - swapped
            if own_minus_swapped > COMPOSITION_TOLERANCE:
                own_beats_swap += 1
            swap_total += 1
            class_rows.append(
                {
                    "host": host,
                    "class": class_name,
                    "gtdb_family": family,
                    "carrier": True,
                    "A": count,
                    "L": load,
                    "Y": y_score(count, load),
                    "N": n_value,
                    "D": d_value,
                    "decoy_median": median(decoys) if decoys else 0.0,
                    "chromosome_delta": chrom_delta,
                    "own_minus_swapped": own_minus_swapped,
                    "defense_burden": len(carried),
                    "n_controls": len(matched_controls(rows, host, class_name, carrier, family, load)),
                }
            )
    per_class = {}
    for class_name, values in necessity_by_class.items():
        per_class[class_name] = {
            "n_pairs": len(values),
            "median_N": median(values),
            "positive_fraction": sum(1 for value in values if value > 0) / len(values) if values else 0.0,
        }
    return class_rows, {
        "necessity_by_class": per_class,
        "own_beats_swap_fraction": own_beats_swap / swap_total if swap_total else 0.0,
        "own_beats_swap_n": swap_total,
        "prophage_beats_chromosome_fraction": chrom_beats / chrom_total if chrom_total else 0.0,
        "prophage_beats_chromosome_n": chrom_total,
        "host_lookup_size": len(host_lookup),
    }


def verdict_from_metrics(metrics: dict[str, object]) -> str:
    total_pairs = int(metrics.get("n_carrier_pairs") or 0)
    mapped_families = int(metrics.get("n_mapped_families") or 0)
    matched_pairs = int(metrics.get("n_matched_pairs") or 0)
    median_d = float(metrics.get("median_D") or 0.0)
    median_n = float(metrics.get("median_N") or 0.0)
    own_swap = float(metrics.get("own_beats_swap_fraction") or 0.0)
    chrom = float(metrics.get("prophage_beats_chromosome_fraction") or 0.0)
    decoy = float(metrics.get("median_decoy_gap") or 0.0)
    if total_pairs < MIN_MATCHED_PAIRS or matched_pairs < MIN_MATCHED_PAIRS or mapped_families == 0:
        return "data_gate_failed"
    if median_n < ANTI_MEDIAN_MARGIN and median_d < ANTI_MEDIAN_MARGIN:
        return "anti"
    if own_swap <= 0.5 and median_d > SUPPORT_MEDIAN_MARGIN:
        return "composition_ecology_dominated"
    if median_d > SUPPORT_MEDIAN_MARGIN and median_n > SUPPORT_MEDIAN_MARGIN and decoy > SUPPORT_MEDIAN_MARGIN and own_swap > 0.5 and chrom > 0.5:
        return "supportive"
    if median_d <= SUPPORT_MEDIAN_MARGIN and median_n <= SUPPORT_MEDIAN_MARGIN:
        return "refuted"
    return "composition_ecology_dominated"


def summarize_results(
    host_rows: list[dict[str, object]],
    class_rows: list[dict[str, object]],
    nulls: dict[str, object],
    classes: list[str],
    family_to_class: dict[str, str],
    bootstrap_n: int,
) -> dict[str, object]:
    ok_hosts = [row for row in host_rows if row.get("ok")]
    matched_rows = [row for row in class_rows if int(row.get("n_controls") or 0) > 0]
    median_d = family_weighted_median([(float(row.get("D") or 0.0), str(row.get("gtdb_family") or "unmapped")) for row in matched_rows])
    median_n = family_weighted_median([(float(row.get("N") or 0.0), str(row.get("gtdb_family") or "unmapped")) for row in matched_rows])
    median_decoy_gap = family_weighted_median(
        [(float(row.get("N") or 0.0) - float(row.get("decoy_median") or 0.0), str(row.get("gtdb_family") or "unmapped")) for row in matched_rows]
    )
    metrics = {
        "n_hosts": len(host_rows),
        "n_ok_hosts": len(ok_hosts),
        "n_carrier_pairs": len(class_rows),
        "n_matched_pairs": len(matched_rows),
        "n_mapped_families": len(family_to_class),
        "median_D": median_d,
        "median_N": median_n,
        "median_decoy_gap": median_decoy_gap,
        "own_beats_swap_fraction": nulls.get("own_beats_swap_fraction", 0.0),
        "prophage_beats_chromosome_fraction": nulls.get("prophage_beats_chromosome_fraction", 0.0),
    }
    return {
        "summary": metrics,
        "per_class_necessity": nulls.get("necessity_by_class", {}),
        "nulls": {
            "non_cognate_decoy_median_gap": median_decoy_gap,
            "cross_host_same_family_swap": {
                "own_beats_swap_fraction": nulls.get("own_beats_swap_fraction", 0.0),
                "n": nulls.get("own_beats_swap_n", 0),
            },
            "chromosome_control": {
                "prophage_beats_chromosome_fraction": nulls.get("prophage_beats_chromosome_fraction", 0.0),
                "n": nulls.get("prophage_beats_chromosome_n", 0),
            },
            "bootstrap": {
                "D": bootstrap_family_weighted_median(matched_rows, "D", "gtdb_family", bootstrap_n),
                "N": bootstrap_family_weighted_median(matched_rows, "N", "gtdb_family", bootstrap_n),
            },
        },
        "classes": classes,
        "verdict": verdict_from_metrics(metrics),
    }


def run_experiment() -> dict[str, object]:
    ensure_dir(CACHE_DIR)
    deadline = deadline_from_env()
    classes = parse_class_list()
    host_limit = parse_host_limit()
    try:
        bootstrap_n = int(os.environ.get("CAD_BOOTSTRAP_N", "2000"))
    except ValueError:
        bootstrap_n = 2000
    flinders_rows, flinders_meta = load_flinders_rows(host_limit)
    family_to_class, mapping_meta = load_seed_family_map(classes)
    host_rows, contacts = prepare_host_payloads(flinders_rows, classes, family_to_class, deadline)
    hosts = {str(row.get("host")) for row in host_rows if row.get("host")}
    host_organisms = {str(row.get("host")): str(row.get("organism") or "") for row in host_rows if row.get("host")}
    gtdb_lookup, gtdb_meta = load_gtdb_lookup(hosts, deadline)
    for row in host_rows:
        host = str(row.get("host") or "")
        tax = infer_taxonomy(host, gtdb_lookup)
        row.update(tax)
    carrier, carrier_meta = load_pads_carriers(classes, hosts, host_organisms, deadline)
    for row in host_rows:
        host = str(row.get("host") or "")
        row["carrier_classes"] = sorted(carrier.get(host, set()))
        row["defense_burden"] = len(carrier.get(host, set()))
    class_rows, nulls = compute_nulls(host_rows, classes, carrier)
    summary = summarize_results(host_rows, class_rows, nulls, classes, family_to_class, bootstrap_n)
    return {
        "experiment": "cognate_anti_defense_payload_enrichment",
        "inputs": {
            "flinders": flinders_meta,
            "seed_family_mapping": mapping_meta,
            "gtdb": gtdb_meta,
            "pads": carrier_meta,
            "cache_dir": CACHE_DIR,
        },
        "contacts": contacts,
        "summary": summary["summary"],
        "per_host_rows": host_rows,
        "per_host_class_rows": class_rows,
        "per_class_necessity": summary["per_class_necessity"],
        "nulls": summary["nulls"],
        "verdict": summary["verdict"],
    }


def assert_close(actual: float, expected: float, tol: float = 1e-9) -> None:
    if abs(actual - expected) > tol:
        raise AssertionError(f"{actual} != {expected}")


def selftest() -> dict[str, object]:
    gff = "\n".join(
        [
            "ctg\tRefSeq\tCDS\t10\t109\t.\t+\t0\tID=cds-a;protein_id=protA",
            "ctg\tRefSeq\tCDS\t180\t279\t.\t+\t0\tID=cds-b;protein_id=protB",
            "other\tRefSeq\tCDS\t10\t90\t.\t+\t0\tID=cds-c;protein_id=protC",
        ]
    )
    cds, _meta = parse_gff_cds(gff)
    regions = [{"contig": "ctg", "start": 1, "stop": 100}]
    prophage, chromosome, _partition = partition_cds_by_prophage(cds, regions, 0.8)
    if prophage != {"protA"} or chromosome != {"protB", "protC"}:
        raise AssertionError("GFF overlap assignment failed")
    assert_close(y_score(1, 9), math.log2(1.5 / 10.0))
    weighted = family_weighted_median([(10.0, "A"), (20.0, "A"), (1.0, "B")])
    assert_close(weighted, 1.0)
    if normalize_class("Restriction-Modification") != "RM":
        raise AssertionError("RM normalization failed")
    if normalize_class("Gabija defense") != "GABIJA":
        raise AssertionError("Gabija normalization failed")
    if normalize_class("toxin-antitoxin module") != "TA":
        raise AssertionError("TA normalization failed")
    supportive = verdict_from_metrics(
        {
            "n_carrier_pairs": 5,
            "n_matched_pairs": 5,
            "n_mapped_families": 2,
            "median_D": 0.2,
            "median_N": 0.1,
            "median_decoy_gap": 0.2,
            "own_beats_swap_fraction": 0.8,
            "prophage_beats_chromosome_fraction": 0.8,
        }
    )
    if supportive != "supportive":
        raise AssertionError("supportive verdict failed")
    if verdict_from_metrics({"n_carrier_pairs": 1, "n_matched_pairs": 1, "n_mapped_families": 2}) != "data_gate_failed":
        raise AssertionError("data gate verdict failed")
    anti = verdict_from_metrics(
        {
            "n_carrier_pairs": 5,
            "n_matched_pairs": 5,
            "n_mapped_families": 2,
            "median_D": -0.2,
            "median_N": -0.2,
        }
    )
    if anti != "anti":
        raise AssertionError("anti verdict failed")
    return {"ok": True, "tested": ["gff_overlap", "log2_score", "family_weighted_median", "class_normalization", "verdict"]}


def main(argv: list[str]) -> int:
    try:
        if "--selftest" in argv:
            print(json.dumps(selftest(), sort_keys=True))
            return 0
        result = run_experiment()
        print(json.dumps(result, sort_keys=True))
        return 0
    except Exception as exc:
        print(json.dumps({"error": f"{type(exc).__name__}: {exc}"}, sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

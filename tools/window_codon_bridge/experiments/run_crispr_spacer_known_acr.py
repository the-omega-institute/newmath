#!/usr/bin/env python3
"""CRISPR spacer exposure versus known anti-CRISPR payload."""
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
CACHE_DIR = os.path.join(SYNCED_DIR, "crispr_spacer_known_acr")
REF_DIR = os.path.join(REPO_ROOT, "_q2ref")

DEFAULT_MANIFEST = os.path.join(REF_DIR, "host_universe_contigs.txt")
DEFAULT_SPACER_FSA = os.path.join(REF_DIR, "spacer_seqName.fsa")
DEFAULT_FLINDERS_BULK = os.path.join(
    SYNCED_DIR,
    "rm_genomes",
    "flinders_prophage",
    "phispy_all_predictions.tsv.gz",
)
DEFAULT_GCA_SUBTYPES = os.path.join(REF_DIR, "gca_to_subtypes.json")
DEFAULT_ACR_FAA = os.path.join(REF_DIR, "Known_Acr.faa")
DEFAULT_DIAMOND = "/opt/homebrew/bin/diamond"

NCBI_EFETCH_URL = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi"
USER_AGENT = "crispr-spacer-known-acr"
FETCH_TIMEOUT = 120
NCBI_DELAY_SECONDS = 0.34
DNA_ALPHABET = set("ACGTN")
AA_ALPHABET = set("ABCDEFGHIKLMNPQRSTVWXYZUO*")
REVCOMP_TABLE = str.maketrans("ACGTNacgtn", "TGCANtgcan")
GENUS_CAP = 0.10
MIN_ACR_REF_LENGTH = 40
MAX_ACR_REF_LENGTH = 250


def ensure_dir(path: str) -> None:
    os.makedirs(path, exist_ok=True)


def safe_name(value: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9_.-]+", "_", value.strip())
    return cleaned[:180] or "item"


def env_int(name: str, default: int) -> int:
    raw = os.environ.get(name, "").strip()
    if not raw:
        return default
    try:
        return int(raw)
    except ValueError:
        return default


def env_float(name: str, default: float) -> float:
    raw = os.environ.get(name, "").strip()
    if not raw:
        return default
    try:
        return float(raw)
    except ValueError:
        return default


def env_path(name: str, default: str) -> str:
    return os.environ.get(name, "").strip() or default


def parse_host_limit() -> int | None:
    value = env_int("CA_HOST_LIMIT", 0)
    return value if value > 0 else None


def deadline_from_env() -> float | None:
    seconds = env_int("CA_FETCH_DEADLINE_SECONDS", 14400)
    return time.monotonic() + seconds if seconds > 0 else None


def deadline_expired(deadline: float | None) -> bool:
    return deadline is not None and time.monotonic() >= deadline


def fetch_bytes(
    url: str,
    deadline: float | None = None,
    attempts: int = 4,
    timeout: int = FETCH_TIMEOUT,
) -> tuple[bytes, dict[str, object]]:
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


def cached_bytes(
    url: str,
    cache_path: str,
    deadline: float | None = None,
    attempts: int = 4,
) -> tuple[bytes, dict[str, object]]:
    ensure_dir(os.path.dirname(cache_path))
    if os.path.exists(cache_path) and os.path.getsize(cache_path) > 0:
        with open(cache_path, "rb") as handle:
            payload = handle.read()
        return payload, {"url": url, "ok": True, "on_disk_cache_hit": True, "cache_path": cache_path, "byte_size": len(payload)}
    payload, contact = fetch_bytes(url, deadline=deadline, attempts=attempts)
    if payload:
        with open(cache_path, "wb") as handle:
            handle.write(payload)
        contact = dict(contact)
        contact.update({"on_disk_cache_hit": False, "cache_path": cache_path})
    return payload, contact


def ncbi_efetch_url(accession: str, rettype: str) -> str:
    query = urllib.parse.urlencode({"db": "nuccore", "id": accession, "rettype": rettype, "retmode": "text"})
    return NCBI_EFETCH_URL + "?" + query


def sanitize_nt(seq: str) -> str:
    return "".join(char for char in seq.upper() if char in DNA_ALPHABET)


def sanitize_aa(seq: str) -> str:
    return "".join(char for char in seq.upper() if char in AA_ALPHABET)


def reverse_complement(seq: str) -> str:
    return seq.translate(REVCOMP_TABLE)[::-1].upper()


def parse_fasta_records(text: str) -> list[tuple[str, str]]:
    records: list[tuple[str, str]] = []
    header = ""
    chunks: list[str] = []
    for line in text.splitlines():
        if line.startswith(">"):
            if header:
                records.append((header, "".join(chunks)))
            header = line[1:].strip()
            chunks = []
        else:
            chunks.append(line.strip())
    if header:
        records.append((header, "".join(chunks)))
    return records


def parse_contig_fasta(text: str) -> tuple[str, str]:
    records = parse_fasta_records(text)
    if not records:
        return "", ""
    header, seq = records[0]
    return header, sanitize_nt(seq)


def parse_int(value: object, default: int = 0) -> int:
    text = str(value).strip()
    if not text:
        return default
    try:
        return int(float(text))
    except ValueError:
        return default


def parse_float(value: object, default: float = 0.0) -> float:
    text = str(value).strip()
    if not text:
        return default
    try:
        return float(text)
    except ValueError:
        return default


def load_manifest(path: str, host_limit: int | None) -> tuple[list[str], dict[str, object]]:
    if not os.path.exists(path):
        raise RuntimeError(f"missing manifest: {path}")
    contigs: list[str] = []
    seen: set[str] = set()
    with open(path, "r", encoding="utf-8", errors="replace") as handle:
        for line in handle:
            value = line.strip()
            if not value or value.startswith("#"):
                continue
            token = value.split()[0]
            if token in seen:
                continue
            seen.add(token)
            contigs.append(token)
            if host_limit is not None and len(contigs) >= host_limit:
                break
    return contigs, {"path": path, "n_manifest_contigs": len(contigs), "host_limit": host_limit}


def build_spacer_index_from_fasta_text(text: str, keep_contigs: set[str] | None = None) -> dict[str, set[str]]:
    index: dict[str, set[str]] = {}
    for header, seq in parse_fasta_records(text):
        spacer = sanitize_nt(seq)
        if not spacer:
            continue
        for accession in header.split()[0].split("+"):
            accession = accession.strip()
            if not accession:
                continue
            if keep_contigs is not None and accession not in keep_contigs:
                continue
            index.setdefault(accession, set()).add(spacer)
    return index


def load_spacer_index(path: str, keep_contigs: set[str]) -> tuple[dict[str, set[str]], dict[str, object]]:
    if not os.path.exists(path):
        raise RuntimeError(f"missing spacer FASTA: {path}")
    with open(path, "r", encoding="utf-8", errors="replace") as handle:
        index = build_spacer_index_from_fasta_text(handle.read(), keep_contigs)
    return index, {
        "path": path,
        "n_contigs_with_spacers": len(index),
        "n_spacer_assignments": sum(len(values) for values in index.values()),
    }


def flinders_row_from_fields(fields: list[str], header: list[str] | None) -> dict[str, object] | None:
    if header is None:
        if len(fields) < 7:
            return None
        raw = {
            "genomeid": fields[0],
            "contig": fields[1],
            "start": fields[2],
            "stop": fields[3],
            "length": fields[4],
            "cds": fields[5],
            "decision": fields[6],
        }
    else:
        keyed = {header[index].strip().lower(): fields[index] if index < len(fields) else "" for index in range(len(header))}
        raw = {
            "genomeid": keyed.get("genomeid") or keyed.get("genome_id") or keyed.get("genome") or keyed.get("assembly") or "",
            "contig": keyed.get("contig") or keyed.get("seqid") or keyed.get("sequence") or "",
            "start": keyed.get("start") or keyed.get("begin") or "",
            "stop": keyed.get("stop") or keyed.get("end") or "",
            "length": keyed.get("length") or keyed.get("len") or "",
            "cds": keyed.get("#cds") or keyed.get("cds") or keyed.get("n_cds") or "",
            "decision": keyed.get("decision") or keyed.get("status") or "",
        }
    decision = str(raw["decision"])
    if "kept" not in decision.lower():
        return None
    contig = str(raw["contig"]).strip()
    if not contig:
        return None
    start = parse_int(raw["start"])
    stop = parse_int(raw["stop"])
    if start <= 0 or stop <= 0:
        return None
    lo, hi = min(start, stop), max(start, stop)
    length = parse_int(raw["length"], hi - lo + 1) or (hi - lo + 1)
    genomeid = str(raw["genomeid"]).strip()
    if not genomeid:
        return None
    return {
        "host": genomeid,
        "contig": contig,
        "start": lo,
        "stop": hi,
        "length": length,
        "flinders_cds": parse_int(raw["cds"]),
        "decision": decision,
    }


def load_flinders_regions(path: str, manifest_contigs: set[str]) -> tuple[dict[str, dict[str, object]], dict[str, object]]:
    if not os.path.exists(path):
        raise RuntimeError(f"missing Flinders bulk: {path}")
    opener = gzip.open if path.endswith(".gz") else open
    hosts: dict[str, dict[str, object]] = {}
    n_rows = 0
    n_kept_manifest_rows = 0
    contig_to_gca: dict[str, str] = {}
    with opener(path, "rt", encoding="utf-8", errors="replace", newline="") as handle:  # type: ignore[arg-type]
        first = handle.readline()
        if not first:
            return hosts, {"path": path, "n_rows": 0, "n_kept_manifest_rows": 0, "n_hosts": 0}
        first_fields = first.rstrip("\n").split("\t")
        lowered = [field.strip().lower() for field in first_fields]
        header = first_fields if any(name in lowered for name in ("genomeid", "contig", "decision", "start")) else None
        pending = [] if header is not None else [first_fields]
        for fields in pending:
            n_rows += 1
            row = flinders_row_from_fields(fields, header)
            if row is None or str(row["contig"]) not in manifest_contigs:
                continue
            n_kept_manifest_rows += 1
            host = str(row["host"])
            contig_to_gca[str(row["contig"])] = host
            hosts.setdefault(host, {"host": host, "contigs": set(), "regions": []})
            hosts[host]["contigs"].add(str(row["contig"]))  # type: ignore[index,union-attr]
            hosts[host]["regions"].append(row)  # type: ignore[index,union-attr]
        for line in handle:
            fields = line.rstrip("\n").split("\t")
            n_rows += 1
            row = flinders_row_from_fields(fields, header)
            if row is None or str(row["contig"]) not in manifest_contigs:
                continue
            n_kept_manifest_rows += 1
            host = str(row["host"])
            contig_to_gca[str(row["contig"])] = host
            hosts.setdefault(host, {"host": host, "contigs": set(), "regions": []})
            hosts[host]["contigs"].add(str(row["contig"]))  # type: ignore[index,union-attr]
            hosts[host]["regions"].append(row)  # type: ignore[index,union-attr]
    for host_data in hosts.values():
        host_data["contigs"] = sorted(host_data["contigs"])  # type: ignore[index]
        host_data["regions"] = sorted(host_data["regions"], key=lambda row: (str(row["contig"]), int(row["start"]), int(row["stop"])))  # type: ignore[index]
    return hosts, {
        "path": path,
        "n_rows": n_rows,
        "n_kept_manifest_rows": n_kept_manifest_rows,
        "n_hosts": len(hosts),
        "n_contig_to_gca_bridges": len(contig_to_gca),
    }


def load_gca_subtypes(path: str) -> tuple[dict[str, list[str]], dict[str, object]]:
    if not os.path.exists(path):
        raise RuntimeError(f"missing GCA subtype map: {path}")
    with open(path, "r", encoding="utf-8", errors="replace") as handle:
        raw = json.load(handle)
    mapping: dict[str, list[str]] = {}
    for key, values in dict(raw).items():
        if isinstance(values, str):
            subtypes = [values]
        else:
            subtypes = [str(value) for value in values]
        cleaned = sorted({value.strip() for value in subtypes if value and value.strip()})
        if cleaned:
            mapping[str(key)] = cleaned
    return mapping, {
        "path": path,
        "n_gca_with_subtypes": len(mapping),
        "n_single_subtype_gca": sum(1 for values in mapping.values() if len(values) == 1),
        "n_multi_subtype_gca": sum(1 for values in mapping.values() if len(values) > 1),
    }


def derive_genus_from_defline(header: str) -> str:
    text = re.sub(r"^\S+\s*", "", header.strip())
    text = re.sub(r"\[[^\]]*\]", " ", text)
    words = [re.sub(r"[^A-Za-z-]", "", word) for word in text.split()]
    skip = {
        "complete",
        "genome",
        "chromosome",
        "plasmid",
        "contig",
        "scaffold",
        "sequence",
        "dna",
        "strain",
        "isolate",
        "whole",
    }
    for word in words:
        if not word:
            continue
        lower = word.lower()
        if lower in skip or len(word) < 2:
            continue
        return word
    return "unmapped"


def fetch_contig_fasta(contig: str, deadline: float | None) -> tuple[str, str, dict[str, object]]:
    cache_path = os.path.join(CACHE_DIR, "genome_fna", safe_name(contig) + ".fna")
    payload, contact = cached_bytes(ncbi_efetch_url(contig, "fasta"), cache_path, deadline=deadline, attempts=4)
    if not payload:
        raise RuntimeError(f"NCBI efetch fasta failed for {contig}")
    header, seq = parse_contig_fasta(payload.decode("utf-8", "replace"))
    if not seq:
        raise RuntimeError(f"empty contig FASTA for {contig}")
    return header, seq, contact


def parse_location_span(location: str) -> tuple[int, int] | None:
    nums = [int(item) for item in re.findall(r"\d+", location)]
    if not nums:
        return None
    return min(nums), max(nums)


def bracket_value(header: str, key: str) -> str:
    match = re.search(r"\[" + re.escape(key) + r"=([^\]]*)\]", header)
    return match.group(1).strip() if match else ""


def parse_fasta_cds_aa(text: str) -> list[dict[str, object]]:
    cds_rows: list[dict[str, object]] = []
    for ordinal, (header, seq) in enumerate(parse_fasta_records(text), start=1):
        location = bracket_value(header, "location")
        span = parse_location_span(location)
        if span is None:
            continue
        product = bracket_value(header, "protein")
        if not product:
            product = re.sub(r"\[[^\]]*\]", " ", header).strip()
            product = re.sub(r"^\S+\s*", "", product).strip()
        protein_id = bracket_value(header, "protein_id") or bracket_value(header, "locus_tag")
        if not protein_id:
            protein_id = header.split()[0] if header.split() else f"cds_{ordinal}"
        aa = sanitize_aa(seq)
        if not aa:
            continue
        cds_rows.append(
            {
                "id": safe_name(protein_id),
                "start": span[0],
                "stop": span[1],
                "product": product,
                "aa": aa,
                "aa_length": len(aa),
            }
        )
    return cds_rows


def fetch_contig_cds_aa(contig: str, deadline: float | None) -> tuple[list[dict[str, object]], dict[str, object]]:
    aa_path = os.path.join(CACHE_DIR, "prophage_faa", safe_name(contig) + ".faa")
    payload, contact = cached_bytes(ncbi_efetch_url(contig, "fasta_cds_aa"), aa_path, deadline=deadline, attempts=4)
    if not payload:
        return [], {"source": "unavailable", "n_cds": 0, "fasta_cds_aa": contact}
    rows = parse_fasta_cds_aa(payload.decode("utf-8", "replace"))
    return rows, {"source": "ncbi_fasta_cds_aa", "n_cds": len(rows), "fasta_cds_aa": contact}


def cds_in_region(cds_rows: list[dict[str, object]], start: int, stop: int) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for row in cds_rows:
        lo = int(row.get("start") or 0)
        hi = int(row.get("stop") or 0)
        if lo >= start and hi <= stop:
            rows.append(row)
    return rows


def interval_overlaps(a_start: int, a_stop: int, b_start: int, b_stop: int) -> bool:
    return max(a_start, b_start) <= min(a_stop, b_stop)


def cds_outside_regions(cds_rows: list[dict[str, object]], regions: list[dict[str, object]]) -> list[dict[str, object]]:
    outside: list[dict[str, object]] = []
    spans = [(int(row.get("start") or 0), int(row.get("stop") or 0)) for row in regions]
    for row in cds_rows:
        lo = int(row.get("start") or 0)
        hi = int(row.get("stop") or 0)
        if not any(interval_overlaps(lo, hi, start, stop) for start, stop in spans):
            outside.append(row)
    return outside


def product_text(products: list[str]) -> str:
    return " ".join(re.sub(r"[^a-z0-9]+", " ", product.lower()) for product in products)


def module_profile(products: list[str], orf_count: int) -> dict[str, object]:
    text = product_text(products)
    modules = {
        "packaging": bool(re.search(r"\bterminase\b", text)),
        "head": bool(re.search(r"\b(capsid|head|portal)\b", text)),
        "tail": bool(re.search(r"\b(tail|tape measure|baseplate)\b", text)),
        "lysis": bool(re.search(r"\b(holin|endolysin|lysin)\b", text)),
        "lysogeny": bool(re.search(r"\b(integrase|excisionase|recombinase)\b", text)),
    }
    modules_present = sum(1 for value in modules.values() if value)
    intact_like = int(orf_count >= 25 and modules_present >= 4 and (modules["packaging"] or modules["head"] or modules["tail"]))
    return {
        "modules": modules,
        "modules_present": modules_present,
        "cryptic_score": 5 - modules_present,
        "intact_like": intact_like,
        "integrase_present": bool(re.search(r"\bintegrase\b", text)),
    }


def gc_fraction(seq: str) -> float:
    if not seq:
        return 0.0
    return (seq.count("G") + seq.count("C")) / len(seq)


def length_bin(length: int) -> str:
    if length < 15000:
        return "lt15k"
    if length < 30000:
        return "15k_30k"
    if length < 50000:
        return "30k_50k"
    if length < 80000:
        return "50k_80k"
    return "ge80k"


def gc_bin(gc: float) -> str:
    return f"{int(max(0.0, min(0.999, gc)) * 20):02d}"


def orf_bin(count: int) -> str:
    if count < 15:
        return "lt15"
    if count < 25:
        return "15_24"
    if count < 40:
        return "25_39"
    if count < 60:
        return "40_59"
    return "ge60"


def find_all(haystack: str, needle: str) -> list[int]:
    starts: list[int] = []
    cursor = haystack.find(needle)
    while cursor >= 0:
        starts.append(cursor)
        cursor = haystack.find(needle, cursor + 1)
    return starts


def spacer_match_intervals(spacer: str, target: str, min_match: int) -> list[tuple[int, int, str]]:
    spacer = sanitize_nt(spacer)
    target = sanitize_nt(target)
    if len(spacer) < min_match or not target:
        return []
    intervals: set[tuple[int, int, str]] = set()
    orientations = [("+", spacer)]
    rc = reverse_complement(spacer)
    if rc != spacer:
        orientations.append(("-", rc))
    for strand, oriented in orientations:
        for start in find_all(target, oriented):
            intervals.add((start, start + len(oriented) - 1, strand))
        if len(oriented) > min_match:
            seen_kmers: set[str] = set()
            for offset in range(0, len(oriented) - min_match + 1):
                kmer = oriented[offset : offset + min_match]
                if kmer in seen_kmers:
                    continue
                seen_kmers.add(kmer)
                for start in find_all(target, kmer):
                    intervals.add((start, start + min_match - 1, strand))
    return sorted(intervals)


def exposure_events_for_spacers(
    host: str,
    spacers: set[str],
    prophages: list[dict[str, object]],
    min_match: int,
) -> tuple[list[dict[str, object]], set[str]]:
    events: list[dict[str, object]] = []
    seen: set[tuple[str, str, str, int, int]] = set()
    exposed: set[str] = set()
    for prophage in prophages:
        seq = str(prophage.get("sequence") or "")
        if not seq:
            continue
        pid = str(prophage["prophage_id"])
        p_start = int(prophage.get("start") or 1)
        for spacer in sorted(spacers):
            for local_start, local_stop, strand in spacer_match_intervals(spacer, seq, min_match):
                start = p_start + local_start
                stop = p_start + local_stop
                key = (host, pid, spacer, start, stop)
                if key in seen:
                    continue
                seen.add(key)
                exposed.add(pid)
                events.append(
                    {
                        "host": host,
                        "prophage_id": pid,
                        "contig": str(prophage.get("contig") or ""),
                        "spacer": spacer,
                        "protospacer_start": start,
                        "protospacer_stop": stop,
                        "strand": strand,
                    }
                )
    return events, exposed


def dinucleotide_shuffle(seq: str, rng: random.Random) -> str:
    seq = sanitize_nt(seq)
    if len(seq) < 3:
        return seq
    for _attempt in range(20):
        adjacency: dict[str, list[str]] = {}
        for left, right in zip(seq, seq[1:]):
            adjacency.setdefault(left, []).append(right)
        for values in adjacency.values():
            rng.shuffle(values)
        stack = [seq[0]]
        path: list[str] = []
        local = {key: list(values) for key, values in adjacency.items()}
        while stack:
            node = stack[-1]
            if local.get(node):
                stack.append(local[node].pop())
            else:
                path.append(stack.pop())
        shuffled = "".join(reversed(path))
        if len(shuffled) == len(seq) and shuffled != seq:
            return shuffled
    chars = list(seq)
    rng.shuffle(chars)
    return "".join(chars)


def median(values: list[float]) -> float:
    return float(statistics.median(values)) if values else 0.0


def family_weighted_median(items: list[tuple[float, str]]) -> float:
    if not items:
        return 0.0
    by_group: dict[str, list[float]] = {}
    for value, group in items:
        by_group.setdefault(group or "unmapped", []).append(value)
    weighted: list[tuple[float, float]] = []
    for values in by_group.values():
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


def genus_group_weights(items: list[tuple[float, str]], cap: float = GENUS_CAP) -> dict[str, float]:
    by_group: dict[str, list[float]] = {}
    for value, group in items:
        _ = value
        by_group.setdefault(group or "unmapped", []).append(0.0)
    groups = sorted(by_group)
    if not groups:
        return {}
    effective_cap = max(0.0, min(1.0, cap))
    if effective_cap <= 0.0 or len(groups) * effective_cap < 1.0:
        effective_cap = 1.0 / len(groups)
    total_count = sum(len(values) for values in by_group.values())
    base = {group: len(by_group[group]) / total_count for group in groups}
    remaining = set(groups)
    remaining_mass = 1.0
    group_weights: dict[str, float] = {}
    while remaining:
        base_mass = sum(base[group] for group in remaining)
        capped = [
            group
            for group in remaining
            if base_mass > 0.0 and remaining_mass * base[group] / base_mass > effective_cap
        ]
        if not capped:
            for group in remaining:
                group_weights[group] = remaining_mass * base[group] / base_mass if base_mass > 0.0 else remaining_mass / len(remaining)
            break
        for group in capped:
            group_weights[group] = effective_cap
            remaining_mass -= effective_cap
            remaining.remove(group)
    return group_weights


def genus_capped_weighted_median(items: list[tuple[float, str]], cap: float = GENUS_CAP) -> float:
    if not items:
        return 0.0
    by_group: dict[str, list[float]] = {}
    for value, group in items:
        by_group.setdefault(group or "unmapped", []).append(value)
    group_weights = genus_group_weights(items, cap)
    weighted: list[tuple[float, float]] = []
    for group, values in by_group.items():
        weight = group_weights.get(group, 0.0) / max(1, len(values))
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


def sign(value: float) -> int:
    if value > 0.0:
        return 1
    if value < 0.0:
        return -1
    return 0


def signs_not_reversed(reference: float, candidate: float) -> bool:
    ref_sign = sign(reference)
    candidate_sign = sign(candidate)
    return bool(ref_sign == 0 or candidate_sign == 0 or ref_sign == candidate_sign)


def y_value(acr_count: int, protein_count: int) -> float:
    return math.log2((acr_count + 0.5) / (protein_count + 1.0))


def parse_acr_family_subtype(family: str) -> str | None:
    token = family.split()[0].split("|")[0].strip()
    match = re.search(r"Acr([A-Za-z0-9_.-]+)", token)
    if not match:
        return None
    suffix = match.group(1)
    roman_order = ["VIII", "VII", "VI", "IV", "III", "II", "IX", "X", "V", "I"]
    for roman in roman_order:
        if suffix.startswith(roman) and len(suffix) > len(roman):
            letter = suffix[len(roman)]
            if "A" <= letter <= "Z":
                return f"{roman}-{letter}"
    return None


def load_acr_references(path: str) -> tuple[dict[str, dict[str, object]], dict[str, str], dict[str, object]]:
    if not os.path.exists(path):
        raise RuntimeError(f"missing Known Acr FASTA: {path}")
    with open(path, "r", encoding="utf-8", errors="replace") as handle:
        records = parse_fasta_records(handle.read())
    refs: dict[str, dict[str, object]] = {}
    family_to_subtype: dict[str, str] = {}
    excluded = 0
    for header, seq in records:
        family = header.split()[0]
        aa = sanitize_aa(seq)
        subtype = parse_acr_family_subtype(family)
        refs[family] = {"family": family, "header": header, "aa_length": len(aa), "subtype": subtype}
        if subtype is None:
            excluded += 1
        else:
            family_to_subtype[family] = subtype
    return refs, family_to_subtype, {
        "path": path,
        "n_known_acr_records": len(refs),
        "n_parseable_cognate_records": len(family_to_subtype),
        "n_excluded_unparseable_records": excluded,
        "subtypes": sorted(set(family_to_subtype.values())),
    }


def write_faa(path: str, rows: list[dict[str, object]], id_prefix: str = "") -> None:
    ensure_dir(os.path.dirname(path))
    with open(path, "w", encoding="utf-8") as handle:
        for index, row in enumerate(rows, start=1):
            base_id = str(row.get("id") or f"protein_{index}")
            qid = safe_name(f"{id_prefix}{base_id}") if id_prefix else safe_name(base_id)
            aa = sanitize_aa(str(row.get("aa") or ""))
            if not aa:
                continue
            handle.write(f">{qid}\n")
            for offset in range(0, len(aa), 80):
                handle.write(aa[offset : offset + 80] + "\n")


def ensure_acr_diamond_db(acr_faa: str, diamond: str) -> tuple[str, dict[str, object]]:
    if not os.path.exists(diamond):
        raise RuntimeError(f"missing diamond executable: {diamond}")
    if not os.path.exists(acr_faa):
        raise RuntimeError(f"missing Known Acr FASTA: {acr_faa}")
    db_prefix = os.path.join(CACHE_DIR, "diamond_db", safe_name(os.path.basename(acr_faa)))
    dmnd_path = db_prefix + ".dmnd"
    ensure_dir(os.path.dirname(db_prefix))
    if os.path.exists(dmnd_path) and os.path.getsize(dmnd_path) > 0:
        return db_prefix, {"db_prefix": db_prefix, "dmnd_path": dmnd_path, "made": False}
    # diamond makedb hangs on whitespace/invalid chars inside sequences (the AcrDB
    # Known_Acr.faa carries embedded spaces). Build the db from a sanitized copy.
    with open(acr_faa, "r", encoding="utf-8", errors="replace") as handle:
        records = parse_fasta_records(handle.read())
    clean_faa = db_prefix + ".clean.faa"
    n_clean = 0
    with open(clean_faa, "w", encoding="utf-8") as handle:
        for header, seq in records:
            aa = sanitize_aa(seq)
            if not aa:
                continue
            handle.write(">" + header.split()[0] + "\n")
            for offset in range(0, len(aa), 80):
                handle.write(aa[offset : offset + 80] + "\n")
            n_clean += 1
    try:
        result = subprocess.run(
            [diamond, "makedb", "--in", clean_faa, "-d", db_prefix, "--quiet"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=300,
        )
    except subprocess.TimeoutExpired:
        raise RuntimeError("diamond makedb timed out (>300s)")
    if result.returncode != 0:
        raise RuntimeError(f"diamond makedb failed: {result.stderr.strip() or result.stdout.strip()}")
    return db_prefix, {"db_prefix": db_prefix, "dmnd_path": dmnd_path, "made": True, "n_clean_refs": n_clean}


def low_complexity_fraction(seq: str) -> float:
    aa = sanitize_aa(seq).replace("*", "")
    if not aa:
        return 1.0
    counts: dict[str, int] = {}
    for char in aa:
        counts[char] = counts.get(char, 0) + 1
    return max(counts.values()) / len(aa)


def diamond_hit_passes(hit: dict[str, object], query_lengths: dict[str, int], acr_refs: dict[str, dict[str, object]]) -> bool:
    qseqid = str(hit.get("qseqid") or "")
    sseqid = str(hit.get("sseqid") or "")
    pident = parse_float(hit.get("pident"))
    length = parse_int(hit.get("length"))
    qlen = parse_int(hit.get("qlen"), query_lengths.get(qseqid, 0))
    slen = parse_int(hit.get("slen"), int(dict(acr_refs.get(sseqid) or {}).get("aa_length") or 0))
    evalue = parse_float(hit.get("evalue"), 1.0)
    ref_len = int(dict(acr_refs.get(sseqid) or {}).get("aa_length") or slen)
    if evalue > 1e-5:
        return False
    if qlen <= 0 or slen <= 0 or length <= 0:
        return False
    if length / qlen < 0.70:
        return False
    if length / slen < 0.70:
        return False
    if pident < 30.0:
        return False
    if ref_len < MIN_ACR_REF_LENGTH or ref_len > MAX_ACR_REF_LENGTH:
        return False
    return True


def parse_diamond_outfmt6(text: str) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    fields = ["qseqid", "sseqid", "pident", "length", "qlen", "slen", "evalue", "bitscore"]
    for line in text.splitlines():
        if not line.strip():
            continue
        parts = line.rstrip("\n").split("\t")
        if len(parts) < len(fields):
            continue
        rows.append({field: parts[index] for index, field in enumerate(fields)})
    return rows


def run_diamond_blastp(
    query_faa: str,
    db_prefix: str,
    diamond: str,
    out_path: str,
) -> tuple[list[dict[str, object]], dict[str, object]]:
    ensure_dir(os.path.dirname(out_path))
    if not os.path.exists(query_faa) or os.path.getsize(query_faa) <= 0:
        return [], {"query_faa": query_faa, "n_raw_hits": 0, "cache_hit": False, "skipped_empty_query": True}
    if os.path.exists(out_path):
        with open(out_path, "r", encoding="utf-8", errors="replace") as handle:
            text = handle.read()
        return parse_diamond_outfmt6(text), {"query_faa": query_faa, "out_path": out_path, "n_raw_hits": len(parse_diamond_outfmt6(text)), "cache_hit": True}
    command = [
        diamond,
        "blastp",
        "-q",
        query_faa,
        "-d",
        db_prefix,
        "--outfmt",
        "6",
        "qseqid",
        "sseqid",
        "pident",
        "length",
        "qlen",
        "slen",
        "evalue",
        "bitscore",
        "--evalue",
        "1e-5",
        "--max-target-seqs",
        "5",
        "--quiet",
    ]
    try:
        result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=180)
    except subprocess.TimeoutExpired:
        return [], {"query_faa": query_faa, "n_raw_hits": 0, "cache_hit": False, "timed_out": True}
    if result.returncode != 0:
        raise RuntimeError(f"diamond blastp failed for {query_faa}: {result.stderr.strip() or result.stdout.strip()}")
    with open(out_path, "w", encoding="utf-8") as handle:
        handle.write(result.stdout)
    rows = parse_diamond_outfmt6(result.stdout)
    return rows, {"query_faa": query_faa, "out_path": out_path, "n_raw_hits": len(rows), "cache_hit": False}


def summarize_acr_hits(
    raw_hits: list[dict[str, object]],
    query_rows: list[dict[str, object]],
    acr_refs: dict[str, dict[str, object]],
    family_to_subtype: dict[str, str],
) -> dict[str, object]:
    query_lengths = {safe_name(str(row.get("id") or "")): int(row.get("aa_length") or len(str(row.get("aa") or ""))) for row in query_rows}
    query_by_id = {safe_name(str(row.get("id") or "")): row for row in query_rows}
    passing: list[dict[str, object]] = []
    counts_by_subtype: dict[str, int] = {}
    counts_by_family: dict[str, int] = {}
    seen: set[tuple[str, str]] = set()
    low_complexity_rejected = 0
    for hit in raw_hits:
        qseqid = str(hit.get("qseqid") or "")
        sseqid = str(hit.get("sseqid") or "").split()[0]
        if (qseqid, sseqid) in seen:
            continue
        seen.add((qseqid, sseqid))
        subtype = family_to_subtype.get(sseqid)
        if subtype is None:
            continue
        if not diamond_hit_passes({**hit, "sseqid": sseqid}, query_lengths, acr_refs):
            continue
        query_seq = str(dict(query_by_id.get(qseqid) or {}).get("aa") or "")
        if query_seq and low_complexity_fraction(query_seq) >= 0.80:
            low_complexity_rejected += 1
            continue
        clean_hit = dict(hit)
        clean_hit["sseqid"] = sseqid
        clean_hit["inhibited_subtype"] = subtype
        passing.append(clean_hit)
        counts_by_subtype[subtype] = counts_by_subtype.get(subtype, 0) + 1
        counts_by_family[sseqid] = counts_by_family.get(sseqid, 0) + 1
    return {
        "hits": passing,
        "counts_by_subtype": counts_by_subtype,
        "counts_by_family": counts_by_family,
        "n_mapped_hits": len(passing),
        "n_low_complexity_rejected": low_complexity_rejected,
    }


def make_prophage_id(host: str, contig: str, start: int, stop: int) -> str:
    return safe_name(f"{host}_{contig}_{start}_{stop}")


def matched_controls(exposed: dict[str, object], candidates: list[dict[str, object]]) -> tuple[list[dict[str, object]], str]:
    tiers = [
        ("same_contig_all_bins", lambda row: row.get("contig") == exposed.get("contig") and row.get("length_bin") == exposed.get("length_bin") and row.get("gc_bin") == exposed.get("gc_bin") and row.get("orf_bin") == exposed.get("orf_bin") and row.get("cryptic_score") == exposed.get("cryptic_score")),
        ("all_bins", lambda row: row.get("length_bin") == exposed.get("length_bin") and row.get("gc_bin") == exposed.get("gc_bin") and row.get("orf_bin") == exposed.get("orf_bin") and row.get("cryptic_score") == exposed.get("cryptic_score")),
        ("length_gc_orf", lambda row: row.get("length_bin") == exposed.get("length_bin") and row.get("gc_bin") == exposed.get("gc_bin") and row.get("orf_bin") == exposed.get("orf_bin")),
        ("length_orf_cryptic", lambda row: row.get("length_bin") == exposed.get("length_bin") and row.get("orf_bin") == exposed.get("orf_bin") and row.get("cryptic_score") == exposed.get("cryptic_score")),
        ("length_bin", lambda row: row.get("length_bin") == exposed.get("length_bin")),
        ("same_host_any_scored", lambda row: True),
    ]
    for label, predicate in tiers:
        rows = [row for row in candidates if predicate(row)]
        if rows:
            return rows, label
    return [], "none"


def subtype_count(prophage: dict[str, object], subtype: str, family_to_subtype: dict[str, str] | None = None) -> int:
    if family_to_subtype is None:
        return int(dict(prophage.get("acr_counts_by_subtype") or {}).get(subtype, 0))
    total = 0
    for family, count in dict(prophage.get("acr_counts_by_family") or {}).items():
        if family_to_subtype.get(str(family)) == subtype:
            total += int(count)
    return total


def estimate_cell_metrics(
    exposed: dict[str, object],
    controls: list[dict[str, object]],
    target_subtype: str,
    host_subtypes: set[str],
    acr_target_subtypes: set[str],
    family_to_subtype: dict[str, str] | None = None,
) -> dict[str, object]:
    protein_count = int(exposed.get("protein_count") or 0)
    a_count = subtype_count(exposed, target_subtype, family_to_subtype)
    y = y_value(a_count, protein_count)
    control_y = [
        y_value(subtype_count(row, target_subtype, family_to_subtype), int(row.get("protein_count") or 0))
        for row in controls
    ]
    control_median_y = median(control_y)
    w = y - control_median_y
    absent_subtypes = sorted(subtype for subtype in acr_target_subtypes if subtype not in host_subtypes)
    decoy_w_values: list[float] = []
    for decoy in absent_subtypes:
        decoy_y = y_value(subtype_count(exposed, decoy, family_to_subtype), protein_count)
        decoy_controls = [
            y_value(subtype_count(row, decoy, family_to_subtype), int(row.get("protein_count") or 0))
            for row in controls
        ]
        decoy_w_values.append(decoy_y - median(decoy_controls))
    decoy_median_w = median(decoy_w_values)
    d_value = w - decoy_median_w
    total_mapped = sum(int(value) for value in dict(exposed.get("acr_counts_by_subtype") or {}).values())
    return {
        "A": a_count,
        "L": protein_count,
        "Y": y,
        "control_median_Y": control_median_y,
        "W": w,
        "decoy_median_W": decoy_median_w,
        "D": d_value,
        "n_absent_subtype_decoys": len(absent_subtypes),
        "mapped_acr_hits": total_mapped,
        "non_cognate_acr_hits": max(0, total_mapped - a_count),
    }


def estimate_rows_for_host(
    host_row: dict[str, object],
    prophages: list[dict[str, object]],
    exposed_ids: set[str],
    target_subtype: str,
    host_subtypes: set[str],
    acr_target_subtypes: set[str],
    label: str,
    family_to_subtype: dict[str, str] | None = None,
    donor_host: str | None = None,
) -> list[dict[str, object]]:
    scored = [row for row in prophages if int(row.get("protein_count") or 0) > 0]
    controls = [row for row in scored if str(row.get("prophage_id")) not in exposed_ids]
    rows: list[dict[str, object]] = []
    for exposed in scored:
        pid = str(exposed.get("prophage_id"))
        if pid not in exposed_ids:
            continue
        matched, match_level = matched_controls(exposed, controls)
        if not matched:
            continue
        metrics = estimate_cell_metrics(exposed, matched, target_subtype, host_subtypes, acr_target_subtypes, family_to_subtype)
        row = {
            "host": str(host_row.get("host") or ""),
            "genus": str(host_row.get("genus") or "unmapped"),
            "prophage_id": pid,
            "contig": str(exposed.get("contig") or ""),
            "subtype": target_subtype,
            "label": label,
            "match_level": match_level,
            "n_matched_unexposed": len(matched),
            "length": int(exposed.get("length") or 0),
            "gc": float(exposed.get("gc") or 0.0),
            "orf_count": int(exposed.get("orf_count") or 0),
            "cryptic_score": exposed.get("cryptic_score"),
            **metrics,
        }
        if donor_host is not None:
            row["donor_host"] = donor_host
        rows.append(row)
    return rows


def prepare_host_data(
    host_data: dict[str, object],
    host_subtypes: list[str],
    spacer_index: dict[str, set[str]],
    min_match: int,
    deadline: float | None,
    db_prefix: str,
    diamond: str,
    acr_refs: dict[str, dict[str, object]],
    family_to_subtype: dict[str, str],
) -> tuple[dict[str, object], list[dict[str, object]], list[dict[str, object]], set[str]]:
    host = str(host_data["host"])
    contigs = list(host_data.get("contigs") or [])
    raw_regions = list(host_data.get("regions") or [])
    host_spacers: set[str] = set()
    for contig in contigs:
        host_spacers.update(spacer_index.get(str(contig), set()))
    contig_sequences: dict[str, str] = {}
    contig_headers: dict[str, str] = {}
    cds_by_contig: dict[str, list[dict[str, object]]] = {}
    fetch_errors: list[str] = []
    for contig in contigs:
        try:
            header, seq, _contact = fetch_contig_fasta(str(contig), deadline)
            contig_headers[str(contig)] = header
            contig_sequences[str(contig)] = seq
        except Exception as exc:
            fetch_errors.append(f"{contig}:fasta:{type(exc).__name__}:{exc}")
        try:
            cds_rows, _cds_contact = fetch_contig_cds_aa(str(contig), deadline)
            cds_by_contig[str(contig)] = cds_rows
        except Exception as exc:
            fetch_errors.append(f"{contig}:cds_aa:{type(exc).__name__}:{exc}")
    genus = "unmapped"
    for header in contig_headers.values():
        genus = derive_genus_from_defline(header)
        if genus != "unmapped":
            break
    regions_by_contig: dict[str, list[dict[str, object]]] = {}
    for raw in raw_regions:
        regions_by_contig.setdefault(str(raw.get("contig") or ""), []).append(raw)
    chromosome_rows: list[dict[str, object]] = []
    for contig, cds_rows in cds_by_contig.items():
        chromosome_rows.extend(cds_outside_regions(cds_rows, regions_by_contig.get(contig, [])))
    chromosome_query = os.path.join(CACHE_DIR, "chromosome_faa", safe_name(host) + ".faa")
    write_faa(chromosome_query, chromosome_rows, id_prefix=safe_name(host) + "_")
    chrom_raw_hits, _chrom_contact = run_diamond_blastp(
        chromosome_query,
        db_prefix,
        diamond,
        os.path.join(CACHE_DIR, "diamond_hits", "chromosome", safe_name(host) + ".tsv"),
    )
    chrom_summary = summarize_acr_hits(chrom_raw_hits, chromosome_rows, acr_refs, family_to_subtype)
    chrom_counts = dict(chrom_summary["counts_by_subtype"])
    prophages: list[dict[str, object]] = []
    for raw in raw_regions:
        contig = str(raw.get("contig") or "")
        start = int(raw.get("start") or 0)
        stop = int(raw.get("stop") or 0)
        seq = ""
        if contig in contig_sequences and start > 0 and stop <= len(contig_sequences[contig]):
            seq = contig_sequences[contig][start - 1 : stop]
        protein_rows = cds_in_region(cds_by_contig.get(contig, []), start, stop)
        products = [str(row.get("product") or "") for row in protein_rows if str(row.get("product") or "")]
        flinders_cds = int(raw.get("flinders_cds") or 0)
        orf_count = len(protein_rows) if protein_rows else flinders_cds
        pid = make_prophage_id(host, contig, start, stop)
        profile = module_profile(products, orf_count)
        gc = gc_fraction(seq)
        query_faa = os.path.join(CACHE_DIR, "query_faa", safe_name(pid) + ".faa")
        indexed_proteins = []
        for index, row in enumerate(protein_rows, start=1):
            clean = dict(row)
            clean["id"] = safe_name(f"{pid}_{index}")
            indexed_proteins.append(clean)
        write_faa(query_faa, indexed_proteins)
        raw_hits, diamond_contact = run_diamond_blastp(
            query_faa,
            db_prefix,
            diamond,
            os.path.join(CACHE_DIR, "diamond_hits", "prophage", safe_name(pid) + ".tsv"),
        )
        hit_summary = summarize_acr_hits(raw_hits, indexed_proteins, acr_refs, family_to_subtype)
        prophage = {
            "host": host,
            "genus": genus,
            "prophage_id": pid,
            "contig": contig,
            "start": start,
            "stop": stop,
            "length": int(raw.get("length") or (stop - start + 1)),
            "sequence": seq,
            "gc": gc,
            "orf_count": orf_count,
            "protein_count": len(indexed_proteins),
            "flinders_cds": flinders_cds,
            "modules": profile["modules"],
            "modules_present": profile["modules_present"],
            "cryptic_score": profile["cryptic_score"],
            "intact_like": profile["intact_like"],
            "integrase_present": profile["integrase_present"],
            "length_bin": length_bin(int(raw.get("length") or (stop - start + 1))),
            "gc_bin": gc_bin(gc),
            "orf_bin": orf_bin(orf_count),
            "acr_counts_by_subtype": hit_summary["counts_by_subtype"],
            "acr_counts_by_family": hit_summary["counts_by_family"],
            "n_mapped_acr_hits": hit_summary["n_mapped_hits"],
            "n_low_complexity_rejected": hit_summary["n_low_complexity_rejected"],
            "diamond": diamond_contact,
        }
        prophages.append(prophage)
    exposure_events, exposed_ids = exposure_events_for_spacers(host, host_spacers, prophages, min_match)
    subtype = host_subtypes[0] if host_subtypes else ""
    chrom_cognate = int(chrom_counts.get(subtype, 0))
    chromosome_y = y_value(chrom_cognate, len(chromosome_rows))
    for prophage in prophages:
        prophage["exposed"] = str(prophage["prophage_id"]) in exposed_ids
        prophage["cognate_acr_hits"] = int(dict(prophage.get("acr_counts_by_subtype") or {}).get(subtype, 0))
        prophage["non_cognate_acr_hits"] = max(0, int(prophage.get("n_mapped_acr_hits") or 0) - int(prophage["cognate_acr_hits"]))
        prophage["chromosome_cognate_Y"] = chromosome_y
    host_row = {
        "host": host,
        "genus": genus,
        "subtypes": host_subtypes,
        "primary_subtype": subtype,
        "n_contigs": len(contigs),
        "n_prophages": len(prophages),
        "n_spacers": len(host_spacers),
        "n_exposed_prophages": len(exposed_ids),
        "n_exposure_events": len(exposure_events),
        "n_prophages_with_proteins": sum(1 for row in prophages if int(row.get("protein_count") or 0) > 0),
        "n_chromosome_proteins": len(chromosome_rows),
        "chromosome_acr_counts_by_subtype": chrom_counts,
        "chromosome_cognate_acr_hits": chrom_cognate,
        "chromosome_cognate_Y": chromosome_y,
        "has_spacer_and_prophage": bool(host_spacers and prophages),
        "fetch_errors": fetch_errors[:8],
    }
    return host_row, prophages, exposure_events, host_spacers


def run_shuffled_null(
    hosts_runtime: dict[str, dict[str, object]],
    min_match: int,
    acr_target_subtypes: set[str],
    seed: int = 2601,
) -> tuple[list[dict[str, object]], dict[str, object]]:
    rng = random.Random(seed)
    rows: list[dict[str, object]] = []
    n_events = 0
    for host, runtime in sorted(hosts_runtime.items()):
        subtype = str(runtime.get("subtype") or "")
        if not subtype:
            continue
        spacers = {dinucleotide_shuffle(spacer, rng) for spacer in set(runtime.get("spacers") or set())}
        prophages = list(runtime.get("prophages") or [])
        host_row = dict(runtime.get("host_row") or {})
        events, exposed = exposure_events_for_spacers(host, spacers, prophages, min_match)
        n_events += len(events)
        rows.extend(estimate_rows_for_host(host_row, prophages, exposed, subtype, {subtype}, acr_target_subtypes, "shuffled"))
    median_w = genus_capped_weighted_median([(float(row.get("W") or 0.0), str(row.get("genus") or "unmapped")) for row in rows])
    median_d = genus_capped_weighted_median([(float(row.get("D") or 0.0), str(row.get("genus") or "unmapped")) for row in rows])
    return rows, {"n_rows": len(rows), "n_exposure_events": n_events, "median_W": median_w, "median_D": median_d}


def run_cross_host_null(
    hosts_runtime: dict[str, dict[str, object]],
    min_match: int,
    acr_target_subtypes: set[str],
) -> tuple[list[dict[str, object]], dict[str, object]]:
    by_genus: dict[str, list[str]] = {}
    for host, runtime in hosts_runtime.items():
        genus = str(dict(runtime.get("host_row") or {}).get("genus") or "unmapped")
        if genus == "unmapped":
            continue
        if runtime.get("spacers") and runtime.get("subtype"):
            by_genus.setdefault(genus, []).append(host)
    rows: list[dict[str, object]] = []
    n_events = 0
    n_swaps = 0
    for host, runtime in sorted(hosts_runtime.items()):
        host_row = dict(runtime.get("host_row") or {})
        genus = str(host_row.get("genus") or "unmapped")
        donors = [candidate for candidate in sorted(by_genus.get(genus, [])) if candidate != host]
        if not donors:
            continue
        prophages = list(runtime.get("prophages") or [])
        for donor in donors[:3]:
            donor_runtime = hosts_runtime[donor]
            donor_spacers = set(donor_runtime.get("spacers") or set())
            donor_subtype = str(donor_runtime.get("subtype") or "")
            if not donor_subtype:
                continue
            events, exposed = exposure_events_for_spacers(host, donor_spacers, prophages, min_match)
            n_events += len(events)
            n_swaps += 1
            rows.extend(
                estimate_rows_for_host(
                    host_row,
                    prophages,
                    exposed,
                    donor_subtype,
                    {donor_subtype},
                    acr_target_subtypes,
                    "same_genus_cross_host",
                    donor_host=donor,
                )
            )
    median_w = genus_capped_weighted_median([(float(row.get("W") or 0.0), str(row.get("genus") or "unmapped")) for row in rows])
    median_d = genus_capped_weighted_median([(float(row.get("D") or 0.0), str(row.get("genus") or "unmapped")) for row in rows])
    return rows, {"n_rows": len(rows), "n_exposure_events": n_events, "n_swaps": n_swaps, "median_W": median_w, "median_D": median_d}


def attach_s_values(own_rows: list[dict[str, object]], cross_rows: list[dict[str, object]]) -> None:
    cross_by_target: dict[tuple[str, str], list[float]] = {}
    for row in cross_rows:
        key = (str(row.get("host") or ""), str(row.get("prophage_id") or ""))
        cross_by_target.setdefault(key, []).append(float(row.get("D") or 0.0))
    for row in own_rows:
        key = (str(row.get("host") or ""), str(row.get("prophage_id") or ""))
        cross_median = median(cross_by_target.get(key, []))
        row["cross_median_D"] = cross_median
        row["S"] = float(row.get("D") or 0.0) - cross_median


def run_label_permutation_null(
    own_rows: list[dict[str, object]],
    hosts_runtime: dict[str, dict[str, object]],
    family_to_subtype: dict[str, str],
    acr_target_subtypes: set[str],
    n: int,
    seed: int = 9109,
) -> dict[str, object]:
    if not own_rows or n <= 0:
        return {"n": 0, "median_permuted_W": 0.0, "true_beats_permuted": False, "p_true_le_permuted": None}
    true_median = genus_capped_weighted_median([(float(row.get("W") or 0.0), str(row.get("genus") or "unmapped")) for row in own_rows])
    families = sorted(family_to_subtype)
    labels = [family_to_subtype[family] for family in families]
    rng = random.Random(seed)
    permuted_medians: list[float] = []
    for _idx in range(n):
        shuffled = list(labels)
        rng.shuffle(shuffled)
        permuted_map = {family: shuffled[index] for index, family in enumerate(families)}
        perm_rows: list[dict[str, object]] = []
        for own in own_rows:
            host = str(own.get("host") or "")
            runtime = hosts_runtime.get(host)
            if not runtime:
                continue
            prophages = list(runtime.get("prophages") or [])
            by_id = {str(row.get("prophage_id")): row for row in prophages}
            exposed = by_id.get(str(own.get("prophage_id") or ""))
            if exposed is None:
                continue
            controls = [row for row in prophages if int(row.get("protein_count") or 0) > 0 and not row.get("exposed")]
            matched, _level = matched_controls(exposed, controls)
            if not matched:
                continue
            subtype = str(own.get("subtype") or "")
            metrics = estimate_cell_metrics(exposed, matched, subtype, {subtype}, acr_target_subtypes, permuted_map)
            perm_rows.append({"W": metrics["W"], "genus": own.get("genus")})
        permuted_medians.append(genus_capped_weighted_median([(float(row["W"]), str(row.get("genus") or "unmapped")) for row in perm_rows]))
    perm_median = median(permuted_medians)
    p_true_le = sum(1 for value in permuted_medians if true_median <= value) / len(permuted_medians) if permuted_medians else None
    return {
        "n": len(permuted_medians),
        "median_permuted_W": perm_median,
        "true_median_W": true_median,
        "true_minus_permuted_W": true_median - perm_median,
        "true_beats_permuted": bool(true_median > perm_median),
        "p_true_le_permuted": p_true_le,
    }


def chromosome_control_summary(own_rows: list[dict[str, object]], hosts_runtime: dict[str, dict[str, object]]) -> dict[str, object]:
    deltas: list[tuple[float, str]] = []
    for row in own_rows:
        host = str(row.get("host") or "")
        pid = str(row.get("prophage_id") or "")
        runtime = hosts_runtime.get(host)
        if not runtime:
            continue
        prophages = {str(prophage.get("prophage_id")): prophage for prophage in list(runtime.get("prophages") or [])}
        prophage = prophages.get(pid)
        if prophage is None:
            continue
        delta = float(row.get("Y") or 0.0) - float(prophage.get("chromosome_cognate_Y") or 0.0)
        deltas.append((delta, str(row.get("genus") or "unmapped")))
    median_delta = genus_capped_weighted_median(deltas)
    return {"n_rows": len(deltas), "median_prophage_minus_chromosome_Y": median_delta, "clean": bool(deltas and median_delta > 0.0)}


def preflight_gates(own_rows: list[dict[str, object]]) -> dict[str, object]:
    known_rows = [row for row in own_rows if int(row.get("mapped_acr_hits") or 0) > 0]
    known_genus_counts: dict[str, int] = {}
    subtype_set: set[str] = set()
    for row in own_rows:
        subtype = str(row.get("subtype") or "")
        if subtype:
            subtype_set.add(subtype)
    for row in known_rows:
        genus = str(row.get("genus") or "unmapped")
        known_genus_counts[genus] = known_genus_counts.get(genus, 0) + 1
    w_items = [(float(row.get("W") or 0.0), str(row.get("genus") or "unmapped")) for row in own_rows]
    group_weights = genus_group_weights(w_items, GENUS_CAP)
    top_genus = None
    top_weight = 0.0
    if group_weights:
        top_genus, top_weight = max(group_weights.items(), key=lambda item: item[1])
    total_known = sum(known_genus_counts.values())
    raw_top_fraction = 0.0
    if total_known > 0:
        raw_top_fraction = max(known_genus_counts.values()) / total_known
    full_w = genus_capped_weighted_median(w_items)
    dropped: dict[str, float] = {}
    stable = bool(w_items)
    for genus in sorted({group for _value, group in w_items}):
        dropped_w = genus_capped_weighted_median([(value, group) for value, group in w_items if group != genus])
        dropped[genus] = dropped_w
        if not signs_not_reversed(full_w, dropped_w):
            stable = False
    checks = {
        "matched_exposed_prophages_ge_100": len(own_rows) >= 100,
        "known_acr_positive_exposed_cells_ge_25": len(known_rows) >= 25,
        "known_acr_positive_genera_ge_10": len(known_genus_counts) >= 10,
        "single_genus_capped_weight_not_gt_20pct": bool(group_weights and top_weight <= 0.20),
        "crispr_subtypes_represented_ge_2": len(subtype_set) >= 2,
        "leave_one_genus_out_direction_not_reversed": stable,
    }
    return {
        "passed": all(checks.values()),
        "checks": checks,
        "counts": {
            "n_exposed_prophages_with_matched_same_host_unexposed_control": len(own_rows),
            "n_known_acr_positive_exposed_cells": len(known_rows),
            "n_cognate_acr_positive_exposed_cells": sum(1 for row in own_rows if int(row.get("A") or 0) > 0),
            "n_known_acr_positive_genera": len(known_genus_counts),
            "known_acr_positive_genus_counts": dict(sorted(known_genus_counts.items())),
            "top_genus_by_capped_weight": top_genus,
            "top_genus_capped_weight": top_weight,
            "raw_top_known_acr_positive_genus_fraction": raw_top_fraction,
            "n_crispr_subtypes_represented": len(subtype_set),
            "subtypes_represented": sorted(subtype_set),
            "genus_capped_median_W": full_w,
            "leave_one_genus_out_median_W": dropped,
        },
    }


def verdict_from_summary(summary: dict[str, object]) -> str:
    preflight = dict(summary.get("preflight") or {})
    if not preflight.get("passed"):
        return "data_gate_failed"
    median_w = float(summary.get("genus_capped_median_W") or 0.0)
    median_d = float(summary.get("genus_capped_median_D") or 0.0)
    median_s = float(summary.get("genus_capped_median_S") or 0.0)
    n2 = dict(summary.get("N2_non_cognate_acr_decoy") or {})
    n3 = dict(summary.get("N3_same_genus_cross_host") or {})
    n4 = dict(summary.get("N4_shuffled_spacer") or {})
    n5 = dict(summary.get("N5_chromosome_protein_control") or {})
    n6 = dict(summary.get("N6_acr_subtype_label_permutation") or {})
    if median_w < 0.0:
        return "anti"
    if bool(n3.get("cross_host_retains_signal")):
        return "ecology_dominated"
    if (
        median_w > 0.0
        and median_d > 0.0
        and median_s > 0.0
        and bool(n2.get("cognate_beats_non_cognate_decoy"))
        and bool(n3.get("own_beats_cross_host"))
        and bool(n4.get("true_spacers_beat_shuffled"))
        and bool(n5.get("clean"))
        and bool(n6.get("true_beats_permuted"))
    ):
        return "supportive"
    return "refuted"


def summarize(
    manifest_meta: dict[str, object],
    spacer_meta: dict[str, object],
    flinders_meta: dict[str, object],
    subtype_meta: dict[str, object],
    acr_meta: dict[str, object],
    diamond_meta: dict[str, object],
    per_host: list[dict[str, object]],
    own_rows: list[dict[str, object]],
    shuffled_rows: list[dict[str, object]],
    shuffled_summary: dict[str, object],
    cross_rows: list[dict[str, object]],
    cross_summary: dict[str, object],
    n6_summary: dict[str, object],
    n5_summary: dict[str, object],
    n_excluded_multi_subtype_hosts: int,
) -> dict[str, object]:
    w_items = [(float(row.get("W") or 0.0), str(row.get("genus") or "unmapped")) for row in own_rows]
    d_items = [(float(row.get("D") or 0.0), str(row.get("genus") or "unmapped")) for row in own_rows]
    s_items = [(float(row.get("S") or 0.0), str(row.get("genus") or "unmapped")) for row in own_rows]
    median_w = genus_capped_weighted_median(w_items)
    median_d = genus_capped_weighted_median(d_items)
    median_s = genus_capped_weighted_median(s_items)
    cross_d = float(cross_summary.get("median_D") or 0.0)
    shuffled_w = float(shuffled_summary.get("median_W") or 0.0)
    preflight = preflight_gates(own_rows)
    subtype_set = sorted({str(row.get("subtype") or "") for row in own_rows if str(row.get("subtype") or "")})
    n_exposure_events = sum(int(row.get("n_exposure_events") or 0) for row in per_host)
    n_single_subtype_hosts = sum(1 for row in per_host if len(list(row.get("subtypes") or [])) == 1)
    summary: dict[str, object] = {
        "n_hosts": len(per_host) + n_excluded_multi_subtype_hosts,
        "n_single_subtype_hosts": n_single_subtype_hosts,
        "n_multi_subtype_hosts_excluded_from_primary": n_excluded_multi_subtype_hosts,
        "n_exposure_events": n_exposure_events,
        "n_matched_exposed_prophage_cells": len(own_rows),
        "input": {
            "manifest": manifest_meta,
            "spacers": spacer_meta,
            "flinders": flinders_meta,
            "gca_subtypes": subtype_meta,
            "known_acr": acr_meta,
            "diamond": diamond_meta,
        },
        "preflight": preflight,
        "genus_capped_median_W": median_w,
        "genus_capped_median_D": median_d,
        "genus_capped_median_S": median_s,
        "N1_same_host_unexposed": {
            "n_rows": len(own_rows),
            "median_W": median_w,
            "matched_control_denominator": "same_host_unexposed_length_orf_gc_cryptic_bins",
        },
        "N2_non_cognate_acr_decoy": {
            "median_D": median_d,
            "cognate_beats_non_cognate_decoy": bool(median_d > 0.0),
        },
        "N3_same_genus_cross_host": {
            **cross_summary,
            "median_cross_D": cross_d,
            "S": median_s,
            "own_beats_cross_host": bool(median_s > 0.0),
            "cross_host_retains_signal": bool(cross_d > 0.0 and median_s <= 0.0),
        },
        "N4_shuffled_spacer": {
            **shuffled_summary,
            "true_minus_shuffled_W": median_w - shuffled_w,
            "true_spacers_beat_shuffled": bool(median_w > shuffled_w and shuffled_w <= 0.0),
        },
        "N5_chromosome_protein_control": n5_summary,
        "N6_acr_subtype_label_permutation": n6_summary,
        "subtypes_represented": subtype_set,
    }
    summary["verdict"] = verdict_from_summary(summary)
    return summary


def clean_prophage_row(row: dict[str, object]) -> dict[str, object]:
    clean = dict(row)
    clean.pop("sequence", None)
    clean.pop("diamond", None)
    return clean


def run_pipeline() -> dict[str, object]:
    host_limit = parse_host_limit()
    min_match = env_int("CA_MIN_SPACER_MATCH", 28)
    n6_permutations = env_int("CA_N6_PERMUTATIONS", 100)
    manifest_path = env_path("CA_MANIFEST", DEFAULT_MANIFEST)
    spacer_path = env_path("CA_SPACER_FSA", DEFAULT_SPACER_FSA)
    flinders_path = env_path("CA_FLINDERS_BULK", DEFAULT_FLINDERS_BULK)
    subtype_path = env_path("CA_GCA_SUBTYPES", DEFAULT_GCA_SUBTYPES)
    acr_faa = env_path("CA_ACR_FAA", DEFAULT_ACR_FAA)
    diamond = env_path("CA_DIAMOND", DEFAULT_DIAMOND)
    deadline = deadline_from_env()

    manifest_contigs, manifest_meta = load_manifest(manifest_path, host_limit)
    manifest_set = set(manifest_contigs)
    spacer_index, spacer_meta = load_spacer_index(spacer_path, manifest_set)
    hosts, flinders_meta = load_flinders_regions(flinders_path, manifest_set)
    gca_subtypes, subtype_meta = load_gca_subtypes(subtype_path)
    acr_refs, family_to_subtype, acr_meta = load_acr_references(acr_faa)
    db_prefix, diamond_meta = ensure_acr_diamond_db(acr_faa, diamond)
    acr_target_subtypes = set(family_to_subtype.values())

    per_host: list[dict[str, object]] = []
    per_prophage: list[dict[str, object]] = []
    own_rows: list[dict[str, object]] = []
    all_events: list[dict[str, object]] = []
    hosts_runtime: dict[str, dict[str, object]] = {}
    n_excluded_multi_subtype_hosts = 0

    for host in sorted(hosts):
        subtypes = list(gca_subtypes.get(host, []))
        if len(subtypes) != 1:
            if len(subtypes) > 1:
                n_excluded_multi_subtype_hosts += 1
            continue
        host_data = hosts[host]
        subtype = subtypes[0]
        host_row, prophages, exposure_events, host_spacers = prepare_host_data(
            host_data,
            subtypes,
            spacer_index,
            min_match,
            deadline,
            db_prefix,
            diamond,
            acr_refs,
            family_to_subtype,
        )
        exposed_ids = {str(row["prophage_id"]) for row in prophages if row.get("exposed")}
        host_rows = estimate_rows_for_host(host_row, prophages, exposed_ids, subtype, set(subtypes), acr_target_subtypes, "own")
        host_row["n_matched_exposed_prophages"] = len(host_rows)
        per_host.append(host_row)
        per_prophage.extend(clean_prophage_row(row) for row in prophages)
        own_rows.extend(host_rows)
        all_events.extend(exposure_events)
        hosts_runtime[host] = {"host_row": host_row, "prophages": prophages, "spacers": host_spacers, "subtype": subtype}

    shuffled_rows, shuffled_summary = run_shuffled_null(hosts_runtime, min_match, acr_target_subtypes)
    cross_rows, cross_summary = run_cross_host_null(hosts_runtime, min_match, acr_target_subtypes)
    attach_s_values(own_rows, cross_rows)
    n6_summary = run_label_permutation_null(own_rows, hosts_runtime, family_to_subtype, acr_target_subtypes, n6_permutations)
    n5_summary = chromosome_control_summary(own_rows, hosts_runtime)
    summary = summarize(
        manifest_meta,
        spacer_meta,
        flinders_meta,
        subtype_meta,
        acr_meta,
        diamond_meta,
        per_host,
        own_rows,
        shuffled_rows,
        shuffled_summary,
        cross_rows,
        cross_summary,
        n6_summary,
        n5_summary,
        n_excluded_multi_subtype_hosts,
    )
    return {
        "summary": summary,
        "per_host": per_host,
        "per_prophage": per_prophage,
        "matched_rows": own_rows,
        "null_rows": {
            "N3_same_genus_cross_host": cross_rows,
            "N4_shuffled_spacer": shuffled_rows,
        },
        "exposure_events": all_events,
    }


def assert_close(actual: float, expected: float, eps: float = 1e-9) -> None:
    if abs(actual - expected) > eps:
        raise AssertionError(f"{actual} != {expected}")


def synthetic_preflight_rows(
    n: int = 120,
    known: int = 30,
    genera: int = 12,
    subtypes: list[str] | None = None,
    w_value: float = 1.0,
) -> list[dict[str, object]]:
    subtype_values = subtypes or ["I-F", "II-A"]
    rows: list[dict[str, object]] = []
    for idx in range(n):
        rows.append(
            {
                "host": f"h{idx}",
                "genus": f"G{idx % genera}",
                "prophage_id": f"p{idx}",
                "subtype": subtype_values[idx % len(subtype_values)],
                "W": w_value,
                "D": 1.0,
                "S": 1.0,
                "A": 1 if idx < known else 0,
                "mapped_acr_hits": 1 if idx < known else 0,
            }
        )
    return rows


def run_selftest() -> dict[str, object]:
    parse_cases = {"AcrIIA4": "II-A", "AcrIF1": "I-F", "AcrIA": "I-A", "AcrVIA2": "VI-A"}
    for family, expected in parse_cases.items():
        actual = parse_acr_family_subtype(family)
        if actual != expected:
            raise AssertionError(f"Acr parse failed for {family}: {actual}")
    if parse_acr_family_subtype("AntiCRISPR") is not None:
        raise AssertionError("unparseable Acr family was not excluded")

    query_rows = [{"id": "q1", "aa": "MSTNPKPQRKTKRNTNRRPQDVKFPGGGQIVGGVYLLPRRGPRLGVRATRKTSERSQPRGRRQPIPKARRPEGRTWA", "aa_length": 84}]
    acr_refs = {"AcrIF1": {"aa_length": 100}}
    good_hit = {"qseqid": "q1", "sseqid": "AcrIF1", "pident": "35", "length": "75", "qlen": "84", "slen": "100", "evalue": "1e-20"}
    if not diamond_hit_passes(good_hit, {"q1": 84}, acr_refs):
        raise AssertionError("diamond pass gate rejected a valid hit")
    for key, value in [("pident", "29.9"), ("length", "69"), ("evalue", "1e-4")]:
        bad = dict(good_hit)
        bad[key] = value
        if diamond_hit_passes(bad, {"q1": 100}, acr_refs):
            raise AssertionError(f"diamond gate accepted bad {key}")
    bad_ref = dict(good_hit)
    if diamond_hit_passes(bad_ref, {"q1": 100}, {"AcrIF1": {"aa_length": 251}}):
        raise AssertionError("diamond gate accepted long Acr reference")
    hit_summary = summarize_acr_hits([good_hit], query_rows, acr_refs, {"AcrIF1": "I-F"})
    if hit_summary["counts_by_subtype"] != {"I-F": 1}:
        raise AssertionError("Acr subtype hit summary failed")

    exposed = {
        "prophage_id": "pE",
        "protein_count": 9,
        "acr_counts_by_subtype": {"I-F": 2, "II-A": 0},
        "acr_counts_by_family": {"AcrIF1": 2},
    }
    controls = [
        {"prophage_id": "pU1", "protein_count": 9, "acr_counts_by_subtype": {"I-F": 0, "II-A": 1}, "acr_counts_by_family": {"AcrIF1": 0, "AcrIIA4": 1}},
        {"prophage_id": "pU2", "protein_count": 9, "acr_counts_by_subtype": {"I-F": 0, "II-A": 1}, "acr_counts_by_family": {"AcrIF1": 0, "AcrIIA4": 1}},
    ]
    metrics = estimate_cell_metrics(exposed, controls, "I-F", {"I-F"}, {"I-F", "II-A"})
    assert_close(metrics["Y"], math.log2(2.5 / 10.0))
    assert_close(metrics["control_median_Y"], math.log2(0.5 / 10.0))
    assert_close(metrics["W"], math.log2(2.5 / 0.5))
    if metrics["D"] <= metrics["W"]:
        raise AssertionError("D should exceed W when absent decoy is enriched in controls")
    own_rows = [{"host": "h1", "prophage_id": "pE", "D": metrics["D"], "genus": "G", "W": metrics["W"]}]
    cross_rows = [{"host": "h1", "prophage_id": "pE", "D": 0.25, "genus": "G"}]
    attach_s_values(own_rows, cross_rows)
    assert_close(float(own_rows[0]["S"]), float(metrics["D"]) - 0.25)

    capped_items = [(0.0, "Dominant") for _idx in range(90)] + [(10.0, f"G{idx}") for idx in range(10)]
    assert_close(genus_capped_weighted_median(capped_items), 10.0)

    passing_rows = synthetic_preflight_rows()
    gates = preflight_gates(passing_rows)
    if not gates["passed"]:
        raise AssertionError(f"preflight pass failed: {gates}")
    failing_sets = {
        "matched_exposed_prophages_ge_100": synthetic_preflight_rows(n=99, known=30, genera=12),
        "known_acr_positive_exposed_cells_ge_25": synthetic_preflight_rows(n=120, known=24, genera=12),
        "known_acr_positive_genera_ge_10": synthetic_preflight_rows(n=120, known=30, genera=9),
        "single_genus_capped_weight_not_gt_20pct": synthetic_preflight_rows(n=120, known=30, genera=4),
        "crispr_subtypes_represented_ge_2": synthetic_preflight_rows(n=120, known=30, genera=12, subtypes=["I-F"]),
        "leave_one_genus_out_direction_not_reversed": [
            {
                "host": f"h{genus_idx}_{slot}",
                "genus": f"LG{genus_idx}",
                "prophage_id": f"lp{genus_idx}_{slot}",
                "subtype": "I-F" if slot % 2 == 0 else "II-A",
                "W": 1.0 if genus_idx < 6 else -1.0,
                "D": 1.0,
                "S": 1.0,
                "A": 1,
                "mapped_acr_hits": 1,
            }
            for genus_idx in range(11)
            for slot in range(10)
        ],
    }
    for check, rows in failing_sets.items():
        result = preflight_gates(rows)
        if result["checks"].get(check):
            raise AssertionError(f"preflight branch did not fail: {check}")

    host_row = {"host": "h1", "genus": "G0"}
    prophages = [
        {
            "prophage_id": "pE",
            "contig": "c",
            "protein_count": 9,
            "length_bin": "A",
            "gc_bin": "B",
            "orf_bin": "C",
            "cryptic_score": 1,
            "acr_counts_by_subtype": {"I-F": 2, "II-A": 0},
            "acr_counts_by_family": {"AcrIF1": 2, "AcrIIA4": 0},
            "exposed": True,
        },
        {
            "prophage_id": "pU",
            "contig": "c",
            "protein_count": 9,
            "length_bin": "A",
            "gc_bin": "B",
            "orf_bin": "C",
            "cryptic_score": 1,
            "acr_counts_by_subtype": {"I-F": 0, "II-A": 1},
            "acr_counts_by_family": {"AcrIF1": 0, "AcrIIA4": 1},
            "exposed": False,
        },
    ]
    n6 = run_label_permutation_null(
        estimate_rows_for_host(host_row, prophages, {"pE"}, "I-F", {"I-F"}, {"I-F", "II-A"}, "own"),
        {"h1": {"host_row": host_row, "prophages": prophages, "subtype": "I-F"}},
        {"AcrIF1": "I-F", "AcrIIA4": "II-A"},
        {"I-F", "II-A"},
        10,
        seed=1,
    )
    if n6["n"] != 10:
        raise AssertionError("N6 permutation count failed")

    base_summary = {
        "preflight": gates,
        "genus_capped_median_W": 1.0,
        "genus_capped_median_D": 1.0,
        "genus_capped_median_S": 1.0,
        "N2_non_cognate_acr_decoy": {"cognate_beats_non_cognate_decoy": True},
        "N3_same_genus_cross_host": {"own_beats_cross_host": True, "cross_host_retains_signal": False},
        "N4_shuffled_spacer": {"true_spacers_beat_shuffled": True},
        "N5_chromosome_protein_control": {"clean": True},
        "N6_acr_subtype_label_permutation": {"true_beats_permuted": True},
    }
    verdict_cases = {
        "supportive": dict(base_summary),
        "refuted": {**base_summary, "genus_capped_median_W": 0.0},
        "ecology_dominated": {**base_summary, "N3_same_genus_cross_host": {"own_beats_cross_host": False, "cross_host_retains_signal": True}},
        "anti": {**base_summary, "genus_capped_median_W": -1.0},
        "data_gate_failed": {**base_summary, "preflight": preflight_gates(synthetic_preflight_rows(n=10, known=1, genera=1))},
    }
    for expected, summary in verdict_cases.items():
        actual = verdict_from_summary(summary)
        if actual != expected:
            raise AssertionError(f"verdict {expected} failed: {actual}")

    test_spacer = "AAAACCCCGGGGTTTTAAAACCCCGGGG"
    tiny_fsa = ">ctgA+ctgB\n" + test_spacer + "\n>ctgC\n" + "TTTTCCCCAAAAGGGGTTTTCCCCAAAAGGGG\n"
    index = build_spacer_index_from_fasta_text(tiny_fsa, {"ctgA", "ctgB"})
    if index != {"ctgA": {test_spacer}, "ctgB": {test_spacer}}:
        raise AssertionError("spacer inverted index failed")
    target = "GGG" + test_spacer + "CCC"
    if not any(start == 3 and strand == "+" for start, _stop, strand in spacer_match_intervals(test_spacer, target, 28)):
        raise AssertionError("plus-strand spacer match failed")
    rc_target = "GGG" + reverse_complement(test_spacer) + "CCC"
    if not any(start == 3 and strand == "-" for start, _stop, strand in spacer_match_intervals(test_spacer, rc_target, 28)):
        raise AssertionError("reverse-complement spacer match failed")

    return {
        "ok": True,
        "tested": [
            "acr_family_subtype_parse",
            "diamond_hit_filter",
            "Y_W_D_S_math",
            "genus_capped_median",
            "preflight_pass_and_failures",
            "N6_label_permutation",
            "verdict_5_way",
            "spacer_exact_match_both_strands",
        ],
    }


def main() -> int:
    try:
        if "--selftest" in sys.argv:
            print(json.dumps(run_selftest(), sort_keys=True))
            return 0
        result = run_pipeline()
        print(json.dumps(result, sort_keys=True))
        return 0
    except Exception as exc:
        print(json.dumps({"error": f"{type(exc).__name__}: {exc}"}, sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

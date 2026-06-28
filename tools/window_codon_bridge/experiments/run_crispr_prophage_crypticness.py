#!/usr/bin/env python3
"""CRISPR spacer exposure versus resident prophage crypticness."""
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
CACHE_DIR = os.path.join(SYNCED_DIR, "crispr_prophage_crypticness")
REF_DIR = os.path.join(REPO_ROOT, "_q2ref")
DEFAULT_MANIFEST = os.path.join(REF_DIR, "host_universe_contigs.txt")
DEFAULT_SPACER_FSA = os.path.join(REF_DIR, "crisprcasdb_spacer_seqName.fsa")
DEFAULT_FLINDERS_BULK = os.path.join(
    SYNCED_DIR,
    "rm_genomes",
    "flinders_prophage",
    "phispy_all_predictions.tsv.gz",
)
DEFAULT_DF_VENV = (
    "/private/tmp/claude-501/-Users-lexa-Desktop-lexa-omega-newmath/"
    "440f01d8-6db8-475a-aa59-e73a67b5f7b8/scratchpad/sshx_gate_recal/df_venv"
)
NCBI_EFETCH_URL = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi"
USER_AGENT = "crispr-prophage-crypticness"
FETCH_TIMEOUT = 120
NCBI_DELAY_SECONDS = 0.34
DNA_ALPHABET = set("ACGTN")
REVCOMP_TABLE = str.maketrans("ACGTNacgtn", "TGCANtgcan")


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
        value = int(raw)
    except ValueError:
        return default
    return value


def env_path(name: str, default: str) -> str:
    return os.environ.get(name, "").strip() or default


def parse_host_limit() -> int | None:
    value = env_int("CC_HOST_LIMIT", 0)
    return value if value > 0 else None


def deadline_from_env() -> float | None:
    seconds = env_int("CC_FETCH_DEADLINE_SECONDS", 14400)
    return time.monotonic() + seconds if seconds > 0 else None


def deadline_expired(deadline: float | None) -> bool:
    return deadline is not None and time.monotonic() >= deadline


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


def parse_int(value: object, default: int = 0) -> int:
    text = str(value).strip()
    if not text:
        return default
    try:
        return int(float(text))
    except ValueError:
        return default


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
    genomeid = str(raw["genomeid"]).strip() or contig
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
    with opener(path, "rt", encoding="utf-8", errors="replace", newline="") as handle:  # type: ignore[arg-type]
        first = handle.readline()
        if not first:
            return hosts, {"path": path, "n_rows": 0, "n_kept_manifest_rows": 0}
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
            hosts.setdefault(host, {"host": host, "contigs": set(), "regions": []})
            hosts[host]["contigs"].add(str(row["contig"]))  # type: ignore[index,union-attr]
            hosts[host]["regions"].append(row)  # type: ignore[index,union-attr]
    for host_data in hosts.values():
        host_data["contigs"] = sorted(host_data["contigs"])  # type: ignore[index]
        host_data["regions"] = sorted(host_data["regions"], key=lambda row: (str(row["contig"]), int(row["start"]), int(row["stop"])))  # type: ignore[index]
    return hosts, {"path": path, "n_rows": n_rows, "n_kept_manifest_rows": n_kept_manifest_rows, "n_hosts": len(hosts)}


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
    url = ncbi_efetch_url(contig, "fasta")
    payload, contact = cached_bytes(url, cache_path, deadline=deadline, attempts=4)
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


def parse_feature_table_cds(text: str) -> list[dict[str, object]]:
    cds_rows: list[dict[str, object]] = []
    current: dict[str, object] | None = None
    for raw_line in text.splitlines():
        if raw_line.startswith(">"):
            continue
        cols = raw_line.rstrip("\n").split("\t")
        if len(cols) >= 3 and cols[2] == "CDS":
            if current is not None:
                cds_rows.append(current)
            start = parse_int(cols[0].lstrip("<>"))
            stop = parse_int(cols[1].lstrip("<>"))
            if start > 0 and stop > 0:
                current = {"start": min(start, stop), "stop": max(start, stop), "product": ""}
            else:
                current = None
            continue
        if current is None:
            continue
        if len(cols) >= 5 and cols[3].strip() == "product":
            current["product"] = cols[4].strip()
        elif len(cols) >= 4 and cols[2].strip() == "product":
            current["product"] = cols[3].strip()
    if current is not None:
        cds_rows.append(current)
    return cds_rows


def bracket_value(header: str, key: str) -> str:
    match = re.search(r"\[" + re.escape(key) + r"=([^\]]*)\]", header)
    return match.group(1).strip() if match else ""


def parse_fasta_cds_aa(text: str) -> list[dict[str, object]]:
    cds_rows: list[dict[str, object]] = []
    for header, _seq in parse_fasta_records(text):
        location = bracket_value(header, "location")
        span = parse_location_span(location)
        if span is None:
            continue
        product = bracket_value(header, "protein")
        if not product:
            product = re.sub(r"\[[^\]]*\]", " ", header).strip()
            product = re.sub(r"^\S+\s*", "", product).strip()
        cds_rows.append({"start": span[0], "stop": span[1], "product": product})
    return cds_rows


def fetch_contig_cds(contig: str, deadline: float | None) -> tuple[list[dict[str, object]], dict[str, object]]:
    ft_path = os.path.join(CACHE_DIR, "feature_table", safe_name(contig) + ".ft")
    ft_payload, ft_contact = cached_bytes(ncbi_efetch_url(contig, "ft"), ft_path, deadline=deadline, attempts=4)
    contacts: dict[str, object] = {"feature_table": ft_contact}
    if ft_payload:
        rows = parse_feature_table_cds(ft_payload.decode("utf-8", "replace"))
        if rows:
            contacts["source"] = "ncbi_feature_table"
            contacts["n_cds"] = len(rows)
            return rows, contacts
    aa_path = os.path.join(CACHE_DIR, "cds_aa", safe_name(contig) + ".faa")
    aa_payload, aa_contact = cached_bytes(ncbi_efetch_url(contig, "fasta_cds_aa"), aa_path, deadline=deadline, attempts=4)
    contacts["fasta_cds_aa"] = aa_contact
    if aa_payload:
        rows = parse_fasta_cds_aa(aa_payload.decode("utf-8", "replace"))
        if rows:
            contacts["source"] = "ncbi_fasta_cds_aa"
            contacts["n_cds"] = len(rows)
            return rows, contacts
    contacts["source"] = "unavailable"
    contacts["n_cds"] = 0
    return [], contacts


def products_in_region(cds_rows: list[dict[str, object]], start: int, stop: int) -> list[str]:
    products: list[str] = []
    for row in cds_rows:
        lo = int(row.get("start") or 0)
        hi = int(row.get("stop") or 0)
        if lo >= start and hi <= stop:
            product = str(row.get("product") or "").strip()
            if product:
                products.append(product)
    return products


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


def interval_overlaps(a_start: int, a_stop: int, b_start: int, b_stop: int) -> bool:
    return max(a_start, b_start) <= min(a_stop, b_stop)


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


def non_prophage_self_targets(
    host: str,
    contig_sequences: dict[str, str],
    prophages: list[dict[str, object]],
    spacers: set[str],
    min_match: int,
) -> list[dict[str, object]]:
    intervals_by_contig: dict[str, list[tuple[int, int]]] = {}
    for prophage in prophages:
        intervals_by_contig.setdefault(str(prophage.get("contig") or ""), []).append((int(prophage.get("start") or 0), int(prophage.get("stop") or 0)))
    events: list[dict[str, object]] = []
    seen: set[tuple[str, str, str, int, int]] = set()
    for contig, seq in contig_sequences.items():
        for spacer in sorted(spacers):
            for local_start, local_stop, strand in spacer_match_intervals(spacer, seq, min_match):
                start = local_start + 1
                stop = local_stop + 1
                if any(interval_overlaps(start, stop, lo, hi) for lo, hi in intervals_by_contig.get(contig, [])):
                    continue
                key = (host, contig, spacer, start, stop)
                if key in seen:
                    continue
                seen.add(key)
                events.append({"host": host, "contig": contig, "spacer": spacer, "start": start, "stop": stop, "strand": strand})
    return events


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


def genus_capped_weighted_median(items: list[tuple[float, str]], cap: float = 0.10) -> float:
    if not items:
        return 0.0
    by_group: dict[str, list[float]] = {}
    for value, group in items:
        by_group.setdefault(group or "unmapped", []).append(value)
    groups = sorted(by_group)
    if not groups:
        return 0.0
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


def bootstrap_weighted_median(rows: list[dict[str, object]], key: str, n: int, seed: int = 104729) -> dict[str, object]:
    values = [(float(row.get(key) or 0.0), str(row.get("genus") or "unmapped")) for row in rows]
    observed = family_weighted_median(values)
    groups = sorted({group for _value, group in values})
    if not values or not groups or n <= 0:
        return {"observed": observed, "n": 0, "p_positive": None, "ci": [observed, observed]}
    by_group: dict[str, list[float]] = {}
    for value, group in values:
        by_group.setdefault(group, []).append(value)
    rng = random.Random(seed)
    boot: list[float] = []
    for _ in range(n):
        sampled: list[tuple[float, str]] = []
        for _slot in groups:
            group = rng.choice(groups)
            sampled.extend((value, group) for value in by_group[group])
        boot.append(family_weighted_median(sampled))
    boot.sort()
    low = boot[int(0.025 * (len(boot) - 1))]
    high = boot[int(0.975 * (len(boot) - 1))]
    return {"observed": observed, "n": n, "p_positive": sum(1 for value in boot if value > 0.0) / len(boot), "ci": [low, high]}


def matched_controls(exposed: dict[str, object], candidates: list[dict[str, object]]) -> tuple[list[dict[str, object]], str]:
    tiers = [
        ("same_contig_all_bins", lambda row: row.get("contig") == exposed.get("contig") and row.get("length_bin") == exposed.get("length_bin") and row.get("gc_bin") == exposed.get("gc_bin") and row.get("orf_bin") == exposed.get("orf_bin") and row.get("integrase_present") == exposed.get("integrase_present")),
        ("all_bins", lambda row: row.get("length_bin") == exposed.get("length_bin") and row.get("gc_bin") == exposed.get("gc_bin") and row.get("orf_bin") == exposed.get("orf_bin") and row.get("integrase_present") == exposed.get("integrase_present")),
        ("length_gc_orf", lambda row: row.get("length_bin") == exposed.get("length_bin") and row.get("gc_bin") == exposed.get("gc_bin") and row.get("orf_bin") == exposed.get("orf_bin")),
        ("length_orf_integrase", lambda row: row.get("length_bin") == exposed.get("length_bin") and row.get("orf_bin") == exposed.get("orf_bin") and row.get("integrase_present") == exposed.get("integrase_present")),
        ("length_bin", lambda row: row.get("length_bin") == exposed.get("length_bin")),
        ("same_host_any_scored", lambda row: True),
    ]
    for label, predicate in tiers:
        rows = [row for row in candidates if predicate(row)]
        if rows:
            return rows, label
    return [], "none"


def estimate_rows_for_host(host_row: dict[str, object], prophages: list[dict[str, object]], exposed_ids: set[str], label: str) -> list[dict[str, object]]:
    scored = [row for row in prophages if row.get("phenotype_scored")]
    controls = [row for row in scored if str(row.get("prophage_id")) not in exposed_ids]
    rows: list[dict[str, object]] = []
    for exposed in scored:
        pid = str(exposed.get("prophage_id"))
        if pid not in exposed_ids:
            continue
        matched, match_level = matched_controls(exposed, controls)
        if not matched:
            continue
        control_cryptic = [float(row.get("cryptic_score") or 0.0) for row in matched]
        control_intact = [float(row.get("intact_like") or 0.0) for row in matched]
        r_value = float(exposed.get("cryptic_score") or 0.0) - median(control_cryptic)
        b_value = float(exposed.get("intact_like") or 0.0) - median(control_intact)
        rows.append(
            {
                "host": str(host_row.get("host") or ""),
                "genus": str(host_row.get("genus") or "unmapped"),
                "prophage_id": pid,
                "label": label,
                "R": r_value,
                "B": b_value,
                "cryptic_score": int(exposed.get("cryptic_score") or 0),
                "intact_like": int(exposed.get("intact_like") or 0),
                "control_median_cryptic_score": median(control_cryptic),
                "control_median_intact_like": median(control_intact),
                "n_matched_unexposed": len(matched),
                "match_level": match_level,
            }
        )
    return rows


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


def pyrodigal_orf_count(seq: str, prophage_id: str, df_venv: str) -> int:
    python_bin = os.path.join(df_venv, "bin", "python")
    if not os.path.exists(python_bin):
        return 0
    fna_path = os.path.join(CACHE_DIR, "pyrodigal_fna", safe_name(prophage_id) + ".fna")
    faa_path = os.path.join(CACHE_DIR, "pyrodigal_faa", safe_name(prophage_id) + ".faa")
    ensure_dir(os.path.dirname(fna_path))
    ensure_dir(os.path.dirname(faa_path))
    with open(fna_path, "w", encoding="utf-8") as handle:
        handle.write(">" + safe_name(prophage_id) + "\n")
        for index in range(0, len(seq), 80):
            handle.write(seq[index : index + 80] + "\n")
    code = r'''
import sys
import pyrodigal

fna_path, faa_path = sys.argv[1], sys.argv[2]
name = ""
chunks = []
for line in open(fna_path, "r", encoding="utf-8"):
    line = line.strip()
    if not line:
        continue
    if line.startswith(">"):
        name = line[1:].split()[0] or "seq"
    else:
        chunks.append(line.upper())
seq = "".join(chunks)
finder = pyrodigal.GeneFinder(meta=True)
genes = finder.find_genes(seq)
with open(faa_path, "w", encoding="utf-8") as out:
    genes.write_translations(out, sequence_id=name)
print(len(genes))
'''
    result = subprocess.run([python_bin, "-c", code, fna_path, faa_path], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if result.returncode != 0:
        return 0
    return parse_int(result.stdout.strip())


def make_prophage_id(host: str, contig: str, start: int, stop: int) -> str:
    return safe_name(f"{host}_{contig}_{start}_{stop}")


def prepare_host_data(
    host_data: dict[str, object],
    spacer_index: dict[str, set[str]],
    min_match: int,
    deadline: float | None,
    df_venv: str,
) -> tuple[dict[str, object], list[dict[str, object]], list[dict[str, object]], list[dict[str, object]]]:
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
            cds_rows, _cds_contact = fetch_contig_cds(str(contig), deadline)
            cds_by_contig[str(contig)] = cds_rows
        except Exception as exc:
            fetch_errors.append(f"{contig}:{type(exc).__name__}:{exc}")
    genus = "unmapped"
    for header in contig_headers.values():
        genus = derive_genus_from_defline(header)
        if genus != "unmapped":
            break
    prophages: list[dict[str, object]] = []
    for raw in raw_regions:
        contig = str(raw.get("contig") or "")
        start = int(raw.get("start") or 0)
        stop = int(raw.get("stop") or 0)
        seq = ""
        if contig in contig_sequences and start > 0 and stop <= len(contig_sequences[contig]):
            seq = contig_sequences[contig][start - 1 : stop]
        products = products_in_region(cds_by_contig.get(contig, []), start, stop)
        flinders_cds = int(raw.get("flinders_cds") or 0)
        orf_count = len(products) if products else flinders_cds
        pid = make_prophage_id(host, contig, start, stop)
        phenotype_scored = bool(products)
        if not products and seq:
            called = pyrodigal_orf_count(seq, pid, df_venv)
            if called:
                orf_count = called
        profile = module_profile(products, orf_count) if phenotype_scored else {
            "modules": {},
            "modules_present": 0,
            "cryptic_score": None,
            "intact_like": None,
            "integrase_present": False,
        }
        gc = gc_fraction(seq)
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
            "flinders_cds": flinders_cds,
            "phenotype_scored": phenotype_scored,
            "modules": profile["modules"],
            "modules_present": profile["modules_present"],
            "cryptic_score": profile["cryptic_score"],
            "intact_like": profile["intact_like"],
            "integrase_present": profile["integrase_present"],
            "length_bin": length_bin(int(raw.get("length") or (stop - start + 1))),
            "gc_bin": gc_bin(gc),
            "orf_bin": orf_bin(orf_count),
        }
        prophages.append(prophage)
    exposure_events, exposed_ids = exposure_events_for_spacers(host, host_spacers, prophages, min_match)
    self_events = non_prophage_self_targets(host, contig_sequences, prophages, host_spacers, min_match) if contig_sequences else []
    for prophage in prophages:
        prophage["exposed"] = str(prophage["prophage_id"]) in exposed_ids
    host_row = {
        "host": host,
        "genus": genus,
        "n_contigs": len(contigs),
        "n_prophages": len(prophages),
        "n_spacers": len(host_spacers),
        "n_scored_prophages": sum(1 for row in prophages if row.get("phenotype_scored")),
        "n_exposed_prophages": len(exposed_ids),
        "n_exposure_events": len(exposure_events),
        "n_nonprophage_self_target_events": len(self_events),
        "has_spacer_and_prophage": bool(host_spacers and prophages),
        "has_comparison_scope": bool(host_spacers and len(prophages) >= 2),
        "fetch_errors": fetch_errors[:5],
    }
    match_rows = estimate_rows_for_host(host_row, prophages, exposed_ids, "own")
    host_row["n_matched_exposed_prophages"] = len(match_rows)
    return host_row, prophages, exposure_events, self_events


def run_shuffled_null(
    hosts_runtime: dict[str, dict[str, object]],
    min_match: int,
    seed: int = 2601,
) -> tuple[list[dict[str, object]], dict[str, object]]:
    rng = random.Random(seed)
    rows: list[dict[str, object]] = []
    n_events = 0
    for host, runtime in sorted(hosts_runtime.items()):
        spacers = {dinucleotide_shuffle(spacer, rng) for spacer in set(runtime.get("spacers") or set())}
        prophages = list(runtime.get("prophages_with_sequence") or [])
        host_row = dict(runtime.get("host_row") or {})
        events, exposed = exposure_events_for_spacers(host, spacers, prophages, min_match)
        n_events += len(events)
        rows.extend(estimate_rows_for_host(host_row, prophages, exposed, "shuffled"))
    median_r = family_weighted_median([(float(row.get("R") or 0.0), str(row.get("genus") or "unmapped")) for row in rows])
    median_b = family_weighted_median([(float(row.get("B") or 0.0), str(row.get("genus") or "unmapped")) for row in rows])
    return rows, {"n_rows": len(rows), "n_exposure_events": n_events, "median_R": median_r, "median_B": median_b}


def run_cross_host_null(hosts_runtime: dict[str, dict[str, object]], min_match: int) -> tuple[list[dict[str, object]], dict[str, object]]:
    by_genus: dict[str, list[str]] = {}
    for host, runtime in hosts_runtime.items():
        genus = str(dict(runtime.get("host_row") or {}).get("genus") or "unmapped")
        if genus == "unmapped":
            continue
        if runtime.get("spacers"):
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
        donor = donors[0]
        donor_spacers = set(hosts_runtime[donor].get("spacers") or set())
        prophages = list(runtime.get("prophages_with_sequence") or [])
        events, exposed = exposure_events_for_spacers(host, donor_spacers, prophages, min_match)
        n_events += len(events)
        n_swaps += 1
        for row in estimate_rows_for_host(host_row, prophages, exposed, "same_genus_cross_host"):
            row["donor_host"] = donor
            rows.append(row)
    median_r = family_weighted_median([(float(row.get("R") or 0.0), str(row.get("genus") or "unmapped")) for row in rows])
    median_b = family_weighted_median([(float(row.get("B") or 0.0), str(row.get("genus") or "unmapped")) for row in rows])
    return rows, {"n_rows": len(rows), "n_exposure_events": n_events, "n_swaps": n_swaps, "median_R": median_r, "median_B": median_b}


def preflight_gates(
    n_ok_hosts: int,
    n_hosts_with_exposure: int,
    n_exposure_events: int,
    n_matched_exposed_prophages: int,
    genus_event_counts: dict[str, int],
) -> dict[str, object]:
    total_events = sum(genus_event_counts.values())
    top_genus = None
    top_fraction = 0.0
    if genus_event_counts and total_events > 0:
        top_genus, top_count = max(genus_event_counts.items(), key=lambda item: item[1])
        top_fraction = top_count / total_events
    checks = {
        "hosts_with_spacer_and_prophage_ge_500": n_ok_hosts >= 500,
        "hosts_with_exposure_ge_150": n_hosts_with_exposure >= 150,
        "exposure_events_ge_100": n_exposure_events >= 100,
        "matched_exposed_prophages_ge_50": n_matched_exposed_prophages >= 50,
        "genera_ge_20": len(genus_event_counts) >= 20,
        "single_genus_not_gt_20pct": bool(total_events > 0 and top_fraction <= 0.20),
    }
    return {
        "passed": all(checks.values()),
        "checks": checks,
        "counts": {
            "n_ok_hosts": n_ok_hosts,
            "n_hosts_with_exposure": n_hosts_with_exposure,
            "n_exposure_events": n_exposure_events,
            "n_matched_exposed_prophages": n_matched_exposed_prophages,
            "n_exposed_event_genera": len(genus_event_counts),
            "top_genus": top_genus,
            "top_genus_fraction": top_fraction,
        },
    }


def closure_preflight_gates(
    n_ok_hosts: int,
    n_exposure_events: int,
    matched_genus_counts: dict[str, int],
) -> dict[str, object]:
    matched_genera_ge1 = sum(1 for count in matched_genus_counts.values() if count >= 1)
    matched_genera_ge3 = sum(1 for count in matched_genus_counts.values() if count >= 3)
    checks = {
        "hosts_with_spacer_and_prophage_ge_500": n_ok_hosts >= 500,
        "exposure_events_ge_100": n_exposure_events >= 100,
        "matched_genera_ge1_ge_20": matched_genera_ge1 >= 20,
        "matched_genera_ge3_ge_10": matched_genera_ge3 >= 10,
    }
    return {
        "passed": all(checks.values()),
        "checks": checks,
        "counts": {
            "n_ok_hosts": n_ok_hosts,
            "n_exposure_events": n_exposure_events,
            "matched_genera_ge1": matched_genera_ge1,
            "matched_genera_ge3": matched_genera_ge3,
            "matched_genus_counts": dict(sorted(matched_genus_counts.items())),
        },
    }


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


def closure_diagnostics(
    own_rows: list[dict[str, object]],
    n_ok_hosts: int,
    n_exposure_events: int,
    cap: float = 0.10,
) -> dict[str, object]:
    r_items = [(float(row.get("R") or 0.0), str(row.get("genus") or "unmapped")) for row in own_rows]
    b_items = [(float(row.get("B") or 0.0), str(row.get("genus") or "unmapped")) for row in own_rows]
    matched_genus_counts: dict[str, int] = {}
    for row in own_rows:
        genus = str(row.get("genus") or "unmapped")
        matched_genus_counts[genus] = matched_genus_counts.get(genus, 0) + 1
    median_r = genus_capped_weighted_median(r_items, cap)
    median_b = genus_capped_weighted_median(b_items, cap)
    full_sign = sign(median_r)
    dropped: dict[str, float] = {}
    for genus in sorted(matched_genus_counts):
        dropped_items = [(value, group) for value, group in r_items if group != genus]
        dropped[genus] = genus_capped_weighted_median(dropped_items, cap)
    leave_one_stable = bool(dropped) and all(sign(value) == full_sign for value in dropped.values())
    non_klebsiella_rows = [
        row
        for row in own_rows
        if "klebsiella" not in str(row.get("genus") or "unmapped").lower()
    ]
    klebsiella_r = genus_capped_weighted_median(
        [(float(row.get("R") or 0.0), str(row.get("genus") or "unmapped")) for row in non_klebsiella_rows],
        cap,
    )
    klebsiella_b = genus_capped_weighted_median(
        [(float(row.get("B") or 0.0), str(row.get("genus") or "unmapped")) for row in non_klebsiella_rows],
        cap,
    )
    klebsiella_not_reversed = bool(
        non_klebsiella_rows
        and signs_not_reversed(median_r, klebsiella_r)
        and signs_not_reversed(median_b, klebsiella_b)
    )
    preflight = closure_preflight_gates(n_ok_hosts, n_exposure_events, matched_genus_counts)
    return {
        "genus_cap": cap,
        "genus_capped_median_R": median_r,
        "genus_capped_median_B": median_b,
        "matched_genera_ge1": preflight["counts"]["matched_genera_ge1"],  # type: ignore[index]
        "matched_genera_ge3": preflight["counts"]["matched_genera_ge3"],  # type: ignore[index]
        "matched_genus_counts": dict(sorted(matched_genus_counts.items())),
        "leave_one_genus_out_stable": leave_one_stable,
        "per_genus_dropped_median_R": dropped,
        "klebsiella_excluded_median_R": klebsiella_r,
        "klebsiella_excluded_median_B": klebsiella_b,
        "klebsiella_excluded_not_reversed": klebsiella_not_reversed,
        "closure_preflight": preflight,
    }


def verdict_from_summary(summary: dict[str, object]) -> str:
    preflight = dict(summary.get("preflight") or {})
    if not preflight.get("passed"):
        return "data_gate_failed"
    median_r = float(summary.get("median_R") or 0.0)
    median_b = float(summary.get("median_B") or 0.0)
    n2 = dict(summary.get("N2_shuffled_spacer") or {})
    n3 = dict(summary.get("N3_same_genus_cross_host") or {})
    n5 = dict(summary.get("N5_nonprophage_self_target") or {})
    n2_beats = bool(n2.get("true_spacers_beat_shuffled"))
    n3_own_beats = bool(n3.get("own_beats_cross_host"))
    n3_retains = bool(n3.get("cross_host_retains_signal"))
    n5_clean = bool(n5.get("clean"))
    if median_r < 0.0 and median_b > 0.0:
        return "anti"
    if n3_retains or (median_r > 0.0 and median_b < 0.0 and not n3_own_beats):
        return "ecology_dominated"
    if median_r > 0.0 and median_b < 0.0 and n2_beats and n3_own_beats and n5_clean:
        if summary.get("closure_mode"):
            closure = dict(summary.get("closure") or {})
            if not (closure.get("leave_one_genus_out_stable") and closure.get("klebsiella_excluded_not_reversed")):
                return "refuted"
        return "supportive"
    return "refuted"


def summarize(
    manifest_meta: dict[str, object],
    spacer_meta: dict[str, object],
    flinders_meta: dict[str, object],
    per_host: list[dict[str, object]],
    own_rows: list[dict[str, object]],
    shuffled_rows: list[dict[str, object]],
    shuffled_summary: dict[str, object],
    cross_rows: list[dict[str, object]],
    cross_summary: dict[str, object],
    n_self_events: int,
    bootstrap_n: int,
    closure_mode: bool = False,
) -> dict[str, object]:
    n_exposure_events = sum(int(row.get("n_exposure_events") or 0) for row in per_host)
    n_ok_hosts = sum(1 for row in per_host if row.get("has_spacer_and_prophage"))
    n_hosts_with_exposure = sum(1 for row in per_host if int(row.get("n_exposure_events") or 0) > 0)
    genus_event_counts: dict[str, int] = {}
    for row in per_host:
        count = int(row.get("n_exposure_events") or 0)
        if count <= 0:
            continue
        genus = str(row.get("genus") or "unmapped")
        genus_event_counts[genus] = genus_event_counts.get(genus, 0) + count
    median_r = family_weighted_median([(float(row.get("R") or 0.0), str(row.get("genus") or "unmapped")) for row in own_rows])
    median_b = family_weighted_median([(float(row.get("B") or 0.0), str(row.get("genus") or "unmapped")) for row in own_rows])
    closure = closure_diagnostics(own_rows, n_ok_hosts, n_exposure_events) if closure_mode else None
    if closure_mode and closure is not None:
        median_r = float(closure.get("genus_capped_median_R") or 0.0)
        median_b = float(closure.get("genus_capped_median_B") or 0.0)
    shuffled_r = float(shuffled_summary.get("median_R") or 0.0)
    cross_r = float(cross_summary.get("median_R") or 0.0)
    cross_b = float(cross_summary.get("median_B") or 0.0)
    n5_ratio = n_self_events / max(1, n_exposure_events)
    preflight = preflight_gates(n_ok_hosts, n_hosts_with_exposure, n_exposure_events, len(own_rows), genus_event_counts)
    if closure_mode and closure is not None:
        preflight = dict(closure.get("closure_preflight") or {})
    summary: dict[str, object] = {
        "n_hosts": len(per_host),
        "n_ok_hosts": n_ok_hosts,
        "n_exposure_events": n_exposure_events,
        "n_matched_exposed_prophages": len(own_rows),
        "input": {"manifest": manifest_meta, "spacers": spacer_meta, "flinders": flinders_meta},
        "preflight": preflight,
        "median_R": median_r,
        "median_B": median_b,
        "N1_same_host_unexposed": {"n_rows": len(own_rows), "median_R": median_r, "median_B": median_b},
        "N2_shuffled_spacer": {
            **shuffled_summary,
            "true_minus_shuffled_R": median_r - shuffled_r,
            "true_spacers_beat_shuffled": bool(median_r > shuffled_r),
        },
        "N3_same_genus_cross_host": {
            **cross_summary,
            "S": median_r - cross_r,
            "own_beats_cross_host": bool(median_r > cross_r),
            "cross_host_retains_signal": bool(cross_r > 0.0 and cross_b < 0.0),
        },
        "N4_low_evidence_orphan_carrier": {
            "available": False,
            "reason": "CRISPRCasdb spacer FASTA does not distinguish linked active carriers from orphan or low-evidence arrays.",
        },
        "N5_nonprophage_self_target": {
            "n_nonprophage_self_target_events": n_self_events,
            "self_to_prophage_event_ratio": n5_ratio,
            "clean": bool(n_self_events <= max(10, n_exposure_events)),
        },
        "bootstrap": {
            "R": bootstrap_weighted_median(own_rows, "R", bootstrap_n),
            "B": bootstrap_weighted_median(own_rows, "B", bootstrap_n),
        },
    }
    if closure_mode and closure is not None:
        summary["closure_mode"] = True
        summary["closure"] = closure
    summary["verdict"] = verdict_from_summary(summary)
    return summary


def run_pipeline() -> dict[str, object]:
    host_limit = parse_host_limit()
    min_match = env_int("CC_MIN_SPACER_MATCH", 28)
    bootstrap_n = env_int("CC_BOOTSTRAP_N", 2000)
    closure_mode = os.environ.get("CC_CLOSURE_MODE", "").strip() == "1"
    manifest_path = env_path("CC_MANIFEST", DEFAULT_MANIFEST)
    spacer_path = env_path("CC_SPACER_FSA", DEFAULT_SPACER_FSA)
    flinders_path = env_path("CC_FLINDERS_BULK", DEFAULT_FLINDERS_BULK)
    df_venv = env_path("CC_DF_VENV", DEFAULT_DF_VENV)
    deadline = deadline_from_env()
    manifest_contigs, manifest_meta = load_manifest(manifest_path, host_limit)
    manifest_set = set(manifest_contigs)
    spacer_index, spacer_meta = load_spacer_index(spacer_path, manifest_set)
    hosts, flinders_meta = load_flinders_regions(flinders_path, manifest_set)
    per_host: list[dict[str, object]] = []
    per_prophage: list[dict[str, object]] = []
    own_rows: list[dict[str, object]] = []
    all_events: list[dict[str, object]] = []
    self_events: list[dict[str, object]] = []
    hosts_runtime: dict[str, dict[str, object]] = {}
    for host in sorted(hosts):
        host_data = hosts[host]
        host_spacers: set[str] = set()
        for contig in list(host_data.get("contigs") or []):
            host_spacers.update(spacer_index.get(str(contig), set()))
        host_row, prophages, exposure_events, host_self_events = prepare_host_data(host_data, spacer_index, min_match, deadline, df_venv)
        per_host.append(host_row)
        output_prophages = []
        for row in prophages:
            clean_row = dict(row)
            clean_row.pop("sequence", None)
            output_prophages.append(clean_row)
        per_prophage.extend(output_prophages)
        all_events.extend(exposure_events)
        self_events.extend(host_self_events)
        own_rows.extend(estimate_rows_for_host(host_row, prophages, {str(row["prophage_id"]) for row in prophages if row.get("exposed")}, "own"))
        hosts_runtime[host] = {"host_row": host_row, "prophages_with_sequence": prophages, "spacers": host_spacers}
    shuffled_rows, shuffled_summary = run_shuffled_null(hosts_runtime, min_match)
    cross_rows, cross_summary = run_cross_host_null(hosts_runtime, min_match)
    summary = summarize(
        manifest_meta,
        spacer_meta,
        flinders_meta,
        per_host,
        own_rows,
        shuffled_rows,
        shuffled_summary,
        cross_rows,
        cross_summary,
        len(self_events),
        bootstrap_n,
        closure_mode,
    )
    return {
        "summary": summary,
        "per_host": per_host,
        "per_prophage": per_prophage,
        "matched_rows": own_rows,
        "null_rows": {"N2_shuffled": shuffled_rows, "N3_same_genus_cross_host": cross_rows},
        "exposure_events": all_events,
    }


def assert_close(actual: float, expected: float, eps: float = 1e-9) -> None:
    if abs(actual - expected) > eps:
        raise AssertionError(f"{actual} != {expected}")


def run_selftest() -> dict[str, object]:
    test_spacer = "AAAACCCCGGGGTTTTAAAACCCCGGGG"
    tiny_fsa = ">ctgA+ctgB\n" + test_spacer + "\n>ctgC\n" + "TTTTCCCCAAAAGGGGTTTTCCCCAAAAGGGG\n"
    index = build_spacer_index_from_fasta_text(tiny_fsa, {"ctgA", "ctgB"})
    spacer = test_spacer
    if index != {"ctgA": {spacer}, "ctgB": {spacer}}:
        raise AssertionError("spacer inverted index failed")
    target = "GGG" + spacer + "CCC"
    matches = spacer_match_intervals(spacer, target, 28)
    if not any(start == 3 and stop == 30 and strand == "+" for start, stop, strand in matches):
        raise AssertionError("plus-strand spacer match failed")
    rc_target = "GGG" + reverse_complement(spacer) + "CCC"
    rc_matches = spacer_match_intervals(spacer, rc_target, 28)
    if not any(start == 3 and strand == "-" for start, _stop, strand in rc_matches):
        raise AssertionError("reverse-complement spacer match failed")
    products = ["large terminase", "major capsid protein", "tail tape measure", "holin", "integrase"]
    profile = module_profile(products, 30)
    if profile["modules_present"] != 5 or profile["cryptic_score"] != 0 or profile["intact_like"] != 1:
        raise AssertionError("intact phenotype failed")
    cryptic = module_profile(["hypothetical protein"], 8)
    if cryptic["modules_present"] != 0 or cryptic["cryptic_score"] != 5 or cryptic["intact_like"] != 0:
        raise AssertionError("cryptic phenotype failed")
    host_row = {"host": "h1", "genus": "Genus"}
    prophages = [
        {"prophage_id": "pE", "contig": "c1", "phenotype_scored": True, "cryptic_score": 5, "intact_like": 0, "length_bin": "A", "gc_bin": "B", "orf_bin": "C", "integrase_present": False},
        {"prophage_id": "pU1", "contig": "c1", "phenotype_scored": True, "cryptic_score": 1, "intact_like": 1, "length_bin": "A", "gc_bin": "B", "orf_bin": "C", "integrase_present": False},
        {"prophage_id": "pU2", "contig": "c1", "phenotype_scored": True, "cryptic_score": 3, "intact_like": 1, "length_bin": "A", "gc_bin": "B", "orf_bin": "C", "integrase_present": False},
    ]
    rows = estimate_rows_for_host(host_row, prophages, {"pE"}, "own")
    if len(rows) != 1:
        raise AssertionError("R/B estimator row count failed")
    assert_close(float(rows[0]["R"]), 3.0)
    assert_close(float(rows[0]["B"]), -1.0)
    gates = preflight_gates(500, 150, 100, 50, {f"G{idx}": 5 for idx in range(20)})
    if not gates["passed"]:
        raise AssertionError("preflight gate failed")
    summary = {
        "preflight": gates,
        "median_R": 1.0,
        "median_B": -1.0,
        "N2_shuffled_spacer": {"true_spacers_beat_shuffled": True},
        "N3_same_genus_cross_host": {"own_beats_cross_host": True, "cross_host_retains_signal": False},
        "N5_nonprophage_self_target": {"clean": True},
    }
    if verdict_from_summary(summary) != "supportive":
        raise AssertionError("supportive verdict failed")
    failed = dict(summary)
    failed["preflight"] = preflight_gates(1, 1, 1, 1, {"G": 1})
    if verdict_from_summary(failed) != "data_gate_failed":
        raise AssertionError("data gate verdict failed")
    anti = dict(summary)
    anti["median_R"] = -1.0
    anti["median_B"] = 1.0
    if verdict_from_summary(anti) != "anti":
        raise AssertionError("anti verdict failed")
    dominated = dict(summary)
    dominated["N3_same_genus_cross_host"] = {"own_beats_cross_host": False, "cross_host_retains_signal": True}
    if verdict_from_summary(dominated) != "ecology_dominated":
        raise AssertionError("ecology verdict failed")
    capped_items = [(0.0, "Dominant") for _idx in range(90)] + [(10.0, f"G{idx}") for idx in range(10)]
    assert_close(genus_capped_weighted_median(capped_items), 10.0)
    closure_rows: list[dict[str, object]] = []
    for idx in range(20):
        count = 3 if idx < 10 else 1
        genus = "Klebsiella" if idx == 0 else f"CG{idx}"
        for slot in range(count):
            closure_rows.append({"genus": genus, "R": 1.0 + idx / 100.0 + slot / 1000.0, "B": -1.0})
    closure = closure_diagnostics(closure_rows, 500, 100)
    closure_summary = {
        "closure_mode": True,
        "closure": closure,
        "preflight": closure["closure_preflight"],
        "median_R": closure["genus_capped_median_R"],
        "median_B": closure["genus_capped_median_B"],
        "N2_shuffled_spacer": {"true_spacers_beat_shuffled": True},
        "N3_same_genus_cross_host": {"own_beats_cross_host": True, "cross_host_retains_signal": False},
        "N5_nonprophage_self_target": {"clean": True},
    }
    if verdict_from_summary(closure_summary) != "supportive":
        raise AssertionError("closure supportive verdict failed")
    klebsiella_reversal = dict(closure)
    klebsiella_reversal["klebsiella_excluded_median_R"] = -1.0
    klebsiella_reversal["klebsiella_excluded_not_reversed"] = False
    reversal_summary = dict(closure_summary)
    reversal_summary["closure"] = klebsiella_reversal
    if verdict_from_summary(reversal_summary) == "supportive":
        raise AssertionError("closure Klebsiella reversal guard failed")
    sparse_rows: list[dict[str, object]] = []
    for idx in range(20):
        count = 3 if idx < 9 else 1
        for _slot in range(count):
            sparse_rows.append({"genus": f"SG{idx}", "R": 1.0, "B": -1.0})
    sparse_closure = closure_diagnostics(sparse_rows, 500, 100)
    sparse_summary = dict(closure_summary)
    sparse_summary["closure"] = sparse_closure
    sparse_summary["preflight"] = sparse_closure["closure_preflight"]
    sparse_summary["median_R"] = sparse_closure["genus_capped_median_R"]
    sparse_summary["median_B"] = sparse_closure["genus_capped_median_B"]
    if verdict_from_summary(sparse_summary) != "data_gate_failed":
        raise AssertionError("closure matched ge3 data gate failed")
    return {
        "ok": True,
        "tested": [
            "spacer_inverted_index",
            "exact_spacer_match_both_strands",
            "module_crypticness",
            "R_B_estimator",
            "preflight_gate",
            "verdict",
            "closure_mode",
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

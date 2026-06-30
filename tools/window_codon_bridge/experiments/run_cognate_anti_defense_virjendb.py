#!/usr/bin/env python3
"""VirJenDB cognate anti-defense payload enrichment experiment."""
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
CACHE_DIR = os.path.join(SYNCED_DIR, "cognate_anti_defense_virjendb")
REF_DIR = os.path.join(REPO_ROOT, "_q2ref")
DEFAULT_MANIFEST = os.path.join(REF_DIR, "virjendb_sample.tsv")
SEED_MAPPING_PATH = os.path.join(REF_DIR, "seed_family_mapping.tsv")
DBAPIS_URL = "https://pro.unl.edu/dbAPIS/download_file.php?file=dbAPIS.hmm"
VIRJENDB_SEQUENCE_URL = "https://api2.virjendb.org/v2/sequence"
NCBI_EFETCH_URL = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi"
DEFAULT_DF_VENV = (
    "/private/tmp/claude-501/-Users-lexa-Desktop-lexa-omega-newmath/"
    "440f01d8-6db8-475a-aa59-e73a67b5f7b8/scratchpad/sshx_gate_recal/df_venv"
)
DEFAULT_CLASSES = ("RM", "BREX", "GABIJA", "THOERIS", "TA")
AA_ALPHABET = set("ACDEFGHIKLMNPQRSTVWYXBZJUO")
USER_AGENT = "virjendb-cognate-anti-defense"
FETCH_TIMEOUT = 120
NCBI_DELAY_SECONDS = 0.34
PSEUDOCOUNT = 0.5


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


def parse_host_limit() -> int | None:
    value = env_int("CAD_HOST_LIMIT", 0)
    return value if value > 0 else None


def deadline_from_env() -> float | None:
    seconds = env_int("CAD_FETCH_DEADLINE_SECONDS", 7200)
    return time.monotonic() + seconds if seconds > 0 else None


def deadline_expired(deadline: float | None) -> bool:
    return deadline is not None and time.monotonic() >= deadline


def fetch_bytes(
    url: str,
    deadline: float | None = None,
    attempts: int = 4,
    timeout: int = FETCH_TIMEOUT,
    data: bytes | None = None,
    headers: dict[str, str] | None = None,
) -> tuple[bytes, dict[str, object]]:
    merged_headers = {"User-Agent": USER_AGENT}
    if headers:
        merged_headers.update(headers)
    last_error = "fetch_failed"
    for attempt in range(1, attempts + 1):
        if deadline_expired(deadline):
            return b"", {"url": url, "ok": False, "error": "fetch_deadline_exceeded", "attempts": attempt - 1}
        request = urllib.request.Request(url, data=data, headers=merged_headers)
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
    if re.search(r"\bta\b", compact) or "toxin antitoxin" in compact:
        return "TA"
    if "restriction modification" in compact or re.search(r"\br m\b", compact):
        return "RM"
    if re.search(r"\brestriction\b", compact) and "modification" in compact:
        return "RM"
    if text.upper() in DEFAULT_CLASSES:
        return text.upper()
    return None


def parse_class_list() -> list[str]:
    raw = os.environ.get("CAD_CLASSES", ",".join(DEFAULT_CLASSES))
    classes: list[str] = []
    for item in raw.split(","):
        label = normalize_class(item) or item.strip().upper()
        if label and label not in classes:
            classes.append(label)
    return classes or list(DEFAULT_CLASSES)


def parse_manifest_text(text: str, host_limit: int | None = None) -> tuple[list[dict[str, object]], dict[str, object]]:
    rows: list[dict[str, object]] = []
    reader = csv.DictReader(text.splitlines(), delimiter="\t")
    required = {"host_assembly", "genus", "prophage_vjids"}
    missing = required.difference(reader.fieldnames or [])
    if missing:
        raise RuntimeError(f"manifest missing columns: {sorted(missing)}")
    for row in reader:
        host = str(row.get("host_assembly") or "").strip()
        genus = str(row.get("genus") or "").strip() or "unmapped"
        vjids = [item.strip() for item in str(row.get("prophage_vjids") or "").split(";") if item.strip()]
        if not host or not vjids:
            continue
        rows.append(
            {
                "host_assembly": host,
                "genus": genus,
                "n_prophages": int(row.get("n_prophages") or len(vjids)),
                "prophage_vjids": vjids,
            }
        )
        if host_limit is not None and len(rows) >= host_limit:
            break
    return rows, {"n_manifest_rows": len(rows), "host_limit": host_limit}


def load_manifest(path: str, host_limit: int | None) -> tuple[list[dict[str, object]], dict[str, object]]:
    if not os.path.exists(path):
        raise RuntimeError(f"missing manifest: {path}")
    with open(path, "r", encoding="utf-8", newline="") as handle:
        rows, meta = parse_manifest_text(handle.read(), host_limit)
    meta["path"] = path
    return rows, meta


def sanitize_fasta_text(text: str) -> tuple[str, dict[str, object]]:
    records: list[tuple[str, str]] = []
    header = ""
    chunks: list[str] = []
    removed = 0
    for line in text.splitlines():
        if line.startswith(">"):
            if header:
                records.append((header, "".join(chunks)))
            token = line[1:].strip().split()[0] if line[1:].strip() else "seq"
            if token.startswith("lcl|"):
                token = token[4:]
            header = token.replace("|", "_")
            chunks = []
        else:
            upper = line.strip().upper()
            clean = "".join(char for char in upper if char in AA_ALPHABET)
            removed += len(upper) - len(clean)
            chunks.append(clean)
    if header:
        records.append((header, "".join(chunks)))
    output: list[str] = []
    written = 0
    for name, seq in records:
        if not seq:
            continue
        output.append(">" + name)
        output.extend(seq[index : index + 60] for index in range(0, len(seq), 60))
        written += 1
    return "\n".join(output) + ("\n" if output else ""), {"n_records": written, "removed_chars": removed}


def count_fasta_records(path: str) -> int:
    if not os.path.exists(path):
        return 0
    count = 0
    with open(path, "r", encoding="utf-8", errors="replace") as handle:
        for line in handle:
            if line.startswith(">"):
                count += 1
    return count


def load_seed_family_map(classes: list[str]) -> tuple[dict[str, str], dict[str, object]]:
    if not os.path.exists(SEED_MAPPING_PATH):
        raise RuntimeError(f"missing seed family mapping: {SEED_MAPPING_PATH}")
    family_to_class: dict[str, str] = {}
    raw_families: set[str] = set()
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
                raw_families.add(family)
            if family and label in classes:
                family_to_class[family] = label
                counts[label] = counts.get(label, 0) + 1
    return family_to_class, {
        "path": SEED_MAPPING_PATH,
        "n_mapped_families": len(family_to_class),
        "n_raw_families": len(raw_families),
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
            family = parts[2]
            try:
                evalue = float(parts[4])
                score = float(parts[5])
            except ValueError:
                continue
            previous = hits.get(target)
            if previous is None or score > float(previous.get("score") or -1e300):
                hits[target] = {"family": family, "evalue": evalue, "score": score}
    return hits


def run_hmmsearch(fasta_path: str, tblout_path: str, hmm_path: str, hmmsearch_bin: str, evalue: str) -> dict[str, object]:
    ensure_dir(os.path.dirname(tblout_path))
    if not os.path.exists(fasta_path) or os.path.getsize(fasta_path) == 0:
        open(tblout_path, "w", encoding="utf-8").close()
        return {"skipped": True, "reason": "empty_fasta", "tblout": tblout_path}
    first_cmd = [hmmsearch_bin, "--tblout", tblout_path, "--noali", "--cut_ga", hmm_path, fasta_path]
    first = subprocess.run(first_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if first.returncode == 0:
        return {"ok": True, "mode": "cut_ga", "tblout": tblout_path, "stderr_tail": first.stderr[-800:]}
    second_cmd = [hmmsearch_bin, "--tblout", tblout_path, "--noali", "-E", evalue, hmm_path, fasta_path]
    second = subprocess.run(second_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if second.returncode != 0:
        raise RuntimeError("hmmsearch failed: " + (second.stderr[-1000:] or first.stderr[-1000:]))
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
        label = family_to_class.get(str(hit.get("family") or ""))
        if label:
            counts[label] = counts.get(label, 0) + 1
        else:
            non_mappable += 1
    return counts, non_mappable


def y_score(anti_count: int, load: int) -> float:
    return math.log2((anti_count + PSEUDOCOUNT) / (load + 1.0))


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


def bootstrap_group_weighted_median(rows: list[dict[str, object]], key: str, n: int, seed: int = 104729) -> dict[str, object]:
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


def fetch_virjendb_sequences(vjids: list[str], deadline: float | None) -> tuple[dict[str, str], list[dict[str, object]]]:
    sequences: dict[str, str] = {}
    contacts: list[dict[str, object]] = []
    for index in range(0, len(vjids), 100):
        chunk = vjids[index : index + 100]
        body = json.dumps({"virjendb_accessions": chunk}).encode("utf-8")
        payload, contact = fetch_bytes(
            VIRJENDB_SEQUENCE_URL,
            deadline=deadline,
            attempts=4,
            timeout=180,
            data=body,
            headers={"Content-Type": "application/json"},
        )
        contacts.append(contact)
        if not payload:
            raise RuntimeError("VirJenDB sequence fetch failed")
        decoded = json.loads(payload.decode("utf-8", "replace"))
        if not isinstance(decoded, dict):
            raise RuntimeError("VirJenDB sequence response was not a JSON object")
        for key, value in decoded.items():
            seq = re.sub(r"[^A-Za-z]", "", str(value)).upper()
            if seq:
                sequences[str(key)] = seq
    return sequences, contacts


def write_nt_fasta(sequences: dict[str, str], path: str) -> None:
    ensure_dir(os.path.dirname(path))
    with open(path, "w", encoding="utf-8") as handle:
        for name, seq in sorted(sequences.items()):
            handle.write(">" + safe_name(name) + "\n")
            for index in range(0, len(seq), 80):
                handle.write(seq[index : index + 80] + "\n")


def translate_prophages_with_pyrodigal(fna_path: str, faa_path: str, df_venv: str) -> dict[str, object]:
    ensure_dir(os.path.dirname(faa_path))
    python_bin = os.path.join(df_venv, "bin", "python")
    code = r'''
import re
import sys
import pyrodigal

fna_path, faa_path = sys.argv[1], sys.argv[2]
records = []
name = ""
chunks = []
for line in open(fna_path, "r", encoding="utf-8"):
    line = line.strip()
    if not line:
        continue
    if line.startswith(">"):
        if name:
            records.append((name, "".join(chunks)))
        name = re.sub(r"[^A-Za-z0-9_.-]+", "_", line[1:].split()[0]) or "seq"
        chunks = []
    else:
        chunks.append(re.sub(r"[^ACGTUNacgtun]", "", line).upper())
if name:
    records.append((name, "".join(chunks)))
finder = pyrodigal.GeneFinder(meta=True)
with open(faa_path, "w", encoding="utf-8") as out:
    for name, seq in records:
        if not seq:
            continue
        genes = finder.find_genes(seq)
        genes.write_translations(out, sequence_id=name)
'''
    result = subprocess.run([python_bin, "-c", code, fna_path, faa_path], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if result.returncode != 0:
        raise RuntimeError("pyrodigal translation failed: " + result.stderr[-1000:])
    return {"ok": True, "protein_count": count_fasta_records(faa_path), "stderr_tail": result.stderr[-800:]}


def prepare_prophage_faa(host: str, vjids: list[str], df_venv: str, deadline: float | None) -> tuple[str, dict[str, object]]:
    faa_path = os.path.join(CACHE_DIR, "prophage_faa", safe_name(host) + ".faa")
    if os.path.exists(faa_path) and os.path.getsize(faa_path) > 0:
        return faa_path, {"on_disk_cache_hit": True, "protein_count": count_fasta_records(faa_path)}
    fna_path = os.path.join(CACHE_DIR, "prophage_fna", safe_name(host) + ".fna")
    sequences, contacts = fetch_virjendb_sequences(vjids, deadline)
    write_nt_fasta(sequences, fna_path)
    translation = translate_prophages_with_pyrodigal(fna_path, faa_path, df_venv)
    return faa_path, {"on_disk_cache_hit": False, "n_sequences": len(sequences), "contacts": contacts, "translation": translation}


def normalize_df_type(raw: str) -> str | None:
    """Map a DefenseFinder `type` (e.g. RM_Type_I, BREX, Gabija, Thoeris) to a canonical
    class label aligned with the dbAPIS cognate map {RM, BREX, GABIJA, THOERIS, TA}.
    DefenseFinder's vocabulary differs from the dbAPIS inhibited_defense_system strings,
    so the carrier needs its own normalizer."""
    t = raw.strip().lower()
    if not t:
        return None
    if t.startswith("rm") or "restriction" in t:
        return "RM"
    if t.startswith("brex"):
        return "BREX"
    if "gabija" in t:
        return "GABIJA"
    if "thoeris" in t:
        return "THOERIS"
    return None


def fetch_assembly_protein_ftp(accession: str, deadline: float | None) -> tuple[str, dict[str, object]]:
    """For a GCA_/GCF_ assembly accession, fetch the annotated proteome from NCBI FTP
    (<ASM>_protein.faa.gz). efetch db=nuccore cannot resolve assembly accessions."""
    m = re.match(r"(GC[AF])_(\d{3})(\d{3})(\d{3})", accession)
    if not m:
        raise RuntimeError("not an assembly accession: " + accession)
    gc, a, b, c = m.groups()
    base = f"https://ftp.ncbi.nlm.nih.gov/genomes/all/{gc}/{a}/{b}/{c}/"
    listing, contact = fetch_bytes(base, deadline=deadline, attempts=4, timeout=120)
    if not listing:
        raise RuntimeError("assembly FTP dir listing failed: " + base)
    text = listing.decode("utf-8", "replace")
    asm = None
    for token in re.findall(re.escape(accession) + r"_[^\"/<>]+", text):
        asm = token
        break
    if not asm:
        raise RuntimeError("assembly dir not found under " + base)
    url = f"{base}{asm}/{asm}_protein.faa.gz"
    payload, c2 = fetch_bytes(url, deadline=deadline, attempts=4, timeout=180)
    if not payload:
        raise RuntimeError("assembly protein.faa.gz fetch failed: " + url)
    try:
        raw = gzip.decompress(payload).decode("utf-8", "replace")
    except OSError as exc:
        raise RuntimeError("protein.faa.gz decompress failed: " + str(exc))
    meta = dict(c2)
    meta["assembly_dir"] = asm
    meta["source"] = "ncbi_ftp_protein_faa"
    return raw, meta


def prepare_host_faa(host: str, deadline: float | None) -> tuple[str, dict[str, object]]:
    faa_path = os.path.join(CACHE_DIR, "host_faa", safe_name(host) + ".faa")
    if os.path.exists(faa_path) and os.path.getsize(faa_path) > 0:
        return faa_path, {"on_disk_cache_hit": True, "protein_count": count_fasta_records(faa_path)}
    if re.match(r"GC[AF]_\d+\.\d+", host):
        raw_text, contact = fetch_assembly_protein_ftp(host, deadline=deadline)
    else:
        query = urllib.parse.urlencode({"db": "nuccore", "id": host, "rettype": "fasta_cds_aa", "retmode": "text"})
        url = NCBI_EFETCH_URL + "?" + query
        payload, contact = fetch_bytes(url, deadline=deadline, attempts=4, timeout=180)
        if not payload:
            raise RuntimeError("NCBI efetch fasta_cds_aa failed")
        raw_text = payload.decode("utf-8", "replace")
    clean, sanitize_meta = sanitize_fasta_text(raw_text)
    ensure_dir(os.path.dirname(faa_path))
    with open(faa_path, "w", encoding="utf-8") as handle:
        handle.write(clean)
    meta = dict(contact)
    meta.update(sanitize_meta)
    meta["protein_count"] = count_fasta_records(faa_path)
    return faa_path, meta


def run_defense_finder(host_faa: str, host: str, df_venv: str) -> tuple[set[str], dict[str, object]]:
    outdir = os.path.join(CACHE_DIR, "defense_finder", safe_name(host))
    ensure_dir(outdir)
    systems_files = [os.path.join(outdir, name) for name in os.listdir(outdir) if name.endswith("_defense_finder_systems.tsv")]
    contact: dict[str, object] = {"outdir": outdir, "on_disk_cache_hit": bool(systems_files)}
    if not systems_files:
        df_bin = os.path.join(df_venv, "bin", "defense-finder")
        cmd = [df_bin, "run", "-o", outdir, "--db-type", "ordered_replicon", host_faa]
        result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        contact.update({"returncode": result.returncode, "stdout_tail": result.stdout[-800:], "stderr_tail": result.stderr[-1200:]})
        if result.returncode != 0:
            raise RuntimeError("defense-finder failed: " + result.stderr[-1000:])
        systems_files = [os.path.join(outdir, name) for name in os.listdir(outdir) if name.endswith("_defense_finder_systems.tsv")]
    classes: set[str] = set()
    raw_types: list[str] = []
    for path in systems_files:
        with open(path, "r", encoding="utf-8", errors="replace", newline="") as handle:
            reader = csv.DictReader(handle, delimiter="\t")
            for row in reader:
                raw = str(row.get("type") or "").strip()
                raw_types.append(raw)
                label = normalize_df_type(raw)
                if label:
                    classes.add(label)
    contact.update({"systems_files": systems_files, "raw_types": sorted(set(raw_types)), "carrier_classes": sorted(classes)})
    return classes, contact


def host_hmm_counts(
    fasta_path: str,
    host: str,
    kind: str,
    hmm_path: str,
    hmmsearch_bin: str,
    evalue: str,
    family_to_class: dict[str, str],
) -> tuple[dict[str, int], int, dict[str, object]]:
    tblout = os.path.join(CACHE_DIR, "hmm_tblout", kind, safe_name(host) + ".tblout")
    run_meta = run_hmmsearch(fasta_path, tblout, hmm_path, hmmsearch_bin, evalue)
    hits = parse_hmm_tblout(tblout)
    counts, non_mappable = count_hits_by_class(hits, family_to_class)
    run_meta.update({"n_hits": len(hits), "non_mappable_hits": non_mappable})
    return counts, non_mappable, run_meta


def prepare_host_row(
    manifest_row: dict[str, object],
    classes: list[str],
    family_to_class: dict[str, str],
    hmm_path: str,
    df_venv: str,
    deadline: float | None,
) -> dict[str, object]:
    host = str(manifest_row["host_assembly"])
    genus = str(manifest_row["genus"])
    vjids = list(manifest_row["prophage_vjids"])
    hmmsearch_bin = os.environ.get("CAD_HMMSEARCH", "hmmsearch")
    evalue = os.environ.get("CAD_EVALUE", "1e-5")
    prophage_faa, prophage_meta = prepare_prophage_faa(host, vjids, df_venv, deadline)
    host_faa, host_meta = prepare_host_faa(host, deadline)
    carrier_classes, defense_meta = run_defense_finder(host_faa, host, df_venv)
    prophage_counts, prophage_non_mappable, prophage_hmm = host_hmm_counts(
        prophage_faa, host, "prophage", hmm_path, hmmsearch_bin, evalue, family_to_class
    )
    chromosome_counts, chromosome_non_mappable, chromosome_hmm = host_hmm_counts(
        host_faa, host, "chromosome", hmm_path, hmmsearch_bin, evalue, family_to_class
    )
    return {
        "host": host,
        "genus": genus,
        "ok": True,
        "n_prophages": int(manifest_row.get("n_prophages") or len(vjids)),
        "prophage_vjids": vjids,
        "prophage_protein_count": count_fasta_records(prophage_faa),
        "chromosome_protein_count": count_fasta_records(host_faa),
        "carrier_classes": sorted(class_name for class_name in carrier_classes if class_name in classes),
        "prophage_counts": {class_name: prophage_counts.get(class_name, 0) for class_name in classes},
        "chromosome_counts": {class_name: chromosome_counts.get(class_name, 0) for class_name in classes},
        "non_mappable_prophage_hits": prophage_non_mappable,
        "non_mappable_chromosome_hits": chromosome_non_mappable,
        "contacts": {
            "prophage": prophage_meta,
            "host_faa": host_meta,
            "defense_finder": defense_meta,
            "hmmsearch": {"prophage": prophage_hmm, "chromosome": chromosome_hmm},
        },
    }


def matched_control_y(rows: list[dict[str, object]], host: str, genus: str, class_name: str, load: int) -> list[float]:
    candidates = []
    for row in rows:
        if not row.get("ok") or str(row.get("host")) == host:
            continue
        if str(row.get("genus") or "") != genus:
            continue
        if class_name in set(row.get("carrier_classes") or []):
            continue
        other_load = int(row.get("prophage_protein_count") or 0)
        if other_load <= 0:
            continue
        counts = row.get("prophage_counts") if isinstance(row.get("prophage_counts"), dict) else {}
        y = y_score(int(counts.get(class_name, 0)), other_load)
        candidates.append((abs(math.log2((other_load + 1.0) / (load + 1.0))), y))
    candidates.sort(key=lambda item: item[0])
    if len(candidates) > 12:
        candidates = candidates[:12]
    return [value for _distance, value in candidates]


def compute_estimator_rows(rows: list[dict[str, object]], classes: list[str]) -> tuple[list[dict[str, object]], dict[str, object]]:
    y_by_host_class: dict[tuple[str, str], float] = {}
    n_by_host_class: dict[tuple[str, str], float] = {}
    d_by_host_class: dict[tuple[str, str], float] = {}
    ok_rows = [row for row in rows if row.get("ok")]
    for row in ok_rows:
        host = str(row.get("host"))
        load = int(row.get("prophage_protein_count") or 0)
        counts = row.get("prophage_counts") if isinstance(row.get("prophage_counts"), dict) else {}
        for class_name in classes:
            y_by_host_class[(host, class_name)] = y_score(int(counts.get(class_name, 0)), load)
    for row in ok_rows:
        host = str(row.get("host"))
        genus = str(row.get("genus") or "unmapped")
        load = int(row.get("prophage_protein_count") or 0)
        for class_name in classes:
            controls = matched_control_y(ok_rows, host, genus, class_name, load)
            n_by_host_class[(host, class_name)] = y_by_host_class[(host, class_name)] - median(controls) if controls else 0.0
    for row in ok_rows:
        host = str(row.get("host"))
        carried = set(row.get("carrier_classes") or [])
        absent = [class_name for class_name in classes if class_name not in carried]
        for class_name in classes:
            decoys = [n_by_host_class[(host, other)] for other in absent if other != class_name]
            d_by_host_class[(host, class_name)] = n_by_host_class[(host, class_name)] - median(decoys) if decoys else n_by_host_class[(host, class_name)]
    class_rows: list[dict[str, object]] = []
    for row in ok_rows:
        host = str(row.get("host"))
        genus = str(row.get("genus") or "unmapped")
        load = int(row.get("prophage_protein_count") or 0)
        chrom_load = int(row.get("chromosome_protein_count") or 0)
        carried = set(row.get("carrier_classes") or [])
        prophage_counts = row.get("prophage_counts") if isinstance(row.get("prophage_counts"), dict) else {}
        chromosome_counts = row.get("chromosome_counts") if isinstance(row.get("chromosome_counts"), dict) else {}
        for class_name in classes:
            if class_name not in carried:
                continue
            swap_values: list[float] = []
            for other in ok_rows:
                if str(other.get("host")) == host or str(other.get("genus") or "unmapped") != genus:
                    continue
                for swapped_class in set(other.get("carrier_classes") or []):
                    if swapped_class in classes:
                        swap_values.append(d_by_host_class[(host, swapped_class)])
            swapped = median(swap_values)
            d_value = d_by_host_class[(host, class_name)]
            s_value = d_value - swapped
            count = int(prophage_counts.get(class_name, 0))
            chrom_count = int(chromosome_counts.get(class_name, 0))
            class_rows.append(
                {
                    "host": host,
                    "genus": genus,
                    "class": class_name,
                    "carrier": True,
                    "A": count,
                    "L": load,
                    "Y": y_by_host_class[(host, class_name)],
                    "N": n_by_host_class[(host, class_name)],
                    "D": d_value,
                    "S": s_value,
                    "cross_host_swap_median": swapped,
                    "chromosome_Y": y_score(chrom_count, chrom_load),
                    "chromosome_delta": y_by_host_class[(host, class_name)] - y_score(chrom_count, chrom_load),
                    "n_same_genus_controls": len(matched_control_y(ok_rows, host, genus, class_name, load)),
                }
            )
    return class_rows, {"n_host_class_rows": len(class_rows)}


def compute_preflight(rows: list[dict[str, object]], classes: list[str]) -> dict[str, object]:
    ok_rows = [row for row in rows if row.get("ok")]
    per_class: dict[str, dict[str, object]] = {}
    pass_classes: list[str] = []
    for class_name in classes:
        c_plus = [row for row in ok_rows if class_name in set(row.get("carrier_classes") or [])]
        c_minus = [row for row in ok_rows if class_name not in set(row.get("carrier_classes") or [])]
        genera_with_both = 0
        for genus in sorted({str(row.get("genus") or "unmapped") for row in ok_rows}):
            genus_rows = [row for row in ok_rows if str(row.get("genus") or "unmapped") == genus]
            has_plus = any(class_name in set(row.get("carrier_classes") or []) for row in genus_rows)
            has_minus = any(class_name not in set(row.get("carrier_classes") or []) for row in genus_rows)
            if has_plus and has_minus:
                genera_with_both += 1
        total_hits = 0
        hit_cells = 0
        hits_by_genus: dict[str, int] = {}
        for row in ok_rows:
            counts = row.get("prophage_counts") if isinstance(row.get("prophage_counts"), dict) else {}
            count = int(counts.get(class_name, 0))
            if count > 0:
                hit_cells += 1
                genus = str(row.get("genus") or "unmapped")
                hits_by_genus[genus] = hits_by_genus.get(genus, 0) + count
            total_hits += count
        max_genus_fraction = max(hits_by_genus.values()) / total_hits if total_hits else 0.0
        checks = {
            "c_plus_hosts": len(c_plus) >= 100,
            "c_minus_hosts": len(c_minus) >= 100,
            "genera_with_both": genera_with_both >= 30,
            "cognate_hits": total_hits >= 50,
            "hit_cells": hit_cells >= 25,
            "max_genus_hit_fraction": max_genus_fraction <= 0.20 if total_hits else False,
        }
        passed = all(checks.values())
        if passed:
            pass_classes.append(class_name)
        per_class[class_name] = {
            "c_plus_hosts": len(c_plus),
            "c_minus_hosts": len(c_minus),
            "genera_with_both": genera_with_both,
            "cognate_hits": total_hits,
            "host_class_cells_with_hit": hit_cells,
            "max_genus_hit_fraction": max_genus_fraction,
            "checks": checks,
            "pass": passed,
        }
    experiment_pass = len(pass_classes) >= 3
    return {"pass": experiment_pass, "passing_classes": pass_classes, "n_passing_classes": len(pass_classes), "per_class": per_class}


def summarize_results(
    rows: list[dict[str, object]],
    class_rows: list[dict[str, object]],
    preflight: dict[str, object],
    classes: list[str],
    bootstrap_n: int,
) -> tuple[dict[str, object], dict[str, object]]:
    passed = set(preflight.get("passing_classes") or [])
    scoped = [row for row in class_rows if str(row.get("class")) in passed] or class_rows
    median_d = family_weighted_median([(float(row.get("D") or 0.0), str(row.get("genus") or "unmapped")) for row in scoped])
    median_s = family_weighted_median([(float(row.get("S") or 0.0), str(row.get("genus") or "unmapped")) for row in scoped])
    chrom_delta = family_weighted_median([(float(row.get("chromosome_delta") or 0.0), str(row.get("genus") or "unmapped")) for row in scoped])
    per_class: dict[str, dict[str, object]] = {}
    for class_name in classes:
        class_scoped = [row for row in class_rows if str(row.get("class")) == class_name]
        ok_rows = [row for row in rows if row.get("ok")]
        plus_y = []
        minus_y = []
        for row in ok_rows:
            counts = row.get("prophage_counts") if isinstance(row.get("prophage_counts"), dict) else {}
            value = y_score(int(counts.get(class_name, 0)), int(row.get("prophage_protein_count") or 0))
            item = (value, str(row.get("genus") or "unmapped"))
            if class_name in set(row.get("carrier_classes") or []):
                plus_y.append(item)
            else:
                minus_y.append(item)
        per_class[class_name] = {
            "c_plus_hosts": int(preflight["per_class"][class_name]["c_plus_hosts"]),
            "c_minus_hosts": int(preflight["per_class"][class_name]["c_minus_hosts"]),
            "median_D": family_weighted_median([(float(row.get("D") or 0.0), str(row.get("genus") or "unmapped")) for row in class_scoped]),
            "median_S": family_weighted_median([(float(row.get("S") or 0.0), str(row.get("genus") or "unmapped")) for row in class_scoped]),
            "median_c_plus_minus_Y_delta": family_weighted_median(plus_y) - family_weighted_median(minus_y) if plus_y and minus_y else 0.0,
            "preflight": preflight["per_class"][class_name],
        }
    c_plus_beats_c_minus = sum(1 for class_name in passed if per_class[class_name]["median_c_plus_minus_Y_delta"] > 0.0) >= 3
    summary = {
        "n_hosts": len(rows),
        "n_ok_hosts": sum(1 for row in rows if row.get("ok")),
        "per_class_c_plus_c_minus": {
            class_name: {"c_plus": per_class[class_name]["c_plus_hosts"], "c_minus": per_class[class_name]["c_minus_hosts"]}
            for class_name in classes
        },
        "preflight": preflight,
        "median_D": median_d,
        "median_S": median_s,
        "c_plus_beats_c_minus": c_plus_beats_c_minus,
        "cognate_beats_non_cognate_decoy": median_d > 0.0,
        "prophage_beats_chromosome": chrom_delta > 0.0,
        "median_prophage_chromosome_delta": chrom_delta,
        "bootstrap": {
            "D": bootstrap_group_weighted_median(scoped, "D", bootstrap_n),
            "S": bootstrap_group_weighted_median(scoped, "S", bootstrap_n),
        },
    }
    summary["verdict"] = verdict_from_summary(summary)
    return summary, per_class


def verdict_from_summary(summary: dict[str, object]) -> str:
    if not bool(summary.get("preflight", {}).get("pass")):
        return "data_gate_failed"
    median_d = float(summary.get("median_D") or 0.0)
    median_s = float(summary.get("median_S") or 0.0)
    cplus = bool(summary.get("c_plus_beats_c_minus"))
    decoy = bool(summary.get("cognate_beats_non_cognate_decoy"))
    chrom = bool(summary.get("prophage_beats_chromosome"))
    if median_d < 0.0 and median_s < 0.0:
        return "anti"
    if median_d > 0.0 and median_s <= 0.0:
        return "composition_ecology_dominated"
    if median_d > 0.0 and median_s > 0.0 and cplus and decoy and chrom:
        return "supportive"
    return "refuted"


def run_experiment() -> dict[str, object]:
    ensure_dir(CACHE_DIR)
    deadline = deadline_from_env()
    classes = parse_class_list()
    host_limit = parse_host_limit()
    bootstrap_n = env_int("CAD_BOOTSTRAP_N", 2000)
    manifest_path = os.environ.get("CAD_MANIFEST", DEFAULT_MANIFEST)
    df_venv = os.environ.get("CAD_DF_VENV", DEFAULT_DF_VENV)
    manifest_rows, manifest_meta = load_manifest(manifest_path, host_limit)
    family_to_class, mapping_meta = load_seed_family_map(classes)
    hmm_path, hmm_meta = load_or_fetch_hmm(deadline)
    host_rows: list[dict[str, object]] = []
    for manifest_row in manifest_rows:
        if deadline_expired(deadline):
            host_rows.append({"host": str(manifest_row.get("host_assembly") or ""), "genus": str(manifest_row.get("genus") or ""), "ok": False, "error": "fetch_deadline_exceeded"})
            break
        try:
            host_rows.append(prepare_host_row(manifest_row, classes, family_to_class, hmm_path, df_venv, deadline))
        except Exception as exc:
            host_rows.append(
                {
                    "host": str(manifest_row.get("host_assembly") or ""),
                    "genus": str(manifest_row.get("genus") or "unmapped"),
                    "ok": False,
                    "error": f"{type(exc).__name__}: {exc}",
                    "n_prophages": int(manifest_row.get("n_prophages") or 0),
                    "prophage_vjids": list(manifest_row.get("prophage_vjids") or []),
                }
            )
    class_rows, estimator_meta = compute_estimator_rows(host_rows, classes)
    preflight = compute_preflight(host_rows, classes)
    summary, per_class = summarize_results(host_rows, class_rows, preflight, classes, bootstrap_n)
    return {
        "experiment": "bridge.host_defense.cognate_anti_defense_virjendb",
        "inputs": {
            "manifest": manifest_meta,
            "seed_family_mapping": mapping_meta,
            "dbapis_hmm": hmm_meta,
            "classes": classes,
            "cache_dir": CACHE_DIR,
            "df_venv": df_venv,
        },
        "summary": summary,
        "per_host_rows": host_rows,
        "per_host_class_rows": class_rows,
        "per_class": per_class,
        "estimator": estimator_meta,
        "verdict": summary["verdict"],
    }


def assert_close(actual: float, expected: float, tol: float = 1e-9) -> None:
    if abs(actual - expected) > tol:
        raise AssertionError(f"{actual} != {expected}")


def selftest() -> dict[str, object]:
    manifest = "host_assembly\tgenus\tn_prophages\tprophage_vjids\nh1\tAlpha\t2\tvj1;vj2\nh2\tAlpha\t1\tvj3\n"
    parsed, meta = parse_manifest_text(manifest, None)
    if len(parsed) != 2 or parsed[0]["prophage_vjids"] != ["vj1", "vj2"] or meta["n_manifest_rows"] != 2:
        raise AssertionError("manifest parse failed")
    clean, sanitize_meta = sanitize_fasta_text(">lcl|abc|def note\nACD-*xjz\n>p2\nM U O\n")
    if ">abc_def" not in clean or "-" in clean or "*" in clean or sanitize_meta["removed_chars"] < 2:
        raise AssertionError("fasta sanitize failed")
    if normalize_class("Restriction-Modification") != "RM" or normalize_class("toxin-antitoxin module") != "TA":
        raise AssertionError("class normalization failed")
    assert_close(y_score(1, 9), math.log2(1.5 / 10.0))
    assert_close(family_weighted_median([(10.0, "A"), (20.0, "A"), (1.0, "B")]), 1.0)
    rows = [
        {"host": "h1", "genus": "Alpha", "ok": True, "prophage_protein_count": 10, "chromosome_protein_count": 100, "carrier_classes": ["RM"], "prophage_counts": {"RM": 2, "BREX": 0}, "chromosome_counts": {"RM": 1, "BREX": 0}},
        {"host": "h2", "genus": "Alpha", "ok": True, "prophage_protein_count": 10, "chromosome_protein_count": 100, "carrier_classes": [], "prophage_counts": {"RM": 0, "BREX": 0}, "chromosome_counts": {"RM": 0, "BREX": 0}},
    ]
    class_rows, _meta = compute_estimator_rows(rows, ["RM", "BREX"])
    if len(class_rows) != 1 or class_rows[0]["D"] <= 0.0:
        raise AssertionError("estimator failed")
    gate = compute_preflight(rows, ["RM", "BREX"])
    if gate["pass"]:
        raise AssertionError("tiny preflight should fail")
    supportive_summary = {
        "preflight": {"pass": True},
        "median_D": 0.2,
        "median_S": 0.1,
        "c_plus_beats_c_minus": True,
        "cognate_beats_non_cognate_decoy": True,
        "prophage_beats_chromosome": True,
    }
    if verdict_from_summary(supportive_summary) != "supportive":
        raise AssertionError("supportive verdict failed")
    dominated_summary = dict(supportive_summary)
    dominated_summary["median_S"] = 0.0
    if verdict_from_summary(dominated_summary) != "composition_ecology_dominated":
        raise AssertionError("composition verdict failed")
    failed_summary = dict(supportive_summary)
    failed_summary["preflight"] = {"pass": False}
    if verdict_from_summary(failed_summary) != "data_gate_failed":
        raise AssertionError("data gate verdict failed")
    return {
        "ok": True,
        "tested": [
            "manifest_parse",
            "fasta_sanitize",
            "normalize_class",
            "family_weighted_median",
            "Y_N_D_S",
            "preflight_gate",
            "verdict",
        ],
    }


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

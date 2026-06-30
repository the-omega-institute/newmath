#!/usr/bin/env python3
"""Fetch probe for codon-E1 mutation-pressure orientation data."""
from __future__ import annotations

from collections import Counter, defaultdict
from datetime import datetime, timezone
import csv
import hashlib
import io
import json
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import gzip
from itertools import product
from pathlib import Path
from typing import Any


EXPERIMENT_ID = "codon_e1_mutation_pressure_fetch_probe"
CLAIM_ID = "bridge.genetic_code.codon_e1_mutation_pressure_orientation"
USER_AGENT = "codon-e1-mutation-pressure-orientation"
NCBI_DELAY_SECONDS = 0.34
MIN_FETCHABLE_CLADES = 6
MIN_FETCHABLE_SPECIES = 6
MIN_CDS = 1000
MIN_SENSE_CODONS = 250000
MIN_EFFECTIVE_SBS = 1000.0
DEFAULT_PANEL_TARGET = 84
DEFAULT_MAX_ATTEMPTS = 30
BASES_DNA = ("T", "C", "A", "G")
BASES_RNA = ("U", "C", "A", "G")
RUIS_RAW_BASE = "https://raw.githubusercontent.com/chrisruis/Mutational_spectra_data/main"
RUIS_API_BASE = "https://api.github.com/repos/chrisruis/Mutational_spectra_data/contents"
ALL_SBS_PATH = "data/all_SBS_spectra.csv"

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[2]
PROBE_CACHE_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "codon_e1_mutation_pressure_fetch_probe.json"
)

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
    "ACU": "T", "ACC": "T", "ACA": "T", "ACG": "T",
    "AAU": "N", "AAC": "N", "AAA": "K", "AAG": "K",
    "AGU": "S", "AGC": "S", "AGA": "R", "AGG": "R",
    "GUU": "V", "GUC": "V", "GUA": "V", "GUG": "V",
    "GCU": "A", "GCC": "A", "GCA": "A", "GCG": "A",
    "GAU": "D", "GAC": "D", "GAA": "E", "GAG": "Glu",
    "GGU": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}
CODON_TO_AA["GAG"] = "E"


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def codon_order_rna() -> list[str]:
    return ["".join(parts) for parts in product(BASES_RNA, repeat=3)]


def sense_codon_order_rna() -> list[str]:
    return [codon for codon in codon_order_rna() if CODON_TO_AA[codon] != "*"]


def dna_to_rna(seq: str) -> str:
    return seq.upper().replace("T", "U")


def rna_to_dna(seq: str) -> str:
    return seq.upper().replace("U", "T")


def species_key_from_clade(clade: str) -> str:
    parts = clade.split("_")
    if len(parts) >= 2:
        return "_".join(parts[:2])
    return clade


def fetch_bytes(url: str, timeout: int = 90, attempts: int = 3) -> tuple[bytes, dict[str, object]]:
    last_error = ""
    for attempt in range(1, attempts + 1):
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                payload = response.read()
                return payload, {
                    "url": url,
                    "reachable": True,
                    "http_status": int(getattr(response, "status", 200)),
                    "byte_size": len(payload),
                    "sha256": hashlib.sha256(payload).hexdigest(),
                    "attempts": attempt,
                }
        except urllib.error.HTTPError as exc:
            last_error = f"HTTPError:{exc.code}"
            if exc.code not in {429, 500, 502, 503, 504}:
                break
        except urllib.error.URLError as exc:
            last_error = f"URLError:{exc.reason}"
        except TimeoutError:
            last_error = "TimeoutError"
        except Exception as exc:  # pragma: no cover - network surface
            last_error = f"{type(exc).__name__}:{exc}"
        time.sleep(NCBI_DELAY_SECONDS * attempt * 2.0)
    return b"", {"url": url, "reachable": False, "blocked": True, "error": last_error or "fetch_failed"}


def fetch_text(url: str, timeout: int = 90, attempts: int = 3) -> tuple[str, dict[str, object]]:
    payload, contact = fetch_bytes(url, timeout=timeout, attempts=attempts)
    if not payload:
        return "", contact
    return payload.decode("utf-8", "replace"), contact


def github_contents(path: str) -> tuple[list[dict[str, object]], dict[str, object]]:
    url = f"{RUIS_API_BASE}/{urllib.parse.quote(path)}?ref=main"
    text, contact = fetch_text(url, timeout=60)
    if not text:
        return [], contact
    try:
        payload = json.loads(text)
    except json.JSONDecodeError as exc:
        contact["parse_error"] = str(exc)
        return [], contact
    if not isinstance(payload, list):
        return [], {**contact, "parse_error": "github contents payload is not a list"}
    return [item for item in payload if isinstance(item, dict)], contact


def github_html_items(path: str) -> tuple[list[dict[str, object]], dict[str, object]]:
    url = f"https://github.com/chrisruis/Mutational_spectra_data/tree/main/{path}"
    text, contact = fetch_text(url, timeout=45, attempts=2)
    if not text:
        return [], contact
    prefix = re.escape("/chrisruis/Mutational_spectra_data/blob/main/" + path.strip("/") + "/")
    names = sorted(set(urllib.parse.unquote(name) for name in re.findall(prefix + r'([^"?#<>]+)', text)))
    contact["n_html_items"] = len(names)
    return [{"name": name, "path": f"{path}/{name}", "type": "file"} for name in names], contact


def raw_url(path: str) -> str:
    return f"{RUIS_RAW_BASE}/{path}"


def load_all_sbs() -> tuple[dict[str, dict[str, float]], dict[str, object]]:
    text, contact = fetch_text(raw_url(ALL_SBS_PATH), timeout=60)
    if not text:
        return {}, contact
    reader = csv.DictReader(io.StringIO(text))
    clades = [field for field in (reader.fieldnames or []) if field != "Substitution"]
    spectra = {clade: {} for clade in clades}
    substitutions: list[str] = []
    for row in reader:
        substitution = str(row["Substitution"])
        substitutions.append(substitution)
        for clade in clades:
            spectra[clade][substitution] = float(row[clade])
    contact["n_clades"] = len(clades)
    contact["n_substitutions"] = len(substitutions)
    contact["substitution_sum_range"] = [
        min(sum(values.values()) for values in spectra.values()) if spectra else None,
        max(sum(values.values()) for values in spectra.values()) if spectra else None,
    ]
    return spectra, contact


def reference_accessions_from_items(clade: str, items: list[dict[str, object]]) -> list[str]:
    accessions: list[str] = []
    for item in items:
        name = str(item.get("name", ""))
        if str(item.get("type")) != "file":
            continue
        lower = name.lower()
        if not lower.endswith((".fa", ".fasta", ".fna")):
            continue
        if name.startswith(clade):
            continue
        match = re.match(r"^((?:NC|NZ|NW|NT|CP|CM|CU|BX|AL|AE|GCF)_?\d+(?:\.\d+)?|[A-Z]{2}\d{6}(?:\.\d+)?|GCF_\d+(?:\.\d+)?)(?:_1)?\.(?:fa|fasta|fna)$", name)
        if match:
            accessions.append(match.group(1))
    return sorted(set(accessions))


def https_ftp_path(ftp_path: str) -> str:
    if ftp_path.startswith("ftp://"):
        return "https://" + ftp_path[len("ftp://") :]
    return ftp_path


def assembly_gbff_for_gcf(accession: str) -> tuple[str, dict[str, object]]:
    search = ncbi_url("esearch", {"db": "assembly", "term": accession, "retmax": 1})
    text, search_contact = fetch_text(search, timeout=45, attempts=2)
    match = re.search(r"<Id>(\d+)</Id>", text or "")
    if not match:
        return "", {"search": search_contact, "error": "assembly_id_not_found"}
    time.sleep(NCBI_DELAY_SECONDS)
    summary = ncbi_url("esummary", {"db": "assembly", "id": match.group(1), "report": "full"})
    text, summary_contact = fetch_text(summary, timeout=60, attempts=2)
    ftp_match = re.search(r"<FtpPath_RefSeq>([^<]+)</FtpPath_RefSeq>", text or "")
    if not ftp_match:
        ftp_match = re.search(r"<FtpPath_GenBank>([^<]+)</FtpPath_GenBank>", text or "")
    if not ftp_match:
        return "", {"search": search_contact, "summary": summary_contact, "error": "assembly_ftp_not_found"}
    ftp = https_ftp_path(ftp_match.group(1)).rstrip("/")
    stem = ftp.rsplit("/", 1)[-1]
    url = f"{ftp}/{stem}_genomic.gbff.gz"
    payload, gbff_contact = fetch_bytes(url, timeout=120, attempts=3)
    if not payload:
        return "", {"search": search_contact, "summary": summary_contact, "gbff": gbff_contact}
    try:
        text = gzip.decompress(payload).decode("utf-8", "replace")
    except Exception as exc:
        return "", {"search": search_contact, "summary": summary_contact, "gbff": {**gbff_contact, "decompress_error": f"{type(exc).__name__}:{exc}"}}
    return text, {"search": search_contact, "summary": summary_contact, "gbff": gbff_contact}


def ncbi_efetch_url(accession: str, rettype: str) -> str:
    params = urllib.parse.urlencode({"db": "nuccore", "id": accession, "rettype": rettype, "retmode": "text"})
    return f"https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?{params}"


def ncbi_url(endpoint: str, params: dict[str, object]) -> str:
    return f"https://eutils.ncbi.nlm.nih.gov/entrez/eutils/{endpoint}.fcgi?{urllib.parse.urlencode(params)}"


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
            if "=" in body:
                name, value = body.split("=", 1)
                value = value.strip().strip('"')
                qualifiers = current["qualifiers"]
                assert isinstance(qualifiers, dict)
                qualifiers.setdefault(name, []).append(value)
                if stripped.count('"') == 1:
                    current_qualifier = name
            else:
                qualifiers = current["qualifiers"]
                assert isinstance(qualifiers, dict)
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
    parts = []
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
    if not parts:
        return None
    return strand, parts


def reverse_complement(seq: str) -> str:
    return seq.translate(str.maketrans("ACGT", "TGCA"))[::-1]


def coding_positions(strand: str, segments: list[tuple[int, int]]) -> list[int]:
    if strand == "+":
        return [pos for start, end in segments for pos in range(start, end)]
    return [pos for start, end in reversed(segments) for pos in range(end - 1, start - 1, -1)]


def coding_sequence(genome: str, strand: str, segments: list[tuple[int, int]]) -> str:
    seq = "".join(genome[start:end] for start, end in segments)
    return seq if strand == "+" else reverse_complement(seq)


def parse_genbank_cds(gb_text: str) -> dict[str, object]:
    lines = gb_text.splitlines()
    genome = parse_origin(lines)
    features = parse_features(lines)
    cds_records = []
    transl_tables: Counter[int] = Counter()
    skipped = Counter()
    for feature in features:
        if feature.get("key") != "CDS":
            continue
        qualifiers = feature.get("qualifiers")
        if not isinstance(qualifiers, dict):
            skipped["missing_qualifiers"] += 1
            continue
        if "pseudo" in qualifiers or "pseudogene" in qualifiers:
            skipped["pseudo"] += 1
            continue
        parsed = parse_location(str(feature.get("location", "")))
        if parsed is None:
            skipped["bad_location"] += 1
            continue
        transl_values = qualifiers.get("transl_table", [])
        transl_table = int(transl_values[0]) if transl_values else 11
        transl_tables[transl_table] += 1
        if transl_table != 11:
            skipped["non_table_11"] += 1
            continue
        strand, segments = parsed
        seq = coding_sequence(genome, strand, segments)
        seq = re.sub(r"[^ACGT]", "N", seq)
        if len(seq) < 3:
            skipped["short"] += 1
            continue
        cds_records.append({"strand": strand, "segments": segments, "positions": coding_positions(strand, segments), "sequence": seq})
    return {
        "genome_length": len(genome),
        "cds_records": cds_records,
        "transl_table_counts": dict(transl_tables),
        "skipped_cds": dict(skipped),
        "n_features_cds": sum(1 for feature in features if feature.get("key") == "CDS"),
    }


def genome_context(genome: str, position: int, strand: str) -> str | None:
    if strand == "+":
        if position <= 0 or position + 1 >= len(genome):
            return None
        context = genome[position - 1 : position + 2]
    else:
        if position <= 0 or position + 1 >= len(genome):
            return None
        context = genome[position - 1 : position + 2]
        context = reverse_complement(context)
    if len(context) == 3 and set(context) <= set("ACGT"):
        return context
    return None


def codon_counts_and_contexts(gb_text: str) -> dict[str, object]:
    parsed = parse_genbank_cds(gb_text)
    genome = parse_origin(gb_text.splitlines())
    counts = {codon: 0 for codon in sense_codon_order_rna()}
    context_counts: dict[str, list[Counter[str]]] = {
        codon: [Counter(), Counter(), Counter()] for codon in sense_codon_order_rna()
    }
    n_sense = 0
    n_stop_or_ambiguous = 0
    n_context_ready_bases = 0
    for record in parsed["cds_records"]:
        seq = str(record["sequence"])
        strand = str(record["strand"])
        positions = record["positions"]
        assert isinstance(positions, list)
        usable_len = (len(seq) // 3) * 3
        for offset in range(0, usable_len, 3):
            codon_dna = seq[offset : offset + 3]
            codon = dna_to_rna(codon_dna)
            if codon not in CODON_TO_AA or CODON_TO_AA[codon] == "*":
                n_stop_or_ambiguous += 1
                continue
            for inner in range(3):
                pos = int(positions[offset + inner])
                context = genome_context(genome, pos, strand)
                if context is not None:
                    context_counts[codon][inner][context] += 1
                    n_context_ready_bases += 1
            counts[codon] += 1
            n_sense += 1
    serial_context_counts = {
        codon: [dict(counter) for counter in context_counts[codon]]
        for codon in sense_codon_order_rna()
    }
    return {
        **{key: value for key, value in parsed.items() if key != "cds_records"},
        "codon_counts_rna": counts,
        "total_sense_codons": n_sense,
        "n_stop_or_ambiguous_codons": n_stop_or_ambiguous,
        "n_cds": len(parsed["cds_records"]),
        "n_context_ready_bases": n_context_ready_bases,
        "codon_context_counts": serial_context_counts,
    }


def compact_attempt(row: dict[str, object]) -> dict[str, object]:
    keys = [
        "clade",
        "species_key",
        "reference_accession",
        "ok_numeric",
        "drop_reason",
        "n_cds",
        "total_sense_codons",
        "n_context_ready_bases",
        "effective_sbs_count",
    ]
    return {key: row.get(key) for key in keys if key in row}


def fetch_clade_payload(clade: str, spectrum: dict[str, float], items: list[dict[str, object]]) -> dict[str, object]:
    accessions = reference_accessions_from_items(clade, items)
    if not accessions:
        return {
            "clade": clade,
            "species_key": species_key_from_clade(clade),
            "ok_numeric": False,
            "drop_reason": "no_reference_accession_in_clade_directory",
        }
    accession = accessions[0]
    if accession.startswith("GCF_"):
        fasta_text = ""
        fasta_contact = {"reachable": None, "note": "assembly accession; genomic gbff fetched from assembly FTP"}
        gb_text, gb_contact = assembly_gbff_for_gcf(accession)
    else:
        fasta_url = ncbi_efetch_url(accession, "fasta_cds_na")
        fasta_text, fasta_contact = fetch_text(fasta_url, timeout=90, attempts=2)
        time.sleep(NCBI_DELAY_SECONDS)
        gb_url = ncbi_efetch_url(accession, "gbwithparts")
        gb_text, gb_contact = fetch_text(gb_url, timeout=120, attempts=3)
        time.sleep(NCBI_DELAY_SECONDS)
    if not gb_text:
        return {
            "clade": clade,
            "species_key": species_key_from_clade(clade),
            "reference_accession": accession,
            "ok_numeric": False,
            "drop_reason": "ncbi_genbank_unreachable",
            "gb_contact": gb_contact,
            "fasta_cds_na_contact": fasta_contact,
        }
    try:
        parsed = codon_counts_and_contexts(gb_text)
    except Exception as exc:
        return {
            "clade": clade,
            "species_key": species_key_from_clade(clade),
            "reference_accession": accession,
            "ok_numeric": False,
            "drop_reason": "genbank_parse_failed",
            "exception": f"{type(exc).__name__}:{exc}",
            "gb_contact": gb_contact,
            "fasta_cds_na_contact": fasta_contact,
        }
    n_cds = int(parsed["n_cds"])
    total_sense = int(parsed["total_sense_codons"])
    # Ruis clade files expose rescaled SBS rates/proportions, not mutation event
    # counts. Keep the preregistered count gate in the ledger as unavailable
    # rather than inventing a count proxy from normalized rates.
    effective_sbs = None
    table11_ok = set(parsed.get("transl_table_counts", {})) <= {11}
    ok_numeric = (
        table11_ok
        and n_cds >= MIN_CDS
        and total_sense >= MIN_SENSE_CODONS
        and len(spectrum) == 96
        and int(parsed["n_context_ready_bases"]) > 0
    )
    if not table11_ok:
        drop_reason = "non_table_11_cds_present"
    elif n_cds < MIN_CDS:
        drop_reason = "too_few_cds"
    elif total_sense < MIN_SENSE_CODONS:
        drop_reason = "too_few_sense_codons"
    elif len(spectrum) != 96:
        drop_reason = "bad_sbs_dimension"
    elif int(parsed["n_context_ready_bases"]) <= 0:
        drop_reason = "no_context_ready_cds_bases"
    else:
        drop_reason = None
    return {
        "clade": clade,
        "species_key": species_key_from_clade(clade),
        "reference_accession": accession,
        "ok_numeric": bool(ok_numeric),
        "drop_reason": drop_reason,
        "sbs_spectrum": spectrum,
        "effective_sbs_count": effective_sbs,
        "effective_sbs_count_status": "unavailable_rates_only",
        "fasta_cds_na_reachable": bool(fasta_contact.get("reachable")) and bool(fasta_text),
        "fasta_cds_na_contact": fasta_contact,
        "gb_contact": gb_contact,
        "sample_codon_counts": {key: parsed["codon_counts_rna"][key] for key in list(sense_codon_order_rna())[:8]},
        **parsed,
    }


def build_probe(
    force_refresh: bool = False,
    panel_target: int = DEFAULT_PANEL_TARGET,
    max_attempts: int = DEFAULT_MAX_ATTEMPTS,
) -> dict[str, object]:
    if PROBE_CACHE_PATH.exists() and not force_refresh:
        cached = json.loads(PROBE_CACHE_PATH.read_text(encoding="utf-8"))
        if int(cached.get("n_clades", 0)) >= MIN_FETCHABLE_CLADES and int(cached.get("n_species", 0)) >= MIN_FETCHABLE_SPECIES:
            return cached

    spectra, sbs_contact = load_all_sbs()
    clade_items, clade_contact = github_contents("data/clade_spectra")
    clade_names = [str(item["name"]) for item in clade_items if item.get("type") == "dir" and str(item.get("name")) in spectra]
    if not clade_names:
        clade_names = list(spectra)
        clade_contact = {**clade_contact, "fallback": "all_sbs_header_clade_order"}

    attempts: list[dict[str, object]] = []
    clades: list[dict[str, object]] = []
    species_seen: set[str] = set()
    accession_cache: dict[str, dict[str, object]] = {}
    for clade in clade_names:
        if len(attempts) >= max_attempts:
            break
        items, contact = github_contents(f"data/clade_spectra/{clade}")
        if not items:
            items, html_contact = github_html_items(f"data/clade_spectra/{clade}")
            contact = {**contact, "html_fallback": html_contact}
        accessions = reference_accessions_from_items(clade, items)
        cache_key = accessions[0] if accessions else ""
        if cache_key and cache_key in accession_cache:
            cached = accession_cache[cache_key]
            row = {
                **cached,
                "clade": clade,
                "species_key": species_key_from_clade(clade),
                "sbs_spectrum": spectra[clade],
            }
        else:
            row = fetch_clade_payload(clade, spectra[clade], items)
            if cache_key and row.get("reference_accession") == cache_key:
                accession_cache[cache_key] = {
                    key: value
                    for key, value in row.items()
                    if key not in {"clade", "species_key", "sbs_spectrum", "github_clade_contact"}
                }
        row["github_clade_contact"] = contact
        attempts.append(compact_attempt(row))
        if not row.get("ok_numeric"):
            continue
        clades.append(row)
        species_seen.add(str(row["species_key"]))
        if len(clades) >= panel_target and len(clades) >= MIN_FETCHABLE_CLADES and len(species_seen) >= MIN_FETCHABLE_SPECIES:
            break

    species = sorted({str(row["species_key"]) for row in clades})
    payload = {
        "status": "ok" if len(clades) >= MIN_FETCHABLE_CLADES and len(species) >= MIN_FETCHABLE_SPECIES else "needs_external",
        "generated_at": now_iso(),
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "provenance": {
            "ruis_repository": "https://github.com/chrisruis/Mutational_spectra_data",
            "all_sbs_path": ALL_SBS_PATH,
            "clade_reference_rule": "use the accession-named reference FASTA in each Ruis clade directory, then fetch NCBI nuccore gbwithparts and fasta_cds_na",
            "not_window6": True,
            "not_causal": True,
        },
        "filters": {
            "transl_table": 11,
            "min_cds": MIN_CDS,
            "min_sense_codons": MIN_SENSE_CODONS,
            "min_effective_sbs_count": MIN_EFFECTIVE_SBS,
            "exclude_hypermutator_or_dna_repair_signature_clades": True,
            "note": "Ruis main clade spectra are used; separate dna_repair_gene_signatures and hypermutator lineage files are not sampled.",
        },
        "source_status": {"all_sbs": sbs_contact, "clade_spectra": clade_contact},
        "sense_codon_order_rna": sense_codon_order_rna(),
        "clades": clades,
        "attempts_compact": attempts,
        "n_clades": len(clades),
        "n_species": len(species),
        "species": species,
        "panel_target": panel_target,
        "max_attempts": max_attempts,
    }
    PROBE_CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    PROBE_CACHE_PATH.write_text(json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def emit(payload: dict[str, object]) -> None:
    status = str(payload.get("status", "needs_external"))
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "ok" else 3)


def main() -> None:
    force = "--force" in sys.argv
    probe_only = "--probe-only" in sys.argv
    target = MIN_FETCHABLE_CLADES if probe_only else int(__import__("os").environ.get("CODON_E1_MUT_PANEL_TARGET", str(DEFAULT_PANEL_TARGET)))
    max_attempts = int(__import__("os").environ.get("CODON_E1_MUT_MAX_ATTEMPTS", "18" if probe_only else str(DEFAULT_MAX_ATTEMPTS)))
    payload = build_probe(force_refresh=force, panel_target=target, max_attempts=max_attempts)
    emit(payload)


if __name__ == "__main__":
    main()

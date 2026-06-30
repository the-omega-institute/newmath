#!/usr/bin/env python3
"""Fetch probe for alternative-code codon-usage strata.

The probe accepts only numeric codon counts.  HTML reachability alone is not a
usable input.  NCBI accession-level CDS FASTA is preferred for mitochondrial
tables because GenBank records carry explicit transl_table qualifiers.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
import html
import json
import re
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any


BASES_DNA = ("T", "C", "A", "G")
BASES_RNA = ("U", "C", "A", "G")
USER_AGENT = "codon-e1-alternative-code-deformation/1.0"
NCBI_DELAY_SECONDS = 0.35
MIN_POWERED_ORGANISMS = 3
MIN_POWERED_TABLES = 2

EXPERIMENT_DIR = Path(__file__).resolve().parent
REPO_ROOT = EXPERIMENT_DIR.parents[2]
GENETIC_CODES_PATH = REPO_ROOT / "tools" / "bio_reality" / "data" / "ncbi_genetic_codes.json"
CACHE_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "codon_e1_alternative_code_fetch_probe_panel.json"
)


NCBI_ACCESSION_CANDIDATES: tuple[dict[str, object], ...] = (
    {
        "table_id": 2,
        "organism": "Homo sapiens",
        "cluster": "vertebrate_mitochondrial_mammal",
        "accession": "NC_012920.1",
    },
    {
        "table_id": 2,
        "organism": "Mus musculus",
        "cluster": "vertebrate_mitochondrial_mammal",
        "accession": "NC_005089.1",
    },
    {
        "table_id": 2,
        "organism": "Rattus norvegicus",
        "cluster": "vertebrate_mitochondrial_mammal",
        "accession": "NC_001665.2",
    },
    {
        "table_id": 2,
        "organism": "Gallus gallus",
        "cluster": "vertebrate_mitochondrial_bird",
        "accession": "NC_001323.1",
    },
    {
        "table_id": 2,
        "organism": "Danio rerio",
        "cluster": "vertebrate_mitochondrial_fish",
        "accession": "NC_002333.2",
    },
    {
        "table_id": 2,
        "organism": "Xenopus laevis",
        "cluster": "vertebrate_mitochondrial_amphibian",
        "accession": "NC_001573.1",
    },
    {
        "table_id": 3,
        "organism": "Saccharomyces cerevisiae S288C",
        "cluster": "yeast_mitochondrial_saccharomyces",
        "accession": "NC_001224.1",
    },
    {
        "table_id": 5,
        "organism": "Drosophila melanogaster",
        "cluster": "invertebrate_mitochondrial_diptera",
        "accession": "NC_024511.2",
    },
    {
        "table_id": 5,
        "organism": "Caenorhabditis elegans",
        "cluster": "invertebrate_mitochondrial_nematode",
        "accession": "NC_001328.1",
    },
    {
        "table_id": 5,
        "organism": "Apis mellifera ligustica",
        "cluster": "invertebrate_mitochondrial_hymenoptera",
        "accession": "NC_001566.1",
    },
    {
        "table_id": 5,
        "organism": "Anopheles gambiae",
        "cluster": "invertebrate_mitochondrial_diptera",
        "accession": "NC_002084.1",
    },
    {
        "table_id": 5,
        "organism": "Aedes aegypti",
        "cluster": "invertebrate_mitochondrial_diptera",
        "accession": "NC_010241.1",
    },
)


KAZUSA_CANDIDATES: tuple[dict[str, object], ...] = (
    {"table_id": 6, "organism": "Tetrahymena thermophila", "taxid": "5911"},
    {"table_id": 6, "organism": "Paramecium tetraurelia", "taxid": "5888"},
    {"table_id": 6, "organism": "Dictyostelium discoideum", "taxid": "44689"},
    {"table_id": 2, "organism": "Homo sapiens", "taxid": "9606"},
    {"table_id": 3, "organism": "Saccharomyces cerevisiae", "taxid": "4932"},
    {"table_id": 5, "organism": "Drosophila melanogaster", "taxid": "7227"},
)


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def codon_order_rna() -> list[str]:
    return ["".join((a, b, c)) for a in BASES_RNA for b in BASES_RNA for c in BASES_RNA]


def fetch_text(url: str, timeout: int = 45, attempts: int = 3) -> tuple[str, dict[str, object]]:
    last_error = ""
    for attempt in range(1, attempts + 1):
        request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                payload = response.read()
                status = int(getattr(response, "status", 200))
                text = payload.decode("utf-8", "replace")
                return text, {
                    "url": url,
                    "reachable": True,
                    "http_status": status,
                    "byte_size": len(payload),
                    "sha256": hashlib.sha256(payload).hexdigest(),
                    "attempts": attempt,
                }
        except urllib.error.HTTPError as exc:
            last_error = f"HTTPError:{exc.code}"
            if exc.code != 429:
                break
        except urllib.error.URLError as exc:
            last_error = f"URLError:{exc.reason}"
        except TimeoutError:
            last_error = "TimeoutError"
        except Exception as exc:  # pragma: no cover - network surface
            last_error = f"{type(exc).__name__}:{exc}"
        time.sleep(NCBI_DELAY_SECONDS * attempt * 2.0)
    return "", {"url": url, "reachable": False, "blocked": True, "error": last_error or "fetch_failed"}


def fetch_ncbi_text(accession: str, rettype: str) -> tuple[str, dict[str, object]]:
    query = urllib.parse.urlencode({"db": "nuccore", "id": accession, "rettype": rettype, "retmode": "text"})
    url = f"https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?{query}"
    text, contact = fetch_text(url)
    time.sleep(NCBI_DELAY_SECONDS)
    return text, contact


def parse_fasta_cds(text: str) -> list[tuple[str, str]]:
    records: list[tuple[str, str]] = []
    header = ""
    chunks: list[str] = []
    for line in text.splitlines():
        if line.startswith(">"):
            if header and chunks:
                records.append((header, "".join(chunks)))
            header = line[1:].strip()
            chunks = []
        else:
            chunks.append(re.sub(r"[^A-Za-z]", "", line).upper())
    if header and chunks:
        records.append((header, "".join(chunks)))
    return records


def parse_genbank_metadata(text: str) -> tuple[str | None, str | None, list[int]]:
    organism_match = re.search(r"^  ORGANISM  (.+)$", text, re.MULTILINE)
    definition_match = re.search(r"^DEFINITION  (.+?)(?:\nACCESSION|\nVERSION)", text, re.MULTILINE | re.DOTALL)
    organism = organism_match.group(1).strip() if organism_match else None
    definition = re.sub(r"\s+", " ", definition_match.group(1)).strip() if definition_match else None
    tables = sorted({int(value) for value in re.findall(r"/transl_table=(\d+)", text)})
    return organism, definition, tables


def load_genetic_codes() -> dict[int, dict[str, object]]:
    payload = json.loads(GENETIC_CODES_PATH.read_text(encoding="utf-8"))
    tables: dict[int, dict[str, object]] = {}
    for item in payload["tables"]:
        table_id = int(item["table_id"])
        aa = str(item["aa"])
        tables[table_id] = {
            "table_id": table_id,
            "name": item["name"],
            "codon_to_aa": dict(zip(payload["codon_order"], aa)),
        }
    return tables


def count_sense_codons(records: list[tuple[str, str]], codon_to_aa: dict[str, str]) -> tuple[dict[str, int], int, int]:
    counts = {codon: 0 for codon, aa in codon_to_aa.items() if aa != "*"}
    skipped = 0
    for _header, seq in records:
        usable = (len(seq) // 3) * 3
        if usable <= 0:
            skipped += 1
            continue
        for offset in range(0, usable, 3):
            codon_dna = seq[offset : offset + 3]
            if len(codon_dna) != 3 or any(base not in BASES_DNA for base in codon_dna):
                continue
            codon = codon_dna.replace("T", "U")
            if codon in counts:
                counts[codon] += 1
    return counts, sum(counts.values()), skipped


def parse_kazusa_counts(text: str) -> tuple[dict[str, int], int]:
    pre_match = re.search(r"<PRE>(.*?)</PRE>", text, re.IGNORECASE | re.DOTALL)
    if not pre_match:
        return {}, 0
    payload = html.unescape(re.sub(r"<.*?>", " ", pre_match.group(1)))
    counts: dict[str, int] = {}
    pattern = re.compile(r"\b([UCAGT]{3})\b\s+(?:[A-Z*]\s+[-0-9.]+\s+)?[-0-9.]+\s*\(\s*([0-9]+)\)")
    for codon, count in pattern.findall(payload):
        counts[codon.replace("T", "U")] = int(count)
    return counts, sum(counts.values())


def fetch_ncbi_accession_panel(force_refresh: bool = False) -> tuple[list[dict[str, object]], dict[str, object]]:
    codes = load_genetic_codes()
    organisms: list[dict[str, object]] = []
    attempts: list[dict[str, object]] = []
    for candidate in NCBI_ACCESSION_CANDIDATES:
        table_id = int(candidate["table_id"])
        accession = str(candidate["accession"])
        gb_text, gb_contact = fetch_ncbi_text(accession, "gb")
        cds_text, cds_contact = fetch_ncbi_text(accession, "fasta_cds_na")
        reachable = bool(gb_contact.get("reachable")) and bool(cds_contact.get("reachable"))
        organism_name, definition, transl_tables = parse_genbank_metadata(gb_text) if gb_text else (None, None, [])
        records = parse_fasta_cds(cds_text) if cds_text else []
        counts: dict[str, int] = {}
        total_sense = 0
        skipped = 0
        if records and table_id in codes:
            counts, total_sense, skipped = count_sense_codons(records, codes[table_id]["codon_to_aa"])  # type: ignore[arg-type]
        ok = reachable and records and total_sense > 0 and transl_tables == [table_id]
        attempt = {
            "source": "NCBI efetch",
            "table_id": table_id,
            "organism": candidate["organism"],
            "accession": accession,
            "reachable": reachable,
            "blocked": not reachable,
            "genbank_contact": gb_contact,
            "cds_contact": cds_contact,
            "transl_tables": transl_tables,
            "n_cds_records": len(records),
            "total_sense_codons": total_sense,
            "sample_counts": {codon: counts.get(codon, 0) for codon in codon_order_rna()[:8]},
            "ok_numeric_table_assigned": bool(ok),
        }
        attempts.append(attempt)
        if ok:
            organisms.append(
                {
                    "source": "NCBI efetch fasta_cds_na",
                    "table_id": table_id,
                    "table_name": codes[table_id]["name"],
                    "organism": candidate["organism"],
                    "ncbi_organism": organism_name,
                    "definition": definition,
                    "accession": accession,
                    "cluster": candidate["cluster"],
                    "codon_counts_rna": counts,
                    "total_sense_codons": total_sense,
                    "n_cds_records": len(records),
                    "n_skipped_cds": skipped,
                }
            )
    source_status = {
        "source": "NCBI efetch accession CDS",
        "reachable": any(item.get("reachable") for item in attempts),
        "blocked": not any(item.get("reachable") for item in attempts),
        "attempted": len(attempts),
        "usable_numeric_table_assigned": len(organisms),
        "attempts": attempts,
    }
    return organisms, source_status


def fetch_kazusa_probe() -> dict[str, object]:
    attempts: list[dict[str, object]] = []
    for candidate in KAZUSA_CANDIDATES:
        query = urllib.parse.urlencode(
            {"species": str(candidate["taxid"]), "aa": str(candidate["table_id"]), "style": "N"}
        )
        url = f"https://www.kazusa.or.jp/codon/cgi-bin/showcodon.cgi?{query}"
        text, contact = fetch_text(url, timeout=30, attempts=2)
        counts, total = parse_kazusa_counts(text) if text else ({}, 0)
        attempts.append(
            {
                "source": "Kazusa CUTG showcodon.cgi",
                "table_id": candidate["table_id"],
                "organism": candidate["organism"],
                "taxid": candidate["taxid"],
                "reachable": bool(contact.get("reachable")),
                "blocked": not bool(contact.get("reachable")),
                "contact": contact,
                "n_numeric_codons": len(counts),
                "total_codons": total,
                "sample_counts": {codon: counts.get(codon, 0) for codon in codon_order_rna()[:8]},
                "ok_numeric": len(counts) == 64 and total > 0,
                "table_assignment_note": (
                    "Kazusa renders counts under a selected code table but the species aggregate page "
                    "does not itself prove that all CDS records belong to that code table."
                ),
            }
        )
    return {
        "source": "Kazusa CUTG showcodon.cgi",
        "reachable": any(item["reachable"] for item in attempts),
        "blocked": not any(item["reachable"] for item in attempts),
        "attempted": len(attempts),
        "usable_numeric": sum(1 for item in attempts if item["ok_numeric"]),
        "attempts": attempts,
    }


def powered_tables(organisms: list[dict[str, object]]) -> dict[str, int]:
    counts = Counter(str(item["table_id"]) for item in organisms)
    return {table_id: count for table_id, count in sorted(counts.items(), key=lambda item: int(item[0]))}


def build_panel(force_refresh: bool = False) -> dict[str, object]:
    if CACHE_PATH.exists() and not force_refresh:
        return json.loads(CACHE_PATH.read_text(encoding="utf-8"))

    organisms, ncbi_status = fetch_ncbi_accession_panel(force_refresh=force_refresh)
    kazusa_status = fetch_kazusa_probe()
    table_counts = powered_tables(organisms)
    powered = {table_id: n for table_id, n in table_counts.items() if n >= MIN_POWERED_ORGANISMS}
    fetchable = len(powered) >= MIN_POWERED_TABLES
    panel = {
        "generated_at": now_iso(),
        "provenance": {
            "source": "NCBI efetch accession-level CDS FASTA with GenBank transl_table qualifiers",
            "note": (
                "Counts are computed from real CDS nucleotide sequences; the experiment is a codon-E1 "
                "alternative-code deformation test and is not Window6 forcing."
            ),
        },
        "codon_order_rna": codon_order_rna(),
        "organisms": organisms,
        "source_status": {"ncbi": ncbi_status, "kazusa": kazusa_status},
        "powered_tables": powered,
        "fetchable": fetchable,
        "fetchability_rule": {
            "min_powered_tables": MIN_POWERED_TABLES,
            "min_organisms_per_table": MIN_POWERED_ORGANISMS,
            "only_numeric_counts_are_accepted": True,
        },
    }
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    CACHE_PATH.write_text(json.dumps(panel, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return panel


def main() -> None:
    panel = build_panel(force_refresh=True)
    for source_name, status in panel["source_status"].items():  # type: ignore[union-attr]
        print(
            json.dumps(
                {
                    "source": source_name,
                    "reachable": status.get("reachable"),
                    "blocked": status.get("blocked"),
                    "usable": status.get("usable_numeric_table_assigned", status.get("usable_numeric")),
                    "sample": [
                        {
                            "table_id": item.get("table_id"),
                            "organism": item.get("organism"),
                            "reachable": item.get("reachable"),
                            "ok": item.get("ok_numeric_table_assigned", item.get("ok_numeric")),
                            "sample_counts": item.get("sample_counts"),
                        }
                        for item in status.get("attempts", [])[:4]
                    ],
                },
                ensure_ascii=True,
                sort_keys=True,
            )
        )
    print(
        json.dumps(
            {
                "status": "fetchable" if panel["fetchable"] else "needs_external",
                "powered_tables": panel["powered_tables"],
                "n_organisms": len(panel["organisms"]),  # type: ignore[arg-type]
                "cache_path": str(CACHE_PATH),
            },
            ensure_ascii=True,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()

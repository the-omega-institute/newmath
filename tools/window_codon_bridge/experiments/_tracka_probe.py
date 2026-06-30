#!/usr/bin/env python3
"""Yield and collinearity probe for Track-A exact-cognate boundary data.

The probe builds a RefSeq GBFF-only panel: each accepted genome supplies both
CDS codon counts and tRNA anticodon features from the same GenBank file.  The
boundary carrier is B_o(c)=1 when the Watson-Crick anticodon for codon c is not
present among tRNAs annotated for c's amino-acid isotype.  The collinearity gate
checks whether that binary boundary remains estimable after smooth decoding
supply and GC3 are controlled.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from datetime import datetime, timezone
import gzip
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import re
import sys
import time
import urllib.error
import urllib.request
from typing import Any


EXPERIMENT_ID = "tracka_exact_cognate_wobble_boundary_probe"
CLAIM_ID = "bridge.genetic_code.tracka_exact_cognate_wobble_boundary"
USER_AGENT = "tracka-exact-cognate-wobble-boundary"
NCBI_DELAY_SECONDS = 0.34
TARGET_GENERA = 24
MIN_GATE_GENERA = 15
MIN_COMPLETE_CDS = 800
MIN_SENSE_CODONS = 200000
MIN_VARIABLE_BOUNDARY_CODONS = 30
MIN_RESIDUAL_SD = 1.0e-3
MIN_RESIDUAL_VARIANCE_RATIO = 0.02
TOL = 1.0e-12

BASES_RNA = ("U", "C", "A", "G")
SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[2]
PROBE_CACHE_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "tracka_exact_cognate_wobble_boundary_probe.json"
)
E1_PANEL_PATH = (
    REPO_ROOT
    / "tools"
    / "window_codon_bridge"
    / "synced"
    / "codon_e1_trna_decoding_supply_orientation_panel.json"
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
    "GAU": "D", "GAC": "D", "GAA": "E", "GAG": "E",
    "GGU": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}

AA3_TO_1 = {
    "Ala": "A", "Arg": "R", "Asn": "N", "Asp": "D", "Cys": "C",
    "Gln": "Q", "Glu": "E", "Gly": "G", "His": "H", "Ile": "I",
    "Leu": "L", "Lys": "K", "Met": "M", "Phe": "F", "Pro": "P",
    "Ser": "S", "Thr": "T", "Trp": "W", "Tyr": "Y", "Val": "V",
}


def load_module(path: Path, name: str) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


E1_FETCH = load_module(SCRIPT_DIR / "_e1_trna_fetch_probe.py", "_e1_trna_fetch_probe_for_tracka")


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def round_float(value: float | None, digits: int = 12) -> float | None:
    if value is None:
        return None
    if not math.isfinite(value):
        return value
    rounded = round(float(value), digits)
    return 0.0 if rounded == -0.0 else rounded


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else math.nan


def variance(values: list[float]) -> float:
    if not values:
        return math.nan
    center = mean(values)
    return sum((value - center) ** 2 for value in values) / len(values)


def sd(values: list[float]) -> float:
    var = variance(values)
    return math.sqrt(var) if math.isfinite(var) else math.nan


def codon_order_rna() -> list[str]:
    out: list[str] = []
    for a in BASES_RNA:
        for b in BASES_RNA:
            for c in BASES_RNA:
                out.append(a + b + c)
    return out


def sense_codon_order_rna() -> list[str]:
    return [codon for codon in codon_order_rna() if CODON_TO_AA[codon] != "*"]


def families_by_aa(codons: list[str]) -> dict[str, list[str]]:
    families: dict[str, list[str]] = defaultdict(list)
    for codon in codons:
        families[CODON_TO_AA[codon]].append(codon)
    return dict(families)


def complement(base: str) -> str | None:
    return {"A": "U", "U": "A", "T": "A", "C": "G", "G": "C", "I": None}.get(base)


def revcomp_rna(seq: str) -> str:
    return "".join({"A": "U", "U": "A", "T": "A", "C": "G", "G": "C"}[base] for base in reversed(seq.upper()))


def normalize_anticodon(raw: str) -> str | None:
    seq = raw.strip().upper().replace("T", "U")
    seq = re.sub(r"[^ACGUI]", "", seq)
    return seq if len(seq) == 3 else None


def stable_sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def fetch_bytes(url: str, timeout: int = 120, attempts: int = 3) -> tuple[bytes, dict[str, object]]:
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
        except Exception as exc:  # network surface
            last_error = f"{type(exc).__name__}:{exc}"
        time.sleep(NCBI_DELAY_SECONDS * attempt * 2.0)
    return b"", {"url": url, "reachable": False, "blocked": True, "error": last_error or "fetch_failed"}


def https_ftp_path(ftp_path: str) -> str:
    if ftp_path.startswith("ftp://"):
        return "https://" + ftp_path[len("ftp://") :]
    return ftp_path


def gbff_url(ftp_path: str) -> str:
    base = https_ftp_path(ftp_path).rstrip("/")
    name = base.rsplit("/", 1)[-1]
    return f"{base}/{name}_genomic.gbff.gz"


def fetch_gbff_text(ftp_path: str) -> tuple[str, dict[str, object]]:
    payload, contact = fetch_bytes(gbff_url(ftp_path))
    time.sleep(NCBI_DELAY_SECONDS)
    if not payload:
        return "", contact
    try:
        text = gzip.decompress(payload).decode("utf-8", "replace")
    except Exception as exc:
        contact["decompress_error"] = f"{type(exc).__name__}:{exc}"
        return "", contact
    contact["decompressed_chars"] = len(text)
    return text, contact


def split_top_level_commas(text: str) -> list[str]:
    parts: list[str] = []
    depth = 0
    start = 0
    for idx, char in enumerate(text):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif char == "," and depth == 0:
            parts.append(text[start:idx])
            start = idx + 1
    parts.append(text[start:])
    return [part.strip() for part in parts if part.strip()]


def reverse_complement_dna(seq: str) -> str:
    return seq.translate(str.maketrans("ACGTacgt", "TGCAtgca"))[::-1].upper()


def extract_location_sequence(location: str, genome_seq: str) -> str | None:
    loc = re.sub(r"\s+", "", location)
    if not loc or any(token in loc for token in ("<", ">", "^", "?")):
        return None
    if loc.startswith("complement(") and loc.endswith(")"):
        inner = loc[len("complement(") : -1]
        seq = extract_location_sequence(inner, genome_seq)
        return reverse_complement_dna(seq) if seq is not None else None
    if loc.startswith("join(") and loc.endswith(")"):
        chunks: list[str] = []
        for part in split_top_level_commas(loc[len("join(") : -1]):
            seq = extract_location_sequence(part, genome_seq)
            if seq is None:
                return None
            chunks.append(seq)
        return "".join(chunks)
    if ":" in loc:
        return None
    match = re.fullmatch(r"(\d+)\.\.(\d+)", loc)
    if match:
        start = int(match.group(1))
        end = int(match.group(2))
    else:
        single = re.fullmatch(r"(\d+)", loc)
        if not single:
            return None
        start = end = int(single.group(1))
    if start < 1 or end < start or end > len(genome_seq):
        return None
    return genome_seq[start - 1 : end].upper()


def genbank_records(text: str) -> list[str]:
    return [record for record in text.split("\n//") if "LOCUS" in record and "ORIGIN" in record]


def origin_sequence(record: str) -> str:
    match = re.search(r"\nORIGIN\s*\n(.*)", record, flags=re.DOTALL)
    if not match:
        return ""
    return re.sub(r"[^A-Za-z]", "", match.group(1)).upper()


def feature_blocks(record: str) -> list[tuple[str, str, str]]:
    feature_match = re.search(r"\nFEATURES\s+Location/Qualifiers\n(.*?)\nORIGIN", record, flags=re.DOTALL)
    if not feature_match:
        return []
    blocks: list[tuple[str, str, str]] = []
    current_key: str | None = None
    current_lines: list[str] = []
    for line in feature_match.group(1).splitlines():
        match = re.match(r"^     (\S+)\s+(.+)$", line)
        if match:
            if current_key is not None:
                location, text = split_feature_text(current_lines)
                blocks.append((current_key, location, text))
            current_key = match.group(1)
            current_lines = [match.group(2).rstrip()]
        elif current_key is not None:
            current_lines.append(line[21:].rstrip() if len(line) >= 21 else line.strip())
    if current_key is not None:
        location, text = split_feature_text(current_lines)
        blocks.append((current_key, location, text))
    return blocks


def split_feature_text(lines: list[str]) -> tuple[str, str]:
    location_parts: list[str] = []
    qual_parts: list[str] = []
    in_qualifiers = False
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("/"):
            in_qualifiers = True
        if in_qualifiers:
            qual_parts.append(stripped)
        else:
            location_parts.append(stripped)
    return "".join(location_parts), "\n".join(qual_parts)


def qualifier_value(text: str, name: str) -> str | None:
    match = re.search(rf"/{re.escape(name)}=(\"(?:[^\"]|\"\")*\"|[^\s/]+)", text, flags=re.DOTALL)
    if not match:
        return None
    value = match.group(1).strip()
    if value.startswith('"') and value.endswith('"'):
        value = value[1:-1]
    return re.sub(r"\s+", " ", value).strip()


def parse_trna_feature(text: str) -> tuple[str, str] | None:
    lowered = text.lower()
    if "/pseudo" in lowered or "/pseudogene" in lowered or "suppressor" in lowered:
        return None
    if re.search(r"\b(sec|selenocys|pyl|pyrrolys)\b", lowered):
        return None
    aa3: str | None = None
    seq: str | None = None
    anticodon = qualifier_value(text, "anticodon")
    if anticodon:
        aa_match = re.search(r"aa:([A-Za-z]+)", anticodon)
        seq_match = re.search(r"seq:([A-Za-z]+)", anticodon)
        if aa_match:
            aa3 = aa_match.group(1).title()[:3]
        if seq_match:
            seq = normalize_anticodon(seq_match.group(1))
    product = qualifier_value(text, "product") or ""
    if not aa3:
        product_match = re.search(r"tRNA-(?:initiator\s+)?([A-Za-z]{3})", product)
        if product_match:
            aa3 = product_match.group(1).title()
    if not seq:
        product_match = re.search(r"tRNA-(?:initiator\s+)?[A-Za-z]{3}\(([A-Za-z]{3})\)", product)
        if product_match:
            seq = normalize_anticodon(product_match.group(1))
    if not seq:
        note = qualifier_value(text, "note") or ""
        note_match = re.search(r"anticodon\s+([A-Za-z]{3})", note, flags=re.IGNORECASE)
        if note_match:
            seq = normalize_anticodon(note_match.group(1))
    if not aa3 or aa3 not in AA3_TO_1 or not seq:
        return None
    return AA3_TO_1[aa3], seq


def count_from_gbff(text: str) -> tuple[dict[str, int], dict[str, Counter[str]], dict[str, object]]:
    sense_codons = sense_codon_order_rna()
    counts = {codon: 0 for codon in sense_codons}
    trna_by_aa: dict[str, Counter[str]] = defaultdict(Counter)
    stop_codons = {codon.replace("U", "T") for codon, aa in CODON_TO_AA.items() if aa == "*"}
    transl_tables: Counter[str] = Counter()
    n_records = 0
    n_cds_features = 0
    n_cds_accepted = 0
    skipped_cds = Counter()
    n_trna_features = 0
    n_trna_with_anticodon = 0
    for record in genbank_records(text):
        n_records += 1
        genome_seq = origin_sequence(record)
        if not genome_seq:
            continue
        for key, location, feature_text in feature_blocks(record):
            if key == "CDS":
                n_cds_features += 1
                table = qualifier_value(feature_text, "transl_table") or "11"
                transl_tables[str(table)] += 1
                if str(table) not in {"1", "11"}:
                    skipped_cds["translation_table"] += 1
                    continue
                if "/pseudo" in feature_text.lower() or "/pseudogene" in feature_text.lower():
                    skipped_cds["pseudo"] += 1
                    continue
                seq = extract_location_sequence(location, genome_seq)
                if seq is None:
                    skipped_cds["location"] += 1
                    continue
                if len(seq) < 3 or len(seq) % 3 != 0:
                    skipped_cds["length"] += 1
                    continue
                if any(base not in {"A", "C", "G", "T"} for base in seq):
                    skipped_cds["ambiguous"] += 1
                    continue
                codons = [seq[offset : offset + 3] for offset in range(0, len(seq), 3)]
                if codons and codons[-1] in stop_codons:
                    codons = codons[:-1]
                if any(codon in stop_codons for codon in codons):
                    skipped_cds["internal_stop"] += 1
                    continue
                n_cds_accepted += 1
                for codon_dna in codons:
                    codon_rna = codon_dna.replace("T", "U")
                    if codon_rna in counts:
                        counts[codon_rna] += 1
            elif key == "tRNA":
                n_trna_features += 1
                parsed = parse_trna_feature(feature_text)
                if parsed is None:
                    continue
                aa, anticodon = parsed
                n_trna_with_anticodon += 1
                trna_by_aa[aa][anticodon] += 1
    meta = {
        "n_genbank_records": n_records,
        "n_cds_features": n_cds_features,
        "n_complete_cds": n_cds_accepted,
        "total_sense_codons": int(sum(counts.values())),
        "skipped_cds": dict(sorted(skipped_cds.items())),
        "n_trna_features": n_trna_features,
        "n_trna_with_anticodon": n_trna_with_anticodon,
        "n_anticodon_isotypes": sum(len(counter) for counter in trna_by_aa.values()),
        "aa_trna_counts": {aa: int(sum(counter.values())) for aa, counter in sorted(trna_by_aa.items())},
        "transl_table_counts": dict(sorted(transl_tables.items(), key=lambda item: int(item[0]))),
    }
    return counts, trna_by_aa, meta


def anticodon_decodes(anticodon: str, codon: str, mode: str) -> float:
    anti = anticodon.upper().replace("T", "U")
    codon = codon.upper().replace("T", "U")
    if len(anti) != 3 or len(codon) != 3:
        return 0.0
    if complement(anti[2]) != codon[0] or complement(anti[1]) != codon[1]:
        return 0.0
    first = anti[0]
    third = codon[2]
    if mode == "exact_only":
        return 1.0 if revcomp_rna(codon) == anti else 0.0
    if mode == "loose_superwobble" and first == "U":
        return 1.0
    allowed = {
        "A": {"U"},
        "C": {"G"},
        "G": {"C", "U"},
        "U": {"A", "G"},
        "I": {"A", "C", "U"},
    }
    return 1.0 if third in allowed.get(first, set()) else 0.0


def smooth_supply(trna_by_aa: dict[str, Counter[str]], codons: list[str], mode: str) -> list[float]:
    values: list[float] = []
    for codon in codons:
        aa = CODON_TO_AA[codon]
        total = 0.0
        for anticodon, count in trna_by_aa.get(aa, Counter()).items():
            total += int(count) * anticodon_decodes(anticodon, codon, mode)
        values.append(math.log1p(total))
    return values


def boundary_vector(trna_by_aa: dict[str, Counter[str]], codons: list[str]) -> list[float]:
    out: list[float] = []
    for codon in codons:
        aa = CODON_TO_AA[codon]
        out.append(0.0 if revcomp_rna(codon) in trna_by_aa.get(aa, Counter()) else 1.0)
    return out


def gc3_vector(codons: list[str]) -> list[float]:
    return [1.0 if codon[2] in {"G", "C"} else 0.0 for codon in codons]


def family_variable_boundary_codons(boundary: list[float], codons: list[str]) -> int:
    index = {codon: idx for idx, codon in enumerate(codons)}
    total = 0
    for family in families_by_aa(codons).values():
        values = {boundary[index[codon]] for codon in family}
        if len(values) >= 2:
            total += len(family)
    return total


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def pearson(left: list[float], right: list[float]) -> float | None:
    if len(left) != len(right) or len(left) < 3:
        return None
    lm = mean(left)
    rm = mean(right)
    x = [value - lm for value in left]
    y = [value - rm for value in right]
    denom = math.sqrt(dot(x, x) * dot(y, y))
    if denom <= TOL:
        return None
    return dot(x, y) / denom


def solve_linear(matrix: list[list[float]], rhs: list[float]) -> list[float] | None:
    n = len(rhs)
    aug = [row[:] + [rhs[idx]] for idx, row in enumerate(matrix)]
    for col in range(n):
        pivot = max(range(col, n), key=lambda row: abs(aug[row][col]))
        if abs(aug[pivot][col]) <= 1.0e-10:
            return None
        if pivot != col:
            aug[col], aug[pivot] = aug[pivot], aug[col]
        pivot_value = aug[col][col]
        for j in range(col, n + 1):
            aug[col][j] /= pivot_value
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor == 0.0:
                continue
            for j in range(col, n + 1):
                aug[row][j] -= factor * aug[col][j]
    return [aug[row][n] for row in range(n)]


def ols_residuals(y: list[float], columns: list[list[float]]) -> tuple[list[float], list[float]] | None:
    if not columns:
        center = mean(y)
        return [center], [value - center for value in y]
    xcols = [[1.0 for _ in y]] + [col[:] for col in columns]
    p = len(xcols)
    xtx = [[dot(xcols[i], xcols[j]) for j in range(p)] for i in range(p)]
    xty = [dot(xcols[i], y) for i in range(p)]
    beta = solve_linear(xtx, xty)
    if beta is None:
        return None
    fitted = [sum(beta[j] * xcols[j][i] for j in range(p)) for i in range(len(y))]
    return beta, [y[i] - fitted[i] for i in range(len(y))]


def collinearity_diagnostics(boundary: list[float], supply: list[float], gc3: list[float]) -> dict[str, object]:
    var_b = variance(boundary)
    residual_result = ols_residuals(boundary, [supply, gc3])
    if var_b <= TOL or residual_result is None:
        residual_var_ratio = 0.0
        residual_sd = 0.0
        vif = math.inf
    else:
        _beta, residuals = residual_result
        residual_var = variance(residuals)
        residual_var_ratio = residual_var / var_b if var_b > TOL else 0.0
        residual_sd = math.sqrt(max(residual_var, 0.0))
        vif = 1.0 / residual_var_ratio if residual_var_ratio > TOL else math.inf
    return {
        "corr_B_S_main": round_float(pearson(boundary, supply)),
        "vif_B_given_S_main_GC3": round_float(vif),
        "residual_sd_B_given_S_main_GC3": round_float(residual_sd),
        "residual_variance_ratio_B_given_S_main_GC3": round_float(residual_var_ratio),
    }


def candidate_summaries() -> tuple[list[dict[str, object]], dict[str, object]]:
    cached_candidates: list[dict[str, object]] = []
    if E1_PANEL_PATH.exists():
        try:
            panel = json.loads(E1_PANEL_PATH.read_text(encoding="utf-8"))
            for row in panel.get("organisms", []):
                if isinstance(row, dict) and row.get("ftp_path_refseq") and row.get("genus"):
                    cached_candidates.append(
                        {
                            "assembly_accession": row.get("assembly_accession"),
                            "assembly_name": row.get("assembly_name", ""),
                            "assembly_status": "Complete Genome",
                            "organism": row.get("organism"),
                            "species_name": row.get("species_name") or row.get("organism"),
                            "genus": row.get("genus"),
                            "taxid": row.get("taxid", ""),
                            "ftp_path_refseq": row.get("ftp_path_refseq"),
                            "candidate_source": str(E1_PANEL_PATH),
                        }
                    )
        except json.JSONDecodeError:
            cached_candidates = []
    source_status: dict[str, object] = {"cached_e1_panel_candidates": len(cached_candidates)}
    if len(cached_candidates) >= TARGET_GENERA:
        return cached_candidates, source_status
    fresh, fresh_status = E1_FETCH.candidate_summaries(retmax=300)
    seen = {str(row.get("assembly_accession")) for row in cached_candidates}
    for row in fresh:
        if str(row.get("assembly_accession")) not in seen:
            cached_candidates.append(row)
            seen.add(str(row.get("assembly_accession")))
    source_status["ncbi_candidate_status"] = fresh_status
    return cached_candidates, source_status


def evaluate_summary(summary: dict[str, object], codons: list[str]) -> dict[str, object]:
    text, contact = fetch_gbff_text(str(summary["ftp_path_refseq"]))
    if not text:
        return {
            **summary,
            "gbff_contact": contact,
            "usable_for_gate": False,
            "reject_reason": "gbff_fetch_failed",
        }
    counts, trna_by_aa, meta = count_from_gbff(text)
    boundary = boundary_vector(trna_by_aa, codons)
    supply_main = smooth_supply(trna_by_aa, codons, "main")
    gc3 = gc3_vector(codons)
    variable_codons = family_variable_boundary_codons(boundary, codons)
    diagnostics = collinearity_diagnostics(boundary, supply_main, gc3)
    table_counts = meta.get("transl_table_counts", {})
    observed_tables = sorted(int(key) for key in table_counts) if isinstance(table_counts, dict) and table_counts else []
    ok_tables = bool(observed_tables) and set(observed_tables) <= {1, 11}
    reject_reasons = []
    if not ok_tables:
        reject_reasons.append("translation_table_not_standard_bacterial_archaeal")
    if int(meta["n_complete_cds"]) < MIN_COMPLETE_CDS:
        reject_reasons.append("too_few_cds")
    if int(meta["total_sense_codons"]) < MIN_SENSE_CODONS:
        reject_reasons.append("too_few_sense_codons")
    if int(meta["n_trna_with_anticodon"]) <= 0:
        reject_reasons.append("no_gbff_trna_anticodon")
    if variable_codons < MIN_VARIABLE_BOUNDARY_CODONS:
        reject_reasons.append("too_little_within_family_boundary_variation")
    residual_sd = float(diagnostics["residual_sd_B_given_S_main_GC3"] or 0.0)
    residual_ratio = float(diagnostics["residual_variance_ratio_B_given_S_main_GC3"] or 0.0)
    if residual_sd < MIN_RESIDUAL_SD or residual_ratio < MIN_RESIDUAL_VARIANCE_RATIO:
        reject_reasons.append("boundary_collinear_with_supply_gc3")
    return {
        **summary,
        "gbff_contact": contact,
        "gbff_sha256_text": stable_sha(text),
        "codon_counts_rna": counts,
        "trna_anticodon_counts_by_aa_rna": {
            aa: dict(sorted(counter.items())) for aa, counter in sorted(trna_by_aa.items())
        },
        "gbff_meta": meta,
        "variable_boundary_codons": variable_codons,
        "boundary_ones": int(sum(boundary)),
        "boundary_zeros": int(len(boundary) - sum(boundary)),
        "collinearity": diagnostics,
        "usable_for_gate": not reject_reasons,
        "reject_reason": ",".join(reject_reasons) if reject_reasons else "",
    }


def compact_attempt(row: dict[str, object]) -> dict[str, object]:
    return {
        "assembly_accession": row.get("assembly_accession"),
        "organism": row.get("organism"),
        "genus": row.get("genus"),
        "usable_for_gate": row.get("usable_for_gate"),
        "reject_reason": row.get("reject_reason"),
        "n_complete_cds": row.get("gbff_meta", {}).get("n_complete_cds") if isinstance(row.get("gbff_meta"), dict) else None,
        "total_sense_codons": row.get("gbff_meta", {}).get("total_sense_codons") if isinstance(row.get("gbff_meta"), dict) else None,
        "n_trna_with_anticodon": row.get("gbff_meta", {}).get("n_trna_with_anticodon") if isinstance(row.get("gbff_meta"), dict) else None,
        "variable_boundary_codons": row.get("variable_boundary_codons"),
        "boundary_ones": row.get("boundary_ones"),
        "boundary_zeros": row.get("boundary_zeros"),
        "collinearity": row.get("collinearity"),
    }


def aggregate_collinearity(rows: list[dict[str, object]]) -> dict[str, object]:
    def values(key: str) -> list[float]:
        out = []
        for row in rows:
            col = row.get("collinearity")
            if isinstance(col, dict) and col.get(key) is not None:
                value = float(col[key])
                if math.isfinite(value):
                    out.append(value)
        return out

    corr = values("corr_B_S_main")
    vif = values("vif_B_given_S_main_GC3")
    rsd = values("residual_sd_B_given_S_main_GC3")
    rvr = values("residual_variance_ratio_B_given_S_main_GC3")
    return {
        "corr_B_S_main_mean": round_float(mean(corr)),
        "corr_B_S_main_min": round_float(min(corr) if corr else math.nan),
        "corr_B_S_main_max": round_float(max(corr) if corr else math.nan),
        "vif_B_given_S_main_GC3_mean": round_float(mean(vif)),
        "vif_B_given_S_main_GC3_max": round_float(max(vif) if vif else math.nan),
        "residual_sd_B_given_S_main_GC3_min": round_float(min(rsd) if rsd else math.nan),
        "residual_sd_B_given_S_main_GC3_mean": round_float(mean(rsd)),
        "residual_variance_ratio_B_given_S_main_GC3_min": round_float(min(rvr) if rvr else math.nan),
        "residual_variance_ratio_B_given_S_main_GC3_mean": round_float(mean(rvr)),
    }


def build_probe(force_refresh: bool = False) -> dict[str, object]:
    if PROBE_CACHE_PATH.exists() and not force_refresh:
        cached = json.loads(PROBE_CACHE_PATH.read_text(encoding="utf-8"))
        if cached.get("record_schema") == "tracka_exact_cognate_wobble_boundary_probe":
            return cached
    codons = sense_codon_order_rna()
    candidates, source_status = candidate_summaries()
    attempts: list[dict[str, object]] = []
    usable: list[dict[str, object]] = []
    seen_genera: set[str] = set()
    for summary in candidates:
        genus = str(summary.get("genus") or "")
        if not genus or genus in seen_genera:
            continue
        seen_genera.add(genus)
        row = evaluate_summary(summary, codons)
        attempts.append(row)
        if row.get("usable_for_gate"):
            usable.append(row)
        if len(usable) >= TARGET_GENERA:
            break
    gate_passed = len(usable) >= MIN_GATE_GENERA and all(
        float(row["collinearity"]["residual_sd_B_given_S_main_GC3"]) >= MIN_RESIDUAL_SD
        and float(row["collinearity"]["residual_variance_ratio_B_given_S_main_GC3"]) >= MIN_RESIDUAL_VARIANCE_RATIO
        for row in usable
    )
    panel = {
        "record_schema": "tracka_exact_cognate_wobble_boundary_probe",
        "generated_at": now_iso(),
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "status": "gate_passed" if gate_passed else "needs_external",
        "gate_passed": gate_passed,
        "gate_rule": {
            "min_gate_genera": MIN_GATE_GENERA,
            "target_genera": TARGET_GENERA,
            "min_complete_cds": MIN_COMPLETE_CDS,
            "min_sense_codons": MIN_SENSE_CODONS,
            "min_variable_boundary_codons": MIN_VARIABLE_BOUNDARY_CODONS,
            "min_residual_sd_B_given_S_main_GC3": MIN_RESIDUAL_SD,
            "min_residual_variance_ratio_B_given_S_main_GC3": MIN_RESIDUAL_VARIANCE_RATIO,
            "one_reference_or_representative_per_genus": True,
            "source_file": "*_genomic.gbff.gz",
        },
        "reason": (
            "yield and B_o-vs-S_o collinearity gate passed"
            if gate_passed
            else "yield or B_o-vs-S_o collinearity gate did not pass; Track-A boundary is descriptive under this carrier"
        ),
        "source_status": source_status,
        "sense_codon_order_rna": codons,
        "n_attempted": len(attempts),
        "n_gate_genera": len(usable),
        "attempts_compact": [compact_attempt(row) for row in attempts],
        "usable_genomes": usable,
        "collinearity_summary": aggregate_collinearity(usable),
        "provenance": {
            "refseq_complete_bacteria_archaea": True,
            "gbff_single_source_for_cds_and_trna": True,
            "not_causal": True,
            "not_codon_E1": True,
            "not_edge_hiding": True,
            "not_Window6": True,
        },
        "cache_path": str(PROBE_CACHE_PATH),
    }
    PROBE_CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    PROBE_CACHE_PATH.write_text(json.dumps(panel, ensure_ascii=True, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return panel


def main() -> None:
    force = "--refresh" in sys.argv
    panel = build_probe(force_refresh=force)
    for row in panel.get("attempts_compact", []):
        print(json.dumps({"source": "refseq_gbff_probe", **row}, ensure_ascii=True, sort_keys=True))
    final = {
        "status": panel["status"],
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "n_gate_genera": panel["n_gate_genera"],
        "gate_rule": panel["gate_rule"],
        "collinearity_summary": panel["collinearity_summary"],
        "reason": panel["reason"],
        "cache_path": panel["cache_path"],
        "note": (
            "Track-A exact-cognate boundary probe for the fibonacci homeless phenomenon; "
            "B_o-vs-S_o collinearity is checked before any certificate test; not causal, "
            "not codon-E1, not edge-hiding, and not Window6."
        ),
    }
    print(json.dumps(final, ensure_ascii=True, sort_keys=True, separators=(",", ":")))
    sys.exit(0 if panel["gate_passed"] else 3)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Window6 off-frame stop ambush test with exact gene-wise synonymous null."""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import combinations
import gzip
import hashlib
import json
import math
import os
import random
import re
import statistics
import sys
import time
import urllib.error
import urllib.request


EXPERIMENT_ID = "w6_offframe_stop_ambush"
CLAIM_ID = "window_codon_bridge.w6_offframe_stop_ambush"
SUMMARY_URL = os.environ.get(
    "W6AMB_ASSEMBLY_SUMMARY_URL",
    "https://ftp.ncbi.nlm.nih.gov/genomes/refseq/bacteria/assembly_summary.txt",
)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(SCRIPT_DIR)))
CACHE_DIR = os.environ.get(
    "W6AMB_CACHE_DIR",
    os.path.join(REPO_ROOT, "tools", "window_codon_bridge", "synced", "asd_w6_self_tail"),
)
MAX_GENOMES = int(os.environ.get("W6AMB_MAX_GENOMES", "0"))
FETCH_TIMEOUT = int(os.environ.get("W6AMB_FETCH_TIMEOUT", "60"))
FETCH_ATTEMPTS = int(os.environ.get("W6AMB_FETCH_ATTEMPTS", "3"))
NCBI_DELAY_SECONDS = float(os.environ.get("W6AMB_NCBI_DELAY_SECONDS", "0.34"))
BOOTSTRAPS = int(os.environ.get("W6AMB_BOOTSTRAPS", "10000"))
DECOY_POOLS = int(os.environ.get("W6AMB_DECOY_POOLS", "10000"))
# The exact composition-matching constraints (GC-count multiset [0,1,1], total
# purine within +/-1, total T within +/-1, no stop overlap) admit a bounded
# universe of distinct valid pseudo-stop triples; exhaustive enumeration yields
# 624 sets, which is the mathematical ceiling, not a generator limitation. A
# top-1% specificity test over the full enumerated population is rigorous well
# below this ceiling (p_decoy resolution = 1/(N+1)), so the derivation gate
# requires only a floor that keeps the top-1% test meaningful.
MIN_DISTINCT_DECOY_SETS = int(os.environ.get("W6AMB_MIN_DISTINCT_DECOY_SETS", "100"))
SELFTEST_SHUFFLES = int(os.environ.get("W6AMB_SELFTEST_SHUFFLES", "20000"))
MC_AUDIT_SHUFFLES = int(os.environ.get("W6AMB_MC_AUDIT_SHUFFLES", "20000"))
MC_AUDIT_GENES = int(os.environ.get("W6AMB_MC_AUDIT_GENES", "20"))
USER_AGENT = "w6-offframe-stop-ambush-exact-null"
PSEUDO = 0.5
EPS = 1.0e-12
DECOY_VARIANCE_SAMPLE = 128

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
STOP_CODONS = frozenset(c for c, aa in CODON_TO_AA.items() if aa == "*")
SENSE_CODONS = tuple(sorted(c for c, aa in CODON_TO_AA.items() if aa != "*"))
CODON_INDEX = {codon: i for i, codon in enumerate(SENSE_CODONS)}
INDEX_CODON = {i: codon for codon, i in CODON_INDEX.items()}
N_CODONS = len(SENSE_CODONS)
N_PAIRS = N_CODONS * N_CODONS
SYNONYMS = {}
for _codon, _aa in CODON_TO_AA.items():
    if _aa != "*":
        SYNONYMS.setdefault(_aa, []).append(_codon)
SYNONYMS = {aa: tuple(sorted(codons)) for aa, codons in SYNONYMS.items()}
AA_PAIRS = tuple((a, b) for a in sorted(SYNONYMS) for b in sorted(SYNONYMS))
DNA_TO_RNA = str.maketrans("ACGTacgt", "ACGUACGU")
BASES_RNA = set("ACGU")


def stable_seed(text):
    return int.from_bytes(hashlib.sha256(text.encode("utf-8")).digest()[:16], "big")


def sha256_hex(payload):
    return hashlib.sha256(payload).hexdigest()


def round_float(value, digits=12):
    if value is None:
        return None
    if not math.isfinite(float(value)):
        return value
    out = round(float(value), digits)
    return 0.0 if out == -0.0 else out


def mean(values):
    return sum(values) / len(values) if values else 0.0


def median(values):
    return statistics.median(values) if values else 0.0


def stdev(values):
    return statistics.stdev(values) if len(values) >= 2 else 0.0


def percentile(sorted_values, q):
    if not sorted_values:
        return 0.0
    if len(sorted_values) == 1:
        return sorted_values[0]
    pos = (len(sorted_values) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return sorted_values[lo]
    frac = pos - lo
    return sorted_values[lo] * (1.0 - frac) + sorted_values[hi] * frac


def clean_json(value):
    if isinstance(value, dict):
        return {str(k): clean_json(v) for k, v in value.items() if k != "log_values"}
    if isinstance(value, list) or isinstance(value, tuple):
        return [clean_json(v) for v in value]
    if isinstance(value, float):
        if math.isnan(value):
            return "nan"
        if math.isinf(value):
            return "inf" if value > 0 else "-inf"
        return round_float(value)
    return value


def emit(verdict, **fields):
    payload = {"verdict": verdict, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(clean_json(payload), ensure_ascii=True, sort_keys=True, separators=(",", ":")))
    sys.exit(0)


def emit_error(message, **fields):
    payload = {"error": message, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(clean_json(payload), ensure_ascii=True, sort_keys=True, separators=(",", ":")))
    sys.exit(1)


def request_bytes(url):
    last = "fetch_failed"
    for attempt in range(1, FETCH_ATTEMPTS + 1):
        req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        try:
            with urllib.request.urlopen(req, timeout=FETCH_TIMEOUT) as response:
                payload = response.read()
                return payload, {
                    "url": url,
                    "reachable": True,
                    "http_status": int(getattr(response, "status", 200)),
                    "byte_size": len(payload),
                    "sha256": sha256_hex(payload),
                    "attempts": attempt,
                }
        except urllib.error.HTTPError as exc:
            last = "HTTPError:%s" % exc.code
            if exc.code not in {429, 500, 502, 503, 504}:
                break
        except urllib.error.URLError as exc:
            last = "URLError:%s" % exc.reason
        except TimeoutError:
            last = "TimeoutError"
        time.sleep(NCBI_DELAY_SECONDS * attempt)
    return b"", {"url": url, "reachable": False, "error": last, "attempts": FETCH_ATTEMPTS}


def cached_url_bytes(url, cache_path):
    parent = os.path.dirname(cache_path)
    if parent:
        os.makedirs(parent, exist_ok=True)
    if os.path.exists(cache_path) and os.path.getsize(cache_path) > 0:
        with open(cache_path, "rb") as handle:
            payload = handle.read()
        return payload, {
            "url": url,
            "reachable": True,
            "on_disk_cache_hit": True,
            "byte_size": len(payload),
            "sha256": sha256_hex(payload),
            "cache_path": cache_path,
        }
    payload, contact = request_bytes(url)
    if payload:
        with open(cache_path, "wb") as handle:
            handle.write(payload)
        contact["cache_path"] = cache_path
        contact["on_disk_cache_hit"] = False
    return payload, contact


def read_text_cached(url, cache_name):
    payload, contact = cached_url_bytes(url, os.path.join(CACHE_DIR, cache_name))
    if not payload:
        return "", contact
    return payload.decode("utf-8", "replace"), contact


def https_ftp_path(value):
    value = value.strip()
    if value.startswith("ftp://"):
        return "https://" + value[len("ftp://"):]
    return value


def assembly_basename(ftp_path):
    return ftp_path.rstrip("/").split("/")[-1]


def parse_date(value):
    parts = re.findall(r"\d+", value or "")
    if len(parts) >= 3:
        return tuple(int(x) for x in parts[:3])
    return (0, 0, 0)


def parse_assembly_summary(text):
    header = None
    rows = []
    for raw in text.splitlines():
        if not raw.strip():
            continue
        if raw.startswith("#"):
            line = raw.lstrip("#").strip()
            if line.startswith("assembly_accession"):
                header = line.split("\t")
            continue
        fields = raw.split("\t")
        if header and len(fields) >= len(header):
            row = dict(zip(header, fields))
        else:
            row = {
                "assembly_accession": fields[0] if len(fields) > 0 else "",
                "refseq_category": fields[4] if len(fields) > 4 else "na",
                "species_taxid": fields[6] if len(fields) > 6 else "",
                "organism_name": fields[7] if len(fields) > 7 else "",
                "version_status": fields[10] if len(fields) > 10 else "",
                "assembly_level": fields[11] if len(fields) > 11 else "",
                "seq_rel_date": fields[14] if len(fields) > 14 else "",
                "ftp_path": fields[19] if len(fields) > 19 else "",
                "excluded_from_refseq": fields[20] if len(fields) > 20 else "",
            }
        rows.append(row)
    return rows


def category_rank(value):
    return {"reference genome": 0, "representative genome": 1}.get((value or "").lower(), 2)


def select_species_assemblies(rows):
    by_species = defaultdict(list)
    for row in rows:
        if (row.get("version_status") or "").lower() != "latest":
            continue
        if row.get("assembly_level") != "Complete Genome":
            continue
        if (row.get("excluded_from_refseq") or "").strip() not in {"", "na"}:
            continue
        ftp_path = https_ftp_path(row.get("ftp_path") or "")
        if not ftp_path:
            continue
        row = dict(row)
        row["ftp_path"] = ftp_path
        by_species[row.get("species_taxid") or row.get("assembly_accession")].append(row)
    selected = []
    for _, items in sorted(by_species.items()):
        items.sort(key=lambda r: (
            category_rank(r.get("refseq_category")),
            tuple(-x for x in parse_date(r.get("seq_rel_date"))),
            r.get("assembly_accession") or "",
        ))
        selected.append(items[0])
    if MAX_GENOMES > 0:
        selected = selected[:MAX_GENOMES]
    return selected


def parse_md5checksums(text):
    out = {}
    for line in text.splitlines():
        parts = line.strip().split()
        if len(parts) >= 2 and re.fullmatch(r"[0-9a-fA-F]{32}", parts[0]):
            out[parts[1].lstrip("./")] = parts[0].lower()
    return out


def fetch_assembly_file(row, suffix):
    ftp_path = row["ftp_path"].rstrip("/")
    asm = assembly_basename(ftp_path)
    filename = asm + suffix
    url = ftp_path + "/" + filename
    cache_path = os.path.join(CACHE_DIR, row["assembly_accession"], filename)
    payload, contact = cached_url_bytes(url, cache_path)
    return filename, payload, contact


def fetch_md5checksums(row):
    ftp_path = row["ftp_path"].rstrip("/")
    filename = "md5checksums.txt"
    url = ftp_path + "/" + filename
    cache_path = os.path.join(CACHE_DIR, row["assembly_accession"], filename)
    payload, contact = cached_url_bytes(url, cache_path)
    return filename, payload, contact


def validate_md5(filename, payload, md5s):
    if not md5s:
        return True, "no_md5_manifest"
    expected = md5s.get(filename) or md5s.get(os.path.basename(filename))
    if not expected:
        return False, "missing_md5_entry"
    observed = hashlib.md5(payload).hexdigest()
    return observed == expected, "md5_ok" if observed == expected else "md5_mismatch"


def iter_fasta_bytes(payload, gzipped=True):
    if gzipped:
        text = gzip.decompress(payload).decode("utf-8", "replace")
    else:
        text = payload.decode("utf-8", "replace")
    header = None
    chunks = []
    for line in text.splitlines():
        if line.startswith(">"):
            if header is not None:
                yield header, "".join(chunks)
            header = line[1:].strip()
            chunks = []
        else:
            chunks.append(line.strip())
    if header is not None:
        yield header, "".join(chunks)


def to_rna(seq):
    return seq.translate(DNA_TO_RNA).upper()


def zero_matrix():
    return [0.0] * N_PAIRS


def add_matrix(dst, src):
    for i, value in enumerate(src):
        if value:
            dst[i] += value


def matrix_sum(matrix):
    return sum(matrix)


def finite_matrix(matrix):
    return all(math.isfinite(float(value)) for value in matrix)


def pair_index(c1, c2):
    return CODON_INDEX[c1] * N_CODONS + CODON_INDEX[c2]


def codons_from_rna(seq):
    return [seq[i:i + 3] for i in range(0, len(seq) - 2, 3)]


def aa_seq(codons):
    return "".join(CODON_TO_AA.get(c, "X") for c in codons)


def parse_translation_table(header):
    m = re.search(r"\[transl_table=(\d+)\]", header)
    if m:
        return int(m.group(1))
    m = re.search(r"transl_table[ =](\d+)", header)
    if m:
        return int(m.group(1))
    return None


def qc_cds_records(payload):
    records = []
    stats = Counter()
    for header, seq in iter_fasta_bytes(payload, gzipped=True):
        stats["total_cds_records"] += 1
        table = parse_translation_table(header)
        if table is not None and table != 11:
            stats["non_table_11_annotation"] += 1
            continue
        rna = to_rna(seq)
        if set(rna) - BASES_RNA:
            stats["ambiguous"] += 1
            continue
        if len(rna) % 3 != 0:
            stats["not_divisible_by_3"] += 1
            continue
        codon_list = codons_from_rna(rna)
        if not codon_list:
            stats["empty"] += 1
            continue
        aas = [CODON_TO_AA.get(c, "X") for c in codon_list]
        if "X" in aas:
            stats["unknown_codon"] += 1
            continue
        if "*" in aas[:-1]:
            stats["internal_stop"] += 1
            continue
        if aas[-1] == "*":
            codon_list = codon_list[:-1]
            aas = aas[:-1]
        if len(codon_list) < 60:
            stats["too_short_after_stop_removal"] += 1
            continue
        records.append({
            "header": header,
            "codons": codon_list,
            "aa": "".join(aas),
            "table_11_annotated": table == 11,
            "table_11_inferable": table is None,
            "length_nt": len(codon_list) * 3,
        })
    stats["qc_passing"] = len(records)
    stats["table_11_annotated_or_inferable"] = sum(
        1 for r in records if r["table_11_annotated"] or r["table_11_inferable"]
    )
    return records, dict(stats)


def internal_pair_starts(n_codons):
    return range(15, n_codons - 11)


def internal_usage_positions(n_codons):
    return range(15, n_codons - 10)


def usage_counts(codon_list, scope):
    counts_by_aa = defaultdict(Counter)
    if scope == "full":
        positions = range(len(codon_list))
    elif scope == "internal":
        positions = internal_usage_positions(len(codon_list))
    else:
        raise ValueError("unknown usage scope: %s" % scope)
    for pos in positions:
        codon = codon_list[pos]
        counts_by_aa[CODON_TO_AA[codon]][codon] += 1
    totals_by_aa = {aa: sum(counts.values()) for aa, counts in counts_by_aa.items()}
    return counts_by_aa, totals_by_aa


def gene_observed_and_expected(codon_list, usage_scope="full"):
    observed = zero_matrix()
    expected = zero_matrix()
    aa_pair_counts = Counter()
    for i in internal_pair_starts(len(codon_list)):
        c1 = codon_list[i]
        c2 = codon_list[i + 1]
        observed[pair_index(c1, c2)] += 1.0
        aa_pair_counts[(CODON_TO_AA[c1], CODON_TO_AA[c2])] += 1
    counts_by_aa, totals_by_aa = usage_counts(codon_list, usage_scope)
    for (aa1, aa2), m_ab in aa_pair_counts.items():
        if aa1 != aa2:
            denom = totals_by_aa.get(aa1, 0) * totals_by_aa.get(aa2, 0)
            if denom <= 0:
                continue
            scale = float(m_ab) / float(denom)
            for c1, n1 in counts_by_aa[aa1].items():
                row = CODON_INDEX[c1] * N_CODONS
                for c2, n2 in counts_by_aa[aa2].items():
                    expected[row + CODON_INDEX[c2]] += scale * n1 * n2
        else:
            n_total = totals_by_aa.get(aa1, 0)
            denom = n_total * (n_total - 1)
            if denom <= 0:
                continue
            scale = float(m_ab) / float(denom)
            counts = counts_by_aa[aa1]
            for c1, n1 in counts.items():
                row = CODON_INDEX[c1] * N_CODONS
                for c2, n2 in counts.items():
                    numerator = n1 * (n2 - (1 if c1 == c2 else 0))
                    if numerator > 0:
                        expected[row + CODON_INDEX[c2]] += scale * numerator
    return observed, expected


def genome_pair_matrices(records):
    observed = zero_matrix()
    expected_full = zero_matrix()
    expected_internal = zero_matrix()
    for record in records:
        codon_list = record["codons"]
        o_gene, e_full_gene = gene_observed_and_expected(codon_list, "full")
        _, e_internal_gene = gene_observed_and_expected(codon_list, "internal")
        add_matrix(observed, o_gene)
        add_matrix(expected_full, e_full_gene)
        add_matrix(expected_internal, e_internal_gene)
    return observed, expected_full, expected_internal


def off_frame_triplets(c1, c2):
    window = c1 + c2
    return window[1:4], window[2:5]


def carrier_maps(stop_set):
    stop_set = frozenset(stop_set)
    k_plus = [0] * N_PAIRS
    k_minus = [0] * N_PAIRS
    k_total = [0] * N_PAIRS
    for c1 in SENSE_CODONS:
        i = CODON_INDEX[c1]
        for c2 in SENSE_CODONS:
            j = CODON_INDEX[c2]
            idx = i * N_CODONS + j
            plus, minus = off_frame_triplets(c1, c2)
            k_plus[idx] = 1 if plus in stop_set else 0
            k_minus[idx] = 1 if minus in stop_set else 0
            k_total[idx] = k_plus[idx] + k_minus[idx]
    opp_by_aa_pair = {}
    for aa1, aa2 in AA_PAIRS:
        values = [
            k_total[pair_index(c1, c2)]
            for c1 in SYNONYMS[aa1]
            for c2 in SYNONYMS[aa2]
        ]
        opp_by_aa_pair[(aa1, aa2)] = max(values) - min(values)
    opp_by_index = [False] * N_PAIRS
    for c1 in SENSE_CODONS:
        aa1 = CODON_TO_AA[c1]
        i = CODON_INDEX[c1]
        for c2 in SENSE_CODONS:
            aa2 = CODON_TO_AA[c2]
            opp_by_index[i * N_CODONS + CODON_INDEX[c2]] = opp_by_aa_pair[(aa1, aa2)] > 0
    return {
        "stop_set": tuple(sorted(stop_set)),
        "k_plus": k_plus,
        "k_minus": k_minus,
        "k_total": k_total,
        "opp_by_aa_pair": opp_by_aa_pair,
        "opp_by_index": opp_by_index,
        "opp_aa_pair_count": sum(1 for value in opp_by_aa_pair.values() if value > 0),
        "positive_state_count": sum(1 for value in k_total if value > 0),
        "plus_state_count": sum(1 for value in k_plus if value > 0),
        "minus_state_count": sum(1 for value in k_minus if value > 0),
        "max_k_total": max(k_total),
    }


TRUE_CARRIER = carrier_maps(STOP_CODONS)


def score_matrix(matrix, carrier, component="total", opportunity=True):
    key = {"total": "k_total", "plus": "k_plus", "minus": "k_minus"}[component]
    weights = carrier[key]
    opp = carrier["opp_by_index"]
    total = 0.0
    for idx, count in enumerate(matrix):
        if not count:
            continue
        if opportunity and not opp[idx]:
            continue
        if not opportunity and opp[idx]:
            continue
        weight = weights[idx]
        if weight:
            total += float(count) * weight
    return total


def ratio(obs, exp):
    return (obs + PSEUDO) / (exp + PSEUDO)


def ratio_log(obs, exp):
    return math.log(ratio(obs, exp))


def score_genome_matrices(observed, expected, expected_internal, carrier):
    observed_hs = score_matrix(observed, carrier, "total", True)
    expected_hs = score_matrix(expected, carrier, "total", True)
    expected_hs_internal = score_matrix(expected_internal, carrier, "total", True)
    observed_plus = score_matrix(observed, carrier, "plus", True)
    expected_plus = score_matrix(expected, carrier, "plus", True)
    observed_minus = score_matrix(observed, carrier, "minus", True)
    expected_minus = score_matrix(expected, carrier, "minus", True)
    observed_control = score_matrix(observed, carrier, "total", False)
    expected_control = score_matrix(expected, carrier, "total", False)
    return {
        "O_HS": observed_hs,
        "E_HS": expected_hs,
        "L_HS": ratio_log(observed_hs, expected_hs),
        "OR_HS": ratio(observed_hs, expected_hs),
        "E_HS_internal": expected_hs_internal,
        "L_HS_internal": ratio_log(observed_hs, expected_hs_internal),
        "OR_HS_internal": ratio(observed_hs, expected_hs_internal),
        "O_plus": observed_plus,
        "E_plus": expected_plus,
        "L_plus": ratio_log(observed_plus, expected_plus),
        "OR_plus": ratio(observed_plus, expected_plus),
        "O_minus": observed_minus,
        "E_minus": expected_minus,
        "L_minus": ratio_log(observed_minus, expected_minus),
        "OR_minus": ratio(observed_minus, expected_minus),
        "O_control": observed_control,
        "E_control": expected_control,
        "L_control": ratio_log(observed_control, expected_control) if expected_control > 0 or observed_control > 0 else 0.0,
        "OR_control": ratio(observed_control, expected_control) if expected_control > 0 or observed_control > 0 else 1.0,
    }


def observed_k_state_count(observed, carrier):
    return sum(
        1
        for idx, count in enumerate(observed)
        if count > 0 and carrier["k_total"][idx] == 1
    )


def gc_count(codon):
    return sum(1 for base in codon if base in "GC")


def purine_count(codon):
    return sum(1 for base in codon if base in "AG")


def t_count(codon):
    return codon.count("U")


def valid_pseudo_stop_sets():
    real_gc = sorted(gc_count(c) for c in STOP_CODONS)
    real_purines = sum(purine_count(c) for c in STOP_CODONS)
    real_t = sum(t_count(c) for c in STOP_CODONS)
    out = []
    for triple in combinations(SENSE_CODONS, 3):
        items = tuple(sorted(triple))
        if set(items) & STOP_CODONS:
            continue
        if sorted(gc_count(c) for c in items) != real_gc:
            continue
        if abs(sum(purine_count(c) for c in items) - real_purines) > 1:
            continue
        if abs(sum(t_count(c) for c in items) - real_t) > 1:
            continue
        out.append(items)
    return tuple(out)


PSEUDO_STOP_SETS = valid_pseudo_stop_sets()
PSEUDO_STOP_DISTINCT_COUNT = len(PSEUDO_STOP_SETS)


def selected_decoy_sets(n_pools):
    if not PSEUDO_STOP_SETS or n_pools <= 0:
        return []
    if n_pools <= len(PSEUDO_STOP_SETS):
        return list(PSEUDO_STOP_SETS[:n_pools])
    rng = random.Random(stable_seed("w6amb_decoy_pool_order"))
    out = list(PSEUDO_STOP_SETS)
    while len(out) < n_pools:
        out.append(rng.choice(PSEUDO_STOP_SETS))
    return out


def decoy_log_for_genome(genome, stop_set):
    carrier = carrier_maps(stop_set)
    scores = score_genome_matrices(
        genome["observed_matrix"],
        genome["expected_matrix"],
        genome["expected_internal_matrix"],
        carrier,
    )
    return scores["L_HS"], scores["E_HS"]


def decoy_variance_for_genome(observed, expected, expected_internal):
    logs = []
    for stop_set in PSEUDO_STOP_SETS[:DECOY_VARIANCE_SAMPLE]:
        carrier = carrier_maps(stop_set)
        logs.append(score_genome_matrices(observed, expected, expected_internal, carrier)["L_HS"])
    return stdev(logs) ** 2 if len(logs) >= 2 else 0.0


def weight_from_expected(value):
    return min(math.sqrt(max(float(value), 0.0)), math.sqrt(1000000.0))


def weighted_pool_log(genomes, log_field="L_HS", expected_field="E_HS"):
    numerator = 0.0
    denominator = 0.0
    for genome in genomes:
        weight = weight_from_expected(genome.get(expected_field, 0.0))
        if weight <= 0:
            continue
        numerator += weight * float(genome.get(log_field, 0.0))
        denominator += weight
    return numerator / denominator if denominator > 0 else 0.0


def group_by_genus(genomes):
    groups = defaultdict(list)
    for genome in genomes:
        groups[genome.get("genus") or "Unknown"].append(genome)
    return dict(groups)


def sign_test_p_value_positive(n_positive, n_total):
    if n_total <= 0:
        return 1.0
    k = max(0, int(n_positive))
    logs = []
    for i in range(k, n_total + 1):
        logs.append(
            math.lgamma(n_total + 1)
            - math.lgamma(i + 1)
            - math.lgamma(n_total - i + 1)
            - n_total * math.log(2.0)
        )
    m = max(logs)
    return min(1.0, math.exp(m) * sum(math.exp(x - m) for x in logs))


def genus_sign_metrics(genomes):
    groups = group_by_genus(genomes)
    medians = [median([g["L_HS"] for g in rows]) for rows in groups.values()]
    positive = sum(1 for value in medians if value > 0.0)
    return {
        "genus_count": len(medians),
        "genus_frac_positive": positive / len(medians) if medians else 0.0,
        "genus_sign_p": sign_test_p_value_positive(positive, len(medians)),
    }


def bootstrap_pool_logs(genomes, n_bootstrap=BOOTSTRAPS, seed="w6amb_genus_bootstrap"):
    groups = group_by_genus(genomes)
    genera = sorted(groups)
    if not genera or n_bootstrap <= 0:
        return {
            "replicates": 0,
            "log_values": [],
            "log_se": float("inf"),
            "lower95_or_pool": 0.0,
            "upper95_or_pool": float("inf"),
            "lower95_or_plus": 0.0,
            "lower95_or_minus": 0.0,
        }
    rng = random.Random(stable_seed(seed))
    logs = []
    logs_plus = []
    logs_minus = []
    for _ in range(n_bootstrap):
        sample = []
        for _ in genera:
            sample.extend(groups[rng.choice(genera)])
        logs.append(weighted_pool_log(sample, "L_HS", "E_HS"))
        logs_plus.append(weighted_pool_log(sample, "L_plus", "E_plus"))
        logs_minus.append(weighted_pool_log(sample, "L_minus", "E_minus"))
    logs_sorted = sorted(logs)
    plus_sorted = sorted(logs_plus)
    minus_sorted = sorted(logs_minus)
    return {
        "replicates": n_bootstrap,
        "log_values": logs,
        "log_se": stdev(logs),
        "lower95_or_pool": math.exp(percentile(logs_sorted, 0.025)),
        "upper95_or_pool": math.exp(percentile(logs_sorted, 0.975)),
        "lower95_or_plus": math.exp(percentile(plus_sorted, 0.025)),
        "lower95_or_minus": math.exp(percentile(minus_sorted, 0.025)),
    }


def aggregate_matrix(genomes, field):
    out = zero_matrix()
    for genome in genomes:
        add_matrix(out, genome[field])
    return out


def pooled_decoy_specificity(genomes, true_pool_log, n_pools=DECOY_POOLS):
    decoys = selected_decoy_sets(n_pools)
    if not decoys:
        return {
            "p_decoy": 1.0,
            "decoy_rank": None,
            "decoy_pools": 0,
            "decoy_log_se": 0.0,
            "decoy_distinct_valid_sets": 0,
            "decoy_generator_distinct_ge_5000": False,
        }
    # The composition-matched pseudo-stop universe has only a bounded number of
    # distinct sets (padded with repeats to reach n_pools), so score each
    # DISTINCT carrier once and replay its pooled log with the pool multiplicity.
    # This is arithmetically identical to scoring every pool independently.
    distinct_pool_log = {}
    for stop_set in decoys:
        if stop_set in distinct_pool_log:
            continue
        numerator = 0.0
        denominator = 0.0
        carrier = carrier_maps(stop_set)
        for genome in genomes:
            scores = score_genome_matrices(
                genome["observed_matrix"],
                genome["expected_matrix"],
                genome["expected_internal_matrix"],
                carrier,
            )
            weight = weight_from_expected(scores["E_HS"])
            if weight > 0:
                numerator += weight * scores["L_HS"]
                denominator += weight
        distinct_pool_log[stop_set] = numerator / denominator if denominator > 0 else None
    pooled_logs = [distinct_pool_log[s] for s in decoys if distinct_pool_log[s] is not None]
    rank = 1 + sum(1 for value in pooled_logs if value >= true_pool_log)
    return {
        "p_decoy": rank / (len(pooled_logs) + 1) if pooled_logs else 1.0,
        "decoy_rank": rank if pooled_logs else None,
        "decoy_pools": len(pooled_logs),
        "decoy_log_se": stdev(pooled_logs),
        "decoy_distinct_valid_sets": PSEUDO_STOP_DISTINCT_COUNT,
        "decoy_generator_distinct_ge_5000": PSEUDO_STOP_DISTINCT_COUNT >= 5000,
    }


def pooled_metrics(genomes):
    if not genomes:
        return {
            "OR_pool": 1.0,
            "L_pool": 0.0,
            "lower95_or_pool": 0.0,
            "upper95_or_pool": float("inf"),
            "OR_plus": 1.0,
            "OR_minus": 1.0,
            "p_decoy": 1.0,
            "decoy_rank": None,
            "species_frac_positive": 0.0,
            "genus_frac_positive": 0.0,
            "genus_sign_p": 1.0,
            "opp_localization_ratio": 0.0,
            "internal_only_sign_retained": False,
            "counted_windows": 0,
            "expected_hs_windows": 0.0,
            "genus_count": 0,
        }
    l_pool = weighted_pool_log(genomes, "L_HS", "E_HS")
    l_plus = weighted_pool_log(genomes, "L_plus", "E_plus")
    l_minus = weighted_pool_log(genomes, "L_minus", "E_minus")
    l_internal = weighted_pool_log(genomes, "L_HS_internal", "E_HS_internal")
    l_control = weighted_pool_log(genomes, "L_control", "E_control")
    boot = bootstrap_pool_logs(genomes)
    genus_metrics = genus_sign_metrics(genomes)
    species_frac_positive = sum(1 for g in genomes if g["L_HS"] > 0.0) / len(genomes)
    decoy = pooled_decoy_specificity(genomes, l_pool)
    localization_ratio = (
        abs(l_pool) / max(abs(l_control), EPS)
        if abs(l_control) > EPS else
        (float("inf") if abs(l_pool) > EPS else 0.0)
    )
    same_sign = (
        (l_pool > 0.0 and l_internal > 0.0)
        or (l_pool < 0.0 and l_internal < 0.0)
        or (abs(l_pool) <= EPS and abs(l_internal) <= EPS)
    )
    retention = abs(l_internal) / abs(l_pool) if abs(l_pool) > EPS else 1.0
    total_observed = aggregate_matrix(genomes, "observed_matrix")
    total_expected = aggregate_matrix(genomes, "expected_matrix")
    total_expected_internal = aggregate_matrix(genomes, "expected_internal_matrix")
    true_scores = score_genome_matrices(total_observed, total_expected, total_expected_internal, TRUE_CARRIER)
    return {
        "OR_pool": math.exp(l_pool),
        "L_pool": l_pool,
        "lower95_or_pool": boot["lower95_or_pool"],
        "upper95_or_pool": boot["upper95_or_pool"],
        "genus_block_se_logOR": boot["log_se"],
        "bootstrap_replicates": boot["replicates"],
        "OR_plus": math.exp(l_plus),
        "OR_minus": math.exp(l_minus),
        "lower95_or_plus": boot["lower95_or_plus"],
        "lower95_or_minus": boot["lower95_or_minus"],
        "p_decoy": decoy["p_decoy"],
        "decoy_rank": decoy["decoy_rank"],
        "decoy_pools": decoy["decoy_pools"],
        "decoy_log_se": decoy["decoy_log_se"],
        "decoy_distinct_valid_sets": decoy["decoy_distinct_valid_sets"],
        "decoy_generator_distinct_ge_5000": decoy["decoy_generator_distinct_ge_5000"],
        "species_frac_positive": species_frac_positive,
        "species_positive_count": sum(1 for g in genomes if g["L_HS"] > 0.0),
        "genus_frac_positive": genus_metrics["genus_frac_positive"],
        "genus_sign_p": genus_metrics["genus_sign_p"],
        "opp_localization_ratio": localization_ratio,
        "control_log_effect": l_control,
        "internal_only_sign_retained": same_sign,
        "internal_only_retention": retention,
        "internal_only_L_pool": l_internal,
        "internal_only_OR_pool": math.exp(l_internal),
        "counted_windows": int(round(sum(g.get("windows", 0.0) for g in genomes))),
        "expected_hs_windows": sum(g.get("E_HS", 0.0) for g in genomes),
        "observed_hs_windows": sum(g.get("O_HS", 0.0) for g in genomes),
        "genus_count": genus_metrics["genus_count"],
        "valid_species": len(genomes),
        "O_HS_aggregate": true_scores["O_HS"],
        "E_HS_aggregate": true_scores["E_HS"],
        "OR_HS_aggregate": true_scores["OR_HS"],
        "carrier_positive_states": TRUE_CARRIER["positive_state_count"],
        "carrier_plus_states": TRUE_CARRIER["plus_state_count"],
        "carrier_minus_states": TRUE_CARRIER["minus_state_count"],
        "carrier_opp_aa_pairs": TRUE_CARRIER["opp_aa_pair_count"],
        "carrier_max_k_total": TRUE_CARRIER["max_k_total"],
    }


def preflight_gates(cohort):
    failures = []
    valid = cohort.get("valid_genomes", [])
    selected = cohort.get("selected_assemblies", 0)
    invalid = cohort.get("invalid_genomes", [])
    invalid_fraction = (len(invalid) / selected) if selected else 1.0
    metrics = cohort.get("metrics", {})
    if len(valid) < 1000:
        failures.append("valid_species_lt_1000")
    if metrics.get("genus_count", 0) < 200:
        failures.append("valid_genera_lt_200")
    if invalid_fraction > 0.20:
        failures.append("qc_exclusion_fraction_gt_0_20")
    if metrics.get("counted_windows", 0) < 50000000:
        failures.append("counted_windows_lt_50000000")
    if metrics.get("expected_hs_windows", 0.0) < 1000000.0:
        failures.append("expected_hs_windows_lt_1000000")
    if metrics.get("genus_block_se_logOR", float("inf")) > 0.01:
        failures.append("genus_block_se_logOR_gt_0_01")
    if metrics.get("genus_block_se_logOR", 0.0) == 0.0:
        failures.append("zero_bootstrap_variance")
    if metrics.get("decoy_log_se", 0.0) == 0.0:
        failures.append("zero_pseudo_stop_decoy_variance")
    if any(g.get("reason") in {"download_failed", "md5_mismatch", "missing_md5_entry"} for g in invalid):
        failures.append("checksum_or_download_failures")
    exact = cohort.get("exact_null_validation", {})
    if not exact.get("toy_gene_selftest_passed", False):
        failures.append("toy_gene_exact_null_selftest_failed")
    if not exact.get("real_or_synthetic_mc_audit_passed", False):
        failures.append("mc_exact_null_audit_failed")
    return {
        "passed": not failures,
        "failures": failures,
        "valid_species": len(valid),
        "valid_genera": metrics.get("genus_count", 0),
        "qc_exclusion_fraction": invalid_fraction,
        "counted_windows": metrics.get("counted_windows", 0),
        "expected_hs_windows": metrics.get("expected_hs_windows", 0.0),
        "genus_block_se_logOR": metrics.get("genus_block_se_logOR", float("inf")),
        "decoy_log_se": metrics.get("decoy_log_se", 0.0),
    }


def derivation_state(cohort):
    reasons = []
    exact = cohort.get("exact_null_validation", {})
    metrics = cohort.get("metrics", {})
    if not exact.get("off_frame_mapping_selftest_passed", False):
        reasons.append("off_frame_mapping_ambiguity")
    if not exact.get("toy_gene_selftest_passed", False) or not exact.get("real_or_synthetic_mc_audit_passed", False):
        reasons.append("exact_null_formula_fails_audit")
    if metrics.get("decoy_distinct_valid_sets", PSEUDO_STOP_DISTINCT_COUNT) < MIN_DISTINCT_DECOY_SETS:
        reasons.append("pseudo_stop_matching_distinct_sets_below_floor")
    invalid = cohort.get("invalid_genomes", [])
    selected = cohort.get("selected_assemblies", 0)
    table_fail = sum(1 for g in invalid if g.get("reason") == "table_11_compatibility_low")
    if selected and table_fail / selected > 0.20:
        reasons.append("table_11_stop_carrier_not_applicable_to_too_many_retained_genomes")
    if TRUE_CARRIER["opp_aa_pair_count"] <= 0 or TRUE_CARRIER["positive_state_count"] < 25:
        reasons.append("k_total_opportunity_classes_collapse_below_power")
    return {"needs_derivation": bool(reasons), "reasons": reasons}


def verdict_from_metrics(cohort):
    derivation = derivation_state(cohort)
    if derivation["needs_derivation"]:
        return "needs_derivation", {"preflight": preflight_gates(cohort), "derivation": derivation}
    gates = preflight_gates(cohort)
    if not gates["passed"]:
        return "data_gate_failed", {"preflight": gates}
    m = cohort["metrics"]
    frame_consistency = (
        m["OR_plus"] >= 1.005
        and m["OR_minus"] >= 1.005
        and (m["lower95_or_plus"] >= 1.01 or m["lower95_or_minus"] >= 1.01)
    )
    specificity = m["p_decoy"] <= 0.01
    top_one_percent = m["decoy_rank"] is not None and m["decoy_rank"] <= max(1, int(math.floor(0.01 * (m["decoy_pools"] + 1))))
    localization = m["opp_localization_ratio"] >= 3.0
    robustness = m["internal_only_sign_retained"] and m["internal_only_retention"] >= 0.70
    certified = [
        m["OR_pool"] >= 1.03,
        m["lower95_or_pool"] >= 1.02,
        m["species_frac_positive"] >= 0.65,
        m["genus_frac_positive"] >= 0.60,
        m["genus_sign_p"] <= 1.0e-4,
        frame_consistency,
        specificity,
        top_one_percent,
        localization,
        robustness,
    ]
    if all(certified):
        return "certified", {"preflight": gates, "conditions": {
            "frame_consistency": frame_consistency,
            "true_stop_specificity": specificity,
            "top_one_percent": top_one_percent,
            "opportunity_localization": localization,
            "internal_only_robustness": robustness,
        }}
    hard_negative = [
        m["OR_pool"] <= 1.00,
        m["upper95_or_pool"] <= 1.01,
        m["species_frac_positive"] < 0.55,
        m["genus_frac_positive"] < 0.50,
        m["p_decoy"] >= 0.20,
        m["OR_plus"] <= 1.00 and m["OR_minus"] <= 1.00,
        not m["internal_only_sign_retained"],
    ]
    if any(hard_negative):
        return "refuted", {"preflight": gates, "conditions": {
            "hard_negative": True,
            "frame_consistency": frame_consistency,
            "true_stop_specificity": specificity,
            "opportunity_localization": localization,
            "internal_only_robustness": robustness,
        }}
    needs_more = (
        m["OR_pool"] > 1.00
        and (
            0.55 <= m["species_frac_positive"] < 0.65
            or 0.50 <= m["genus_frac_positive"] < 0.60
            or 0.01 < m["p_decoy"] < 0.20
            or m["lower95_or_pool"] < 1.02
        )
    )
    if needs_more:
        return "needs_more_organisms", {"preflight": gates, "conditions": {
            "direction_positive": True,
            "bootstrap_ci_crosses_certification_floor": m["lower95_or_pool"] < 1.02,
        }}
    coincidence = (
        m["OR_pool"] > 1.0
        and (
            not specificity
            or m["species_frac_positive"] < 0.65
            or m["genus_frac_positive"] < 0.60
            or (m["OR_plus"] > 1.0 and m["OR_minus"] < 1.0)
            or (m["OR_minus"] > 1.0 and m["OR_plus"] < 1.0)
            or not robustness
            or not localization
        )
    )
    if coincidence:
        return "coincidence", {"preflight": gates, "conditions": {
            "frame_consistency": frame_consistency,
            "true_stop_specificity": specificity,
            "opportunity_localization": localization,
            "internal_only_robustness": robustness,
        }}
    return "refuted", {"preflight": gates, "conditions": {"fallback": True}}


def genus_from_name(name):
    match = re.match(r"([A-Z][A-Za-z0-9_.-]+)", name or "")
    return match.group(1) if match else ""


def invalid_result(row, reason, contacts=None, **fields):
    out = {
        "assembly_accession": row.get("assembly_accession", ""),
        "organism_name": row.get("organism_name", ""),
        "species_taxid": row.get("species_taxid", ""),
        "genus": genus_from_name(row.get("organism_name", "")),
        "valid": False,
        "reason": reason,
    }
    if contacts is not None:
        out["contacts"] = contacts
    out.update(fields)
    return out


def analyze_assembly(row):
    accession = row["assembly_accession"]
    ftp_path = row["ftp_path"]
    asm = assembly_basename(ftp_path)
    _, md5_payload, md5_contact = fetch_md5checksums(row)
    md5s = parse_md5checksums(md5_payload.decode("utf-8", "replace")) if md5_payload else {}
    contacts = {"md5checksums.txt": md5_contact}
    filename, payload, contact = fetch_assembly_file(row, "_cds_from_genomic.fna.gz")
    contacts[filename] = contact
    if not payload:
        return invalid_result(row, "download_failed", contacts)
    ok, reason = validate_md5(filename, payload, md5s)
    if not ok:
        return invalid_result(row, reason, contacts)
    records, cds_stats = qc_cds_records(payload)
    observed, expected, expected_internal = genome_pair_matrices(records)
    scores = score_genome_matrices(observed, expected, expected_internal, TRUE_CARRIER)
    windows = int(round(matrix_sum(observed)))
    total_for_table = cds_stats.get("qc_passing", 0) + cds_stats.get("non_table_11_annotation", 0)
    table11_fraction = cds_stats.get("qc_passing", 0) / total_for_table if total_for_table else 0.0
    decoy_variance = decoy_variance_for_genome(observed, expected, expected_internal)
    base = {
        "assembly_accession": accession,
        "organism_name": row.get("organism_name", ""),
        "genus": genus_from_name(row.get("organism_name", "")),
        "species_taxid": row.get("species_taxid", ""),
        "ftp_path": ftp_path,
        "asm": asm,
        "qc_cds": cds_stats.get("qc_passing", 0),
        "cds_stats": cds_stats,
        "table11_fraction": table11_fraction,
        "windows": windows,
        "matrix_windows_observed": matrix_sum(observed),
        "matrix_windows_expected": matrix_sum(expected),
        "matrix_windows_expected_internal": matrix_sum(expected_internal),
        "finite_exact_matrices": finite_matrix(observed) and finite_matrix(expected) and finite_matrix(expected_internal),
        "k_total_observed_state_count": observed_k_state_count(observed, TRUE_CARRIER),
        "decoy_variance": decoy_variance,
        "decoy_variance_sample": min(DECOY_VARIANCE_SAMPLE, PSEUDO_STOP_DISTINCT_COUNT),
        "contacts": contacts,
        "observed_matrix": observed,
        "expected_matrix": expected,
        "expected_internal_matrix": expected_internal,
    }
    base.update(scores)
    per_genome_failures = []
    if base["qc_cds"] < 800:
        per_genome_failures.append("qc_cds_lt_800")
    if windows < 150000:
        per_genome_failures.append("internal_windows_lt_150000")
    if scores["E_HS"] < 1000.0:
        per_genome_failures.append("expected_hs_windows_lt_1000")
    if base["k_total_observed_state_count"] < 25:
        per_genome_failures.append("observed_k_total_state_count_lt_25")
    if decoy_variance <= 0.0:
        per_genome_failures.append("zero_pseudo_stop_decoy_variance")
    if table11_fraction < 0.95:
        per_genome_failures.append("table_11_compatibility_low")
    if not base["finite_exact_matrices"]:
        per_genome_failures.append("nonfinite_exact_matrices")
    if per_genome_failures:
        base["valid"] = False
        base["reason"] = per_genome_failures[0]
        base["per_genome_failures"] = per_genome_failures
    else:
        base["valid"] = True
    return base


def stripped_genome_for_output(genome):
    return {
        k: v
        for k, v in genome.items()
        if k not in {"observed_matrix", "expected_matrix", "expected_internal_matrix", "contacts"}
    }


def shuffled_gene_codons(codon_list, rng):
    out = list(codon_list)
    positions_by_aa = defaultdict(list)
    values_by_aa = defaultdict(list)
    for i, codon in enumerate(codon_list):
        aa = CODON_TO_AA[codon]
        positions_by_aa[aa].append(i)
        values_by_aa[aa].append(codon)
    for aa, positions in positions_by_aa.items():
        values = list(values_by_aa[aa])
        rng.shuffle(values)
        for pos, codon in zip(positions, values):
            out[pos] = codon
    return out


def observed_matrix_for_codons(codon_list):
    observed = zero_matrix()
    for i in internal_pair_starts(len(codon_list)):
        observed[pair_index(codon_list[i], codon_list[i + 1])] += 1.0
    return observed


def synthetic_formula_codons():
    unit = [
        "GCU", "GCC", "GCA", "GCG", "GCU", "GCC",
        "UUU", "UUC", "AAA", "AAG", "UGG", "AUG",
        "GAA", "GAG", "GAU", "GAC", "CGU", "CGC",
    ]
    return ["AUG"] + unit * 5 + ["GCU", "GCC", "GCA", "GCG", "AAA", "AAG", "UUU", "UUC"]


def audit_exact_formula_for_codons(codon_list, replicates, seed):
    _, expected = gene_observed_and_expected(codon_list, "full")
    sums = zero_matrix()
    sums_sq = zero_matrix()
    rng = random.Random(seed)
    for _ in range(replicates):
        observed = observed_matrix_for_codons(shuffled_gene_codons(codon_list, rng))
        for idx, value in enumerate(observed):
            if value:
                sums[idx] += value
                sums_sq[idx] += value * value
    checked = 0
    max_z = 0.0
    max_abs = 0.0
    failures = []
    for idx, exact in enumerate(expected):
        if exact <= 0 and sums[idx] <= 0:
            continue
        sample_mean = sums[idx] / replicates
        variance = max(0.0, (sums_sq[idx] / replicates) - sample_mean * sample_mean)
        se = math.sqrt(variance / replicates) if variance > 0 else 0.0
        diff = abs(sample_mean - exact)
        limit = max(5.0 * se, 0.03)
        checked += 1
        max_abs = max(max_abs, diff)
        z = diff / se if se > 0 else 0.0
        max_z = max(max_z, z)
        if diff > limit:
            failures.append({"idx": idx, "exact": exact, "mean": sample_mean, "se": se, "diff": diff})
    return {
        "passed": not failures,
        "replicates": replicates,
        "checked_pairs": checked,
        "max_abs_error": max_abs,
        "max_mc_z": max_z,
        "failures": failures[:5],
    }


def run_exact_formula_selftest(replicates=SELFTEST_SHUFFLES):
    return audit_exact_formula_for_codons(synthetic_formula_codons(), max(20000, int(replicates)), 83391)


def audit_real_or_synthetic_records(records, replicates=MC_AUDIT_SHUFFLES, n_genes=MC_AUDIT_GENES):
    selected = [r["codons"] for r in records[:n_genes]]
    synthetic = False
    if len(selected) < n_genes:
        synthetic = True
        selected = [synthetic_formula_codons() for _ in range(n_genes)]
    gene_results = []
    for idx, codons in enumerate(selected):
        result = audit_exact_formula_for_codons(codons, replicates, 90017 + idx)
        gene_results.append(result)
        if not result["passed"]:
            break
    return {
        "passed": all(r["passed"] for r in gene_results),
        "synthetic_fallback": synthetic,
        "genes": len(gene_results),
        "replicates_per_gene": replicates,
        "max_abs_error": max((r["max_abs_error"] for r in gene_results), default=0.0),
        "max_mc_z": max((r["max_mc_z"] for r in gene_results), default=0.0),
        "failures": [r for r in gene_results if not r["passed"]][:3],
    }


def selftest_carrier():
    plus_idx = pair_index("AUA", "AAA")
    minus_idx = pair_index("AAU", "AAG")
    assert TRUE_CARRIER["k_plus"][plus_idx] == 1
    assert TRUE_CARRIER["k_minus"][plus_idx] == 0
    assert TRUE_CARRIER["k_plus"][minus_idx] == 0
    assert TRUE_CARRIER["k_minus"][minus_idx] == 1
    assert TRUE_CARRIER["max_k_total"] == 1
    opp_ilys = TRUE_CARRIER["opp_by_aa_pair"][(CODON_TO_AA["AUA"], CODON_TO_AA["AAA"])]
    assert opp_ilys > 0
    return {
        "plus_pair": ["AUA", "AAA"],
        "minus_pair": ["AAU", "AAG"],
        "opp_IK": opp_ilys,
        "positive_state_count": TRUE_CARRIER["positive_state_count"],
        "opp_aa_pair_count": TRUE_CARRIER["opp_aa_pair_count"],
        "max_k_total": TRUE_CARRIER["max_k_total"],
    }


def selftest_decoys():
    valid = PSEUDO_STOP_SETS
    for triple in valid[:10]:
        assert len(triple) == 3
        assert not (set(triple) & STOP_CODONS)
        assert sorted(gc_count(c) for c in triple) == [0, 1, 1]
        assert abs(sum(purine_count(c) for c in triple) - 6) <= 1
        assert abs(sum(t_count(c) for c in triple) - 3) <= 1
    return {
        "distinct_valid_sets": len(valid),
        "distinct_valid_sets_ge_5000": len(valid) >= 5000,
        "first_sets": [list(x) for x in valid[:3]],
    }


def selftest_opportunity_localization():
    records = [{"codons": synthetic_formula_codons()}]
    observed, expected, expected_internal = genome_pair_matrices(records)
    scores = score_genome_matrices(observed, expected, expected_internal, TRUE_CARRIER)
    ratio_value = abs(scores["L_HS"]) / max(abs(scores["L_control"]), EPS) if abs(scores["L_control"]) > EPS else float("inf")
    assert math.isfinite(scores["L_HS"])
    return {
        "L_HS": scores["L_HS"],
        "L_control": scores["L_control"],
        "opp_localization_ratio": ratio_value,
    }


def make_metric_template():
    return {
        "OR_pool": 1.04,
        "L_pool": math.log(1.04),
        "lower95_or_pool": 1.025,
        "upper95_or_pool": 1.06,
        "genus_block_se_logOR": 0.005,
        "OR_plus": 1.012,
        "OR_minus": 1.011,
        "lower95_or_plus": 1.011,
        "lower95_or_minus": 1.006,
        "p_decoy": 0.005,
        "decoy_rank": 1,
        "decoy_pools": 10000,
        "decoy_log_se": 0.01,
        "decoy_distinct_valid_sets": 5000,
        "decoy_generator_distinct_ge_5000": True,
        "species_frac_positive": 0.70,
        "species_positive_count": 700,
        "genus_frac_positive": 0.65,
        "genus_sign_p": 1.0e-5,
        "opp_localization_ratio": 3.5,
        "control_log_effect": 0.01,
        "internal_only_sign_retained": True,
        "internal_only_retention": 0.75,
        "internal_only_L_pool": math.log(1.03),
        "internal_only_OR_pool": 1.03,
        "counted_windows": 150000000,
        "expected_hs_windows": 1200000.0,
        "observed_hs_windows": 1248000.0,
        "genus_count": 200,
        "valid_species": 1000,
        "carrier_positive_states": TRUE_CARRIER["positive_state_count"],
        "carrier_plus_states": TRUE_CARRIER["plus_state_count"],
        "carrier_minus_states": TRUE_CARRIER["minus_state_count"],
        "carrier_opp_aa_pairs": TRUE_CARRIER["opp_aa_pair_count"],
        "carrier_max_k_total": TRUE_CARRIER["max_k_total"],
    }


def synthetic_genomes_for_preflight():
    genomes = []
    for i in range(1000):
        genomes.append({
            "assembly_accession": "GCF_SYN_%04d" % i,
            "genus": "Genus%d" % (i % 200),
            "valid": True,
            "windows": 150000,
            "E_HS": 1200.0,
            "L_HS": math.log(1.04),
        })
    return genomes


def synthetic_validation(passed=True):
    return {
        "off_frame_mapping_selftest_passed": passed,
        "toy_gene_selftest_passed": passed,
        "real_or_synthetic_mc_audit_passed": passed,
        "decoy_generator_distinct_valid_sets": 5000,
    }


def synthetic_cohort(kind):
    metrics = make_metric_template()
    if kind == "coincidence":
        metrics["OR_plus"] = 1.03
        metrics["OR_minus"] = 0.995
        metrics["lower95_or_plus"] = 1.02
        metrics["lower95_or_minus"] = 0.98
    elif kind == "refuted":
        metrics["OR_pool"] = 0.999
        metrics["L_pool"] = math.log(0.999)
    elif kind == "needs_more_organisms":
        metrics["OR_pool"] = 1.02
        metrics["L_pool"] = math.log(1.02)
        metrics["species_frac_positive"] = 0.60
    elif kind == "needs_derivation":
        metrics["decoy_distinct_valid_sets"] = 20
        metrics["decoy_generator_distinct_ge_5000"] = False
    elif kind == "data_gate_failed":
        metrics["counted_windows"] = 1000
    return {
        "selected_assemblies": 1000,
        "valid_genomes": synthetic_genomes_for_preflight(),
        "invalid_genomes": [],
        "metrics": metrics,
        "exact_null_validation": synthetic_validation(True),
    }


def selftest_verdicts():
    expected = {
        "certified": "certified",
        "coincidence": "coincidence",
        "refuted": "refuted",
        "needs_more_organisms": "needs_more_organisms",
        "needs_derivation": "needs_derivation",
        "data_gate_failed": "data_gate_failed",
    }
    out = {}
    for kind, want in expected.items():
        got, _ = verdict_from_metrics(synthetic_cohort(kind))
        assert got == want, (kind, got, want)
        out[kind] = got
    return out


def selftest_bootstrap():
    genomes = []
    for i in range(20):
        genomes.append({
            "genus": "Genus%d" % (i % 5),
            "L_HS": math.log(1.02 + 0.001 * (i % 3)),
            "E_HS": 1000.0 + i,
            "L_plus": math.log(1.01),
            "E_plus": 500.0,
            "L_minus": math.log(1.012),
            "E_minus": 500.0,
        })
    boot = bootstrap_pool_logs(genomes, n_bootstrap=100, seed="selftest_bootstrap")
    assert boot["replicates"] == 100
    assert boot["lower95_or_pool"] > 1.0
    return {k: v for k, v in boot.items() if k != "log_values"}


def run_selftest():
    formula = run_exact_formula_selftest()
    assert formula["passed"], formula
    audit = audit_real_or_synthetic_records([], replicates=20000, n_genes=1)
    assert audit["passed"], audit
    carrier = selftest_carrier()
    decoys = selftest_decoys()
    localization = selftest_opportunity_localization()
    boot = selftest_bootstrap()
    verdicts = selftest_verdicts()
    payload = {
        "ok": True,
        "experiment_id": EXPERIMENT_ID,
        "exact_formula": formula,
        "mc_audit": audit,
        "carrier": carrier,
        "decoys": decoys,
        "opportunity_localization": localization,
        "bootstrap": boot,
        "verdicts": verdicts,
    }
    print(json.dumps(clean_json(payload), ensure_ascii=True, sort_keys=True, separators=(",", ":")))


def run_real():
    carrier_selftest = selftest_carrier()
    formula = run_exact_formula_selftest()
    decoy_info = selftest_decoys()
    text, contact = read_text_cached(SUMMARY_URL, "assembly_summary.txt")
    if not text:
        emit("data_gate_failed", reason="assembly_summary_unreachable", summary_contact=contact)
    rows = parse_assembly_summary(text)
    selected = select_species_assemblies(rows)
    valid = []
    invalid = []
    audit_records = []
    for idx, row in enumerate(selected, 1):
        result = analyze_assembly(row)
        if result.get("valid"):
            valid.append(result)
            if len(audit_records) < MC_AUDIT_GENES:
                for record in result.get("cds_stats_records", []):
                    audit_records.append(record)
        else:
            invalid.append(result)
        print(json.dumps({
            "status": "assembly_done",
            "index": idx,
            "selected": len(selected),
            "assembly_accession": row.get("assembly_accession"),
            "valid": bool(result.get("valid")),
            "reason": result.get("reason"),
        }, sort_keys=True), file=sys.stderr, flush=True)
    audit = audit_real_or_synthetic_records(audit_records, replicates=MC_AUDIT_SHUFFLES, n_genes=MC_AUDIT_GENES)
    metrics = pooled_metrics(valid)
    metrics["selected_assemblies"] = len(selected)
    metrics["invalid_genomes"] = len(invalid)
    metrics["qc_exclusion_fraction"] = len(invalid) / len(selected) if selected else 1.0
    exact_validation = {
        "off_frame_mapping_selftest_passed": bool(carrier_selftest),
        "toy_gene_selftest_passed": formula["passed"],
        "toy_gene_selftest": formula,
        "real_or_synthetic_mc_audit_passed": audit["passed"],
        "real_or_synthetic_mc_audit": audit,
        "decoy_generator_distinct_valid_sets": decoy_info["distinct_valid_sets"],
        "decoy_generator_distinct_ge_5000": decoy_info["distinct_valid_sets_ge_5000"],
    }
    cohort = {
        "selected_assemblies": len(selected),
        "valid_genomes": valid,
        "invalid_genomes": invalid,
        "metrics": metrics,
        "exact_null_validation": exact_validation,
    }
    verdict, details = verdict_from_metrics(cohort)
    emit(
        verdict,
        selected_assemblies=len(selected),
        valid_genomes=len(valid),
        invalid_genomes=len(invalid),
        metrics=metrics,
        details=details,
        exact_null_validation=exact_validation,
        invalid_reasons=dict(Counter(g.get("reason", "unknown") for g in invalid)),
        invalid_examples=[stripped_genome_for_output(g) for g in invalid[:20]],
        summary_contact=contact,
    )


def main(argv):
    if "--selftest" in argv:
        run_selftest()
        return
    try:
        run_real()
    except Exception as exc:
        emit_error(type(exc).__name__ + ":" + str(exc))


if __name__ == "__main__":
    main(sys.argv[1:])

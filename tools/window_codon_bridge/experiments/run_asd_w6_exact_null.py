#!/usr/bin/env python3
"""ASD-W6 self-tail Window6 codon-pair certificate with exact gene-wise null."""
from __future__ import annotations

from collections import Counter, defaultdict
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


EXPERIMENT_ID = "asd_w6_self_tail_exact_null"
CLAIM_ID = "window_codon_bridge.asd_w6_self_tail"
SUMMARY_URL = os.environ.get(
    "ASD_W6_ASSEMBLY_SUMMARY_URL",
    "https://ftp.ncbi.nlm.nih.gov/genomes/refseq/bacteria/assembly_summary.txt",
)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(SCRIPT_DIR)))
CACHE_DIR = os.environ.get(
    "ASD_W6_CACHE_DIR",
    os.path.join(REPO_ROOT, "tools", "window_codon_bridge", "synced", "asd_w6_self_tail"),
)
MAX_GENOMES = int(os.environ.get("ASD_W6_MAX_GENOMES", "0"))
FETCH_TIMEOUT = int(os.environ.get("ASD_W6_FETCH_TIMEOUT", "60"))
FETCH_ATTEMPTS = int(os.environ.get("ASD_W6_FETCH_ATTEMPTS", "3"))
NCBI_DELAY_SECONDS = float(os.environ.get("ASD_W6_NCBI_DELAY_SECONDS", "0.34"))
BOOTSTRAPS = int(os.environ.get("ASD_W6_BOOTSTRAPS", "10000"))
CARRIER_DECOYS = int(os.environ.get("ASD_W6_CARRIER_DECOYS", "1000"))
GLOBAL_DECOY_POOLS = int(os.environ.get("ASD_W6_GLOBAL_DECOY_POOLS", "10000"))
SELFTEST_SHUFFLES = int(os.environ.get("ASD_W6_SELFTEST_SHUFFLES", "5000"))
USER_AGENT = "asd-w6-self-tail-exact-null"
NULL_REPLICATES_VERDICT = 0
USE_EXACT_GENEWISE_SYNONYMOUS_EXPECTATION = True
BIN_LABELS = ("0", "1", "2", "3", "4", "5", "6+")
BASES_RNA = set("ACGU")
BASES_DNA = set("ACGT")
PSEUDO = 0.5
EPS = 1.0e-12

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
DNA_TO_RNA = str.maketrans("ACGTacgt", "ACGUACGU")
RNA_COMP = str.maketrans("ACGUacgu", "UGCAUGCA")


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
    if not values:
        return 0.0
    return statistics.median(values)


def stdev(values):
    return statistics.stdev(values) if len(values) >= 2 else 0.0


def emit(verdict, **fields):
    payload = {"verdict": verdict, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(clean_json(payload), ensure_ascii=True, sort_keys=True, separators=(",", ":")))
    sys.exit(0)


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


def clean_rna(seq):
    return re.sub(r"[^ACGU]", "", to_rna(seq))


def revcomp_rna(seq):
    return seq.translate(RNA_COMP)[::-1].upper()


def complement_rna(seq):
    return seq.translate(RNA_COMP).upper()


def identity(left, right):
    if len(left) != len(right) or not left:
        return 0.0
    return sum(1 for a, b in zip(left, right) if a == b) / len(left)


def extract_16s_records(payload):
    out = []
    for header, seq in iter_fasta_bytes(payload, gzipped=True):
        marker = header.lower()
        if "16s ribosomal rna" not in marker and "rf00177" not in marker:
            continue
        rna = clean_rna(seq)
        if len(rna) >= 1200 and set(rna) <= BASES_RNA:
            out.append({"header": header, "sequence": rna})
    return out


def resolve_tail13(records):
    tails = [row["sequence"][-13:] for row in records if len(row.get("sequence", "")) >= 13]
    if not tails:
        return None, {"reason": "no_full_length_16s"}
    counts = Counter(tails)
    tail, n = counts.most_common(1)[0]
    if n / len(tails) >= 0.70:
        return tail, {"method": "copy_majority", "n_16s": len(tails), "support": n}
    consensus = []
    support = []
    for pos in range(13):
        base, base_n = Counter(t[pos] for t in tails).most_common(1)[0]
        if base_n / len(tails) < 0.70:
            return None, {"reason": "unresolved_tail13", "n_16s": len(tails), "position": pos}
        consensus.append(base)
        support.append(base_n)
    return "".join(consensus), {"method": "positionwise_consensus", "n_16s": len(tails), "support": support}


def base_pair_score(x, y):
    if (x, y) in {("G", "C"), ("C", "G")}:
        return 3
    if (x, y) in {("A", "U"), ("U", "A")}:
        return 2
    if (x, y) in {("G", "U"), ("U", "G")}:
        return 1
    return 0


def pairing_score(tail13, sixmer):
    best = 0
    for j in range(8):
        total = 0
        for k in range(6):
            total += base_pair_score(tail13[j + 5 - k], sixmer[k])
        if total > best:
            best = total
    return best


def carrier_maps(tail13):
    b_map = {}
    d_map = {}
    d_by_index = [0] * N_PAIRS
    for c1 in SENSE_CODONS:
        for c2 in SENSE_CODONS:
            pair = c1 + c2
            b_map[pair] = pairing_score(tail13, pair)
    for c1 in SENSE_CODONS:
        aa1 = CODON_TO_AA[c1]
        i = CODON_INDEX[c1]
        for c2 in SENSE_CODONS:
            aa2 = CODON_TO_AA[c2]
            j = CODON_INDEX[c2]
            pair = c1 + c2
            floor = min(b_map[x + y] for x in SYNONYMS[aa1] for y in SYNONYMS[aa2])
            d = b_map[pair] - floor
            d_map[pair] = d
            d_by_index[i * N_CODONS + j] = d
    hist = Counter(d_map.values())
    return {"tail13": tail13, "b": b_map, "d": d_map, "d_by_index": d_by_index, "hist": dict(sorted(hist.items()))}


def d_bin(value):
    return "6+" if value >= 6 else str(max(0, value))


def zero_counts():
    return {label: 0.0 for label in BIN_LABELS}


def add_counts(dst, src, scale=1.0):
    for key, value in src.items():
        dst[key] = dst.get(key, 0.0) + scale * value


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
        if len(codon_list) < 27:
            stats["too_short_for_internal_windows"] += 1
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


def score_matrix_by_d(matrix, d_by_index):
    bins = zero_counts()
    hi = 0.0
    dpos = 0.0
    windows = 0.0
    for idx, count in enumerate(matrix):
        if not count:
            continue
        d = d_by_index[idx]
        bins[d_bin(d)] += float(count)
        if d >= 4:
            hi += float(count)
        if d > 0:
            dpos += float(count)
        windows += float(count)
    return {"bins": bins, "hi": hi, "dpos": dpos, "windows": windows}


def tail_scores(observed_matrix, expected_matrix, expected_internal_matrix, tail13):
    maps = carrier_maps(tail13)
    observed = score_matrix_by_d(observed_matrix, maps["d_by_index"])
    expected = score_matrix_by_d(expected_matrix, maps["d_by_index"])
    expected_internal = score_matrix_by_d(expected_internal_matrix, maps["d_by_index"])
    return maps, observed, expected, expected_internal


def ratio_log(obs, exp):
    return math.log((obs + PSEUDO) / (exp + PSEUDO))


def ratio(obs, exp):
    return (obs + PSEUDO) / (exp + PSEUDO)


def internal_decoy_tails(seq, true_tail, rng, n):
    candidates = []
    limit = max(0, len(seq) - 50)
    for i in range(0, max(0, limit - 13 + 1)):
        tail = seq[i:i + 13]
        if len(tail) == 13 and set(tail) <= BASES_RNA and identity(tail, true_tail) < 0.80:
            candidates.append(tail)
    if not candidates:
        return []
    if len(candidates) >= n:
        return rng.sample(candidates, n)
    return [rng.choice(candidates) for _ in range(n)]


def mono_shuffle_tail(tail, rng):
    chars = list(tail)
    rng.shuffle(chars)
    return "".join(chars)


def orientation_tails(tail, n):
    variants = []
    primitives = [tail[::-1], complement_rna(tail), revcomp_rna(tail)]
    for item in primitives:
        if item != tail:
            variants.append(item)
    for shift in range(1, len(tail)):
        item = tail[shift:] + tail[:shift]
        if item != tail:
            variants.append(item)
    out = []
    i = 0
    while len(out) < n and variants:
        out.append(variants[i % len(variants)])
        i += 1
    return out


def build_decoy_tails(records_16s, true_tail, accession, n_decoys=CARRIER_DECOYS):
    rng = random.Random(stable_seed(accession + ":decoys"))
    seq = records_16s[0]["sequence"] if records_16s else true_tail
    decoys = []
    for tail in internal_decoy_tails(seq, true_tail, rng, int(n_decoys * 0.70)):
        decoys.append(("16s_internal", tail))
    for _ in range(int(n_decoys * 0.20)):
        tail = mono_shuffle_tail(true_tail, rng)
        if tail != true_tail:
            decoys.append(("mono_shuffle", tail))
    for tail in orientation_tails(true_tail, max(1, n_decoys - len(decoys))):
        decoys.append(("orientation", tail))
        if len(decoys) >= n_decoys:
            break
    while len(decoys) < n_decoys:
        decoys.append(("mono_shuffle", mono_shuffle_tail(true_tail, rng)))
    return decoys[:n_decoys]


def decoy_effect(observed_matrix, expected_matrix, tail13):
    maps = carrier_maps(tail13)
    observed = score_matrix_by_d(observed_matrix, maps["d_by_index"])
    expected = score_matrix_by_d(expected_matrix, maps["d_by_index"])
    return {
        "observed_hi": observed["hi"],
        "expected_hi": expected["hi"],
        "log_or": ratio_log(observed["hi"], expected["hi"]),
    }


def decoy_specificity(records_16s, true_tail, accession, true_log_or, observed_matrix, expected_matrix, n_decoys=CARRIER_DECOYS):
    values = []
    for cls, tail in build_decoy_tails(records_16s, true_tail, accession, n_decoys):
        effect = decoy_effect(observed_matrix, expected_matrix, tail)
        values.append({"class": cls, "tail13": tail, **effect})
    decoy_logs = [row["log_or"] for row in values if math.isfinite(row["log_or"])]
    stronger = sum(1 for v in decoy_logs if v <= true_log_or)
    rank = (stronger + 1) / (len(decoy_logs) + 1) if decoy_logs else None
    variance = stdev(decoy_logs) ** 2 if len(decoy_logs) >= 2 else 0.0
    return {"rank_percentile": rank, "n_decoys": len(decoy_logs), "variance": variance, "decoys": values}


def sign_test_p_value(n_negative, n_total):
    if n_total <= 0:
        return 1.0
    k = int(n_negative)
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


def spearman(xs, ys):
    if len(xs) != len(ys) or len(xs) < 2:
        return 0.0

    def ranks(values):
        order = sorted(range(len(values)), key=lambda i: values[i])
        out = [0.0] * len(values)
        i = 0
        while i < len(order):
            j = i + 1
            while j < len(order) and values[order[j]] == values[order[i]]:
                j += 1
            rank = (i + j - 1) / 2.0
            for k in range(i, j):
                out[order[k]] = rank
            i = j
        return out

    rx, ry = ranks(xs), ranks(ys)
    mx, my = mean(rx), mean(ry)
    num = sum((a - mx) * (b - my) for a, b in zip(rx, ry))
    denx = math.sqrt(sum((a - mx) ** 2 for a in rx))
    deny = math.sqrt(sum((b - my) ** 2 for b in ry))
    return num / (denx * deny) if denx > 0 and deny > 0 else 0.0


def monotone_nonincreasing(values):
    return all(values[i] >= values[i + 1] for i in range(len(values) - 1))


def weighted_pool_log(genomes, field="log_or_hi_exact", expected_field="expected_hi_exact"):
    numerator = 0.0
    denominator = 0.0
    for genome in genomes:
        expected = max(float(genome.get(expected_field, 0.0)), 0.0)
        weight = min(math.sqrt(expected), math.sqrt(1000000.0))
        if weight <= 0:
            continue
        numerator += weight * float(genome.get(field, 0.0))
        denominator += weight
    return numerator / denominator if denominator > 0 else 0.0


def dose_values_from_totals(bins_obs, bins_exp):
    return [ratio(bins_obs[label], bins_exp[label]) for label in BIN_LABELS]


def dose_logs_from_totals(bins_obs, bins_exp):
    return {label: ratio_log(bins_obs[label], bins_exp[label]) for label in BIN_LABELS}


def dose_slope(values):
    xs = list(range(len(values)))
    mx = mean(xs)
    my = mean(values)
    den = sum((x - mx) ** 2 for x in xs)
    return sum((x - mx) * (y - my) for x, y in zip(xs, values)) / den if den > 0 else 0.0


def pooled_bin_totals(genomes, expected_key="expected_bins_exact"):
    bins_obs = zero_counts()
    bins_exp = zero_counts()
    for genome in genomes:
        add_counts(bins_obs, genome["observed_bins"])
        add_counts(bins_exp, genome[expected_key])
    return bins_obs, bins_exp


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


def group_by_genus(genomes):
    groups = defaultdict(list)
    for genome in genomes:
        groups[genome.get("genus") or "Unknown"].append(genome)
    return dict(groups)


def genus_block_bootstrap(genomes, n_bootstrap=BOOTSTRAPS, seed="genus_bootstrap"):
    groups = group_by_genus(genomes)
    genera = sorted(groups)
    if not genera or n_bootstrap <= 0:
        return {
            "replicates": 0,
            "log_values": [],
            "log_se": float("inf"),
            "upper95_or_hi": float("inf"),
            "depletion_p": 1.0,
            "negative_dose_slope_fraction": 0.0,
        }
    rng = random.Random(stable_seed(seed))
    logs = []
    negative_slopes = 0
    for _ in range(n_bootstrap):
        sample = []
        for _ in genera:
            sample.extend(groups[rng.choice(genera)])
        l_pool = weighted_pool_log(sample)
        logs.append(l_pool)
        bins_obs, bins_exp = pooled_bin_totals(sample)
        values = [math.log(v) for v in dose_values_from_totals(bins_obs, bins_exp)]
        if dose_slope(values) < 0:
            negative_slopes += 1
    logs_sorted = sorted(logs)
    return {
        "replicates": n_bootstrap,
        "log_values": logs,
        "log_se": stdev(logs),
        "upper95_or_hi": math.exp(percentile(logs_sorted, 0.975)),
        "depletion_p": (sum(1 for value in logs if value >= 0.0) + 1) / (len(logs) + 1),
        "negative_dose_slope_fraction": negative_slopes / len(logs) if logs else 0.0,
    }


def global_decoy_specificity(genomes, true_pool_log, n_pools=GLOBAL_DECOY_POOLS):
    usable = [g for g in genomes if g.get("decoy_logs")]
    if not usable or n_pools <= 0:
        return {"p_decoy": 1.0, "global_pools": 0, "decoy_log_se": 0.0}
    rng = random.Random(stable_seed("global_decoy_pools"))
    pooled = []
    for _ in range(n_pools):
        numerator = 0.0
        denominator = 0.0
        for genome in usable:
            logs = genome["decoy_logs"]
            expected = max(float(genome.get("expected_hi_exact", 0.0)), 0.0)
            weight = min(math.sqrt(expected), math.sqrt(1000000.0))
            if logs and weight > 0:
                numerator += weight * rng.choice(logs)
                denominator += weight
        if denominator > 0:
            pooled.append(numerator / denominator)
    return {
        "p_decoy": (sum(1 for value in pooled if value <= true_pool_log) + 1) / (len(pooled) + 1) if pooled else 1.0,
        "global_pools": len(pooled),
        "decoy_log_se": stdev(pooled),
    }


def genus_sign_metrics(genomes):
    groups = group_by_genus(genomes)
    medians = [median([g["log_or_hi_exact"] for g in rows]) for rows in groups.values()]
    negative = sum(1 for value in medians if value < 0.0)
    return {
        "genus_count": len(medians),
        "genus_negative_fraction": negative / len(medians) if medians else 0.0,
        "genus_sign_p": sign_test_p_value(negative, len(medians)),
    }


def pooled_metrics(genomes):
    if not genomes:
        return {
            "pooled_high_log_se": float("inf"),
            "or_pool_hi": float("inf"),
            "log_or_pool_hi": 0.0,
            "upper95_or_pool_hi": float("inf"),
            "bootstrap_depletion_p": 1.0,
            "species_negative_fraction": 0.0,
            "genus_negative_fraction": 0.0,
            "genus_sign_p": 1.0,
            "dose_monotone": False,
            "dose_spearman": 0.0,
            "dose_negative_slope_bootstrap_fraction": 0.0,
            "p_decoy": 1.0,
            "self_species_top5_fraction": 0.0,
            "robustness_same_sign": False,
            "robustness_retains_70pct": False,
        }
    log_pool = weighted_pool_log(genomes)
    bins_obs, bins_exp = pooled_bin_totals(genomes)
    ratios = {label: ratio(bins_obs[label], bins_exp[label]) for label in BIN_LABELS}
    logs = dose_logs_from_totals(bins_obs, bins_exp)
    values = [ratios[label] for label in BIN_LABELS]
    boot = genus_block_bootstrap(genomes)
    genus_metrics = genus_sign_metrics(genomes)
    decoy = global_decoy_specificity(genomes, log_pool)
    internal_logs = [g["log_or_hi_internal_exact"] for g in genomes]
    full_logs = [g["log_or_hi_exact"] for g in genomes]
    internal_pool = weighted_pool_log(genomes, "log_or_hi_internal_exact", "expected_hi_internal_exact")
    same_sign = (internal_pool < 0 and log_pool < 0) or (internal_pool > 0 and log_pool > 0) or (internal_pool == log_pool == 0)
    retains = abs(internal_pool) >= 0.70 * abs(log_pool) if abs(log_pool) > EPS else True
    self_ranks = [
        g["decoy_rank_percentile"]
        for g in genomes
        if g.get("decoy_rank_percentile") is not None and g.get("carrier_decoy_variance", 0.0) > 0.0
    ]
    return {
        "observed_hi": sum(g["observed_hi"] for g in genomes),
        "expected_hi_exact": sum(g["expected_hi_exact"] for g in genomes),
        "or_pool_hi": math.exp(log_pool),
        "log_or_pool_hi": log_pool,
        "upper95_or_pool_hi": boot["upper95_or_hi"],
        "pooled_high_log_se": boot["log_se"],
        "bootstrap_depletion_p": boot["depletion_p"],
        "species_negative_fraction": sum(1 for value in full_logs if value < 0.0) / len(full_logs),
        "species_sign_p": sign_test_p_value(sum(1 for value in full_logs if value < 0.0), len(full_logs)),
        "genus_negative_fraction": genus_metrics["genus_negative_fraction"],
        "genus_sign_p": genus_metrics["genus_sign_p"],
        "genus_count": genus_metrics["genus_count"],
        "bin_ratios": ratios,
        "bin_logs": logs,
        "dose_monotone": monotone_nonincreasing(values),
        "dose_spearman": spearman(list(range(len(values))), values),
        "dose_negative_slope_bootstrap_fraction": boot["negative_dose_slope_fraction"],
        "p_decoy": decoy["p_decoy"],
        "global_decoy_pools": decoy["global_pools"],
        "carrier_decoy_pool_log_se": decoy["decoy_log_se"],
        "self_species_top5_fraction": sum(1 for r in self_ranks if r <= 0.05) / len(self_ranks) if self_ranks else 0.0,
        "self_species_with_decoy_variance": len(self_ranks),
        "log_or_hi_internal_pool": internal_pool,
        "robustness_same_sign": same_sign,
        "robustness_retains_70pct": retains,
        "internal_log_or_mean": mean(internal_logs),
        "null_replicates_verdict": NULL_REPLICATES_VERDICT,
        "use_exact_genewise_synonymous_expectation": USE_EXACT_GENEWISE_SYNONYMOUS_EXPECTATION,
    }


def preflight_gates(cohort):
    failures = []
    valid = cohort.get("valid_genomes", [])
    for genome in valid:
        prefix = genome.get("assembly_accession", "unknown") + ":"
        if genome.get("qc_cds", 0) < 800:
            failures.append(prefix + "qc_cds_lt_800")
        if genome.get("windows", 0) < 150000:
            failures.append(prefix + "internal_windows_lt_150000")
        if not genome.get("tail13"):
            failures.append(prefix + "unresolved_16s_tail")
        if genome.get("table11_fraction", 0.0) < 0.95:
            failures.append(prefix + "table11_fraction_lt_0_95")
        if genome.get("hi_state_count", 0) < 35:
            failures.append(prefix + "hi_state_count_lt_35")
        if genome.get("expected_hi_exact", 0.0) < 1000:
            failures.append(prefix + "expected_hi_exact_lt_1000")
        if not genome.get("finite_exact_matrices", False):
            failures.append(prefix + "nonfinite_exact_matrix")
        if genome.get("carrier_decoy_variance", 0.0) <= 0.0:
            failures.append(prefix + "carrier_decoy_variance_zero")
    genera = set(g.get("genus", "") for g in valid if g.get("genus"))
    total_windows = sum(g.get("windows", 0) for g in valid)
    total_dpos = sum(g.get("dpos_windows", 0.0) for g in valid)
    total_expected_hi = sum(g.get("expected_hi_exact", 0.0) for g in valid)
    pooled_se = cohort.get("metrics", {}).get("pooled_high_log_se", float("inf"))
    if len(valid) < 1000:
        failures.append("cohort_species_assemblies_lt_1000")
    if len(genera) < 200:
        failures.append("cohort_genera_lt_200")
    if total_windows < 50000000:
        failures.append("cohort_windows_lt_50000000")
    if total_dpos < 10000000:
        failures.append("cohort_testable_dpos_lt_10000000")
    if total_expected_hi < 1000000:
        failures.append("cohort_expected_hi_exact_lt_1000000")
    if pooled_se > 0.015:
        failures.append("cohort_genus_bootstrap_se_gt_0_015")
    if not cohort.get("exact_null_selftest_passed", False):
        failures.append("exact_null_selftest_failed")
    return {"passed": not failures, "failures": failures}


def derivation_state(cohort):
    otherwise = cohort.get("otherwise_valid_genomes", [])
    if not otherwise:
        return {"needs_derivation": False, "reasons": []}
    n = len(otherwise)
    hi_collapse = sum(1 for g in otherwise if g.get("hi_state_count", 0) < 10)
    orientation_ambiguous = sum(1 for g in otherwise if g.get("orientation_ambiguous"))
    exact_mismatch = sum(1 for g in otherwise if g.get("exact_expectation_mismatch"))
    reasons = []
    if orientation_ambiguous / n > 0.20:
        reasons.append("tail_orientation_ambiguous_gt_20_percent")
    if hi_collapse / n > 0.20:
        reasons.append("D_ge_4_state_collapse_gt_20_percent")
    if exact_mismatch / n > 0.20:
        reasons.append("exact_expectation_shuffle_mismatch_gt_20_percent")
    return {"needs_derivation": bool(reasons), "reasons": reasons}


def verdict_from_metrics(cohort):
    derivation = derivation_state(cohort)
    if derivation["needs_derivation"]:
        return "needs_derivation", {"derivation": derivation}
    gates = preflight_gates(cohort)
    if not gates["passed"]:
        return "data_gate_failed", {"preflight": gates}
    m = cohort["metrics"]
    hi_abs = abs(m["log_or_pool_hi"])
    d0_abs = abs(m["bin_logs"]["0"])
    localization = d0_abs <= 0.25 * hi_abs and hi_abs >= 3.0 * d0_abs
    certified_conditions = [
        m["or_pool_hi"] <= 0.95,
        m["upper95_or_pool_hi"] <= 0.97,
        m["species_negative_fraction"] >= 0.65,
        m["genus_negative_fraction"] >= 0.60,
        m["genus_sign_p"] <= 1.0e-4,
        m["bootstrap_depletion_p"] <= 1.0e-4,
        m["dose_monotone"],
        m["dose_spearman"] <= -0.70,
        m["dose_negative_slope_bootstrap_fraction"] >= 0.95,
        localization,
        m["p_decoy"] <= 0.01,
        m["self_species_top5_fraction"] >= 0.70,
        m["robustness_same_sign"],
        m["robustness_retains_70pct"],
    ]
    if all(certified_conditions):
        return "certified", {"preflight": gates, "conditions": {"localization": localization}}
    refuted_conditions = [
        m["or_pool_hi"] >= 0.99,
        m["log_or_pool_hi"] >= 0.0,
        m["species_negative_fraction"] < 0.55,
        m["genus_negative_fraction"] < 0.50,
        m["p_decoy"] >= 0.20,
        not m["dose_monotone"] or m["dose_spearman"] >= 0.0,
        d0_abs >= hi_abs,
        not m["robustness_same_sign"],
    ]
    if any(refuted_conditions):
        return "refuted", {"preflight": gates, "conditions": {"localization": localization}}
    if m["or_pool_hi"] < 1.0:
        return "coincidence", {"preflight": gates, "conditions": {"localization": localization}}
    return "refuted", {"preflight": gates, "conditions": {"localization": localization}}


def genus_from_name(name):
    match = re.match(r"([A-Z][A-Za-z0-9_.-]+)", name or "")
    return match.group(1) if match else ""


def analyze_assembly(row):
    accession = row["assembly_accession"]
    ftp_path = row["ftp_path"]
    asm = assembly_basename(ftp_path)
    _, md5_payload, md5_contact = fetch_md5checksums(row)
    md5s = parse_md5checksums(md5_payload.decode("utf-8", "replace")) if md5_payload else {}
    needed = ["_rna_from_genomic.fna.gz", "_cds_from_genomic.fna.gz"]
    files = {}
    contacts = {"md5checksums.txt": md5_contact}
    for suffix in needed:
        filename, payload, contact = fetch_assembly_file(row, suffix)
        contacts[filename] = contact
        if not payload:
            return {"assembly_accession": accession, "valid": False, "reason": "download_failed", "contacts": contacts}
        ok, reason = validate_md5(filename, payload, md5s)
        if not ok:
            return {"assembly_accession": accession, "valid": False, "reason": reason, "contacts": contacts}
        files[suffix] = payload
    records_16s = extract_16s_records(files["_rna_from_genomic.fna.gz"])
    tail13, tail_meta = resolve_tail13(records_16s)
    if not tail13:
        return {"assembly_accession": accession, "valid": False, "reason": "unresolved_16s_tail", "tail_meta": tail_meta}
    cds_records, cds_stats = qc_cds_records(files["_cds_from_genomic.fna.gz"])
    observed_matrix, expected_matrix, expected_internal_matrix = genome_pair_matrices(cds_records)
    maps, observed, expected, expected_internal = tail_scores(observed_matrix, expected_matrix, expected_internal_matrix, tail13)
    log_or = ratio_log(observed["hi"], expected["hi"])
    log_or_internal = ratio_log(observed["hi"], expected_internal["hi"])
    hi_state_count = sum(1 for v in maps["d"].values() if v >= 4)
    dpos_state_count = sum(1 for v in maps["d"].values() if v > 0)
    table11_fraction = (
        cds_stats.get("table_11_annotated_or_inferable", 0) / cds_stats.get("qc_passing", 1)
        if cds_stats.get("qc_passing", 0) else 0.0
    )
    decoy = decoy_specificity(records_16s, tail13, accession, log_or, observed_matrix, expected_matrix)
    out = {
        "assembly_accession": accession,
        "organism_name": row.get("organism_name", ""),
        "genus": genus_from_name(row.get("organism_name", "")),
        "species_taxid": row.get("species_taxid", ""),
        "valid": True,
        "ftp_path": ftp_path,
        "asm": asm,
        "tail13": tail13,
        "tail_meta": tail_meta,
        "qc_cds": cds_stats.get("qc_passing", 0),
        "cds_stats": cds_stats,
        "table11_fraction": table11_fraction,
        "windows": int(round(observed["windows"])),
        "dpos_windows": observed["dpos"],
        "observed_hi": observed["hi"],
        "observed_bins": observed["bins"],
        "expected_hi_exact": expected["hi"],
        "expected_bins_exact": expected["bins"],
        "expected_hi_internal_exact": expected_internal["hi"],
        "expected_bins_internal_exact": expected_internal["bins"],
        "or_hi_exact": ratio(observed["hi"], expected["hi"]),
        "log_or_hi_exact": log_or,
        "or_hi_internal_exact": ratio(observed["hi"], expected_internal["hi"]),
        "log_or_hi_internal_exact": log_or_internal,
        "hi_state_count": hi_state_count,
        "dpos_state_count": dpos_state_count,
        "d_hist": maps["hist"],
        "finite_exact_matrices": finite_matrix(observed_matrix) and finite_matrix(expected_matrix) and finite_matrix(expected_internal_matrix),
        "matrix_windows_observed": matrix_sum(observed_matrix),
        "matrix_windows_expected": matrix_sum(expected_matrix),
        "matrix_windows_expected_internal": matrix_sum(expected_internal_matrix),
        "decoy_rank_percentile": decoy["rank_percentile"],
        "n_decoys": decoy["n_decoys"],
        "carrier_decoy_variance": decoy["variance"],
        "decoy_logs": [row["log_or"] for row in decoy["decoys"]],
        "contacts": contacts,
    }
    return out


def run_real():
    if not run_exact_formula_selftest(replicates=max(2000, min(SELFTEST_SHUFFLES, 5000)))["passed"]:
        emit("data_gate_failed", reason="exact_null_selftest_failed")
    text, contact = read_text_cached(SUMMARY_URL, "assembly_summary.txt")
    if not text:
        emit("data_gate_failed", reason="assembly_summary_unreachable", contact=contact)
    rows = parse_assembly_summary(text)
    selected = select_species_assemblies(rows)
    valid = []
    invalid = []
    otherwise_valid = []
    for idx, row in enumerate(selected, 1):
        result = analyze_assembly(row)
        if result.get("tail13"):
            otherwise_valid.append(result)
        if result.get("valid"):
            valid.append(result)
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
    metrics = pooled_metrics(valid)
    cohort = {
        "valid_genomes": valid,
        "invalid_genomes": invalid,
        "otherwise_valid_genomes": otherwise_valid,
        "metrics": metrics,
        "exact_null_selftest_passed": True,
    }
    verdict, details = verdict_from_metrics(cohort)
    emit(
        verdict,
        summary_contact=contact,
        selected_assemblies=len(selected),
        valid_genomes=len(valid),
        invalid_genomes=len(invalid),
        metrics=metrics,
        details=details,
    )


def clean_json(value):
    if isinstance(value, dict):
        return {str(k): clean_json(v) for k, v in value.items() if k != "log_values"}
    if isinstance(value, list):
        return [clean_json(v) for v in value]
    if isinstance(value, float):
        if math.isnan(value):
            return "nan"
        if math.isinf(value):
            return "inf" if value > 0 else "-inf"
        return round_float(value)
    return value


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


def run_exact_formula_selftest(replicates=SELFTEST_SHUFFLES):
    reps = max(2000, int(replicates))
    codon_list = synthetic_formula_codons()
    _, expected = gene_observed_and_expected(codon_list, "full")
    sums = zero_matrix()
    sums_sq = zero_matrix()
    rng = random.Random(83391)
    for _ in range(reps):
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
        sample_mean = sums[idx] / reps
        variance = max(0.0, (sums_sq[idx] / reps) - sample_mean * sample_mean)
        se = math.sqrt(variance / reps) if variance > 0 else 0.0
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
        "replicates": reps,
        "checked_pairs": checked,
        "max_abs_error": max_abs,
        "max_mc_z": max_z,
        "failures": failures[:5],
    }


def selftest_pairing_and_d():
    tail = "AAAACCUCCUGGG"
    score = pairing_score(tail, "AGGAGG")
    maps = carrier_maps(tail)
    assert score == 16, score
    assert maps["d"]["AGGAGG"] > 0
    assert maps["d"]["AUGUGG"] == 0
    assert len(maps["d_by_index"]) == 61 * 61
    return {"pairing_score": score, "d_aggagg": maps["d"]["AGGAGG"], "d_augugg": maps["d"]["AUGUGG"]}


def selftest_matrix_accumulation():
    records = [{"codons": synthetic_formula_codons()}, {"codons": list(reversed(synthetic_formula_codons()))}]
    observed, expected, expected_internal = genome_pair_matrices(records)
    windows = matrix_sum(observed)
    assert abs(windows - matrix_sum(expected)) < 1.0e-9
    assert abs(windows - matrix_sum(expected_internal)) < 1.0e-9
    maps, observed_scores, expected_scores, _ = tail_scores(observed, expected, expected_internal, "AAAACCUCCUGGG")
    assert observed_scores["windows"] == windows
    assert expected_scores["windows"] > 0
    assert sum(1 for value in maps["d"].values() if value >= 4) >= 35
    assert score_matrix_by_d(observed, maps["d_by_index"])["hi"] == observed_scores["hi"]
    return {
        "windows": windows,
        "expected_windows": matrix_sum(expected),
        "hi_observed": observed_scores["hi"],
        "hi_expected": expected_scores["hi"],
    }


def synthetic_genomes_for_gates():
    genomes = []
    for i in range(1000):
        genus = "Genus%d" % (i % 200)
        log_or = math.log(0.94)
        g = {
            "assembly_accession": "GCF_SYN_%04d" % i,
            "qc_cds": 800,
            "windows": 150000,
            "tail13": "AAACCUCCUGGG",
            "table11_fraction": 0.95,
            "hi_state_count": 35,
            "dpos_state_count": 1200,
            "expected_hi_exact": 1000.0,
            "expected_hi_internal_exact": 1000.0,
            "finite_exact_matrices": True,
            "carrier_decoy_variance": 0.01,
            "dpos_windows": 10000.0,
            "genus": genus,
            "observed_hi": 940.0,
            "observed_bins": {"0": 1000.0, "1": 970.0, "2": 950.0, "3": 940.0, "4": 930.0, "5": 920.0, "6+": 910.0},
            "expected_bins_exact": {label: 1000.0 for label in BIN_LABELS},
            "log_or_hi_exact": log_or,
            "log_or_hi_internal_exact": log_or,
            "decoy_logs": [log_or + 0.2, log_or + 0.3],
            "decoy_rank_percentile": 0.01,
        }
        genomes.append(g)
    return genomes


def synthetic_cohort_for_gates():
    genomes = synthetic_genomes_for_gates()
    metrics = {
        "pooled_high_log_se": 0.01,
        "or_pool_hi": 0.94,
        "log_or_pool_hi": math.log(0.94),
        "upper95_or_pool_hi": 0.96,
        "bootstrap_depletion_p": 1.0e-5,
        "species_negative_fraction": 0.70,
        "genus_negative_fraction": 0.65,
        "genus_sign_p": 1.0e-5,
        "dose_monotone": True,
        "dose_spearman": -0.75,
        "dose_negative_slope_bootstrap_fraction": 0.96,
        "bin_logs": {"0": -0.005, "1": -0.04, "2": -0.06, "3": -0.08, "4": -0.20, "5": -0.25, "6+": -0.30},
        "p_decoy": 0.005,
        "self_species_top5_fraction": 0.75,
        "robustness_same_sign": True,
        "robustness_retains_70pct": True,
    }
    return {
        "valid_genomes": genomes,
        "otherwise_valid_genomes": genomes,
        "metrics": metrics,
        "exact_null_selftest_passed": True,
    }


def selftest_preflight():
    cohort = synthetic_cohort_for_gates()
    assert preflight_gates(cohort)["passed"]
    branches = {}
    edits = [
        ("qc_cds", 799, "qc_cds_lt_800"),
        ("windows", 149999, "internal_windows_lt_150000"),
        ("tail13", "", "unresolved_16s_tail"),
        ("table11_fraction", 0.949, "table11_fraction_lt_0_95"),
        ("hi_state_count", 34, "hi_state_count_lt_35"),
        ("expected_hi_exact", 999.0, "expected_hi_exact_lt_1000"),
        ("finite_exact_matrices", False, "nonfinite_exact_matrix"),
        ("carrier_decoy_variance", 0.0, "carrier_decoy_variance_zero"),
    ]
    for key, bad, marker in edits:
        altered = synthetic_cohort_for_gates()
        altered["valid_genomes"][0][key] = bad
        failures = preflight_gates(altered)["failures"]
        assert any(marker in item for item in failures), (key, failures[:5])
        branches[key] = marker
    cohort_failures = [
        ("species", lambda c: c["valid_genomes"].pop(), "cohort_species_assemblies_lt_1000"),
        ("genera", lambda c: [g.update({"genus": "Only"}) for g in c["valid_genomes"]], "cohort_genera_lt_200"),
        ("windows", lambda c: [g.update({"windows": 1}) for g in c["valid_genomes"]], "cohort_windows_lt_50000000"),
        ("dpos", lambda c: [g.update({"dpos_windows": 1}) for g in c["valid_genomes"]], "cohort_testable_dpos_lt_10000000"),
        ("expected_hi", lambda c: [g.update({"expected_hi_exact": 1}) for g in c["valid_genomes"]], "cohort_expected_hi_exact_lt_1000000"),
        ("pooled_se", lambda c: c["metrics"].update({"pooled_high_log_se": 0.016}), "cohort_genus_bootstrap_se_gt_0_015"),
        ("selftest", lambda c: c.update({"exact_null_selftest_passed": False}), "exact_null_selftest_failed"),
    ]
    for name, mutate, marker in cohort_failures:
        altered = synthetic_cohort_for_gates()
        mutate(altered)
        failures = preflight_gates(altered)["failures"]
        assert marker in failures, (name, failures)
        branches[name] = marker
    return {"branches": branches}


def verdict_fixture(kind):
    cohort = synthetic_cohort_for_gates()
    metrics = cohort["metrics"]
    if kind == "coincidence":
        metrics["p_decoy"] = 0.05
    elif kind == "refuted":
        metrics["or_pool_hi"] = 1.0
        metrics["log_or_pool_hi"] = 0.0
    elif kind == "needs_derivation":
        for g in cohort["otherwise_valid_genomes"][:250]:
            g["hi_state_count"] = 5
    elif kind == "data_gate_failed":
        cohort["valid_genomes"] = cohort["valid_genomes"][:10]
    return cohort


def selftest_verdicts():
    expected = {
        "certified": "certified",
        "coincidence": "coincidence",
        "refuted": "refuted",
        "needs_derivation": "needs_derivation",
        "data_gate_failed": "data_gate_failed",
    }
    out = {}
    for kind, want in expected.items():
        got, _ = verdict_from_metrics(verdict_fixture(kind))
        assert got == want, (kind, got, want)
        out[kind] = got
    return out


def run_selftest():
    formula = run_exact_formula_selftest()
    assert formula["passed"], formula
    payload = {
        "ok": True,
        "config": {
            "null_replicates_verdict": NULL_REPLICATES_VERDICT,
            "use_exact_genewise_synonymous_expectation": USE_EXACT_GENEWISE_SYNONYMOUS_EXPECTATION,
            "carrier_decoys": CARRIER_DECOYS,
            "global_decoy_pools": GLOBAL_DECOY_POOLS,
        },
        "exact_formula": formula,
        "pairing_and_d": selftest_pairing_and_d(),
        "matrix_accumulation": selftest_matrix_accumulation(),
        "preflight": selftest_preflight(),
        "verdicts": selftest_verdicts(),
    }
    print(json.dumps(clean_json(payload), ensure_ascii=True, sort_keys=True, separators=(",", ":")))


def main(argv):
    if "--selftest" in argv:
        run_selftest()
        return
    run_real()


if __name__ == "__main__":
    main(sys.argv[1:])

#!/usr/bin/env python3
"""ASD-W6 self-tail Window6 codon-pair forcing certificate."""
from __future__ import annotations

from collections import Counter, defaultdict
import csv
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


EXPERIMENT_ID = "asd_w6_self_tail"
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
NULL_REPLICATES = int(os.environ.get("ASD_W6_NULL_REPLICATES", "400"))
MAX_GENOMES = int(os.environ.get("ASD_W6_MAX_GENOMES", "0"))
FETCH_TIMEOUT = int(os.environ.get("ASD_W6_FETCH_TIMEOUT", "60"))
FETCH_ATTEMPTS = int(os.environ.get("ASD_W6_FETCH_ATTEMPTS", "3"))
NCBI_DELAY_SECONDS = float(os.environ.get("ASD_W6_NCBI_DELAY_SECONDS", "0.34"))
USER_AGENT = "asd-w6-self-tail"
BASES_RNA = set("ACGU")
BASES_DNA = set("ACGT")
BIN_LABELS = ("0", "1", "2", "3", "4", "5", "6+")
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


def stdev(values):
    return statistics.stdev(values) if len(values) >= 2 else 0.0


def emit(verdict, **fields):
    payload = {"verdict": verdict, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")))
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
    for species, items in sorted(by_species.items()):
        items.sort(key=lambda r: (category_rank(r.get("refseq_category")), tuple(-x for x in parse_date(r.get("seq_rel_date"))), r.get("assembly_accession") or ""))
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
    for c1 in SENSE_CODONS:
        for c2 in SENSE_CODONS:
            pair = c1 + c2
            b_map[pair] = pairing_score(tail13, pair)
    for c1 in SENSE_CODONS:
        aa1 = CODON_TO_AA[c1]
        for c2 in SENSE_CODONS:
            aa2 = CODON_TO_AA[c2]
            pair = c1 + c2
            floor = min(b_map[x + y] for x in SYNONYMS[aa1] for y in SYNONYMS[aa2])
            d_map[pair] = b_map[pair] - floor
    hist = Counter(d_map.values())
    return {"tail13": tail13, "b": b_map, "d": d_map, "hist": dict(sorted(hist.items()))}


def d_bin(value):
    return "6+" if value >= 6 else str(max(0, value))


def zero_counts():
    return {label: 0.0 for label in BIN_LABELS}


def add_counts(dst, src, scale=1.0):
    for key, value in src.items():
        dst[key] = dst.get(key, 0.0) + scale * value


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
    stats["table_11_annotated_or_inferable"] = sum(1 for r in records if r["table_11_annotated"] or r["table_11_inferable"])
    return records, dict(stats)


def count_observed(records, d_map):
    counts = zero_counts()
    hi = 0.0
    dpos = 0.0
    windows = 0
    for record in records:
        codon_list = record["codons"]
        for i in range(15, len(codon_list) - 10 - 1):
            pair = codon_list[i] + codon_list[i + 1]
            d = d_map[pair]
            counts[d_bin(d)] += 1.0
            if d >= 4:
                hi += 1.0
            if d > 0:
                dpos += 1.0
            windows += 1
    return {"bins": counts, "hi": hi, "dpos": dpos, "windows": windows}


def pair_counter_for_codons(codon_list):
    counts = Counter()
    for i in range(15, len(codon_list) - 10 - 1):
        counts[codon_list[i] + codon_list[i + 1]] += 1
    return counts


def pair_counter_for_records(records):
    counts = Counter()
    for record in records:
        counts.update(pair_counter_for_codons(record["codons"]))
    return counts


def count_pair_counter(pair_counts, d_map):
    bins = zero_counts()
    hi = 0.0
    dpos = 0.0
    windows = 0
    for pair, count in pair_counts.items():
        d = d_map[pair]
        bins[d_bin(d)] += float(count)
        if d >= 4:
            hi += float(count)
        if d > 0:
            dpos += float(count)
        windows += int(count)
    return {"bins": bins, "hi": hi, "dpos": dpos, "windows": windows}


def shuffled_gene_codons(codon_list, rng):
    out = list(codon_list)
    positions_by_aa = defaultdict(list)
    values_by_aa = defaultdict(list)
    for i, codon in enumerate(codon_list):
        aa = CODON_TO_AA[codon]
        positions_by_aa[aa].append(i)
        values_by_aa[aa].append(codon)
    for aa, positions in positions_by_aa.items():
        if len(SYNONYMS[aa]) <= 1:
            continue
        values = list(values_by_aa[aa])
        rng.shuffle(values)
        for pos, codon in zip(positions, values):
            out[pos] = codon
    return out


def shuffled_pair_counters(records, assembly_accession, replicates):
    out = []
    for rep in range(replicates):
        rng = random.Random(stable_seed(assembly_accession + ":" + str(rep)))
        counts = Counter()
        for record in records:
            counts.update(pair_counter_for_codons(shuffled_gene_codons(record["codons"], rng)))
        out.append(counts)
    return out


def null_from_pair_counters(pair_counters, d_map):
    hi_values = []
    bin_values = {label: [] for label in BIN_LABELS}
    for pair_counts in pair_counters:
        counted = count_pair_counter(pair_counts, d_map)
        hi_values.append(counted["hi"])
        for label in BIN_LABELS:
            bin_values[label].append(counted["bins"][label])
    return {"hi_values": hi_values, "bin_values": bin_values}


def analytical_null(records, d_map):
    bins = zero_counts()
    hi = 0.0
    windows = 0.0
    for record in records:
        codon_list = record["codons"]
        counts_by_aa = defaultdict(Counter)
        for codon in codon_list:
            counts_by_aa[CODON_TO_AA[codon]][codon] += 1
        totals_by_aa = {aa: sum(counts.values()) for aa, counts in counts_by_aa.items()}
        for i in range(15, len(codon_list) - 10 - 1):
            aa1 = CODON_TO_AA[codon_list[i]]
            aa2 = CODON_TO_AA[codon_list[i + 1]]
            n1 = totals_by_aa[aa1]
            n2 = totals_by_aa[aa2]
            if aa1 != aa2:
                denom = n1 * n2
                if denom <= 0:
                    continue
                for x, cx in counts_by_aa[aa1].items():
                    for y, cy in counts_by_aa[aa2].items():
                        weight = (cx * cy) / denom
                        d = d_map[x + y]
                        bins[d_bin(d)] += weight
                        if d >= 4:
                            hi += weight
            else:
                denom = n1 * (n1 - 1)
                if denom <= 0:
                    continue
                counts = counts_by_aa[aa1]
                for x, cx in counts.items():
                    for y, cy in counts.items():
                        numerator = cx * (cy - 1) if x == y else cx * cy
                        if numerator <= 0:
                            continue
                        weight = numerator / denom
                        d = d_map[x + y]
                        bins[d_bin(d)] += weight
                        if d >= 4:
                            hi += weight
            windows += 1.0
    return {"bins": bins, "hi": hi, "windows": windows}


def ratio_log(obs, exp):
    return math.log((obs + EPS) / (exp + EPS))


def genome_stats(observed, shuffle, analytical):
    null_hi = shuffle["hi_values"]
    expected_hi = mean(null_hi)
    sd_hi = stdev(null_hi)
    z = (observed["hi"] - expected_hi) / sd_hi if sd_hi > 0 else 0.0
    bins_expected = {label: mean(shuffle["bin_values"][label]) for label in BIN_LABELS}
    ratios = {label: (observed["bins"][label] + EPS) / (bins_expected[label] + EPS) for label in BIN_LABELS}
    return {
        "expected_hi_shuffle": expected_hi,
        "sd_hi_shuffle": sd_hi,
        "z": z,
        "or_hi_shuffle": (observed["hi"] + EPS) / (expected_hi + EPS),
        "log_or_hi_shuffle": ratio_log(observed["hi"], expected_hi),
        "expected_bins_shuffle": bins_expected,
        "bin_ratios_shuffle": ratios,
        "analytical_or_hi": (observed["hi"] + EPS) / (analytical["hi"] + EPS),
        "analytical_log_or_hi": ratio_log(observed["hi"], analytical["hi"]),
    }


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


def build_decoy_tails(records_16s, true_tail, accession):
    rng = random.Random(stable_seed(accession + ":decoys"))
    seq = records_16s[0]["sequence"] if records_16s else true_tail
    decoys = []
    for tail in internal_decoy_tails(seq, true_tail, rng, 700):
        decoys.append(("16s_internal", tail))
    for _ in range(200):
        tail = mono_shuffle_tail(true_tail, rng)
        if tail != true_tail:
            decoys.append(("mono_shuffle", tail))
    for tail in orientation_tails(true_tail, 100):
        decoys.append(("orientation", tail))
    while len(decoys) < 1000:
        decoys.append(("mono_shuffle", mono_shuffle_tail(true_tail, rng)))
    return decoys[:1000]


def decoy_effect(observed_pair_counts, null_pair_counts, tail):
    maps = carrier_maps(tail)
    observed = count_pair_counter(observed_pair_counts, maps["d"])
    shuffle = null_from_pair_counters(null_pair_counts, maps["d"])
    expected_hi = mean(shuffle["hi_values"])
    return {"observed_hi": observed["hi"], "expected_hi": expected_hi, "log_or": ratio_log(observed["hi"], expected_hi)}


def decoy_specificity(records_16s, true_tail, accession, true_log_or, observed_pair_counts, null_pair_counts):
    values = []
    for cls, tail in build_decoy_tails(records_16s, true_tail, accession):
        effect = decoy_effect(observed_pair_counts, null_pair_counts, tail)
        values.append({"class": cls, "tail13": tail, **effect})
    decoy_logs = [row["log_or"] for row in values if math.isfinite(row["log_or"])]
    stronger = sum(1 for v in decoy_logs if v <= true_log_or)
    rank = (stronger + 1) / (len(decoy_logs) + 1) if decoy_logs else None
    return {"rank_percentile": rank, "n_decoys": len(decoy_logs), "decoys": values}


def sign_test_p_value(n_negative, n_total):
    if n_total <= 0:
        return 1.0
    k = int(n_negative)
    logs = []
    for i in range(k, n_total + 1):
        logs.append(math.lgamma(n_total + 1) - math.lgamma(i + 1) - math.lgamma(n_total - i + 1) - n_total * math.log(2.0))
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


def dose_bootstrap_q(genomes, seed="dose_bootstrap", n_bootstrap=1000):
    if not genomes:
        return 1.0
    rng = random.Random(stable_seed(seed))
    failures = 0
    for _ in range(n_bootstrap):
        bins_obs = zero_counts()
        bins_exp = zero_counts()
        for _ in genomes:
            g = rng.choice(genomes)
            add_counts(bins_obs, g["observed_bins"])
            add_counts(bins_exp, g["expected_bins_shuffle"])
        ratios = [(bins_obs[label] + EPS) / (bins_exp[label] + EPS) for label in BIN_LABELS]
        if (not monotone_nonincreasing(ratios)) or spearman(list(range(len(ratios))), ratios) > -0.7:
            failures += 1
    return failures / n_bootstrap


def poisson_upper_log_se(expected, variance):
    if expected <= 0:
        return float("inf")
    return math.sqrt(max(variance, EPS)) / expected


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
        if genome.get("expected_hi_shuffle", 0.0) < 1000:
            failures.append(prefix + "expected_hi_lt_1000")
        if genome.get("sd_hi_shuffle", 0.0) <= 0.0:
            failures.append(prefix + "null_variance_zero")
    genera = set(g.get("genus", "") for g in valid if g.get("genus"))
    total_windows = sum(g.get("windows", 0) for g in valid)
    total_dpos = sum(g.get("dpos_windows", 0.0) for g in valid)
    total_expected_hi = sum(g.get("expected_hi_shuffle", 0.0) for g in valid)
    pooled_se = cohort.get("pooled_high_log_se", float("inf"))
    if len(valid) < 1000:
        failures.append("cohort_species_assemblies_lt_1000")
    if len(genera) < 200:
        failures.append("cohort_genera_lt_200")
    if total_windows < 50000000:
        failures.append("cohort_windows_lt_50000000")
    if total_dpos < 10000000:
        failures.append("cohort_testable_dpos_lt_10000000")
    if total_expected_hi < 1000000:
        failures.append("cohort_expected_hi_lt_1000000")
    if pooled_se > 0.01:
        failures.append("cohort_pooled_se_gt_0_01")
    return {"passed": not failures, "failures": failures}


def derivation_state(cohort):
    otherwise = cohort.get("otherwise_valid_genomes", [])
    if not otherwise:
        return {"needs_derivation": False, "reasons": []}
    n = len(otherwise)
    zero_nonzero = sum(1 for g in otherwise if g.get("dpos_state_count", 0) == 0)
    hi_collapse = sum(1 for g in otherwise if g.get("hi_state_count", 0) < 10)
    orientation_ambiguous = sum(1 for g in otherwise if g.get("orientation_ambiguous"))
    reasons = []
    if zero_nonzero / n > 0.20:
        reasons.append("nonzero_D_classes_absent_gt_20_percent")
    if orientation_ambiguous / n > 0.20:
        reasons.append("tail_orientation_ambiguous_gt_20_percent")
    if hi_collapse / n > 0.20:
        reasons.append("D_ge_4_state_collapse_gt_20_percent")
    return {"needs_derivation": bool(reasons), "reasons": reasons}


def pooled_metrics(genomes):
    obs_hi = sum(g["observed_hi"] for g in genomes)
    exp_hi = sum(g["expected_hi_shuffle"] for g in genomes)
    variance_hi = sum(g["sd_hi_shuffle"] ** 2 for g in genomes)
    se = poisson_upper_log_se(exp_hi, variance_hi)
    log_or = ratio_log(obs_hi, exp_hi)
    bins_obs = zero_counts()
    bins_exp = zero_counts()
    bins_ana = zero_counts()
    for g in genomes:
        add_counts(bins_obs, g["observed_bins"])
        add_counts(bins_exp, g["expected_bins_shuffle"])
        add_counts(bins_ana, g["analytical_bins"])
    ratios = {label: (bins_obs[label] + EPS) / (bins_exp[label] + EPS) for label in BIN_LABELS}
    logs = {label: ratio_log(bins_obs[label], bins_exp[label]) for label in BIN_LABELS}
    analytical_hi = sum(g["analytical_hi"] for g in genomes)
    z_items = []
    for g in genomes:
        weight = math.sqrt(min(float(g["windows"]), 150000.0))
        z_items.append((g["z"], weight))
    z_num = sum(z * w for z, w in z_items)
    z_den = math.sqrt(sum(w * w for _, w in z_items))
    stouffer = z_num / z_den if z_den > 0 else 0.0
    negative = sum(1 for g in genomes if g["z"] < 0)
    sign_p = sign_test_p_value(negative, len(genomes))
    values = [ratios[label] for label in BIN_LABELS]
    rho = spearman(list(range(len(values))), values)
    self_ranks = [g.get("decoy_rank_percentile") for g in genomes if g.get("decoy_rank_percentile") is not None]
    decoy_totals = []
    for idx in range(1000):
        obs = 0.0
        exp = 0.0
        used = 0
        for g in genomes:
            rows = g.get("decoys") or []
            if idx < len(rows):
                obs += float(rows[idx].get("observed_hi", 0.0))
                exp += float(rows[idx].get("expected_hi", 0.0))
                used += 1
        if used:
            decoy_totals.append(ratio_log(obs, exp))
    global_rank = None
    if decoy_totals:
        global_rank = (sum(1 for value in decoy_totals if value <= log_or) + 1) / (len(decoy_totals) + 1)
    return {
        "observed_hi": obs_hi,
        "expected_hi_shuffle": exp_hi,
        "or_hi_shuffle": (obs_hi + EPS) / (exp_hi + EPS),
        "log_or_hi_shuffle": log_or,
        "upper95_or_hi_shuffle": math.exp(log_or + 1.96 * se) if math.isfinite(se) else float("inf"),
        "pooled_high_log_se": se,
        "stouffer_z": stouffer,
        "species_negative_fraction": negative / len(genomes) if genomes else 0.0,
        "species_sign_p": sign_p,
        "species_sign_q": sign_p,
        "bin_ratios": ratios,
        "bin_logs": logs,
        "dose_monotone": monotone_nonincreasing(values),
        "dose_spearman": rho,
        "dose_bootstrap_q": dose_bootstrap_q(genomes),
        "analytical_or_hi": (obs_hi + EPS) / (analytical_hi + EPS),
        "analytical_log_or_hi": ratio_log(obs_hi, analytical_hi),
        "self_global_rank_percentile": global_rank,
        "self_species_top5_fraction": sum(1 for r in self_ranks if r <= 0.05) / len(self_ranks) if self_ranks else 0.0,
    }


def verdict_from_metrics(cohort):
    derivation = derivation_state(cohort)
    if derivation["needs_derivation"]:
        return "needs_derivation", {"derivation": derivation}
    gates = preflight_gates(cohort)
    if not gates["passed"]:
        return "data_gate_failed", {"preflight": gates}
    m = cohort["metrics"]
    hi_abs = abs(m["log_or_hi_shuffle"])
    d0_abs = abs(m["bin_logs"]["0"])
    localization = d0_abs <= 0.25 * hi_abs and hi_abs >= 3.0 * d0_abs
    certified_conditions = [
        m["or_hi_shuffle"] <= 0.95,
        m["upper95_or_hi_shuffle"] <= 0.97,
        m["species_negative_fraction"] >= 0.65,
        m["species_sign_q"] < 1.0e-6,
        m["stouffer_z"] <= -8.0,
        m["dose_monotone"],
        m["dose_spearman"] <= -0.7,
        m.get("dose_bootstrap_q", 1.0) < 1.0e-4,
        localization,
        (m["self_global_rank_percentile"] is not None and m["self_global_rank_percentile"] <= 0.01),
        m["self_species_top5_fraction"] >= 0.70,
        m["analytical_or_hi"] <= 0.95,
    ]
    if all(certified_conditions):
        return "certified", {"preflight": gates, "conditions": {"localization": localization}}
    refuted_conditions = [
        m["or_hi_shuffle"] >= 0.99,
        m["stouffer_z"] > -2.0,
        m["species_negative_fraction"] < 0.55,
        (m["self_global_rank_percentile"] is not None and m["self_global_rank_percentile"] > 0.50),
    ]
    if any(refuted_conditions):
        return "refuted", {"preflight": gates, "conditions": {"localization": localization}}
    if m["or_hi_shuffle"] < 1.0:
        return "coincidence", {"preflight": gates, "conditions": {"localization": localization}}
    return "refuted", {"preflight": gates, "conditions": {"localization": localization}}


def genus_from_name(name):
    match = re.match(r"([A-Z][A-Za-z0-9_.-]+)", name or "")
    return match.group(1) if match else ""


def analyze_assembly(row):
    accession = row["assembly_accession"]
    ftp_path = row["ftp_path"]
    asm = assembly_basename(ftp_path)
    md5_name, md5_payload, md5_contact = fetch_md5checksums(row)
    md5s = parse_md5checksums(md5_payload.decode("utf-8", "replace")) if md5_payload else {}
    needed = [
        "_rna_from_genomic.fna.gz",
        "_cds_from_genomic.fna.gz",
        "_genomic.gff.gz",
        "_assembly_report.txt",
    ]
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
    maps = carrier_maps(tail13)
    observed_pair_counts = pair_counter_for_records(cds_records)
    null_pair_counts = shuffled_pair_counters(cds_records, accession, NULL_REPLICATES)
    observed = count_pair_counter(observed_pair_counts, maps["d"])
    shuffle = null_from_pair_counters(null_pair_counts, maps["d"])
    analytical = analytical_null(cds_records, maps["d"])
    stats = genome_stats(observed, shuffle, analytical)
    hi_state_count = sum(1 for v in maps["d"].values() if v >= 4)
    dpos_state_count = sum(1 for v in maps["d"].values() if v > 0)
    table11_fraction = (
        cds_stats.get("table_11_annotated_or_inferable", 0) / cds_stats.get("qc_passing", 1)
        if cds_stats.get("qc_passing", 0) else 0.0
    )
    decoy = decoy_specificity(records_16s, tail13, accession, stats["log_or_hi_shuffle"], observed_pair_counts, null_pair_counts)
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
        "windows": observed["windows"],
        "dpos_windows": observed["dpos"],
        "observed_hi": observed["hi"],
        "observed_bins": observed["bins"],
        "analytical_hi": analytical["hi"],
        "analytical_bins": analytical["bins"],
        "hi_state_count": hi_state_count,
        "dpos_state_count": dpos_state_count,
        "d_hist": maps["hist"],
        "decoy_rank_percentile": decoy["rank_percentile"],
        "n_decoys": decoy["n_decoys"],
        "decoys": [
            {"observed_hi": row["observed_hi"], "expected_hi": row["expected_hi"], "log_or": row["log_or"]}
            for row in decoy["decoys"]
        ],
        "contacts": contacts,
    }
    out.update(stats)
    return out


def run_real():
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
    metrics = pooled_metrics(valid) if valid else {
        "pooled_high_log_se": float("inf"),
        "or_hi_shuffle": float("inf"),
        "upper95_or_hi_shuffle": float("inf"),
        "species_negative_fraction": 0.0,
        "species_sign_q": 1.0,
        "stouffer_z": 0.0,
        "bin_logs": {label: 0.0 for label in BIN_LABELS},
        "dose_monotone": False,
        "dose_spearman": 0.0,
        "self_global_rank_percentile": None,
        "self_species_top5_fraction": 0.0,
        "analytical_or_hi": float("inf"),
    }
    cohort = {
        "valid_genomes": valid,
        "invalid_genomes": invalid,
        "otherwise_valid_genomes": otherwise_valid,
        "metrics": metrics,
        "pooled_high_log_se": metrics.get("pooled_high_log_se", float("inf")),
    }
    verdict, details = verdict_from_metrics(cohort)
    emit(verdict, summary_contact=contact, selected_assemblies=len(selected), metrics=clean_json(metrics), details=clean_json(details))


def clean_json(value):
    if isinstance(value, dict):
        return {str(k): clean_json(v) for k, v in value.items()}
    if isinstance(value, list):
        return [clean_json(v) for v in value]
    if isinstance(value, float):
        if math.isnan(value):
            return "nan"
        if math.isinf(value):
            return "inf" if value > 0 else "-inf"
        return round_float(value)
    return value


def selftest_pairing_and_d():
    tail = "AAAACCUCCUGGG"
    score = pairing_score(tail, "AGGAGG")
    maps = carrier_maps(tail)
    assert score == 16, score
    assert maps["d"]["AGGAGG"] > 0
    assert maps["d"]["AUGUGG"] == 0
    return {"pairing_score": score, "d_aggagg": maps["d"]["AGGAGG"], "d_augugg": maps["d"]["AUGUGG"]}


def selftest_shuffle():
    codon_list = ["GCU", "GCC", "GCA", "GCG", "UUU", "UUC", "GCU", "GCC"]
    record = {"codons": codon_list}
    rng = random.Random(17)
    shuffled = shuffled_gene_codons(codon_list, rng)
    assert aa_seq(codon_list) == aa_seq(shuffled)
    assert Counter(codon_list) == Counter(shuffled)
    assert Counter(c[2] in "GC" for c in codon_list) == Counter(c[2] in "GC" for c in shuffled)
    assert len(shuffled) == len(codon_list)
    assert record["codons"] == codon_list
    return {"protein": aa_seq(codon_list), "changed": shuffled != codon_list}


def synthetic_cohort_for_gates():
    genome = {
        "assembly_accession": "GCF_SYN",
        "qc_cds": 800,
        "windows": 50000000,
        "tail13": "AAACCUCCUGGG",
        "table11_fraction": 0.95,
        "hi_state_count": 35,
        "dpos_state_count": 1200,
        "expected_hi_shuffle": 1000000.0,
        "sd_hi_shuffle": 1000.0,
        "dpos_windows": 10000000.0,
        "genus": "Genus0",
    }
    genomes = []
    for i in range(1000):
        g = dict(genome)
        g["assembly_accession"] = "GCF_SYN_%04d" % i
        g["genus"] = "Genus%d" % (i % 200)
        g["windows"] = 150000
        g["dpos_windows"] = 10000
        g["expected_hi_shuffle"] = 1000.0
        g["sd_hi_shuffle"] = 0.001
        genomes.append(g)
    return {"valid_genomes": genomes, "otherwise_valid_genomes": genomes, "pooled_high_log_se": 0.01, "metrics": {}}


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
        ("expected_hi_shuffle", 999.0, "expected_hi_lt_1000"),
        ("sd_hi_shuffle", 0.0, "null_variance_zero"),
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
        ("expected_hi", lambda c: [g.update({"expected_hi_shuffle": 1}) for g in c["valid_genomes"]], "cohort_expected_hi_lt_1000000"),
        ("pooled_se", lambda c: c.update({"pooled_high_log_se": 0.011}), "cohort_pooled_se_gt_0_01"),
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
    metrics = {
        "or_hi_shuffle": 0.94,
        "log_or_hi_shuffle": math.log(0.94),
        "upper95_or_hi_shuffle": 0.96,
        "species_negative_fraction": 0.70,
        "species_sign_q": 1.0e-7,
        "stouffer_z": -9.0,
        "dose_monotone": True,
        "dose_spearman": -0.75,
        "dose_bootstrap_q": 0.0,
        "bin_logs": {"0": -0.005, "1": -0.04, "2": -0.06, "3": -0.08, "4": -0.20, "5": -0.25, "6+": -0.30},
        "self_global_rank_percentile": 0.005,
        "self_species_top5_fraction": 0.75,
        "analytical_or_hi": 0.94,
        "pooled_high_log_se": 0.01,
    }
    cohort["metrics"] = metrics
    if kind == "coincidence":
        metrics["dose_monotone"] = False
        metrics["dose_spearman"] = -0.1
    elif kind == "refuted":
        metrics["or_hi_shuffle"] = 1.0
    elif kind == "needs_derivation":
        for g in cohort["otherwise_valid_genomes"][:250]:
            g["dpos_state_count"] = 0
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
    payload = {
        "ok": True,
        "pairing_and_d": selftest_pairing_and_d(),
        "shuffle": selftest_shuffle(),
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

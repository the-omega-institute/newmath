#!/usr/bin/env python3
"""Window6 U-cluster transducer against m1Psi polysome-load shift."""
from __future__ import annotations

from collections import defaultdict
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
import urllib.request
import xml.etree.ElementTree as ET
import zipfile


CLAIM_ID = "window_codon_bridge.kpsi_w6_ucluster_transducer"
EXPERIMENT_ID = "kpsi_w6_ucluster_transducer"
CARRIER_URL = "https://static-content.springer.com/esm/art%3A10.1038%2Fs41586-025-09945-5/MediaObjects/41586_2025_9945_MOESM3_ESM.xlsx"
READOUT_URL = "https://ftp.ncbi.nlm.nih.gov/geo/series/GSE309nnn/GSE309271/suppl/GSE309271_library_reads.tsv.gz"
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(SCRIPT_DIR)))
DEFAULT_CACHE_DIR = os.path.join(REPO_ROOT, "tools", "window_codon_bridge", "synced", "kpsi_w6_ucluster_transducer")
USER_AGENT = "kpsi-w6-ucluster-transducer"
EPS = 1.0e-12


CODON_TO_AA = {
    "TTT": "F", "TTC": "F", "TTA": "L", "TTG": "L",
    "TCT": "S", "TCC": "S", "TCA": "S", "TCG": "S",
    "TAT": "Y", "TAC": "Y", "TAA": "*", "TAG": "*",
    "TGT": "C", "TGC": "C", "TGA": "*", "TGG": "W",
    "CTT": "L", "CTC": "L", "CTA": "L", "CTG": "L",
    "CCT": "P", "CCC": "P", "CCA": "P", "CCG": "P",
    "CAT": "H", "CAC": "H", "CAA": "Q", "CAG": "Q",
    "CGT": "R", "CGC": "R", "CGA": "R", "CGG": "R",
    "ATT": "I", "ATC": "I", "ATA": "I", "ATG": "M",
    "ACT": "T", "ACC": "T", "ACA": "T", "ACG": "T",
    "AAT": "N", "AAC": "N", "AAA": "K", "AAG": "K",
    "AGT": "S", "AGC": "S", "AGA": "R", "AGG": "R",
    "GTT": "V", "GTC": "V", "GTA": "V", "GTG": "V",
    "GCT": "A", "GCC": "A", "GCA": "A", "GCG": "A",
    "GAT": "D", "GAC": "D", "GAA": "E", "GAG": "E",
    "GGT": "G", "GGC": "G", "GGA": "G", "GGG": "G",
}
STOP_CODONS = {codon for codon, aa in CODON_TO_AA.items() if aa == "*"}
ORDER_CARRIERS = ("kpsi", "acluster", "ccluster", "gcluster", "purine_cluster", "single_window_u")
DECOY_NAMES = ("acluster", "ccluster", "gcluster", "purine_cluster", "single_window_u", "raw_total_u")


def stable_seed(text):
    return int.from_bytes(hashlib.sha256(text.encode("utf-8")).digest()[:16], "big")


def clean_json(value):
    if isinstance(value, dict):
        return {str(k): clean_json(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [clean_json(v) for v in value]
    if isinstance(value, float):
        if not math.isfinite(value):
            return None
        out = round(value, 12)
        return 0.0 if out == -0.0 else out
    return value


def emit_json(payload, code=0):
    print(json.dumps(clean_json(payload), ensure_ascii=True, sort_keys=True, separators=(",", ":")))
    sys.exit(code)


def mean(values):
    return sum(values) / len(values) if values else 0.0


def variance(values):
    if not values:
        return 0.0
    m = mean(values)
    return sum((x - m) * (x - m) for x in values) / len(values)


def sample_sd(values):
    if len(values) < 2:
        return 0.0
    return statistics.stdev(values)


def median(values):
    return statistics.median(values) if values else 0.0


def choose2(n):
    return n * (n - 1) / 2.0


def fetch_or_read(env_name, default_url, cache_name, cache_dir):
    value = os.environ.get(env_name, "").strip()
    if value and os.path.exists(value):
        with open(value, "rb") as handle:
            return handle.read(), value
    url = value or default_url
    os.makedirs(cache_dir, exist_ok=True)
    cache_path = os.path.join(cache_dir, cache_name)
    if os.path.exists(cache_path) and os.path.getsize(cache_path) > 0:
        with open(cache_path, "rb") as handle:
            return handle.read(), cache_path
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=90) as response:
        payload = response.read()
    with open(cache_path, "wb") as handle:
        handle.write(payload)
    return payload, cache_path


def col_from_cell(cell_ref):
    return re.sub(r"[^A-Z]", "", cell_ref.upper())


def row_from_cell(cell_ref):
    digits = re.sub(r"[^0-9]", "", cell_ref)
    return int(digits) if digits else 0


def xml_texts(element, ns):
    return "".join((node.text or "") for node in element.iter("{%s}t" % ns))


def read_shared_strings(zf):
    path = "xl/sharedStrings.xml"
    if path not in zf.namelist():
        return []
    ns = "http://schemas.openxmlformats.org/spreadsheetml/2006/main"
    root = ET.fromstring(zf.read(path))
    return [xml_texts(si, ns) for si in root.findall("{%s}si" % ns)]


def workbook_sheet_paths(zf):
    main_ns = "http://schemas.openxmlformats.org/spreadsheetml/2006/main"
    rel_ns = "http://schemas.openxmlformats.org/package/2006/relationships"
    office_ns = "http://schemas.openxmlformats.org/officeDocument/2006/relationships"
    workbook = ET.fromstring(zf.read("xl/workbook.xml"))
    rels = ET.fromstring(zf.read("xl/_rels/workbook.xml.rels"))
    rel_targets = {}
    for rel in rels:
        rid = rel.attrib.get("Id", "")
        target = rel.attrib.get("Target", "")
        if target and not target.startswith("/"):
            target = "xl/" + target
        rel_targets[rid] = target
    out = {}
    for sheet in workbook.findall(".//{%s}sheet" % main_ns):
        name = sheet.attrib.get("name", "")
        rid = sheet.attrib.get("{%s}id" % office_ns, "")
        if name and rid in rel_targets:
            out[name] = rel_targets[rid]
    return out


def decode_xlsx_cell(cell, shared_strings):
    main_ns = "http://schemas.openxmlformats.org/spreadsheetml/2006/main"
    ctype = cell.attrib.get("t", "")
    v = cell.find("{%s}v" % main_ns)
    if ctype == "s":
        if v is None or v.text is None:
            return ""
        idx = int(v.text)
        return shared_strings[idx] if 0 <= idx < len(shared_strings) else ""
    if ctype == "inlineStr":
        inline = cell.find("{%s}is" % main_ns)
        return xml_texts(inline, main_ns) if inline is not None else ""
    if v is None or v.text is None:
        return ""
    return v.text


def read_xlsx_sheet_rows(payload, sheet_name):
    temp_path = "/tmp/kpsi_xlsx_%s.xlsx" % os.getpid()
    with open(temp_path, "wb") as handle:
        handle.write(payload)
    try:
        with zipfile.ZipFile(temp_path) as zf:
            shared = read_shared_strings(zf)
            paths = workbook_sheet_paths(zf)
            if sheet_name not in paths:
                raise ValueError("missing sheet: %s" % sheet_name)
            main_ns = "http://schemas.openxmlformats.org/spreadsheetml/2006/main"
            root = ET.fromstring(zf.read(paths[sheet_name]))
            rows = defaultdict(dict)
            for cell in root.iter("{%s}c" % main_ns):
                ref = cell.attrib.get("r", "")
                r = row_from_cell(ref)
                c = col_from_cell(ref)
                if r and c:
                    rows[r][c] = decode_xlsx_cell(cell, shared)
            return [rows[i] for i in sorted(rows)]
    finally:
        try:
            os.remove(temp_path)
        except OSError:
            pass


def parse_fluc_library(payload):
    rows = read_xlsx_sheet_rows(payload, "fluc_library")
    records = []
    for row in rows[1:]:
        name = (row.get("A") or "").strip()
        seq = re.sub(r"\s+", "", row.get("P") or "").upper().replace("U", "T")
        if not name:
            continue
        records.append({
            "id": name,
            "sequence": seq,
            "raw_length": len(seq),
            "paper_score": parse_float(row.get("N")),
            "raw_percent_u": parse_float(row.get("D")),
        })
    return records


def parse_float(value):
    try:
        return float(str(value).strip())
    except (TypeError, ValueError):
        return None


def parse_int(value):
    try:
        return int(float(str(value).strip()))
    except (TypeError, ValueError):
        return 0


def read_library_reads(payload):
    text = gzip.decompress(payload).decode("utf-8", "replace")
    lines = [line for line in text.splitlines() if line.strip()]
    if not lines:
        raise ValueError("empty readout table")
    header = lines[0].split("\t")
    rows = {}
    for line in lines[1:]:
        fields = line.split("\t")
        if len(fields) < len(header):
            fields += ["0"] * (len(header) - len(fields))
        row = dict(zip(header, fields))
        vid = row.get("sequence", "").strip()
        if vid:
            rows[vid] = {k: parse_int(v) for k, v in row.items() if k != "sequence"}
    return header, rows


def required_readout_columns():
    columns = []
    for cond in ("n1m", "utp"):
        for rep in ("a", "b", "c"):
            columns.append("all_%s_%s" % (cond, rep))
    for frac in range(1, 6):
        for cond in ("n1m", "utp"):
            for rep in ("a", "b", "c"):
                columns.append("frac%d_%s_%s" % (frac, cond, rep))
    return columns


def extract_orf(sequence):
    seq = re.sub(r"[^ACGT]", "", sequence.upper().replace("U", "T"))
    start = seq.find("ATG")
    if start < 0:
        return None, None, "missing_start"
    for pos in range(start, len(seq) - 2, 3):
        codon = seq[pos:pos + 3]
        if codon in STOP_CODONS:
            cds = seq[start:pos]
            if len(cds) == 0 or len(cds) % 3 != 0:
                return None, None, "bad_frame"
            return [cds[i:i + 3] for i in range(0, len(cds), 3)], codon, ""
    return None, None, "missing_stop"


def translate_codons(codons):
    aas = []
    for codon in codons:
        aa = CODON_TO_AA.get(codon)
        if aa is None or aa == "*":
            return None
        aas.append(aa)
    return "".join(aas)


def score_codons_all(codons):
    totals = {name: 0.0 for name in ORDER_CARRIERS}
    if len(codons) < 2:
        return totals
    for i in range(len(codons) - 1):
        window = codons[i] + codons[i + 1]
        a = window.count("A")
        c = window.count("C")
        g = window.count("G")
        t = window.count("T")
        totals["kpsi"] += choose2(t)
        totals["acluster"] += choose2(a)
        totals["ccluster"] += choose2(c)
        totals["gcluster"] += choose2(g)
        totals["purine_cluster"] += choose2(a + g)
        totals["single_window_u"] += float(t)
    denom = float(len(codons) - 1)
    return {name: totals[name] / denom for name in totals}


def raw_total_u_score(codons, percent_u):
    if percent_u is not None:
        return percent_u
    seq = "".join(codons)
    return 100.0 * seq.count("T") / len(seq) if seq else 0.0


def shuffled_synonymous_codons(codons, protein, rng):
    out = list(codons)
    positions = defaultdict(list)
    for idx, aa in enumerate(protein):
        positions[aa].append(idx)
    for aa, idxs in positions.items():
        values = [out[idx] for idx in idxs]
        rng.shuffle(values)
        for j, idx in enumerate(idxs):
            out[idx] = values[j]
    return out


def compute_order_carriers(variants, b_variant, rng):
    for variant in variants:
        observed = score_codons_all(variant["codons"])
        shuffle_scores = {name: [] for name in ORDER_CARRIERS}
        for _ in range(b_variant):
            shuffled = shuffled_synonymous_codons(variant["codons"], variant["protein"], rng)
            scores = score_codons_all(shuffled)
            for name in ORDER_CARRIERS:
                shuffle_scores[name].append(scores[name])
        carrier = {}
        for name in ORDER_CARRIERS:
            mu = mean(shuffle_scores[name])
            sd = sample_sd(shuffle_scores[name])
            z = None if sd <= EPS else (observed[name] - mu) / sd
            null_z = [] if sd <= EPS else [(x - mu) / sd for x in shuffle_scores[name]]
            carrier[name] = {
                "observed": observed[name],
                "mean_shuffle": mu,
                "sd_shuffle": sd,
                "z": z,
                "null_z": null_z,
            }
        variant["carriers"] = carrier
        variant["raw_total_u"] = raw_total_u_score(variant["codons"], variant.get("raw_percent_u"))


def pli_for(row, cond, rep):
    denom = 0
    numer = 0
    for frac in range(1, 6):
        count = row.get("frac%d_%s_%s" % (frac, cond, rep), 0)
        denom += count
        numer += frac * count
    return None if denom <= 0 else float(numer) / float(denom)


def count_qc(row):
    for cond in ("n1m", "utp"):
        total = sum(row.get("all_%s_%s" % (cond, rep), 0) for rep in ("a", "b", "c"))
        frac_total = sum(row.get("frac%d_%s_%s" % (frac, cond, rep), 0) for frac in range(1, 6) for rep in ("a", "b", "c"))
        if total < 100 or frac_total < 100:
            return False
    return True


def attach_readout(variant, row):
    pl = {}
    for cond in ("n1m", "utp"):
        for rep in ("a", "b", "c"):
            value = pli_for(row, cond, rep)
            if value is None:
                return False
            pl[(cond, rep)] = value
    variant["pli"] = pl
    variant["dpli"] = mean([pl[("n1m", rep)] for rep in ("a", "b", "c")]) - mean([pl[("utp", rep)] for rep in ("a", "b", "c")])
    variant["total_abundance"] = mean([row.get("all_%s_%s" % (cond, rep), 0) for cond in ("n1m", "utp") for rep in ("a", "b", "c")])
    variant["median_total_count"] = median([row.get("all_%s_%s" % (cond, rep), 0) for cond in ("n1m", "utp") for rep in ("a", "b", "c")])
    variant["median_fraction_count"] = median([row.get("frac%d_%s_%s" % (frac, cond, rep), 0) for frac in range(1, 6) for cond in ("n1m", "utp") for rep in ("a", "b", "c")])
    return True


def ranks(values):
    indexed = sorted(enumerate(values), key=lambda item: item[1])
    out = [0.0] * len(values)
    i = 0
    while i < len(indexed):
        j = i + 1
        while j < len(indexed) and indexed[j][1] == indexed[i][1]:
            j += 1
        rank = (i + 1 + j) / 2.0
        for k in range(i, j):
            out[indexed[k][0]] = rank
        i = j
    return out


def pearson(x_values, y_values):
    if len(x_values) != len(y_values) or len(x_values) < 2:
        return 0.0
    mx = mean(x_values)
    my = mean(y_values)
    num = sum((x - mx) * (y - my) for x, y in zip(x_values, y_values))
    vx = sum((x - mx) * (x - mx) for x in x_values)
    vy = sum((y - my) * (y - my) for y in y_values)
    if vx <= EPS or vy <= EPS:
        return 0.0
    return num / math.sqrt(vx * vy)


def spearman(x_values, y_values):
    if len(x_values) != len(y_values) or len(x_values) < 2:
        return 0.0
    return pearson(ranks(x_values), ranks(y_values))


def one_sided_order_null(variants, dpli_values, observed_rho, b_global, rng):
    ge = 0
    completed = 0
    for _ in range(b_global):
        xs = []
        usable = True
        for variant in variants:
            null_z = variant["carriers"]["kpsi"]["null_z"]
            if not null_z:
                usable = False
                break
            xs.append(null_z[rng.randrange(len(null_z))])
        if not usable:
            continue
        completed += 1
        if spearman(xs, dpli_values) >= observed_rho:
            ge += 1
    return (1.0 + ge) / (1.0 + completed) if completed else 1.0, completed


def one_sided_label_null(z_values, dpli_values, observed_rho, b_label, rng):
    z_ranks = ranks(z_values)
    y_ranks = ranks(dpli_values)
    ge = 0
    for _ in range(b_label):
        shuffled = list(y_ranks)
        rng.shuffle(shuffled)
        if pearson(z_ranks, shuffled) >= observed_rho:
            ge += 1
    return (1.0 + ge) / (1.0 + b_label)


def top_bottom_gap(z_values, dpli_values, b_boot, rng):
    paired = sorted(zip(z_values, dpli_values), key=lambda item: item[0])
    q = max(1, len(paired) // 5)
    bottom = [y for _, y in paired[:q]]
    top = [y for _, y in paired[-q:]]
    gap = mean(top) - mean(bottom)
    boots = []
    for _ in range(b_boot):
        top_sample = [top[rng.randrange(len(top))] for _ in top]
        bottom_sample = [bottom[rng.randrange(len(bottom))] for _ in bottom]
        boots.append(mean(top_sample) - mean(bottom_sample))
    boots.sort()
    lower = boots[int(0.025 * (len(boots) - 1))] if boots else gap
    return gap, lower


def replicate_consistency(variants, z_values):
    rhos = []
    for nrep in ("a", "b", "c"):
        for urep in ("a", "b", "c"):
            y = [variant["pli"][("n1m", nrep)] - variant["pli"][("utp", urep)] for variant in variants]
            rhos.append(spearman(z_values, y))
    return sum(1 for r in rhos if r > 0), median(rhos), rhos


def decoy_correlations(variants, dpli_values):
    out = {}
    for name in ("acluster", "ccluster", "gcluster", "purine_cluster", "single_window_u"):
        xs = []
        for variant in variants:
            z = variant["carriers"][name]["z"]
            xs.append(0.0 if z is None else z)
        out[name] = spearman(xs, dpli_values)
    out["raw_total_u"] = spearman([variant["raw_total_u"] for variant in variants], dpli_values)
    return out


def kpsi_specificity(kpsi_rho, decoy_rhos):
    ge = sum(1 for value in decoy_rhos.values() if value >= kpsi_rho - EPS)
    rank = 1 + ge
    return rank, ge == 0


def evaluate_preflight(facts):
    failures = []
    classes = []
    def add(name, cls):
        failures.append(name)
        classes.append(cls)
    if facts.get("mapped", 0) <= 0:
        add("data:variant_ids_not_mapped_to_sequences", "data")
    if facts.get("missing_columns"):
        add("data:missing_required_readout_columns", "data")
    if facts.get("same_protein_frac", 0.0) < 0.90:
        add("carrier:same_protein_fraction_below_90pct", "derivation")
    if not facts.get("retained_exact_same_protein", False):
        add("carrier:retained_set_not_same_protein", "derivation")
    if facts.get("n_retained", 0) < 250:
        add("power:retained_variants_below_250", "power" if facts.get("n_retained", 0) >= 200 else "data")
    if facts.get("retained_fraction", 0.0) < 0.80:
        add("data:retained_fraction_below_80pct", "data")
    if not facts.get("all_cds_lengths_identical", False):
        add("data:retained_cds_lengths_not_identical", "data")
    if facts.get("usable_n1m_reps", 0) < 3 or facts.get("usable_utp_reps", 0) < 3:
        add("data:replicate_count_below_3", "data")
    if facts.get("median_total_count", 0.0) < 500:
        add("data:median_total_count_below_500", "data")
    if facts.get("median_fraction_count", 0.0) < 500:
        add("data:median_fraction_count_below_500", "data")
    if facts.get("var_dpli", 0.0) <= EPS:
        add("data:dpli_zero_variance", "data")
    if facts.get("var_zorder", 0.0) <= EPS:
        add("carrier:zorder_zero_variance", "derivation")
    if facts.get("nonzero_shuffle_sd_fraction", 0.0) < 0.80:
        add("carrier:shuffle_sd_nonzero_fraction_below_80pct", "derivation")
    if not facts.get("b_variant_completed", False):
        add("carrier:b_variant_not_completed", "derivation")
    if not facts.get("b_global_completed", False):
        add("carrier:b_global_not_completed", "derivation")
    if not facts.get("b_label_completed", False):
        add("data:b_label_not_completed", "data")
    if not facts.get("decoy_variance_nonzero", False):
        add("carrier:decoy_variance_zero", "derivation")
    return {"passed": not failures, "failures": failures, "_classes": classes}


def decide_verdict(preflight, metrics, n_retained):
    classes = preflight.get("_classes", [])
    if not preflight.get("passed", False):
        if "derivation" in classes:
            return "needs_derivation"
        if "power" in classes:
            return "needs_more_data"
        return "data_gate_failed"
    rho = metrics["spearman_rho"]
    pear = metrics["pearson_r"]
    p_order = metrics["p_order"]
    p_label = metrics["p_label"]
    gap = metrics["topbot_quintile_gap"]
    lower = metrics["topbot_ci_lower"]
    pos = metrics["replicate_pos_pairs"]
    med_rep = metrics["median_replicate_rho"]
    top5 = metrics["kpsi_top5pct"]
    ratio = metrics["abundance_corr_ratio"]
    certified = (
        rho >= 0.20 and pear >= 0.15 and p_order <= 0.01 and p_label <= 0.01
        and gap >= 0.15 and lower > 0.0 and pos >= 7 and med_rep >= 0.15
        and top5 and ratio <= 0.5
    )
    if certified:
        return "certified"
    if rho <= 0.0 or p_label >= 0.20 or p_order >= 0.20 or gap <= 0.0 or pos <= 3:
        return "refuted"
    # Coincidence = nominal positive AND significant, but NECESSITY fails and cannot be
    # rescued by collecting more data: the specific Window6 carrier does not beat the
    # composition-matched decoys (raw total U / single-window U -> not top5), or total
    # RNA abundance explains the same signal (ratio > 0.5). This necessity failure takes
    # precedence over the power-band needs_more_data check below.
    if rho > 0.0 and p_label < 0.05 and (not top5 or ratio > 0.5):
        return "coincidence"
    if 0.0 < rho < 0.20 or 0.01 < p_order < 0.20 or 0.01 < p_label < 0.20 or pos in (5, 6) or 200 <= n_retained < 250:
        return "needs_more_data"
    if rho > 0.0 and p_label < 0.05:
        return "coincidence"
    return "refuted"


def build_variants(carrier_records, readout_rows):
    by_id = {record["id"]: record for record in carrier_records}
    ids = sorted(set(by_id) & set(readout_rows))
    variants = []
    length_classes = defaultdict(int)
    protein_counts = defaultdict(int)
    for vid in ids:
        rec = by_id[vid]
        length_classes[str(rec["raw_length"])] += 1
        codons, stop, error = extract_orf(rec["sequence"])
        if error:
            continue
        protein = translate_codons(codons)
        if not protein:
            continue
        protein_counts[protein] += 1
        row = readout_rows[vid]
        variant = {
            "id": vid,
            "codons": codons,
            "stop": stop,
            "protein": protein,
            "raw_percent_u": rec.get("raw_percent_u"),
            "paper_score": rec.get("paper_score"),
            "cds_len": len(codons),
        }
        if attach_readout(variant, row):
            variant["count_qc"] = count_qc(row)
            variants.append(variant)
    if protein_counts:
        major_protein = max(protein_counts, key=lambda p: protein_counts[p])
        same_protein_frac = float(protein_counts[major_protein]) / float(sum(protein_counts.values()))
    else:
        major_protein = ""
        same_protein_frac = 0.0
    return ids, variants, major_protein, same_protein_frac, dict(length_classes)


def analyze():
    cache_dir = os.environ.get("KPSI_CACHE_DIR", DEFAULT_CACHE_DIR)
    b_variant = int(os.environ.get("KPSI_B_VARIANT", "500"))
    b_global = int(os.environ.get("KPSI_B_GLOBAL", "10000"))
    b_label = int(os.environ.get("KPSI_B_LABEL", "10000"))
    b_boot = int(os.environ.get("KPSI_B_BOOT", str(b_label)))
    seed_text = os.environ.get("KPSI_SEED", "kpsi-w6-ucluster-transducer")
    rng = random.Random(stable_seed(seed_text))
    carrier_payload, _ = fetch_or_read("KPSI_CARRIER_XLSX", CARRIER_URL, "suppl_table1.xlsx", cache_dir)
    readout_payload, _ = fetch_or_read("KPSI_READOUT_TSVGZ", READOUT_URL, "library_reads.tsv.gz", cache_dir)
    carrier_records = parse_fluc_library(carrier_payload)
    header, readout_rows = read_library_reads(readout_payload)
    missing_columns = [col for col in required_readout_columns() if col not in header]
    mapped_ids, variants_all, major_protein, same_protein_frac, length_classes = build_variants(carrier_records, readout_rows)
    same_protein_variants = [v for v in variants_all if v["protein"] == major_protein and v["count_qc"]]
    compute_order_carriers(same_protein_variants, b_variant, rng)
    retained = [v for v in same_protein_variants if v["carriers"]["kpsi"]["z"] is not None]
    z_values = [v["carriers"]["kpsi"]["z"] for v in retained]
    dpli_values = [v["dpli"] for v in retained]
    rho = spearman(z_values, dpli_values)
    pear = pearson(z_values, dpli_values)
    p_order, global_completed = one_sided_order_null(retained, dpli_values, rho, b_global, rng)
    p_label = one_sided_label_null(z_values, dpli_values, rho, b_label, rng)
    gap, ci_lower = top_bottom_gap(z_values, dpli_values, b_boot, rng)
    rep_pos, med_rep, _ = replicate_consistency(retained, z_values)
    decoy_rhos = decoy_correlations(retained, dpli_values)
    decoy_vectors = []
    for name in ("acluster", "ccluster", "gcluster", "purine_cluster", "single_window_u"):
        decoy_vectors.append([0.0 if v["carriers"][name]["z"] is None else v["carriers"][name]["z"] for v in retained])
    decoy_vectors.append([v["raw_total_u"] for v in retained])
    decoy_variance_nonzero = all(variance(vec) > EPS for vec in decoy_vectors)
    kpsi_rank, kpsi_top5 = kpsi_specificity(rho, decoy_rhos)
    abundance_corr = spearman(z_values, [v["total_abundance"] for v in retained])
    abundance_ratio = abs(abundance_corr) / abs(rho) if abs(rho) > EPS else (0.0 if abs(abundance_corr) <= EPS else 999999.0)
    paper_pairs = [(v["carriers"]["kpsi"]["z"], v["paper_score"]) for v in retained if v.get("paper_score") is not None]
    paper_corr = spearman([x for x, _ in paper_pairs], [y for _, y in paper_pairs]) if len(paper_pairs) >= 2 else 0.0
    zero_sd_count = sum(1 for v in same_protein_variants if v["carriers"]["kpsi"]["sd_shuffle"] <= EPS)
    nonzero_sd_frac = 1.0 - (float(zero_sd_count) / float(len(same_protein_variants))) if same_protein_variants else 0.0
    retained_fraction = float(len(retained)) / float(len(carrier_records)) if carrier_records else 0.0
    retained_cds_lengths = {v["cds_len"] for v in retained}
    metrics = {
        "spearman_rho": rho,
        "pearson_r": pear,
        "p_order": p_order,
        "p_label": p_label,
        "topbot_quintile_gap": gap,
        "topbot_ci_lower": ci_lower,
        "replicate_pos_pairs": rep_pos,
        "median_replicate_rho": med_rep,
        "decoy_rhos": decoy_rhos,
        "kpsi_decoy_rank": kpsi_rank,
        "kpsi_top5pct": kpsi_top5,
        "abundance_corr_ratio": abundance_ratio,
        "paper_score_corr": paper_corr,
        "var_dpli": variance(dpli_values),
        "var_zorder": variance(z_values),
        "frac_zero_shuffle_sd": float(zero_sd_count) / float(len(same_protein_variants)) if same_protein_variants else 1.0,
    }
    facts = {
        "mapped": len(mapped_ids),
        "missing_columns": missing_columns,
        "same_protein_frac": same_protein_frac,
        "retained_exact_same_protein": len({v["protein"] for v in retained}) <= 1 and bool(retained),
        "n_retained": len(retained),
        "retained_fraction": retained_fraction,
        "all_cds_lengths_identical": len(retained_cds_lengths) == 1,
        "usable_n1m_reps": 3,
        "usable_utp_reps": 3,
        "median_total_count": median([v["median_total_count"] for v in retained]),
        "median_fraction_count": median([v["median_fraction_count"] for v in retained]),
        "var_dpli": metrics["var_dpli"],
        "var_zorder": metrics["var_zorder"],
        "nonzero_shuffle_sd_fraction": nonzero_sd_frac,
        "b_variant_completed": all(len(v["carriers"]["kpsi"]["null_z"]) == b_variant for v in retained),
        "b_global_completed": global_completed == b_global,
        "b_label_completed": b_label > 0,
        "decoy_variance_nonzero": decoy_variance_nonzero,
    }
    preflight = evaluate_preflight(facts)
    verdict = decide_verdict(preflight, metrics, len(retained))
    public_preflight = {"passed": preflight["passed"], "failures": list(preflight["failures"])}
    return {
        "claim_id": CLAIM_ID,
        "experiment_id": EXPERIMENT_ID,
        "verdict": verdict,
        "n_mapped": len(mapped_ids),
        "n_retained": len(retained),
        "metrics": metrics,
        "details": {
            "preflight": public_preflight,
            "same_protein_frac": same_protein_frac,
            "length_classes": length_classes,
        },
    }


def make_tiny_xlsx(path):
    workbook = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?><workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships"><sheets><sheet name="fluc_library" sheetId="1" r:id="rId1"/></sheets></workbook>"""
    rels = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet1.xml"/><Relationship Id="rId2" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/sharedStrings" Target="sharedStrings.xml"/></Relationships>"""
    shared = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?><sst xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" count="4" uniqueCount="4"><si><t>Name</t></si><si><t>Sequence</t></si><si><t>fluc_x</t></si><si><t>AAATGTTTTAATTT</t></si></sst>"""
    sheet = """<?xml version="1.0" encoding="UTF-8" standalone="yes"?><worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main"><sheetData><row r="1"><c r="A1" t="s"><v>0</v></c><c r="P1" t="s"><v>1</v></c></row><row r="2"><c r="A2" t="s"><v>2</v></c><c r="N2"><v>1.5</v></c><c r="P2" t="s"><v>3</v></c></row></sheetData></worksheet>"""
    with zipfile.ZipFile(path, "w") as zf:
        zf.writestr("xl/workbook.xml", workbook)
        zf.writestr("xl/_rels/workbook.xml.rels", rels)
        zf.writestr("xl/sharedStrings.xml", shared)
        zf.writestr("xl/worksheets/sheet1.xml", sheet)


def assert_true(condition, name):
    if not condition:
        raise AssertionError(name)


def selftest():
    rng = random.Random(7)
    checks = []
    xlsx_path = "/tmp/kpsi_selftest_%s.xlsx" % os.getpid()
    make_tiny_xlsx(xlsx_path)
    try:
        with open(xlsx_path, "rb") as handle:
            recs = parse_fluc_library(handle.read())
        assert_true(recs[0]["id"] == "fluc_x" and recs[0]["paper_score"] == 1.5, "xlsx decode")
        checks.append("xlsx_cell_decode")
    finally:
        try:
            os.remove(xlsx_path)
        except OSError:
            pass
    codons, stop, error = extract_orf("CCCATGTTTTTCTAAAGG")
    assert_true(error == "" and codons == ["ATG", "TTT", "TTC"] and stop == "TAA", "orf extraction")
    assert_true(translate_codons(codons) == "MFF", "translation")
    checks.append("orf_translation")
    known = score_codons_all(["TTT", "AAT"])
    assert_true(abs(known["kpsi"] - choose2(4)) < EPS, "kpsi choose")
    checks.append("kpsi_window6")
    variable = {"id": "v", "codons": ["GCT", "GCC", "TTT", "TTC"], "protein": "AAFF"}
    compute_order_carriers([variable], 30, rng)
    assert_true(variable["carriers"]["kpsi"]["sd_shuffle"] > 0.0, "shuffle sd nonzero")
    fixed = {"id": "f", "codons": ["ATG", "TGG"], "protein": "MW"}
    compute_order_carriers([fixed], 30, rng)
    assert_true(fixed["carriers"]["kpsi"]["sd_shuffle"] == 0.0, "shuffle sd zero")
    checks.append("synonymous_shuffle_zorder")
    row = {}
    for cond in ("n1m", "utp"):
        for rep in ("a", "b", "c"):
            row["all_%s_%s" % (cond, rep)] = 100
            for frac in range(1, 6):
                row["frac%d_%s_%s" % (frac, cond, rep)] = 10 * frac
    assert_true(abs(pli_for(row, "n1m", "a") - (550.0 / 150.0)) < EPS, "pli")
    v = {"codons": ["GCT"], "protein": "A"}
    assert_true(attach_readout(v, row) and abs(v["dpli"]) < EPS, "dpli")
    checks.append("pli_dpli")
    assert_true(spearman([1, 2, 3], [1, 4, 9]) > 0.99 and pearson([1, 2, 3], [1, 2, 3]) > 0.99, "corr")
    checks.append("correlations")
    zs = [-2, -1, 0, 1, 2]
    ys = [-1, -0.5, 0, 0.5, 1]
    fake_vars = []
    for i, z in enumerate(zs):
        fv = {
            "carriers": {
                "kpsi": {"null_z": [z - 1, z + 1]},
                "acluster": {"z": -z},
                "ccluster": {"z": z * 0.1},
                "gcluster": {"z": z * 0.2},
                "purine_cluster": {"z": z * 0.3},
                "single_window_u": {"z": z * 0.4},
            },
            "raw_total_u": float(i),
            "pli": {},
        }
        for nr in ("a", "b", "c"):
            for ur in ("a", "b", "c"):
                fv["pli"][("n1m", nr)] = float(i + 2)
                fv["pli"][("utp", ur)] = float(2 - i)
        fake_vars.append(fv)
    obs = spearman(zs, ys)
    po, done = one_sided_order_null(fake_vars, ys, obs, 20, rng)
    pl = one_sided_label_null(zs, ys, obs, 20, rng)
    decoys = decoy_correlations(fake_vars, ys)
    gap, lower = top_bottom_gap(zs, ys, 20, rng)
    pos, med, _ = replicate_consistency(fake_vars, zs)
    assert_true(done == 20 and 0.0 < po <= 1.0 and 0.0 < pl <= 1.0, "nulls")
    assert_true("raw_total_u" in decoys and gap > 0.0 and lower <= gap and pos == 9 and med > 0.0, "decoy quintile replicate")
    checks.append("nulls_decoys_quintile_replicates")
    base_facts = {
        "mapped": 300,
        "missing_columns": [],
        "same_protein_frac": 1.0,
        "retained_exact_same_protein": True,
        "n_retained": 260,
        "retained_fraction": 0.90,
        "all_cds_lengths_identical": True,
        "usable_n1m_reps": 3,
        "usable_utp_reps": 3,
        "median_total_count": 600,
        "median_fraction_count": 600,
        "var_dpli": 1.0,
        "var_zorder": 1.0,
        "nonzero_shuffle_sd_fraction": 0.90,
        "b_variant_completed": True,
        "b_global_completed": True,
        "b_label_completed": True,
        "decoy_variance_nonzero": True,
    }
    assert_true(evaluate_preflight(base_facts)["passed"], "preflight pass")
    for key, bad in (
        ("mapped", 0), ("same_protein_frac", 0.5), ("n_retained", 100),
        ("retained_fraction", 0.5), ("all_cds_lengths_identical", False),
        ("median_total_count", 10), ("var_dpli", 0.0), ("var_zorder", 0.0),
        ("nonzero_shuffle_sd_fraction", 0.1), ("b_variant_completed", False),
        ("b_global_completed", False), ("b_label_completed", False),
        ("decoy_variance_nonzero", False),
    ):
        facts = dict(base_facts)
        facts[key] = bad
        assert_true(not evaluate_preflight(facts)["passed"], "preflight fail %s" % key)
    facts = dict(base_facts)
    facts["missing_columns"] = ["frac1_n1m_a"]
    assert_true(not evaluate_preflight(facts)["passed"], "preflight missing columns")
    checks.append("preflight_branches")
    certified_metrics = {
        "spearman_rho": 0.30, "pearson_r": 0.25, "p_order": 0.001, "p_label": 0.001,
        "topbot_quintile_gap": 0.20, "topbot_ci_lower": 0.05,
        "replicate_pos_pairs": 9, "median_replicate_rho": 0.20,
        "kpsi_top5pct": True, "abundance_corr_ratio": 0.2,
    }
    pre = evaluate_preflight(base_facts)
    assert_true(decide_verdict(pre, certified_metrics, 260) == "certified", "certified verdict")
    m = dict(certified_metrics)
    m["p_order"] = 0.02
    assert_true(decide_verdict(pre, m, 260) == "needs_more_data", "needs_more_data verdict")
    m = dict(certified_metrics)
    m["spearman_rho"] = -0.1
    assert_true(decide_verdict(pre, m, 260) == "refuted", "refuted verdict")
    m = dict(certified_metrics)
    m["kpsi_top5pct"] = False
    assert_true(decide_verdict(pre, m, 260) == "coincidence", "coincidence verdict")
    facts = dict(base_facts)
    facts["mapped"] = 0
    assert_true(decide_verdict(evaluate_preflight(facts), certified_metrics, 0) == "data_gate_failed", "data gate verdict")
    facts = dict(base_facts)
    facts["var_zorder"] = 0.0
    assert_true(decide_verdict(evaluate_preflight(facts), certified_metrics, 260) == "needs_derivation", "needs_derivation verdict")
    checks.append("verdicts")
    return {"ok": True, "checks": checks}


def main():
    if "--selftest" in sys.argv:
        emit_json(selftest(), 0)
    emit_json(analyze(), 0)


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        emit_json({"error": "%s: %s" % (exc.__class__.__name__, exc)}, 1)

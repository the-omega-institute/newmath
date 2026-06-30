#!/usr/bin/env python3
"""Per-species GtRNAdb tRNA edge coupling for Claim20."""
from __future__ import annotations

from collections import Counter, defaultdict
from pathlib import Path
import hashlib
import html
import json
import math
import random
import re
import sys
import urllib.error
import urllib.parse
import urllib.request

from run_claim20_neutral_trna_edge_coupling import (
    ALL_CODONS,
    BASES,
    CODON_TO_AA,
    DATA_DIR,
    GENES_PER_SPECIES,
    MIN_PAIR_COUNT,
    THIRD_GC,
    GeneRecord,
    build_dataset as build_global_proxy_dataset,
    degree_class,
    empirical_upper_p,
    gc3_preserving_mapping,
    hamming1,
    load_gene_records,
    load_selection_vectors,
    mean,
    neutral_edges,
    normalize_codon,
    permute_h_by_stratum,
    residualize,
    round_float,
    sample_sd,
    solve_linear,
    subset_dataset,
    transformed_sse,
)


EXPERIMENT_ID = "claim20_per_species_trna_edge_coupling"
CLAIM_ID = "bridge.genetic_code.neutral_trna_edge_coupling"
RANDOM_SEED = 200621
CV_SPLITS = 100
NULL_DRAWS = 100
STRICT_FE_EPS = 1e-8
STRICT_RESIDUALIZE_PASSES = 10
TRNA_CACHE_DIR = Path("/tmp/c20-trna")
GTRNADB_SPECIES_INDEX_URL = "https://gtrnadb.ucsc.edu/js/species.json"
GTRNADB_DOMAIN_PATH = {"e": "eukaryota", "a": "archaea", "b": "bacteria"}
USER_AGENT = "Claim20-per-species-tRNA/1.0"
MAX_BYTES = 100 * 1024 * 1024

RNA_COMPLEMENT = {"A": "U", "U": "A", "C": "G", "G": "C"}
AA_ONE_TO_THREE = {
    "A": "Ala",
    "R": "Arg",
    "N": "Asn",
    "D": "Asp",
    "C": "Cys",
    "Q": "Gln",
    "E": "Glu",
    "G": "Gly",
    "H": "His",
    "I": "Ile",
    "L": "Leu",
    "K": "Lys",
    "M": "Met",
    "F": "Phe",
    "P": "Pro",
    "S": "Ser",
    "T": "Thr",
    "W": "Trp",
    "Y": "Tyr",
    "V": "Val",
}
AA_ALIASES = {"fMet": "Met", "iMet": "Met", "Ile2": "Ile"}
WOBBLE_S = {
    ("G", "U"): 0.41,
    ("U", "G"): 0.68,
    ("I", "C"): 0.28,
    ("I", "A"): 0.9999,
    ("I", "U"): 0.0,
    ("L", "A"): 0.89,
}
HEADER_RE = re.compile(r"tRNA-([A-Za-z0-9]+)-([ACGTU]{3})")
FALLBACK_RE = re.compile(r"\)\s+([A-Za-z0-9]+)\s+\(([ACGTU]{3})\)")


class FetchFailure(Exception):
    pass


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def fetch_bytes(url: str) -> bytes:
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(request, timeout=60) as response:
            status = int(getattr(response, "status", 200))
            payload = response.read(MAX_BYTES + 1)
            if status != 200:
                raise FetchFailure(f"HTTP status {status}")
            if len(payload) > MAX_BYTES:
                raise FetchFailure("response exceeds 100 MB")
            if not payload:
                raise FetchFailure("empty HTTP payload")
            return payload
    except urllib.error.HTTPError as exc:
        raise FetchFailure(f"HTTP status {exc.code}") from exc
    except urllib.error.URLError as exc:
        raise FetchFailure(f"URL error: {exc.reason}") from exc


def slugify(label: str) -> str:
    value = label.lower()
    value = re.sub(r"\([^)]*\)", " ", value)
    value = re.sub(r"[^a-z0-9]+", "_", value)
    value = re.sub(r"_+", "_", value).strip("_")
    return value[:90] or "organism"


def normalized_label(label: str) -> str:
    value = html.unescape(str(label)).lower().replace("_", " ")
    value = re.sub(r"\([^)]*\)", " ", value)
    value = re.sub(
        r"\b(str\.?|strain|substr\.?|subsp\.?|serovar|biovar|pv\.?|var\.?|f\.?|sp\.)\b",
        " ",
        value,
    )
    value = re.sub(r"[^a-z0-9]+", " ", value)
    return re.sub(r"\s+", " ", value).strip()


def binomial(label: str) -> str:
    parts = normalized_label(label).split()
    return " ".join(parts[:2]) if len(parts) >= 2 else normalized_label(label)


def label_tokens(label: str) -> set[str]:
    return set(normalized_label(label).split())


def gtrnadb_fasta_url(entry: dict[str, str]) -> str:
    domain = GTRNADB_DOMAIN_PATH[entry["d"]]
    genome_id = urllib.parse.quote(entry["i"], safe="")
    prefix = urllib.parse.quote(entry["f"], safe="")
    return f"https://gtrnadb.ucsc.edu/genomes/{domain}/{genome_id}/{prefix}-tRNAs.fa"


def load_gtrnadb_species_index() -> list[dict[str, str]]:
    TRNA_CACHE_DIR.mkdir(parents=True, exist_ok=True)
    index_path = TRNA_CACHE_DIR / "species_index.json"
    if index_path.exists():
        payload = index_path.read_bytes()
    else:
        payload = fetch_bytes(GTRNADB_SPECIES_INDEX_URL)
        index_path.write_bytes(payload)
    records = json.loads(payload.decode("utf-8"))
    if not isinstance(records, list) or not records:
        raise FetchFailure("GtRNAdb species index is empty or malformed")
    species = []
    for record in records:
        if not isinstance(record, dict):
            continue
        if not all(key in record for key in ("d", "i", "n", "f")):
            continue
        if str(record["d"]) not in GTRNADB_DOMAIN_PATH:
            continue
        species.append({"d": str(record["d"]), "i": str(record["i"]), "n": str(record["n"]), "f": str(record["f"])})
    if not species:
        raise FetchFailure("GtRNAdb species index yielded no usable records")
    return species


def load_species_metadata() -> dict[str, dict[str, object]]:
    result: dict[str, dict[str, object]] = {}
    for path in sorted(DATA_DIR.glob("cds_codon_counts_*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        organism = str(data.get("organism") or path.stem.replace("cds_codon_counts_", ""))
        labels = []
        for key in ("organism_label", "assembly_organism_name", "organism"):
            value = data.get(key)
            if value:
                labels.append(str(value))
        result[organism] = {
            "organism": organism,
            "labels": labels or [organism],
            "domain": str(data.get("domain") or ""),
            "path": str(path),
        }
    return result


def candidate_matches(meta: dict[str, object], index: list[dict[str, str]]) -> list[dict[str, object]]:
    labels = [str(label) for label in meta["labels"]]
    normalized_targets = {normalized_label(label) for label in labels if normalized_label(label)}
    binomial_targets = {binomial(label) for label in labels if binomial(label)}
    target_tokens = set()
    for label in labels:
        target_tokens.update(label_tokens(label))
    wanted_domain = str(meta.get("domain") or "").lower()
    scored = []
    for entry in index:
        entry_norm = normalized_label(entry["n"])
        entry_binomial = binomial(entry["n"])
        entry_tokens = label_tokens(entry["n"])
        score = 0.0
        kind = ""
        if entry_norm in normalized_targets:
            score = 100.0
            kind = "exact_normalized_label"
        elif entry_binomial in binomial_targets and entry_binomial:
            shared = len(target_tokens & entry_tokens)
            score = 55.0 + shared
            kind = "binomial_with_token_overlap"
        else:
            shared = len(target_tokens & entry_tokens)
            union = len(target_tokens | entry_tokens) or 1
            if shared >= 3:
                score = 20.0 + shared / union
                kind = "token_overlap"
        if score <= 0.0:
            continue
        domain_name = GTRNADB_DOMAIN_PATH[entry["d"]]
        if wanted_domain and wanted_domain in domain_name:
            score += 2.0
        scored.append(
            {
                "score": score,
                "match_kind": kind,
                "gtrnadb_label": entry["n"],
                "gtrnadb_domain_code": entry["d"],
                "gtrnadb_domain": domain_name,
                "gtrnadb_genome_id": entry["i"],
                "gtrnadb_prefix": entry["f"],
                "gtrnadb_fasta_url": gtrnadb_fasta_url(entry),
            }
        )
    scored.sort(key=lambda item: (-float(item["score"]), str(item["gtrnadb_label"]), str(item["gtrnadb_genome_id"])))
    return scored[:8]


def dna_to_rna(text: str) -> str:
    return text.upper().replace("T", "U")


def normalize_aa(label: str) -> str:
    return AA_ALIASES.get(label, label)


def parse_gtrnadb_fasta(raw_payload_text: str) -> list[dict[str, str]]:
    records = []
    for line in raw_payload_text.splitlines():
        if not line.startswith(">"):
            continue
        match = HEADER_RE.search(line) or FALLBACK_RE.search(line)
        if match is None:
            records.append({"header": line, "aa_label": "", "aa": "", "anticodon": "", "matched": "false"})
            continue
        aa_label = match.group(1)
        records.append(
            {
                "header": line,
                "aa_label": aa_label,
                "aa": normalize_aa(aa_label),
                "anticodon": dna_to_rna(match.group(2)),
                "matched": "true",
            }
        )
    return records


def first_two_positions_match(codon: str, anticodon: str) -> bool:
    return RNA_COMPLEMENT.get(anticodon[2]) == codon[0] and RNA_COMPLEMENT.get(anticodon[1]) == codon[1]


def effective_wobble_base(aa_label: str, anticodon: str, organism: str) -> str:
    wobble = anticodon[0]
    if aa_label == "Ile2" and anticodon == "CAU" and organism == "escherichia_coli":
        return "L"
    if wobble == "A":
        return "I"
    return wobble


def wobble_penalty(wobble: str, codon_third: str) -> float | None:
    if RNA_COMPLEMENT.get(wobble) == codon_third:
        return 0.0
    return WOBBLE_S.get((wobble, codon_third))


def aa_anticodon_copy_counts(records: list[dict[str, str]]) -> dict[tuple[str, str, str], int]:
    counts: Counter[tuple[str, str, str]] = Counter()
    for record in records:
        aa = record.get("aa", "")
        aa_label = record.get("aa_label", "")
        anticodon = record.get("anticodon", "")
        if aa and aa_label and anticodon:
            counts[(aa, aa_label, anticodon)] += 1
    return dict(counts)


def codon_availability(organism: str, records: list[dict[str, str]], families: dict[str, list[str]]) -> dict[str, float]:
    copy_counts = aa_anticodon_copy_counts(records)
    raw_w: dict[str, float] = {}
    for codon in [codon for codon in ALL_CODONS if CODON_TO_AA[codon] != "*"]:
        aa = AA_ONE_TO_THREE[CODON_TO_AA[codon]]
        total = 0.0
        for (record_aa, aa_label, anticodon), copy in copy_counts.items():
            if record_aa != aa or len(anticodon) != 3:
                continue
            if not first_two_positions_match(codon, anticodon):
                continue
            wobble = effective_wobble_base(aa_label, anticodon, organism)
            penalty = wobble_penalty(wobble, codon[2])
            if penalty is None:
                continue
            total += max(0.0, (1.0 - penalty) * copy)
        raw_w[codon] = total
    nonzero = [value for value in raw_w.values() if value > 0.0]
    if not nonzero:
        raise ValueError("no nonzero wobble-corrected codon availability")
    fallback = math.exp(sum(math.log(value) for value in nonzero) / len(nonzero))
    filled = {codon: (value if value > 0.0 else fallback) for codon, value in raw_w.items()}
    availability: dict[str, float] = {}
    for aa, codons in families.items():
        family_mean = mean([filled[codon] for codon in codons])
        if family_mean <= 0.0:
            raise ValueError(f"zero family availability for {aa}")
        for codon in codons:
            availability[codon] = filled[codon] / family_mean
    return availability


def fetch_trna_records(meta: dict[str, object], match: dict[str, object]) -> list[dict[str, str]]:
    url = str(match["gtrnadb_fasta_url"])
    cache_key = hashlib.sha256(url.encode("utf-8")).hexdigest()[:16]
    path = TRNA_CACHE_DIR / f"{slugify(str(meta['organism']))}_{cache_key}.fa"
    if path.exists():
        text = path.read_text(encoding="utf-8")
    else:
        text = fetch_bytes(url).decode("utf-8", "replace")
        path.write_text(text, encoding="utf-8")
    records = parse_gtrnadb_fasta(text)
    if not any(record.get("anticodon") for record in records):
        raise ValueError("FASTA contains no parseable anticodon headers")
    return records


def fetch_species_availability(
    species_names: list[str],
    metadata: dict[str, dict[str, object]],
    families: dict[str, list[str]],
    checks: list[str],
) -> tuple[dict[str, dict[str, float]], dict[str, dict[str, object]], list[str]]:
    index = load_gtrnadb_species_index()
    availability_by_species: dict[str, dict[str, float]] = {}
    match_by_species: dict[str, dict[str, object]] = {}
    failures: list[str] = []
    for species in species_names:
        meta = metadata.get(species)
        if meta is None:
            failures.append(f"{species}:missing_cds_metadata")
            continue
        candidates = candidate_matches(meta, index)
        if not candidates:
            failures.append(f"{species}:no_gtrnadb_candidate")
            continue
        last_error = ""
        for candidate in candidates:
            try:
                records = fetch_trna_records(meta, candidate)
                availability = codon_availability(species, records, families)
            except Exception as exc:
                last_error = str(exc)
                continue
            availability_by_species[species] = availability
            match_by_species[species] = candidate
            break
        if species not in availability_by_species:
            failures.append(f"{species}:fetch_or_tai_failed:{last_error}")
    checks.append(f"gtrnadb_species_index_records={len(index)}")
    checks.append(f"gtrnadb_trna_success={len(availability_by_species)}")
    checks.append(f"gtrnadb_trna_failures={len(failures)}")
    if failures:
        checks.append(f"gtrnadb_trna_failure_sample={failures[:8]}")
    return availability_by_species, match_by_species, failures


def decorate_edges(base_edges: list[dict[str, object]], vectors: dict[str, dict[str, float]], mapping: dict[str, str] | None = None) -> list[dict[str, object]]:
    mapping = mapping or {codon: codon for codon in ALL_CODONS}
    raw_h: dict[int, float] = {}
    provisional: list[dict[str, object]] = []
    for base in base_edges:
        edge_id = int(base["edge_id"])
        c1 = mapping[str(base["c1"])]
        c2 = mapping[str(base["c2"])]
        raw_h[edge_id] = abs(vectors[c1]["d_perp"] - vectors[c2]["d_perp"])
        provisional.append(
            {
                "edge_id": edge_id,
                "c1": c1,
                "c2": c2,
                "aa": str(base["aa"]),
                "edge_class": str(base["edge_class"]),
                "delta_gc3": float((c1[2] in THIRD_GC) - (c2[2] in THIRD_GC)),
                "delta_f3": vectors[c1]["f3"] - vectors[c2]["f3"],
            }
        )
    h_center = mean(list(raw_h.values()))
    h_scale = sample_sd(list(raw_h.values()))
    for row in provisional:
        edge_id = int(row["edge_id"])
        row["H"] = 0.0 if h_scale <= 0.0 else (raw_h[edge_id] - h_center) / h_scale
    return provisional


def remap_records(records: list[GeneRecord], species_names: list[str], keep_species: set[str]) -> tuple[list[GeneRecord], list[str], dict[int, int]]:
    new_species_names = [species for species in species_names if species in keep_species]
    old_to_new = {old_id: new_species_names.index(species) for old_id, species in enumerate(species_names) if species in keep_species}
    remapped = []
    for record in records:
        if record.species not in keep_species:
            continue
        remapped.append(
            GeneRecord(
                species=record.species,
                species_id=old_to_new[record.species_id],
                gc3=record.gc3,
                log_length=record.log_length,
                counts=record.counts,
                logp_by_aa=record.logp_by_aa,
            )
        )
    return remapped, new_species_names, old_to_new


def build_dataset(
    records: list[GeneRecord],
    edges: list[dict[str, object]],
    aa_to_id: dict[str, int],
    availability_by_species_id: dict[int, dict[str, float]],
) -> dict[str, object]:
    y: list[float] = []
    t_col: list[float] = []
    th_col: list[float] = []
    gc3_col: list[float] = []
    dgc3_col: list[float] = []
    df3_col: list[float] = []
    logl_col: list[float] = []
    species_group: list[int] = []
    aa_group: list[int] = []
    edge_group: list[int] = []
    retained_by_edge: Counter[int] = Counter()
    for record in records:
        availability = availability_by_species_id[record.species_id]
        for edge in edges:
            c1 = str(edge["c1"])
            c2 = str(edge["c2"])
            aa = str(edge["aa"])
            if record.counts[c1] + record.counts[c2] < MIN_PAIR_COUNT:
                continue
            logp = record.logp_by_aa[aa]
            t_value = math.log(availability[c1] + 0.5) - math.log(availability[c2] + 0.5)
            h_value = float(edge["H"])
            y.append(logp[c1] - logp[c2])
            t_col.append(t_value)
            th_col.append(t_value * h_value)
            gc3_col.append(record.gc3)
            dgc3_col.append(float(edge["delta_gc3"]))
            df3_col.append(float(edge["delta_f3"]))
            logl_col.append(record.log_length)
            species_group.append(record.species_id)
            aa_group.append(aa_to_id[aa])
            edge_id = int(edge["edge_id"])
            edge_group.append(edge_id)
            retained_by_edge[edge_id] += 1
    return {
        "y": y,
        "cols": {
            "T": t_col,
            "TH": th_col,
            "GC3": gc3_col,
            "delta_GC3": dgc3_col,
            "delta_f3": df3_col,
            "logL": logl_col,
        },
        "groups": {"species": species_group, "aa": aa_group, "edge": edge_group},
        "retained_by_edge": retained_by_edge,
    }


def dataset_with_permuted_h(data: dict[str, object], permuted_h: dict[int, float]) -> dict[str, object]:
    edge_group = data["groups"]["edge"]
    t_col = data["cols"]["T"]
    return {
        "y": data["y"],
        "cols": {
            "T": t_col,
            "TH": [t_col[i] * permuted_h[edge_group[i]] for i in range(len(t_col))],
            "GC3": data["cols"]["GC3"],
            "delta_GC3": data["cols"]["delta_GC3"],
            "delta_f3": data["cols"]["delta_f3"],
            "logL": data["cols"]["logL"],
        },
        "groups": data["groups"],
        "retained_by_edge": data.get("retained_by_edge", Counter()),
    }


def column_norm_after_absorption(data: dict[str, object], column_name: str, fixed_effects: tuple[str, ...]) -> float:
    _y, cols = residualize(
        [0.0] * len(data["y"]),
        [data["cols"][column_name]],
        [data["groups"][name] for name in fixed_effects],
        passes=2,
    )
    return math.sqrt(sum(value * value for value in cols[0]))


def fit_ols_absorbed(data: dict[str, object], column_names: list[str], fixed_effects: tuple[str, ...]) -> dict[str, object] | None:
    if len(data["y"]) <= len(column_names) + 2:
        return None
    columns = [data["cols"][name] for name in column_names]
    groups = [data["groups"][name] for name in fixed_effects]
    y_res, x_res = residualize(data["y"], columns, groups, passes=STRICT_RESIDUALIZE_PASSES)
    norms = [math.sqrt(sum(value * value for value in column)) for column in x_res]
    active = [index for index, norm in enumerate(norms) if norm > STRICT_FE_EPS]
    if not active:
        return None
    p = len(active)
    xtx = [[0.0 for _ in range(p)] for _ in range(p)]
    xty = [0.0 for _ in range(p)]
    sst = sum(value * value for value in y_res)
    for i, y_value in enumerate(y_res):
        row = [x_res[index][i] for index in active]
        for j in range(p):
            xty[j] += row[j] * y_value
            for k in range(j, p):
                xtx[j][k] += row[j] * row[k]
    for j in range(p):
        for k in range(j):
            xtx[j][k] = xtx[k][j]
    active_beta = solve_linear(xtx, xty)
    if active_beta is None:
        return None
    beta_values = [0.0] * len(column_names)
    for index, value in zip(active, active_beta):
        beta_values[index] = value
    beta = dict(zip(column_names, beta_values))
    sse = 0.0
    for i, y_value in enumerate(y_res):
        pred = sum(beta[column_names[j]] * x_res[j][i] for j in range(len(column_names)))
        resid = y_value - pred
        sse += resid * resid
    absorbed = [column_names[index] for index, norm in enumerate(norms) if norm <= STRICT_FE_EPS]
    return {"beta": beta, "sse": sse, "sst": sst, "n": len(y_res), "absorbed": absorbed, "norms": dict(zip(column_names, norms))}


def fit_models(data: dict[str, object], fixed_effects: tuple[str, ...] = ("species", "aa", "edge")) -> dict[str, object] | None:
    baseline_cols = ["T", "GC3", "delta_GC3", "delta_f3", "logL"]
    full_cols = ["T", "TH", "GC3", "delta_GC3", "delta_f3", "logL"]
    baseline = fit_ols_absorbed(data, baseline_cols, fixed_effects)
    full = fit_ols_absorbed(data, full_cols, fixed_effects)
    if baseline is None or full is None:
        return None
    if float(full["norms"].get("TH", 0.0)) <= STRICT_FE_EPS:
        return None
    n = int(full["n"])
    sse_base = max(float(baseline["sse"]), 1e-300)
    sse_full = max(float(full["sse"]), 1e-300)
    d_ll = 0.5 * n * math.log(sse_base / sse_full)
    return {"baseline": baseline, "full": full, "dLL": d_ll}


def transformed_sse_absorbed(
    data: dict[str, object],
    column_names: list[str],
    beta: dict[str, float],
    fixed_effects: tuple[str, ...],
) -> tuple[float, float, int]:
    columns = [data["cols"][name] for name in column_names]
    groups = [data["groups"][name] for name in fixed_effects]
    y_res, x_res = residualize(data["y"], columns, groups, passes=STRICT_RESIDUALIZE_PASSES)
    sse = 0.0
    sst = sum(value * value for value in y_res)
    for i, y_value in enumerate(y_res):
        pred = sum(beta[column_names[j]] * x_res[j][i] for j in range(len(column_names)))
        resid = y_value - pred
        sse += resid * resid
    return sse, sst, len(y_res)


def cv_lift(data: dict[str, object], species_count: int, rng: random.Random) -> tuple[list[float], list[str]]:
    species = list(range(species_count))
    lifts: list[float] = []
    checks: list[str] = []
    baseline_cols = ["T", "GC3", "delta_GC3", "delta_f3", "logL"]
    full_cols = ["T", "TH", "GC3", "delta_GC3", "delta_f3", "logL"]
    for split in range(CV_SPLITS):
        shuffled = species[:]
        rng.shuffle(shuffled)
        holdout_count = max(1, round(0.2 * len(shuffled)))
        test_species = set(shuffled[:holdout_count])
        train_species = set(shuffled[holdout_count:])
        train = subset_dataset(data, train_species)
        test = subset_dataset(data, test_species)
        baseline = fit_ols_absorbed(train, baseline_cols, ("species", "aa", "edge"))
        full = fit_ols_absorbed(train, full_cols, ("species", "aa", "edge"))
        if baseline is None or full is None or not test["y"]:
            checks.append(f"cv_split_{split}:fit_or_test_empty")
            continue
        sse_base, _sst_base, n_test = transformed_sse_absorbed(test, baseline_cols, baseline["beta"], ("species", "aa", "edge"))
        sse_full, _sst_full, _n = transformed_sse_absorbed(test, full_cols, full["beta"], ("species", "aa", "edge"))
        lifts.append(0.5 * n_test * math.log(max(sse_base, 1e-300) / max(sse_full, 1e-300)))
    return lifts, checks


def median(values: list[float]) -> float:
    sorted_values = sorted(values)
    mid = len(sorted_values) // 2
    if len(sorted_values) % 2:
        return sorted_values[mid]
    return 0.5 * (sorted_values[mid - 1] + sorted_values[mid])


def species_clade_key(label: str) -> str:
    parts = normalized_label(label).split()
    return parts[0] if parts else label


def choose_null3_mode(species_names: list[str], metadata: dict[str, dict[str, object]]) -> tuple[str, dict[str, list[int]]]:
    blocks: dict[str, list[int]] = defaultdict(list)
    for index, species in enumerate(species_names):
        labels = metadata.get(species, {}).get("labels", [species])
        label = str(labels[0]) if labels else species
        blocks[species_clade_key(label)].append(index)
    movable = sum(len(indices) for indices in blocks.values() if len(indices) > 1)
    if movable >= max(10, len(species_names) // 2):
        return "genus_block_permutation", dict(blocks)
    return "ordinary_permutation_optimistic", {"all": list(range(len(species_names)))}


def permuted_availability_by_species_id(
    availability_by_species_id: dict[int, dict[str, float]],
    blocks: dict[str, list[int]],
    rng: random.Random,
) -> dict[int, dict[str, float]]:
    result = dict(availability_by_species_id)
    for ids in blocks.values():
        if len(ids) < 2:
            continue
        shuffled = ids[:]
        rng.shuffle(shuffled)
        for target, source in zip(ids, shuffled):
            result[target] = availability_by_species_id[source]
    return result


def main() -> None:
    rng = random.Random(RANDOM_SEED)
    checks: list[str] = []
    try:
        vectors = load_selection_vectors()
    except Exception as exc:
        emit("needs_derivation", n_species_trna=0, strict_edge_fe_TH_norm=None, beta_bridge=None, beta_T=None, checks=[f"selection_vectors_error:{exc}"], note="selection vector load failed")

    families: dict[str, list[str]] = defaultdict(list)
    for codon in ALL_CODONS:
        aa = CODON_TO_AA[codon]
        if aa != "*":
            families[aa].append(codon)
    families = {aa: codons for aa, codons in sorted(families.items()) if len(codons) > 1}
    aa_to_id = {aa: index for index, aa in enumerate(sorted(families))}

    base_edges = neutral_edges(ALL_CODONS)
    edges = decorate_edges(base_edges, vectors)
    degree_hist = Counter()
    for codon in ALL_CODONS:
        degree_hist[sum(1 for other in ALL_CODONS if other != codon and CODON_TO_AA[other] == CODON_TO_AA[codon] and hamming1(codon, other))] += 1
    checks.append(f"standard_code_neutral_adjacency_codons_28_22_8_6={[degree_hist[3], degree_hist[1], degree_hist[2], degree_hist[0] + degree_hist[4]]}")
    checks.append(f"sense_neutral_edges={len(edges)}")
    checks.append(f"edge_class_counts={dict(sorted(Counter(str(edge['edge_class']) for edge in edges).items()))}")

    records, species_names, data_checks = load_gene_records(families, rng)
    checks.extend(data_checks)
    if len(species_names) < 10 or not records:
        emit(
            "needs_derivation",
            n_species_trna=0,
            strict_edge_fe_TH_norm=None,
            beta_bridge=None,
            beta_T=None,
            cv_median_dLL=None,
            cv_frac_positive=None,
            null1_p=None,
            null2_p=None,
            null3_p=None,
            checks=checks,
            note="needs-external: insufficient real codon-count species before GtRNAdb fetch",
        )

    metadata = load_species_metadata()
    try:
        availability_by_species, match_by_species, _failures = fetch_species_availability(species_names, metadata, families, checks)
    except Exception as exc:
        emit(
            "needs_derivation",
            n_species_trna=0,
            strict_edge_fe_TH_norm=None,
            beta_bridge=None,
            beta_T=None,
            cv_median_dLL=None,
            cv_frac_positive=None,
            null1_p=None,
            null2_p=None,
            null3_p=None,
            checks=checks + [f"gtrnadb_index_or_fetch_error:{exc}"],
            note="needs-external: GtRNAdb fetch insufficient",
        )

    if len(availability_by_species) < 10:
        emit(
            "needs_derivation",
            n_species_trna=len(availability_by_species),
            strict_edge_fe_TH_norm=None,
            beta_bridge=None,
            beta_T=None,
            cv_median_dLL=None,
            cv_frac_positive=None,
            null1_p=None,
            null2_p=None,
            null3_p=None,
            checks=checks,
            note="needs-external: GtRNAdb fetch insufficient",
        )
    if len(availability_by_species) < 15:
        checks.append("gtrnadb_trna_success_below_15_continuing_low_power")

    records, species_names, _old_to_new = remap_records(records, species_names, set(availability_by_species))
    availability_by_species_id = {index: availability_by_species[species] for index, species in enumerate(species_names)}
    checks.append(f"n_species_after_trna_filter={len(species_names)}")
    checks.append(f"sampled_gene_records_after_trna_filter={len(records)}")
    sample_matches = [
        {
            "species": species,
            "gtrnadb_label": str(match_by_species[species]["gtrnadb_label"]),
            "match_kind": str(match_by_species[species]["match_kind"]),
        }
        for species in species_names[:5]
    ]
    checks.append(f"gtrnadb_match_sample={sample_matches}")

    data = build_dataset(records, edges, aa_to_id, availability_by_species_id)
    checks.append(f"gene_edge_observations={len(data['y'])}")
    checks.append(f"edges_with_retained_observations={len(data['retained_by_edge'])}")
    if len(data["y"]) < 1000 or len(data["retained_by_edge"]) < 40:
        emit(
            "needs_derivation",
            n_species_trna=len(species_names),
            strict_edge_fe_TH_norm=None,
            beta_bridge=None,
            beta_T=None,
            cv_median_dLL=None,
            cv_frac_positive=None,
            null1_p=None,
            null2_p=None,
            null3_p=None,
            checks=checks,
            note="too few gene-edge observations after applying per-species tRNA availability",
        )

    strict_edge_fe_t_norm = column_norm_after_absorption(data, "T", ("edge",))
    strict_edge_fe_th_norm = column_norm_after_absorption(data, "TH", ("edge",))
    strict_full_th_norm = column_norm_after_absorption(data, "TH", ("species", "aa", "edge"))
    checks.append(f"strict_edge_fe_T_norm={strict_edge_fe_t_norm:.6g}")
    checks.append(f"strict_edge_fe_TH_norm={strict_edge_fe_th_norm:.6g}")
    checks.append(f"strict_species_aa_edge_fe_TH_norm={strict_full_th_norm:.6g}")
    if strict_edge_fe_th_norm <= STRICT_FE_EPS or strict_full_th_norm <= STRICT_FE_EPS:
        emit(
            "needs_derivation",
            n_species_trna=len(species_names),
            strict_edge_fe_TH_norm=round_float(strict_edge_fe_th_norm),
            beta_bridge=None,
            beta_T=None,
            cv_median_dLL=None,
            cv_frac_positive=None,
            null1_p=None,
            null2_p=None,
            null3_p=None,
            checks=checks,
            note="per-species T did not survive strict edge fixed-effect absorption",
        )
    checks.append("strict_edge_fe_identifiability=identified_for_per_species_T")

    fitted = fit_models(data)
    if fitted is None:
        emit(
            "needs_derivation",
            n_species_trna=len(species_names),
            strict_edge_fe_TH_norm=round_float(strict_edge_fe_th_norm),
            beta_bridge=None,
            beta_T=None,
            cv_median_dLL=None,
            cv_frac_positive=None,
            null1_p=None,
            null2_p=None,
            null3_p=None,
            checks=checks,
            note="strict fixed-effect OLS normal equations were singular",
        )
    full_beta = fitted["full"]["beta"]
    beta_bridge = float(full_beta["TH"])
    beta_t = float(full_beta["T"])
    checks.append(f"strict_model_train_dLL={float(fitted['dLL']):.6g}")
    checks.append(f"absorbed_covariates_full={fitted['full']['absorbed']}")

    cv_values, cv_checks = cv_lift(data, len(species_names), rng)
    checks.extend(cv_checks[:10])
    checks.append(f"cv_splits_used={len(cv_values)}")
    if not cv_values:
        emit(
            "needs_derivation",
            n_species_trna=len(species_names),
            strict_edge_fe_TH_norm=round_float(strict_edge_fe_th_norm),
            beta_bridge=round_float(beta_bridge),
            beta_T=round_float(beta_t),
            cv_median_dLL=None,
            cv_frac_positive=None,
            null1_p=None,
            null2_p=None,
            null3_p=None,
            checks=checks,
            note="species-heldout CV produced no usable folds",
        )
    cv_median = median(cv_values)
    cv_frac_positive = sum(1 for value in cv_values if value > 0.0) / len(cv_values)

    null1_values: list[float] = []
    null1_failures = 0
    for _draw in range(NULL_DRAWS):
        mapping = gc3_preserving_mapping(rng)
        perm_edges = decorate_edges(base_edges, vectors, mapping)
        perm_data = build_dataset(records, perm_edges, aa_to_id, availability_by_species_id)
        fit = fit_models(perm_data)
        if fit is None:
            null1_failures += 1
            continue
        null1_values.append(float(fit["full"]["beta"]["TH"]))
    checks.append(f"null1_draws_used={len(null1_values)}")
    if null1_failures:
        checks.append(f"null1_fit_failures={null1_failures}")

    null2_values: list[float] = []
    null2_failures = 0
    for _draw in range(NULL_DRAWS):
        permuted_h = permute_h_by_stratum(edges, rng)
        perm_data = dataset_with_permuted_h(data, permuted_h)
        fit = fit_models(perm_data)
        if fit is None:
            null2_failures += 1
            continue
        null2_values.append(float(fit["full"]["beta"]["TH"]))
    checks.append(f"null2_draws_used={len(null2_values)}")
    if null2_failures:
        checks.append(f"null2_fit_failures={null2_failures}")

    null3_mode, null3_blocks = choose_null3_mode(species_names, metadata)
    null3_values: list[float] = []
    null3_failures = 0
    for _draw in range(NULL_DRAWS):
        perm_availability = permuted_availability_by_species_id(availability_by_species_id, null3_blocks, rng)
        perm_data = build_dataset(records, edges, aa_to_id, perm_availability)
        fit = fit_models(perm_data)
        if fit is None:
            null3_failures += 1
            continue
        null3_values.append(float(fit["full"]["beta"]["TH"]))
    checks.append(f"null3_draws_used={len(null3_values)}")
    checks.append(f"null3_species_tRNA_decoupling={null3_mode}")
    if null3_failures:
        checks.append(f"null3_fit_failures={null3_failures}")

    if len(null1_values) < 50 or len(null2_values) < 50 or len(null3_values) < 50:
        emit(
            "needs_derivation",
            n_species_trna=len(species_names),
            strict_edge_fe_TH_norm=round_float(strict_edge_fe_th_norm),
            beta_bridge=round_float(beta_bridge),
            beta_T=round_float(beta_t),
            cv_median_dLL=round_float(cv_median),
            cv_frac_positive=round_float(cv_frac_positive),
            null1_p=None,
            null2_p=None,
            null3_p=None,
            checks=checks,
            note="permutation nulls did not yield enough fitted draws",
        )

    null1_p = empirical_upper_p(beta_bridge, null1_values)
    null2_p = empirical_upper_p(beta_bridge, null2_values)
    null3_p = empirical_upper_p(beta_bridge, null3_values)
    cv_pass = cv_median > 0.0 and cv_frac_positive >= 0.70
    null1_pass = null1_p < 0.01
    null2_pass = null2_p < 0.01
    null3_pass = null3_p < 0.01
    checks.append(f"cv_gate_median_gt_0_frac_ge_0p70={cv_pass}")
    checks.append(f"null_gates_p_lt_0p01={[null1_pass, null2_pass, null3_pass]}")

    if beta_bridge > 0.0 and cv_pass and null1_pass and null2_pass and null3_pass:
        status = "certified"
        note = "per-species GtRNAdb tRNA availability identifies and validates Window6 edge-score modulation of tRNA-usage edge coupling"
    elif beta_bridge <= 0.0:
        status = "refuted"
        note = "strict per-species tRNA interaction is non-positive"
    else:
        status = "coincidence"
        note = "strict per-species tRNA interaction is estimable but does not pass the pre-registered CV/null gates"

    emit(
        status,
        n_species_trna=len(species_names),
        strict_edge_fe_TH_norm=round_float(strict_edge_fe_th_norm),
        beta_bridge=round_float(beta_bridge),
        beta_T=round_float(beta_t),
        cv_median_dLL=round_float(cv_median),
        cv_frac_positive=round_float(cv_frac_positive),
        null1_p=round_float(null1_p),
        null2_p=round_float(null2_p),
        null3_p=round_float(null3_p),
        n_edges=len(edges),
        n_gene_edge_observations=len(data["y"]),
        null_draws=NULL_DRAWS,
        checks=checks,
        note=note,
    )


if __name__ == "__main__":
    main()

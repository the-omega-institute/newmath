#!/usr/bin/env python3
"""ASD-shadow exclusion killgate runner with initiation and hygiene controls."""
from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import json
import math
import os
from pathlib import Path
import random
import re
import statistics
import sys
import time
from typing import Any

import _asd_fetch_probe as fetch_probe
import run_asd_shadow_exclusion as v1


EXPERIMENT_ID = "asd_shadow_exclusion_v2"
CLAIM_ID = "bridge.genetic_code.asd_shadow_exclusion"

TARGET_BACTERIA = int(os.environ.get("ASD_TARGET_BACTERIA", "64"))
TARGET_ARCHAEA = int(os.environ.get("ASD_TARGET_ARCHAEA", "8"))
MAX_FETCH_ATTEMPTS = int(os.environ.get("ASD_MAX_FETCH_ATTEMPTS", str(TARGET_BACTERIA + TARGET_ARCHAEA + 24)))
FETCH_DEADLINE_SECONDS = float(os.environ.get("ASD_FETCH_DEADLINE_SECONDS", "120"))
ANALYSIS_ORGANISM_LIMIT = int(os.environ.get("ASD_ANALYSIS_ORGANISM_LIMIT", "16"))
R_NULL = int(os.environ.get("ASD_NULL_R", "80"))
N_DECOYS = int(os.environ.get("ASD_N_DECOYS", "24"))
N_BOOTSTRAP = int(os.environ.get("ASD_BOOTSTRAP", "120"))
DEFAULT_MAX_GENES = "8" if "ASD_ANALYSIS_ORGANISM_LIMIT" in os.environ and "ASD_MAX_GENES_PER_ORGANISM" not in os.environ else "96"
MAX_GENES_PER_ORGANISM = int(os.environ.get("ASD_MAX_GENES_PER_ORGANISM", DEFAULT_MAX_GENES))
DEFAULT_PROFILE_LIMIT = "180" if "ASD_ANALYSIS_ORGANISM_LIMIT" in os.environ and "ASD_PROFILE_KMER_LIMIT" not in os.environ else "900"
PROFILE_KMER_LIMIT = int(os.environ.get("ASD_PROFILE_KMER_LIMIT", DEFAULT_PROFILE_LIMIT))
NULL_PLACE_R = int(os.environ.get("ASD_NULL_PLACE_R", str(max(8, min(R_NULL, 48)))))
MIN_GATE_STARTS = int(os.environ.get("ASD_GATE_I0_MIN_STARTS", "500"))
MIN_PRIMARY_ORGANISMS = int(os.environ.get("ASD_MIN_PRIMARY_ORGANISMS", "12"))
MIN_PRIMARY_FAMILIES = int(os.environ.get("ASD_MIN_PRIMARY_FAMILIES", "6"))

BASES = set("ACGU")
START_CODONS = {"AUG", "GUG", "UUG"}
STOP_CODONS = {codon for codon, aa in fetch_probe.CODON_TO_AA.items() if aa == "*"}
CANONICAL_TAIL_CORE = "CCUCCU"
CANONICAL_SD_MRNA = "AGGAGG"
LAMBDA = math.log(2.0)
EPS = 1.0e-12
SCRIPT_DIR = Path(__file__).resolve().parent
STRONG_SD_MIN_K = 5
STRONG_SD_MAX_K = 8
STRONG_SD_RAW_5MER = 9
STRONG_SD_RAW_6_8MER = 11
GATE_BG_WINDOW = 16
GATE_BG_PER_START = 5
GATE_EMPIRICAL_DRAWS = 1000

SCOPE_NOTE = (
    "Primary scope is Gate-I0-pass Bacteria with masked internal CDS windows. "
    "Archaea and Gate-I0-fail Bacteria are reported only as scope controls. "
    "The runner is stdlib-only and does not use numpy, Biopython, or BLAST."
)


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status in {"certified", "coincidence"} else (3 if status == "needs_external" else 2))


def stable_seed(text: str) -> int:
    return int.from_bytes(hashlib.sha256(text.encode("utf-8")).digest()[:16], "big")


def round_float(value: object, digits: int = 12) -> float | None:
    if not isinstance(value, (int, float)):
        return None
    value = float(value)
    if not math.isfinite(value):
        return value
    out = round(value, digits)
    return 0.0 if out == -0.0 else out


def median(values: list[float]) -> float | None:
    clean = [float(value) for value in values if math.isfinite(float(value))]
    return statistics.median(clean) if clean else None


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def sd(values: list[float]) -> float:
    return statistics.stdev(values) if len(values) >= 2 else 0.0


def percentile(values: list[float], q: float) -> float | None:
    clean = sorted(value for value in values if math.isfinite(value))
    if not clean:
        return None
    pos = (len(clean) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return clean[lo]
    return clean[lo] * (hi - pos) + clean[hi] * (pos - lo)


def z_score(obs: float, nulls: list[float]) -> float:
    sigma = sd(nulls)
    return 0.0 if sigma <= EPS else (obs - mean(nulls)) / sigma


def rank_low(value: float | None, competitors: list[float]) -> float | None:
    if value is None:
        return None
    clean = [float(v) for v in competitors if math.isfinite(float(v))]
    if not clean:
        return None
    return sum(1 for item in clean if item <= value) / (len(clean) + 1)


def rank_high(value: float | None, competitors: list[float]) -> float | None:
    if value is None:
        return None
    clean = [float(v) for v in competitors if math.isfinite(float(v))]
    if not clean:
        return None
    return sum(1 for item in clean if item >= value) / (len(clean) + 1)


def family_bootstrap(values: list[float], families: list[str], seed: str) -> dict[str, object]:
    pairs = [(float(v), fam or "unknown") for v, fam in zip(values, families) if math.isfinite(float(v))]
    if not pairs:
        return {"observed": None, "ci95": [None, None], "p_one_sided_negative": None, "n_blocks": 0}
    by_family: dict[str, list[float]] = defaultdict(list)
    for value, family in pairs:
        by_family[family].append(value)
    keys = sorted(by_family)
    observed = statistics.median(statistics.median(by_family[key]) for key in keys)
    rng = random.Random(stable_seed(seed))
    boots = []
    for _ in range(max(10, N_BOOTSTRAP)):
        sampled = [rng.choice(keys) for _ in keys]
        boots.append(statistics.median(statistics.median(by_family[key]) for key in sampled))
    p_neg = (1 + sum(1 for value in boots if value >= 0.0)) / (1 + len(boots))
    return {
        "observed": round_float(observed),
        "ci95": [round_float(percentile(boots, 0.025)), round_float(percentile(boots, 0.975))],
        "p_one_sided_negative": round_float(p_neg),
        "n_blocks": len(keys),
    }


def seq_gc(seq: str) -> float:
    return sum(1 for base in seq if base in "GC") / len(seq) if seq else 0.0


def rna_revcomp(seq: str) -> str:
    return v1.rna_revcomp(seq)


def genomic_interval_to_gene_positions(record: dict[str, object], lo: int, hi: int) -> set[int]:
    if not record.get("coord_available"):
        return set()
    start = int(record.get("start", 0))
    end = int(record.get("end", 0))
    left = max(start, lo)
    right = min(end, hi)
    if left >= right:
        return set()
    if str(record.get("strand") or "+") == "+":
        return {pos - start for pos in range(left, right)}
    return {end - 1 - pos for pos in range(left, right)}


def start_coord(record: dict[str, object]) -> int | None:
    if not record.get("coord_available"):
        return None
    return int(record["start"]) if str(record.get("strand") or "+") == "+" else int(record["end"]) - 1


def stop_coord(record: dict[str, object]) -> int | None:
    if not record.get("coord_available"):
        return None
    return int(record["end"]) - 1 if str(record.get("strand") or "+") == "+" else int(record["start"])


def transcript_order_key(record: dict[str, object]) -> int:
    if str(record.get("strand") or "+") == "+":
        return int(record.get("start", 0))
    return -int(record.get("end", 0))


def upstream_window(record: dict[str, object], contigs: dict[str, str], lo: int = -20, hi: int = -4) -> str | None:
    if not record.get("coord_available"):
        return None
    contig = contigs.get(str(record.get("seqid") or ""))
    if not contig:
        return None
    start = int(record["start"])
    end = int(record["end"])
    if str(record.get("strand") or "+") == "+":
        a = start + lo
        b = start + hi
        if a < 0 or b > len(contig) or a >= b:
            return None
        seq = contig[a:b].upper()
    else:
        a = end - hi
        b = end - lo
        if a < 0 or b > len(contig) or a >= b:
            return None
        seq = fetch_probe.reverse_complement_dna(contig[a:b])
    if len(seq) != hi - lo or any(base not in fetch_probe.BASES_DNA for base in seq):
        return None
    return fetch_probe.dna_to_rna(seq)


def strong_kmer_hit(kmer: str, table: dict[str, tuple[float, int]]) -> bool:
    raw = int(table.get(kmer, (0.0, 0))[1])
    if len(kmer) == 5:
        return raw >= STRONG_SD_RAW_5MER
    return len(kmer) >= 6 and raw >= STRONG_SD_RAW_6_8MER


def strong_sd_hit(seq: str, table: dict[str, tuple[float, int]]) -> bool:
    # The cutoff is expressed in raw antiparallel pairing points so the statistic
    # tracks concrete SD-like matches, not the maximum of a broad score field.
    clean = seq.upper()
    for k in range(STRONG_SD_MIN_K, STRONG_SD_MAX_K + 1):
        if len(clean) < k:
            continue
        for i in range(0, len(clean) - k + 1):
            kmer = clean[i : i + k]
            if set(kmer) <= BASES and strong_kmer_hit(kmer, table):
                return True
    return False


def strong_hit_fraction(windows: list[str], table: dict[str, tuple[float, int]]) -> tuple[float, int, int]:
    clean = [seq.upper() for seq in windows if seq and set(seq.upper()) <= BASES]
    hits = sum(1 for seq in clean if strong_sd_hit(seq, table))
    n = len(clean)
    return (hits / n if n else 0.0), hits, n


def profile_strong_metrics(profile: dict[str, object], table: dict[str, tuple[float, int]]) -> tuple[int, int, float]:
    counts = profile.get("counts")
    if not isinstance(counts, Counter):
        counts = Counter(counts if isinstance(counts, dict) else {})
    n = int(profile.get("n_windows") or sum(counts.values()))
    hits = 0
    for kmer, count in counts.items():
        text = str(kmer)
        if set(text) <= BASES and strong_kmer_hit(text, table):
            hits += int(count)
    return hits, n, (hits / n if n else 0.0)


def log2_density_ratio(obs_hits: int, obs_n: int, null_hits: int, null_n: int) -> float:
    obs_rate = (obs_hits + 0.5) / (obs_n + 1.0)
    null_rate = (null_hits + 0.5) / (null_n + 1.0)
    return math.log(obs_rate / max(EPS, null_rate), 2.0)


def eval_log2_ratio(obs_profile: dict[str, object], null_profiles: list[dict[str, object]], carrier: dict[str, object]) -> float:
    counts = obs_profile.get("counts")
    needed = set(str(kmer) for kmer in counts) if isinstance(counts, Counter) else set()
    for profile in null_profiles:
        pc = profile.get("counts")
        if isinstance(pc, Counter):
            needed.update(str(kmer) for kmer in pc)
    table = v1.score_table_for_kmers(carrier, needed)
    obs_hits, obs_n, _ = profile_strong_metrics(obs_profile, table)
    ratios = []
    for profile in null_profiles:
        null_hits, null_n, _ = profile_strong_metrics(profile, table)
        ratios.append(log2_density_ratio(obs_hits, obs_n, null_hits, null_n))
    return median(ratios) if ratios else 0.0


def canonical_sd_diagnostics(carrier: dict[str, object]) -> dict[str, object]:
    kmers = {CANONICAL_SD_MRNA, CANONICAL_SD_MRNA[1:]}
    table = v1.score_table_for_kmers(carrier, kmers)
    return {
        "AGGAGG_raw": int(table.get(CANONICAL_SD_MRNA, (0.0, 0))[1]),
        "GGAGG_raw": int(table.get(CANONICAL_SD_MRNA[1:], (0.0, 0))[1]),
    }


def profile_masked(
    seq: str,
    masked_positions: set[int],
    seed: str,
    m3_starts: set[int] | None = None,
) -> dict[str, object]:
    seq = seq.upper()
    counts: Counter[str] = Counter()
    possible: list[tuple[int, int]] = []
    prefix = [0] * (len(seq) + 1)
    if masked_positions:
        for idx in range(len(seq)):
            prefix[idx + 1] = prefix[idx] + (1 if idx in masked_positions else 0)
    for k in range(5, 9):
        for i in range(0, len(seq) - k + 1):
            if masked_positions and prefix[i + k] != prefix[i]:
                continue
            if m3_starts is not None and i in m3_starts:
                continue
            possible.append((i, k))
    if PROFILE_KMER_LIMIT > 0 and len(possible) > PROFILE_KMER_LIMIT:
        rng = random.Random(stable_seed(seed))
        possible = rng.sample(possible, PROFILE_KMER_LIMIT)
    for i, k in possible:
        kmer = seq[i : i + k]
        if set(kmer) <= BASES:
            counts[kmer] += 1
    return {"counts": counts, "n_windows": sum(counts.values())}


def m3_motif_starts(seq: str) -> set[int]:
    valid_start_positions = set()
    for pos in range(0, len(seq) - 2, 3):
        codon = seq[pos : pos + 3]
        if codon not in START_CODONS:
            continue
        aa_codons = 0
        for j in range(pos, len(seq) - 2, 3):
            if seq[j : j + 3] in STOP_CODONS:
                break
            aa_codons += 1
            if aa_codons >= 30:
                valid_start_positions.add(pos)
                break
    starts = set()
    for pos in valid_start_positions:
        for offset in range(4, 15):
            motif_start = pos - offset
            if motif_start >= 0:
                starts.add(motif_start)
    return starts


def masked_prefix(masked_positions: set[int], n: int) -> list[int]:
    prefix = [0] * (n + 1)
    if masked_positions:
        for idx in range(n):
            prefix[idx + 1] = prefix[idx] + (1 if idx in masked_positions else 0)
    return prefix


def background_exclusion_masks(records: list[dict[str, object]], contigs: dict[str, str], own_carrier: dict[str, object]) -> tuple[dict[int, set[int]], int]:
    masks: dict[int, set[int]] = {}
    for idx, record in enumerate(records):
        n = len(str(record.get("sequence_rna") or ""))
        masks[idx] = set(range(0, min(45, n))) | set(range(max(0, n - 30), n))
    coord_records = [(idx, record) for idx, record in enumerate(records) if record.get("coord_available")]
    starts_by_strand: dict[tuple[str, str], list[int]] = defaultdict(list)
    for _, record in coord_records:
        sc = start_coord(record)
        if sc is not None:
            starts_by_strand[(str(record.get("seqid") or ""), str(record.get("strand") or "+"))].append(sc)
    for idx, record in coord_records:
        seqid = str(record.get("seqid") or "")
        strand = str(record.get("strand") or "+")
        for sc in starts_by_strand[(seqid, strand)]:
            masks[idx].update(genomic_interval_to_gene_positions(record, sc - 25, sc + 16))

    table = v1.score_table(own_carrier)
    predicted_pairs = 0
    for key in sorted(set((str(r.get("seqid") or ""), str(r.get("strand") or "+")) for _, r in coord_records)):
        same = [(idx, r) for idx, r in coord_records if (str(r.get("seqid") or ""), str(r.get("strand") or "+")) == key]
        same.sort(key=lambda item: transcript_order_key(item[1]))
        for (up_idx, up), (_, down) in zip(same, same[1:]):
            if str(up.get("strand") or "+") == "+":
                gap = int(down.get("start", 0)) - int(up.get("end", 0))
            else:
                gap = int(up.get("start", 0)) - int(down.get("end", 0))
            if gap > 50:
                continue
            upwin = upstream_window(down, contigs)
            if not upwin or not strong_sd_hit(upwin, table):
                continue
            sc = start_coord(down)
            if sc is None:
                continue
            masks[up_idx].update(genomic_interval_to_gene_positions(up, sc - 35, sc + 16))
            predicted_pairs += 1
    return masks, predicted_pairs


def internal_background_candidates(records: list[dict[str, object]], contigs: dict[str, str], own_carrier: dict[str, object]) -> tuple[list[dict[str, object]], dict[str, object]]:
    exclusions, predicted_pairs = background_exclusion_masks(records, contigs, own_carrier)
    candidates: list[dict[str, object]] = []
    for idx, record in enumerate(records):
        seq = str(record.get("sequence_rna") or "").upper()
        if len(seq) < 120 or set(seq) - BASES:
            continue
        prefix = masked_prefix(exclusions.get(idx, set()), len(seq))
        for pos in range(45, max(45, len(seq) - 30 - GATE_BG_WINDOW + 1)):
            if prefix[pos + GATE_BG_WINDOW] != prefix[pos]:
                continue
            window = seq[pos : pos + GATE_BG_WINDOW]
            if len(window) == GATE_BG_WINDOW and set(window) <= BASES:
                candidates.append(
                    {
                        "seq": window,
                        "gc": window.count("G") + window.count("C"),
                        "g": window.count("G"),
                        "purine": window.count("A") + window.count("G"),
                    }
                )
    return candidates, {"candidate_windows": len(candidates), "m2_predicted_coupled_starts": predicted_pairs}


def matched_background_windows(
    records: list[dict[str, object]],
    contigs: dict[str, str],
    own_carrier: dict[str, object],
    upstream_windows: list[str],
    seed: str,
) -> tuple[list[str], dict[str, object]]:
    candidates, meta = internal_background_candidates(records, contigs, own_carrier)
    rng = random.Random(stable_seed(seed))
    out: list[str] = []
    exact_support = 0
    relaxed_support = 0
    no_support = 0
    bins: dict[tuple[int, int], list[str]] = defaultdict(list)
    for row in candidates:
        bins[(int(row["gc"]), int(row["g"]))].append(str(row["seq"]))
    for key in list(bins):
        bins[key].sort()

    def pool_for(gc: int, g: int, radius: int) -> list[str]:
        pool: list[str] = []
        for gc_key in range(gc - radius, gc + radius + 1):
            for g_key in range(g - radius, g + radius + 1):
                pool.extend(bins.get((gc_key, g_key), []))
        return pool

    for idx, upstream in enumerate(upstream_windows):
        gc = upstream.count("G") + upstream.count("C")
        g = upstream.count("G")
        exact = pool_for(gc, g, 1)
        pool = exact
        if not pool:
            pool = pool_for(gc, g, 2)
            if pool:
                relaxed_support += 1
            else:
                no_support += 1
                continue
        else:
            exact_support += 1
        keyed = sorted(pool)
        local_rng = random.Random(stable_seed(f"{seed}.{idx}.{upstream}.{rng.randrange(1 << 30)}"))
        if len(keyed) <= GATE_BG_PER_START:
            out.extend(keyed)
        else:
            out.extend(local_rng.sample(keyed, GATE_BG_PER_START))
    meta.update(
        {
            "background_windows": len(out),
            "exact_matched_starts": exact_support,
            "relaxed_matched_starts": relaxed_support,
            "unmatched_starts": no_support,
            "background_per_start_cap": GATE_BG_PER_START,
        }
    )
    return out, meta


def matched_draw_pvalue(obs_windows: list[str], bg_windows: list[str], table: dict[str, tuple[float, int]], observed_delta: float, seed: str) -> float:
    if not obs_windows or not bg_windows:
        return 1.0
    _, _, obs_n = strong_hit_fraction(obs_windows, table)
    _, _, bg_n = strong_hit_fraction(bg_windows, table)
    if obs_n <= 0 or bg_n <= 0:
        return 1.0
    rng = random.Random(stable_seed(seed))
    bg_fraction, _, _ = strong_hit_fraction(bg_windows, table)
    draws = max(100, GATE_EMPIRICAL_DRAWS)
    exceed = 0
    sample_n = min(obs_n, len(bg_windows))
    for draw_idx in range(draws):
        if len(bg_windows) <= sample_n:
            sample = bg_windows[:]
        else:
            sample = rng.sample(bg_windows, sample_n)
        sample_fraction, _, _ = strong_hit_fraction(sample, table)
        if sample_fraction - bg_fraction >= observed_delta - EPS:
            exceed += 1
    return (1 + exceed) / (1 + draws)


def parse_gff_coordinates(gff_text: str, fna_text: str) -> tuple[list[dict[str, object]], list[dict[str, object]], dict[str, str], dict[str, object]]:
    contigs = fetch_probe.parse_fasta_records(fna_text)
    cds: list[dict[str, object]] = []
    rrna: list[dict[str, object]] = []
    skipped: Counter[str] = Counter()
    for line in gff_text.splitlines():
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) < 9:
            continue
        seqid, _, feature, start_s, end_s, _, strand, _, attr_raw = fields[:9]
        if feature not in {"CDS", "rRNA"}:
            continue
        contig = contigs.get(seqid)
        if not contig:
            skipped["missing_contig"] += 1
            continue
        try:
            start = int(start_s) - 1
            end = int(end_s)
        except ValueError:
            skipped["bad_coordinate"] += 1
            continue
        attrs = fetch_probe.parse_gff_attributes(attr_raw)
        prod = " ".join(str(attrs.get(key, "")) for key in ("product", "Name", "gene", "Note", "locus_tag"))
        piece = contig[start:end].upper()
        if strand == "-":
            piece = fetch_probe.reverse_complement_dna(piece)
        if feature == "rRNA":
            if "16S" not in prod and "small subunit" not in prod.lower():
                continue
            if 1200 <= len(piece) <= 1700 and set(piece) <= fetch_probe.BASES_DNA:
                rrna.append({"sequence_rna": fetch_probe.dna_to_rna(piece), "product": prod, "strand": strand, "length_nt": len(piece)})
            continue
        intact, reason = fetch_probe.intact_cds_sequence(piece)
        if intact is None:
            skipped[str(reason)] += 1
            continue
        seq_rna = fetch_probe.dna_to_rna(intact)
        metrics = fetch_probe.sequence_metrics(seq_rna)
        cds.append(
            {
                "sequence_rna": seq_rna,
                "product": prod,
                "strand": strand if strand in {"+", "-"} else "+",
                "length_nt": len(seq_rna),
                "gc": metrics["gc"],
                "gc3": metrics["gc3"],
                "transl_table": int(attrs.get("transl_table", "11")) if str(attrs.get("transl_table", "11")).isdigit() else 11,
                "is_heg": fetch_probe.is_heg_product(prod, len(seq_rna)),
                "coord_available": True,
                "seqid": seqid,
                "start": start,
                "end": end,
            }
        )
    return cds, rrna, contigs, {"source_parser": "coordinate_gff", "skipped": dict(skipped), "n_contigs": len(contigs)}


def parse_gbff_coordinates(gbff_text: str) -> tuple[list[dict[str, object]], list[dict[str, object]], dict[str, str], dict[str, object]]:
    lines = gbff_text.splitlines()
    genome = fetch_probe.parse_origin(lines)
    features = fetch_probe.parse_features(lines)
    contigs = {"gbff": genome}
    cds: list[dict[str, object]] = []
    rrna: list[dict[str, object]] = []
    skipped: Counter[str] = Counter()
    for feature in features:
        key = str(feature.get("key") or "")
        if key not in {"CDS", "rRNA"}:
            continue
        qualifiers = feature.get("qualifiers")
        if not isinstance(qualifiers, dict):
            continue
        loc = fetch_probe.parse_location(str(feature.get("location") or ""))
        if loc is None:
            skipped["bad_location"] += 1
            continue
        strand, segments = loc
        seq_dna = fetch_probe.sequence_from_segments(genome, strand, segments)
        prod = fetch_probe.product_text(qualifiers)
        start = min(a for a, _ in segments)
        end = max(b for _, b in segments)
        if key == "rRNA":
            if "16S" not in prod and "small subunit" not in prod.lower():
                continue
            clean = re.sub(r"[^ACGT]", "N", seq_dna.upper())
            if 1200 <= len(clean) <= 1700 and "N" not in clean:
                rrna.append({"sequence_rna": fetch_probe.dna_to_rna(clean), "product": prod, "strand": strand, "length_nt": len(clean)})
            continue
        intact, reason = fetch_probe.intact_cds_sequence(seq_dna)
        if intact is None:
            skipped[str(reason)] += 1
            continue
        seq_rna = fetch_probe.dna_to_rna(intact)
        metrics = fetch_probe.sequence_metrics(seq_rna)
        cds.append(
            {
                "sequence_rna": seq_rna,
                "product": prod,
                "strand": strand,
                "length_nt": len(seq_rna),
                "gc": metrics["gc"],
                "gc3": metrics["gc3"],
                "transl_table": 11,
                "is_heg": fetch_probe.is_heg_product(prod, len(seq_rna)),
                "coord_available": True,
                "seqid": "gbff",
                "start": start,
                "end": end,
            }
        )
    return cds, rrna, contigs, {"source_parser": "coordinate_gbff", "skipped": dict(skipped), "n_contigs": 1}


def coordinate_records(organism: dict[str, object]) -> tuple[list[dict[str, object]], list[dict[str, object]], dict[str, str], dict[str, object]]:
    accession = str(organism.get("assembly_accession") or "")
    ftp_path = str(organism.get("ftp_path") or "")
    if ftp_path:
        gff, gff_contact = fetch_probe.cached_assembly_file(ftp_path, "genomic.gff.gz", accession)
        fna, fna_contact = fetch_probe.cached_assembly_file(ftp_path, "genomic.fna.gz", accession)
        if gff and fna:
            cds, rrna, contigs, meta = parse_gff_coordinates(gff, fna)
            if cds and rrna:
                return cds, rrna, contigs, {**meta, "contacts": {"gff": slim_contact(gff_contact), "fna": slim_contact(fna_contact)}}
        gbff, gbff_contact = fetch_probe.cached_assembly_file(ftp_path, "genomic.gbff.gz", accession)
        if gbff:
            cds, rrna, contigs, meta = parse_gbff_coordinates(gbff)
            if cds and rrna:
                return cds, rrna, contigs, {**meta, "contacts": {"gbff": slim_contact(gbff_contact)}}
    cds = []
    for row in organism.get("cds_records", []):
        if isinstance(row, dict):
            copy = dict(row)
            copy["coord_available"] = False
            cds.append(copy)
    rrna = [dict(row) for row in organism.get("rrna_records", []) if isinstance(row, dict)]
    return cds, rrna, {}, {"source_parser": "parsed_cache_without_coordinates", "coord_available": False}


def slim_contact(contact: dict[str, object]) -> dict[str, object]:
    return {key: contact.get(key) for key in ("on_disk_cache_hit", "borrowed_cache_hit", "reachable", "error", "cache_path") if key in contact}


def tail_sanity(rrnas: list[dict[str, object]], tail20: str, seed: str) -> dict[str, object]:
    tails13 = [str(row.get("sequence_rna") or "")[-13:].upper() for row in rrnas if len(str(row.get("sequence_rna") or "")) >= 13]
    cores = []
    for tail in tails13:
        candidates = [tail[i : i + 6] for i in range(0, len(tail) - 5)]
        cores.append(max(candidates, key=lambda item: v1.identity(item, CANONICAL_TAIL_CORE)) if candidates else "")
    consensus13 = "".join(Counter(tail[i] for tail in tails13 if len(tail) > i).most_common(1)[0][0] for i in range(13)) if tails13 else ""
    max_core_div = 0
    for i, left in enumerate(cores):
        for right in cores[i + 1 :]:
            if len(left) == len(right) == 6:
                max_core_div = max(max_core_div, sum(1 for a, b in zip(left, right) if a != b))

    true_carrier = v1.carrier_from_tail("true", "own_tail", tail20)
    table = v1.score_table_for_kmers(true_carrier, set(v1.ALL_KMERS_BY_K[6]))
    best_tail_core = max([tail20[i : i + 6] for i in range(0, len(tail20) - 5)], key=lambda item: v1.identity(item, CANONICAL_TAIL_CORE))
    exact_kmer = rna_revcomp(best_tail_core)
    exact_score = table.get(exact_kmer, (0.0, 0))[0]
    all_scores = sorted((score for score, _ in table.values()), reverse=True)
    exact_rank = (sum(1 for score in all_scores if score > exact_score) + 1) / max(1, len(all_scores))

    rev_carrier = v1.carrier_from_tail("reverse", "reverse_tail", tail20[::-1])
    rev_table = v1.score_table_for_kmers(rev_carrier, set(v1.ALL_KMERS_BY_K[6]))
    rev_score = rev_table.get(exact_kmer, (0.0, 0))[0]
    rev_scores = sorted((score for score, _ in rev_table.values()), reverse=True)
    reverse_rank = (sum(1 for score in rev_scores if score > rev_score) + 1) / max(1, len(rev_scores))
    canonical_similarity = max(v1.identity(tail20[i : i + 6], CANONICAL_TAIL_CORE) for i in range(0, len(tail20) - 5))
    failed = max_core_div > 1 or exact_rank > 0.01 or reverse_rank <= 0.01 or canonical_similarity < (4 / 6)
    return {
        "passed": not failed,
        "n_16s_copies": len(tails13),
        "consensus_tail_13nt": consensus13,
        "copy_core6_max_divergence": max_core_div,
        "synthetic_exact_complement_rank": round_float(exact_rank),
        "reverse_orientation_rank": round_float(reverse_rank),
        "canonical_similarity_core6": round_float(canonical_similarity),
        "best_tail_core6": best_tail_core,
    }


def build_masks(records: list[dict[str, object]], contigs: dict[str, str], own_carrier: dict[str, object]) -> tuple[dict[int, dict[str, set[int]]], dict[str, object]]:
    masks: dict[int, dict[str, set[int]]] = {}
    for idx, record in enumerate(records):
        n = len(str(record.get("sequence_rna") or ""))
        masks[idx] = {
            "unmasked": set(),
            "M0": set(range(0, min(45, n))) | set(range(max(0, n - 30), n)),
            "M1": set(),
            "M2": set(),
        }
    coord_records = [(idx, record) for idx, record in enumerate(records) if record.get("coord_available")]
    starts_by_strand: dict[tuple[str, str], list[int]] = defaultdict(list)
    for _, record in coord_records:
        sc = start_coord(record)
        if sc is not None:
            starts_by_strand[(str(record.get("seqid") or ""), str(record.get("strand") or "+"))].append(sc)
    for idx, record in coord_records:
        seqid = str(record.get("seqid") or "")
        strand = str(record.get("strand") or "+")
        for sc in starts_by_strand[(seqid, strand)]:
            masks[idx]["M1"].update(genomic_interval_to_gene_positions(record, sc - 25, sc + 16))

    table = v1.score_table(own_carrier)
    predicted_pairs = 0
    for key in sorted(set((str(r.get("seqid") or ""), str(r.get("strand") or "+")) for _, r in coord_records)):
        same = [(idx, r) for idx, r in coord_records if (str(r.get("seqid") or ""), str(r.get("strand") or "+")) == key]
        same.sort(key=lambda item: transcript_order_key(item[1]))
        for (up_idx, up), (_, down) in zip(same, same[1:]):
            if str(up.get("strand") or "+") == "+":
                gap = int(down.get("start", 0)) - int(up.get("end", 0))
            else:
                gap = int(up.get("start", 0)) - int(down.get("end", 0))
            if gap > 50:
                continue
            upwin = upstream_window(down, contigs)
            if not upwin or not strong_sd_hit(upwin, table):
                continue
            sc = start_coord(down)
            if sc is None:
                continue
            masks[up_idx]["M2"].update(genomic_interval_to_gene_positions(up, sc - 35, sc + 16))
            predicted_pairs += 1
    return masks, {"coordinate_genes": len(coord_records), "m2_predicted_coupled_starts": predicted_pairs}


def combined_mask(stage: str, parts: dict[str, set[int]]) -> tuple[set[int], bool]:
    if stage == "unmasked":
        return set(), False
    mask = set(parts["M0"])
    if stage in {"M0_M1", "M0_M1_M2", "M0_M1_M2_M3"}:
        mask.update(parts["M1"])
    if stage in {"M0_M1_M2", "M0_M1_M2_M3"}:
        mask.update(parts["M2"])
    return mask, stage == "M0_M1_M2_M3"


def gate_i0(records: list[dict[str, object]], contigs: dict[str, str], tail20: str, heterologous_tails: list[str], seed: str) -> dict[str, object]:
    own = v1.carrier_from_tail("own", "own_tail", tail20)
    decoys = v1.decoy_carriers(tail20, heterologous_tails, records[:80], max(6, N_DECOYS), seed + ".gate.decoys")
    canonical = v1.carrier_from_windows("canonical", "canonical_tail_core", [CANONICAL_TAIL_CORE])
    carriers = [own, canonical] + decoys
    usable_windows = []
    for record in records:
        seq = upstream_window(record, contigs)
        if seq and seq.count("N") == 0:
            usable_windows.append(seq)
    bg_windows, bg_meta = matched_background_windows(records, contigs, own, usable_windows, seed + ".gate.bg")
    effects: dict[str, float] = {}
    fractions: dict[str, tuple[float, int, int, float, int, int]] = {}
    for carrier in carriers:
        table = v1.score_table(carrier)
        obs_fraction, obs_hits, obs_n = strong_hit_fraction(usable_windows, table)
        bg_fraction, bg_hits, bg_n = strong_hit_fraction(bg_windows, table)
        effects[str(carrier["label"])] = obs_fraction - bg_fraction
        fractions[str(carrier["label"])] = (obs_fraction, obs_hits, obs_n, bg_fraction, bg_hits, bg_n)
    own_obs, own_hits, own_n, own_bg, bg_hits, bg_n = fractions.get("own", (0.0, 0, 0, 0.0, 0, 0))
    delta = own_obs - own_bg
    ratio = ((own_hits + 0.5) / (own_n + 1.0)) / max(EPS, ((bg_hits + 0.5) / (bg_n + 1.0)))
    decoy_effects = [value for label, value in effects.items() if label != "own"]
    own_rank = rank_high(delta, decoy_effects)
    usable_starts = len(usable_windows)
    required = usable_starts >= MIN_GATE_STARTS or usable_starts >= int(0.60 * max(1, len(records)))
    p_value = matched_draw_pvalue(usable_windows, bg_windows, v1.score_table(own), delta, seed + ".gate.p")
    passed = (
        required
        and own_obs >= 0.15
        and ratio >= 2.0
        and delta >= 0.05
        and p_value <= 0.01
        and (own_rank is not None and own_rank <= 0.35)
    )
    return {
        "passed": passed,
        "obs_fraction": round_float(own_obs),
        "bg_fraction": round_float(own_bg),
        "delta_fraction": round_float(delta),
        "ratio": round_float(ratio),
        "matched_empirical_p": round_float(p_value),
        "init_tail_rank": round_float(own_rank),
        "usable_starts": usable_starts,
        "usable_start_fraction": round_float(usable_starts / max(1, len(records))),
        "obs_hits": own_hits,
        "bg_hits": bg_hits,
        "bg_windows": bg_n,
        "effect_decoy_median": round_float(median(decoy_effects)),
        "matched_background": bg_meta,
        "strong_sd_thresholds": {"raw_5mer": STRONG_SD_RAW_5MER, "raw_6_8mer": STRONG_SD_RAW_6_8MER},
        "canonical_sd_diagnostics": canonical_sd_diagnostics(own),
    }


def cai_scores(records: list[dict[str, object]]) -> dict[int, float]:
    heg_weights = v1.organism_codon_weights(records, heg_only=True)
    out = {}
    for idx, record in enumerate(records):
        vals = []
        for codon in v1.codons(str(record.get("sequence_rna") or "")):
            aa = fetch_probe.CODON_TO_AA.get(codon)
            if aa and aa != "*":
                vals.append(math.log(max(1.0e-9, heg_weights.get(aa, {}).get(codon, 1.0e-9))))
        out[idx] = mean(vals) if vals else -999.0
    return out


def leading_intergenic(record: dict[str, object], records: list[dict[str, object]]) -> int | None:
    if not record.get("coord_available"):
        return None
    same = [row for row in records if row.get("coord_available") and row.get("seqid") == record.get("seqid") and row.get("strand") == record.get("strand")]
    same.sort(key=transcript_order_key)
    idx = same.index(record) if record in same else -1
    if idx <= 0:
        return 10**9
    prev = same[idx - 1]
    if str(record.get("strand") or "+") == "+":
        return int(record.get("start", 0)) - int(prev.get("end", 0))
    return int(prev.get("start", 0)) - int(record.get("end", 0))


def select_analysis_records(records: list[dict[str, object]], seed: str) -> list[dict[str, object]]:
    eligible = [dict(row) for row in records if 150 <= int(row.get("length_nt", 0)) <= 2400 and set(str(row.get("sequence_rna") or "")) <= BASES]
    rng = random.Random(stable_seed(seed + ".select"))
    heg = [row for row in eligible if row.get("is_heg")]
    non = [row for row in eligible if not row.get("is_heg")]
    rng.shuffle(heg)
    rng.shuffle(non)
    keep_heg = heg[: min(len(heg), max(12, MAX_GENES_PER_ORGANISM // 4))]
    keep_non = non[: max(0, MAX_GENES_PER_ORGANISM - len(keep_heg))]
    return keep_heg + keep_non


def evaluate_organism(organism: dict[str, object], heterologous_tails: list[str], seed: str) -> dict[str, object]:
    records, rrnas, contigs, coord_meta = coordinate_records(organism)
    tail20, tail_meta = v1.consensus_terminal20(rrnas)
    if tail20 is None:
        return {"ok": False, "drop_reason": "carrier_unavailable", "assembly_accession": organism.get("assembly_accession")}
    own_carrier = v1.carrier_from_tail("own", "own_tail", tail20)
    canonical_carrier = v1.carrier_from_windows("canonical_core", "canonical_tail_core", [CANONICAL_TAIL_CORE])
    sanity = tail_sanity(rrnas, tail20, seed + ".tail")
    gate = gate_i0(records, contigs, tail20, heterologous_tails, seed)
    masks, mask_meta = build_masks(records, contigs, own_carrier)
    selected = select_analysis_records(records, seed)
    if len(selected) < 12:
        return {"ok": False, "drop_reason": "insufficient_analysis_cds", "assembly_accession": organism.get("assembly_accession"), "gate_i0": gate}

    record_to_idx = {id(row): idx for idx, row in enumerate(records)}
    coord_key_to_idx = {(row.get("seqid"), row.get("start"), row.get("end"), row.get("strand"), row.get("product")): idx for idx, row in enumerate(records)}
    selected_indices = []
    for row in selected:
        key = (row.get("seqid"), row.get("start"), row.get("end"), row.get("strand"), row.get("product"))
        selected_indices.append(coord_key_to_idx.get(key, record_to_idx.get(id(row), 0)))

    decoys = v1.decoy_carriers(tail20, heterologous_tails, selected, max(4, N_DECOYS), seed + ".decoys")
    weights = v1.organism_codon_weights(records, heg_only=False)
    heg_weights = v1.organism_codon_weights(records, heg_only=True)
    cai = cai_scores(records)
    cai_cut = percentile([cai.get(idx, -999.0) for idx, row in enumerate(records) if not row.get("is_heg")], 0.90) or 999.0

    stages = ["unmasked", "M0", "M0_M1", "M0_M1_M2", "M0_M1_M2_M3"]
    stage_d: dict[str, list[float]] = {stage: [] for stage in stages}
    stage_windows: dict[str, int] = {stage: 0 for stage in stages}
    stage_heg_windows: dict[str, int] = {stage: 0 for stage in stages}
    pc1_d: list[float] = []
    pc2_d: list[float] = []
    own_clean_d: list[float] = []
    place_clean_d: list[float] = []
    decoy_clean_d: dict[str, list[float]] = {str(d["label"]): [] for d in decoys}
    strata: dict[str, list[float]] = {"ribosomal_all_masked": [], "ribosomal_leading_only": [], "nonribo_CAI_top10": [], "matched_background": []}

    for local_idx, (record, original_idx) in enumerate(zip(selected, selected_indices)):
        seq = str(record.get("sequence_rna") or "")
        rec_weights = heg_weights if record.get("is_heg") else weights
        null1, _ = v1.constrained_recodings(seq, rec_weights, R_NULL, f"{seed}.gene.{local_idx}.null1")
        null_place = v1.exact_multiset_permutations(seq, NULL_PLACE_R, f"{seed}.gene.{local_idx}.place")
        parts = masks.get(original_idx, {"unmasked": set(), "M0": set(range(0, min(45, len(seq)))), "M1": set(), "M2": set()})
        seq_m3_starts = m3_motif_starts(seq)
        null1_m3_starts = [m3_motif_starts(candidate) for candidate in null1]
        place_m3_starts = [m3_motif_starts(candidate) for candidate in null_place]

        profiles_by_stage: dict[str, tuple[dict[str, object], list[dict[str, object]]]] = {}
        for stage in stages:
            mask, m3 = combined_mask(stage, parts)
            obs_profile = profile_masked(seq, mask, f"{seed}.gene.{local_idx}.{stage}.obs", m3_starts=seq_m3_starts if m3 else None)
            null_profiles = [
                profile_masked(candidate, mask, f"{seed}.gene.{local_idx}.{stage}.null.{j}", m3_starts=null1_m3_starts[j] if m3 else None)
                for j, candidate in enumerate(null1)
            ]
            profiles_by_stage[stage] = (obs_profile, null_profiles)
            d_value = eval_log2_ratio(obs_profile, null_profiles, own_carrier)
            stage_d[stage].append(d_value)
            nwin = int(obs_profile.get("n_windows") or 0)
            stage_windows[stage] += nwin
            if record.get("is_heg"):
                stage_heg_windows[stage] += nwin

        clean_mask, clean_m3 = combined_mask("M0_M1_M2_M3", parts)
        clean_obs, clean_null = profiles_by_stage["M0_M1_M2_M3"]
        d_own = eval_log2_ratio(clean_obs, clean_null, own_carrier)
        own_clean_d.append(d_own)
        pc_d_value = eval_log2_ratio(clean_obs, clean_null, canonical_carrier)
        pc1_d.append(pc_d_value)
        if record.get("is_heg"):
            pc2_d.append(pc_d_value)
        place_profiles = [
            profile_masked(candidate, clean_mask, f"{seed}.gene.{local_idx}.place.{j}", m3_starts=place_m3_starts[j] if clean_m3 else None)
            for j, candidate in enumerate(null_place)
        ]
        place_clean_d.append(eval_log2_ratio(clean_obs, place_profiles, own_carrier))
        for decoy in decoys:
            decoy_clean_d[str(decoy["label"])].append(eval_log2_ratio(clean_obs, clean_null, decoy))

        if record.get("is_heg"):
            strata["ribosomal_all_masked"].append(d_own)
            ig = leading_intergenic(record, records)
            if ig is not None and ig >= 50 and int(record.get("length_nt", 0)) >= 200:
                strata["ribosomal_leading_only"].append(d_own)
        else:
            idx = original_idx
            close_coupled = (leading_intergenic(record, records) or 999999) < 50
            if cai.get(idx, -999.0) >= cai_cut and not close_coupled:
                strata["nonribo_CAI_top10"].append(d_own)
            elif not close_coupled:
                strata["matched_background"].append(d_own)

    clean_d = median(own_clean_d)
    decoy_ds = [median(vals) for vals in decoy_clean_d.values()]
    clean_rank = rank_low(clean_d, [float(v) for v in decoy_ds if v is not None])
    pc1_value = median(pc1_d)
    pc2_value = median(pc2_d)
    d_place = median(place_clean_d)
    unmasked_windows = max(1, stage_windows["unmasked"])
    unmasked_heg_windows = max(1, stage_heg_windows["unmasked"])
    mask_impact = {}
    for stage in stages:
        mask_impact[stage] = {
            "D": round_float(median(stage_d[stage])),
            "fraction_windows_removed": round_float(1.0 - stage_windows[stage] / unmasked_windows),
            "fraction_HEG_windows_removed": round_float(1.0 - stage_heg_windows[stage] / unmasked_heg_windows),
        }

    return {
        "ok": True,
        "assembly_accession": organism.get("assembly_accession"),
        "organism": organism.get("organism"),
        "domain": organism.get("domain"),
        "genus": organism.get("genus"),
        "family": organism.get("family") or organism.get("genus") or "unknown",
        "order": organism.get("order") or "unknown",
        "tail20": tail20,
        "tail_meta": tail_meta,
        "tail_sanity": sanity,
        "gate_i0": gate,
        "coordinate_meta": coord_meta,
        "mask_meta": mask_meta,
        "n_cds": len(records),
        "n_selected": len(selected),
        "n_heg_selected": sum(1 for row in selected if row.get("is_heg")),
        "D_PC1": pc1_value,
        "D_PC2": pc2_value,
        "D_abundance_clean": clean_d,
        "clean_decoy_rank": clean_rank,
        "D_place_clean": d_place,
        "Z_ribosomal_all_masked": median(strata["ribosomal_all_masked"]),
        "Z_ribosomal_leading_only": median(strata["ribosomal_leading_only"]),
        "Z_nonribo_CAI_top10": median(strata["nonribo_CAI_top10"]),
        "Z_matched_background": median(strata["matched_background"]),
        "strata_counts": {key: len(vals) for key, vals in strata.items()},
        "mask_impact": mask_impact,
        "estimator": "strong_sd_hit_log2_density_ratio",
    }


def sign_fraction_by_family(rows: list[dict[str, object]], key: str) -> float | None:
    by_family: dict[str, list[float]] = defaultdict(list)
    for row in rows:
        value = row.get(key)
        if isinstance(value, (int, float)) and math.isfinite(float(value)):
            by_family[str(row.get("family") or "unknown")].append(float(value))
    if not by_family:
        return None
    signs = [statistics.median(vals) < 0.0 for vals in by_family.values()]
    return sum(1 for value in signs if value) / len(signs)


def aggregate(rows: list[dict[str, object]], fetch_meta: dict[str, object], elapsed: float) -> dict[str, object]:
    ok = [row for row in rows if row.get("ok")]
    bacteria = [row for row in ok if row.get("domain") == "Bacteria"]
    archaea = [row for row in ok if row.get("domain") == "Archaea"]
    primary = [row for row in bacteria if row.get("gate_i0", {}).get("passed") and row.get("tail_sanity", {}).get("passed")]
    families = sorted(set(str(row.get("family") or "unknown") for row in primary))

    pc_rows = bacteria
    pc_values = [float(row["D_PC1"]) for row in pc_rows if isinstance(row.get("D_PC1"), (int, float))]
    pc_families = [str(row.get("family") or "unknown") for row in pc_rows if isinstance(row.get("D_PC1"), (int, float))]
    pc_boot = family_bootstrap(pc_values, pc_families, EXPERIMENT_ID + ".pc1")
    pc_sign = sign_fraction_by_family(pc_rows, "D_PC1")
    pc1_passed = bool(pc_values) and (median(pc_values) or 0.0) <= -0.15 and (pc_boot["ci95"][1] is not None and float(pc_boot["ci95"][1]) <= 0.0) and (pc_sign is not None and pc_sign >= 0.60)
    pc2_values = [float(row["D_PC2"]) for row in pc_rows if isinstance(row.get("D_PC2"), (int, float))]
    pc2_passed = bool(pc2_values) and (median(pc2_values) or 0.0) < 0.0

    d_vals = [float(row["D_abundance_clean"]) for row in primary if isinstance(row.get("D_abundance_clean"), (int, float))]
    d_fams = [str(row.get("family") or "unknown") for row in primary if isinstance(row.get("D_abundance_clean"), (int, float))]
    rank_vals = [float(row["clean_decoy_rank"]) for row in primary if isinstance(row.get("clean_decoy_rank"), (int, float))]
    place_vals = [float(row["D_place_clean"]) for row in primary if isinstance(row.get("D_place_clean"), (int, float))]
    ribo_leading = [float(row["Z_ribosomal_leading_only"]) for row in primary if isinstance(row.get("Z_ribosomal_leading_only"), (int, float))]
    nonribo_cai = [float(row["Z_nonribo_CAI_top10"]) for row in primary if isinstance(row.get("Z_nonribo_CAI_top10"), (int, float))]
    d_boot = family_bootstrap(d_vals, d_fams, EXPERIMENT_ID + ".abundance")
    d_sign = sign_fraction_by_family(primary, "D_abundance_clean")

    h1 = bool(d_vals) and (median(d_vals) or 0.0) < 0.0
    h2 = bool(rank_vals) and (median(rank_vals) or 1.0) <= 0.35
    h3 = ((median(nonribo_cai) is not None and (median(nonribo_cai) or 0.0) <= -0.25) or (median(ribo_leading) is not None and (median(ribo_leading) or 0.0) <= -0.25))
    h4 = bool(place_vals) and (median(place_vals) or 0.0) < 0.0
    rescue_passed = (
        pc1_passed
        and bool(d_vals)
        and (median(d_vals) or 0.0) <= -0.25
        and h2
        and isinstance(d_boot.get("p_one_sided_negative"), float)
        and float(d_boot["p_one_sided_negative"]) <= 0.10
        and d_sign is not None
        and d_sign >= 0.60
        and h3
    )

    if not pc1_passed:
        decision = "DEBUG"
        status = "needs_external"
    elif rescue_passed:
        decision = "SCALE"
        status = "needs_external"
    elif (not h1 or not h2) and h4:
        decision = "PIVOT_PLACEMENT"
        status = "coincidence"
    else:
        decision = "REFUTE"
        status = "refuted"

    compact = []
    for row in ok:
        compact.append(
            {
                "assembly_accession": row.get("assembly_accession"),
                "organism": row.get("organism"),
                "domain": row.get("domain"),
                "family": row.get("family"),
                "gate_i0": row.get("gate_i0"),
                "tail_sanity": row.get("tail_sanity"),
                "D_PC1": round_float(row.get("D_PC1")),
                "D_PC2": round_float(row.get("D_PC2")),
                "D_abundance_clean": round_float(row.get("D_abundance_clean")),
                "clean_decoy_rank": round_float(row.get("clean_decoy_rank")),
                "D_place_clean": round_float(row.get("D_place_clean")),
                "Z_ribosomal_leading_only": round_float(row.get("Z_ribosomal_leading_only")),
                "Z_nonribo_CAI_top10": round_float(row.get("Z_nonribo_CAI_top10")),
                "strata_counts": row.get("strata_counts"),
                "mask_impact": row.get("mask_impact"),
            }
        )

    return {
        "status": status,
        "DECISION": decision,
        "verdict": status,
        "scope_note": SCOPE_NOTE,
        "honest_scope_note": SCOPE_NOTE,
        "PC1": {
            "passed": pc1_passed,
            "median_D_PC1": round_float(median(pc_values)),
            "family_block_bootstrap": pc_boot,
            "negative_family_fraction": round_float(pc_sign),
        },
        "PC2": {"passed": pc2_passed, "median_D_PC2": round_float(median(pc2_values))},
        "Gate_I0": {
            "pass_count": len(primary),
            "bacteria_evaluated": len(bacteria),
            "tail_sanity_pass_count": sum(1 for row in bacteria if row.get("tail_sanity", {}).get("passed")),
        },
        "H1_H4": {
            "H1_median_D_abundance_clean_lt_0": h1,
            "H2_median_clean_decoy_rank_le_0_35": h2,
            "H3_HEG_B_or_C_negative": h3,
            "H4_median_D_place_clean_lt_0": h4,
            "median_D_abundance_clean": round_float(median(d_vals)),
            "median_clean_decoy_rank": round_float(median(rank_vals)),
            "median_Z_HEG_nonribo_CAI_top10": round_float(median(nonribo_cai)),
            "median_Z_ribosomal_leading_only": round_float(median(ribo_leading)),
            "median_D_place_clean": round_float(median(place_vals)),
            "family_block_abundance": d_boot,
            "negative_family_fraction": round_float(d_sign),
            "rescue_passed": rescue_passed,
        },
        "D_place": {"median_D_place_clean": round_float(median(place_vals)), "n": len(place_vals)},
        "tail_sanity_summary": {
            "passed": sum(1 for row in ok if row.get("tail_sanity", {}).get("passed")),
            "failed": sum(1 for row in ok if not row.get("tail_sanity", {}).get("passed")),
        },
        "mask_impact_summary": summarize_mask_impact(primary),
        "n_primary": len(primary),
        "n_primary_bacteria": len(primary),
        "n_families": len(families),
        "n_bacteria_evaluated": len(bacteria),
        "n_archaea_exploratory": len(archaea),
        "parameters": {
            "target_bacteria": TARGET_BACTERIA,
            "target_archaea": TARGET_ARCHAEA,
            "analysis_organism_limit": ANALYSIS_ORGANISM_LIMIT,
            "r_null": R_NULL,
            "null_place_r": NULL_PLACE_R,
            "n_decoys": N_DECOYS,
            "n_bootstrap": N_BOOTSTRAP,
            "max_genes_per_organism": MAX_GENES_PER_ORGANISM,
            "numpy_free": True,
            "biopython_free": True,
            "blast_free": True,
        },
        "fetch_meta": {
            "n_attempts": fetch_meta.get("n_attempts"),
            "n_organisms": fetch_meta.get("n_organisms"),
            "accepted_by_domain": fetch_meta.get("accepted_by_domain"),
            "fetch_success_rate": fetch_meta.get("fetch_success_rate"),
        },
        "timing_seconds": round_float(elapsed, 6),
        "per_organism": compact,
        "drops": [row for row in rows if not row.get("ok")],
    }


def summarize_mask_impact(rows: list[dict[str, object]]) -> dict[str, object]:
    stages = ["unmasked", "M0", "M0_M1", "M0_M1_M2", "M0_M1_M2_M3"]
    out = {}
    for stage in stages:
        ds = []
        removed = []
        heg_removed = []
        for row in rows:
            impact = row.get("mask_impact")
            if not isinstance(impact, dict) or stage not in impact:
                continue
            item = impact[stage]
            if isinstance(item, dict):
                if isinstance(item.get("D"), (int, float)):
                    ds.append(float(item["D"]))
                if isinstance(item.get("fraction_windows_removed"), (int, float)):
                    removed.append(float(item["fraction_windows_removed"]))
                if isinstance(item.get("fraction_HEG_windows_removed"), (int, float)):
                    heg_removed.append(float(item["fraction_HEG_windows_removed"]))
        out[stage] = {
            "median_D": round_float(median(ds)),
            "median_fraction_windows_removed": round_float(median(removed)),
            "median_fraction_HEG_windows_removed": round_float(median(heg_removed)),
        }
    return out


def main() -> None:
    start = time.monotonic()
    fetch_bacteria = min(TARGET_BACTERIA, max(1, ANALYSIS_ORGANISM_LIMIT))
    fetch_archaea = min(TARGET_ARCHAEA, max(0, ANALYSIS_ORGANISM_LIMIT - fetch_bacteria))
    fetch_attempts = min(MAX_FETCH_ATTEMPTS, max(fetch_bacteria + fetch_archaea, ANALYSIS_ORGANISM_LIMIT + 8))
    organisms, fetch_meta = fetch_probe.fetch_panel(
        target_bacteria=fetch_bacteria,
        target_archaea=fetch_archaea,
        max_attempts=fetch_attempts,
        seed=EXPERIMENT_ID + ".fetch",
        deadline_seconds=FETCH_DEADLINE_SECONDS,
    )
    organisms = organisms[:ANALYSIS_ORGANISM_LIMIT]
    tail_pairs = []
    for organism in organisms:
        rrnas = [row for row in organism.get("rrna_records", []) if isinstance(row, dict)]
        tail, _ = v1.consensus_terminal20(rrnas)
        if tail:
            tail_pairs.append((str(organism.get("assembly_accession") or ""), tail))

    rows: list[dict[str, object]] = []
    for organism in organisms:
        accession = str(organism.get("assembly_accession") or "")
        heterologous = [tail for other, tail in tail_pairs if other != accession]
        try:
            row = evaluate_organism(organism, heterologous, EXPERIMENT_ID + "." + accession)
        except Exception as exc:
            row = {
                "ok": False,
                "assembly_accession": accession,
                "organism": organism.get("organism"),
                "domain": organism.get("domain"),
                "drop_reason": f"analysis_error:{type(exc).__name__}:{exc}",
            }
        rows.append(row)

    summary = aggregate(rows, fetch_meta, time.monotonic() - start)
    status = str(summary.pop("status"))
    emit(status, **summary)


if __name__ == "__main__":
    main()

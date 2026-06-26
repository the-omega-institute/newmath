#!/usr/bin/env python3
"""ASD-shadow exclusion pilot runner."""
from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import json
import math
import os
from pathlib import Path
import random
import statistics
import sys
import time
from typing import Any

import _asd_fetch_probe as fetch_probe


EXPERIMENT_ID = "asd_shadow_exclusion"
CLAIM_ID = "bridge.genetic_code.asd_shadow_exclusion"

TARGET_BACTERIA = int(os.environ.get("ASD_TARGET_BACTERIA", "50"))
TARGET_ARCHAEA = int(os.environ.get("ASD_TARGET_ARCHAEA", "10"))
MAX_FETCH_ATTEMPTS = int(os.environ.get("ASD_MAX_FETCH_ATTEMPTS", str(TARGET_BACTERIA + TARGET_ARCHAEA)))
FETCH_DEADLINE_SECONDS = float(os.environ.get("ASD_FETCH_DEADLINE_SECONDS", "60"))
REQUESTED_R_NULL = 150
REQUESTED_N_DECOYS = 40
REQUESTED_MAX_GENES_PER_ORGANISM = 60
R_NULL = int(os.environ.get("ASD_NULL_R", "20"))
N_DECOYS = int(os.environ.get("ASD_N_DECOYS", "12"))
N_BOOTSTRAP = int(os.environ.get("ASD_BOOTSTRAP", "120"))
MAX_GENES_PER_ORGANISM = int(os.environ.get("ASD_MAX_GENES_PER_ORGANISM", "24"))
MAX_HEG_PER_ORGANISM = int(os.environ.get("ASD_MAX_HEG_PER_ORGANISM", "12"))
MIN_HEG_PER_ORGANISM = int(os.environ.get("ASD_MIN_HEG_PER_ORGANISM", "10"))
ANALYSIS_ORGANISM_LIMIT = int(os.environ.get("ASD_ANALYSIS_ORGANISM_LIMIT", "3"))
MIN_CERT_ORGANISMS = 250
MIN_CERT_FAMILIES = 30
LAMBDA = math.log(2.0)
EPS = 1.0e-12

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[2]

BASES = "UCAG"
CANONICAL_ASD = "AGGAGG"
SCOPE_NOTE = (
    "statistical synonymous-level depletion of internal anti-SD-complementary motifs in annotated high-expression "
    "(ribosomal-protein) genes vs length/GC3/strand/gene-GC-matched controls; scoped ONLY to canonical Shine-Dalgarno "
    "(leadered) initiation taxa; does NOT extend to leaderless mRNAs, S1-dependent or divergent-anti-SD organisms; "
    "not causal proof of pause avoidance. PILOT scale - directional only, data-gate unmet."
)


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status in {"certified", "coincidence"} else (3 if status == "needs_external" else 2))


def stable_seed(text: str) -> int:
    return int.from_bytes(hashlib.sha256(text.encode("utf-8")).digest()[:16], "big")


def round_float(value: float | None, digits: int = 12) -> float | None:
    if value is None:
        return None
    if not math.isfinite(value):
        return value
    out = round(float(value), digits)
    return 0.0 if out == -0.0 else out


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def sd(values: list[float]) -> float:
    if len(values) < 2:
        return 0.0
    return statistics.stdev(values)


def percentile(values: list[float], q: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    pos = (len(ordered) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return ordered[lo]
    return ordered[lo] * (hi - pos) + ordered[hi] * (pos - lo)


def median(values: list[float]) -> float | None:
    return statistics.median(values) if values else None


def weighted_median(pairs: list[tuple[float, float]]) -> float | None:
    clean = [(value, max(0.0, weight)) for value, weight in pairs if math.isfinite(value) and weight > 0]
    if not clean:
        return None
    clean.sort(key=lambda item: item[0])
    total = sum(weight for _, weight in clean)
    acc = 0.0
    for value, weight in clean:
        acc += weight
        if acc >= 0.5 * total:
            return value
    return clean[-1][0]


def rank_percentile(value: float, null_values: list[float]) -> float | None:
    values = [v for v in null_values if math.isfinite(v)]
    if not values:
        return None
    return (sum(1 for v in values if v <= value) + 0.5) / (len(values) + 1)


def bootstrap_ci(values: list[float], blocks: list[str], n_bootstrap: int, seed: str) -> dict[str, object]:
    pairs = [(value, block or "unknown") for value, block in zip(values, blocks) if math.isfinite(value)]
    if not pairs:
        return {"p_directional": None, "ci95": [None, None], "n_blocks": 0}
    by_block: dict[str, list[float]] = defaultdict(list)
    for value, block in pairs:
        by_block[block].append(value)
    keys = sorted(by_block)
    observed = statistics.median([statistics.median(by_block[key]) for key in keys])
    rng = random.Random(stable_seed(seed))
    boots = []
    for _ in range(n_bootstrap):
        sampled = [rng.choice(keys) for _ in keys]
        block_medians = [statistics.median(by_block[key]) for key in sampled]
        boots.append(statistics.median(block_medians))
    reverse = sum(1 for value in boots if value >= 0.0) if observed < 0 else sum(1 for value in boots if value <= 0.0)
    return {
        "observed": round_float(observed),
        "p_directional": round_float((1 + reverse) / (1 + len(boots))),
        "ci95": [round_float(percentile(boots, 0.025)), round_float(percentile(boots, 0.975))],
        "n_blocks": len(keys),
    }


def rna_revcomp(seq: str) -> str:
    return seq.translate(str.maketrans("ACGUacgu", "UGCAugca"))[::-1].upper()


def pair_score(left: str, right: str) -> int:
    score = 0
    for a, b in zip(left, right):
        if (a, b) in {("A", "U"), ("U", "A"), ("G", "C"), ("C", "G")}:
            score += 2
        elif (a, b) in {("G", "U"), ("U", "G")}:
            score += 1
    return score


def all_kmers(k: int) -> list[str]:
    if k == 0:
        return [""]
    prev = all_kmers(k - 1)
    return [prefix + base for prefix in prev for base in BASES]


ALL_KMERS_BY_K = {k: all_kmers(k) for k in range(5, 9)}


def terminal_tail(rrna_sequence: str) -> str:
    return rrna_sequence[-30:].upper()


def terminal20(rrna_sequence: str) -> str:
    return rrna_sequence[-20:].upper()


def identity(left: str, right: str) -> float:
    if not left or not right or len(left) != len(right):
        return 0.0
    return sum(1 for a, b in zip(left, right) if a == b) / len(left)


def consensus_terminal20(rrnas: list[dict[str, object]]) -> tuple[str | None, dict[str, object]]:
    tails = [terminal20(str(row.get("sequence_rna") or "")) for row in rrnas if len(str(row.get("sequence_rna") or "")) >= 20]
    if not tails:
        return None, {"drop_reason": "no_terminal20"}
    min_pairwise = 1.0
    for i, left in enumerate(tails):
        for right in tails[i + 1 :]:
            min_pairwise = min(min_pairwise, identity(left, right))
    if len(tails) > 1 and min_pairwise < 0.8:
        return None, {"drop_reason": "rrn_terminal20_identity_below_0_8", "min_pairwise_identity": min_pairwise, "n_rrn": len(tails)}
    consensus = []
    for pos in range(20):
        counts = Counter(tail[pos] for tail in tails if pos < len(tail))
        consensus.append(counts.most_common(1)[0][0])
    return "".join(consensus), {"n_rrn": len(tails), "min_pairwise_identity": min_pairwise}


def carrier_windows_from_tail20(tail20: str) -> list[str]:
    out = []
    for k in range(5, 9):
        for i in range(0, len(tail20) - k + 1):
            window = tail20[i : i + k].upper()
            if set(window) <= set(BASES):
                out.append(window)
    return sorted(set(out))


def carrier_from_windows(label: str, class_name: str, windows: list[str]) -> dict[str, object]:
    return {"label": label, "class": class_name, "windows": sorted(set(windows))}


def carrier_from_tail(label: str, class_name: str, tail20: str) -> dict[str, object]:
    return carrier_from_windows(label, class_name, carrier_windows_from_tail20(tail20))


def score_table(carrier: dict[str, object]) -> dict[str, tuple[float, int]]:
    windows = [str(w) for w in carrier.get("windows", [])]
    by_len: dict[int, list[str]] = defaultdict(list)
    for window in windows:
        by_len[len(window)].append(rna_revcomp(window))
    table: dict[str, tuple[float, int]] = {}
    for k, kmers in ALL_KMERS_BY_K.items():
        targets = by_len.get(k, [])
        for kmer in kmers:
            if not targets:
                table[kmer] = (0.0, 0)
                continue
            best = max(pair_score(kmer, target) for target in targets)
            table[kmer] = (best / k, best)
    return table


def burden(seq: str, table: dict[str, tuple[float, int]]) -> dict[str, float]:
    return burden_from_profile(kmer_profile(seq), table)


def kmer_profile(seq: str) -> dict[str, object]:
    internal = seq[45:-45] if len(seq) > 90 else ""
    counts: Counter[str] = Counter()
    if len(internal) < 8:
        return {"counts": counts, "n_windows": 0}
    for k in range(5, 9):
        for i in range(0, len(internal) - k + 1):
            kmer = internal[i : i + k]
            if set(kmer) - set(BASES):
                continue
            counts[kmer] += 1
    return {"counts": counts, "n_windows": sum(counts.values())}


def burden_from_profile(profile: dict[str, object], table: dict[str, tuple[float, int]]) -> dict[str, float]:
    counts = profile.get("counts")
    if not isinstance(counts, Counter):
        counts = Counter(counts if isinstance(counts, dict) else {})
    n = int(profile.get("n_windows") or sum(counts.values()))
    if n <= 0:
        return {"shadow": 0.0, "strong_count": 0.0, "max_shadow": 0.0, "n_windows": 0.0}
    total = 0.0
    strong = 0
    max_shadow = 0.0
    for kmer, count in counts.items():
        normalized, raw = table[str(kmer)]
        value = math.exp(LAMBDA * normalized)
        total += value * int(count)
        max_shadow = max(max_shadow, value)
        if len(str(kmer)) >= 6 and raw >= 11:
            strong += int(count)
    return {"shadow": total / n if n else 0.0, "strong_count": float(strong), "max_shadow": max_shadow, "n_windows": float(n)}


def codons(seq: str) -> list[str]:
    return [seq[i : i + 3] for i in range(0, len(seq) - 2, 3)]


def aa_sequence(seq: str) -> str:
    return "".join(fetch_probe.CODON_TO_AA.get(codon, "X") for codon in codons(seq))


def sense_families() -> dict[str, list[str]]:
    fam: dict[str, list[str]] = defaultdict(list)
    for codon, aa in fetch_probe.CODON_TO_AA.items():
        if aa != "*":
            fam[aa].append(codon)
    return {aa: sorted(items) for aa, items in fam.items()}


FAMILIES = sense_families()


def organism_codon_weights(records: list[dict[str, object]]) -> dict[str, dict[str, float]]:
    counts_by_aa: dict[str, Counter[str]] = defaultdict(Counter)
    for record in records:
        if record.get("is_heg"):
            continue
        for codon in codons(str(record.get("sequence_rna") or "")):
            aa = fetch_probe.CODON_TO_AA.get(codon)
            if aa and aa != "*":
                counts_by_aa[aa][codon] += 1
    weights: dict[str, dict[str, float]] = {}
    for aa, family in FAMILIES.items():
        denom = sum(counts_by_aa[aa].get(codon, 0) + 0.5 for codon in family)
        weights[aa] = {codon: (counts_by_aa[aa].get(codon, 0) + 0.5) / denom for codon in family}
    return weights


def gc_metrics(seq: str) -> tuple[float, float]:
    if not seq:
        return 0.0, 0.0
    gc = sum(1 for base in seq if base in "GC") / len(seq)
    cs = codons(seq)
    gc3 = sum(1 for codon in cs if codon[2] in "GC") / len(cs) if cs else 0.0
    return gc, gc3


def dinuc_freq(seq: str) -> dict[str, float]:
    counts = Counter(seq[i : i + 2] for i in range(0, len(seq) - 1))
    denom = max(1, len(seq) - 1)
    return {a + b: counts.get(a + b, 0) / denom for a in BASES for b in BASES}


def dinuc_distance(left: dict[str, float], right: dict[str, float]) -> float:
    return max(abs(left.get(key, 0.0) - right.get(key, 0.0)) for key in set(left) | set(right))


def weighted_choice(weights: dict[str, float], rng: random.Random) -> str:
    total = sum(weights.values())
    threshold = rng.random() * total
    acc = 0.0
    last = ""
    for key, weight in sorted(weights.items()):
        acc += weight
        last = key
        if acc >= threshold:
            return key
    return last


def synonymous_recoding(seq: str, weights: dict[str, dict[str, float]], rng: random.Random) -> str:
    out = []
    for codon in codons(seq):
        aa = fetch_probe.CODON_TO_AA.get(codon)
        if not aa or aa == "*" or len(FAMILIES.get(aa, [])) <= 1:
            out.append(codon)
        else:
            out.append(weighted_choice(weights[aa], rng))
    return "".join(out)


def mcmc_refine(seq: str, target_gc: float, target_gc3: float, target_dinuc: dict[str, float], rng: random.Random, max_steps: int = 180) -> str:
    if len(seq) > 1800:
        return seq
    current = seq
    current_gc, current_gc3 = gc_metrics(current)
    current_d = dinuc_distance(dinuc_freq(current), target_dinuc)
    current_loss = abs(current_gc - target_gc) + abs(current_gc3 - target_gc3) + 2.0 * current_d
    codon_list = codons(current)
    mutable = [i for i, codon in enumerate(codon_list) if len(FAMILIES.get(fetch_probe.CODON_TO_AA.get(codon, ""), [])) > 1]
    if not mutable:
        return current
    for _ in range(max_steps):
        if abs(current_gc - target_gc) <= 0.005 and abs(current_gc3 - target_gc3) <= 0.005 and current_d <= 0.012:
            break
        idx = rng.choice(mutable)
        old = codon_list[idx]
        aa = fetch_probe.CODON_TO_AA.get(old, "")
        choices = [codon for codon in FAMILIES.get(aa, []) if codon != old]
        if not choices:
            continue
        codon_list[idx] = rng.choice(choices)
        candidate = "".join(codon_list)
        cand_gc, cand_gc3 = gc_metrics(candidate)
        cand_d = dinuc_distance(dinuc_freq(candidate), target_dinuc)
        cand_loss = abs(cand_gc - target_gc) + abs(cand_gc3 - target_gc3) + 2.0 * cand_d
        accept = cand_loss <= current_loss or rng.random() < math.exp(min(0.0, (current_loss - cand_loss) * 60.0))
        if accept:
            current = candidate
            current_gc, current_gc3, current_d, current_loss = cand_gc, cand_gc3, cand_d, cand_loss
        else:
            codon_list[idx] = old
    return current


def constrained_recodings(seq: str, weights: dict[str, dict[str, float]], r: int, seed: str) -> tuple[list[str], dict[str, object]]:
    rng = random.Random(stable_seed(seed))
    target_gc, target_gc3 = gc_metrics(seq)
    target_dinuc = dinuc_freq(seq)
    accepted: list[str] = []
    attempts = 0
    relaxed = 0
    max_attempts = max(r * 12, r + 20)
    while len(accepted) < r and attempts < max_attempts:
        attempts += 1
        candidate = synonymous_recoding(seq, weights, rng)
        candidate = mcmc_refine(candidate, target_gc, target_gc3, target_dinuc, rng, max_steps=60 if len(seq) <= 900 else 20)
        cand_gc, cand_gc3 = gc_metrics(candidate)
        cand_d = dinuc_distance(dinuc_freq(candidate), target_dinuc)
        if abs(cand_gc - target_gc) <= 0.005 and abs(cand_gc3 - target_gc3) <= 0.005 and cand_d <= 0.012:
            accepted.append(candidate)
        elif attempts > r * 5 and abs(cand_gc - target_gc) <= 0.010 and abs(cand_gc3 - target_gc3) <= 0.010 and cand_d <= 0.020:
            relaxed += 1
            accepted.append(candidate)
    while len(accepted) < r:
        relaxed += 1
        accepted.append(synonymous_recoding(seq, weights, rng))
    return accepted, {"attempts": attempts, "relaxed_accepts": relaxed}


def exact_multiset_permutations(seq: str, r: int, seed: str) -> list[str]:
    rng = random.Random(stable_seed(seed))
    original = codons(seq)
    positions_by_aa: dict[str, list[int]] = defaultdict(list)
    codons_by_aa: dict[str, list[str]] = defaultdict(list)
    for idx, codon in enumerate(original):
        aa = fetch_probe.CODON_TO_AA.get(codon)
        if aa and aa != "*":
            positions_by_aa[aa].append(idx)
            codons_by_aa[aa].append(codon)
    out = []
    for _ in range(r):
        working = original[:]
        for aa, positions in positions_by_aa.items():
            values = codons_by_aa[aa][:]
            rng.shuffle(values)
            for pos, codon in zip(positions, values):
                working[pos] = codon
        out.append("".join(working))
    return out


def pick_gene_panel(organism: dict[str, object], seed: str) -> tuple[list[dict[str, object]], list[dict[str, object]], dict[str, object]]:
    rng = random.Random(stable_seed(seed))
    cds = [dict(row) for row in organism.get("cds_records", []) if isinstance(row, dict)]
    heg = [row for row in cds if row.get("is_heg")]
    bg = [row for row in cds if not row.get("is_heg")]
    heg = [row for row in heg if 150 <= int(row.get("length_nt", 0)) <= 1500]
    rng.shuffle(heg)
    n_heg = min(MAX_HEG_PER_ORGANISM, max(MIN_HEG_PER_ORGANISM, MAX_GENES_PER_ORGANISM // 2), len(heg))
    selected_heg = heg[:n_heg]
    selected_bg: list[dict[str, object]] = []
    used_bg: set[int] = set()
    for h in selected_heg:
        h_len = float(h.get("length_nt", 0))
        h_gc3 = float(h.get("gc3", 0.0))
        h_gc = float(h.get("gc", 0.0))
        h_strand = str(h.get("strand") or "+")
        best_idx = None
        best_score = 1.0e99
        for idx, b in enumerate(bg):
            if idx in used_bg:
                continue
            b_len = float(b.get("length_nt", 0))
            score = abs(math.log((b_len + 1) / (h_len + 1))) + 4.0 * abs(float(b.get("gc3", 0.0)) - h_gc3) + 2.0 * abs(float(b.get("gc", 0.0)) - h_gc)
            if str(b.get("strand") or "+") != h_strand:
                score += 0.20
            if score < best_score:
                best_idx = idx
                best_score = score
        if best_idx is not None:
            used_bg.add(best_idx)
            selected_bg.append(bg[best_idx])
    return selected_heg, selected_bg, {
        "n_heg_available": len(heg),
        "n_background_available": len(bg),
        "n_heg_selected": len(selected_heg),
        "n_background_selected": len(selected_bg),
    }


def random_seq_with_gc(length: int, gc_count: int, rng: random.Random) -> str:
    gc_count = max(0, min(length, gc_count))
    bases = [rng.choice("GC") for _ in range(gc_count)] + [rng.choice("AU") for _ in range(length - gc_count)]
    rng.shuffle(bases)
    return "".join(bases)


def random_seq_with_purine_g(length: int, purines: int, gs: int, rng: random.Random) -> str:
    gs = max(0, min(length, gs))
    purines = max(gs, min(length, purines))
    seq = ["G"] * gs
    seq.extend("A" for _ in range(purines - gs))
    seq.extend(rng.choice("UC") for _ in range(length - len(seq)))
    rng.shuffle(seq)
    return "".join(seq)


def random_g_rich(length: int, g_count: int, rng: random.Random) -> str:
    motifs = "GGAAGGAGGGAG"
    seq = [motifs[i % len(motifs)] for i in range(length)]
    while seq.count("G") > g_count:
        idxs = [i for i, base in enumerate(seq) if base == "G"]
        seq[rng.choice(idxs)] = rng.choice("AUC")
    while seq.count("G") < g_count:
        idxs = [i for i, base in enumerate(seq) if base != "G"]
        if not idxs:
            break
        seq[rng.choice(idxs)] = "G"
    shift = rng.randrange(length)
    return "".join(seq[shift:] + seq[:shift])


def carrier_stickiness(carrier: dict[str, object], sample_kmers: list[str]) -> float:
    table = score_table(carrier)
    return mean([table[kmer][0] for kmer in sample_kmers]) if sample_kmers else 0.0


def sample_internal_kmers(records: list[dict[str, object]], limit: int, seed: str) -> list[str]:
    rng = random.Random(stable_seed(seed))
    kmers = []
    for record in records:
        seq = str(record.get("sequence_rna") or "")
        internal = seq[45:-45] if len(seq) > 90 else seq
        for _ in range(min(8, max(1, len(internal) // 250))):
            k = rng.randint(5, 8)
            if len(internal) >= k:
                i = rng.randrange(0, len(internal) - k + 1)
                kmer = internal[i : i + k]
                if set(kmer) <= set(BASES):
                    kmers.append(kmer)
        if len(kmers) >= limit:
            break
    return kmers[:limit]


def decoy_carriers(tail20: str, heterologous_tails: list[str], records: list[dict[str, object]], n_decoys: int, seed: str) -> list[dict[str, object]]:
    rng = random.Random(stable_seed(seed))
    decoys: list[dict[str, object]] = []
    gc_count = sum(1 for base in tail20 if base in "GC")
    g_count = tail20.count("G")
    purines = sum(1 for base in tail20 if base in "AG")
    true_windows = set(carrier_windows_from_tail20(tail20))
    sample_kmers = sample_internal_kmers(records, 240, seed + ".stickiness")
    true_stickiness = carrier_stickiness(carrier_from_tail("true", "true", tail20), sample_kmers)

    def add(label: str, cls: str, seq: str) -> None:
        if len(decoys) >= n_decoys:
            return
        windows = carrier_windows_from_tail20(seq)
        if not windows:
            return
        decoys.append(carrier_from_windows(label, cls, windows))

    while len(decoys) < n_decoys and len([d for d in decoys if d["class"] == "same_gc"]) < max(1, min(4, n_decoys // 6)):
        add(f"gc_{len(decoys)}", "same_gc", random_seq_with_gc(20, gc_count, rng))
    while len(decoys) < n_decoys and len([d for d in decoys if d["class"] == "purine_g"]) < max(1, min(4, n_decoys // 6)):
        add(f"purine_g_{len(decoys)}", "purine_g", random_seq_with_purine_g(20, purines, g_count, rng))
    tries = 0
    while len(decoys) < n_decoys and len([d for d in decoys if d["class"] == "shuffle_tail"]) < max(1, min(4, n_decoys // 6)) and tries < 300:
        tries += 1
        chars = list(tail20)
        rng.shuffle(chars)
        seq = "".join(chars)
        windows = set(carrier_windows_from_tail20(seq))
        if windows & true_windows:
            continue
        if any(identity(w, t) >= (len(w) - 1) / len(w) for w in windows for t in true_windows if len(w) == len(t)):
            continue
        add(f"shuffle_{len(decoys)}", "shuffle_tail", seq)
    while len(decoys) < n_decoys and len([d for d in decoys if d["class"] == "g_rich"]) < max(1, min(4, n_decoys // 6)):
        add(f"g_rich_{len(decoys)}", "g_rich", random_g_rich(20, g_count, rng))
    tries = 0
    strength_target = max(0.02, true_stickiness)
    while len(decoys) < n_decoys and len([d for d in decoys if d["class"] == "pairing_strength_matched"]) < max(1, min(6, n_decoys // 5)) and tries < 600:
        tries += 1
        seq = random_seq_with_gc(20, gc_count, rng)
        candidate = carrier_from_tail(f"strength_{len(decoys)}", "pairing_strength_matched", seq)
        stick = carrier_stickiness(candidate, sample_kmers)
        if abs(stick - true_stickiness) <= max(0.04, 0.20 * strength_target):
            decoys.append(candidate)
    for other in heterologous_tails:
        if len(decoys) >= n_decoys:
            break
        if other != tail20:
            add(f"foreign_{len(decoys)}", "heterologous", other)
    while len(decoys) < n_decoys:
        add(f"fill_{len(decoys)}", "same_gc", random_seq_with_gc(20, gc_count, rng))
    return decoys[:n_decoys]


def canonical_decoys(n_decoys: int, seed: str) -> list[dict[str, object]]:
    rng = random.Random(stable_seed(seed))
    gc_count = sum(1 for b in CANONICAL_ASD if b in "GC")
    purines = sum(1 for b in CANONICAL_ASD if b in "AG")
    g_count = CANONICAL_ASD.count("G")
    out = []
    for idx in range(n_decoys):
        if idx % 3 == 0:
            seq = random_seq_with_gc(len(CANONICAL_ASD), gc_count, rng)
        elif idx % 3 == 1:
            seq = random_seq_with_purine_g(len(CANONICAL_ASD), purines, g_count, rng)
        else:
            chars = list(CANONICAL_ASD)
            rng.shuffle(chars)
            seq = "".join(chars)
        out.append(carrier_from_windows(f"canonical_decoy_{idx}", "canonical_own_decoy", [seq]))
    return out


def z_for_burdens(obs: float, nulls: list[float]) -> float:
    mu = mean(nulls)
    sigma = sd(nulls)
    if sigma <= EPS:
        return 0.0
    return (obs - mu) / sigma


def evaluate_carrier_for_gene(seq: str, recodings: list[str], table: dict[str, tuple[float, int]]) -> tuple[float, list[float], float, float, float]:
    return evaluate_carrier_for_profiles(kmer_profile(seq), [kmer_profile(candidate) for candidate in recodings], table)


def evaluate_carrier_for_profiles(obs_profile: dict[str, object], null_profiles: list[dict[str, object]], table: dict[str, tuple[float, int]]) -> tuple[float, list[float], float, float, float]:
    obs_metrics = burden_from_profile(obs_profile, table)
    obs = obs_metrics["shadow"]
    nulls = [burden_from_profile(candidate, table)["shadow"] for candidate in null_profiles]
    return z_for_burdens(obs, nulls), nulls, obs_metrics["strong_count"], obs_metrics["max_shadow"], obs_metrics["n_windows"]


def d_stat_for_carrier(gene_rows: list[dict[str, object]], label: str) -> tuple[float | None, float | None, float | None]:
    heg_pairs = []
    bg_pairs = []
    for row in gene_rows:
        z = row.get(f"z_{label}")
        if not isinstance(z, (int, float)) or not math.isfinite(float(z)):
            continue
        pair = (float(z), float(row.get("length_nt") or 1.0))
        if row.get("class") == "HEG":
            heg_pairs.append(pair)
        else:
            bg_pairs.append(pair)
    z_heg = weighted_median(heg_pairs)
    z_bg = weighted_median(bg_pairs)
    if z_heg is None or z_bg is None:
        return None, z_heg, z_bg
    return z_heg - z_bg, z_heg, z_bg


def analyze_organism(organism: dict[str, object], heterologous_tails: list[str], seed: str) -> dict[str, object]:
    tail20, tail_meta = consensus_terminal20([row for row in organism.get("rrna_records", []) if isinstance(row, dict)])
    if tail20 is None:
        return {"ok": False, "drop_reason": tail_meta.get("drop_reason") or "carrier_unavailable"}
    heg, bg, panel_meta = pick_gene_panel(organism, seed + ".panel")
    if len(heg) < MIN_HEG_PER_ORGANISM or len(bg) < MIN_HEG_PER_ORGANISM:
        return {"ok": False, "drop_reason": "insufficient_matched_gene_panel", "panel_meta": panel_meta}
    records = heg + bg
    weights = organism_codon_weights([row for row in organism.get("cds_records", []) if isinstance(row, dict)])
    true_carrier = carrier_from_tail("true", "own_tail", tail20)
    decoys = decoy_carriers(tail20, heterologous_tails, records, N_DECOYS, seed + ".decoys")
    carriers = [true_carrier] + decoys
    tables = {str(carrier["label"]): score_table(carrier) for carrier in carriers}

    gene_rows: list[dict[str, object]] = []
    gene_profile_rows: list[dict[str, object]] = []
    recoding_meta = Counter()
    for idx, record in enumerate(records):
        seq = str(record.get("sequence_rna") or "")
        recodings, meta = constrained_recodings(seq, weights, R_NULL, f"{seed}.gene.{idx}.recoding")
        obs_profile = kmer_profile(seq)
        null_profiles = [kmer_profile(candidate) for candidate in recodings]
        recoding_meta["attempts"] += int(meta.get("attempts", 0))
        recoding_meta["relaxed_accepts"] += int(meta.get("relaxed_accepts", 0))
        row: dict[str, object] = {
            "class": "HEG" if idx < len(heg) else "BG",
            "length_nt": int(record.get("length_nt", 0)),
            "gc": float(record.get("gc", 0.0)),
            "gc3": float(record.get("gc3", 0.0)),
            "strand": record.get("strand") or "+",
            "product": str(record.get("product") or "")[:120],
        }
        for carrier in carriers:
            label = str(carrier["label"])
            z, _, strong, max_shadow, n_windows = evaluate_carrier_for_profiles(obs_profile, null_profiles, tables[label])
            row[f"z_{label}"] = z
            if label == "true":
                row["strong_count_true"] = strong
                row["max_shadow_true"] = max_shadow
                row["n_windows"] = n_windows
        exact = exact_multiset_permutations(seq, max(20, min(60, R_NULL // 2)), f"{seed}.gene.{idx}.exact")
        z_exact, _, _, _, _ = evaluate_carrier_for_profiles(obs_profile, [kmer_profile(candidate) for candidate in exact], tables["true"])
        row["z_exact_multiset"] = z_exact
        gene_rows.append(row)
        gene_profile_rows.append({"class": row["class"], "length_nt": row["length_nt"], "obs_profile": obs_profile, "null_profiles": null_profiles})

    d_true, z_heg, z_bg = d_stat_for_carrier(gene_rows, "true")
    decoy_ds = []
    decoy_by_class: dict[str, list[float]] = defaultdict(list)
    for decoy in decoys:
        label = str(decoy["label"])
        d, _, _ = d_stat_for_carrier(gene_rows, label)
        if d is not None:
            decoy_ds.append(d)
            decoy_by_class[str(decoy.get("class"))].append(d)
    rank = rank_percentile(float(d_true), decoy_ds) if d_true is not None else None

    canonical = carrier_from_windows("canonical", "canonical_asd", [CANONICAL_ASD])
    canonical_decoy_list = canonical_decoys(max(12, min(N_DECOYS, 24)), seed + ".canonical")
    own_tail_decoys = decoy_carriers(tail20, [], records, max(12, min(N_DECOYS, 24)), seed + ".own_tail_for_gate")
    gate_carriers = [canonical] + canonical_decoy_list + own_tail_decoys
    gate_tables = {str(carrier["label"]): score_table(carrier) for carrier in gate_carriers}
    gate_rows: list[dict[str, object]] = []
    for profile_row in gene_profile_rows:
        row = {"class": profile_row["class"], "length_nt": profile_row["length_nt"]}
        obs_profile = profile_row["obs_profile"]
        null_profiles = profile_row["null_profiles"]
        assert isinstance(obs_profile, dict)
        assert isinstance(null_profiles, list)
        for carrier in gate_carriers:
            label = str(carrier["label"])
            z, _, _, _, _ = evaluate_carrier_for_profiles(obs_profile, null_profiles, gate_tables[label])
            row[f"z_{label}"] = z
        gate_rows.append(row)
    d_canonical, _, _ = d_stat_for_carrier(gate_rows, "canonical")
    canonical_decoy_ds = [d_stat_for_carrier(gate_rows, str(c["label"]))[0] for c in canonical_decoy_list]
    own_tail_decoy_ds = [d_stat_for_carrier(gate_rows, str(c["label"]))[0] for c in own_tail_decoys]
    canonical_decoy_ds = [float(v) for v in canonical_decoy_ds if isinstance(v, (int, float))]
    own_tail_decoy_ds = [float(v) for v in own_tail_decoy_ds if isinstance(v, (int, float))]
    true_own_rank = rank_percentile(float(d_true), own_tail_decoy_ds) if d_true is not None else None
    canonical_own_rank = rank_percentile(float(d_canonical), canonical_decoy_ds) if d_canonical is not None else None
    gate_n2_c = (true_own_rank - canonical_own_rank) if true_own_rank is not None and canonical_own_rank is not None else None

    exact_heg = weighted_median([(float(row["z_exact_multiset"]), float(row["length_nt"])) for row in gene_rows if row["class"] == "HEG"])
    exact_bg = weighted_median([(float(row["z_exact_multiset"]), float(row["length_nt"])) for row in gene_rows if row["class"] == "BG"])
    exact_d = (exact_heg - exact_bg) if exact_heg is not None and exact_bg is not None else None
    strong_heg = [float(row.get("strong_count_true", 0.0)) for row in gene_rows if row["class"] == "HEG"]
    strong_bg = [float(row.get("strong_count_true", 0.0)) for row in gene_rows if row["class"] == "BG"]

    kmer_table_size = sum(len(table) for table in tables.values())
    return {
        "ok": True,
        "assembly_accession": organism.get("assembly_accession"),
        "organism": organism.get("organism"),
        "domain": organism.get("domain"),
        "genus": organism.get("genus"),
        "family": organism.get("family"),
        "order": organism.get("order"),
        "source": organism.get("source"),
        "tail20": tail20,
        "tail_meta": tail_meta,
        "n_16s_rrna": len(organism.get("rrna_records", [])),
        "n_cds": len(organism.get("cds_records", [])),
        "n_heg_available": panel_meta["n_heg_available"],
        "n_heg": len(heg),
        "n_background": len(bg),
        "z_heg": z_heg,
        "z_background": z_bg,
        "d_true": d_true,
        "rank": rank,
        "decoy_d_median": median(decoy_ds),
        "decoy_d_by_class": {key: round_float(median(vals)) for key, vals in sorted(decoy_by_class.items())},
        "gate_n2_c": gate_n2_c,
        "gate_n2_true_own_rank": true_own_rank,
        "gate_n2_canonical_own_rank": canonical_own_rank,
        "d_canonical": d_canonical,
        "null3_exact_multiset_d": exact_d,
        "null3_exact_multiset_z_heg": exact_heg,
        "null3_exact_multiset_z_background": exact_bg,
        "strong_count_heg_median": median(strong_heg),
        "strong_count_background_median": median(strong_bg),
        "max_shadow_heg_median": median([float(row.get("max_shadow_true", 0.0)) for row in gene_rows if row["class"] == "HEG"]),
        "max_shadow_background_median": median([float(row.get("max_shadow_true", 0.0)) for row in gene_rows if row["class"] == "BG"]),
        "kmer_table_size": kmer_table_size,
        "recoding_meta": dict(recoding_meta),
        "gene_rows": gene_rows,
    }


def summarize(rows: list[dict[str, object]], fetch_meta: dict[str, object], elapsed: float) -> dict[str, object]:
    ok_rows = [row for row in rows if row.get("ok")]
    bacteria = [row for row in ok_rows if row.get("domain") == "Bacteria"]
    archaea = [row for row in ok_rows if row.get("domain") == "Archaea"]
    primary = bacteria
    d_values = [float(row["d_true"]) for row in primary if isinstance(row.get("d_true"), (int, float))]
    rank_pairs = [(float(row["rank"]), str(row.get("family") or row.get("genus") or "unknown")) for row in primary if isinstance(row.get("rank"), (int, float))]
    ranks = [value for value, _ in rank_pairs]
    z_heg = [float(row["z_heg"]) for row in primary if isinstance(row.get("z_heg"), (int, float))]
    gate_pairs = [(float(row["gate_n2_c"]), str(row.get("family") or row.get("genus") or "unknown")) for row in primary if isinstance(row.get("gate_n2_c"), (int, float))]
    gate_c = [value for value, _ in gate_pairs]
    exact_d = [float(row["null3_exact_multiset_d"]) for row in primary if isinstance(row.get("null3_exact_multiset_d"), (int, float))]
    families = sorted(set(str(row.get("family") or row.get("genus") or "unknown") for row in primary))
    orders = [str(row.get("order") or row.get("family") or row.get("genus") or "unknown") for row in primary]
    family_blocks = [str(row.get("family") or row.get("genus") or "unknown") for row in primary]
    d_boot = bootstrap_ci(d_values, family_blocks, N_BOOTSTRAP, EXPERIMENT_ID + ".d.family")
    order_boot = bootstrap_ci(d_values, orders, N_BOOTSTRAP, EXPERIMENT_ID + ".d.order")
    rank_shift = [value - 0.5 for value in ranks]
    rank_boot = bootstrap_ci(rank_shift, [block for _, block in rank_pairs], N_BOOTSTRAP, EXPERIMENT_ID + ".rank.family")
    gate_boot = bootstrap_ci(gate_c, [block for _, block in gate_pairs], N_BOOTSTRAP, EXPERIMENT_ID + ".gate.family")

    data_gate = len(primary) >= MIN_CERT_ORGANISMS and len(families) >= MIN_CERT_FAMILIES
    directional = bool(d_values) and (median(d_values) or 0.0) < 0.0
    rank_special = bool(ranks) and (median(ranks) or 1.0) < 0.10
    gate_specific = bool(gate_c) and (median(gate_c) or 1.0) < 0.0
    p_d = d_boot.get("p_directional")
    p_rank = rank_boot.get("p_directional")
    certified_gates = data_gate and directional and rank_special and gate_specific and isinstance(p_d, float) and p_d <= 0.01 and isinstance(p_rank, float) and p_rank <= 0.01
    if certified_gates:
        verdict = "certified"
    elif not d_values or len(primary) < 5:
        verdict = "needs_external"
    elif (median(d_values) or 0.0) >= -0.05:
        verdict = "refuted"
    elif ranks and (median(ranks) or 0.0) >= 0.25:
        verdict = "coincidence"
    else:
        verdict = "needs_external"
    if not data_gate:
        verdict = "needs_external"

    compact_rows = []
    for row in ok_rows:
        compact_rows.append(
            {
                "assembly_accession": row.get("assembly_accession"),
                "organism": row.get("organism"),
                "domain": row.get("domain"),
                "genus": row.get("genus"),
                "family": row.get("family"),
                "order": row.get("order"),
                "n_16s_rrna": row.get("n_16s_rrna"),
                "n_cds": row.get("n_cds"),
                "n_heg": row.get("n_heg"),
                "n_background": row.get("n_background"),
                "z_heg": round_float(row.get("z_heg")),
                "z_background": round_float(row.get("z_background")),
                "d_true": round_float(row.get("d_true")),
                "rank": round_float(row.get("rank")),
                "gate_n2_c": round_float(row.get("gate_n2_c")),
                "null3_exact_multiset_d": round_float(row.get("null3_exact_multiset_d")),
                "decoy_d_median": round_float(row.get("decoy_d_median")),
                "decoy_d_by_class": row.get("decoy_d_by_class"),
                "strong_count_heg_median": round_float(row.get("strong_count_heg_median")),
                "strong_count_background_median": round_float(row.get("strong_count_background_median")),
                "kmer_table_size": row.get("kmer_table_size"),
            }
        )

    return {
        "verdict": verdict,
        "scope_note": SCOPE_NOTE,
        "data_gate": {
            "passed": data_gate,
            "required_organisms": MIN_CERT_ORGANISMS,
            "required_families": MIN_CERT_FAMILIES,
            "actual_primary_bacteria": len(primary),
            "actual_families": len(families),
        },
        "n_organisms": len(ok_rows),
        "n_primary_bacteria": len(primary),
        "n_archaea": len(archaea),
        "n_families": len(families),
        "n_orders": len(set(orders)),
        "fetch_success_rate": fetch_meta.get("fetch_success_rate"),
        "fetch_attempts": fetch_meta.get("n_attempts"),
        "median_z_heg": round_float(median(z_heg)),
        "median_d": round_float(median(d_values)),
        "median_rank": round_float(median(ranks)),
        "median_gate_n2_c": round_float(median(gate_c)),
        "median_null3_exact_multiset_d": round_float(median(exact_d)),
        "block_stats": {
            "family_d": d_boot,
            "order_d": order_boot,
            "family_rank_shift": rank_boot,
            "family_gate_n2_c": gate_boot,
        },
        "archaea_specificity": {
            "n_archaea": len(archaea),
            "median_d": round_float(median([float(row["d_true"]) for row in archaea if isinstance(row.get("d_true"), (int, float))])),
            "median_rank": round_float(median([float(row["rank"]) for row in archaea if isinstance(row.get("rank"), (int, float))])),
        },
        "parameters": {
            "target_bacteria": TARGET_BACTERIA,
            "target_archaea": TARGET_ARCHAEA,
            "max_fetch_attempts": MAX_FETCH_ATTEMPTS,
            "analysis_organism_limit": ANALYSIS_ORGANISM_LIMIT,
            "r_null": R_NULL,
            "n_decoys": N_DECOYS,
            "n_bootstrap": N_BOOTSTRAP,
            "max_genes_per_organism": MAX_GENES_PER_ORGANISM,
            "requested_design": {
                "target_bacteria": 50,
                "target_archaea": 10,
                "r_null": REQUESTED_R_NULL,
                "n_decoys": REQUESTED_N_DECOYS,
                "max_genes_per_organism": REQUESTED_MAX_GENES_PER_ORGANISM,
                "note": "Set ASD_NULL_R=150 ASD_N_DECOYS=40 ASD_MAX_GENES_PER_ORGANISM=60 and raise ASD_ANALYSIS_ORGANISM_LIMIT for the full pilot run.",
            },
            "lambda": LAMBDA,
            "numpy_free": True,
            "biopython_free": True,
        },
        "timing_seconds": round_float(elapsed, 6),
        "fetch_meta": fetch_meta,
        "per_organism": compact_rows,
        "drops": [row for row in rows if not row.get("ok")],
    }


def main() -> None:
    start = time.monotonic()
    organisms, fetch_meta = fetch_probe.fetch_panel(
        target_bacteria=TARGET_BACTERIA,
        target_archaea=TARGET_ARCHAEA,
        max_attempts=MAX_FETCH_ATTEMPTS,
        deadline_seconds=FETCH_DEADLINE_SECONDS,
    )
    tail_pairs = []
    for organism in organisms[:ANALYSIS_ORGANISM_LIMIT]:
        tail, _ = consensus_terminal20([row for row in organism.get("rrna_records", []) if isinstance(row, dict)])
        if tail:
            tail_pairs.append((str(organism.get("assembly_accession")), tail))
    rows: list[dict[str, object]] = []
    for organism in organisms:
        accession = str(organism.get("assembly_accession") or "")
        heterologous = [tail for other, tail in tail_pairs if other != accession]
        try:
            row = analyze_organism(organism, heterologous, EXPERIMENT_ID + "." + accession)
        except Exception as exc:
            row = {
                "ok": False,
                "assembly_accession": accession,
                "organism": organism.get("organism"),
                "domain": organism.get("domain"),
                "drop_reason": f"analysis_error:{type(exc).__name__}:{exc}",
            }
        rows.append(row)
    elapsed = time.monotonic() - start
    summary = summarize(rows, fetch_meta, elapsed)
    emit(str(summary["verdict"]), **{k: v for k, v in summary.items() if k != "verdict"})


if __name__ == "__main__":
    main()

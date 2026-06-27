#!/usr/bin/env python3
"""Run the RM motif escape full-signal exploratory experiment."""
from __future__ import annotations

from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
import json
import math
import os
import random
import re
import statistics
import sys
import time
from typing import Any

try:
    from ._asd_fetch_probe import (
        CODON_TO_AA,
        cached_assembly_file,
        intact_cds_sequence,
        parse_fasta_records,
        parse_features,
        parse_gff_attributes,
        parse_location,
        parse_origin,
        product_text,
        reverse_complement_dna,
        sequence_from_segments,
    )
    from ._rm_fetch_probe import (
        IUPAC_DEGENERACY,
        assembly_accession_core,
        carrier_rows_by_host,
        canonical_motif,
        genbank_summary_for_accession,
        host_inventory_map,
        load_blow_carriers,
        load_flinders_host_prophage_rows,
        load_rebase_carriers,
        map_carriers_to_assemblies,
        motif_degeneracy,
        parse_fasta_full,
        plasmid_target_inventory,
        prophage_inventory_for_host,
        prophage_target_inventory,
        reverse_complement_motif,
        tier_a_blow_groups,
        tier_a_rebase_groups,
    )
except ImportError:  # pragma: no cover - direct script execution
    from _asd_fetch_probe import (  # type: ignore
        CODON_TO_AA,
        cached_assembly_file,
        intact_cds_sequence,
        parse_fasta_records,
        parse_features,
        parse_gff_attributes,
        parse_location,
        parse_origin,
        product_text,
        reverse_complement_dna,
        sequence_from_segments,
    )
    from _rm_fetch_probe import (  # type: ignore
        IUPAC_DEGENERACY,
        assembly_accession_core,
        carrier_rows_by_host,
        canonical_motif,
        genbank_summary_for_accession,
        host_inventory_map,
        load_blow_carriers,
        load_flinders_host_prophage_rows,
        load_rebase_carriers,
        map_carriers_to_assemblies,
        motif_degeneracy,
        parse_fasta_full,
        plasmid_target_inventory,
        prophage_inventory_for_host,
        prophage_target_inventory,
        reverse_complement_motif,
        tier_a_blow_groups,
        tier_a_rebase_groups,
    )


EXPERIMENT_ID = "RM_motif_escape_full_signal_exploratory"
CLAIM = "Claim 69"
DEFAULT_NULL_N = 200
DEFAULT_DECOY_K = 200
DEFAULT_BOOTSTRAP_N = 2000
MIN_PRIMARY_HOSTS = 80
SUPPORT_MEDIAN_D_MAX = -0.15
SUPPORT_MEDIAN_RANK_MAX = 0.40
SUPPORT_RANK_SHIFT_MIN = 0.10
SUPPORT_BOOTSTRAP_P_MAX = 0.01
REFUTED_POWER_HOSTS = 80
EPS = 1e-12

IUPAC_BASES = {
    "A": frozenset("A"),
    "C": frozenset("C"),
    "G": frozenset("G"),
    "T": frozenset("T"),
    "R": frozenset("AG"),
    "Y": frozenset("CT"),
    "S": frozenset("CG"),
    "W": frozenset("AT"),
    "K": frozenset("GT"),
    "M": frozenset("AC"),
    "B": frozenset("CGT"),
    "D": frozenset("AGT"),
    "H": frozenset("ACT"),
    "V": frozenset("ACG"),
    "N": frozenset("ACGT"),
}
DNA_BASES = set("ACGT")
STOP_CODONS_DNA = {codon.replace("U", "T") for codon, aa in CODON_TO_AA.items() if aa == "*"}
CODON_TO_AA_DNA = {codon.replace("U", "T"): aa for codon, aa in CODON_TO_AA.items()}


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def stable_seed(text: str) -> int:
    return int.from_bytes(hashlib.sha256(text.encode("utf-8")).digest()[:8], "big")


def round_float(value: float | None, digits: int = 6) -> float | None:
    if value is None or not math.isfinite(value):
        return None
    return round(float(value), digits)


def percentile(values: list[float], q: float) -> float | None:
    clean = sorted(v for v in values if math.isfinite(v))
    if not clean:
        return None
    if len(clean) == 1:
        return clean[0]
    pos = q * (len(clean) - 1)
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return clean[lo]
    return clean[lo] * (hi - pos) + clean[hi] * (pos - lo)


def median(values: list[float]) -> float | None:
    clean = [v for v in values if math.isfinite(v)]
    return float(statistics.median(clean)) if clean else None


def weighted_median(pairs: list[tuple[float, float]]) -> float | None:
    clean = [(float(value), float(weight)) for value, weight in pairs if math.isfinite(value) and weight > 0]
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


def family_weighted_median(rows: list[dict[str, Any]], key: str) -> float | None:
    by_family: dict[str, list[float]] = defaultdict(list)
    for row in rows:
        value = row.get(key)
        if isinstance(value, (int, float)) and math.isfinite(float(value)):
            by_family[str(row.get("gtdb_family") or "unknown")].append(float(value))
    pairs = []
    for values in by_family.values():
        fam_median = median(values)
        if fam_median is not None:
            pairs.append((fam_median, 1.0))
    return weighted_median(pairs)


def family_block_bootstrap_rank_shift(rows: list[dict[str, Any]], n_bootstrap: int, seed: str) -> dict[str, Any]:
    by_family: dict[str, list[float]] = defaultdict(list)
    for row in rows:
        rank = row.get("carrier_rank")
        if isinstance(rank, (int, float)) and math.isfinite(float(rank)):
            by_family[str(row.get("gtdb_family") or "unknown")].append(float(rank))
    keys = sorted(by_family)
    if not keys:
        return {"observed": None, "p_one_sided_rank_shift_positive": None, "ci95": [None, None], "n_blocks": 0}
    observed_median_rank = statistics.median(statistics.median(by_family[key]) for key in keys)
    observed_shift = 0.5 - observed_median_rank
    rng = random.Random(stable_seed(seed))
    boots = []
    for _ in range(max(10, n_bootstrap)):
        sampled = [rng.choice(keys) for _ in keys]
        med_rank = statistics.median(statistics.median(by_family[key]) for key in sampled)
        boots.append(0.5 - med_rank)
    reverse = sum(1 for value in boots if value <= 0.0)
    return {
        "observed": round_float(observed_shift),
        "observed_median_rank": round_float(observed_median_rank),
        "p_one_sided_rank_shift_positive": round_float((1 + reverse) / (1 + len(boots))),
        "ci95": [round_float(percentile(boots, 0.025)), round_float(percentile(boots, 0.975))],
        "n_blocks": len(keys),
        "n_bootstrap": max(10, n_bootstrap),
    }


def motif_profile(row: dict[str, Any]) -> tuple[int, int, bool]:
    motif = str(row.get("motif_canonical") or "")
    return (
        int(row.get("motif_len") or len(motif)),
        int(row.get("degeneracy") or motif_degeneracy(motif)),
        bool(row.get("palindrome_flag")),
    )


def unique_motifs(rows: list[dict[str, Any]]) -> list[str]:
    motifs = sorted({str(row.get("motif_canonical") or "") for row in rows if row.get("motif_canonical")})
    return [motif for motif in motifs if motif and all(ch in IUPAC_BASES for ch in motif)]


def motif_matches(seq: str, start: int, motif: str) -> bool:
    if start + len(motif) > len(seq):
        return False
    for offset, ch in enumerate(motif):
        if seq[start + offset] not in IUPAC_BASES[ch]:
            return False
    return True


def count_one_orientation(seq: str, motif: str) -> int:
    if len(seq) < len(motif):
        return 0
    return sum(1 for i in range(0, len(seq) - len(motif) + 1) if motif_matches(seq, i, motif))


def count_motif(seq: str, motif: str) -> int:
    clean = re.sub(r"[^ACGT]", "", seq.upper())
    if not clean or not motif:
        return 0
    rc = reverse_complement_motif(motif)
    count = count_one_orientation(clean, motif)
    if rc != motif:
        count += count_one_orientation(clean, rc)
    return count


def count_motif_set(seqs: list[str], motifs: list[str]) -> int:
    if not seqs or not motifs:
        return 0
    total = 0
    for seq in seqs:
        clean = re.sub(r"[^ACGT]", "", seq.upper())
        if clean:
            total += sum(count_motif(clean, motif) for motif in motifs)
    return total


def log2_depletion(observed: float, expected: float) -> float:
    return math.log2((observed + 1.0) / (expected + 1.0))


def de_bruijn_shuffle(seq: str, k: int, rng: random.Random) -> str:
    clean = re.sub(r"[^ACGT]", "", seq.upper())
    if len(clean) <= k:
        return clean
    edges: dict[str, list[str]] = defaultdict(list)
    start = clean[: k - 1]
    for i in range(0, len(clean) - k + 1):
        left = clean[i : i + k - 1]
        right = clean[i + 1 : i + k]
        edges[left].append(right)
    for values in edges.values():
        rng.shuffle(values)
    stack = [start]
    path: list[str] = []
    while stack:
        current = stack[-1]
        choices = edges.get(current)
        if choices:
            stack.append(choices.pop())
        else:
            path.append(stack.pop())
    path.reverse()
    if not path:
        return clean
    shuffled = path[0] + "".join(node[-1] for node in path[1:])
    return shuffled if len(shuffled) == len(clean) else fallback_kmer_shuffle(clean, k, rng)


def fallback_kmer_shuffle(seq: str, k: int, rng: random.Random) -> str:
    if len(seq) <= k:
        return seq
    prefix = seq[: k - 1]
    suffixes = [seq[i + k - 1] for i in range(0, len(seq) - k + 1)]
    rng.shuffle(suffixes)
    return prefix + "".join(suffixes)


def null_a_sequence(seq: str, rng: random.Random) -> str:
    return de_bruijn_shuffle(seq, 3, rng)


def synonym_shuffle_cds(seq: str, rng: random.Random) -> str | None:
    clean = re.sub(r"[^ACGT]", "", seq.upper())
    intact, _reason = intact_cds_sequence(clean)
    if intact is None or len(intact) < 3:
        return None
    codons = [intact[i : i + 3] for i in range(0, len(intact), 3)]
    by_aa: dict[str, list[str]] = defaultdict(list)
    positions = []
    for idx, codon in enumerate(codons):
        aa = CODON_TO_AA_DNA.get(codon)
        if aa is None or aa == "*":
            return None
        by_aa[aa].append(codon)
        positions.append((idx, aa))
    for aa, values in by_aa.items():
        rng.shuffle(values)
        by_aa[aa] = values
    out = list(codons)
    cursor: Counter[str] = Counter()
    for idx, aa in positions:
        out[idx] = by_aa[aa][cursor[aa]]
        cursor[aa] += 1
    return "".join(out)


def parse_gff_cds_records(gff_text: str, fna_text: str) -> tuple[list[dict[str, Any]], dict[str, str], dict[str, Any]]:
    contigs = parse_fasta_records(fna_text)
    records: list[dict[str, Any]] = []
    skipped: Counter[str] = Counter()
    for line in gff_text.splitlines():
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) < 9:
            continue
        seqid, _source, feature, start_s, end_s, _score, strand, _phase, attr_raw = fields[:9]
        if feature != "CDS":
            continue
        seq = contigs.get(seqid)
        if not seq:
            skipped["missing_contig"] += 1
            continue
        try:
            start0 = int(start_s) - 1
            end = int(end_s)
        except ValueError:
            skipped["bad_coordinate"] += 1
            continue
        if start0 < 0 or end <= start0 or end > len(seq):
            skipped["coordinate_out_of_bounds"] += 1
            continue
        attrs = parse_gff_attributes(attr_raw)
        prod = " ".join(str(attrs.get(key, "")) for key in ("product", "Name", "gene", "Note"))
        if "pseudo" in attrs or "pseudogene" in prod.lower():
            skipped["pseudo"] += 1
            continue
        piece = seq[start0:end].upper()
        if strand == "-":
            piece = reverse_complement_dna(piece)
        intact, reason = intact_cds_sequence(piece)
        if intact is None:
            skipped[str(reason)] += 1
            continue
        records.append(
            {
                "seqid": seqid,
                "start": start0,
                "end": end,
                "strand": strand if strand in {"+", "-"} else "+",
                "sequence": intact,
            }
        )
    return records, contigs, {"source_parser": "genomic.gff", "skipped": dict(skipped), "n_contigs": len(contigs)}


def parse_gbff_cds_records(gbff_text: str) -> tuple[list[dict[str, Any]], dict[str, str], dict[str, Any]]:
    lines = gbff_text.splitlines()
    genome = parse_origin(lines)
    features = parse_features(lines)
    records: list[dict[str, Any]] = []
    skipped: Counter[str] = Counter()
    for feature in features:
        if str(feature.get("key") or "") != "CDS":
            continue
        qualifiers = feature.get("qualifiers")
        if not isinstance(qualifiers, dict):
            continue
        prod = product_text(qualifiers)
        if "pseudo" in qualifiers or "pseudogene" in prod.lower():
            skipped["pseudo"] += 1
            continue
        loc = parse_location(str(feature.get("location") or ""))
        if loc is None:
            skipped["bad_location"] += 1
            continue
        strand, segments = loc
        seq_dna = sequence_from_segments(genome, strand, segments)
        intact, reason = intact_cds_sequence(seq_dna)
        if intact is None:
            skipped[str(reason)] += 1
            continue
        records.append(
            {
                "seqid": "gbff",
                "start": min(a for a, _ in segments),
                "end": max(b for _, b in segments),
                "strand": strand,
                "sequence": intact,
            }
        )
    return records, {"gbff": genome}, {"source_parser": "genomic.gbff", "skipped": dict(skipped), "n_contigs": 1}


def intervals_overlap(a0: int, a1: int, b0: int, b1: int) -> bool:
    return a0 < b1 and b0 < a1


def extract_regions_from_contigs(
    contigs: dict[str, str],
    regions: list[dict[str, Any]],
) -> tuple[list[dict[str, Any]], Counter[str]]:
    targets: list[dict[str, Any]] = []
    errors: Counter[str] = Counter()
    for region in regions:
        contig = str(region.get("contig") or "")
        seq = contigs.get(contig)
        if seq is None:
            errors["contig_not_found"] += 1
            continue
        start0 = int(region.get("start") or 0) - 1
        stop = int(region.get("stop") or 0)
        if start0 < 0 or stop <= start0 or stop > len(seq):
            errors["coordinate_out_of_bounds"] += 1
            continue
        subseq = re.sub(r"[^ACGT]", "", seq[start0:stop].upper())
        if not subseq:
            errors["empty_sequence"] += 1
            continue
        targets.append({"contig": contig, "start": start0, "end": stop, "sequence": subseq})
    return targets, errors


def non_prophage_windows(contigs: dict[str, str], regions: list[dict[str, Any]], target_bp: int, seed: str) -> list[str]:
    by_contig: dict[str, list[tuple[int, int]]] = defaultdict(list)
    for region in regions:
        contig = str(region.get("contig") or "")
        start0 = int(region.get("start") or 0) - 1
        stop = int(region.get("stop") or 0)
        if contig and start0 >= 0 and stop > start0:
            by_contig[contig].append((start0, stop))
    rng = random.Random(stable_seed(seed))
    pieces: list[str] = []
    remaining = target_bp
    candidates = []
    for contig, seq in contigs.items():
        clean = re.sub(r"[^ACGT]", "N", seq.upper())
        blocked = sorted(by_contig.get(contig, []))
        cursor = 0
        for start, end in blocked + [(len(clean), len(clean))]:
            if start - cursor >= 1000:
                candidates.append((contig, cursor, start))
            cursor = max(cursor, end)
    rng.shuffle(candidates)
    for contig, start, end in candidates:
        if remaining <= 0:
            break
        seq = contigs[contig][start:end].upper()
        if len(seq) > remaining:
            max_start = len(seq) - remaining
            offset = rng.randrange(max_start + 1) if max_start > 0 else 0
            seq = seq[offset : offset + remaining]
        seq = re.sub(r"[^ACGT]", "", seq)
        if seq:
            pieces.append(seq)
            remaining -= len(seq)
    return pieces


def load_host_sequence_context(
    host: str,
    ftp_path: str,
    regions: list[dict[str, Any]],
    deadline: float | None,
) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    flinders_ids = sorted({str(region.get("flinders_genomeid") or "") for region in regions if region.get("flinders_genomeid")})
    fetch_accession = host
    fetch_ftp_path = ftp_path
    fetch_mode = "mapped_host_assembly"
    gb_lookup: dict[str, Any] = {"skipped": True}
    if flinders_ids:
        gb_row, gb_contact = genbank_summary_for_accession(flinders_ids[0], deadline=deadline)
        gb_lookup = gb_contact
        if gb_row and gb_row.get("ftp_path"):
            fetch_accession = flinders_ids[0]
            fetch_ftp_path = str(gb_row["ftp_path"])
            fetch_mode = "flinders_genbank_assembly"
    fna_text, fna_contact = cached_assembly_file(fetch_ftp_path, "genomic.fna.gz", fetch_accession, deadline=deadline)
    if not fna_text:
        return None, {"error": "genomic_fna_fetch_failed", "fna": fna_contact, "genbank_lookup": gb_lookup}
    contigs = {header.split()[0]: seq.upper() for header, seq in parse_fasta_full(fna_text)}
    targets, errors = extract_regions_from_contigs(contigs, regions)

    cds_records: list[dict[str, Any]] = []
    annotation_meta: dict[str, Any] = {}
    gff_text, gff_contact = cached_assembly_file(fetch_ftp_path, "genomic.gff.gz", fetch_accession, deadline=deadline)
    if gff_text:
        cds_records, _gff_contigs, annotation_meta = parse_gff_cds_records(gff_text, fna_text)
        annotation_meta["contacts"] = {"gff": slim_contact(gff_contact), "fna": slim_contact(fna_contact)}
    if not cds_records:
        gbff_text, gbff_contact = cached_assembly_file(fetch_ftp_path, "genomic.gbff.gz", fetch_accession, deadline=deadline)
        if gbff_text:
            cds_records, gbff_contigs, annotation_meta = parse_gbff_cds_records(gbff_text)
            if fetch_mode == "flinders_genbank_assembly":
                contigs = gbff_contigs
                targets, errors = extract_regions_from_contigs(contigs, regions)
            annotation_meta["contacts"] = {"gbff": slim_contact(gbff_contact), "fna": slim_contact(fna_contact)}
        else:
            annotation_meta = {"source_parser": "none", "contacts": {"gff": slim_contact(gff_contact), "fna": slim_contact(fna_contact), "gbff": slim_contact(gbff_contact)}}

    return (
        {
            "fetch_accession": fetch_accession,
            "fetch_mode": fetch_mode,
            "contigs": contigs,
            "target_regions": targets,
            "target_sequences": [row["sequence"] for row in targets],
            "cds_records": cds_records,
        },
        {
            "fetch_accession": fetch_accession,
            "fetch_mode": fetch_mode,
            "n_target_regions": len(targets),
            "target_bp": sum(len(str(row["sequence"])) for row in targets),
            "extraction_errors": dict(errors),
            "annotation": annotation_meta,
            "fna": slim_contact(fna_contact),
            "genbank_lookup": slim_contact(gb_lookup),
        },
    )


def slim_contact(contact: dict[str, Any]) -> dict[str, Any]:
    return {key: contact.get(key) for key in ("on_disk_cache_hit", "borrowed_cache_hit", "reachable", "error", "cache_path", "match_mode") if key in contact}


def target_cds_segments(target: dict[str, Any], cds_records: list[dict[str, Any]]) -> list[dict[str, Any]]:
    contig = str(target["contig"])
    start = int(target["start"])
    end = int(target["end"])
    segments = []
    for cds in cds_records:
        if str(cds.get("seqid") or "") != contig:
            continue
        c0 = int(cds.get("start") or 0)
        c1 = int(cds.get("end") or 0)
        if not intervals_overlap(start, end, c0, c1):
            continue
        overlap0 = max(start, c0)
        overlap1 = min(end, c1)
        if overlap1 - overlap0 < 90:
            continue
        seq = str(cds.get("sequence") or "")
        if not seq:
            continue
        rel0 = overlap0 - c0
        rel1 = overlap1 - c0
        rel0 -= rel0 % 3
        rel1 -= rel1 % 3
        if rel1 - rel0 < 90 or rel1 > len(seq):
            continue
        piece = seq[rel0:rel1]
        if str(cds.get("strand") or "+") == "-":
            piece = reverse_complement_dna(piece)
        segments.append({"start": overlap0 - start, "end": overlap1 - start, "sequence": piece})
    segments.sort(key=lambda row: int(row["start"]))
    return segments


def null_b_sequence(target: dict[str, Any], cds_records: list[dict[str, Any]], rng: random.Random) -> tuple[str, int, int]:
    seq = str(target["sequence"])
    out = list(null_a_sequence(seq, rng))
    covered = [False] * len(seq)
    replaced_bp = 0
    for segment in target_cds_segments(target, cds_records):
        start = int(segment["start"])
        end = int(segment["end"])
        shuffled = synonym_shuffle_cds(str(segment["sequence"]), rng)
        if shuffled is None or len(shuffled) != end - start:
            continue
        out[start:end] = list(shuffled)
        for i in range(start, end):
            if 0 <= i < len(covered) and not covered[i]:
                covered[i] = True
                replaced_bp += 1
    return "".join(out), replaced_bp, len(seq)


def expected_under_null_a(seqs: list[str], motifs: list[str], n_null: int, seed: str) -> tuple[float, dict[str, Any]]:
    rng = random.Random(stable_seed(seed))
    counts = []
    for _ in range(n_null):
        shuffled = [null_a_sequence(seq, rng) for seq in seqs]
        counts.append(float(count_motif_set(shuffled, motifs)))
    return (statistics.mean(counts) if counts else 0.0), {
        "n": n_null,
        "median": round_float(median(counts)),
        "mean": round_float(statistics.mean(counts) if counts else 0.0),
        "ci95": [round_float(percentile(counts, 0.025)), round_float(percentile(counts, 0.975))],
    }


def expected_under_null_b(targets: list[dict[str, Any]], cds_records: list[dict[str, Any]], motifs: list[str], n_null: int, seed: str) -> tuple[float, dict[str, Any]]:
    rng = random.Random(stable_seed(seed))
    counts = []
    covered_bp_values = []
    total_bp_values = []
    for _ in range(n_null):
        shuffled = []
        covered_bp = 0
        total_bp = 0
        for target in targets:
            seq, covered, total = null_b_sequence(target, cds_records, rng)
            shuffled.append(seq)
            covered_bp += covered
            total_bp += total
        covered_bp_values.append(float(covered_bp))
        total_bp_values.append(float(total_bp))
        counts.append(float(count_motif_set(shuffled, motifs)))
    mean_count = statistics.mean(counts) if counts else 0.0
    mean_covered = statistics.mean(covered_bp_values) if covered_bp_values else 0.0
    mean_total = statistics.mean(total_bp_values) if total_bp_values else 0.0
    return mean_count, {
        "n": n_null,
        "median": round_float(median(counts)),
        "mean": round_float(mean_count),
        "ci95": [round_float(percentile(counts, 0.025)), round_float(percentile(counts, 0.975))],
        "mean_coding_bp_replaced": round_float(mean_covered),
        "mean_target_bp": round_float(mean_total),
        "mean_coding_replacement_fraction": round_float(mean_covered / mean_total if mean_total > 0 else 0.0),
    }


def build_decoy_pools(background_by_host: dict[str, list[dict[str, Any]]]) -> dict[tuple[int, int, bool], dict[str, list[str]]]:
    pools: dict[tuple[int, int, bool], dict[str, list[str]]] = defaultdict(lambda: defaultdict(list))
    for host, rows in background_by_host.items():
        for row in rows:
            motif = str(row.get("motif_canonical") or "")
            if motif:
                pools[motif_profile(row)][host].append(motif)
    return pools


def sample_decoy_motifs(
    host: str,
    own_rows: list[dict[str, Any]],
    pools: dict[tuple[int, int, bool], dict[str, list[str]]],
    rng: random.Random,
) -> list[str] | None:
    sampled = []
    true_motifs = set(unique_motifs(own_rows))
    by_profile: dict[tuple[int, int, bool], list[str]] = defaultdict(list)
    for row in own_rows:
        motif = str(row.get("motif_canonical") or "")
        if motif:
            by_profile[motif_profile(row)].append(motif)
    for profile, motifs in by_profile.items():
        candidates = [
            motif
            for pool_host, pool_motifs in pools.get(profile, {}).items()
            if pool_host != host
            for motif in pool_motifs
            if motif not in true_motifs
        ]
        if len(candidates) < len(motifs):
            return None
        sampled.extend(rng.sample(candidates, len(motifs)))
    result = sorted(set(sampled))
    return result if result else None


def decoy_scores(
    host: str,
    own_rows: list[dict[str, Any]],
    seqs: list[str],
    pools: dict[tuple[int, int, bool], dict[str, list[str]]],
    k_decoy: int,
    n_null: int,
    seed: str,
) -> tuple[list[float], dict[str, Any]]:
    rng = random.Random(stable_seed(seed))
    scores = []
    attempts = 0
    while len(scores) < k_decoy and attempts < k_decoy * 25:
        attempts += 1
        motifs = sample_decoy_motifs(host, own_rows, pools, rng)
        if not motifs:
            continue
        observed = float(count_motif_set(seqs, motifs))
        expected, _meta = expected_under_null_a(seqs, motifs, max(1, min(20, n_null)), seed + f".{attempts}")
        scores.append(log2_depletion(observed, expected))
    return scores, {"requested_k": k_decoy, "realized_k": len(scores), "attempts": attempts}


def rank_fraction(true_score: float, decoy_values: list[float]) -> float | None:
    clean = [value for value in decoy_values if math.isfinite(value)]
    if not clean:
        return None
    return sum(1 for value in clean if value <= true_score) / len(clean)


def load_carriers(carrier_source: str, deadline: float | None) -> tuple[list[dict[str, Any]], list[dict[str, Any]], dict[str, Any], dict[str, Any]]:
    if carrier_source == "rebase":
        source_rows, source_meta = load_rebase_carriers(deadline=deadline)
        carrier_rows, tier_meta = tier_a_rebase_groups(source_rows)
    elif carrier_source == "blow":
        source_rows, source_meta = load_blow_carriers(deadline=deadline)
        carrier_rows, tier_meta = tier_a_blow_groups(source_rows)
    else:
        raise ValueError(f"unknown carrier source: {carrier_source}")
    return source_rows, carrier_rows, source_meta, tier_meta


def compute_host(
    host: str,
    carriers: list[dict[str, Any]],
    context: dict[str, Any],
    decoy_pools: dict[tuple[int, int, bool], dict[str, list[str]]],
    null_n: int,
    decoy_k: int,
) -> dict[str, Any]:
    motifs = unique_motifs(carriers)
    targets = list(context["target_regions"])
    seqs = [str(row["sequence"]) for row in targets]
    observed = float(count_motif_set(seqs, motifs))
    expected_a, null_a_meta = expected_under_null_a(seqs, motifs, null_n, EXPERIMENT_ID + f".{host}.A")
    expected_b, null_b_meta = expected_under_null_b(targets, list(context.get("cds_records") or []), motifs, null_n, EXPERIMENT_ID + f".{host}.B")
    d_a = log2_depletion(observed, expected_a)
    d_b = log2_depletion(observed, expected_b)
    d_decoys, decoy_meta = decoy_scores(host, carriers, seqs, decoy_pools, decoy_k, null_n, EXPERIMENT_ID + f".{host}.C")
    rank = rank_fraction(d_a, d_decoys)
    return {
        "host_accession": host,
        "gtdb_family": str(carriers[0].get("gtdb_family") or "unknown"),
        "gtdb_genus": str(carriers[0].get("gtdb_genus") or ""),
        "host_organism": str(carriers[0].get("host_organism") or ""),
        "motif_count": len(motifs),
        "motifs": motifs[:30],
        "target_regions": len(targets),
        "target_bp": sum(len(seq) for seq in seqs),
        "observed_count": observed,
        "expected_count_null_a": expected_a,
        "expected_count_null_b": expected_b,
        "D_null_a": d_a,
        "D_null_b": d_b,
        "D_null_c_decoy_median": median(d_decoys),
        "carrier_rank": rank,
        "decoy": decoy_meta,
        "null_a": null_a_meta,
        "null_b": null_b_meta,
    }


def compute_nc1(
    host_rows: list[dict[str, Any]],
    context_by_host: dict[str, dict[str, Any]],
    carriers_by_host: dict[str, list[dict[str, Any]]],
    null_n: int,
) -> dict[str, Any]:
    rows = []
    for row in host_rows:
        host = str(row["host_accession"])
        context = context_by_host.get(host)
        carriers = carriers_by_host.get(host, [])
        if not context or not carriers:
            continue
        target_bp = int(row.get("target_bp") or 0)
        windows = non_prophage_windows(
            dict(context["contigs"]),
            list(context["target_regions"]),
            target_bp,
            EXPERIMENT_ID + f".{host}.NC1",
        )
        if not windows:
            continue
        motifs = unique_motifs(carriers)
        observed = float(count_motif_set(windows, motifs))
        expected, meta = expected_under_null_a(windows, motifs, max(1, min(null_n, 40)), EXPERIMENT_ID + f".{host}.NC1.A")
        rows.append(
            {
                "host_accession": host,
                "gtdb_family": row.get("gtdb_family"),
                "target_bp": sum(len(seq) for seq in windows),
                "D_null_a": log2_depletion(observed, expected),
                "observed_count": observed,
                "expected_count": expected,
                "null_a": meta,
            }
        )
    med = family_weighted_median(rows, "D_null_a")
    return {
        "description": "same-host chromosome non-prophage windows as target",
        "n_hosts": len(rows),
        "median_D_null_a_family_weighted": round_float(med),
        "strong_depletion": bool(med is not None and med <= SUPPORT_MEDIAN_D_MAX),
        "expected_no_strong_depletion": bool(med is None or med > SUPPORT_MEDIAN_D_MAX),
        "preview": rows[:12],
    }


def compute_nc2(host_rows: list[dict[str, Any]], context_by_host: dict[str, dict[str, Any]], carriers_by_host: dict[str, list[dict[str, Any]]], null_n: int) -> dict[str, Any]:
    by_family: dict[str, list[str]] = defaultdict(list)
    for row in host_rows:
        by_family[str(row.get("gtdb_family") or "unknown")].append(str(row["host_accession"]))
    rows = []
    for row in host_rows:
        host = str(row["host_accession"])
        family = str(row.get("gtdb_family") or "unknown")
        candidates = [other for other in by_family.get(family, []) if other != host and other in context_by_host]
        if not candidates:
            continue
        rng = random.Random(stable_seed(EXPERIMENT_ID + f".{host}.NC2"))
        other = rng.choice(sorted(candidates))
        carriers = carriers_by_host.get(host, [])
        if not carriers:
            continue
        seqs = [str(target["sequence"]) for target in context_by_host[other]["target_regions"]]
        motifs = unique_motifs(carriers)
        observed = float(count_motif_set(seqs, motifs))
        expected, meta = expected_under_null_a(seqs, motifs, max(1, min(null_n, 40)), EXPERIMENT_ID + f".{host}.NC2.A")
        rows.append(
            {
                "host_accession": host,
                "swapped_target_host": other,
                "gtdb_family": family,
                "D_null_a": log2_depletion(observed, expected),
                "observed_count": observed,
                "expected_count": expected,
                "null_a": meta,
            }
        )
    med = family_weighted_median(rows, "D_null_a")
    return {
        "description": "within-family cross-host target swap",
        "n_hosts": len(rows),
        "median_D_null_a_family_weighted": round_float(med),
        "strong_depletion": bool(med is not None and med <= SUPPORT_MEDIAN_D_MAX),
        "expected_signal_loss": bool(med is None or med > SUPPORT_MEDIAN_D_MAX),
        "preview": rows[:12],
    }


def orphan_tier_b_rows(carriers: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for row in carriers:
        cognate = str(row.get("rebase_cognate_re_names") or row.get("enzyme_names") or "")
        mtase = str(row.get("mtase_name") or row.get("enzyme_name") or "")
        if cognate.strip() or re.match(r"^[A-Z][A-Za-z0-9]*[A-Z]I", mtase):
            continue
        copy = dict(row)
        copy["evidence_tier"] = "orphan_tier_b_mtase_only"
        rows.append(copy)
    return rows


def compute_nc3(
    host_rows: list[dict[str, Any]],
    context_by_host: dict[str, dict[str, Any]],
    orphan_by_host: dict[str, list[dict[str, Any]]],
    null_n: int,
) -> dict[str, Any]:
    rows = []
    for row in host_rows:
        host = str(row["host_accession"])
        context = context_by_host.get(host)
        carriers = orphan_by_host.get(host, [])
        if not context or not carriers:
            continue
        seqs = [str(target["sequence"]) for target in context["target_regions"]]
        motifs = unique_motifs(carriers)
        if not motifs:
            continue
        observed = float(count_motif_set(seqs, motifs))
        expected, meta = expected_under_null_a(seqs, motifs, max(1, min(null_n, 40)), EXPERIMENT_ID + f".{host}.NC3.A")
        rows.append(
            {
                "host_accession": host,
                "gtdb_family": row.get("gtdb_family"),
                "motif_count": len(motifs),
                "D_null_a": log2_depletion(observed, expected),
                "observed_count": observed,
                "expected_count": expected,
                "null_a": meta,
            }
        )
    med = family_weighted_median(rows, "D_null_a")
    return {
        "description": "orphan/Tier-B-only MTase motifs as carrier",
        "n_hosts": len(rows),
        "median_D_null_a_family_weighted": round_float(med),
        "expected_weaker_than_active_rm": True,
        "preview": rows[:12],
    }


def verdict_for(summary: dict[str, Any]) -> tuple[str, str, int]:
    n_hosts = int(summary.get("n_hosts") or 0)
    median_d = summary.get("median_D_A")
    median_rank = summary.get("median_rank")
    rank_shift = summary.get("family_rank_shift")
    boot = summary.get("family_block_bootstrap") if isinstance(summary.get("family_block_bootstrap"), dict) else {}
    p = boot.get("p_one_sided_rank_shift_positive") if isinstance(boot, dict) else None
    nulls_negative = bool(summary.get("nulls_all_directional_negative"))
    nc1_ok = bool(summary.get("NC1_expected"))
    nc2_ok = bool(summary.get("NC2_expected"))
    if n_hosts < MIN_PRIMARY_HOSTS:
        return (
            "needs_external",
            "exploratory_underpowered",
            2,
        )
    if (
        isinstance(median_d, (int, float))
        and isinstance(median_rank, (int, float))
        and isinstance(rank_shift, (int, float))
        and isinstance(p, (int, float))
        and median_d <= SUPPORT_MEDIAN_D_MAX
        and median_rank <= SUPPORT_MEDIAN_RANK_MAX
        and rank_shift >= SUPPORT_RANK_SHIFT_MIN
        and p <= SUPPORT_BOOTSTRAP_P_MAX
        and nulls_negative
        and nc1_ok
        and nc2_ok
    ):
        return ("supportive", "all_oracle_gates_directional", 0)
    if (
        n_hosts >= REFUTED_POWER_HOSTS
        and isinstance(median_rank, (int, float))
        and isinstance(rank_shift, (int, float))
        and 0.45 <= median_rank <= 0.55
        and rank_shift <= 0.03
    ):
        return ("refuted", "powered_rank_near_null", 3)
    if (
        isinstance(median_d, (int, float))
        and isinstance(median_rank, (int, float))
        and median_d > 0.10
        and median_rank >= 0.60
    ):
        return ("anti_predicted", "motif_enrichment_against_prediction", 3)
    return ("needs_external", "directional_but_not_oracle_supportive", 2)


def main() -> int:
    started = time.monotonic()
    carrier_source = os.environ.get("RM_CARRIER_SOURCE", "blow").strip().lower() or "blow"
    target_source = os.environ.get("RM_TARGET_SOURCE", "prophage").strip().lower() or "prophage"
    host_limit_raw = os.environ.get("RM_HOST_LIMIT", "").strip()
    host_limit = int(host_limit_raw) if host_limit_raw else None
    null_n = int(os.environ.get("RM_NULL_N", str(DEFAULT_NULL_N)))
    decoy_k = int(os.environ.get("RM_DECOY_K", str(DEFAULT_DECOY_K)))
    bootstrap_n = int(os.environ.get("RM_BOOTSTRAP_N", str(DEFAULT_BOOTSTRAP_N)))
    deadline_seconds = float(os.environ.get("RM_FETCH_DEADLINE_SECONDS", "300"))
    deadline = time.monotonic() + deadline_seconds if deadline_seconds > 0 else None

    if target_source != "prophage":
        print(json.dumps({"error": "unsupported_RM_TARGET_SOURCE_for_full_signal", "RM_TARGET_SOURCE": target_source}, sort_keys=True))
        return 4
    try:
        source_rows, carrier_rows, source_meta, tier_meta = load_carriers(carrier_source, deadline)
    except ValueError as exc:
        print(json.dumps({"error": str(exc)}, sort_keys=True))
        return 4

    mapped_all, mapping_meta = map_carriers_to_assemblies(carrier_rows, host_limit=None, deadline=deadline)
    mapped = mapped_all
    if host_limit is not None and host_limit > 0:
        limited_organisms = sorted({str(row.get("rebase_organism") or "") for row in carrier_rows})[:host_limit]
        limited_set = set(limited_organisms)
        mapped = [row for row in mapped_all if str(row.get("rebase_organism") or "") in limited_set]
    inventory, target_meta = prophage_target_inventory(mapped, deadline=deadline)
    inv_by_host = host_inventory_map(inventory)
    carriers_by_host = carrier_rows_by_host(mapped)
    background_by_host = carrier_rows_by_host(mapped_all)
    decoy_pools = build_decoy_pools(background_by_host)
    regions_by_host, flinders_meta = load_flinders_host_prophage_rows(set(carriers_by_host))

    context_by_host: dict[str, dict[str, Any]] = {}
    context_meta: dict[str, Any] = {}
    host_rows = []
    skip_counts: Counter[str] = Counter()
    for host, carriers in sorted(carriers_by_host.items()):
        inv = inv_by_host.get(host, {})
        if int(inv.get("num_targets") or 0) <= 0:
            skip_counts["no_prophage_target"] += 1
            continue
        ftp_path = str(carriers[0].get("host_ftp_path") or "")
        regions = regions_by_host.get(host, [])
        context, meta = load_host_sequence_context(host, ftp_path, regions, deadline=deadline)
        context_meta[host] = meta
        if not context or not context.get("target_sequences"):
            skip_counts["target_sequence_unavailable"] += 1
            continue
        row = compute_host(host, carriers, context, decoy_pools, null_n, decoy_k)
        if row.get("carrier_rank") is None:
            skip_counts["decoy_unavailable"] += 1
            continue
        context_by_host[host] = context
        host_rows.append(row)

    orphan_rows = orphan_tier_b_rows(mapped)
    orphan_by_host = carrier_rows_by_host(orphan_rows)

    median_d_a = family_weighted_median(host_rows, "D_null_a")
    median_d_b = family_weighted_median(host_rows, "D_null_b")
    median_rank = family_weighted_median(host_rows, "carrier_rank")
    family_rank_shift = (0.5 - median_rank) if median_rank is not None else None
    median_d_c = family_weighted_median(host_rows, "D_null_c_decoy_median")
    boot = family_block_bootstrap_rank_shift(host_rows, bootstrap_n, EXPERIMENT_ID + ".rank_shift")
    nc1 = compute_nc1(host_rows, context_by_host, carriers_by_host, null_n)
    nc2 = compute_nc2(host_rows, context_by_host, carriers_by_host, null_n)
    nc3 = compute_nc3(host_rows, context_by_host, orphan_by_host, null_n)
    nulls_all_negative = bool(
        median_d_a is not None
        and median_d_b is not None
        and median_d_c is not None
        and median_d_a < 0
        and median_d_b < 0
        and median_d_c < 0
    )
    summary: dict[str, Any] = {
        "n_hosts": len(host_rows),
        "n_families": len({str(row.get("gtdb_family") or "unknown") for row in host_rows}),
        "median_D_A": round_float(median_d_a),
        "median_D_B": round_float(median_d_b),
        "median_D_C_decoy": round_float(median_d_c),
        "median_rank": round_float(median_rank),
        "family_rank_shift": round_float(family_rank_shift),
        "family_block_bootstrap": boot,
        "nulls_all_directional_negative": nulls_all_negative,
        "NC1_expected": bool(nc1.get("expected_no_strong_depletion")),
        "NC2_expected": bool(nc2.get("expected_signal_loss")),
        "NC3_n_hosts": nc3.get("n_hosts"),
    }
    verdict, status_note, exit_code = verdict_for(summary)
    summary["verdict"] = verdict
    summary["status_note"] = status_note

    payload = {
        "experiment_id": EXPERIMENT_ID,
        "claim": CLAIM,
        "generated_at": now_iso(),
        "runtime_seconds": round_float(time.monotonic() - started, 3),
        "carrier_source": carrier_source,
        "target_source": target_source,
        "host_limit": host_limit,
        "null_N": null_n,
        "decoy_K": decoy_k,
        "bootstrap_N": bootstrap_n,
        "exploratory_note": "Blow methylome carrier is Tier-B sensitivity for this claim; primary status needs REBASE Genomes Tier-A1 and larger host count.",
        "oracle_spec": {
            "main_evidence": "carrier-specific rank fraction of matched decoy carrier D values <= true D; smaller rank is stronger depletion specific to resident carrier",
            "supportive_rule": {
                "median_D_A": "<= -0.15",
                "median_clean_rank": "<= 0.40",
                "family_rank_shift": ">= 0.10",
                "family_block_bootstrap_one_sided_p": "<= 0.01",
                "nulls": "A/B/C directional negative",
                "negative_controls": "NC1 and NC2 no strong depletion",
            },
        },
        "summary": summary,
        "null_A": {
            "description": "exact 3-mer-preserving per-target shuffle",
            "median_D_family_weighted": round_float(median_d_a),
            "directional_negative": bool(median_d_a is not None and median_d_a < 0),
        },
        "null_B": {
            "description": "coding-aware synonymous codon multiset shuffle within annotated CDS overlaps, noncoding fallback to Null A",
            "median_D_family_weighted": round_float(median_d_b),
            "directional_negative": bool(median_d_b is not None and median_d_b < 0),
            "median_coding_replacement_fraction": round_float(
                median([
                    float(row["null_b"].get("mean_coding_replacement_fraction") or 0.0)
                    for row in host_rows
                    if isinstance(row.get("null_b"), dict)
                ])
            ),
        },
        "null_C": {
            "description": "matched carrier-decoy sets by motif length, degeneracy, and palindrome flag",
            "median_decoy_D_family_weighted": round_float(median_d_c),
            "median_rank_family_weighted": round_float(median_rank),
            "family_rank_shift": round_float(family_rank_shift),
            "directional_negative": bool(median_d_c is not None and median_d_c < 0),
        },
        "negative_controls": {
            "NC1_same_host_nonprophage_windows": nc1,
            "NC2_cross_host_target_swap_same_family": nc2,
            "NC3_orphan_tier_b_only_mtase": nc3,
        },
        "input_audit": {
            "source_meta": source_meta,
            "tier_filter": tier_meta,
            "mapping": {
                **mapping_meta,
                "host_limit": host_limit,
                "n_limited_mapped_hosts": len(carriers_by_host),
                "n_background_mapped_hosts": len(background_by_host),
            },
            "target": target_meta,
            "flinders": flinders_meta,
            "n_source_rows": len(source_rows),
            "n_tier_rows": len(carrier_rows),
            "n_mapped_rows": len(mapped),
        },
        "skip_counts": dict(skip_counts),
        "host_rows": host_rows,
        "host_context_meta_preview": {host: context_meta[host] for host in sorted(context_meta)[:20]},
    }
    print(json.dumps(payload, ensure_ascii=True, sort_keys=True, indent=2))
    return exit_code


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Conserved synonymous edge-hiding across NCBI genetic code tables.

The primary statistic counts Hamming-1 synonymous codon pairs among sense
codons only.  Stop is still part of the degeneracy profile and the null
assignment, but Stop-Stop edges are not counted as protein-synonymous hiding.

The conservation test compares each natural code table against random code
tables with the same exact degeneracy profile, then aggregates the natural-vs-
null contrast over reassignment clusters.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from itertools import product
import json
import math
import random
import sys


EXPERIMENT_ID = "altcode_edge_hiding_tau"
CLAIM_ID = "bridge.genetic_code.altcode_edge_hiding.tau_conservation"

NULL_SEED = 620260620
NULL_DRAWS = 20000
BOOTSTRAP_DRAWS = 20000
CLUSTER_DISTANCE_THRESHOLD = 0.35

CERTIFIED_CLUSTER_P = 0.001
CERTIFIED_MIN_FLOOR_FRACTION = 0.95

BASES = ("U", "C", "A", "G")
AMINO_ACIDS = tuple("*ACDEFGHIKLMNPQRSTVWY")
STOP = "*"

# Order is U,C,A,G lexicographic over the three codon positions.
# Data are from NCBI genetic code table version 4.5 as packaged by Biopython.
FALLBACK_TABLES = (
    (1, "Standard", "SGC0", "FFLLSSSSYY**CC*WLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (2, "Vertebrate Mitochondrial", "SGC1", "FFLLSSSSYY**CCWWLLLLPPPPHHQQRRRRIIMMTTTTNNKKSS**VVVVAAAADDEEGGGG"),
    (3, "Yeast Mitochondrial", "SGC2", "FFLLSSSSYY**CCWWTTTTPPPPHHQQRRRRIIMMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (4, "Mold Mitochondrial; Protozoan Mitochondrial; Coelenterate Mitochondrial; Mycoplasma; Spiroplasma", "SGC3", "FFLLSSSSYY**CCWWLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (5, "Invertebrate Mitochondrial", "SGC4", "FFLLSSSSYY**CCWWLLLLPPPPHHQQRRRRIIMMTTTTNNKKSSSSVVVVAAAADDEEGGGG"),
    (6, "Ciliate Nuclear; Dasycladacean Nuclear; Hexamita Nuclear", "SGC5", "FFLLSSSSYYQQCC*WLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (9, "Echinoderm Mitochondrial; Flatworm Mitochondrial", "SGC8", "FFLLSSSSYY**CCWWLLLLPPPPHHQQRRRRIIIMTTTTNNNKSSSSVVVVAAAADDEEGGGG"),
    (10, "Euplotid Nuclear", "SGC9", "FFLLSSSSYY**CCCWLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (11, "Bacterial, Archaeal and Plant Plastid", None, "FFLLSSSSYY**CC*WLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (12, "Alternative Yeast Nuclear", None, "FFLLSSSSYY**CC*WLLLSPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (13, "Ascidian Mitochondrial", None, "FFLLSSSSYY**CCWWLLLLPPPPHHQQRRRRIIMMTTTTNNKKSSGGVVVVAAAADDEEGGGG"),
    (14, "Alternative Flatworm Mitochondrial", None, "FFLLSSSSYYY*CCWWLLLLPPPPHHQQRRRRIIIMTTTTNNNKSSSSVVVVAAAADDEEGGGG"),
    (15, "Blepharisma Macronuclear", None, "FFLLSSSSYY*QCC*WLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (16, "Chlorophycean Mitochondrial", None, "FFLLSSSSYY*LCC*WLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (21, "Trematode Mitochondrial", None, "FFLLSSSSYY**CCWWLLLLPPPPHHQQRRRRIIMMTTTTNNNKSSSSVVVVAAAADDEEGGGG"),
    (22, "Scenedesmus obliquus Mitochondrial", None, "FFLLSS*SYY*LCC*WLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (23, "Thraustochytrium Mitochondrial", None, "FF*LSSSSYY**CC*WLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (24, "Pterobranchia Mitochondrial", None, "FFLLSSSSYY**CCWWLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSSKVVVVAAAADDEEGGGG"),
    (25, "Candidate Division SR1 and Gracilibacteria", None, "FFLLSSSSYY**CCGWLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (26, "Pachysolen tannophilus Nuclear", None, "FFLLSSSSYY**CC*WLLLAPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (27, "Karyorelict Nuclear", None, "FFLLSSSSYYQQCC*WLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (28, "Condylostoma Nuclear", None, "FFLLSSSSYY**CC*WLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (29, "Mesodinium Nuclear", None, "FFLLSSSSYYYYCC*WLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (30, "Peritrich Nuclear", None, "FFLLSSSSYYEECC*WLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (31, "Blastocrithidia Nuclear", None, "FFLLSSSSYY**CCWWLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (32, "Balanophoraceae Plastid", None, "FFLLSSSSYY*WCC*WLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSRRVVVVAAAADDEEGGGG"),
    (33, "Cephalodiscidae Mitochondrial", None, "FFLLSSSSYYY*CCWWLLLLPPPPHHQQRRRRIIIMTTTTNNKKSSSKVVVVAAAADDEEGGGG"),
)


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def codon_order() -> list[str]:
    return ["".join(parts) for parts in product(BASES, repeat=3)]


CODONS = codon_order()


def hamming1_edges() -> tuple[list[tuple[int, int]], list[list[int]]]:
    index = {codon: pos for pos, codon in enumerate(CODONS)}
    edges: list[tuple[int, int]] = []
    neighbors: list[list[int]] = [[] for _ in CODONS]
    for codon in CODONS:
        left = index[codon]
        for pos in range(3):
            for base in BASES:
                if base == codon[pos]:
                    continue
                other = codon[:pos] + base + codon[pos + 1 :]
                right = index[other]
                neighbors[left].append(right)
                if left < right:
                    edges.append((left, right))
    return edges, neighbors


EDGES, NEIGHBORS = hamming1_edges()


def labels_from_sequence(seq: str) -> list[str]:
    if len(seq) != 64:
        raise ValueError(f"codon table sequence has length {len(seq)}, expected 64")
    bad = sorted(set(seq) - set(AMINO_ACIDS))
    if bad:
        raise ValueError(f"unknown amino acid symbols in fallback table: {bad}")
    return list(seq)


def load_tables() -> tuple[list[dict[str, object]], str]:
    try:
        from Bio.Data import CodonTable  # type: ignore
    except Exception:
        tables = [
            {
                "id": table_id,
                "name": name,
                "alt_name": alt_name,
                "labels": labels_from_sequence(seq),
            }
            for table_id, name, alt_name, seq in FALLBACK_TABLES
        ]
        return tables, "fallback_ncbi_table_version_4_5_from_biopython_source"

    tables = []
    for table_id in sorted(CodonTable.unambiguous_dna_by_id):
        table = CodonTable.unambiguous_dna_by_id[table_id]
        mapping = {codon.replace("T", "U"): aa for codon, aa in table.forward_table.items()}
        for codon in table.stop_codons:
            mapping[codon.replace("T", "U")] = STOP
        missing = [codon for codon in CODONS if codon not in mapping]
        if missing:
            raise ValueError(f"Biopython table {table_id} missing codons: {missing}")
        names = list(getattr(table, "names", []))
        name = names[0] if names else f"NCBI table {table_id}"
        alt_name = names[-1] if len(names) > 1 else None
        tables.append(
            {
                "id": table_id,
                "name": name,
                "alt_name": alt_name,
                "labels": [mapping[codon] for codon in CODONS],
            }
        )
    return tables, "biopython"


def edge_count(labels: list[str]) -> int:
    total = 0
    for left, right in EDGES:
        label = labels[left]
        if label != STOP and label == labels[right]:
            total += 1
    return total


def profile_key(labels: list[str]) -> tuple[int, ...]:
    counts = Counter(labels)
    return tuple(sorted(counts.values(), reverse=True))


def labels_for_profile(profile: tuple[int, ...]) -> list[int]:
    labels: list[int] = []
    for block, size in enumerate(profile):
        labels.extend([block] * size)
    return labels


def score_blocks(labels: list[int], stop_block: int | None = None) -> int:
    score = 0
    for left, right in EDGES:
        block = labels[left]
        if block == labels[right] and block != stop_block:
            score += 1
    return score


def shuffled_profile(profile: tuple[int, ...], rng: random.Random) -> list[int]:
    labels = labels_for_profile(profile)
    rng.shuffle(labels)
    return labels


def null_distribution(profile: tuple[int, ...], stop_size: int, seed: int) -> list[int]:
    rng = random.Random(seed)
    stop_block = profile.index(stop_size)
    return [score_blocks(shuffled_profile(profile, rng), stop_block) for _ in range(NULL_DRAWS)]


def quantiles(values: list[int]) -> dict[str, float | int]:
    ordered = sorted(values)
    n = len(ordered)
    mean = sum(ordered) / n
    variance = sum((value - mean) * (value - mean) for value in ordered) / (n - 1)

    def pick(q: float) -> int:
        return ordered[int(q * (n - 1))]

    return {
        "mean": mean,
        "sd": math.sqrt(variance),
        "min": ordered[0],
        "p01": pick(0.01),
        "p05": pick(0.05),
        "median": pick(0.50),
        "p95": pick(0.95),
        "p99": pick(0.99),
        "max": ordered[-1],
    }


def upper_p(values: list[int], observed: int) -> float:
    return (1 + sum(1 for value in values if value >= observed)) / (len(values) + 1)


def median(values: list[float]) -> float:
    ordered = sorted(values)
    n = len(ordered)
    middle = n // 2
    if n % 2 == 1:
        return ordered[middle]
    return (ordered[middle - 1] + ordered[middle]) / 2.0


def reassigned_set(labels: list[str], standard: list[str]) -> frozenset[str]:
    return frozenset(codon for codon, aa, std in zip(CODONS, labels, standard) if aa != std)


def reassignment_distance(a: frozenset[str], b: frozenset[str]) -> float:
    union = a | b
    if not union:
        return 0.0
    return 1.0 - (len(a & b) / len(union))


def cluster_tables(tables: list[dict[str, object]], standard: list[str]) -> list[list[int]]:
    sets = [reassigned_set(table["labels"], standard) for table in tables]  # type: ignore[arg-type]
    parent = list(range(len(tables)))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x: int, y: int) -> None:
        rx = find(x)
        ry = find(y)
        if rx != ry:
            parent[ry] = rx

    for i in range(len(tables)):
        for j in range(i + 1, len(tables)):
            if reassignment_distance(sets[i], sets[j]) <= CLUSTER_DISTANCE_THRESHOLD:
                union(i, j)

    groups: dict[int, list[int]] = defaultdict(list)
    for index in range(len(tables)):
        groups[find(index)].append(index)
    return sorted((sorted(group) for group in groups.values()), key=lambda group: (len(group), group[0]))


def cluster_bootstrap_p(
    clusters: list[list[int]],
    observed_effects: list[float],
    null_effects_by_code: list[list[float]],
    seed: int,
) -> tuple[float, dict[str, object]]:
    rng = random.Random(seed)
    observed_cluster_means = [sum(observed_effects[index] for index in cluster) / len(cluster) for cluster in clusters]
    observed = median(observed_cluster_means)
    exceed = 0
    null_medians: list[float] = []
    for _ in range(BOOTSTRAP_DRAWS):
        sampled = [rng.randrange(len(clusters)) for _ in clusters]
        values = []
        for cluster_index in sampled:
            cluster = clusters[cluster_index]
            code_values = []
            for index in cluster:
                samples = null_effects_by_code[index]
                code_values.append(samples[rng.randrange(len(samples))])
            values.append(sum(code_values) / len(code_values))
        sample_median = median(values)
        null_medians.append(sample_median)
        if sample_median >= observed:
            exceed += 1
    return (1 + exceed) / (BOOTSTRAP_DRAWS + 1), {
        "statistic": "median_cluster_mean_null_z",
        "observed": observed,
        "null_summary": quantiles([int(round(value * 1000000)) for value in null_medians]),
        "null_summary_scale": "values multiplied by 1000000 before integer summary",
        "draws": BOOTSTRAP_DRAWS,
    }


def code_summary(table: dict[str, object], standard: list[str]) -> dict[str, object]:
    labels = table["labels"]
    assert isinstance(labels, list)
    changes = sorted(reassigned_set(labels, standard))
    counts = Counter(labels)
    return {
        "id": table["id"],
        "name": table["name"],
        "alt_name": table["alt_name"],
        "degeneracy_profile": dict(sorted(counts.items())),
        "profile_multiset": list(profile_key(labels)),
        "reassigned_codons": changes,
        "n_reassigned_codons": len(changes),
        "e_in": edge_count(labels),
    }


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {"name": name, "ok": observed == expected, "observed": observed, "expected": expected}


def null_z_scores(null_values: list[int], observed: int) -> tuple[float, list[float]]:
    summary = quantiles(null_values)
    mean = float(summary["mean"])
    sd = float(summary["sd"])
    if sd == 0.0:
        return 0.0, [0.0 for _ in null_values]
    return (observed - mean) / sd, [(value - mean) / sd for value in null_values]


def verdict(
    floor_fraction: float,
    all_at_floor: bool,
    cluster_p: float,
) -> tuple[str, str]:
    if floor_fraction >= CERTIFIED_MIN_FLOOR_FRACTION and cluster_p <= CERTIFIED_CLUSTER_P:
        return (
            "certified",
            "natural codes' synonymous edge-hiding is systematically far above degeneracy-matched random codes across the family and survives phylogenetic clustering; no global bound claim is made",
        )
    if (all_at_floor or floor_fraction >= CERTIFIED_MIN_FLOOR_FRACTION) and cluster_p > CERTIFIED_CLUSTER_P:
        return (
            "coincidence",
            "per-code natural-vs-null contrasts are extreme, but the aggregate contrast does not survive phylogenetic clustering",
        )
    return (
        "coincidence",
        "natural-vs-null edge-hiding contrast does not satisfy the declared per-code and cluster-level conservation test",
    )


def main() -> None:
    try:
        tables, source = load_tables()
    except Exception as exc:
        emit(
            "needs_derivation",
            reason=f"could not load genetic code tables: {type(exc).__name__}: {exc}",
            null_seed=NULL_SEED,
            stop_handling="sense_to_sense_primary_stop_in_profile",
            checks=[],
        )

    tables = sorted(tables, key=lambda table: int(table["id"]))
    standard_table = next((table for table in tables if table["id"] == 1), None)
    if standard_table is None:
        emit(
            "needs_derivation",
            reason="NCBI standard table id 1 unavailable",
            null_seed=NULL_SEED,
            stop_handling="sense_to_sense_primary_stop_in_profile",
            checks=[],
        )
    standard = standard_table["labels"]
    assert isinstance(standard, list)

    by_profile: dict[tuple[tuple[int, ...], int], dict[str, object]] = {}
    profile_keys: set[tuple[tuple[int, ...], int]] = set()
    for table in tables:
        labels = table["labels"]
        assert isinstance(labels, list)
        profile_keys.add((profile_key(labels), Counter(labels)[STOP]))

    for group_index, cache_key in enumerate(sorted(profile_keys)):
        profile, stop_size = cache_key
        null_values = null_distribution(profile, stop_size, NULL_SEED + 7919 * group_index)
        by_profile[cache_key] = {
            "null_values": null_values,
            "null_summary": quantiles(null_values),
        }

    analyses: list[dict[str, object]] = []
    observed_z_by_code: list[float] = []
    null_z_by_code_samples: list[list[float]] = []
    for table in tables:
        labels = table["labels"]
        assert isinstance(labels, list)
        profile = profile_key(labels)
        stop_size = Counter(labels)[STOP]
        cache_key = (profile, stop_size)
        cached = by_profile[cache_key]
        e_in = edge_count(labels)
        null_values = cached["null_values"]
        assert isinstance(null_values, list)
        observed_z, null_z = null_z_scores(null_values, e_in)
        observed_z_by_code.append(observed_z)
        null_z_by_code_samples.append(null_z)
        analyses.append(
            {
                **code_summary(table, standard),
                "profile_upper_tail_p": upper_p(null_values, e_in),
                "null_z": observed_z,
                "null_e_in_summary": cached["null_summary"],
            }
        )

    upper_ps = [float(row["profile_upper_tail_p"]) for row in analyses]
    monte_carlo_floor = 1.0 / (NULL_DRAWS + 1)
    all_at_floor = all(p == monte_carlo_floor for p in upper_ps)
    floor_fraction = sum(p == monte_carlo_floor for p in upper_ps) / len(upper_ps)

    clusters = cluster_tables(tables, standard)
    observed_reassignment_sets = [reassigned_set(table["labels"], standard) for table in tables]  # type: ignore[arg-type]
    cluster_payload = [
        {
            "cluster_index": pos,
            "code_ids": [tables[index]["id"] for index in cluster],
            "members": [tables[index]["name"] for index in cluster],
            "reassigned_codon_union": sorted(set().union(*(observed_reassignment_sets[index] for index in cluster))),
        }
        for pos, cluster in enumerate(clusters)
    ]

    cluster_p, bootstrap_summary = cluster_bootstrap_p(
        clusters,
        observed_z_by_code,
        null_z_by_code_samples,
        NULL_SEED + 424242,
    )
    status, reason = verdict(floor_fraction, all_at_floor, cluster_p)

    changed_union = sorted(set().union(*(row["reassigned_codons"] for row in analyses)))
    checks = [
        check_row("codon_count", len(CODONS), 64),
        check_row("hamming1_edge_count", len(EDGES), 288),
        check_row("n_codes_at_least_25", len(tables) >= 25, True),
        check_row("standard_code_present", 1 in [table["id"] for table in tables], True),
        check_row("rewritten_codon_union_size", len(changed_union), 13),
        check_row("all_tables_cover_64_codons", all(len(table["labels"]) == 64 for table in tables), True),
        check_row("all_profile_p_at_floor", all_at_floor, True),
        check_row("cluster_bootstrap_p_within_threshold", cluster_p <= CERTIFIED_CLUSTER_P, True),
    ]

    emit(
        status,
        n_codes=len(tables),
        code_ids=[table["id"] for table in tables],
        per_code_profile_p={str(row["id"]): row["profile_upper_tail_p"] for row in analyses},
        all_at_floor=all_at_floor,
        null_z_by_code={str(row["id"]): row["null_z"] for row in analyses},
        per_code_e_in={str(row["id"]): row["e_in"] for row in analyses},
        n_clusters=len(clusters),
        cluster_bootstrap_p=cluster_p,
        cluster_bootstrap_summary=bootstrap_summary,
        cluster_structure=cluster_payload,
        null_seed=NULL_SEED,
        draws=NULL_DRAWS,
        stop_handling="primary statistic counts sense-to-sense synonymous Hamming-1 edges; Stop is retained as a profile block but Stop-Stop edges are excluded",
        table_source=source,
        biopython_used=(source == "biopython"),
        rewritten_codon_union_size=len(changed_union),
        rewritten_codon_union=changed_union,
        thresholds={
            "certified_cluster_bootstrap_p": CERTIFIED_CLUSTER_P,
            "certified_min_profile_floor_fraction": CERTIFIED_MIN_FLOOR_FRACTION,
            "profile_monte_carlo_floor": monte_carlo_floor,
            "cluster_distance_threshold": CLUSTER_DISTANCE_THRESHOLD,
        },
        code_results=analyses,
        checks=checks,
        reason=reason,
    )


if __name__ == "__main__":
    main()

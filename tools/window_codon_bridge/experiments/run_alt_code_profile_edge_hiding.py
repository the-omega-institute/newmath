#!/usr/bin/env python3
"""Profile-normalized local edge-hiding across alternative genetic codes."""
from __future__ import annotations

from collections import Counter
from itertools import product
import argparse
import json
import math
import random
import statistics
import sys
from pathlib import Path
from typing import Iterable


EXPERIMENT_ID = "alt_code_profile_edge_hiding"
CLAIM_ID = "bridge.genetic_code.altcode_profile_edge_hiding"
NULL_SEED = 620260701
DEFAULT_NULL_DRAWS = 20000
SELFTEST_NULL_DRAWS = 400

BASES = ("U", "C", "A", "G")
STOP = "*"
MIN_DISTINCT_TABLES = 20
NEAR_MAX_FLOOR = 0.89
CERTIFIED_MEDIAN_TAU_FLOOR = 0.94
CERTIFIED_MIN_TAU_FLOOR = 0.89
CERTIFIED_P_GE_FLOOR = 1.0 / (DEFAULT_NULL_DRAWS + 1)
CERTIFIED_MIN_Z = 5.0
REFUTED_MIN_TAU = 0.80

# Edge-isoperimetric maxima for a single block of k vertices in H(3,4), k <= 8.
# The NCBI genetic-code degeneracy profiles in this experiment never exceed 8.
SINGLE_BLOCK_EDGE_MAX = {
    0: 0,
    1: 0,
    2: 1,
    3: 3,
    4: 6,
    5: 7,
    6: 9,
    7: 12,
    8: 16,
}

PROFILE_CERTIFICATES = {
    (6, 6, 4, 4, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2): "3AGE30HE38G235HK7B4F704J7842754D1B1F001J1812C51D9A6I006I9862C56K",
    (6, 6, 5, 4, 4, 4, 4, 4, 4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1): "E20K11115555EI0I2222H999CJCD44446B0F6G016G0D6B0F3333HAA177778888",
    (6, 6, 5, 5, 4, 4, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1): "KAEHDCIC4F7H5132BG32BGI24F7251329990D00041705130JAE8666641785138",
    (6, 6, 6, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2): "127B44449IKI3333127B1HED92KDF2EF127A1H8A6666555512700C800JJ0GCG0",
    (6, 6, 6, 4, 4, 4, 4, 4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1): "72I47KI470G47634H2C1EJJ1HDCDF6392221EAA1B0G1B631828855550000F639",
    (6, 6, 6, 4, 4, 4, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1): "EIEI6666097D0K8D3GG23H2239723H2204F504F5047504851111B1BCA97AJ18C",
    (6, 6, 6, 4, 4, 4, 4, 4, 4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1): "006420110085J0B9ID642A11FD85HHB9CC642A21GG853333K7642721F785E7E9",
    (6, 6, 6, 4, 4, 4, 4, 4, 4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1): "DGEEFHFJ9H9955554444I2I288882222333366660A000A00DGCC777711B111B1",
    (6, 6, 6, 5, 4, 4, 4, 4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1): "883855557777G1B03333222H222HG1J066664444FFDDCCB09190K1I0E1AAE1I0",
    (7, 6, 4, 4, 4, 4, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1): "4IIK07CC31GGF2AF415E07503158H25H416E07603168B26D499907J031J8B2AD",
    (7, 6, 4, 4, 4, 4, 4, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1): "32043204320432049699G60GA6AAE6FFJ7B5D705D7K5E7B518HH110118CI18CI",
    (7, 6, 5, 4, 4, 4, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1): "B11HBD15G1180010249HC4C5G498J49I6666FDF5EAAE0000237K23752378237I",
    (7, 6, 6, 4, 4, 4, 4, 4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1): "9291888155551111300A3C0C300H300A2222JFIIBFBH7777G246ED46GK46ED46",
    (8, 6, 4, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2): "845C000017GG1K2JH453FEA3F7A3HD2314561EB617B61D26845C000097II9K2J",
    (8, 6, 4, 4, 4, 4, 4, 4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1): "E72H171GE7FF4736II2H111100004B36CA2CJAJG00004B3688285555D99D4K36",
    (8, 6, 4, 4, 4, 4, 4, 4, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1): "73K904B90DD96EFF738104BJ0A816G8G73H104I10AI16EH1732504250C256C25",
    (8, 6, 4, 4, 4, 4, 4, 4, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1): "2A47BG408H40JH4F2AI71110111033332AK7BDD08CC055552967EG608960E96F",
    (8, 6, 6, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2): "B4I822222A2ABJ38G4K5EE95GH15CH35D4KD66661111C73704I00F900F100J30",
}


def repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def codon_order() -> list[str]:
    return ["".join(parts) for parts in product(BASES, repeat=3)]


CODONS = codon_order()


def hamming1_edges(codons: list[str]) -> list[tuple[int, int]]:
    index = {codon: pos for pos, codon in enumerate(codons)}
    edges: list[tuple[int, int]] = []
    for codon in codons:
        left = index[codon]
        for pos in range(3):
            for base in BASES:
                if base == codon[pos]:
                    continue
                other = codon[:pos] + base + codon[pos + 1 :]
                right = index[other]
                if left < right:
                    edges.append((left, right))
    return edges


EDGES = hamming1_edges(CODONS)


def data_path() -> Path:
    return repo_root() / "tools" / "bio_reality" / "data" / "ncbi_genetic_codes.json"


def load_code_data(path: Path | None = None) -> dict[str, object]:
    source = path or data_path()
    return json.loads(source.read_text())


def validate_code_data(data: dict[str, object]) -> None:
    codons = data.get("codon_order")
    tables = data.get("tables")
    if codons != CODONS:
        raise ValueError("codon_order must match NCBI UCAG order")
    if not isinstance(tables, list) or not tables:
        raise ValueError("tables must be a non-empty list")
    seen: set[int] = set()
    for raw_table in tables:
        if not isinstance(raw_table, dict):
            raise ValueError("each table must be an object")
        table_id = raw_table.get("table_id")
        aa = raw_table.get("aa")
        starts = raw_table.get("starts")
        if not isinstance(table_id, int):
            raise ValueError("table_id must be an integer")
        if table_id in seen:
            raise ValueError(f"duplicate table_id {table_id}")
        seen.add(table_id)
        if not isinstance(aa, str) or len(aa) != 64:
            raise ValueError(f"table {table_id} aa row must have length 64")
        if not isinstance(starts, str) or len(starts) != 64:
            raise ValueError(f"table {table_id} starts row must have length 64")


def load_tables() -> tuple[list[dict[str, object]], dict[str, object]]:
    data = load_code_data()
    validate_code_data(data)
    tables = sorted(data["tables"], key=lambda table: int(table["table_id"]))  # type: ignore[index]
    return tables, data


def edge_count(labels: list[str], edges: Iterable[tuple[int, int]] = EDGES) -> int:
    return sum(1 for left, right in edges if labels[left] == labels[right])


def profile(labels: list[str]) -> tuple[int, ...]:
    return tuple(sorted(Counter(labels).values(), reverse=True))


def emax_for_profile(profile_key: tuple[int, ...]) -> tuple[int, bool, str]:
    missing = [size for size in profile_key if size not in SINGLE_BLOCK_EDGE_MAX]
    if missing:
        upper = sum(SINGLE_BLOCK_EDGE_MAX.get(size, size * 9 // 2) for size in profile_key)
        return upper, False, f"family sizes outside certified beta table: {sorted(set(missing))}"
    upper = sum(SINGLE_BLOCK_EDGE_MAX[size] for size in profile_key)
    if verify_profile_certificate(profile_key, upper):
        return upper, True, "exact_beta_sum_with_attainment_certificate"
    return upper, False, "missing profile attainment certificate"


def labels_for_profile(profile_key: tuple[int, ...]) -> list[int]:
    labels: list[int] = []
    for block_id, size in enumerate(profile_key):
        labels.extend([block_id] * size)
    return labels


def random_profile_assignment(profile_key: tuple[int, ...], rng: random.Random) -> list[int]:
    labels = labels_for_profile(profile_key)
    rng.shuffle(labels)
    return labels


def edge_count_int(labels: list[int], edges: Iterable[tuple[int, int]] = EDGES) -> int:
    return sum(1 for left, right in edges if labels[left] == labels[right])


def certificate_labels(encoded: str) -> list[str]:
    if len(encoded) != 64:
        raise ValueError("profile certificate must encode 64 vertices")
    return list(encoded)


def certificate_profile(encoded: str) -> tuple[int, ...]:
    return tuple(sorted(Counter(certificate_labels(encoded)).values(), reverse=True))


def certificate_edge_count(encoded: str) -> int:
    labels = certificate_labels(encoded)
    return sum(1 for left, right in EDGES if labels[left] == labels[right])


def verify_profile_certificate(profile_key: tuple[int, ...], e_max: int) -> bool:
    encoded = PROFILE_CERTIFICATES.get(profile_key)
    if encoded is None:
        return False
    return certificate_profile(encoded) == profile_key and certificate_edge_count(encoded) == e_max


def summarize_numeric(values: list[float]) -> dict[str, float]:
    ordered = sorted(values)
    n = len(ordered)
    if n == 0:
        raise ValueError("cannot summarize empty values")

    def pick(q: float) -> float:
        return ordered[int(q * (n - 1))]

    mean = sum(ordered) / n
    variance = sum((value - mean) * (value - mean) for value in ordered) / (n - 1) if n > 1 else 0.0
    return {
        "min": ordered[0],
        "p05": pick(0.05),
        "median": statistics.median(ordered),
        "p95": pick(0.95),
        "max": ordered[-1],
        "mean": mean,
        "sd": math.sqrt(variance),
    }


def null_distribution(profile_key: tuple[int, ...], draws: int, seed: int) -> list[int]:
    rng = random.Random(seed)
    return [edge_count_int(random_profile_assignment(profile_key, rng)) for _ in range(draws)]


def null_stats(null_values: list[int], observed: int) -> dict[str, object]:
    numeric = [float(value) for value in null_values]
    summary = summarize_numeric(numeric)
    sd = float(summary["sd"])
    z = 0.0 if sd == 0.0 else (observed - float(summary["mean"])) / sd
    p_ge = (1 + sum(1 for value in null_values if value >= observed)) / (len(null_values) + 1)
    return {
        "draws": len(null_values),
        "summary": summary,
        "z": z,
        "p_ge": p_ge,
    }


def table_labels(table: dict[str, object]) -> list[str]:
    aa = table.get("aa")
    if not isinstance(aa, str) or len(aa) != 64:
        raise ValueError(f"bad aa row for table {table.get('table_id')}")
    return list(aa)


def reassigned_codons(labels: list[str], standard: list[str]) -> list[str]:
    return [codon for codon, label, base_label in zip(CODONS, labels, standard) if label != base_label]


def analyze_tables(draws: int = DEFAULT_NULL_DRAWS) -> dict[str, object]:
    tables, data = load_tables()
    if len(tables) < MIN_DISTINCT_TABLES:
        return {
            "status": "data_gate_failed",
            "reason": "insufficient distinct code tables",
            "n_tables": len(tables),
        }

    standard_table = next((table for table in tables if table.get("table_id") == 1), None)
    if standard_table is None:
        return {
            "status": "data_gate_failed",
            "reason": "standard NCBI table 1 is absent",
            "n_tables": len(tables),
        }

    standard_labels = table_labels(standard_table)
    standard_e_in = edge_count(standard_labels)
    profile_cache: dict[tuple[int, ...], dict[str, object]] = {}
    unresolved_profiles: set[tuple[int, ...]] = set()
    rows: list[dict[str, object]] = []

    for index, table in enumerate(tables):
        labels = table_labels(table)
        profile_key = profile(labels)
        e_max, exact, method = emax_for_profile(profile_key)
        if not exact:
            unresolved_profiles.add(profile_key)
        if profile_key not in profile_cache:
            profile_cache[profile_key] = {
                "null": null_distribution(profile_key, draws, NULL_SEED + 7919 * len(profile_cache)),
                "e_max": e_max,
                "exact": exact,
                "method": method,
            }
        e_in = edge_count(labels)
        cached = profile_cache[profile_key]
        null_values = cached["null"]
        assert isinstance(null_values, list)
        tau = e_in / e_max if e_max else 1.0
        row = {
            "table_id": table["table_id"],
            "name": table.get("name", f"NCBI table {table['table_id']}"),
            "e_in": e_in,
            "e_max": e_max,
            "tau": tau,
            "profile": list(profile_key),
            "profile_exact": exact,
            "profile_method": method,
            "null": null_stats(null_values, e_in),
            "reassigned_codons": reassigned_codons(labels, standard_labels),
        }
        rows.append(row)

    taus = [float(row["tau"]) for row in rows]
    null_z = [float(row["null"]["z"]) for row in rows]  # type: ignore[index]
    null_p = [float(row["null"]["p_ge"]) for row in rows]  # type: ignore[index]
    unresolved_fraction = len(unresolved_profiles) / max(1, len(profile_cache))
    alt_rows = [row for row in rows if row["table_id"] != 1]
    alt_taus = [float(row["tau"]) for row in alt_rows]
    alt_z = [float(row["null"]["z"]) for row in alt_rows]  # type: ignore[index]
    alt_p = [float(row["null"]["p_ge"]) for row in alt_rows]  # type: ignore[index]

    checks = [
        check_row("codon_count", len(CODONS), 64),
        check_row("hamming1_edge_count", len(EDGES), 288),
        check_row("standard_code_e_in", standard_e_in, 69),
        check_row("distinct_table_count_at_least_gate", len(tables) >= MIN_DISTINCT_TABLES, True),
        check_row("all_tau_in_unit_interval", all(0.0 <= tau <= 1.0 for tau in taus), True),
        check_row("resolved_profile_fraction", unresolved_fraction <= 0.20, True),
    ]

    status, reason = verdict_from_metrics(
        len(tables),
        unresolved_fraction,
        min(alt_taus),
        statistics.median(alt_taus),
        min(alt_z),
        max(alt_p),
    )

    return {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "reason": reason,
        "table_source": {
            "path": str(data_path().relative_to(repo_root())),
            "source_url": data.get("source_url"),
            "snapshot_date": data.get("snapshot_date"),
            "version": data.get("version"),
        },
        "n_tables": len(tables),
        "code_ids": [table["table_id"] for table in tables],
        "standard": {
            "table_id": 1,
            "e_in": standard_e_in,
            "e_max": next(row["e_max"] for row in rows if row["table_id"] == 1),
            "tau": next(row["tau"] for row in rows if row["table_id"] == 1),
        },
        "tau_distribution_all": summarize_numeric(taus),
        "tau_distribution_alternative": summarize_numeric(alt_taus),
        "null_z_distribution_all": summarize_numeric(null_z),
        "null_z_distribution_alternative": summarize_numeric(alt_z),
        "profile_random_max_p_ge_alternative": max(alt_p),
        "profile_random_min_z_alternative": min(alt_z),
        "profile_count": len(profile_cache),
        "unresolved_profile_count": len(unresolved_profiles),
        "unresolved_profile_fraction": unresolved_fraction,
        "e_max_method": {
            "type": "exact_edge_isoperimetric_beta_sum",
            "single_block_edge_max": SINGLE_BLOCK_EDGE_MAX,
            "guarantee": "For observed profiles with all family sizes <=8, beta gives a profile upper bound and the embedded certificate reaches it.",
        },
        "null_seed": NULL_SEED,
        "null_draws": draws,
        "thresholds": {
            "near_max_floor": NEAR_MAX_FLOOR,
            "certified_median_tau_floor": CERTIFIED_MEDIAN_TAU_FLOOR,
            "certified_min_tau_floor": CERTIFIED_MIN_TAU_FLOOR,
            "certified_min_z": CERTIFIED_MIN_Z,
            "refuted_min_tau": REFUTED_MIN_TAU,
        },
        "checks": checks,
        "code_results": rows,
    }


def verdict_from_metrics(
    n_tables: int,
    unresolved_fraction: float,
    min_alt_tau: float,
    median_alt_tau: float,
    min_alt_z: float,
    max_alt_p: float,
) -> tuple[str, str]:
    if n_tables < MIN_DISTINCT_TABLES:
        return "data_gate_failed", "insufficient distinct code tables"
    if unresolved_fraction > 0.20:
        return "needs_derivation", "e_max was not resolved for more than 20 percent of observed profiles"
    near_max = min_alt_tau >= CERTIFIED_MIN_TAU_FLOOR and median_alt_tau >= CERTIFIED_MEDIAN_TAU_FLOOR
    null_beaten = min_alt_z >= CERTIFIED_MIN_Z and max_alt_p <= max(0.01, 5.0 * CERTIFIED_P_GE_FLOOR)
    if near_max and null_beaten:
        return "certified", "alternative codes stay near the profile maximum and beat the profile-random null across tables"
    if min_alt_tau < REFUTED_MIN_TAU or median_alt_tau < NEAR_MAX_FLOOR:
        return "refuted", "profile-normalized edge-hiding is not stably near the profile maximum"
    if min_alt_z <= 0.0 or max_alt_p >= 0.50:
        return "refuted", "real codes do not beat the profile-random null"
    return "coincidence", "nominal edge-hiding survives, but the declared near-max and null-separation margins are not both met"


def check_row(name: str, observed: object, expected: object) -> dict[str, object]:
    return {
        "name": name,
        "passed": observed == expected,
        "observed": observed,
        "expected": expected,
    }


def tiny_edges(width: int) -> list[tuple[int, int]]:
    return [(i, i + 1) for i in range(width - 1)]


def verdict_examples() -> dict[str, str]:
    examples = {}
    examples["certified"] = verdict_from_metrics(25, 0.0, 0.91, 0.95, 6.0, 0.0001)[0]
    examples["coincidence"] = verdict_from_metrics(25, 0.0, 0.90, 0.93, 4.0, 0.03)[0]
    examples["refuted_tau"] = verdict_from_metrics(25, 0.0, 0.70, 0.84, 6.0, 0.001)[0]
    examples["needs_derivation"] = verdict_from_metrics(25, 0.25, 0.91, 0.95, 6.0, 0.001)[0]
    examples["data_gate_failed"] = verdict_from_metrics(5, 0.0, 0.91, 0.95, 6.0, 0.001)[0]
    return examples


def selftest() -> int:
    tables, _data = load_tables()
    standard = next(table for table in tables if table["table_id"] == 1)
    standard_e_in = edge_count(table_labels(standard))

    toy_labels = ["A", "A", "B", "B"]
    toy_e_in = edge_count(toy_labels, tiny_edges(4))

    tiny_profile = (2, 2)
    tiny_assignments = [
        ["A", "A", "B", "B"],
        ["A", "B", "A", "B"],
        ["A", "B", "B", "A"],
        ["B", "A", "A", "B"],
        ["B", "A", "B", "A"],
        ["B", "B", "A", "A"],
    ]
    tiny_exact = max(edge_count(labels, tiny_edges(4)) for labels in tiny_assignments)

    main_payload = analyze_tables(draws=SELFTEST_NULL_DRAWS)
    taus = [float(row["tau"]) for row in main_payload["code_results"]]  # type: ignore[index]
    first_row = main_payload["code_results"][0]  # type: ignore[index]
    first_null = first_row["null"]  # type: ignore[index]
    examples = verdict_examples()
    exact_profiles = {
        profile(table_labels(table))
        for table in tables
    }

    checks = [
        check_row("standard_code_e_in", standard_e_in, 69),
        check_row("toy_code_e_in_by_hand", toy_e_in, 2),
        check_row("tiny_profile_exact_emax", tiny_exact, 2),
        check_row(
            "profile_certificates_reach_emax",
            all(verify_profile_certificate(key, emax_for_profile(key)[0]) for key in exact_profiles),
            True,
        ),
        check_row("tau_in_unit_interval", all(0.0 <= tau <= 1.0 for tau in taus), True),
        check_row("profile_random_null_has_z", isinstance(first_null["z"], float), True),
        check_row("profile_random_null_has_p_ge", 0.0 <= first_null["p_ge"] <= 1.0, True),
        check_row("verdict_certified_example", examples["certified"], "certified"),
        check_row("verdict_coincidence_example", examples["coincidence"], "coincidence"),
        check_row("verdict_refuted_example", examples["refuted_tau"], "refuted"),
        check_row("verdict_needs_derivation_example", examples["needs_derivation"], "needs_derivation"),
        check_row("verdict_data_gate_failed_example", examples["data_gate_failed"], "data_gate_failed"),
    ]
    ok = all(bool(check["passed"]) for check in checks)
    print(json.dumps({"ok": ok, "checks": checks}, sort_keys=True))
    return 0 if ok else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--selftest", action="store_true", help="run offline sanity checks")
    parser.add_argument("--null-draws", type=int, default=DEFAULT_NULL_DRAWS, help="profile-random samples per profile")
    args = parser.parse_args(argv)

    if args.selftest:
        return selftest()
    if args.null_draws <= 0:
        raise SystemExit("--null-draws must be positive")
    payload = analyze_tables(draws=args.null_draws)
    print(json.dumps(payload, sort_keys=False))
    status = payload.get("status")
    if status in {"certified", "coincidence"}:
        return 0
    if status == "refuted":
        return 2
    return 3


if __name__ == "__main__":
    raise SystemExit(main())

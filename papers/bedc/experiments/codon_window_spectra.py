#!/usr/bin/env python3
from __future__ import annotations

import collections
import collections.abc
import functools
import fractions
import http.client
import itertools
import json
import math
import pathlib
import random
import re
import time
import urllib.error
import urllib.request


NCBI_GENETIC_CODES_URL = "https://www.ncbi.nlm.nih.gov/Taxonomy/Utils/wprintgc.cgi?chapter=tgencodes"
NCBI_GENETIC_CODES_CACHE = pathlib.Path(__file__).with_name("cache") / "ncbi_genetic_codes.html"
BASE_BITS = {"T": "00", "C": "01", "A": "10", "G": "11"}
BASES = "TCAG"
MODULES = {
    "Stop/Trp": {"TAA", "TAG", "TGA", "TGG"},
    "Ile/Met": {"ATT", "ATC", "ATA", "ATG"},
    "Phe/Leu": {"TTT", "TTC", "TTA", "TTG", "CTT", "CTC", "CTA", "CTG"},
    "AGA/AGG": {"AGA", "AGG"},
}
WRR_CUBE = ("TAA", "TAG", "TGA", "TGG", "AAA", "AAG", "AGA", "AGG")
CORE_HOTSPOT = WRR_CUBE + ("ATA",)
ACTIVE_CORE = ("TAA", "TAG", "TGA", "AAA", "AGA", "AGG", "ATA")
FINEST_MODULE_PARTITION = (
    ("TAA", "TAG"),
    ("TGA",),
    ("AAA",),
    ("AGA", "AGG"),
    ("ATA",),
)
MODULE_NAMES = {
    ("TAA", "TAG"): "StopArm",
    ("TGA",): "UGA",
    ("AAA",): "AAA",
    ("AGA", "AGG"): "AGR",
    ("ATA",): "AUA",
}
MODULE_SYMBOLS = {
    "StopArm": "S",
    "UGA": "U",
    "AAA": "N",
    "AGR": "R",
    "AUA": "I",
}
LATENT_SS = (("*", "*"), ("W",), ("K",), ("S", "S"), ("I",))
LATENT_PARTIAL = (("*", "*"), ("*|W",), ("K",), ("R", "R"), ("I",))
LATENT_N = (("*", "*"), ("W",), ("N",), ("R", "R"), ("I",))
LATENT_Q_PARTIAL = (("Q|*", "Q|*"), ("*",), ("K",), ("R", "R"), ("I",))
TRANSFER_SQUARE = ("TGA", "TGG", "AGA", "AGG")
ARG_MAIN_BOX = ("CGT", "CGC", "CGA", "CGG")
ARG_SATELLITE = ("AGA", "AGG")
SER_SATELLITE = ("AGT", "AGC")
LABEL_NAMES = {
    "STOP": "*",
    "STOP *": "*",
    "Ter": "*",
    "Trp": "W",
    "Trp W": "W",
    "Gln": "Q",
    "Gln Q": "Q",
    "Glu": "E",
    "Glu E": "E",
    "Tyr": "Y",
    "Tyr Y": "Y",
    "Ser": "S",
    "Ser S": "S",
    "Lys": "K",
    "Lys K": "K",
    "Arg": "R",
    "Arg R": "R",
    "Ile": "I",
    "Ile I": "I",
    "Met": "M",
    "Met M": "M",
    "Gly": "G",
    "Gly G": "G",
    "Cys": "C",
    "Cys C": "C",
    "Ala": "A",
    "Ala A": "A",
    "Leu": "L",
    "Leu L": "L",
    "Asn": "N",
    "Asn N": "N",
    "Thr": "T",
    "Thr T": "T",
}
AMBIGUOUS_LABELS = {
    frozenset(("*", "W")): "*|W",
    frozenset(("Q", "*")): "Q|*",
    frozenset(("E", "*")): "E|*",
}


def fetch_ncbi_page() -> str:
    if NCBI_GENETIC_CODES_CACHE.exists():
        return NCBI_GENETIC_CODES_CACHE.read_text(encoding="utf-8", errors="replace")
    request = urllib.request.Request(
        NCBI_GENETIC_CODES_URL,
        headers={"User-Agent": "BEDC-codon-window-spectra", "Accept-Encoding": "identity"},
    )
    last_error: Exception | None = None
    for attempt in range(5):
        try:
            data = urllib.request.urlopen(request, timeout=30).read()
            break
        except http.client.IncompleteRead as exc:
            data = exc.partial
            break
        except (http.client.RemoteDisconnected, TimeoutError, urllib.error.URLError) as exc:
            last_error = exc
            if attempt == 4:
                if NCBI_GENETIC_CODES_CACHE.exists():
                    return NCBI_GENETIC_CODES_CACHE.read_text(encoding="utf-8", errors="replace")
                raise
            time.sleep(1 + attempt)
    else:
        raise RuntimeError("unreachable NCBI fetch state") from last_error
    text = data.decode("utf-8", "replace")
    NCBI_GENETIC_CODES_CACHE.parent.mkdir(parents=True, exist_ok=True)
    NCBI_GENETIC_CODES_CACHE.write_text(text, encoding="utf-8")
    return text


def parse_tables(text: str) -> dict[int, dict[str, str]]:
    heads = list(
        re.finditer(
            r"<h2>(\d+)\.\s*(.*?)\s*\(transl_table=(\d+)\)</h2>",
            text,
            re.S,
        )
    )
    tables: dict[int, dict[str, str]] = {}
    for index, head in enumerate(heads):
        table_id = int(head.group(3))
        start = head.end()
        end = heads[index + 1].start() if index + 1 < len(heads) else len(text)
        segment = text[start:end]
        pre = re.search(r"<pre>\s*(.*?)\s*</pre>", segment, re.S)
        if not pre:
            raise RuntimeError(f"missing table body for transl_table={table_id}")
        block = re.sub(r"<.*?>", "", pre.group(1))
        table: dict[str, str] = {}
        for codon, one_letter, _name in re.findall(
            r"([TCAG]{3})\s+([A-Z*])\s+([A-Za-z?]+)",
            block,
        ):
            table.setdefault(codon, one_letter)
        if len(table) != 64:
            raise RuntimeError(f"transl_table={table_id} has {len(table)} codons")
        tables[table_id] = table
    if len(tables) != 27:
        raise RuntimeError(f"expected 27 tables, found {len(tables)}")
    return tables


def normalize_difference_label(label: str) -> str:
    label = " ".join(label.split())
    if " or " in label:
        parts = tuple(normalize_difference_label(part) for part in label.split(" or "))
        return AMBIGUOUS_LABELS.get(frozenset(parts), "|".join(parts))
    return LABEL_NAMES.get(label, label)


def parse_difference_overrides(text: str) -> dict[int, dict[str, str]]:
    heads = list(
        re.finditer(
            r"<h2>(\d+)\.\s*(.*?)\s*\(transl_table=(\d+)\)</h2>",
            text,
            re.S,
        )
    )
    overrides: dict[int, dict[str, str]] = {}
    for index, head in enumerate(heads):
        table_id = int(head.group(3))
        start = head.end()
        end = heads[index + 1].start() if index + 1 < len(heads) else len(text)
        segment = text[start:end]
        match = re.search(r"<h4>Differences from the Standard Code:</h4>.*?<pre>(.*?)</pre>", segment, re.S)
        rows: dict[str, str] = {}
        if match:
            block = re.sub(r"<.*?>", "", match.group(1))
            for line in block.splitlines():
                columns = re.split(r"\s{2,}", line.strip())
                if len(columns) >= 3 and re.fullmatch(r"[UTCAG]{3}", columns[0]):
                    rows[columns[0].replace("U", "T")] = normalize_difference_label(columns[1])
        overrides[table_id] = rows
    return overrides


def partial_aware_tables(text: str) -> dict[int, dict[str, str]]:
    tables = parse_tables(text)
    overrides = parse_difference_overrides(text)
    adjusted = {table_id: table.copy() for table_id, table in tables.items()}
    for table_id, rows in overrides.items():
        adjusted[table_id].update(rows)
    return adjusted


def all_codons() -> list[str]:
    return ["".join(parts) for parts in itertools.product(BASES, repeat=3)]


def bits(codon: str) -> str:
    return "".join(BASE_BITS[base] for base in codon)


def codon_from_bits(word: str) -> str:
    inverse = {value: key for key, value in BASE_BITS.items()}
    return "".join(inverse[word[index : index + 2]] for index in (0, 2, 4))


def multiplicity_pattern(labels: list[str]) -> str:
    counts = sorted(collections.Counter(labels).values(), reverse=True)
    return "+".join(str(count) for count in counts)


def q1_spectrum(table: dict[str, str]) -> tuple[list[int], list[int]]:
    same_by_direction: list[int] = []
    diff_by_direction: list[int] = []
    for direction in range(6):
        same = 0
        diff = 0
        for point in itertools.product("01", repeat=6):
            if point[direction] == "1":
                continue
            neighbor = list(point)
            neighbor[direction] = "1"
            left = codon_from_bits("".join(point))
            right = codon_from_bits("".join(neighbor))
            if table[left] == table[right]:
                same += 1
            else:
                diff += 1
        same_by_direction.append(same)
        diff_by_direction.append(diff)
    return same_by_direction, diff_by_direction


def q1_random_baseline(table: dict[str, str]) -> dict[str, object]:
    sizes = collections.Counter(table.values())
    same_pairs = sum(size * (size - 1) // 2 for size in sizes.values())
    total_pairs = 64 * 63 // 2
    probability = fractions.Fraction(same_pairs, total_pairs)
    expected_edges = probability * 192
    observed_edges = sum(q1_spectrum(table)[0])
    ratio = fractions.Fraction(observed_edges, 1) / expected_edges
    ordered_same_pairs = sum(size * (size - 1) for size in sizes.values())
    ordered_same_triples = sum(size * (size - 1) * (size - 2) for size in sizes.values())
    ordered_same_quads = sum(size * (size - 1) * (size - 2) * (size - 3) for size in sizes.values())
    ordered_same_pair_squares = sum((size * (size - 1)) ** 2 for size in sizes.values())
    adjacent_edge_pairs = 64 * 15
    disjoint_edge_pairs = 192 * 191 // 2 - adjacent_edge_pairs
    adjacent_same_probability = fractions.Fraction(ordered_same_triples, 64 * 63 * 62)
    disjoint_same_probability = fractions.Fraction(
        ordered_same_quads + ordered_same_pairs * ordered_same_pairs - ordered_same_pair_squares,
        64 * 63 * 62 * 61,
    )
    variance = (
        192 * (probability - probability * probability)
        + 2
        * (
            adjacent_edge_pairs * (adjacent_same_probability - probability * probability)
            + disjoint_edge_pairs * (disjoint_same_probability - probability * probability)
        )
    )
    z_score = (float(observed_edges) - float(expected_edges)) / (float(variance) ** 0.5)
    histogram = collections.Counter(sizes.values())
    return {
        "degeneracy_histogram": dict(sorted(histogram.items())),
        "same_pair_count": same_pairs,
        "total_codon_pairs": total_pairs,
        "same_edge_probability": {
            "numerator": probability.numerator,
            "denominator": probability.denominator,
            "decimal": float(probability),
        },
        "expected_same_edges": {
            "numerator": expected_edges.numerator,
            "denominator": expected_edges.denominator,
            "decimal": float(expected_edges),
        },
        "observed_same_edges": observed_edges,
        "observed_to_expected_ratio": {
            "numerator": ratio.numerator,
            "denominator": ratio.denominator,
            "decimal": float(ratio),
        },
        "variance": {
            "numerator": variance.numerator,
            "denominator": variance.denominator,
            "decimal": float(variance),
        },
        "standard_deviation": float(variance) ** 0.5,
        "z_score": z_score,
    }


def nucleotide_substitution_spectrum(table: dict[str, str]) -> dict[str, object]:
    same = [0, 0, 0]
    diff = [0, 0, 0]
    for position in range(3):
        for prefix in itertools.product(BASES, repeat=2):
            other_positions = iter(prefix)
            codons = []
            for base in BASES:
                codon_parts = []
                for index in range(3):
                    codon_parts.append(base if index == position else next(other_positions))
                codons.append("".join(codon_parts))
                other_positions = iter(prefix)
            for left, right in itertools.combinations(codons, 2):
                if table[left] == table[right]:
                    same[position] += 1
                else:
                    diff[position] += 1
    return {"same_by_position": same, "diff_by_position": diff, "same_total": sum(same)}


def q2_faces(table: dict[str, str]) -> tuple[collections.Counter[str], dict[str, collections.Counter[str]], list[dict[str, object]]]:
    total: collections.Counter[str] = collections.Counter()
    geometry: dict[str, collections.Counter[str]] = collections.defaultdict(collections.Counter)
    three_one: list[dict[str, object]] = []
    for free in itertools.combinations(range(6), 2):
        fixed = [index for index in range(6) if index not in free]
        for values in itertools.product("01", repeat=4):
            word = [""] * 6
            for index, value in zip(fixed, values):
                word[index] = value
            vertices: list[str] = []
            local_words: list[str] = []
            for local in ("00", "01", "10", "11"):
                candidate = word.copy()
                candidate[free[0]] = local[0]
                candidate[free[1]] = local[1]
                vertices.append(codon_from_bits("".join(candidate)))
                local_words.append(local)
            labels = [table[codon] for codon in vertices]
            pattern = multiplicity_pattern(labels)
            total[pattern] += 1
            positions = [index // 2 for index in free]
            axes = [index % 2 for index in free]
            if positions[0] == positions[1]:
                geometry_key = "same_base"
            elif axes[0] == axes[1]:
                geometry_key = "cross_base_same_axis"
            else:
                geometry_key = "cross_base_mixed_axis"
            geometry[geometry_key][pattern] += 1
            if pattern == "3+1":
                counts = collections.Counter(labels)
                singleton_label = next(label for label, count in counts.items() if count == 1)
                singleton_index = next(index for index, label in enumerate(labels) if label == singleton_label)
                three_one.append(
                    {
                        "free_bits": free,
                        "vertices": vertices,
                        "labels": labels,
                        "singleton_corner": local_words[singleton_index],
                    }
                )
    return total, geometry, three_one


def complete_global_tiles(table: dict[str, str]) -> list[dict[str, object]]:
    label_sizes = collections.Counter(table.values())
    complete: list[dict[str, object]] = []
    for _total, _geometry, three_one in [q2_faces(table)]:
        for face in three_one:
            labels = list(face["labels"])
            counts = collections.Counter(labels)
            singleton_label = next(label for label, count in counts.items() if count == 1)
            tripleton_label = next(label for label, count in counts.items() if count == 3)
            if label_sizes[singleton_label] == 1 and label_sizes[tripleton_label] == 3:
                complete.append(
                    {
                        "vertices": face["vertices"],
                        "tripleton": tripleton_label,
                        "singleton": singleton_label,
                        "singleton_corner": face["singleton_corner"],
                    }
                )
    return complete


def q3_spectrum(table: dict[str, str]) -> tuple[collections.Counter[str], list[dict[str, object]]]:
    total: collections.Counter[str] = collections.Counter()
    cubes: list[dict[str, object]] = []
    for free in itertools.combinations(range(6), 3):
        fixed = [index for index in range(6) if index not in free]
        for values in itertools.product("01", repeat=3):
            word = [""] * 6
            for index, value in zip(fixed, values):
                word[index] = value
            vertices: list[str] = []
            for local in itertools.product("01", repeat=3):
                candidate = word.copy()
                for index, value in zip(free, local):
                    candidate[index] = value
                vertices.append(codon_from_bits("".join(candidate)))
            pattern = multiplicity_pattern([table[codon] for codon in vertices])
            total[pattern] += 1
            cubes.append({"free_bits": free, "vertices": vertices, "pattern": pattern})
    return total, cubes


def containing_cube_patterns(cubes: list[dict[str, object]], tile: set[str]) -> collections.Counter[str]:
    patterns: collections.Counter[str] = collections.Counter()
    for cube in cubes:
        if tile.issubset(set(cube["vertices"])):
            patterns[str(cube["pattern"])] += 1
    return patterns


def hamming_edges() -> list[tuple[str, str, int]]:
    edges: list[tuple[str, str, int]] = []
    for direction in range(6):
        for point in itertools.product("01", repeat=6):
            if point[direction] == "1":
                continue
            neighbor = list(point)
            neighbor[direction] = "1"
            edges.append((codon_from_bits("".join(point)), codon_from_bits("".join(neighbor)), direction))
    return edges


def component_sizes_for_codons(codons: list[str], edges: list[tuple[str, str, int]]) -> list[int]:
    codon_set = set(codons)
    adjacency: dict[str, set[str]] = {codon: set() for codon in codons}
    for left, right, _direction in edges:
        if left in codon_set and right in codon_set:
            adjacency[left].add(right)
            adjacency[right].add(left)
    seen: set[str] = set()
    sizes: list[int] = []
    for codon in codons:
        if codon in seen:
            continue
        stack = [codon]
        seen.add(codon)
        size = 0
        while stack:
            item = stack.pop()
            size += 1
            for neighbor in adjacency[item]:
                if neighbor not in seen:
                    seen.add(neighbor)
                    stack.append(neighbor)
        sizes.append(size)
    return sorted(sizes, reverse=True)


def synonymous_graph_summary(table: dict[str, str]) -> dict[str, object]:
    edges = hamming_edges()
    codons_by_class: dict[str, list[str]] = collections.defaultdict(list)
    for codon, label in table.items():
        codons_by_class[label].append(codon)
    class_rows: dict[str, dict[str, object]] = {}
    component_types: dict[str, list[str]] = collections.defaultdict(list)
    for label, codons in sorted(codons_by_class.items()):
        internal_edges = sum(1 for left, right, _direction in edges if table[left] == label and table[right] == label)
        boundary_degree = 6 * len(codons) - 2 * internal_edges
        component_sizes = component_sizes_for_codons(sorted(codons), edges)
        component_key = "+".join(str(size) for size in component_sizes)
        component_types[component_key].append(label)
        class_rows[label] = {
            "size": len(codons),
            "component_sizes": component_sizes,
            "internal_edges": internal_edges,
            "external_boundary_degree": boundary_degree,
        }
    return {
        "component_types": {key: sorted(value) for key, value in sorted(component_types.items())},
        "classes": class_rows,
    }


def class_adjacency_summary(table: dict[str, str]) -> dict[str, object]:
    inter_class: collections.Counter[tuple[str, str]] = collections.Counter()
    internal: collections.Counter[str] = collections.Counter()
    for left, right, _direction in hamming_edges():
        left_label = table[left]
        right_label = table[right]
        if left_label == right_label:
            internal[left_label] += 1
            continue
        pair = tuple(sorted((left_label, right_label)))
        inter_class[pair] += 1
    top_pairs = sorted(inter_class.items(), key=lambda item: (-item[1], item[0]))
    return {
        "inter_class_edges": {"-".join(pair): count for pair, count in sorted(inter_class.items())},
        "internal_edges": dict(sorted(internal.items())),
        "top_inter_class_edges": [
            {"pair": "-".join(pair), "count": count}
            for pair, count in top_pairs[:12]
        ],
        "control_pair_edges": {
            "I-M": inter_class[("I", "M")],
            "*-W": inter_class[("*", "W")],
        },
    }


def class_transition_summary(table: dict[str, str]) -> dict[str, object]:
    codons_by_class: dict[str, list[str]] = collections.defaultdict(list)
    for codon, label in table.items():
        codons_by_class[label].append(codon)
    counts: dict[str, dict[str, int]] = {}
    probabilities: dict[str, dict[str, dict[str, object]]] = {}
    for label, codons in sorted(codons_by_class.items()):
        row: collections.Counter[str] = collections.Counter()
        for codon in codons:
            word = bits(codon)
            for direction in range(6):
                neighbor = list(word)
                neighbor[direction] = "1" if word[direction] == "0" else "0"
                row[table[codon_from_bits("".join(neighbor))]] += 1
        denominator = 6 * len(codons)
        counts[label] = dict(sorted(row.items()))
        probabilities[label] = {
            target: {
                "numerator": count,
                "denominator": denominator,
                "decimal": count / denominator,
            }
            for target, count in sorted(row.items())
        }
    return {
        "counts": counts,
        "probabilities": probabilities,
    }


def q4_spectrum(table: dict[str, str]) -> tuple[dict[str, object], list[dict[str, object]]]:
    max_distribution: collections.Counter[int] = collections.Counter()
    complete_six: collections.Counter[str] = collections.Counter()
    cubes: list[dict[str, object]] = []
    class_sizes = collections.Counter(table.values())
    for free in itertools.combinations(range(6), 4):
        fixed = [index for index in range(6) if index not in free]
        for values in itertools.product("01", repeat=2):
            word = [""] * 6
            for index, value in zip(fixed, values):
                word[index] = value
            vertices: list[str] = []
            for local in itertools.product("01", repeat=4):
                candidate = word.copy()
                for index, value in zip(free, local):
                    candidate[index] = value
                vertices.append(codon_from_bits("".join(candidate)))
            counts = collections.Counter(table[codon] for codon in vertices)
            max_distribution[max(counts.values())] += 1
            for label, count in counts.items():
                if count == 6 and class_sizes[label] == 6:
                    complete_six[label] += 1
            cubes.append(
                {
                    "free_bits": free,
                    "vertices": tuple(vertices),
                    "pattern": multiplicity_pattern([table[codon] for codon in vertices]),
                    "class_counts": dict(sorted(counts.items())),
                }
            )
    return {
        "max_class_size_distribution": dict(sorted(max_distribution.items())),
        "complete_six_class_occurrences": dict(sorted(complete_six.items())),
    }, cubes


def containing_q4_neighborhoods(cubes: list[dict[str, object]], tile: set[str]) -> list[dict[str, object]]:
    neighborhoods: list[dict[str, object]] = []
    for cube in cubes:
        if tile.issubset(set(cube["vertices"])):
            neighborhoods.append(
                {
                    "free_bits": cube["free_bits"],
                    "pattern": cube["pattern"],
                    "class_counts": cube["class_counts"],
                    "vertices": cube["vertices"],
                }
            )
    neighborhoods.sort(key=lambda item: item["free_bits"])
    return neighborhoods


def q5_control_half_cube_summary(table: dict[str, str]) -> dict[str, object]:
    control_codons = MODULES["Ile/Met"] | MODULES["Stop/Trp"]
    shared_fixed_bits: list[dict[str, object]] = []
    control_words = {codon: bits(codon) for codon in control_codons}
    for direction in range(6):
        values = {word[direction] for word in control_words.values()}
        if len(values) == 1:
            value = next(iter(values))
            shared_fixed_bits.append({"bit": direction, "value": value})
    if len(shared_fixed_bits) != 1:
        raise RuntimeError(f"expected a unique shared fixed bit, found {shared_fixed_bits}")
    fixed = shared_fixed_bits[0]
    vertices = [
        codon
        for codon in all_codons()
        if bits(codon)[fixed["bit"]] == fixed["value"]
    ]
    counts = collections.Counter(table[codon] for codon in vertices)
    return {
        "shared_fixed_bits": shared_fixed_bits,
        "vertices": tuple(sorted(vertices)),
        "class_counts": dict(sorted(counts.items(), key=lambda item: (-item[1], item[0]))),
        "control_class_counts": {
            "Stop": counts["*"],
            "I": counts["I"],
            "W": counts["W"],
            "M": counts["M"],
        },
    }


def state_components(tables: dict[int, dict[str, str]], codons: tuple[str, ...]) -> dict[str, object]:
    states: dict[tuple[str, ...], list[int]] = collections.defaultdict(list)
    for table_id, table in sorted(tables.items()):
        states[tuple(table[codon] for codon in codons)].append(table_id)
    nodes = list(states)
    adjacency: dict[int, set[int]] = {index: set() for index in range(len(nodes))}
    for left, right in itertools.combinations(range(len(nodes)), 2):
        distance = sum(a != b for a, b in zip(nodes[left], nodes[right]))
        if distance == 1:
            adjacency[left].add(right)
            adjacency[right].add(left)
    seen: set[int] = set()
    components: list[list[int]] = []
    for index in range(len(nodes)):
        if index in seen:
            continue
        stack = [index]
        seen.add(index)
        component: list[int] = []
        while stack:
            item = stack.pop()
            component.append(item)
            for neighbor in adjacency[item]:
                if neighbor not in seen:
                    seen.add(neighbor)
                    stack.append(neighbor)
        components.append(component)
    components.sort(key=lambda component: (-len(component), min(min(states[nodes[index]]) for index in component)))
    return {
        "distinct_state_count": len(states),
        "standard_state_tables": states[tuple(tables[1][codon] for codon in codons)],
        "component_count": len(components),
        "component_sizes": sorted([len(component) for component in components], reverse=True),
        "components": [[states[nodes[index]] for index in component] for component in components],
    }


def set_partitions(items: tuple[str, ...]) -> list[tuple[tuple[str, ...], ...]]:
    if not items:
        return [()]
    first, *rest_items = items
    rest = set_partitions(tuple(rest_items))
    partitions: list[tuple[tuple[str, ...], ...]] = []
    for partition in rest:
        partitions.append(((first,),) + partition)
        for index in range(len(partition)):
            merged = tuple(sorted((first,) + partition[index], key=items.index))
            blocks = list(partition)
            blocks[index] = merged
            blocks.sort(key=lambda block: items.index(block[0]))
            partitions.append(tuple(blocks))
    unique: dict[tuple[tuple[str, ...], ...], None] = {}
    for partition in partitions:
        normalized = tuple(sorted(partition, key=lambda block: items.index(block[0])))
        unique[normalized] = None
    return list(unique)


def module_distance(left: tuple[str, ...], right: tuple[str, ...], partition: tuple[tuple[int, ...], ...]) -> tuple[int, int | None]:
    changed: list[int] = []
    for index, block in enumerate(partition):
        if any(left[position] != right[position] for position in block):
            changed.append(index)
    if len(changed) == 1:
        return 1, changed[0]
    return len(changed), None


def graph_from_partition(nodes: list[tuple[str, ...]], partition: tuple[tuple[int, ...], ...]) -> tuple[dict[int, set[int]], collections.Counter[int]]:
    adjacency: dict[int, set[int]] = {index: set() for index in range(len(nodes))}
    edge_labels: collections.Counter[int] = collections.Counter()
    for left, right in itertools.combinations(range(len(nodes)), 2):
        distance, block = module_distance(nodes[left], nodes[right], partition)
        if distance == 1 and block is not None:
            adjacency[left].add(right)
            adjacency[right].add(left)
            edge_labels[block] += 1
    return adjacency, edge_labels


def connected_components(adjacency: dict[int, set[int]]) -> list[list[int]]:
    seen: set[int] = set()
    components: list[list[int]] = []
    for index in adjacency:
        if index in seen:
            continue
        stack = [index]
        seen.add(index)
        component: list[int] = []
        while stack:
            item = stack.pop()
            component.append(item)
            for neighbor in adjacency[item]:
                if neighbor not in seen:
                    seen.add(neighbor)
                    stack.append(neighbor)
        components.append(sorted(component))
    return components


def graph_distances(adjacency: dict[int, set[int]], source: int) -> dict[int, int]:
    distances = {source: 0}
    queue = collections.deque([source])
    while queue:
        item = queue.popleft()
        for neighbor in sorted(adjacency[item]):
            if neighbor in distances:
                continue
            distances[neighbor] = distances[item] + 1
            queue.append(neighbor)
    return distances


def active_module_partition_summary(tables: dict[int, dict[str, str]]) -> dict[str, object]:
    states: dict[tuple[str, ...], list[int]] = collections.defaultdict(list)
    for table_id, table in sorted(tables.items()):
        states[tuple(table[codon] for codon in ACTIVE_CORE)].append(table_id)
    nodes = list(states)
    active_index = {codon: index for index, codon in enumerate(ACTIVE_CORE)}
    partitions = set_partitions(ACTIVE_CORE)
    connected: list[tuple[tuple[str, ...], ...]] = []
    for partition in partitions:
        indexed = tuple(tuple(active_index[codon] for codon in block) for block in partition)
        adjacency, _edge_labels = graph_from_partition(nodes, indexed)
        if len(connected_components(adjacency)) == 1:
            connected.append(partition)
    max_blocks = max(len(partition) for partition in connected)
    finest = [partition for partition in connected if len(partition) == max_blocks]
    finest_partition = finest[0]
    indexed_finest = tuple(tuple(active_index[codon] for codon in block) for block in finest_partition)
    adjacency, edge_labels = graph_from_partition(nodes, indexed_finest)
    standard_state = tuple(tables[1][codon] for codon in ACTIVE_CORE)
    standard_index = nodes.index(standard_state)
    source_distances = graph_distances(adjacency, standard_index)
    distance_distribution = collections.Counter(source_distances.values())
    diameter = 0
    for index in range(len(nodes)):
        distances = graph_distances(adjacency, index)
        diameter = max(diameter, max(distances.values()))
    return {
        "active_codons": ACTIVE_CORE,
        "bell_count": len(partitions),
        "connected_partition_count": len(connected),
        "finest_partition_count": len(finest),
        "finest_partition": finest_partition,
        "module_edge_count": sum(edge_labels.values()),
        "module_edge_counts": {
            MODULE_NAMES[finest_partition[index]]: edge_labels[index]
            for index in range(len(finest_partition))
        },
        "standard_degree": len(adjacency[standard_index]),
        "standard_distance_distribution": dict(sorted(distance_distribution.items())),
        "diameter": diameter,
    }


def satisfies_module_grammar(pattern: set[str]) -> bool:
    return (
        ("R" not in pattern or "U" in pattern)
        and ("I" not in pattern or "U" in pattern)
        and ("N" not in pattern or "R" in pattern)
        and not ("S" in pattern and "I" in pattern)
    )


def module_activation_summary(tables: dict[int, dict[str, str]]) -> dict[str, object]:
    standard = tables[1]
    module_order = tuple(MODULE_SYMBOLS[MODULE_NAMES[block]] for block in FINEST_MODULE_PARTITION)
    pattern_tables: dict[tuple[str, ...], list[int]] = collections.defaultdict(list)
    for table_id, table in sorted(tables.items()):
        active: list[str] = []
        for block in FINEST_MODULE_PARTITION:
            if any(table[codon] != standard[codon] for codon in block):
                active.append(MODULE_SYMBOLS[MODULE_NAMES[block]])
        pattern_tables[tuple(active)].append(table_id)
    solutions = [
        tuple(symbol for symbol in module_order if symbol in active)
        for active in itertools.chain.from_iterable(
            itertools.combinations(module_order, count) for count in range(len(module_order) + 1)
        )
        if satisfies_module_grammar(set(active))
    ]
    solutions.sort(key=lambda pattern: (len(pattern), pattern))
    observed = sorted(pattern_tables, key=lambda pattern: (len(pattern), pattern))
    return {
        "module_order": module_order,
        "observed_pattern_count": len(pattern_tables),
        "observed_patterns": {
            "+".join(pattern) if pattern else "none": pattern_tables[pattern]
            for pattern in observed
        },
        "grammar_solution_count": len(solutions),
        "grammar_solutions": ["+".join(pattern) if pattern else "none" for pattern in solutions],
        "exact_match": set(observed) == set(solutions),
        "constraints": {
            "R_implies_U": all("U" in pattern for pattern in pattern_tables if "R" in pattern),
            "I_implies_U": all("U" in pattern for pattern in pattern_tables if "I" in pattern),
            "N_implies_R": all("R" in pattern for pattern in pattern_tables if "N" in pattern),
            "S_disjoint_I": all(not ("S" in pattern and "I" in pattern) for pattern in pattern_tables),
        },
    }


def module_state(table: dict[str, str]) -> tuple[tuple[str, ...], ...]:
    return tuple(tuple(table[codon] for codon in block) for block in FINEST_MODULE_PARTITION)


def module_value_key(value: tuple[str, ...]) -> str:
    return value[0] if len(value) == 1 else "(" + ",".join(value) + ")"


def generated_module_value_states() -> dict[str, list[tuple[tuple[str, ...], ...]]]:
    std_s = (("*", "*"),)
    std_u = (("*",),)
    std_n = (("K",),)
    std_r = (("R", "R"),)
    std_i = (("I",),)
    branch_a_s = [("*", "*"), ("Q", "Q"), ("*", "Q"), ("*", "L"), ("Y", "Y"), ("E", "E"), ("*", "W")]
    branch_b_u = [("C",), ("G",)]
    branch_c_s = [("Q", "Q"), ("Q|*", "Q|*")]
    branch_d = [
        (("*", "*"), ("W",), ("K",), ("R", "R"), ("I",)),
        (("*", "*"), ("W",), ("K",), ("R", "R"), ("M",)),
        (("E|*", "E|*"), ("W",), ("K",), ("R", "R"), ("I",)),
        (("*", "*"), ("W",), ("K",), ("*", "*"), ("M",)),
        (("*", "*"), ("W",), ("K",), ("S", "S"), ("M",)),
        (("*", "*"), ("W",), ("K",), ("G", "G"), ("M",)),
        (("*", "*"), ("W",), ("N",), ("S", "S"), ("I",)),
        (("Y", "*"), ("W",), ("N",), ("S", "S"), ("I",)),
        (("*", "*"), ("W",), ("N",), ("S", "S"), ("M",)),
        (("*", "*"), ("W",), ("K",), ("S", "K"), ("I",)),
        (("Y", "*"), ("W",), ("K",), ("S", "K"), ("I",)),
    ]
    return {
        "U_star_stoparm": [(s, std_u[0], std_n[0], std_r[0], std_i[0]) for s in branch_a_s],
        "U_cg_pure": [(std_s[0], u, std_n[0], std_r[0], std_i[0]) for u in branch_b_u],
        "U_partial_boundary": [(s, ("*|W",), std_n[0], std_r[0], std_i[0]) for s in branch_c_s],
        "U_w_deep": branch_d,
    }


def module_value_grammar_summary(tables: dict[int, dict[str, str]]) -> dict[str, object]:
    state_tables: dict[tuple[tuple[str, ...], ...], list[int]] = collections.defaultdict(list)
    for table_id, table in sorted(tables.items()):
        state_tables[module_state(table)].append(table_id)
    observed = set(state_tables)
    generated_by_branch = generated_module_value_states()
    generated = set(itertools.chain.from_iterable(generated_by_branch.values()))
    value_sets: dict[str, set[tuple[str, ...]]] = {name: set() for name in MODULE_SYMBOLS.values()}
    for state in observed:
        for name, value in zip(MODULE_SYMBOLS.values(), state):
            value_sets[name].add(value)
    constraints = {
        "R_nonstandard_implies_U_W": all(state[1] == ("W",) for state in observed if state[3] != ("R", "R")),
        "I_M_implies_U_W_and_S_standard": all(
            state[1] == ("W",) and state[0] == ("*", "*") for state in observed if state[4] == ("M",)
        ),
        "N_N_implies_U_W_and_R_SS": all(
            state[1] == ("W",) and state[3] == ("S", "S") for state in observed if state[2] == ("N",)
        ),
        "R_stop_or_gly_implies_I_M_S_standard_N_K": all(
            state[4] == ("M",) and state[0] == ("*", "*") and state[2] == ("K",)
            for state in observed
            if state[3] in (("*", "*"), ("G", "G"))
        ),
        "R_SK_implies_I_I_N_K_U_W": all(
            state[4] == ("I",) and state[2] == ("K",) and state[1] == ("W",)
            for state in observed
            if state[3] == ("S", "K")
        ),
    }
    return {
        "distinct_state_count": len(observed),
        "module_value_counts": {name: len(values) for name, values in value_sets.items()},
        "module_values": {
            name: sorted(module_value_key(value) for value in values)
            for name, values in value_sets.items()
        },
        "branch_counts": {name: len(states) for name, states in generated_by_branch.items()},
        "generated_state_count": len(generated),
        "exact_match": observed == generated,
        "constraints": constraints,
        "state_tables": {
            "/".join(module_value_key(value) for value in state): table_ids
            for state, table_ids in sorted(state_tables.items(), key=lambda item: (item[0], item[1]))
        },
    }


def tile_pattern_summary(tables: dict[int, dict[str, str]]) -> dict[str, object]:
    ile_met = ("ATT", "ATC", "ATA", "ATG")
    stop_trp = ("TAA", "TAG", "TGA", "TGG")
    ile_patterns: collections.Counter[tuple[str, ...]] = collections.Counter()
    stop_patterns: collections.Counter[tuple[str, ...]] = collections.Counter()
    ile_tables: dict[tuple[str, ...], list[int]] = collections.defaultdict(list)
    stop_tables: dict[tuple[str, ...], list[int]] = collections.defaultdict(list)
    for table_id, table in sorted(tables.items()):
        ile_pattern = tuple(table[codon] for codon in ile_met)
        stop_pattern = tuple(table[codon] for codon in stop_trp)
        ile_patterns[ile_pattern] += 1
        stop_patterns[stop_pattern] += 1
        ile_tables[ile_pattern].append(table_id)
        stop_tables[stop_pattern].append(table_id)
    return {
        "ile_met_patterns": {
            "/".join(pattern): {"count": count, "tables": ile_tables[pattern]}
            for pattern, count in sorted(ile_patterns.items(), key=lambda item: (-item[1], item[0]))
        },
        "stop_trp_patterns": {
            "/".join(pattern): {"count": count, "tables": stop_tables[pattern]}
            for pattern, count in sorted(stop_patterns.items(), key=lambda item: (-item[1], item[0]))
        },
    }


def reassignment_concentration_summary(tables: dict[int, dict[str, str]]) -> dict[str, object]:
    standard = tables[1]
    diffs: list[tuple[int, str, str, str]] = []
    for table_id, table in sorted(tables.items()):
        if table_id == 1:
            continue
        for codon in all_codons():
            if table[codon] != standard[codon]:
                diffs.append((table_id, codon, standard[codon], table[codon]))
    codon_counts: collections.Counter[str] = collections.Counter(codon for _table_id, codon, _old, _new in diffs)
    codon_targets: dict[str, collections.Counter[str]] = collections.defaultdict(collections.Counter)
    for _table_id, codon, _old, new in diffs:
        codon_targets[codon][new] += 1

    half_cube_counts = collections.Counter(bits(codon)[1] for _table_id, codon, _old, _new in diffs)
    control_half_cube_codons = [codon for codon in sorted(codon_counts) if bits(codon)[1] == "0"]
    outside_control_half_cube_codons = [codon for codon in sorted(codon_counts) if bits(codon)[1] == "1"]

    refined_modules = {
        "Stop/Trp_X2": {"TAA", "TAG", "TGA"},
        "AGR": {"AGA", "AGG"},
        "Ile/Met_leaf": {"ATA"},
        "AAA_leaf": {"AAA"},
        "rare_stop_insertions": {"TCA", "TTA"},
        "CUN_Leu": {"CTT", "CTC", "CTA", "CTG"},
    }
    refined_counts: dict[str, int] = {}
    for name, codons in refined_modules.items():
        refined_counts[name] = sum(codon_counts[codon] for codon in codons)

    reassigned_codons = sorted(codon_counts)
    reassigned_set = set(reassigned_codons)
    induced_edges = [
        (left, right)
        for left, right, _direction in hamming_edges()
        if left in reassigned_set and right in reassigned_set
    ]
    adjacency: dict[str, set[str]] = {codon: set() for codon in reassigned_codons}
    for left, right in induced_edges:
        adjacency[left].add(right)
        adjacency[right].add(left)
    seen: set[str] = set()
    components: list[list[str]] = []
    for codon in reassigned_codons:
        if codon in seen:
            continue
        stack = [codon]
        seen.add(codon)
        component: list[str] = []
        while stack:
            item = stack.pop()
            component.append(item)
            for neighbor in adjacency[item]:
                if neighbor not in seen:
                    seen.add(neighbor)
                    stack.append(neighbor)
        components.append(sorted(component))
    components.sort(key=lambda component: (-len(component), component))

    q1_by_table = {table_id: q1_spectrum(table)[0] for table_id, table in sorted(tables.items())}
    q1_totals = {table_id: sum(counts) for table_id, counts in q1_by_table.items()}
    q1_direction_ranges = []
    for direction in range(6):
        values = [counts[direction] for counts in q1_by_table.values()]
        q1_direction_ranges.append(
            {
                "min": min(values),
                "max": max(values),
                "mean": sum(values) / len(values),
            }
        )

    nucleotide_by_table = {
        table_id: nucleotide_substitution_spectrum(table)
        for table_id, table in sorted(tables.items())
    }
    nucleotide_totals = [row["same_total"] for row in nucleotide_by_table.values()]
    nucleotide_position_values = [
        [row["same_by_position"][position] for row in nucleotide_by_table.values()]
        for position in range(3)
    ]
    nucleotide_position_stats = [
        {
            "min": min(values),
            "max": max(values),
            "mean": sum(values) / len(values),
        }
        for values in nucleotide_position_values
    ]

    return {
        "distinct_reassigned_codon_count": len(reassigned_codons),
        "distinct_reassigned_codons": reassigned_codons,
        "weighted_event_count": len(diffs),
        "codon_counts": {
            codon: {
                "standard": standard[codon],
                "count": codon_counts[codon],
                "targets": dict(sorted(codon_targets[codon].items())),
            }
            for codon in sorted(codon_counts, key=lambda codon: (-codon_counts[codon], codon))
        },
        "control_half_cube": {
            "fixed_bit": 1,
            "fixed_value": "0",
            "inside_event_count": half_cube_counts["0"],
            "outside_event_count": half_cube_counts["1"],
            "inside_fraction": half_cube_counts["0"] / len(diffs),
            "inside_codons": control_half_cube_codons,
            "outside_codons": outside_control_half_cube_codons,
        },
        "refined_module_counts": refined_counts,
        "reassigned_codon_graph": {
            "node_count": len(reassigned_codons),
            "edge_count": len(induced_edges),
            "component_count": len(components),
            "component_sizes": [len(component) for component in components],
            "edges": induced_edges,
        },
        "q1_all_tables": {
            "min": min(q1_totals.values()),
            "max": max(q1_totals.values()),
            "mean": sum(q1_totals.values()) / len(q1_totals),
            "distribution": dict(sorted(collections.Counter(q1_totals.values()).items())),
            "direction_ranges": q1_direction_ranges,
        },
        "nucleotide_substitution_all_tables": {
            "same_total_min": min(nucleotide_totals),
            "same_total_max": max(nucleotide_totals),
            "same_total_mean": sum(nucleotide_totals) / len(nucleotide_totals),
            "same_by_position": nucleotide_position_stats,
        },
    }


def subcube_vertices(free_bits: tuple[int, ...], fixed_values: tuple[str, ...]) -> tuple[str, ...]:
    fixed = [index for index in range(6) if index not in free_bits]
    word = [""] * 6
    for index, value in zip(fixed, fixed_values):
        word[index] = value
    vertices: list[str] = []
    for local in itertools.product("01", repeat=len(free_bits)):
        candidate = word.copy()
        for index, value in zip(free_bits, local):
            candidate[index] = value
        vertices.append(codon_from_bits("".join(candidate)))
    return tuple(vertices)


def fixed_conditions(free_bits: tuple[int, ...], fixed_values: tuple[str, ...]) -> tuple[tuple[int, str], ...]:
    fixed = [index for index in range(6) if index not in free_bits]
    return tuple(zip(fixed, fixed_values))


def gf2_rank(columns: list[int]) -> int:
    basis: dict[int, int] = {}
    for column in columns:
        vector = column
        while vector:
            pivot = vector.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = vector
                break
            vector ^= basis[pivot]
    return len(basis)


def cubical_complex_summary(vertices: set[str]) -> dict[str, object]:
    cells_by_dim: dict[int, list[dict[str, object]]] = {dimension: [] for dimension in range(7)}
    cell_keys_by_dim: dict[int, dict[tuple[tuple[int, ...], tuple[str, ...]], int]] = {
        dimension: {} for dimension in range(7)
    }
    for dimension in range(0, 7):
        for free in itertools.combinations(range(6), dimension):
            for values in itertools.product("01", repeat=6 - dimension):
                cell_vertices = subcube_vertices(free, values)
                if set(cell_vertices) <= vertices:
                    key = (free, values)
                    cell_keys_by_dim[dimension][key] = len(cells_by_dim[dimension])
                    cells_by_dim[dimension].append(
                        {
                            "free_bits": free,
                            "fixed_conditions": fixed_conditions(free, values),
                            "vertices": cell_vertices,
                        }
                    )

    def facet_key(
        free_bits: tuple[int, ...],
        fixed_values: tuple[str, ...],
        fixed_bit: int,
        fixed_value: str,
    ) -> tuple[tuple[int, ...], tuple[str, ...]]:
        old_fixed = [index for index in range(6) if index not in free_bits]
        word = [""] * 6
        for index, value in zip(old_fixed, fixed_values):
            word[index] = value
        word[fixed_bit] = fixed_value
        new_free = tuple(index for index in free_bits if index != fixed_bit)
        new_fixed = [index for index in range(6) if index not in new_free]
        return new_free, tuple(word[index] for index in new_fixed)

    boundary_ranks: dict[int, int] = {}
    for dimension in range(1, 7):
        row_index = cell_keys_by_dim[dimension - 1]
        columns: list[int] = []
        for cell in cells_by_dim[dimension]:
            mask = 0
            free_bits = cell["free_bits"]
            fixed_values = tuple(value for _index, value in cell["fixed_conditions"])
            for bit in free_bits:
                for value in ("0", "1"):
                    key = facet_key(free_bits, fixed_values, bit, value)
                    mask ^= 1 << row_index[key]
            columns.append(mask)
        boundary_ranks[dimension] = gf2_rank(columns)

    f_vector = tuple(len(cells_by_dim[dimension]) for dimension in range(7))
    max_dimension = max((dimension for dimension, cells in cells_by_dim.items() if cells), default=0)
    betti: list[int] = []
    for dimension in range(max_dimension + 1):
        boundary_rank = boundary_ranks.get(dimension, 0)
        coboundary_rank = boundary_ranks.get(dimension + 1, 0)
        betti.append(f_vector[dimension] - boundary_rank - coboundary_rank)
    euler = sum(((-1) ** dimension) * count for dimension, count in enumerate(f_vector))
    return {
        "f_vector": f_vector,
        "max_dimension": max_dimension,
        "euler_characteristic": euler,
        "boundary_ranks": dict(sorted(boundary_ranks.items())),
        "betti": tuple(betti),
        "cells_by_dimension": {
            dimension: [
                {
                    "free_bits": cell["free_bits"],
                    "vertices": cell["vertices"],
                }
                for cell in cells
            ]
            for dimension, cells in cells_by_dim.items()
            if cells
        },
    }


def simplicial_reduced_betti(face_masks: set[int], vertex_count: int) -> dict[int, int]:
    if not face_masks:
        return {-1: 1}
    faces_by_dim: dict[int, list[int]] = {}
    for mask in face_masks:
        dimension = mask.bit_count() - 1
        faces_by_dim.setdefault(dimension, []).append(mask)
    max_dimension = max(faces_by_dim)
    boundary_ranks: dict[int, int] = {}
    for dimension in range(1, max_dimension + 1):
        domain_faces = sorted(faces_by_dim.get(dimension, []))
        row_faces = {face: index for index, face in enumerate(sorted(faces_by_dim.get(dimension - 1, [])))}
        columns = []
        for face in domain_faces:
            column = 0
            for vertex in range(vertex_count):
                if face & (1 << vertex):
                    boundary_face = face ^ (1 << vertex)
                    column ^= 1 << row_faces[boundary_face]
            columns.append(column)
        boundary_ranks[dimension] = gf2_rank(columns)
    reduced: dict[int, int] = {}
    for dimension in range(max_dimension + 1):
        chain_count = len(faces_by_dim.get(dimension, []))
        boundary_rank = boundary_ranks.get(dimension, 0)
        coboundary_rank = boundary_ranks.get(dimension + 1, 0)
        betti = chain_count - boundary_rank - coboundary_rank
        if dimension == 0:
            betti -= 1
        if betti:
            reduced[dimension] = betti
    return reduced


def edge_isoperimetric_max_edges(dimension: int, size: int) -> int:
    memo: dict[tuple[int, int], int] = {}

    def recur(dim: int, count: int) -> int:
        key = (dim, count)
        if key in memo:
            return memo[key]
        if count <= 1 or dim == 0:
            memo[key] = 0
            return 0
        half = 1 << (dim - 1)
        lower = max(0, count - half)
        upper = min(half, count)
        value = max(
            recur(dim - 1, split)
            + recur(dim - 1, count - split)
            + min(split, count - split)
            for split in range(lower, upper + 1)
        )
        memo[key] = value
        return value

    return recur(dimension, size)


@functools.lru_cache(maxsize=None)
def median_codon(left: str, middle: str, right: str) -> str:
    return codon_from_bits(
        "".join(
            "1" if (int(a) + int(b) + int(c)) >= 2 else "0"
            for a, b, c in zip(bits(left), bits(middle), bits(right))
        )
    )


def median_closure(codons: set[str]) -> tuple[set[str], list[dict[str, object]]]:
    closed = set(codons)
    stages: list[dict[str, object]] = []
    stage_index = 0
    while True:
        additions = {
            median_codon(left, middle, right)
            for left, middle, right in itertools.combinations_with_replacement(sorted(closed), 3)
        } - closed
        if not additions:
            break
        stage_index += 1
        closed |= additions
        stages.append(
            {
                "stage": stage_index,
                "added_count": len(additions),
                "added": tuple(sorted(additions)),
                "total_size": len(closed),
            }
        )
    return closed, stages


BIT_COORDINATES = ("s1", "f1", "s2", "f2", "s3", "f3")


def cube_automorphisms() -> tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]:
    return tuple(
        (permutation, flips)
        for permutation in itertools.permutations(range(6))
        for flips in itertools.product((0, 1), repeat=6)
    )


def apply_cube_automorphism(
    codon: str,
    permutation: tuple[int, ...],
    flips: tuple[int, ...],
) -> str:
    word = bits(codon)
    return codon_from_bits(
        "".join(str(int(word[permutation[index]]) ^ flips[index]) for index in range(6))
    )


def automorphism_name(permutation: tuple[int, ...], flips: tuple[int, ...]) -> str:
    identity = tuple(range(6))
    if permutation == identity and all(flip == 0 for flip in flips):
        return "id"
    if permutation == (3, 1, 2, 0, 4, 5) and all(flip == 0 for flip in flips):
        return "swap(s1,f2)"
    moved = [
        f"{BIT_COORDINATES[index]}<-{BIT_COORDINATES[source]}"
        for index, source in enumerate(permutation)
        if index != source
    ]
    flipped = [
        f"flip({BIT_COORDINATES[index]})"
        for index, flip in enumerate(flips)
        if flip
    ]
    return ";".join(moved + flipped)


def stabilizer_of_set(
    codons: set[str],
    automorphisms: tuple[tuple[tuple[int, ...], tuple[int, ...]], ...],
) -> tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]:
    return tuple(
        (permutation, flips)
        for permutation, flips in automorphisms
        if {
            apply_cube_automorphism(codon, permutation, flips)
            for codon in codons
        }
        == codons
    )


def stabilizer_of_weight(
    weights: dict[str, int],
    automorphisms: tuple[tuple[tuple[int, ...], tuple[int, ...]], ...],
) -> tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]:
    codons = tuple(sorted(weights))
    return tuple(
        (permutation, flips)
        for permutation, flips in automorphisms
        if all(
            weights[apply_cube_automorphism(codon, permutation, flips)] == weights[codon]
            for codon in codons
        )
    )


def automorphism_orbits(
    codons: set[str],
    automorphisms: tuple[tuple[tuple[int, ...], tuple[int, ...]], ...],
) -> tuple[tuple[str, ...], ...]:
    remaining = set(codons)
    orbits: list[tuple[str, ...]] = []
    while remaining:
        seed = min(remaining)
        orbit = {
            apply_cube_automorphism(seed, permutation, flips)
            for permutation, flips in automorphisms
        } & codons
        orbit_tuple = tuple(sorted(orbit))
        orbits.append(orbit_tuple)
        remaining -= orbit
    orbits.sort(key=lambda orbit: (-len(orbit), orbit))
    return tuple(orbits)


def automorphism_permutation_vector(
    permutation: tuple[int, ...],
    flips: tuple[int, ...],
    codons: tuple[str, ...],
    codon_index: dict[str, int],
) -> tuple[int, ...]:
    bit_codes = tuple(int(bits(codon), 2) for codon in codons)
    index_by_bit_code = {code: index for index, code in enumerate(bit_codes)}
    return tuple(
        index_by_bit_code[
            sum(
                (((code >> (5 - permutation[index])) & 1) ^ flips[index]) << (5 - index)
                for index in range(6)
            )
        ]
        for code in bit_codes
    )


def set_stabilizer_indices(
    codon_indices: frozenset[int],
    automorphism_vectors: tuple[tuple[int, ...], ...],
) -> tuple[int, ...]:
    return tuple(
        index
        for index, vector in enumerate(automorphism_vectors)
        if frozenset(vector[codon_index] for codon_index in codon_indices) == codon_indices
    )


def weight_stabilizer_indices(
    weights: tuple[int, ...],
    automorphism_vectors: tuple[tuple[int, ...], ...],
) -> tuple[int, ...]:
    return tuple(
        index
        for index, vector in enumerate(automorphism_vectors)
        if all(weights[vector[codon_index]] == weights[codon_index] for codon_index in range(len(weights)))
    )


def indexed_orbits(
    codon_indices: frozenset[int],
    stabilizer_indices: tuple[int, ...],
    automorphism_vectors: tuple[tuple[int, ...], ...],
    codons: tuple[str, ...],
) -> tuple[tuple[str, ...], ...]:
    remaining = set(codon_indices)
    orbits: list[tuple[str, ...]] = []
    while remaining:
        seed = min(remaining)
        orbit_indices = {
            automorphism_vectors[automorphism_index][seed]
            for automorphism_index in stabilizer_indices
        } & set(codon_indices)
        orbit_indices.add(seed)
        orbit = tuple(sorted(codons[index] for index in orbit_indices))
        orbits.append(orbit)
        remaining -= orbit_indices
    orbits.sort(key=lambda orbit: (-len(orbit), orbit))
    return tuple(orbits)


def median_index(left: int, middle: int, right: int) -> int:
    value = 0
    for bit_index in range(6):
        mask = 1 << bit_index
        ones = int(bool(left & mask)) + int(bool(middle & mask)) + int(bool(right & mask))
        if ones >= 2:
            value |= mask
    return value


def solve_fraction_linear_system(
    matrix: list[list[fractions.Fraction]],
    vector: list[fractions.Fraction],
) -> list[fractions.Fraction]:
    size = len(vector)
    augmented = [row[:] + [value] for row, value in zip(matrix, vector)]
    for pivot in range(size):
        pivot_row = next(row for row in range(pivot, size) if augmented[row][pivot] != 0)
        if pivot_row != pivot:
            augmented[pivot], augmented[pivot_row] = augmented[pivot_row], augmented[pivot]
        pivot_value = augmented[pivot][pivot]
        augmented[pivot] = [entry / pivot_value for entry in augmented[pivot]]
        for row in range(size):
            if row == pivot:
                continue
            factor = augmented[row][pivot]
            if factor:
                augmented[row] = [
                    current - factor * pivot_entry
                    for current, pivot_entry in zip(augmented[row], augmented[pivot])
                ]
    return [row[-1] for row in augmented]


def fraction_string(value: fractions.Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def dominant_symmetric_eigenpair(
    matrix: list[list[float]],
    tolerance: float = 1e-15,
    max_iterations: int = 10000,
) -> tuple[float, list[float]]:
    size = len(matrix)
    vector = [1.0 / (size ** 0.5) for _index in range(size)]
    previous = 0.0
    for _iteration in range(max_iterations):
        shifted = [
            vector[row] + sum(matrix[row][column] * vector[column] for column in range(size))
            for row in range(size)
        ]
        norm = sum(entry * entry for entry in shifted) ** 0.5
        vector = [entry / norm for entry in shifted]
        value = sum(
            vector[row] * sum(matrix[row][column] * vector[column] for column in range(size))
            for row in range(size)
        )
        if abs(value - previous) < tolerance:
            break
        previous = value
    if sum(vector) < 0:
        vector = [-entry for entry in vector]
    return value, vector


def interval_closure(codons: set[str]) -> tuple[set[str], list[dict[str, object]]]:
    closed = set(codons)
    stages: list[dict[str, object]] = []
    stage_index = 0
    while True:
        additions: set[str] = set()
        for left, right in itertools.combinations(sorted(closed), 2):
            left_bits = bits(left)
            right_bits = bits(right)
            free = [index for index, (a, b) in enumerate(zip(left_bits, right_bits)) if a != b]
            base = list(left_bits)
            for values in itertools.product("01", repeat=len(free)):
                candidate = base.copy()
                for index, value in zip(free, values):
                    candidate[index] = value
                additions.add(codon_from_bits("".join(candidate)))
        additions -= closed
        if not additions:
            break
        stage_index += 1
        closed |= additions
        stages.append(
            {
                "stage": stage_index,
                "added_count": len(additions),
                "added": tuple(sorted(additions)),
                "total_size": len(closed),
            }
        )
    return closed, stages


def q2_face_vertices() -> tuple[tuple[str, ...], ...]:
    return tuple(
        subcube_vertices(free, values)
        for free in itertools.combinations(range(6), 2)
        for values in itertools.product("01", repeat=4)
    )


def q2_completion_closure(
    codons: set[str],
    faces: tuple[tuple[str, ...], ...] | None = None,
) -> tuple[set[str], list[dict[str, object]]]:
    if faces is None:
        faces = q2_face_vertices()
    closed = set(codons)
    stages: list[dict[str, object]] = []
    stage_index = 0
    while len(closed) < 64:
        additions: set[str] = set()
        for face in faces:
            if sum(1 for codon in face if codon in closed) >= 3:
                additions.update(codon for codon in face if codon not in closed)
        additions -= closed
        if not additions:
            break
        stage_index += 1
        closed |= additions
        stages.append(
            {
                "stage": stage_index,
                "added_count": len(additions),
                "added": tuple(sorted(additions)),
                "total_size": len(closed),
            }
        )
    return closed, stages


def reassignment_mass_geometry_summary(tables: dict[int, dict[str, str]]) -> dict[str, object]:
    standard = tables[1]
    codon_counts: collections.Counter[str] = collections.Counter()
    changed_tables: dict[str, set[int]] = collections.defaultdict(set)
    for table_id, table in sorted(tables.items()):
        if table_id == 1:
            continue
        for codon in all_codons():
            if table[codon] != standard[codon]:
                codon_counts[codon] += 1
                changed_tables[codon].add(table_id)

    total_mass = sum(codon_counts.values())
    max_subcubes: dict[str, dict[str, object]] = {}
    for dimension in (5, 4, 3, 2):
        candidates: list[dict[str, object]] = []
        max_mass = -1
        for free in itertools.combinations(range(6), dimension):
            fixed_count = 6 - dimension
            for values in itertools.product("01", repeat=fixed_count):
                vertices = subcube_vertices(free, values)
                mass = sum(codon_counts[codon] for codon in vertices)
                if mass > max_mass:
                    max_mass = mass
                    candidates = []
                if mass == max_mass:
                    candidates.append(
                        {
                            "free_bits": free,
                            "fixed_conditions": fixed_conditions(free, values),
                            "vertices": vertices,
                            "mass": mass,
                        }
                    )
        max_subcubes[f"Q{dimension}"] = {
            "max_mass": max_mass,
            "max_count": len(candidates),
            "maximizers": candidates,
            "mass_fraction": max_mass / total_mass,
        }

    reassigned = set(codon_counts)
    full_q2_faces: list[dict[str, object]] = []
    q2_reassigned_vertex_distribution: collections.Counter[int] = collections.Counter()
    for free in itertools.combinations(range(6), 2):
        for values in itertools.product("01", repeat=4):
            vertices = subcube_vertices(free, values)
            reassigned_vertices = [codon for codon in vertices if codon in reassigned]
            q2_reassigned_vertex_distribution[len(reassigned_vertices)] += 1
            if len(reassigned_vertices) == 4:
                full_q2_faces.append(
                    {
                        "free_bits": free,
                        "fixed_conditions": fixed_conditions(free, values),
                        "vertices": vertices,
                        "mass": sum(codon_counts[codon] for codon in vertices),
                    }
                )
    full_q2_faces.sort(key=lambda item: (-item["mass"], item["vertices"]))

    positive_edges: list[dict[str, object]] = []
    zero_edges: list[tuple[str, str]] = []
    for left, right, _direction in hamming_edges():
        if left not in reassigned or right not in reassigned:
            continue
        weight = len(changed_tables[left] & changed_tables[right])
        if weight > 0:
            positive_edges.append({"edge": (left, right), "weight": weight})
        else:
            zero_edges.append((left, right))
    positive_edges.sort(key=lambda item: (-item["weight"], item["edge"]))

    positive_adjacency: dict[str, set[str]] = {codon: set() for codon in sorted(reassigned)}
    for item in positive_edges:
        left, right = item["edge"]
        positive_adjacency[left].add(right)
        positive_adjacency[right].add(left)
    seen: set[str] = set()
    components: list[list[str]] = []
    for codon in sorted(reassigned):
        if codon in seen:
            continue
        stack = [codon]
        seen.add(codon)
        component: list[str] = []
        while stack:
            item = stack.pop()
            component.append(item)
            for neighbor in positive_adjacency[item]:
                if neighbor not in seen:
                    seen.add(neighbor)
                    stack.append(neighbor)
        components.append(sorted(component))
    components.sort(key=lambda component: (-len(component), component))

    purine_core = ("TAA", "TAG", "TGA", "TGG", "AAA", "AAG", "AGA", "AGG")
    a_ending_square = ("AAA", "AGA", "TAA", "TGA")
    return {
        "total_mass": total_mass,
        "codon_weights": dict(sorted(codon_counts.items(), key=lambda item: (-item[1], item[0]))),
        "max_subcubes": max_subcubes,
        "purine_core_q3": {
            "vertices": purine_core,
            "mass": sum(codon_counts[codon] for codon in purine_core),
            "standard_labels": {codon: standard[codon] for codon in purine_core},
            "weights": {codon: codon_counts[codon] for codon in purine_core},
        },
        "a_ending_square": {
            "vertices": a_ending_square,
            "mass": sum(codon_counts[codon] for codon in a_ending_square),
            "standard_labels": {codon: standard[codon] for codon in a_ending_square},
            "weights": {codon: codon_counts[codon] for codon in a_ending_square},
        },
        "q2_reassigned_vertex_distribution": dict(sorted(q2_reassigned_vertex_distribution.items())),
        "full_reassigned_q2_faces": full_q2_faces,
        "co_reassignment_edges": positive_edges,
        "zero_reassignment_edges": zero_edges,
        "positive_co_reassignment_components": components,
    }


def is_connected_codons(codons: tuple[str, ...], edge_pairs: set[tuple[str, str]]) -> bool:
    if not codons:
        return False
    codon_set = set(codons)
    seen = {codons[0]}
    stack = [codons[0]]
    while stack:
        item = stack.pop()
        for left, right in edge_pairs:
            neighbor = None
            if left == item and right in codon_set:
                neighbor = right
            elif right == item and left in codon_set:
                neighbor = left
            if neighbor is not None and neighbor not in seen:
                seen.add(neighbor)
                stack.append(neighbor)
    return seen == codon_set


def weighted_deformation_spine_summary(tables: dict[int, dict[str, str]]) -> dict[str, object]:
    standard = tables[1]
    codon_weights: collections.Counter[str] = collections.Counter()
    for table_id, table in sorted(tables.items()):
        if table_id == 1:
            continue
        for codon in all_codons():
            if table[codon] != standard[codon]:
                codon_weights[codon] += 1
    reassigned = tuple(sorted(codon_weights))
    reassigned_set = set(reassigned)
    total_mass = sum(codon_weights.values())
    edge_pairs = {
        tuple(sorted((left, right)))
        for left, right, _direction in hamming_edges()
        if left in reassigned_set and right in reassigned_set
    }

    connected_optima: dict[int, dict[str, object]] = {}
    for size in range(1, len(reassigned) + 1):
        max_mass = -1
        optima: list[tuple[str, ...]] = []
        for candidate in itertools.combinations(reassigned, size):
            if not is_connected_codons(candidate, edge_pairs):
                continue
            mass = sum(codon_weights[codon] for codon in candidate)
            if mass > max_mass:
                max_mass = mass
                optima = []
            if mass == max_mass:
                optima.append(candidate)
        connected_optima[size] = {
            "max_mass": max_mass,
            "optimum_count": len(optima),
            "optima": optima,
        }

    bit_majority: list[dict[str, object]] = []
    for direction in range(6):
        masses = collections.Counter()
        for codon, weight in codon_weights.items():
            masses[bits(codon)[direction]] += weight
        majority_value, majority_mass = max(masses.items(), key=lambda item: (item[1], item[0]))
        bit_majority.append(
            {
                "bit": direction,
                "majority_value": majority_value,
                "zero_mass": masses["0"],
                "one_mass": masses["1"],
                "majority_mass": majority_mass,
                "majority_fraction": majority_mass / total_mass,
            }
        )

    q3_candidates: list[dict[str, object]] = []
    for free in itertools.combinations(range(6), 3):
        for values in itertools.product("01", repeat=3):
            vertices = subcube_vertices(free, values)
            support_count = sum(1 for codon in vertices if codon in reassigned_set)
            mass = sum(codon_weights[codon] for codon in vertices)
            q3_candidates.append(
                {
                    "free_bits": free,
                    "fixed_conditions": fixed_conditions(free, values),
                    "vertices": vertices,
                    "support_count": support_count,
                    "mass": mass,
                }
            )
    max_q3_support = max(candidate["support_count"] for candidate in q3_candidates)
    cardinality_q3 = [
        candidate for candidate in q3_candidates if candidate["support_count"] == max_q3_support
    ]
    cardinality_q3.sort(key=lambda item: (-item["mass"], item["vertices"]))

    cover_blocks: list[dict[str, object]] = []
    for dimension in (3, 2):
        for free in itertools.combinations(range(6), dimension):
            for values in itertools.product("01", repeat=6 - dimension):
                vertices = subcube_vertices(free, values)
                covered = tuple(sorted(codon for codon in vertices if codon in reassigned_set))
                if not covered:
                    continue
                cover_blocks.append(
                    {
                        "dimension": dimension,
                        "fixed_conditions": fixed_conditions(free, values),
                        "vertices": vertices,
                        "covered": covered,
                        "covered_count": len(covered),
                        "mass": sum(codon_weights[codon] for codon in covered),
                    }
                )
    minimal_covers: list[tuple[dict[str, object], ...]] = []
    for cover_size in range(1, 5):
        for blocks in itertools.combinations(cover_blocks, cover_size):
            covered_union = set().union(*(set(block["covered"]) for block in blocks))
            if covered_union == reassigned_set:
                minimal_covers.append(blocks)
        if minimal_covers:
            break
    minimal_covers.sort(
        key=lambda blocks: (
            -sum(block["mass"] for block in blocks),
            tuple((block["dimension"], block["vertices"]) for block in blocks),
        )
    )
    canonical_cover_vertices = [
        ("TAA", "TAG", "TGA", "TGG", "AAA", "AAG", "AGA", "AGG"),
        ("CTT", "CTC", "CTA", "CTG"),
        ("TTA", "TCA", "ATA", "ACA"),
    ]
    canonical_cover: list[dict[str, object]] = []
    for vertices in canonical_cover_vertices:
        covered = tuple(sorted(codon for codon in vertices if codon in reassigned_set))
        canonical_cover.append(
            {
                "vertices": vertices,
                "covered": covered,
                "covered_count": len(covered),
                "mass": sum(codon_weights[codon] for codon in covered),
            }
        )
    return {
        "connected_optima": connected_optima,
        "bit_majority": bit_majority,
        "max_q3_support_count": max_q3_support,
        "cardinality_q3_maximizers": cardinality_q3,
        "minimal_q2_q3_cover_size": len(minimal_covers[0]),
        "minimal_q2_q3_cover_count": len(minimal_covers),
        "preferred_q2_q3_cover": list(minimal_covers[0]),
        "canonical_q2_q3_cover": canonical_cover,
    }


def max_subcube_mass_from_weights(weights_by_codon: dict[str, int], dimension: int) -> int:
    max_mass = -1
    for free in itertools.combinations(range(6), dimension):
        fixed_count = 6 - dimension
        for values in itertools.product("01", repeat=fixed_count):
            vertices = subcube_vertices(free, values)
            mass = sum(weights_by_codon.get(codon, 0) for codon in vertices)
            max_mass = max(max_mass, mass)
    return max_mass


def subcube_index_sets(codons: list[str], dimension: int) -> list[tuple[int, ...]]:
    codon_index = {codon: index for index, codon in enumerate(codons)}
    index_sets: list[tuple[int, ...]] = []
    for free in itertools.combinations(range(6), dimension):
        fixed_count = 6 - dimension
        for values in itertools.product("01", repeat=fixed_count):
            vertices = subcube_vertices(free, values)
            index_sets.append(tuple(codon_index[codon] for codon in vertices))
    return index_sets


def max_subcube_mass_from_vector(weights: list[int], index_sets: list[tuple[int, ...]]) -> int:
    return max(sum(weights[index] for index in index_set) for index_set in index_sets)


def reassignment_spectral_compression_summary(
    tables: dict[int, dict[str, str]],
    *,
    monte_carlo_trials: int = 100000,
    seed: int = 20260521,
) -> dict[str, object]:
    standard = tables[1]
    weights: dict[str, int] = {codon: 0 for codon in all_codons()}
    for table_id, table in sorted(tables.items()):
        if table_id == 1:
            continue
        for codon in all_codons():
            if table[codon] != standard[codon]:
                weights[codon] += 1

    coefficients: dict[tuple[int, ...], float] = {}
    for size in range(7):
        for subset in itertools.combinations(range(6), size):
            total = 0
            for codon, weight in weights.items():
                parity = sum(int(bits(codon)[index]) for index in subset) % 2
                total += weight * (-1 if parity else 1)
            coefficients[subset] = total / 64

    nontrivial = [
        {
            "bits": subset,
            "coefficient": coefficients[subset],
            "abs_coefficient": abs(coefficients[subset]),
        }
        for subset in coefficients
        if subset
    ]
    nontrivial.sort(key=lambda item: (-item["abs_coefficient"], item["bits"]))

    degree_energy: dict[int, float] = collections.defaultdict(float)
    for subset, coefficient in coefficients.items():
        if not subset:
            continue
        degree_energy[len(subset)] += coefficient * coefficient
    nonmean_energy = sum(degree_energy.values())
    degree_energy_share = {
        degree: degree_energy[degree] / nonmean_energy
        for degree in sorted(degree_energy)
    }
    cumulative_energy_share: dict[int, float] = {}
    running = 0.0
    for degree in sorted(degree_energy):
        running += degree_energy_share[degree]
        cumulative_energy_share[degree] = running

    observed_max = {
        dimension: max_subcube_mass_from_weights(weights, dimension)
        for dimension in (2, 3, 4, 5)
    }
    codons = all_codons()
    weight_multiset = [weights[codon] for codon in codons]
    subcube_indices = {
        dimension: subcube_index_sets(codons, dimension)
        for dimension in observed_max
    }
    rng = random.Random(seed)
    exceed_counts = {dimension: 0 for dimension in observed_max}
    max_sums = {dimension: 0 for dimension in observed_max}
    for _trial in range(monte_carlo_trials):
        shuffled = weight_multiset.copy()
        rng.shuffle(shuffled)
        for dimension, observed in observed_max.items():
            max_mass = max_subcube_mass_from_vector(shuffled, subcube_indices[dimension])
            max_sums[dimension] += max_mass
            if max_mass >= observed:
                exceed_counts[dimension] += 1
    monte_carlo = {
        dimension: {
            "observed_max_mass": observed_max[dimension],
            "random_mean_max_mass": max_sums[dimension] / monte_carlo_trials,
            "exceed_count": exceed_counts[dimension],
            "p_value": exceed_counts[dimension] / monte_carlo_trials,
        }
        for dimension in sorted(observed_max)
    }

    return {
        "total_weight": sum(weights.values()),
        "mean_coefficient": coefficients[()],
        "top_nontrivial_coefficients": nontrivial[:7],
        "degree_energy_share": degree_energy_share,
        "cumulative_energy_share": cumulative_energy_share,
        "monte_carlo": {
            "trials": monte_carlo_trials,
            "seed": seed,
            "subcube_maxima": monte_carlo,
        },
    }


IUPAC_BASES = {
    "U": {"T"},
    "C": {"C"},
    "A": {"A"},
    "G": {"G"},
    "N": {"T", "C", "A", "G"},
    "R": {"A", "G"},
    "W": {"T", "A"},
    "Y": {"T", "C"},
}


def expand_iupac_motif(motif: str) -> tuple[str, ...]:
    choices = [sorted(IUPAC_BASES[symbol], key=BASES.index) for symbol in motif]
    return tuple("".join(parts) for parts in itertools.product(*choices))


def support_compression_summary(tables: dict[int, dict[str, str]]) -> dict[str, object]:
    standard = tables[1]
    support = {
        codon
        for table_id, table in sorted(tables.items())
        if table_id != 1
        for codon in all_codons()
        if table[codon] != standard[codon]
    }
    exact_motifs = ("CUN", "AGR", "UNA", "WWA", "UAR")
    exact_sets = {motif: set(expand_iupac_motif(motif)) for motif in exact_motifs}
    exact_union = set().union(*exact_sets.values())

    all_internal_subcubes: list[dict[str, object]] = []
    for dimension in range(0, 7):
        for free in itertools.combinations(range(6), dimension):
            for values in itertools.product("01", repeat=6 - dimension):
                vertices = subcube_vertices(free, values)
                vertex_set = set(vertices)
                if vertex_set <= support:
                    all_internal_subcubes.append(
                        {
                            "dimension": dimension,
                            "fixed_conditions": fixed_conditions(free, values),
                            "vertices": vertices,
                        }
                    )
    maximal_internal: list[dict[str, object]] = []
    for candidate in all_internal_subcubes:
        candidate_set = set(candidate["vertices"])
        if not any(
            candidate_set < set(other["vertices"])
            for other in all_internal_subcubes
        ):
            maximal_internal.append(candidate)
    maximal_internal.sort(key=lambda item: (-item["dimension"], item["vertices"]))

    minimal_prime_covers: list[tuple[dict[str, object], ...]] = []
    for cover_size in range(1, 8):
        for blocks in itertools.combinations(maximal_internal, cover_size):
            covered = set().union(*(set(block["vertices"]) for block in blocks))
            if covered == support:
                minimal_prime_covers.append(blocks)
        if minimal_prime_covers:
            break
    def subcube_name(vertices: tuple[str, ...]) -> str:
        vertex_set = set(vertices)
        known = {
            tuple(expand_iupac_motif("CUN")): "CUN",
            tuple(expand_iupac_motif("UNA")): "UNA",
            tuple(expand_iupac_motif("WWA")): "WWA",
            tuple(expand_iupac_motif("WRA")): "WRA",
            tuple(expand_iupac_motif("AGR")): "AGR",
            tuple(expand_iupac_motif("UAR")): "UAR",
            tuple(expand_iupac_motif("YUA")): "YUA",
            tuple(expand_iupac_motif("WNR")): "WNR",
            tuple(expand_iupac_motif("YUR")): "YUR",
            tuple(expand_iupac_motif("WYG")): "WYG",
            tuple(("TAG",)): "UAG",
            tuple(("TCA",)): "UCA",
            tuple(("ATA", "AAA")): "AWA",
            tuple(("TCA", "TGA")): "USA",
            tuple(("TTA", "ATA")): "WUA",
            tuple(("TTA", "TAA")): "UWA",
            tuple(("AAA",)): "AAA",
            tuple(("TTA",)): "UUA",
        }
        for codons, name in known.items():
            if set(codons) == vertex_set:
                return name
        return "/".join(vertices)

    def vertex_key(block: dict[str, object]) -> tuple[str, ...]:
        return tuple(block["vertices"])

    def codon_weight(codon: str) -> int:
        return sum(
            1
            for table_id, table in sorted(tables.items())
            if table_id != 1 and table[codon] != standard[codon]
        )

    def block_weight(block: dict[str, object]) -> int:
        return sum(codon_weight(codon) for codon in block["vertices"])

    minimal_exact_covers: list[tuple[dict[str, object], ...]] = []
    for cover_size in range(1, 8):
        for blocks in itertools.combinations(all_internal_subcubes, cover_size):
            covered = set().union(*(set(block["vertices"]) for block in blocks))
            if covered == support:
                minimal_exact_covers.append(blocks)
        if minimal_exact_covers:
            break
    common_exact_blocks = set(vertex_key(block) for block in minimal_exact_covers[0])
    for cover in minimal_exact_covers[1:]:
        common_exact_blocks &= set(vertex_key(block) for block in cover)

    prime_overlap_rows: list[dict[str, object]] = []
    for left, right in itertools.combinations(maximal_internal, 2):
        overlap = tuple(codon for codon in left["vertices"] if codon in set(right["vertices"]))
        if not overlap:
            continue
        weight = sum(codon_weight(codon) for codon in overlap)
        prime_overlap_rows.append(
            {
                "left": subcube_name(left["vertices"]),
                "right": subcube_name(right["vertices"]),
                "overlap": overlap,
                "weight": weight,
            }
        )
    overlap_weight_by_prime: collections.Counter[str] = collections.Counter()
    for row in prime_overlap_rows:
        overlap_weight_by_prime[row["left"]] += row["weight"]
        overlap_weight_by_prime[row["right"]] += row["weight"]

    envelope_motifs = ("WRR", "CUN", "WYA")
    envelope_sets = {motif: set(expand_iupac_motif(motif)) for motif in envelope_motifs}
    envelope_union = set().union(*envelope_sets.values())

    graph_edges = tuple(
        (left, right)
        for left, right, _direction in hamming_edges()
        if left in support and right in support
    )
    graph_adjacency: dict[str, set[str]] = {codon: set() for codon in support}
    for left, right in graph_edges:
        graph_adjacency[left].add(right)
        graph_adjacency[right].add(left)

    def graph_components(adjacency: dict[str, set[str]]) -> list[tuple[str, ...]]:
        seen: set[str] = set()
        components: list[tuple[str, ...]] = []
        for node in sorted(adjacency):
            if node in seen:
                continue
            stack = [node]
            seen.add(node)
            component: list[str] = []
            while stack:
                item = stack.pop()
                component.append(item)
                for neighbor in sorted(adjacency[item], reverse=True):
                    if neighbor not in seen:
                        seen.add(neighbor)
                        stack.append(neighbor)
            components.append(tuple(sorted(component)))
        components.sort(key=lambda component: (-len(component), component))
        return components

    graph_components_list = graph_components(graph_adjacency)

    q2_squares = [
        {
            **block,
            "name": subcube_name(block["vertices"]),
            "weight": block_weight(block),
        }
        for block in all_internal_subcubes
        if block["dimension"] == 2
    ]
    q2_squares.sort(key=lambda block: block["name"])

    wna = set(expand_iupac_motif("WNA"))
    punctured_wna = wna - {"ACA"}
    cun = set(expand_iupac_motif("CUN"))
    leaves = {"TAG", "AGG"}
    skeleton_union = punctured_wna | cun | leaves

    def edges_inside(vertices: set[str]) -> tuple[tuple[str, str], ...]:
        return tuple((left, right) for left, right in graph_edges if left in vertices and right in vertices)

    punctured_edges = edges_inside(punctured_wna)
    cun_edges = edges_inside(cun)
    bridge_edges = tuple(
        (left, right)
        for left, right in graph_edges
        if (left, right) not in punctured_edges and (left, right) not in cun_edges
    )

    def without_vertex_components(removed: str) -> list[tuple[str, ...]]:
        adjacency = {
            node: {neighbor for neighbor in neighbors if neighbor != removed}
            for node, neighbors in graph_adjacency.items()
            if node != removed
        }
        return graph_components(adjacency)

    articulation_rows = [
        {
            "codon": codon,
            "components_after_removal": without_vertex_components(codon),
        }
        for codon in sorted(support)
        if len(without_vertex_components(codon)) > 1
    ]

    def biconnected_components() -> list[tuple[str, ...]]:
        discovery: dict[str, int] = {}
        low: dict[str, int] = {}
        parent: dict[str, str | None] = {}
        edge_stack: list[tuple[str, str]] = []
        components: list[tuple[str, ...]] = []
        tick = 0

        def dfs(node: str) -> None:
            nonlocal tick
            discovery[node] = tick
            low[node] = tick
            tick += 1
            for neighbor in sorted(graph_adjacency[node]):
                if neighbor not in discovery:
                    parent[neighbor] = node
                    edge_stack.append((node, neighbor))
                    dfs(neighbor)
                    low[node] = min(low[node], low[neighbor])
                    if low[neighbor] >= discovery[node]:
                        vertices: set[str] = set()
                        while edge_stack:
                            edge = edge_stack.pop()
                            vertices.update(edge)
                            if edge == (node, neighbor):
                                break
                        components.append(tuple(sorted(vertices)))
                elif parent.get(node) != neighbor and discovery[neighbor] < discovery[node]:
                    low[node] = min(low[node], discovery[neighbor])
                    edge_stack.append((node, neighbor))

        for node in sorted(graph_adjacency):
            if node not in discovery:
                parent[node] = None
                dfs(node)
                if edge_stack:
                    vertices = set()
                    while edge_stack:
                        vertices.update(edge_stack.pop())
                    components.append(tuple(sorted(vertices)))
        components.sort(key=lambda component: (-len(component), component))
        return components

    biconnected = biconnected_components()
    random_trials = 100000
    random_seed = 20260522
    random_generator = random.Random(random_seed)
    all_edges = tuple((left, right) for left, right, _direction in hamming_edges())
    all_codon_tuple = tuple(all_codons())
    exceed_count = 0
    edge_sum = 0
    for _trial in range(random_trials):
        sample = set(random_generator.sample(all_codon_tuple, len(support)))
        edge_count = sum(1 for left, right in all_edges if left in sample and right in sample)
        edge_sum += edge_count
        if edge_count >= len(graph_edges):
            exceed_count += 1

    boundary_neighbors: dict[str, list[str]] = collections.defaultdict(list)
    boundary_edges: list[tuple[str, str]] = []
    for left, right in all_edges:
        if left in support and right not in support:
            boundary_neighbors[right].append(left)
            boundary_edges.append((left, right))
        elif right in support and left not in support:
            boundary_neighbors[left].append(right)
            boundary_edges.append((right, left))
    boundary_rows = [
        {
            "codon": codon,
            "standard": standard[codon],
            "boundary_degree": len(neighbors),
            "boundary_pressure": sum(codon_weight(neighbor) for neighbor in neighbors),
            "neighbors": tuple(sorted(neighbors)),
        }
        for codon, neighbors in sorted(boundary_neighbors.items())
    ]
    boundary_rows.sort(
        key=lambda row: (-row["boundary_degree"], -row["boundary_pressure"], row["codon"])
    )

    q2_completion_faces: list[dict[str, object]] = []
    completion_frontier: set[str] = set()
    for free in itertools.combinations(range(6), 2):
        for values in itertools.product("01", repeat=4):
            vertices = subcube_vertices(free, values)
            present = tuple(codon for codon in vertices if codon in support)
            missing = tuple(codon for codon in vertices if codon not in support)
            if len(present) == 3 and len(missing) == 1:
                completion_frontier.add(missing[0])
                q2_completion_faces.append(
                    {
                        "vertices": vertices,
                        "present": present,
                        "missing": missing[0],
                    }
                )

    cached_q2_faces = q2_face_vertices()
    closed, completion_stages = q2_completion_closure(support, cached_q2_faces)

    boundary_class: dict[str, dict[str, object]] = {}
    for row in boundary_rows:
        label = row["standard"]
        if label not in boundary_class:
            boundary_class[label] = {
                "boundary_edges": 0,
                "boundary_pressure": 0,
                "codons": [],
            }
        boundary_class[label]["boundary_edges"] += row["boundary_degree"]
        boundary_class[label]["boundary_pressure"] += row["boundary_pressure"]
        boundary_class[label]["codons"].append(row["codon"])
    boundary_class_rows = [
        {"class": label, **values, "codons": tuple(sorted(values["codons"]))}
        for label, values in boundary_class.items()
    ]
    boundary_class_rows.sort(
        key=lambda row: (-row["boundary_pressure"], -row["boundary_edges"], row["class"])
    )

    inactive_anchors = set(envelope_union - support)
    anchor_closure = support | inactive_anchors
    wna_set = set(expand_iupac_motif("WNA"))
    wrr_set = set(expand_iupac_motif("WRR"))
    wra_set = set(expand_iupac_motif("WRA"))
    closure_formula_union = wna_set | wrr_set | cun
    active_complex = cubical_complex_summary(support)
    closure_complex = cubical_complex_summary(anchor_closure)
    closure_edges = tuple(
        (left, right)
        for left, right, _direction in hamming_edges()
        if left in anchor_closure and right in anchor_closure
    )
    closure_boundary_edge_count = 6 * len(anchor_closure) - 2 * len(closure_edges)
    closure_degrees: dict[str, int] = {
        codon: sum(1 for left, right in closure_edges if codon in (left, right))
        for codon in sorted(anchor_closure)
    }
    support_tuple = tuple(sorted(support))
    median_set, median_stages = median_closure(support)
    convex_set, convex_stages = interval_closure(support)
    wnr_set = set(expand_iupac_motif("WNR"))
    yur_set = set(expand_iupac_motif("YUR"))
    wyg_set = set(expand_iupac_motif("WYG"))
    median_formula_union = wnr_set | cun
    median_complex = cubical_complex_summary(median_set)
    median_stage_one = support | set(median_stages[0]["added"])
    median_stage_one_formula = (wnr_set - {"ACG"}) | cun
    median_stage_one_complex = cubical_complex_summary(median_stage_one)
    median_stage_delta_f = tuple(
        median_complex["f_vector"][index] - median_stage_one_complex["f_vector"][index]
        for index in range(len(median_complex["f_vector"]))
    )
    active_triple_outputs = [
        {"triple": triple, "median": median_codon(*triple)}
        for triple in itertools.combinations(support_tuple, 3)
    ]
    leakage_triples = [
        row for row in active_triple_outputs if row["median"] not in support
    ]
    closed_triple_count = len(active_triple_outputs) - len(leakage_triples)
    median_centrality = collections.Counter(row["median"] for row in active_triple_outputs)
    median_centrality_rows = [
        {
            "codon": codon,
            "active": codon in support,
            "median_count": median_centrality[codon],
        }
        for codon in sorted(median_set)
    ]
    median_centrality_rows.sort(
        key=lambda row: (-row["median_count"], row["codon"])
    )
    leakage_output_counts = collections.Counter(row["median"] for row in leakage_triples)
    leakage_output_rows = [
        {"codon": codon, "median_count": count}
        for codon, count in leakage_output_counts.items()
    ]
    leakage_output_rows.sort(key=lambda row: (-row["median_count"], row["codon"]))
    leakage_catalyst_counts = collections.Counter(
        codon for row in leakage_triples for codon in row["triple"]
    )
    leakage_catalyst_rows = [
        {"codon": codon, "leakage_triple_count": count}
        for codon, count in leakage_catalyst_counts.items()
    ]
    leakage_catalyst_rows.sort(
        key=lambda row: (-row["leakage_triple_count"], row["codon"])
    )
    leakage_random_trials = 100000
    leakage_random_seed = 20260522
    leakage_random = random.Random(leakage_random_seed)
    observed_leakage_outputs = set(leakage_output_counts)
    random_closed_sum = 0
    random_one_step_size_sum = 0
    random_leakage_output_sum = 0
    random_closed_exceed = 0
    random_leakage_output_leq = 0
    indexed_median_triples = {
        (left, middle, right): median_index(left, middle, right)
        for left, middle, right in itertools.combinations(range(64), 3)
    }
    for _trial in range(leakage_random_trials):
        sample_indices = sorted(leakage_random.sample(range(64), len(support)))
        sample_index_set = set(sample_indices)
        sample_outputs = []
        sample_closed = 0
        for triple in itertools.combinations(sample_indices, 3):
            output = indexed_median_triples[triple]
            sample_outputs.append(output)
            if output in sample_index_set:
                sample_closed += 1
        sample_output_set = set(sample_outputs)
        sample_leakage_outputs = sample_output_set - sample_index_set
        random_closed_sum += sample_closed
        random_one_step_size_sum += len(sample_index_set | sample_output_set)
        random_leakage_output_sum += len(sample_leakage_outputs)
        if sample_closed >= closed_triple_count:
            random_closed_exceed += 1
        if len(sample_leakage_outputs) <= len(observed_leakage_outputs):
            random_leakage_output_leq += 1
    inactive_median_points = median_set - support
    minimal_inactive_generators: list[tuple[str, ...]] = []
    minimal_inactive_generator_size = 0
    for size in range(1, len(support_tuple) + 1):
        for subset in itertools.combinations(support_tuple, size):
            generated, _stages = median_closure(set(subset))
            if inactive_median_points <= generated:
                minimal_inactive_generators.append(subset)
        if minimal_inactive_generators:
            minimal_inactive_generator_size = size
            break
    acg_second_order_triples = tuple(
        triple
        for triple in itertools.combinations(tuple(sorted(median_stage_one)), 3)
        if median_codon(*triple) == "ACG"
    )
    active_one_step_medians = {
        median_codon(left, middle, right)
        for left, middle, right in itertools.combinations_with_replacement(support_tuple, 3)
    }
    median_first_step_witnesses = [
        {"codon": "ACA", "triple": ("AGA", "ATA", "TCA")},
        {"codon": "TGG", "triple": ("AGG", "TAG", "TGA")},
        {"codon": "AAG", "triple": ("AAA", "AGG", "TAG")},
        {"codon": "ATG", "triple": ("AGG", "ATA", "CTG")},
        {"codon": "TCG", "triple": ("AGG", "TCA", "CTC")},
        {"codon": "TTG", "triple": ("ATA", "CTG", "TAG")},
    ]
    median_second_step_witness = {"codon": "ACG", "triple": ("TGG", "ATG", "ACA")}
    maximal_median_cells: list[dict[str, object]] = []
    median_cells = [
        cell
        for cells in median_complex["cells_by_dimension"].values()
        for cell in cells
    ]
    for cell in median_cells:
        cell_vertices = set(cell["vertices"])
        if not any(
            cell_vertices < set(other["vertices"])
            for other in median_cells
        ):
            maximal_median_cells.append(cell)
    maximal_median_cells.sort(key=lambda cell: (-len(cell["free_bits"]), cell["vertices"]))
    median_boundary_edges = 6 * len(median_set) - 2 * median_complex["f_vector"][1]
    minimal_median_generators: list[tuple[str, ...]] = []
    minimal_median_generator_size = 0
    for size in range(1, len(support_tuple) + 1):
        for subset in itertools.combinations(support_tuple, size):
            generated, _stages = median_closure(set(subset))
            if generated == median_set:
                minimal_median_generators.append(subset)
        if minimal_median_generators:
            minimal_median_generator_size = size
            break
    median_forced_generators = tuple(
        codon
        for codon in support_tuple
        if all(codon in generator for generator in minimal_median_generators)
    )

    deletion_rows: list[dict[str, object]] = []
    for codon in support_tuple:
        deletion_closure, _stages = median_closure(support - {codon})
        deletion_rows.append(
            {
                "codon": codon,
                "closure_size": len(deletion_closure),
                "preserves_median": deletion_closure == median_set,
                "lost": tuple(sorted(median_set - deletion_closure)),
            }
        )
    median_essential = tuple(row["codon"] for row in deletion_rows if not row["preserves_median"])
    median_redundant = tuple(row["codon"] for row in deletion_rows if row["preserves_median"])

    complement_pairs = tuple(
        (left, right)
        for left, right in itertools.combinations(support_tuple, 2)
        if all(a != b for a, b in zip(bits(left), bits(right)))
    )

    q2_deletion_rows: list[dict[str, object]] = []
    for codon in support_tuple:
        deletion_q2, stages = q2_completion_closure(support - {codon}, cached_q2_faces)
        q2_deletion_rows.append(
            {
                "codon": codon,
                "closure_size": len(deletion_q2),
                "percolates": len(deletion_q2) == 64,
                "stage_count": len(stages),
            }
        )

    q2_percolating_seeds: list[tuple[str, ...]] = []
    minimal_q2_percolating_seed_size = 0
    for size in range(1, len(support_tuple) + 1):
        for subset in itertools.combinations(support_tuple, size):
            generated, _stages = q2_completion_closure(set(subset), cached_q2_faces)
            if len(generated) == 64:
                q2_percolating_seeds.append(subset)
        if q2_percolating_seeds:
            minimal_q2_percolating_seed_size = size
            break

    automorphisms = cube_automorphisms()
    symmetry_codons = tuple(all_codons())
    symmetry_codon_index = {codon: index for index, codon in enumerate(symmetry_codons)}
    automorphism_vectors = tuple(
        automorphism_permutation_vector(permutation, flips, symmetry_codons, symmetry_codon_index)
        for permutation, flips in automorphisms
    )
    support_indices = frozenset(symmetry_codon_index[codon] for codon in support)
    anchor_indices = frozenset(symmetry_codon_index[codon] for codon in anchor_closure)
    stage_one_indices = frozenset(symmetry_codon_index[codon] for codon in median_stage_one)
    median_indices = frozenset(symmetry_codon_index[codon] for codon in median_set)
    support_stabilizer_indices = set_stabilizer_indices(support_indices, automorphism_vectors)
    anchor_stabilizer_indices = set_stabilizer_indices(anchor_indices, automorphism_vectors)
    stage_one_stabilizer_indices = set_stabilizer_indices(stage_one_indices, automorphism_vectors)
    median_stabilizer_indices = set_stabilizer_indices(median_indices, automorphism_vectors)
    weights_for_symmetry = tuple(codon_weight(codon) for codon in symmetry_codons)
    weight_stabilizer_indices_tuple = weight_stabilizer_indices(weights_for_symmetry, automorphism_vectors)
    tau = ((3, 1, 2, 0, 4, 5), (0, 0, 0, 0, 0, 0))
    tau_index = automorphisms.index(tau)
    tau_orbits = {
        "support": indexed_orbits(support_indices, (0, tau_index), automorphism_vectors, symmetry_codons),
        "anchor_closure": indexed_orbits(anchor_indices, (0, tau_index), automorphism_vectors, symmetry_codons),
        "stage_one": indexed_orbits(stage_one_indices, (0, tau_index), automorphism_vectors, symmetry_codons),
    }
    median_formula_stabilizer = [
        index
        for index in median_stabilizer_indices
        for permutation, flips in (automorphisms[index],)
        if set(permutation[index] for index in (0, 2, 3)) == {0, 2, 3}
        and permutation[1] == 1
        and permutation[4] == 4
        and permutation[5] == 5
        and all(flips[index] == 0 for index in (0, 1, 2, 3, 4))
    ]
    median_orbits = indexed_orbits(median_indices, median_stabilizer_indices, automorphism_vectors, symmetry_codons)
    acg_orbit = tuple(orbit for orbit in median_orbits if "ACG" in orbit)[0]
    quotient_orbits = (
        tuple(orbit for orbit in median_orbits if set(orbit) == {"AAA", "AAG", "ACA", "ACG", "TGA", "TGG"})[0],
        tuple(orbit for orbit in median_orbits if set(orbit) == {"ATA", "ATG", "TAA", "TAG", "TCA", "TCG"})[0],
        tuple(orbit for orbit in median_orbits if set(orbit) == {"AGA", "AGG"})[0],
        tuple(orbit for orbit in median_orbits if set(orbit) == {"TTA", "TTG"})[0],
        tuple(orbit for orbit in median_orbits if set(orbit) == {"CTA", "CTG"})[0],
        tuple(orbit for orbit in median_orbits if set(orbit) == {"CTC", "CTT"})[0],
    )
    orbit_names = ("Anchor6", "StopStart6", "AGR", "UUR", "CUR", "CUY")
    orbit_index = {
        codon: index
        for index, orbit in enumerate(quotient_orbits)
        for codon in orbit
    }
    orbit_rows = [
        {
            "index": index,
            "name": orbit_names[index],
            "codons": orbit,
            "size": len(orbit),
            "active_codons": tuple(codon for codon in orbit if codon in support),
            "inactive_codons": tuple(codon for codon in orbit if codon not in support),
            "weight": sum(codon_weight(codon) for codon in orbit),
        }
        for index, orbit in enumerate(quotient_orbits)
    ]
    median_edges = tuple(
        (left, right)
        for left, right, _direction in hamming_edges()
        if left in median_set and right in median_set
    )
    orbit_adjacency_matrix = [[0 for _ in quotient_orbits] for _orbit in quotient_orbits]
    for left, right in median_edges:
        left_orbit = orbit_index[left]
        right_orbit = orbit_index[right]
        if left_orbit == right_orbit:
            orbit_adjacency_matrix[left_orbit][left_orbit] += 1
        else:
            orbit_adjacency_matrix[left_orbit][right_orbit] += 1
            orbit_adjacency_matrix[right_orbit][left_orbit] += 1
    orbit_cross_edges = tuple(
        {
            "left": orbit_names[left],
            "right": orbit_names[right],
            "weight": orbit_adjacency_matrix[left][right],
        }
        for left in range(len(quotient_orbits))
        for right in range(left + 1, len(quotient_orbits))
        if orbit_adjacency_matrix[left][right]
    )
    inactive_layer = median_set - support
    inactive_edges = tuple(
        (left, right)
        for left, right, _direction in hamming_edges()
        if left in inactive_layer and right in inactive_layer
    )
    inactive_complex = cubical_complex_summary(inactive_layer)
    active_inactive_edges = tuple(
        (left, right)
        for left, right, _direction in hamming_edges()
        if (left in support and right in inactive_layer)
        or (right in support and left in inactive_layer)
    )
    inactive_interface: dict[str, list[str]] = collections.defaultdict(list)
    active_interface: dict[str, list[str]] = collections.defaultdict(list)
    for left, right in active_inactive_edges:
        active, inactive = (left, right) if left in support else (right, left)
        inactive_interface[inactive].append(active)
        active_interface[active].append(inactive)
    inactive_interface_rows = [
        {
            "inactive_codon": codon,
            "active_neighbors": tuple(sorted(neighbors)),
            "interface_degree": len(neighbors),
        }
        for codon, neighbors in sorted(inactive_interface.items())
    ]
    active_interface_rows = [
        {
            "active_codon": codon,
            "inactive_neighbors": tuple(sorted(active_interface.get(codon, []))),
            "interface_degree": len(active_interface.get(codon, [])),
        }
        for codon in support_tuple
    ]
    active_interface_rows.sort(key=lambda row: (-row["interface_degree"], row["active_codon"]))
    path_order = ("AGR", "Anchor6", "StopStart6", "UUR", "CUR", "CUY")
    path_indices = tuple(orbit_names.index(name) for name in path_order)
    transition_matrix: list[list[fractions.Fraction]] = []
    leakage_probabilities: list[fractions.Fraction] = []
    for source in path_indices:
        denominator = 6 * len(quotient_orbits[source])
        row: list[fractions.Fraction] = []
        internal_half_edges = 0
        for target in path_indices:
            if source == target:
                half_edges = 2 * orbit_adjacency_matrix[source][target]
            else:
                half_edges = orbit_adjacency_matrix[source][target]
            internal_half_edges += half_edges
            row.append(fractions.Fraction(half_edges, denominator))
        transition_matrix.append(row)
        leakage_probabilities.append(fractions.Fraction(denominator - internal_half_edges, denominator))
    identity_minus_q = [
        [
            (fractions.Fraction(1, 1) if row == column else fractions.Fraction(0, 1))
            - transition_matrix[row][column]
            for column in range(len(path_order))
        ]
        for row in range(len(path_order))
    ]
    expected_exit_times = solve_fraction_linear_system(
        identity_minus_q,
        [fractions.Fraction(1, 1) for _state in path_order],
    )

    def retention_row(name: str, codons: set[str]) -> dict[str, object]:
        edge_count = sum(1 for left, right, _direction in hamming_edges() if left in codons and right in codons)
        boundary_half_edges = 6 * len(codons) - 2 * edge_count
        retention = fractions.Fraction(2 * edge_count, 6 * len(codons))
        return {
            "name": name,
            "vertices": len(codons),
            "internal_edges": edge_count,
            "boundary_half_edges": boundary_half_edges,
            "retention": fraction_string(retention),
            "retention_float": float(retention),
        }

    closure_retention_rows = [
        retention_row("support", support),
        retention_row("anchor_closure", anchor_closure),
        retention_row("median_stage_one", median_stage_one),
        retention_row("median_closure", median_set),
    ]
    acg_stage_one_neighbors = tuple(
        sorted(
            right if left == "ACG" else left
            for left, right, _direction in hamming_edges()
            if "ACG" in (left, right)
            and (right if left == "ACG" else left) in median_stage_one
        )
    )
    acg_boundary_delta = 6 - 2 * len(acg_stage_one_neighbors)

    def killed_walk_matrix(codons: set[str]) -> tuple[tuple[str, ...], list[list[float]]]:
        ordered = tuple(sorted(codons))
        codon_to_index = {codon: index for index, codon in enumerate(ordered)}
        matrix = [[0.0 for _column in ordered] for _row in ordered]
        for left, right, _direction in hamming_edges():
            if left in codon_to_index and right in codon_to_index:
                left_index = codon_to_index[left]
                right_index = codon_to_index[right]
                matrix[left_index][right_index] = 1.0 / 6.0
                matrix[right_index][left_index] = 1.0 / 6.0
        return ordered, matrix

    spectral_closure_sets = (
        ("support", support),
        ("anchor_closure", anchor_closure),
        ("median_stage_one", median_stage_one),
        ("median_closure", median_set),
    )
    spectral_rows: list[dict[str, object]] = []
    median_eigenvector: list[float] = []
    median_ordered_codons: tuple[str, ...] = ()
    median_spectral_radius = 0.0
    for name, codons in spectral_closure_sets:
        ordered_codons, killed_matrix = killed_walk_matrix(codons)
        spectral_radius, eigenvector = dominant_symmetric_eigenpair(killed_matrix)
        retention = next(row for row in closure_retention_rows if row["name"] == name)
        spectral_rows.append(
            {
                "name": name,
                "vertices": len(codons),
                "internal_edges": retention["internal_edges"],
                "retention": retention["retention"],
                "retention_float": retention["retention_float"],
                "spectral_radius": spectral_radius,
                "quasi_lifetime": 1.0 / (1.0 - spectral_radius),
            }
        )
        if name == "median_closure":
            median_ordered_codons = ordered_codons
            median_eigenvector = eigenvector
            median_spectral_radius = spectral_radius

    median_codon_to_spectral_index = {
        codon: index for index, codon in enumerate(median_ordered_codons)
    }
    eigenvector_sum = sum(median_eigenvector)
    quotient_state_sets = {
        name: set(quotient_orbits[orbit_names.index(name)])
        for name in path_order
    }
    qsd_rows: list[dict[str, object]] = []
    survival_rows: list[dict[str, object]] = []
    state_potentials = {
        name: sum(median_eigenvector[median_codon_to_spectral_index[codon]] for codon in codons) / len(codons)
        for name, codons in quotient_state_sets.items()
    }
    max_potential = max(state_potentials.values())
    for name in path_order:
        codons = quotient_state_sets[name]
        mass = sum(
            median_eigenvector[median_codon_to_spectral_index[codon]]
            for codon in codons
        ) / eigenvector_sum
        qsd_rows.append({"state": name, "mass": mass})
        survival_rows.append({"state": name, "potential": state_potentials[name] / max_potential})

    exit_prestates = []
    median_exit_probability = 1.0 - median_spectral_radius
    for row, outside_probability in zip(qsd_rows, leakage_probabilities):
        exit_prestates.append(
            {
                "state": row["state"],
                "conditional_probability": row["mass"] * float(outside_probability) / median_exit_probability,
            }
        )

    outside_target_by_class: collections.Counter[str] = collections.Counter()
    for codon in sorted(median_set):
        codon_index = median_codon_to_spectral_index[codon]
        word = bits(codon)
        for bit_index in range(6):
            neighbor_word = list(word)
            neighbor_word[bit_index] = "1" if neighbor_word[bit_index] == "0" else "0"
            neighbor = codon_from_bits("".join(neighbor_word))
            if neighbor not in median_set:
                outside_target_by_class[standard[neighbor]] += (
                    median_eigenvector[codon_index]
                    / eigenvector_sum
                    * (1.0 / 6.0)
                    / median_exit_probability
                )
    outside_target_rows = [
        {"class": label, "probability": probability}
        for label, probability in outside_target_by_class.items()
    ]
    outside_target_rows.sort(key=lambda row: (-row["probability"], row["class"]))

    def flipped_codon(codon: str, bit_index: int) -> str:
        word = list(bits(codon))
        word[bit_index] = "1" if word[bit_index] == "0" else "0"
        return codon_from_bits("".join(word))

    exit_probability_by_bit: collections.Counter[str] = collections.Counter()
    outside_target_by_codon: collections.Counter[str] = collections.Counter()
    boundary_exit_entries = []
    for codon in sorted(median_set):
        codon_index = median_codon_to_spectral_index[codon]
        source_mass = median_eigenvector[codon_index] / eigenvector_sum
        for bit_index, bit_name in enumerate(BIT_COORDINATES):
            neighbor = flipped_codon(codon, bit_index)
            if neighbor not in median_set:
                probability = source_mass * (1.0 / 6.0) / median_exit_probability
                exit_probability_by_bit[bit_name] += probability
                outside_target_by_codon[neighbor] += probability
                boundary_exit_entries.append(
                    {
                        "source": codon,
                        "target": neighbor,
                        "bit": bit_name,
                        "target_class": standard[neighbor],
                        "probability": probability,
                    }
                )
    boundary_exit_entries.sort(key=lambda row: (row["source"], row["target"], row["bit"]))
    exit_bit_rows = [
        {"bit": bit_name, "probability": exit_probability_by_bit.get(bit_name, 0.0)}
        for bit_name in BIT_COORDINATES
    ]
    exit_bit_rows.sort(key=lambda row: (-row["probability"], row["bit"]))
    outside_target_codon_rows = [
        {
            "codon": codon,
            "class": standard[codon],
            "probability": probability,
        }
        for codon, probability in outside_target_by_codon.items()
    ]
    outside_target_codon_rows.sort(key=lambda row: (-row["probability"], row["codon"]))

    median_order = tuple(sorted(median_set))
    median_order_index = {codon: index for index, codon in enumerate(median_order)}
    internal_transition_matrix = [
        [
            fractions.Fraction(0, 1)
            for _column in median_order
        ]
        for _row in median_order
    ]
    for row, codon in enumerate(median_order):
        for bit_index in range(6):
            neighbor = flipped_codon(codon, bit_index)
            if neighbor in median_order_index:
                internal_transition_matrix[row][median_order_index[neighbor]] += fractions.Fraction(1, 6)
    first_exit_bit_solutions: dict[str, list[fractions.Fraction]] = {}
    identity_minus_internal = [
        [
            (fractions.Fraction(1, 1) if row == column else fractions.Fraction(0, 1))
            - internal_transition_matrix[row][column]
            for column in range(len(median_order))
        ]
        for row in range(len(median_order))
    ]
    for bit_index, bit_name in enumerate(BIT_COORDINATES):
        immediate_exit = [
            fractions.Fraction(1, 6)
            if flipped_codon(codon, bit_index) not in median_order_index
            else fractions.Fraction(0, 1)
            for codon in median_order
        ]
        first_exit_bit_solutions[bit_name] = solve_fraction_linear_system(
            identity_minus_internal,
            immediate_exit,
        )
    eventual_exit_bit_rows = []
    for state in path_order:
        codons = tuple(sorted(quotient_state_sets[state]))
        row = {"state": state}
        for bit_name in BIT_COORDINATES:
            row[bit_name] = float(
                sum(
                    first_exit_bit_solutions[bit_name][median_order_index[codon]]
                    for codon in codons
                )
                / len(codons)
            )
        eventual_exit_bit_rows.append(row)
    first_exit_channel_summary = {
        "origin_rows": exit_prestates,
        "anchor_stopstart_origin_share": sum(
            row["conditional_probability"]
            for row in exit_prestates
            if row["state"] in {"Anchor6", "StopStart6"}
        ),
        "cun_tail_origin_share": sum(
            row["conditional_probability"]
            for row in exit_prestates
            if row["state"] in {"CUR", "CUY"}
        ),
        "exit_bit_rows": exit_bit_rows,
        "gate_axis_exit_share": sum(
            row["probability"]
            for row in exit_bit_rows
            if row["bit"] in {"s3", "f1"}
        ),
        "f3_exit_probability": exit_probability_by_bit.get("f3", 0.0),
        "eventual_exit_bit_rows": eventual_exit_bit_rows,
        "outside_target_class_rows": outside_target_rows,
        "outside_target_codon_rows": outside_target_codon_rows,
        "top_outside_target_codon_rows": outside_target_codon_rows[:14],
        "has_stop_target": any(row["class"] == "*" for row in outside_target_rows),
        "boundary_exit_entries": tuple(boundary_exit_entries),
    }

    def neighbor_count_in_set(codon: str, codons: set[str]) -> int:
        return sum(
            1
            for left, right, _direction in hamming_edges()
            if codon in (left, right)
            and (right if left == codon else left) in codons
        )

    global_codon_order = tuple(all_codons())
    global_codon_index = {codon: index for index, codon in enumerate(global_codon_order)}
    global_neighbors: list[list[int]] = [[] for _codon in global_codon_order]
    for left, right, _direction in hamming_edges():
        left_index = global_codon_index[left]
        right_index = global_codon_index[right]
        global_neighbors[left_index].append(right_index)
        global_neighbors[right_index].append(left_index)

    def spectral_radius_for_set(codons: set[str]) -> float:
        nodes = tuple(sorted(global_codon_index[codon] for codon in codons))
        node_set = set(nodes)
        local_index = {node: index for index, node in enumerate(nodes)}
        adjacency = [
            [local_index[neighbor] for neighbor in global_neighbors[node] if neighbor in node_set]
            for node in nodes
        ]
        size = len(nodes)
        vector = [1.0 / (size ** 0.5) for _node in nodes]
        previous = 0.0
        for _iteration in range(1000):
            action = [
                sum(vector[neighbor] for neighbor in adjacency[row]) / 6.0
                for row in range(size)
            ]
            shifted = [vector[row] + action[row] for row in range(size)]
            norm = sum(entry * entry for entry in shifted) ** 0.5
            vector = [entry / norm for entry in shifted]
            value = sum(
                vector[row] * sum(vector[neighbor] for neighbor in adjacency[row]) / 6.0
                for row in range(size)
            )
            if abs(value - previous) < 1e-13:
                break
            previous = value
        return value

    def spectral_radius_for_edge_set(codons: set[str], edges: set[tuple[str, str]]) -> float:
        ordered = tuple(sorted(codons))
        codon_to_index = {codon: index for index, codon in enumerate(ordered)}
        matrix = [[0.0 for _column in ordered] for _row in ordered]
        for left, right in edges:
            if left in codon_to_index and right in codon_to_index:
                left_index = codon_to_index[left]
                right_index = codon_to_index[right]
                matrix[left_index][right_index] = 1.0 / 6.0
                matrix[right_index][left_index] = 1.0 / 6.0
        radius, _vector = dominant_symmetric_eigenpair(matrix)
        return radius

    def permute_s3_c2(codon: str, permutation: tuple[int, int, int], flip_f3: bool) -> str:
        word = bits(codon)
        bit_values = {
            "s1": word[0],
            "f1": word[1],
            "s2": word[2],
            "f2": word[3],
            "s3": word[4],
            "f3": word[5],
        }
        source_names = ("s1", "s2", "f2")
        target_names = ("s1", "s2", "f2")
        transformed = bit_values.copy()
        for target, source_index in zip(target_names, permutation):
            transformed[target] = bit_values[source_names[source_index]]
        if flip_f3:
            transformed["f3"] = "1" if transformed["f3"] == "0" else "0"
        return codon_from_bits(
            "".join(transformed[name] for name in ("s1", "f1", "s2", "f2", "s3", "f3"))
        )

    def gamma_orbit(codon: str) -> tuple[str, ...]:
        return tuple(
            sorted(
                {
                    permute_s3_c2(codon, permutation, flip_f3)
                    for permutation in itertools.permutations((0, 1, 2))
                    for flip_f3 in (False, True)
                }
            )
        )

    external_codons = set(all_codons()) - median_set
    post_median_single_rows = []
    for codon in sorted(external_codons):
        radius = spectral_radius_for_set(median_set | {codon})
        post_median_single_rows.append(
            {
                "codon": codon,
                "class": standard[codon],
                "spectral_radius": radius,
                "gain": radius - median_spectral_radius,
                "first_exit_probability": outside_target_by_codon.get(codon, 0.0),
            }
        )
    post_median_single_rows.sort(key=lambda row: (-row["spectral_radius"], row["codon"]))
    post_median_best_single_radius = post_median_single_rows[0]["spectral_radius"]
    post_median_best_single_rows = [
        row
        for row in post_median_single_rows
        if abs(row["spectral_radius"] - post_median_best_single_radius) < 1e-12
    ]
    gate_shell = set(row["codon"] for row in post_median_best_single_rows)
    gate_shell_plus = median_set | gate_shell
    gate_shell_radius = spectral_radius_for_set(gate_shell_plus)
    median_retention_for_gate_shell = retention_row("median_closure", median_set)
    gate_shell_retention = retention_row("post_median_gate_shell", gate_shell_plus)
    external_orbits = sorted({gamma_orbit(codon) for codon in external_codons})
    post_median_orbit_rows = []
    for orbit in external_orbits:
        orbit_set = set(orbit)
        radius = spectral_radius_for_set(median_set | orbit_set)
        post_median_orbit_rows.append(
            {
                "orbit": orbit,
                "size": len(orbit),
                "spectral_radius": radius,
                "gain": radius - median_spectral_radius,
                "first_exit_probability": sum(outside_target_by_codon.get(codon, 0.0) for codon in orbit),
            }
        )
    post_median_orbit_rows.sort(key=lambda row: (-row["spectral_radius"], row["orbit"]))
    f3_pair_seen: set[tuple[str, ...]] = set()
    f3_pair_rows = []
    for codon in sorted(external_codons):
        pair = tuple(sorted({codon, flipped_codon(codon, BIT_COORDINATES.index("f3"))}))
        if pair in f3_pair_seen or not set(pair) <= external_codons:
            continue
        f3_pair_seen.add(pair)
        radius = spectral_radius_for_set(median_set | set(pair))
        f3_pair_rows.append(
            {
                "pair": pair,
                "spectral_radius": radius,
                "gain": radius - median_spectral_radius,
                "first_exit_probability": sum(outside_target_by_codon.get(codon, 0.0) for codon in pair),
            }
        )
    f3_pair_rows.sort(key=lambda row: (-row["spectral_radius"], row["pair"]))

    def leakage_by_state(codons: set[str], states: dict[str, set[str]]) -> dict[str, float]:
        result: dict[str, float] = {}
        codon_set = set(codons)
        for state, state_codons in states.items():
            outside_half_edges = 0
            total_half_edges = 6 * len(state_codons)
            for codon in state_codons:
                for bit_index in range(6):
                    if flipped_codon(codon, bit_index) not in codon_set:
                        outside_half_edges += 1
            result[state] = outside_half_edges / total_half_edges
        return result

    gate_shell_edge_groups: collections.Counter[str] = collections.Counter()
    gate_state_sets = dict(quotient_state_sets)
    gate_state_sets["GateShell"] = gate_shell
    gate_state_by_codon = {
        codon: state
        for state, codons in gate_state_sets.items()
        for codon in codons
    }
    gate_state_order = path_order + ("GateShell",)
    gate_state_position = {state: index for index, state in enumerate(gate_state_order)}
    for left, right, _direction in hamming_edges():
        if left in gate_shell_plus and right in gate_shell_plus:
            left_state = gate_state_by_codon[left]
            right_state = gate_state_by_codon[right]
            if left_state == right_state:
                group = f"{left_state}_internal"
            elif gate_state_position[left_state] <= gate_state_position[right_state]:
                group = f"{left_state}-{right_state}"
            else:
                group = f"{right_state}-{left_state}"
            gate_shell_edge_groups[group] += 1
    post_median_gate_shell_summary = {
        "gate_shell": tuple(sorted(gate_shell)),
        "gate_shell_iupac": ("CAR", "CCR", "GTR"),
        "single_point_candidate_count": len(external_codons),
        "best_single_rows": post_median_best_single_rows,
        "best_single_spectral_radius": post_median_best_single_radius,
        "best_single_gain": post_median_best_single_radius - median_spectral_radius,
        "top_single_rows": post_median_single_rows[:12],
        "external_gamma_orbit_count": len(external_orbits),
        "orbit_rows": post_median_orbit_rows,
        "best_orbit": post_median_orbit_rows[0],
        "f3_pair_rows": f3_pair_rows,
        "best_f3_pair_rows": [
            row for row in f3_pair_rows if abs(row["spectral_radius"] - f3_pair_rows[0]["spectral_radius"]) < 1e-12
        ],
        "post_median_vertices": len(gate_shell_plus),
        "post_median_internal_edges": gate_shell_retention["internal_edges"],
        "post_median_retention": gate_shell_retention["retention"],
        "post_median_retention_float": gate_shell_retention["retention_float"],
        "post_median_spectral_radius": gate_shell_radius,
        "post_median_spectral_gain": gate_shell_radius - median_spectral_radius,
        "median_retention_float": median_retention_for_gate_shell["retention_float"],
        "median_spectral_radius": median_spectral_radius,
        "leakage_before": leakage_by_state(median_set, quotient_state_sets),
        "leakage_after": leakage_by_state(gate_shell_plus, quotient_state_sets),
        "edge_group_counts": dict(sorted(gate_shell_edge_groups.items())),
        "cur_neighbors_after": {
            codon: tuple(sorted(flipped_codon(codon, bit_index) for bit_index in range(6)))
            for codon in sorted(quotient_state_sets["CUR"])
        },
        "stopstart_gate_edges": gate_shell_edge_groups["StopStart6-GateShell"],
        "gate_cur_edges": gate_shell_edge_groups["CUR-GateShell"],
    }

    def motif_codons(pattern: str) -> set[str]:
        return set(expand_iupac_motif(pattern))

    mstar_set = motif_codons("NNR") | motif_codons("CUY")
    full_cube_set = set(all_codons())
    cuy_bits_prefix = bits("CTT")[:4]
    y_shells: dict[int, set[str]] = {index: set() for index in range(5)}
    for codon in full_cube_set:
        word = bits(codon)
        if word[4] != "0":
            continue
        distance = sum(left != right for left, right in zip(word[:4], cuy_bits_prefix))
        y_shells[distance].add(codon)
    mstar_closure, mstar_closure_stages = median_closure(mstar_set)
    shell_trigger_rows = []
    for shell_index in range(1, 5):
        start_set = mstar_set | y_shells[shell_index]
        closure, stages = median_closure(start_set)
        shell_trigger_rows.append(
            {
                "shell": f"H{shell_index}",
                "shell_index": shell_index,
                "shell_size": len(y_shells[shell_index]),
                "start_size": len(start_set),
                "closure_size": len(closure),
                "stage_additions": tuple(
                    {
                        "stage": stage["stage"],
                        "added_count": stage["added_count"],
                        "total_size": stage["total_size"],
                    }
                    for stage in stages
                ),
                "closure_is_full_cube": closure == full_cube_set,
            }
        )
    single_antipode_rows = []
    for codon in sorted(y_shells[4]):
        closure, stages = median_closure(mstar_set | {codon})
        single_antipode_rows.append(
            {
                "codon": codon,
                "closure_size": len(closure),
                "stage_count": len(stages),
                "stage_additions": tuple(
                    {
                        "stage": stage["stage"],
                        "added_count": stage["added_count"],
                        "total_size": stage["total_size"],
                    }
                    for stage in stages
                ),
                "closure_is_full_cube": closure == full_cube_set,
            }
        )
    single_trigger_rows = []
    mstar_base_radius = spectral_radius_for_set(mstar_set)
    for shell_index in range(1, 5):
        shell_codons = sorted(y_shells[shell_index])
        representative = shell_codons[0]
        closure, stages = median_closure(mstar_set | {representative})
        radius = spectral_radius_for_set(mstar_set | {representative})
        single_trigger_rows.append(
            {
                "shell": f"H{shell_index}",
                "representative": representative,
                "shell_size": len(shell_codons),
                "median_closure_size": len(closure),
                "stage_count": len(stages),
                "spectral_radius": radius,
                "gain": radius - mstar_base_radius,
            }
        )
    shell_filling_rows = []
    cumulative = set(y_shells[0])
    for shell_index in range(5):
        if shell_index:
            cumulative |= y_shells[shell_index]
        shell_set = motif_codons("NNR") | cumulative
        retention = retention_row(f"mstar_shell_{shell_index}", shell_set)
        shell_filling_rows.append(
            {
                "level": f"S{shell_index}",
                "size": len(shell_set),
                "structure": "NNR+H0" if shell_index == 0 else f"+H{shell_index}",
                "spectral_radius": spectral_radius_for_set(shell_set),
                "retention": retention["retention"],
                "retention_float": retention["retention_float"],
                "internal_edges": retention["internal_edges"],
            }
        )
    y_external_codons = sorted(full_cube_set - mstar_set)

    def anchor_support(codon: str) -> frozenset[int]:
        return frozenset(
            index
            for index, (left, right) in enumerate(zip(bits(codon)[:4], cuy_bits_prefix))
            if left != right
        )

    def span_dimension(codons: set[str]) -> int:
        support: set[int] = set()
        for codon in codons:
            support.update(anchor_support(codon))
        return len(support)

    def predicted_mstar_closure_for_support(support: set[int] | frozenset[int]) -> set[str]:
        y_side = {
            codon
            for codon in full_cube_set
            if bits(codon)[4] == "0"
            and all(
                (index in support) or (bits(codon)[index] == cuy_bits_prefix[index])
                for index in range(4)
            )
        }
        return motif_codons("NNR") | y_side

    def predicted_mstar_closure(codons: set[str]) -> set[str]:
        support: set[int] = set()
        for codon in codons:
            support.update(anchor_support(codon))
        return predicted_mstar_closure_for_support(support)

    coordinate_universe = frozenset(range(4))
    support_patterns = tuple(
        frozenset(pattern)
        for support_size in range(5)
        for pattern in itertools.combinations(range(4), support_size)
    )
    external_closure_sets = {
        support_pattern: frozenset(
            codon
            for codon in y_external_codons
            if anchor_support(codon) <= support_pattern
        )
        for support_pattern in support_patterns
    }
    coverage_closure_rows = [
        {
            "rank": len(support_pattern),
            "support": tuple(BIT_COORDINATES[index] for index in support_pattern),
            "external_closure_size": len(external_closure_sets[support_pattern]),
            "external_closure_formula_size": 2 * ((2 ** len(support_pattern)) - 1),
            "median_closure_size": len(mstar_set) + len(external_closure_sets[support_pattern]),
        }
        for support_pattern in support_patterns
    ]
    coverage_closure_formula_verified = all(
        row["external_closure_size"] == row["external_closure_formula_size"]
        and row["median_closure_size"] == 32 + (2 ** (row["rank"] + 1))
        for row in coverage_closure_rows
    )
    coverage_closure_lattice_verified = all(
        (external_closure_sets[left] & external_closure_sets[right])
        == external_closure_sets[left & right]
        and external_closure_sets[left] | external_closure_sets[right]
        <= external_closure_sets[left | right]
        for left in support_patterns
        for right in support_patterns
    )
    span_size_rows = [
        {
            "span_dimension": dimension,
            "closure_size": 32 + (2 ** (dimension + 1)),
        }
        for dimension in range(5)
    ]
    single_span_rows = []
    for shell_index in range(1, 5):
        closure_size = 32 + (2 ** (shell_index + 1))
        single_span_rows.append(
            {
                "shell": f"H{shell_index}",
                "shell_size": len(y_shells[shell_index]),
                "span_dimension": shell_index,
                "closure_size": closure_size,
            }
        )
    trigger_count_rows = []
    for added_size in range(1, 5):
        counts: collections.Counter[int] = collections.Counter()
        for subset in itertools.combinations(y_external_codons, added_size):
            subset_set = set(subset)
            dimension = span_dimension(subset_set)
            counts[32 + (2 ** (dimension + 1))] += 1
        trigger_count_rows.append(
            {
                "added_size": added_size,
                "candidate_count": sum(counts.values()),
                "closure_size_counts": dict(sorted(counts.items())),
                "full_cube_count": counts[64],
            }
        )
    support_pattern_verification_rows = []
    for support_size in range(1, 5):
        for support_pattern in itertools.combinations(range(4), support_size):
            representative = next(
                codon
                for codon in y_external_codons
                if anchor_support(codon) == frozenset(support_pattern)
            )
            subset_set = {representative}
            closure, _stages = median_closure(mstar_set | subset_set)
            predicted = predicted_mstar_closure(subset_set)
            support_pattern_verification_rows.append(
                {
                    "support": tuple(BIT_COORDINATES[index] for index in support_pattern),
                    "representative": representative,
                    "closure_size": len(closure),
                    "predicted_size": len(predicted),
                    "matches_formula": closure == predicted,
                }
            )
    trigger_lattice_sets = {
        support_pattern: predicted_mstar_closure_for_support(support_pattern)
        for support_pattern in support_patterns
    }
    boolean_lattice_intersection_verified = all(
        (trigger_lattice_sets[left] & trigger_lattice_sets[right])
        == trigger_lattice_sets[left & right]
        for left in support_patterns
        for right in support_patterns
    )
    boolean_lattice_median_join_verified = True
    for left in support_patterns:
        for right in support_patterns:
            joined_closure, _joined_stages = median_closure(trigger_lattice_sets[left] | trigger_lattice_sets[right])
            if joined_closure != trigger_lattice_sets[left | right]:
                boolean_lattice_median_join_verified = False
                break
        if not boolean_lattice_median_join_verified:
            break

    def cubical_formula_f_vector(rank: int) -> tuple[int, ...]:
        max_dimension = max(5, rank + 2)
        return tuple(
            (
                (2 ** (5 - cell_dimension)) * math.comb(5, cell_dimension)
                + (2 ** (rank + 2 - cell_dimension)) * math.comb(rank + 2, cell_dimension)
                - (2 ** (rank + 1 - cell_dimension)) * math.comb(rank + 1, cell_dimension)
            )
            for cell_dimension in range(max_dimension + 1)
        )

    boolean_lattice_rank_rows = []
    quotient_spectral_equations = {
        0: "mu^6 - 21 mu^4 + 80 mu^2 - 24 = 0",
        1: "mu^4 - 4 mu^3 - 5 mu^2 + 18 mu + 6 = 0",
        2: "mu^4 - 8 mu^3 + 19 mu^2 - 12 mu - 2 = 0",
        3: "mu^2 - 6 mu + 7 = 0",
        4: "mu - 5 = 0",
    }
    quotient_spectral_polynomials = {
        0: lambda value: value**6 - 21 * value**4 + 80 * value**2 - 24,
        1: lambda value: value**4 - 4 * value**3 - 5 * value**2 + 18 * value + 6,
        2: lambda value: value**4 - 8 * value**3 + 19 * value**2 - 12 * value - 2,
        3: lambda value: value**2 - 6 * value + 7,
        4: lambda value: value - 5,
    }

    def largest_positive_root(polynomial: collections.abc.Callable[[float], float], upper_bound: float = 6.0) -> float:
        intervals: list[tuple[float, float]] = []
        previous_x = 0.0
        previous_value = polynomial(previous_x)
        steps = 6000
        for step in range(1, steps + 1):
            current_x = upper_bound * step / steps
            current_value = polynomial(current_x)
            if current_value == 0.0:
                intervals.append((current_x, current_x))
            elif previous_value == 0.0 or previous_value * current_value < 0.0:
                intervals.append((previous_x, current_x))
            previous_x = current_x
            previous_value = current_value
        lower, upper = intervals[-1]
        if lower == upper:
            return lower
        lower_value = polynomial(lower)
        for _iteration in range(100):
            middle = (lower + upper) / 2.0
            middle_value = polynomial(middle)
            if lower_value * middle_value <= 0.0:
                upper = middle
            else:
                lower = middle
                lower_value = middle_value
        return (lower + upper) / 2.0

    quotient_spectrum_rows = []
    for rank in range(5):
        support_pattern = frozenset(range(rank))
        closure_set = trigger_lattice_sets[support_pattern]
        complex_summary = cubical_complex_summary(closure_set)
        f_vector = tuple(value for value in complex_summary["f_vector"] if value)
        spectral_radius = spectral_radius_for_set(closure_set)
        quotient_root = largest_positive_root(quotient_spectral_polynomials[rank])
        quotient_spectrum_rows.append(
            {
                "rank": rank,
                "equation": quotient_spectral_equations[rank],
                "mu": quotient_root,
                "lambda_from_mu": (quotient_root + 1.0) / 6.0,
                "lambda_matches_rank_radius": abs(((quotient_root + 1.0) / 6.0) - spectral_radius) < 1e-8,
            }
        )
        boolean_lattice_rank_rows.append(
            {
                "rank": rank,
                "support": tuple(BIT_COORDINATES[index] for index in support_pattern),
                "closure_size": len(closure_set),
                "f_vector": f_vector,
                "f_vector_formula": cubical_formula_f_vector(rank),
                "f_vector_matches_formula": f_vector == cubical_formula_f_vector(rank),
                "spectral_radius": spectral_radius,
            }
        )

    def trigger_rank_count(added_size: int, rank: int) -> int:
        total = 0
        for omitted in range(rank + 1):
            total += (
                ((-1) ** omitted)
                * math.comb(rank, omitted)
                * math.comb(2 * ((2 ** (rank - omitted)) - 1), added_size)
            )
        return math.comb(4, rank) * total

    rank_distribution_rows = []
    for added_size in range(1, 7):
        rank_counts = {
            rank: trigger_rank_count(added_size, rank)
            for rank in range(1, 5)
        }
        candidate_count = math.comb(len(y_external_codons), added_size)
        rank_distribution_rows.append(
            {
                "added_size": added_size,
                "candidate_count": candidate_count,
                "rank_counts": rank_counts,
                "full_cube_count": rank_counts[4],
                "full_cube_probability": rank_counts[4] / candidate_count,
                "counts_sum_to_candidate_count": sum(rank_counts.values()) == candidate_count,
            }
        )
    trigger_count_formula_matches_enumeration = all(
        {
            32 + (2 ** (rank + 1)): row["rank_counts"][rank]
            for rank in range(1, 5)
            if row["rank_counts"][rank]
        }
        == trigger_count_rows[row["added_size"] - 1]["closure_size_counts"]
        for row in rank_distribution_rows[:4]
    )
    rank_spectral_radius = {
        row["rank"]: row["spectral_radius"]
        for row in boolean_lattice_rank_rows
    }
    maximum_nontrigger_rank = 3
    maximum_nontrigger_external_size = 2 * ((2 ** maximum_nontrigger_rank) - 1)
    maximum_nontrigger_blocker_count = math.comb(4, maximum_nontrigger_rank)

    def rank_count_for_draw(added_size: int, rank: int) -> int:
        if rank == 0:
            return 1 if added_size == 0 else 0
        return trigger_rank_count(added_size, rank)

    def rank_probabilities(added_size: int) -> dict[int, float]:
        denominator = math.comb(len(y_external_codons), added_size)
        return {
            rank: rank_count_for_draw(added_size, rank) / denominator
            for rank in range(5)
        }

    random_trigger_probability_rows = []
    trigger_cdf_by_size = {0: 0.0}
    for added_size in range(1, 11):
        candidate_count = math.comb(len(y_external_codons), added_size)
        full_count = trigger_rank_count(added_size, 4)
        probability = full_count / candidate_count
        trigger_cdf_by_size[added_size] = probability
        random_trigger_probability_rows.append(
            {
                "added_size": added_size,
                "candidate_count": candidate_count,
                "full_trigger_count": full_count,
                "full_trigger_probability": probability,
            }
        )
    trigger_time_rows = []
    for added_size in range(1, 11):
        probability_mass = trigger_cdf_by_size[added_size] - trigger_cdf_by_size[added_size - 1]
        survival_before = 1.0 - trigger_cdf_by_size[added_size - 1]
        trigger_time_rows.append(
            {
                "trigger_time": added_size,
                "probability": probability_mass,
                "hazard": probability_mass / survival_before,
            }
        )
    expected_trigger_time = sum(
        1.0 - (
            trigger_rank_count(added_size, 4) / math.comb(len(y_external_codons), added_size)
            if added_size > 0
            else 0.0
        )
        for added_size in range(0, maximum_nontrigger_external_size + 1)
    )
    trigger_quantile_rows = []
    for quantile in (0.5, 0.9, 0.95, 0.99):
        threshold = next(
            added_size
            for added_size in range(1, maximum_nontrigger_external_size + 2)
            if trigger_rank_count(added_size, 4) / math.comb(len(y_external_codons), added_size) >= quantile
        )
        trigger_quantile_rows.append(
            {
                "quantile": quantile,
                "threshold": threshold,
            }
        )
    expected_rank_rows = []
    for added_size in range(1, 8):
        probabilities = rank_probabilities(added_size)
        expected_rank = sum(rank * probability for rank, probability in probabilities.items())
        formula_value = 4.0 * (
            1.0 - (math.comb(maximum_nontrigger_external_size, added_size) / math.comb(len(y_external_codons), added_size))
        )
        expected_rank_rows.append(
            {
                "added_size": added_size,
                "expected_rank": expected_rank,
                "formula_value": formula_value,
            }
        )
    expected_closure_rows = []
    expected_spectral_rows = []
    for added_size in range(0, 11):
        probabilities = rank_probabilities(added_size)
        expected_closure_rows.append(
            {
                "added_size": added_size,
                "expected_closure_size": sum((32 + (2 ** (rank + 1))) * probability for rank, probability in probabilities.items()),
            }
        )
        expected_spectral_rows.append(
            {
                "added_size": added_size,
                "expected_spectral_radius": sum(rank_spectral_radius[rank] * probability for rank, probability in probabilities.items()),
            }
        )

    def markov_transition_probabilities(added_size: int, rank: int) -> dict[int, float]:
        if rank == 4:
            return {4: 1.0}
        denominator = len(y_external_codons) - added_size
        transitions: dict[int, float] = {}
        same_count = 2 * ((2 ** rank) - 1) - added_size
        if same_count:
            transitions[rank] = same_count / denominator
        for increase in range(1, 5 - rank):
            target_rank = rank + increase
            transitions[target_rank] = (
                2 * (2 ** rank) * math.comb(4 - rank, increase) / denominator
            )
        return transitions

    markov_transition_state_rows = []
    for added_size, rank in ((0, 0), (1, 1), (1, 2), (1, 3), (2, 2), (3, 3), (6, 3)):
        transitions = markov_transition_probabilities(added_size, rank)
        markov_transition_state_rows.append(
            {
                "state": (added_size, rank),
                "transitions": transitions,
                "direct_trigger_probability": transitions.get(4, 0.0),
                "expected_rank_increment": sum((target_rank - rank) * probability for target_rank, probability in transitions.items()),
                "drift_formula_value": 16 * (4 - rank) / (len(y_external_codons) - added_size),
                "probability_sum": sum(transitions.values()),
            }
        )

    @functools.cache
    def markov_remaining_mean(added_size: int, rank: int) -> float:
        if rank == 4:
            return 0.0
        transitions = markov_transition_probabilities(added_size, rank)
        return 1.0 + sum(
            probability * markov_remaining_mean(added_size + 1, target_rank)
            for target_rank, probability in transitions.items()
        )

    @functools.cache
    def markov_remaining_second_moment(added_size: int, rank: int) -> float:
        if rank == 4:
            return 0.0
        transitions = markov_transition_probabilities(added_size, rank)
        return sum(
            probability
            * (
                1.0
                + 2.0 * markov_remaining_mean(added_size + 1, target_rank)
                + markov_remaining_second_moment(added_size + 1, target_rank)
            )
            for target_rank, probability in transitions.items()
        )

    trigger_time_variance = markov_remaining_second_moment(0, 0) - (markov_remaining_mean(0, 0) ** 2)
    markov_remaining_time_rows = [
        {
            "state": state,
            "expected_remaining_steps": markov_remaining_mean(*state),
        }
        for state in (
            (0, 0),
            (1, 1),
            (1, 2),
            (1, 3),
            (2, 1),
            (2, 2),
            (2, 3),
            (3, 2),
            (3, 3),
            (6, 2),
            (6, 3),
        )
    ]

    blocker_coordinate_rows = []
    maximal_blocker_sets: dict[int, set[str]] = {}
    coordinate_motifs = {
        0: "YNY",
        1: "SNY",
        2: "NYY",
        3: "NWY",
    }
    for coordinate in range(4):
        blocker = {
            codon
            for codon in y_external_codons
            if coordinate not in anchor_support(codon)
        }
        maximal_blocker_sets[coordinate] = blocker
        blocker_coordinate_rows.append(
            {
                "missing_coordinate": BIT_COORDINATES[coordinate],
                "motif": coordinate_motifs[coordinate],
                "size": len(blocker),
            }
        )
    blocker_intersection_rows = []
    for missing_count in range(1, 5):
        sizes = sorted(
            len(set.intersection(*(maximal_blocker_sets[coordinate] for coordinate in missing_coordinates)))
            for missing_coordinates in itertools.combinations(range(4), missing_count)
        )
        blocker_intersection_rows.append(
            {
                "missing_coordinate_count": missing_count,
                "intersection_sizes": tuple(sizes),
                "common_size": sizes[0],
                "formula_size": 2 * ((2 ** (4 - missing_count)) - 1),
            }
        )
    blocker_nerve = {
        "vertex_count": 4,
        "edge_count": math.comb(4, 2),
        "triangle_count": math.comb(4, 3),
        "tetrahedron_count": 0,
        "is_tetrahedron_boundary": all(row["common_size"] > 0 for row in blocker_intersection_rows[:3])
        and blocker_intersection_rows[3]["common_size"] == 0,
    }
    blocker_f_vector = tuple(
        4 * math.comb(14, face_size)
        - 6 * math.comb(6, face_size)
        + 4 * math.comb(2, face_size)
        for face_size in range(1, 15)
    )
    blocker_independence_coefficients = (1,) + blocker_f_vector
    blocker_dimension = 13
    stanley_reisner_dimension = blocker_dimension + 1
    thickened_sphere_rows = (
        {"intersection_kind": "facet", "vertex_count": 14, "simplex_dimension": 13, "multiplicity": 4},
        {"intersection_kind": "pair", "vertex_count": 6, "simplex_dimension": 5, "multiplicity": 6},
        {"intersection_kind": "triple", "vertex_count": 2, "simplex_dimension": 1, "multiplicity": 4},
        {
            "intersection_kind": "quadruple",
            "vertex_count": 0,
            "simplex_dimension": -1,
            "multiplicity": 1,
        },
    )
    blocker_hilbert_series = "4/(1-z)^14 - 6/(1-z)^6 + 4/(1-z)^2 - 1"
    blocker_h_polynomial = "4 - 6(1-z)^8 + 4(1-z)^12 - (1-z)^14"
    blocker_h_vector = [0 for _degree in range(stanley_reisner_dimension + 1)]
    blocker_h_vector[0] += 4
    for degree in range(9):
        blocker_h_vector[degree] -= 6 * ((-1) ** degree) * math.comb(8, degree)
    for degree in range(13):
        blocker_h_vector[degree] += 4 * ((-1) ** degree) * math.comb(12, degree)
    for degree in range(15):
        blocker_h_vector[degree] -= ((-1) ** degree) * math.comb(14, degree)
    blocker_h_vector = tuple(blocker_h_vector)
    blocker_is_cohen_macaulay = False
    blocker_non_cm_witness = {
        "complex_dimension": blocker_dimension,
        "homology_degree": 2,
        "reduced_homology_rank": 1,
    }
    blocker_projective_dimension = len(y_external_codons) - 3
    blocker_depth = 3
    blocker_regularity = 3
    blocker_cohen_macaulay_defect = stanley_reisner_dimension - blocker_depth
    blocker_hochster_witness = {
        "betti_i": blocker_projective_dimension,
        "betti_j": len(y_external_codons),
        "homology_degree": 2,
        "betti_value": 1,
    }
    local_link_stratification_rows = []
    for rank in range(4):
        saturated_face_sizes = set()
        link_lift_counts = set()
        link_sphere_dimensions = set()
        saturated_face_count = 0
        for coordinate_subset in itertools.combinations(range(4), rank):
            coordinate_set = frozenset(coordinate_subset)
            saturated_face = {
                codon
                for codon in y_external_codons
                if anchor_support(codon) <= coordinate_set
            }
            saturated_face_count += 1
            saturated_face_sizes.add(len(saturated_face))
            link_lift_counts.add(2 * (2 ** rank))
            link_sphere_dimensions.add((4 - rank) - 2)
        local_link_stratification_rows.append(
            {
                "support_rank": rank,
                "saturated_face_count": saturated_face_count,
                "saturated_face_sizes": tuple(sorted(saturated_face_sizes)),
                "link_coordinate_count": 4 - rank,
                "link_lift_count": tuple(sorted(link_lift_counts))[0],
                "link_sphere_dimension": tuple(sorted(link_sphere_dimensions))[0],
            }
        )
    local_link_examples = {
        "unit_s1_face": tuple(
            sorted(
                codon
                for codon in y_external_codons
                if anchor_support(codon) <= frozenset({0})
            )
        ),
        "unit_s1_link_sphere_dimension": 1,
        "first_base_face": tuple(
            sorted(
                codon
                for codon in y_external_codons
                if anchor_support(codon) <= frozenset({0, 1})
            )
        ),
        "first_base_link_sphere_dimension": 0,
    }
    local_link_non_saturated_links_are_cones = True
    blocker_is_buchsbaum = False
    blocker_buchsbaum_obstruction = {
        "face_support_rank": 1,
        "link_complex_dimension": 11,
        "link_homology_dimension": 1,
    }
    hochster_nerve_vertex_count = 4
    hochster_possible_homology_degrees = (-1, 0, 1, 2)
    hochster_betti_diagonals = (0, 1, 2, 3)
    top_betti_strand_rows = [
        {
            "j": degree,
            "i": degree - 3,
            "betti": sum(
                math.comb(4, singleton_double_lift_count)
                * (2 ** (4 - singleton_double_lift_count))
                * math.comb(22, degree - 4 - singleton_double_lift_count)
                for singleton_double_lift_count in range(5)
                if 0 <= degree - 4 - singleton_double_lift_count <= 22
            ),
        }
        for degree in range(4, 31)
    ]
    top_betti_strand_generating_function = "(2x+x^2)^4(1+x)^22"
    betti_table_diagonal_rows = (
        {"diagonal": 0, "homology_degree": -1, "nonzero_count": 3},
        {"diagonal": 1, "homology_degree": 0, "nonzero_count": 17},
        {"diagonal": 2, "homology_degree": 1, "nonzero_count": 24},
        {"diagonal": 3, "homology_degree": 2, "nonzero_count": 27},
    )
    blocker_euler_characteristic = sum(
        ((-1) ** index) * count
        for index, count in enumerate(blocker_f_vector)
    )
    blocker_probability_tail_rows = []
    for added_size in range(1, 11):
        blocker_count = blocker_f_vector[added_size - 1]
        candidate_count = math.comb(len(y_external_codons), added_size)
        blocker_probability_tail_rows.append(
            {
                "added_size": added_size,
                "blocker_count": blocker_count,
                "nontrigger_probability": blocker_count / candidate_count,
                "full_trigger_probability": 1.0 - (blocker_count / candidate_count),
            }
        )
    alexander_dual_generator_rows = []
    for coordinate in range(4):
        generator_codons = tuple(
            sorted(codon for codon in y_external_codons if coordinate in anchor_support(codon))
        )
        alexander_dual_generator_rows.append(
            {
                "coordinate": BIT_COORDINATES[coordinate],
                "degree": len(generator_codons),
                "codons": generator_codons,
            }
        )
    alexander_dual_lcm_rows = []
    for subset_size in range(1, 5):
        degrees = []
        for coordinate_subset in itertools.combinations(range(4), subset_size):
            lcm_codons = {
                codon
                for codon in y_external_codons
                if anchor_support(codon) & frozenset(coordinate_subset)
            }
            degrees.append(len(lcm_codons))
        alexander_dual_lcm_rows.append(
            {
                "subset_size": subset_size,
                "subset_count": math.comb(4, subset_size),
                "lcm_degrees": tuple(sorted(degrees)),
                "formula_degree": 32 - (2 ** (5 - subset_size)),
                "reliability_coefficient": ((-1) ** (subset_size + 1)) * math.comb(4, subset_size),
            }
        )
    alexander_dual_resolution_rows = [
        {
            "homological_position": subset_size,
            "rank": math.comb(4, subset_size),
            "shift": 32 - (2 ** (5 - subset_size)),
        }
        for subset_size in range(1, 5)
    ]
    alexander_dual_betti_pattern = (1, 4, 6, 4, 1)
    alexander_dual_reliability_terms = tuple(
        (
            row["subset_size"],
            row["reliability_coefficient"],
            row["formula_degree"],
        )
        for row in alexander_dual_lcm_rows
    )

    nonempty_support_patterns = tuple(pattern for pattern in support_patterns if pattern)
    hochster_diagonal_coefficients = {-1: [0 for _degree in range(31)], 0: [0 for _degree in range(31)], 1: [0 for _degree in range(31)], 2: [0 for _degree in range(31)]}
    support_level_betti_coefficients = {-1: [0 for _degree in range(16)], 0: [0 for _degree in range(16)], 1: [0 for _degree in range(16)], 2: [0 for _degree in range(16)]}
    support_nerve_signature_counts: collections.Counter[tuple[int, int, int, int]] = collections.Counter()
    boundary_face_masks = tuple(range(15))

    def is_boundary_subcomplex(face_family: set[int]) -> bool:
        for face in face_family:
            subface = face
            while True:
                if subface not in face_family:
                    return False
                if subface == 0:
                    break
                subface = (subface - 1) & face
        return True

    def maximal_faces(face_family: set[int]) -> set[int]:
        return {
            face
            for face in face_family
            if not any(face != other and (face & ~other) == 0 for other in face_family)
        }

    support_to_nerve_subcomplex_signature_counts: collections.Counter[tuple[int, int, int, int]] = collections.Counter()
    support_to_nerve_fiber_total = 0
    support_to_nerve_h2_subcomplex_count = 0
    for subcomplex_bits in range(1 << len(boundary_face_masks)):
        subcomplex_faces = {
            face
            for face_index, face in enumerate(boundary_face_masks)
            if (subcomplex_bits >> face_index) & 1
        }
        if not is_boundary_subcomplex(subcomplex_faces):
            continue
        subcomplex_nonempty_faces = {face for face in subcomplex_faces if face}
        reduced_betti = simplicial_reduced_betti(subcomplex_nonempty_faces, 4)
        signature = tuple(reduced_betti.get(homology_degree, 0) for homology_degree in (-1, 0, 1, 2))
        subcomplex_facets = maximal_faces(subcomplex_faces)
        support_to_nerve_subcomplex_signature_counts[signature] += 1
        support_to_nerve_fiber_total += 2 ** (len(subcomplex_faces) - len(subcomplex_facets))
        if signature == (0, 0, 0, 1):
            support_to_nerve_h2_subcomplex_count += 1
    for support_type_size in range(len(nonempty_support_patterns) + 1):
        lift_coefficients = [
            math.comb(support_type_size, double_lift_count) * (2 ** (support_type_size - double_lift_count))
            for double_lift_count in range(support_type_size + 1)
        ]
        for support_type_subset in itertools.combinations(nonempty_support_patterns, support_type_size):
            nerve_faces: set[int] = set()
            for face_size in range(1, 5):
                for coordinate_subset in itertools.combinations(range(4), face_size):
                    coordinate_mask = sum(1 << coordinate for coordinate in coordinate_subset)
                    if any(support.isdisjoint(coordinate_subset) for support in support_type_subset):
                        nerve_faces.add(coordinate_mask)
            reduced_betti = simplicial_reduced_betti(nerve_faces, 4)
            signature = tuple(reduced_betti.get(homology_degree, 0) for homology_degree in (-1, 0, 1, 2))
            support_nerve_signature_counts[signature] += 1
            for homology_degree, betti_value in reduced_betti.items():
                support_level_betti_coefficients[homology_degree][support_type_size] += betti_value
                for double_lift_count, coefficient in enumerate(lift_coefficients):
                    total_degree = support_type_size + double_lift_count
                    hochster_diagonal_coefficients[homology_degree][total_degree] += betti_value * coefficient
    support_nerve_signature_rows = [
        {
            "signature": signature,
            "support_family_count": count,
        }
        for signature, count in sorted(support_nerve_signature_counts.items())
    ]
    support_nerve_census_total = sum(support_nerve_signature_counts.values())
    support_nerve_contractible_count = support_nerve_signature_counts[(0, 0, 0, 0)]
    support_nerve_h2_count = support_nerve_signature_counts[(0, 0, 0, 1)]
    support_to_nerve_subcomplex_signature_rows = [
        {
            "signature": signature,
            "subcomplex_count": count,
        }
        for signature, count in sorted(support_to_nerve_subcomplex_signature_counts.items())
    ]
    support_to_nerve_subcomplex_total = sum(support_to_nerve_subcomplex_signature_counts.values())
    support_level_betti_rows = [
        {
            "homology_degree": homology_degree,
            "coefficients": tuple(coefficients),
            "nonzero_count": sum(1 for coefficient in coefficients if coefficient),
            "total_support_mass": sum(coefficients),
        }
        for homology_degree, coefficients in sorted(support_level_betti_coefficients.items())
    ]
    hochster_diagonal_rows = [
        {
            "homology_degree": homology_degree,
            "diagonal": homology_degree + 1,
            "coefficients": tuple(coefficients),
            "nonzero_count": sum(1 for coefficient in coefficients if coefficient),
            "total_betti_mass": sum(coefficients),
        }
        for homology_degree, coefficients in sorted(hochster_diagonal_coefficients.items())
    ]
    hochster_diagonal_generating_functions = {
        -1: "(1+x)^2",
        0: "x^2(x+1)^2(x+2)^2P0(x)",
        1: "x^3(x+1)^10(x+2)^3P1(x)",
        2: "x^4(x+1)^22(x+2)^4",
    }
    support_level_betti_generating_functions = {
        -1: "1+z",
        0: "z^2(1+z)(4z^6+28z^5+87z^4+152z^3+157z^2+92z+25)",
        1: "z^3(1+z)^5(6z^5+38z^4+99z^3+132z^2+89z+22)",
        2: "z^4(1+z)^11",
    }
    support_lift_substitution = "z=(1+x)^2-1=2x+x^2"
    hochster_p0_coefficients_desc = (4, 48, 268, 920, 2167, 3704, 4736, 4592, 3373, 1844, 720, 184, 25)
    hochster_p1_coefficients_desc = (6, 60, 278, 784, 1491, 2002, 1928, 1320, 617, 178, 22)
    quotient_minimal_trigger_counts: collections.Counter[int] = collections.Counter()
    quotient_minimal_trigger_type_counts: collections.Counter[tuple[int, ...]] = collections.Counter()
    for trigger_size in range(1, 5):
        for family in itertools.combinations(nonempty_support_patterns, trigger_size):
            union_support = frozenset().union(*family)
            if union_support != coordinate_universe:
                continue
            is_minimal = all(
                frozenset().union(*(other for index, other in enumerate(family) if index != removed_index))
                != coordinate_universe
                for removed_index in range(len(family))
            )
            if is_minimal:
                quotient_minimal_trigger_counts[trigger_size] += 1
                support_size_type = tuple(sorted(len(support) for support in family))
                quotient_minimal_trigger_type_counts[support_size_type] += 1
    minimal_trigger_rows = [
        {
            "trigger_size": trigger_size,
            "quotient_count": quotient_minimal_trigger_counts[trigger_size],
            "codon_count": quotient_minimal_trigger_counts[trigger_size] * (2 ** trigger_size),
        }
        for trigger_size in range(1, 5)
    ]
    minimal_trigger_type_rows = [
        {
            "trigger_size": len(support_size_type),
            "support_size_type": support_size_type,
            "energy": sum(support_size_type),
            "quotient_count": quotient_count,
            "codon_count": quotient_count * (2 ** len(support_size_type)),
        }
        for support_size_type, quotient_count in sorted(
            quotient_minimal_trigger_type_counts.items(),
            key=lambda item: (len(item[0]), item[0]),
        )
    ]
    quotient_minimal_trigger_energy_counts: collections.Counter[int] = collections.Counter()
    codon_minimal_trigger_energy_counts: collections.Counter[int] = collections.Counter()
    for row in minimal_trigger_type_rows:
        quotient_minimal_trigger_energy_counts[row["energy"]] += row["quotient_count"]
        codon_minimal_trigger_energy_counts[row["energy"]] += row["codon_count"]
    minimal_trigger_energy_rows = [
        {
            "energy": energy,
            "quotient_count": quotient_minimal_trigger_energy_counts[energy],
            "codon_count": codon_minimal_trigger_energy_counts[energy],
        }
        for energy in sorted(quotient_minimal_trigger_energy_counts)
    ]
    energy_minimal_trigger_rows = [
        {
            "trigger_size": trigger_size,
            "partition_type": partition_type,
            "quotient_count": quotient_count,
            "codon_count": quotient_count * (2 ** trigger_size),
        }
        for trigger_size, partition_type, quotient_count in (
            (1, "4", 1),
            (2, "1+3 or 2+2", 7),
            (3, "1+1+2", 6),
            (4, "1+1+1+1", 1),
        )
    ]
    trigger_energy_minimum = len(coordinate_universe)
    energy_minimal_quotient_total = sum(row["quotient_count"] for row in energy_minimal_trigger_rows)
    energy_minimal_codon_total = sum(row["codon_count"] for row in energy_minimal_trigger_rows)
    quotient_bivariate_minimal_trigger_terms = tuple(
        (row["trigger_size"], row["energy"], row["quotient_count"])
        for row in minimal_trigger_type_rows
    )
    codon_bivariate_minimal_trigger_terms = tuple(
        (row["trigger_size"], row["energy"], row["codon_count"])
        for row in minimal_trigger_type_rows
    )
    minimal_trigger_polynomial_quotient = tuple(
        (row["trigger_size"], row["quotient_count"])
        for row in minimal_trigger_rows
    )
    minimal_trigger_polynomial_codon = tuple(
        (row["trigger_size"], row["codon_count"])
        for row in minimal_trigger_rows
    )
    minimal_trigger_homology_core_rows = [
        {
            "trigger_size": row["trigger_size"],
            "homology_degree": row["trigger_size"] - 2,
            "sphere": f"S^{row['trigger_size'] - 2}",
            "quotient_count": row["quotient_count"],
            "codon_count": row["codon_count"],
        }
        for row in minimal_trigger_rows
    ]
    rank_enumerator_rows = [
        {
            "added_size": added_size,
            "rank_counts": {
                rank: (
                    1
                    if added_size == 0 and rank == 0
                    else (
                        trigger_rank_count(added_size, rank)
                        if added_size > 0 and rank > 0
                        else 0
                    )
                )
                for rank in range(5)
            },
        }
        for added_size in range(0, 5)
    ]
    rank_enumerator_rows = [
        {
            **row,
            "candidate_count": math.comb(len(y_external_codons), row["added_size"]),
            "counts_sum_to_candidate_count": sum(row["rank_counts"].values())
            == math.comb(len(y_external_codons), row["added_size"]),
        }
        for row in rank_enumerator_rows
    ]
    coverage_rank_singleton_witnesses = tuple(
        sorted(codon for codon in y_external_codons if len(anchor_support(codon)) == 4)
    )
    stanley_reisner_degree_rows = tuple(
        {
            "degree": row["trigger_size"],
            "minimal_generator_count": row["codon_count"],
        }
        for row in minimal_trigger_rows
    )
    stanley_reisner_degree_one_generators = tuple(
        sorted(codon for codon in y_external_codons if anchor_support(codon) == coordinate_universe)
    )

    def reliability_probability(activation_probability: float) -> float:
        omission_probability = 1.0 - activation_probability
        return (
            1.0
            - 4.0 * (omission_probability ** 16)
            + 6.0 * (omission_probability ** 24)
            - 4.0 * (omission_probability ** 28)
            + omission_probability ** 30
        )

    def reliability_threshold(target_probability: float) -> float:
        lower = 0.0
        upper = 1.0
        for _iteration in range(100):
            midpoint = (lower + upper) / 2.0
            if reliability_probability(midpoint) >= target_probability:
                upper = midpoint
            else:
                lower = midpoint
        return (lower + upper) / 2.0

    def energy_partition_factor(coordinate_count: int, activity: float, energy_factor: float) -> float:
        total = 1.0
        for support_size in range(1, coordinate_count + 1):
            total *= (1.0 + activity * (energy_factor ** support_size)) ** (
                2 * math.comb(coordinate_count, support_size)
            )
        return total

    def energy_biased_blocker_partition(activity: float, energy_factor: float) -> float:
        return (
            4.0 * energy_partition_factor(3, activity, energy_factor)
            - 6.0 * energy_partition_factor(2, activity, energy_factor)
            + 4.0 * energy_partition_factor(1, activity, energy_factor)
            - 1.0
        )

    def energy_biased_total_partition(activity: float, energy_factor: float) -> float:
        return energy_partition_factor(4, activity, energy_factor)

    def energy_biased_reliability(activity: float, energy_factor: float) -> float:
        return 1.0 - (
            energy_biased_blocker_partition(activity, energy_factor)
            / energy_biased_total_partition(activity, energy_factor)
        )

    def energy_partition_log_activity_derivative(coordinate_count: int, activity: float, energy_factor: float) -> float:
        return sum(
            2.0
            * math.comb(coordinate_count, support_size)
            * (
                (activity * (energy_factor ** support_size))
                / (1.0 + activity * (energy_factor ** support_size))
            )
            for support_size in range(1, coordinate_count + 1)
        )

    def energy_partition_log_energy_derivative(coordinate_count: int, activity: float, energy_factor: float) -> float:
        return sum(
            2.0
            * math.comb(coordinate_count, support_size)
            * support_size
            * (
                (activity * (energy_factor ** support_size))
                / (1.0 + activity * (energy_factor ** support_size))
            )
            for support_size in range(1, coordinate_count + 1)
        )

    def energy_biased_trigger_partition(activity: float, energy_factor: float) -> float:
        return (
            energy_biased_total_partition(activity, energy_factor)
            - energy_biased_blocker_partition(activity, energy_factor)
        )

    def energy_biased_trigger_activity_derivative(activity: float, energy_factor: float) -> float:
        total = energy_biased_total_partition(activity, energy_factor)
        blocker_derivative = (
            4.0
            * energy_partition_factor(3, activity, energy_factor)
            * energy_partition_log_activity_derivative(3, activity, energy_factor)
            - 6.0
            * energy_partition_factor(2, activity, energy_factor)
            * energy_partition_log_activity_derivative(2, activity, energy_factor)
            + 4.0
            * energy_partition_factor(1, activity, energy_factor)
            * energy_partition_log_activity_derivative(1, activity, energy_factor)
        )
        return (
            total * energy_partition_log_activity_derivative(4, activity, energy_factor)
            - blocker_derivative
        )

    def energy_biased_trigger_energy_derivative(activity: float, energy_factor: float) -> float:
        total = energy_biased_total_partition(activity, energy_factor)
        blocker_derivative = (
            4.0
            * energy_partition_factor(3, activity, energy_factor)
            * energy_partition_log_energy_derivative(3, activity, energy_factor)
            - 6.0
            * energy_partition_factor(2, activity, energy_factor)
            * energy_partition_log_energy_derivative(2, activity, energy_factor)
            + 4.0
            * energy_partition_factor(1, activity, energy_factor)
            * energy_partition_log_energy_derivative(1, activity, energy_factor)
        )
        return (
            total * energy_partition_log_energy_derivative(4, activity, energy_factor)
            - blocker_derivative
        )

    def conditional_trigger_expected_size(activity: float, energy_factor: float) -> float:
        return (
            energy_biased_trigger_activity_derivative(activity, energy_factor)
            / energy_biased_trigger_partition(activity, energy_factor)
        )

    def conditional_trigger_expected_energy(activity: float, energy_factor: float) -> float:
        return (
            energy_biased_trigger_energy_derivative(activity, energy_factor)
            / energy_biased_trigger_partition(activity, energy_factor)
        )

    def energy_biased_expected_selected(activity: float, energy_factor: float) -> float:
        return sum(
            2.0
            * math.comb(4, support_size)
            * (
                (activity * (energy_factor ** support_size))
                / (1.0 + activity * (energy_factor ** support_size))
            )
            for support_size in range(1, 5)
        )

    def energy_biased_activity_threshold(target_probability: float, energy_factor: float) -> float:
        lower = 0.0
        upper = 1.0
        while energy_biased_reliability(upper, energy_factor) < target_probability:
            upper *= 2.0
        for _iteration in range(100):
            midpoint = (lower + upper) / 2.0
            if energy_biased_reliability(midpoint, energy_factor) >= target_probability:
                upper = midpoint
            else:
                lower = midpoint
        return (lower + upper) / 2.0

    reliability_threshold_rows = []
    for target_probability in (0.5, 0.9, 0.95, 0.99):
        threshold = reliability_threshold(target_probability)
        reliability_threshold_rows.append(
            {
                "target_probability": target_probability,
                "activation_probability": threshold,
                "expected_selected_codons": len(y_external_codons) * threshold,
            }
        )
    energy_biased_threshold_rows = []
    for target_probability in (0.5, 0.9, 0.95):
        for energy_factor in (1.0, 0.75, 0.5, 0.25, 0.1):
            activity = energy_biased_activity_threshold(target_probability, energy_factor)
            energy_biased_threshold_rows.append(
                {
                    "target_probability": target_probability,
                    "energy_factor": energy_factor,
                    "activity": activity,
                    "expected_selected_codons": energy_biased_expected_selected(activity, energy_factor),
                    "reliability": energy_biased_reliability(activity, energy_factor),
                }
            )
    energy_biased_low_energy_terms = tuple(
        (row["trigger_size"], row["codon_count"])
        for row in energy_minimal_trigger_rows
    )
    conditional_trigger_rows = []
    for target_probability in (0.5, 0.9):
        for energy_factor in (1.0, 0.75, 0.5, 0.25, 0.1):
            activity = energy_biased_activity_threshold(target_probability, energy_factor)
            conditional_trigger_rows.append(
                {
                    "target_probability": target_probability,
                    "energy_factor": energy_factor,
                    "activity": activity,
                    "conditional_expected_size": conditional_trigger_expected_size(activity, energy_factor),
                    "conditional_expected_energy": conditional_trigger_expected_energy(activity, energy_factor),
                }
            )

    def low_energy_partition_distribution(activity: float) -> dict[int, float]:
        weights = {
            row["trigger_size"]: row["codon_count"] * (activity ** row["trigger_size"])
            for row in energy_minimal_trigger_rows
        }
        total = sum(weights.values())
        return {
            trigger_size: weight / total
            for trigger_size, weight in weights.items()
        }

    low_energy_partition_rows = []
    for activity in (0.1, 0.25, 0.5, 1.0, 2.0, 5.0, 10.0):
        distribution = low_energy_partition_distribution(activity)
        low_energy_partition_rows.append(
            {
                "activity": activity,
                "size_probabilities": distribution,
                "expected_size": sum(
                    trigger_size * probability
                    for trigger_size, probability in distribution.items()
                ),
            }
        )
    low_energy_partition_crossover_rows = [
        {"left_size": 1, "right_size": 2, "activity": 1.0 / 14.0},
        {"left_size": 2, "right_size": 3, "activity": 7.0 / 12.0},
        {"left_size": 3, "right_size": 4, "activity": 3.0},
    ]

    def stirling_second_kind(total: int, blocks: int) -> int:
        if total == 0 and blocks == 0:
            return 1
        if total == 0 or blocks == 0:
            return 0
        table = [[0 for _block in range(blocks + 1)] for _item in range(total + 1)]
        table[0][0] = 1
        for item in range(1, total + 1):
            for block in range(1, blocks + 1):
                table[item][block] = table[item - 1][block - 1] + block * table[item - 1][block]
        return table[total][blocks]

    def universal_coverage_trigger_summary(coordinate_count: int, lift_count: int) -> dict[str, object]:
        external_size = lift_count * ((2 ** coordinate_count) - 1)
        closure_size_by_rank = [
            {
                "rank": rank,
                "external_closure_size": lift_count * ((2 ** rank) - 1),
            }
            for rank in range(coordinate_count + 1)
        ]
        maximal_blocker_size = lift_count * ((2 ** (coordinate_count - 1)) - 1)
        blocker_intersection_formula_rows = [
            {
                "missing_coordinate_count": missing_count,
                "intersection_size": lift_count * ((2 ** (coordinate_count - missing_count)) - 1),
            }
            for missing_count in range(1, coordinate_count + 1)
        ]
        blocker_count_rows = [
            {
                "added_size": added_size,
                "blocker_count": sum(
                    ((-1) ** (missing_count + 1))
                    * math.comb(coordinate_count, missing_count)
                    * math.comb(lift_count * ((2 ** (coordinate_count - missing_count)) - 1), added_size)
                    for missing_count in range(1, coordinate_count + 1)
                ),
            }
            for added_size in range(1, min(maximal_blocker_size, 10) + 1)
        ]
        reliability_term_rows = [
            {
                "missing_coordinate_count": missing_count,
                "coefficient": ((-1) ** (missing_count + 1)) * math.comb(coordinate_count, missing_count),
                "exponent": lift_count * ((2 ** coordinate_count) - (2 ** (coordinate_count - missing_count))),
            }
            for missing_count in range(1, coordinate_count + 1)
        ]
        markov_transition_rows = [
            {
                "rank_increase": increase,
                "numerator_factor": lift_count * (2 ** 0) * math.comb(coordinate_count, increase),
            }
            for increase in range(1, coordinate_count + 1)
        ]
        alexander_dual_shift_rows = [
            {
                "subset_size": subset_size,
                "multiplicity": math.comb(coordinate_count, subset_size),
                "shift": lift_count * ((2 ** coordinate_count) - (2 ** (coordinate_count - subset_size))),
            }
            for subset_size in range(1, coordinate_count + 1)
        ]
        energy_minimal_rows = [
            {
                "trigger_size": trigger_size,
                "stirling_count": stirling_second_kind(coordinate_count, trigger_size),
                "lifted_count": (lift_count ** trigger_size) * stirling_second_kind(coordinate_count, trigger_size),
            }
            for trigger_size in range(1, coordinate_count + 1)
        ]
        stanley_reisner_dimension_formula = maximal_blocker_size
        homological_core_dimension = coordinate_count - 2
        depth_formula = coordinate_count - 1
        regularity_formula = coordinate_count - 1
        projective_dimension_formula = external_size - depth_formula
        cohen_macaulay_defect_formula = stanley_reisner_dimension_formula - depth_formula
        local_link_formula_rows = [
            {
                "support_rank": rank,
                "saturated_face_size": lift_count * ((2 ** rank) - 1),
                "link_coordinate_count": coordinate_count - rank,
                "link_lift_count": lift_count * (2 ** rank),
                "link_sphere_dimension": coordinate_count - rank - 2,
            }
            for rank in range(coordinate_count)
        ]
        top_betti_generating_function = (
            f"((1+x)^{lift_count}-1)^{coordinate_count}"
            f"(1+x)^{lift_count * ((2 ** coordinate_count) - 1 - coordinate_count)}"
        )
        return {
            "coordinate_count": coordinate_count,
            "lift_count": lift_count,
            "external_size": external_size,
            "closure_lattice_size": 2 ** coordinate_count,
            "closure_size_by_rank": closure_size_by_rank,
            "blocker_homotopy_sphere_dimension": coordinate_count - 2,
            "maximal_blocker_size": maximal_blocker_size,
            "forced_trigger_threshold": maximal_blocker_size + 1,
            "blocker_intersection_formula_rows": blocker_intersection_formula_rows,
            "blocker_count_rows": blocker_count_rows,
            "reliability_term_rows": reliability_term_rows,
            "markov_drift_numerator_factor": lift_count * (2 ** (coordinate_count - 1)),
            "markov_initial_transition_rows": markov_transition_rows,
            "alexander_dual_generator_count": coordinate_count,
            "alexander_dual_shift_rows": alexander_dual_shift_rows,
            "stanley_reisner_dimension_formula": stanley_reisner_dimension_formula,
            "homological_core_dimension": homological_core_dimension,
            "depth_formula": depth_formula,
            "regularity_formula": regularity_formula,
            "projective_dimension_formula": projective_dimension_formula,
            "cohen_macaulay_defect_formula": cohen_macaulay_defect_formula,
            "hochster_full_vertex_witness": {
                "betti_i": projective_dimension_formula,
                "betti_j": external_size,
                "homology_degree": homological_core_dimension,
                "betti_value": 1,
            },
            "local_link_formula_rows": local_link_formula_rows,
            "top_betti_strand_formula": top_betti_generating_function,
            "top_betti_singleton_support_count": coordinate_count,
            "top_betti_free_element_count": lift_count * ((2 ** coordinate_count) - 1 - coordinate_count),
            "energy_minimum": coordinate_count,
            "energy_minimal_rows": energy_minimal_rows,
            "energy_minimal_total": sum(row["lifted_count"] for row in energy_minimal_rows),
        }

    universal_trigger_summary = universal_coverage_trigger_summary(4, 2)
    antipodal_trigger_summary = {
        "mstar": tuple(sorted(mstar_set)),
        "mstar_size": len(mstar_set),
        "mstar_is_median_closed": mstar_closure == mstar_set,
        "mstar_closure_stage_count": len(mstar_closure_stages),
        "mstar_structure": ("NNR", "CUY"),
        "y_shell_rows": [
            {
                "shell": f"H{index}",
                "size": len(y_shells[index]),
                "codons": tuple(sorted(y_shells[index])),
            }
            for index in range(5)
        ],
        "shell_trigger_rows": shell_trigger_rows,
        "single_antipode_rows": single_antipode_rows,
        "single_trigger_rows": single_trigger_rows,
        "shell_filling_rows": shell_filling_rows,
        "mstar_spectral_radius": shell_filling_rows[0]["spectral_radius"],
        "mstar_retention_float": shell_filling_rows[0]["retention_float"],
        "full_cube_spectral_radius": shell_filling_rows[-1]["spectral_radius"],
        "full_cube_retention_float": shell_filling_rows[-1]["retention_float"],
        "anchor_subcube_formula_verified": all(row["matches_formula"] for row in support_pattern_verification_rows),
        "span_size_rows": span_size_rows,
        "single_span_rows": single_span_rows,
        "trigger_count_rows": trigger_count_rows,
        "support_pattern_verification_rows": support_pattern_verification_rows,
        "coverage_closure_rows": coverage_closure_rows,
        "coverage_closure_formula_verified": coverage_closure_formula_verified,
        "coverage_closure_lattice_verified": coverage_closure_lattice_verified,
        "coverage_rank_coordinates": BIT_COORDINATES[:4],
        "coverage_rank_is_submodular_formula": "r(B)=sum_i 1[i in J(B)]",
        "coverage_rank_singleton_witnesses": coverage_rank_singleton_witnesses,
        "full_trigger_condition_coordinates": BIT_COORDINATES[:4],
        "agy_support": tuple(sorted(BIT_COORDINATES[index] for index in anchor_support("AGT"))),
        "boolean_lattice_closure_count": len(support_patterns),
        "boolean_lattice_intersection_verified": boolean_lattice_intersection_verified,
        "boolean_lattice_median_join_verified": boolean_lattice_median_join_verified,
        "boolean_lattice_rank_rows": boolean_lattice_rank_rows,
        "quotient_spectrum_rows": quotient_spectrum_rows,
        "rank_distribution_rows": rank_distribution_rows,
        "trigger_count_formula_matches_enumeration": trigger_count_formula_matches_enumeration,
        "random_trigger_probability_rows": random_trigger_probability_rows,
        "trigger_time_rows": trigger_time_rows,
        "expected_trigger_time": expected_trigger_time,
        "trigger_quantile_rows": trigger_quantile_rows,
        "expected_rank_rows": expected_rank_rows,
        "expected_closure_rows": expected_closure_rows,
        "expected_spectral_rows": expected_spectral_rows,
        "markov_transition_state_rows": markov_transition_state_rows,
        "markov_remaining_time_rows": markov_remaining_time_rows,
        "markov_expected_trigger_time": markov_remaining_mean(0, 0),
        "trigger_time_variance": trigger_time_variance,
        "trigger_time_standard_deviation": trigger_time_variance ** 0.5,
        "blocker_vertex_count": sum(1 for codon in y_external_codons if len(anchor_support(codon)) < 4),
        "blocker_coordinate_rows": blocker_coordinate_rows,
        "blocker_intersection_rows": blocker_intersection_rows,
        "blocker_nerve": blocker_nerve,
        "blocker_dimension": blocker_dimension,
        "stanley_reisner_dimension": stanley_reisner_dimension,
        "thickened_sphere_rows": thickened_sphere_rows,
        "blocker_f_vector": blocker_f_vector,
        "blocker_independence_polynomial": "4(1+t)^14 - 6(1+t)^6 + 4(1+t)^2 - 1",
        "blocker_independence_coefficients": blocker_independence_coefficients,
        "blocker_hilbert_series": blocker_hilbert_series,
        "blocker_h_polynomial": blocker_h_polynomial,
        "blocker_h_vector": blocker_h_vector,
        "blocker_is_cohen_macaulay": blocker_is_cohen_macaulay,
        "blocker_non_cm_witness": blocker_non_cm_witness,
        "blocker_projective_dimension": blocker_projective_dimension,
        "blocker_depth": blocker_depth,
        "blocker_regularity": blocker_regularity,
        "blocker_cohen_macaulay_defect": blocker_cohen_macaulay_defect,
        "blocker_hochster_witness": blocker_hochster_witness,
        "local_link_stratification_rows": local_link_stratification_rows,
        "local_link_examples": local_link_examples,
        "local_link_non_saturated_links_are_cones": local_link_non_saturated_links_are_cones,
        "blocker_is_buchsbaum": blocker_is_buchsbaum,
        "blocker_buchsbaum_obstruction": blocker_buchsbaum_obstruction,
        "hochster_nerve_vertex_count": hochster_nerve_vertex_count,
        "hochster_possible_homology_degrees": hochster_possible_homology_degrees,
        "hochster_betti_diagonals": hochster_betti_diagonals,
        "top_betti_strand_generating_function": top_betti_strand_generating_function,
        "top_betti_strand_rows": top_betti_strand_rows,
        "betti_table_diagonal_rows": betti_table_diagonal_rows,
        "hochster_diagonal_rows": hochster_diagonal_rows,
        "hochster_diagonal_generating_functions": hochster_diagonal_generating_functions,
        "support_level_betti_rows": support_level_betti_rows,
        "support_level_betti_generating_functions": support_level_betti_generating_functions,
        "support_lift_substitution": support_lift_substitution,
        "support_nerve_signature_rows": support_nerve_signature_rows,
        "support_nerve_census_total": support_nerve_census_total,
        "support_nerve_contractible_count": support_nerve_contractible_count,
        "support_nerve_h2_count": support_nerve_h2_count,
        "support_to_nerve_subcomplex_signature_rows": support_to_nerve_subcomplex_signature_rows,
        "support_to_nerve_subcomplex_total": support_to_nerve_subcomplex_total,
        "support_to_nerve_fiber_total": support_to_nerve_fiber_total,
        "support_to_nerve_h2_subcomplex_count": support_to_nerve_h2_subcomplex_count,
        "hochster_p0_coefficients_desc": hochster_p0_coefficients_desc,
        "hochster_p1_coefficients_desc": hochster_p1_coefficients_desc,
        "blocker_euler_characteristic": blocker_euler_characteristic,
        "blocker_probability_tail_rows": blocker_probability_tail_rows,
        "alexander_dual_generator_count": len(alexander_dual_generator_rows),
        "alexander_dual_generator_rows": alexander_dual_generator_rows,
        "alexander_dual_lcm_rows": alexander_dual_lcm_rows,
        "alexander_dual_betti_pattern": alexander_dual_betti_pattern,
        "alexander_dual_resolution_rows": alexander_dual_resolution_rows,
        "alexander_dual_resolution_string": "0 -> R0(-30) -> R0(-28)^4 -> R0(-24)^6 -> R0(-16)^4 -> J -> 0",
        "alexander_dual_reliability_terms": alexander_dual_reliability_terms,
        "alexander_dual_reliability_polynomial": "4q^16 - 6q^24 + 4q^28 - q^30",
        "minimal_trigger_rows": minimal_trigger_rows,
        "minimal_trigger_quotient_total": sum(row["quotient_count"] for row in minimal_trigger_rows),
        "minimal_trigger_codon_total": sum(row["codon_count"] for row in minimal_trigger_rows),
        "minimal_trigger_polynomial_quotient": minimal_trigger_polynomial_quotient,
        "minimal_trigger_polynomial_codon": minimal_trigger_polynomial_codon,
        "minimal_trigger_homology_core_rows": minimal_trigger_homology_core_rows,
        "minimal_trigger_type_rows": minimal_trigger_type_rows,
        "trigger_energy_minimum": trigger_energy_minimum,
        "trigger_energy_minimum_condition": "support partition of Omega",
        "energy_minimal_trigger_rows": energy_minimal_trigger_rows,
        "energy_minimal_quotient_total": energy_minimal_quotient_total,
        "energy_minimal_codon_total": energy_minimal_codon_total,
        "minimal_trigger_energy_rows": minimal_trigger_energy_rows,
        "quotient_bivariate_minimal_trigger_terms": quotient_bivariate_minimal_trigger_terms,
        "codon_bivariate_minimal_trigger_terms": codon_bivariate_minimal_trigger_terms,
        "quotient_bivariate_minimal_trigger_polynomial": "z y^4 + z^2(7y^4+12y^5+6y^6) + z^3(6y^4+12y^5+4y^6) + z^4 y^4",
        "codon_bivariate_minimal_trigger_polynomial": "2z y^4 + z^2(28y^4+48y^5+24y^6) + z^3(48y^4+96y^5+32y^6) + 16z^4 y^4",
        "rank_enumerator_formula": "sum_d binom(4,d) u^d sum_k (-1)^(d-k) binom(d,k) (1+t)^(2(2^k-1))",
        "rank_enumerator_rows": rank_enumerator_rows,
        "stanley_reisner_generator_count": sum(row["codon_count"] for row in minimal_trigger_rows),
        "stanley_reisner_degree_rows": stanley_reisner_degree_rows,
        "stanley_reisner_degree_one_generators": stanley_reisner_degree_one_generators,
        "reliability_polynomial": "1 - 4q^16 + 6q^24 - 4q^28 + q^30",
        "reliability_threshold_rows": reliability_threshold_rows,
        "energy_biased_total_partition": "(1+ty)^8 (1+ty^2)^12 (1+ty^3)^8 (1+ty^4)^2",
        "energy_biased_blocker_partition": "4A3(t,y) - 6A2(t,y) + 4A1(t,y) - 1",
        "energy_biased_reliability_formula": "1 - (4A3(t,y)-6A2(t,y)+4A1(t,y)-1)/A4(t,y)",
        "energy_biased_low_energy_terms": energy_biased_low_energy_terms,
        "energy_biased_low_energy_polynomial": "y^4(2t+28t^2+48t^3+16t^4)",
        "energy_biased_threshold_rows": energy_biased_threshold_rows,
        "conditional_trigger_size_formula": "t d_t log Z_trig(t,y)",
        "conditional_trigger_energy_formula": "y d_y log Z_trig(t,y)",
        "conditional_trigger_rows": conditional_trigger_rows,
        "low_energy_partition_distribution_formula": "a_m t^m / (2t+28t^2+48t^3+16t^4)",
        "low_energy_partition_rows": low_energy_partition_rows,
        "low_energy_partition_crossover_rows": low_energy_partition_crossover_rows,
        "universal_coverage_trigger": universal_trigger_summary,
        "maximum_nontrigger_external_size": maximum_nontrigger_external_size,
        "maximum_nontrigger_blocker_count": maximum_nontrigger_blocker_count,
        "forced_full_trigger_threshold": maximum_nontrigger_external_size + 1,
    }

    def spectral_expansion_search(
        base: set[str],
        added_size: int,
        top_count: int = 5,
    ) -> dict[str, object]:
        base_radius = spectral_radius_for_set(base)
        rows: list[dict[str, object]] = []
        for added in itertools.combinations(sorted(set(all_codons()) - base), added_size):
            expanded = base | set(added)
            radius = spectral_radius_for_set(expanded)
            rows.append(
                {
                    "added": added,
                    "spectral_radius": radius,
                    "gain": radius - base_radius,
                    "base_neighbor_count": sum(neighbor_count_in_set(codon, base) for codon in added),
                }
            )
        rows.sort(key=lambda row: (-row["spectral_radius"], row["added"]))
        best_radius = rows[0]["spectral_radius"]
        best_rows = [
            row for row in rows if abs(row["spectral_radius"] - best_radius) < 1e-12
        ]
        return {
            "base_spectral_radius": base_radius,
            "candidate_count": len(rows),
            "best_count": len(best_rows),
            "best_added": best_rows[0]["added"],
            "best_rows": best_rows,
            "best_spectral_radius": best_radius,
            "best_gain": best_rows[0]["gain"],
            "top_rows": rows[:top_count],
        }

    anchor_triple_spectral_search = spectral_expansion_search(support, 3)
    support_pair_spectral_search = spectral_expansion_search(support, 2)
    first_median_triple_spectral_search = spectral_expansion_search(anchor_closure, 3)
    anchor_single_spectral_search = spectral_expansion_search(anchor_closure, 1)
    anchor_pair_spectral_search = spectral_expansion_search(anchor_closure, 2)
    acg_single_spectral_search = spectral_expansion_search(median_stage_one, 1)
    support_single_spectral_search = spectral_expansion_search(support, 1)
    support_quad_best_sets = (
        ("AAG", "ACA", "ATG", "TTG"),
        ("ACA", "TCG", "TGG", "TTG"),
    )
    support_quad_best_rows = [
        {
            "added": added,
            "spectral_radius": spectral_radius_for_set(support | set(added)),
            "gain": spectral_radius_for_set(support | set(added)) - spectral_radius_for_set(support),
            "base_neighbor_count": sum(neighbor_count_in_set(codon, support) for codon in added),
        }
        for added in support_quad_best_sets
    ]
    support_quad_best_radius = support_quad_best_rows[0]["spectral_radius"]
    assert all(abs(row["spectral_radius"] - support_quad_best_radius) < 1e-12 for row in support_quad_best_rows)
    assert tuple(sorted(apply_cube_automorphism(codon, *tau) for codon in support_quad_best_sets[0])) == support_quad_best_sets[1]
    tau_invariant_frontier_rows = [
        {"budget": 1, "best_added": ("ACA",)},
        {"budget": 2, "best_added": ("ACA", "TTG")},
        {"budget": 3, "best_added": ("AAG", "ACA", "TGG")},
        {"budget": 4, "best_added": ("AAG", "ACA", "TGG", "TTG")},
        {"budget": 5, "best_added": ("AAG", "ATG", "TCG", "TGG", "TTG")},
        {"budget": 6, "best_added": ("AAG", "ACA", "ATG", "TCG", "TGG", "TTG")},
        {"budget": 6, "best_added": ("AAG", "ACG", "ATG", "TCG", "TGG", "TTG")},
        {"budget": 7, "best_added": ("AAG", "ACA", "ACG", "ATG", "TCG", "TGG", "TTG")},
    ]
    for row in tau_invariant_frontier_rows:
        assert all(apply_cube_automorphism(codon, *tau) in row["best_added"] for codon in row["best_added"])
    greedy_spectral_chain_rows = [
        {
            "set": "support",
            "added": (),
            "vertices": len(support),
            "spectral_radius": anchor_triple_spectral_search["base_spectral_radius"],
        },
        {
            "set": "anchor_closure",
            "added": anchor_triple_spectral_search["best_added"],
            "vertices": len(anchor_closure),
            "spectral_radius": anchor_triple_spectral_search["best_spectral_radius"],
        },
        {
            "set": "median_stage_one",
            "added": first_median_triple_spectral_search["best_added"],
            "vertices": len(median_stage_one),
            "spectral_radius": first_median_triple_spectral_search["best_spectral_radius"],
        },
        {
            "set": "median_closure",
            "added": acg_single_spectral_search["best_added"],
            "vertices": len(median_set),
            "spectral_radius": acg_single_spectral_search["best_spectral_radius"],
        },
    ]

    def flip_bit(codon: str, direction: int) -> str:
        word = list(bits(codon))
        word[direction] = "1" if word[direction] == "0" else "0"
        return codon_from_bits("".join(word))

    def directional_saturation(codons: set[str], direction: int) -> set[str]:
        return codons | {flip_bit(codon, direction) for codon in codons}

    def directional_boundary_counts(codons: set[str]) -> tuple[int, ...]:
        return tuple(
            sum(1 for codon in codons if flip_bit(codon, direction) not in codons)
            for direction in range(6)
        )

    directional_saturation_rows = []
    for direction, name in enumerate(BIT_COORDINATES):
        saturated = directional_saturation(support, direction)
        added = saturated - support
        leaks = added - median_set
        directional_saturation_rows.append(
            {
                "direction": name,
                "direction_index": direction,
                "added_count": len(added),
                "added": tuple(sorted(added)),
                "leaks_outside_median": tuple(sorted(leaks)),
                "contained_in_median": saturated <= median_set,
            }
        )

    f3_index = BIT_COORDINATES.index("f3")
    f3_saturation = directional_saturation(support, f3_index)
    f3_completion_points = tuple(
        sorted(
            codon
            for codon in set(all_codons()) - support
            if directional_saturation(support | {codon}, f3_index) == median_set
        )
    )
    direction_boundary_sets = (
        ("support", support),
        ("anchor_closure", anchor_closure),
        ("median_stage_one", median_stage_one),
        ("median_closure", median_set),
    )
    direction_boundary_rows = [
        {
            "set": name,
            "counts": dict(zip(BIT_COORDINATES, directional_boundary_counts(codons))),
            "total": sum(directional_boundary_counts(codons)),
        }
        for name, codons in direction_boundary_sets
    ]
    stage_one_f3_boundary_edges = tuple(
        sorted(
            tuple(sorted((codon, flip_bit(codon, f3_index))))
            for codon in median_stage_one
            if flip_bit(codon, f3_index) not in median_stage_one
        )
    )

    def median_boolean_formula(codon: str) -> bool:
        word = bits(codon)
        s1, f1, s2, f2, s3, _f3 = (int(bit) for bit in word)
        return (f1 == 0 and s3 == 1) or (
            f1 == 1 and s1 == 0 and s2 == 0 and f2 == 0
        )

    median_boolean_formula_vertices = {
        codon for codon in all_codons() if median_boolean_formula(codon)
    }

    inverse_base_bits = {value: key for key, value in BASE_BITS.items()}

    def rna_label(text: str) -> str:
        return text.replace("T", "U")

    def project_without_f3(codon: str) -> str:
        word = bits(codon)
        return word[:5]

    def quotient_label(word: str) -> str:
        first = inverse_base_bits[word[0:2]]
        second = inverse_base_bits[word[2:4]]
        third = "R" if word[4] == "1" else "Y"
        return rna_label(first + second + third)

    def quotient_pair(word: str) -> tuple[str, ...]:
        return tuple(
            rna_label(codon)
            for codon in sorted(
                codon_from_bits(word + family_bit)
                for family_bit in "01"
            )
        )

    def median_word(left: str, middle: str, right: str) -> str:
        return "".join(
            "1" if (int(a) + int(b) + int(c)) >= 2 else "0"
            for a, b, c in zip(left, middle, right)
        )

    def median_closure_words(words: set[str]) -> tuple[set[str], list[dict[str, object]]]:
        closed = set(words)
        stages: list[dict[str, object]] = []
        stage_index = 0
        while True:
            additions = {
                median_word(left, middle, right)
                for left, middle, right in itertools.combinations_with_replacement(sorted(closed), 3)
            } - closed
            if not additions:
                break
            stage_index += 1
            closed |= additions
            stages.append(
                {
                    "stage": stage_index,
                    "added_count": len(additions),
                    "added": tuple(quotient_label(word) for word in sorted(additions)),
                    "total_size": len(closed),
                }
            )
        return closed, stages

    def q5_subcube_vertices(free_bits: tuple[int, ...], fixed_values: tuple[str, ...]) -> tuple[str, ...]:
        fixed = [index for index in range(5) if index not in free_bits]
        word = [""] * 5
        for index, value in zip(fixed, fixed_values):
            word[index] = value
        vertices: list[str] = []
        for local in itertools.product("01", repeat=len(free_bits)):
            candidate = word.copy()
            for index, value in zip(free_bits, local):
                candidate[index] = value
            vertices.append("".join(candidate))
        return tuple(vertices)

    def q5_cubical_complex(vertices: set[str]) -> dict[str, object]:
        cells_by_dimension: dict[int, list[dict[str, object]]] = {dimension: [] for dimension in range(6)}
        for dimension in range(6):
            for free in itertools.combinations(range(5), dimension):
                for values in itertools.product("01", repeat=5 - dimension):
                    cell_vertices = q5_subcube_vertices(free, values)
                    if set(cell_vertices) <= vertices:
                        cells_by_dimension[dimension].append(
                            {
                                "free_bits": free,
                                "vertices": cell_vertices,
                                "labels": tuple(quotient_label(word) for word in cell_vertices),
                            }
                        )
        all_cells = [
            cell
            for cells in cells_by_dimension.values()
            for cell in cells
        ]
        maximal_cells = [
            cell
            for cell in all_cells
            if not any(set(cell["vertices"]) < set(other["vertices"]) for other in all_cells)
        ]
        maximal_cells.sort(key=lambda cell: (-len(cell["free_bits"]), cell["labels"]))
        return {
            "f_vector": tuple(len(cells_by_dimension[dimension]) for dimension in range(6)),
            "maximal_cells": maximal_cells,
        }

    def q5_edges(vertices: set[str]) -> tuple[tuple[str, str], ...]:
        return tuple(
            (left, right)
            for left, right in itertools.combinations(sorted(vertices), 2)
            if sum(a != b for a, b in zip(left, right)) == 1
        )

    quotient_support = {project_without_f3(codon) for codon in support}
    quotient_median = {project_without_f3(codon) for codon in median_set}
    quotient_median_from_support, quotient_median_stages = median_closure_words(quotient_support)
    quotient_complex = q5_cubical_complex(quotient_median)
    quotient_support_complex = q5_cubical_complex(quotient_support)
    quotient_edges = q5_edges(quotient_median)
    quotient_adjacency_matrix = [[0.0 for _column in quotient_median] for _row in quotient_median]
    quotient_ordered_words = tuple(sorted(quotient_median))
    quotient_word_index = {word: index for index, word in enumerate(quotient_ordered_words)}
    for left, right in quotient_edges:
        left_index = quotient_word_index[left]
        right_index = quotient_word_index[right]
        quotient_adjacency_matrix[left_index][right_index] = 1.0
        quotient_adjacency_matrix[right_index][left_index] = 1.0
    quotient_mu_max, _quotient_eigenvector = dominant_symmetric_eigenpair(quotient_adjacency_matrix)
    quotient_product_spectral_radius = (quotient_mu_max + 1.0) / 6.0
    quotient_product_f_vector = tuple(
        2 * quotient_complex["f_vector"][index]
        + (quotient_complex["f_vector"][index - 1] if index > 0 else 0)
        for index in range(5)
    )
    quotient_label_order = ("UUR", "UCR", "UAR", "UGR", "AUR", "ACR", "AAR", "AGR", "CUR", "CUY")
    quotient_label_to_word = {
        quotient_label(word): word
        for word in quotient_median
    }
    quotient_occupancy_rows = [
        {
            "quotient": label,
            "pair": quotient_pair(quotient_label_to_word[label]),
            "active_occupancy": sum(
                1
                for codon in all_codons()
                if project_without_f3(codon) == quotient_label_to_word[label]
                and codon in support
            ),
        }
        for label in quotient_label_order
    ]
    quotient_preimage = {
        codon for codon in all_codons() if project_without_f3(codon) in quotient_median
    }
    radial_state_order = ("X3", "X2", "X1", "X0", "YR", "YY")
    radial_state_names = {
        "X3": "AGR",
        "X2": "Anchor6",
        "X1": "StopStart6",
        "X0": "UUR",
        "YR": "CUR",
        "YY": "CUY",
    }
    radial_state_codons = {
        "X3": ("AGR",),
        "X2": ("AAR", "ACR", "UGR"),
        "X1": ("AUR", "UAR", "UCR"),
        "X0": ("UUR",),
        "YR": ("CUR",),
        "YY": ("CUY",),
    }
    radial_matrix = (
        (0, 3, 0, 0, 0, 0),
        (1, 0, 2, 0, 0, 0),
        (0, 2, 0, 1, 0, 0),
        (0, 0, 3, 0, 1, 0),
        (0, 0, 0, 1, 0, 1),
        (0, 0, 0, 0, 1, 0),
    )

    def polynomial_add(left: list[int], right: list[int]) -> list[int]:
        size = max(len(left), len(right))
        result = [0 for _index in range(size)]
        for index, value in enumerate(left):
            result[index] += value
        for index, value in enumerate(right):
            result[index] += value
        while len(result) > 1 and result[-1] == 0:
            result.pop()
        return result

    def polynomial_mul(left: list[int], right: list[int]) -> list[int]:
        result = [0 for _index in range(len(left) + len(right) - 1)]
        for left_index, left_value in enumerate(left):
            for right_index, right_value in enumerate(right):
                result[left_index + right_index] += left_value * right_value
        while len(result) > 1 and result[-1] == 0:
            result.pop()
        return result

    def polynomial_det(matrix: list[list[list[int]]]) -> list[int]:
        size = len(matrix)
        if size == 1:
            return matrix[0][0]
        total = [0]
        for column in range(size):
            minor = [
                [matrix[row][minor_column] for minor_column in range(size) if minor_column != column]
                for row in range(1, size)
            ]
            term = polynomial_mul(matrix[0][column], polynomial_det(minor))
            if column % 2:
                term = [-coefficient for coefficient in term]
            total = polynomial_add(total, term)
        return total

    radial_characteristic_matrix = [
        [
            ([-radial_matrix[row][column], 1] if row == column else [-radial_matrix[row][column]])
            for column in range(len(radial_matrix))
        ]
        for row in range(len(radial_matrix))
    ]
    radial_characteristic_polynomial = tuple(polynomial_det(radial_characteristic_matrix))
    radial_matrix_float = [[float(value) for value in row] for row in radial_matrix]
    radial_mu_max, radial_vector = dominant_symmetric_eigenpair(radial_matrix_float)
    radial_max = max(radial_vector)
    radial_survival_rows = [
        {
            "state": state,
            "name": radial_state_names[state],
            "potential": radial_vector[index] / radial_max,
        }
        for index, state in enumerate(radial_state_order)
    ]
    radial_lift_sizes = tuple(2 * len(radial_state_codons[state]) for state in radial_state_order)
    radial_mass_denominator = sum(
        size * radial_vector[index]
        for index, size in enumerate(radial_lift_sizes)
    )
    radial_qsd_rows = [
        {
            "state": state,
            "name": radial_state_names[state],
            "orbit_size": radial_lift_sizes[index],
            "mass": radial_lift_sizes[index] * radial_vector[index] / radial_mass_denominator,
        }
        for index, state in enumerate(radial_state_order)
    ]
    radial_cubic_coefficients = (-9, 26, -12, 1)
    radial_r_max = radial_mu_max * radial_mu_max
    radial_product_lambda = (radial_mu_max + 1.0) / 6.0
    core_codon_set = set(expand_iupac_motif("WNR"))
    core_retention = retention_row("wnr_core", core_codon_set)
    core_spectral_radius = 4.0 / 6.0
    median_retention = next(row for row in closure_retention_rows if row["name"] == "median_closure")

    def tail_path_matrix(length: int) -> list[list[float]]:
        size = 4 + length
        matrix = [[0.0 for _column in range(size)] for _row in range(size)]
        for index in range(4):
            if index:
                matrix[index][index - 1] = float(index)
            if index < 3:
                matrix[index][index + 1] = float(3 - index)
        if length:
            matrix[0][4] = 1.0
            matrix[4][0] = 1.0
            for tail_index in range(4, size - 1):
                matrix[tail_index][tail_index + 1] = 1.0
                matrix[tail_index + 1][tail_index] = 1.0
        return matrix

    tail_length_rows = []
    for length in range(6):
        tail_mu, _tail_vector = dominant_symmetric_eigenpair(tail_path_matrix(length))
        tail_length_rows.append(
            {
                "tail_length": length,
                "mu_max": tail_mu,
                "lambda_with_wobble": (tail_mu + 1.0) / 6.0,
            }
        )
    tail_limit_mu = tail_length_rows[-1]["mu_max"]
    tail_gain_capture = (
        (radial_mu_max - 3.0)
        / (tail_limit_mu - 3.0)
    )
    tail_qsd_mass = sum(
        row["mass"]
        for row in radial_qsd_rows
        if row["state"] in {"YR", "YY"}
    )
    spectral_antenna_summary = {
        "core": {
            "vertices": len(core_codon_set),
            "internal_edges": core_retention["internal_edges"],
            "retention": core_retention["retention"],
            "retention_float": core_retention["retention_float"],
            "spectral_radius": core_spectral_radius,
        },
        "median": {
            "vertices": len(median_set),
            "internal_edges": median_retention["internal_edges"],
            "retention": median_retention["retention"],
            "retention_float": median_retention["retention_float"],
            "spectral_radius": median_spectral_radius,
        },
        "retention_drops": median_retention["retention_float"] < core_retention["retention_float"],
        "spectral_radius_rises": median_spectral_radius > core_spectral_radius,
        "tail_self_energy_formula": "mu/(mu^2-1)",
        "tail_self_energy_at_mu_max": radial_mu_max / (radial_mu_max * radial_mu_max - 1.0),
        "tail_length_rows": tail_length_rows,
        "tail_gain_capture_against_length_5": tail_gain_capture,
        "tail_qsd_mass": tail_qsd_mass,
        "spectral_gain_over_core": radial_product_lambda - core_spectral_radius,
    }
    median_edge_set = {tuple(sorted((left, right))) for left, right in median_edges}
    state_by_codon = {
        codon: state
        for state, codons in quotient_state_sets.items()
        for codon in codons
    }
    state_position = {state: index for index, state in enumerate(path_order)}

    def loss_row(name: str, radius: float, **extra: object) -> dict[str, object]:
        return {
            "name": name,
            **extra,
            "spectral_radius": radius,
            "loss": median_spectral_radius - radius,
        }

    single_codon_ablation_rows = []
    for codon in sorted(median_set):
        reduced = median_set - {codon}
        radius = spectral_radius_for_set(reduced)
        single_codon_ablation_rows.append(
            loss_row(
                codon,
                radius,
                state=state_by_codon[codon],
            )
        )
    single_codon_ablation_rows.sort(key=lambda row: (-row["loss"], row["name"]))
    single_codon_orbit_rows = []
    for state in path_order:
        rows = [row for row in single_codon_ablation_rows if row["state"] == state]
        single_codon_orbit_rows.append(
            {
                "state": state,
                "codons": tuple(sorted(row["name"] for row in rows)),
                "spectral_radius": rows[0]["spectral_radius"],
                "loss": rows[0]["loss"],
            }
        )
    single_codon_orbit_rows.sort(key=lambda row: (-row["loss"], row["state"]))

    module_ablation_rows = []
    for state in path_order:
        reduced = median_set - quotient_state_sets[state]
        radius = spectral_radius_for_set(reduced)
        module_ablation_rows.append(
            loss_row(
                state,
                radius,
                size=len(quotient_state_sets[state]),
                codons=tuple(sorted(quotient_state_sets[state])),
            )
        )
    module_ablation_rows.sort(key=lambda row: (-row["loss"], row["name"]))

    edge_groups: dict[str, set[tuple[str, str]]] = collections.defaultdict(set)
    for left, right in median_edge_set:
        left_state = state_by_codon[left]
        right_state = state_by_codon[right]
        if left_state == right_state:
            group = f"{left_state}_internal"
        else:
            if state_position[left_state] <= state_position[right_state]:
                group = f"{left_state}-{right_state}"
            else:
                group = f"{right_state}-{left_state}"
        edge_groups[group].add((left, right))
    edge_group_ablation_rows = []
    for group, edges in sorted(edge_groups.items()):
        radius = spectral_radius_for_edge_set(median_set, median_edge_set - edges)
        edge_group_ablation_rows.append(
            loss_row(
                group,
                radius,
                edge_count=len(edges),
                edges=tuple(sorted(edges)),
            )
        )
    edge_group_ablation_rows.sort(key=lambda row: (-row["loss"], row["name"]))

    single_edge_ablation_rows = []
    for edge in sorted(median_edge_set):
        radius = spectral_radius_for_edge_set(median_set, median_edge_set - {edge})
        left, right = edge
        single_edge_ablation_rows.append(
            loss_row(
                f"{left}-{right}",
                radius,
                edge=edge,
                states=tuple(sorted((state_by_codon[left], state_by_codon[right]), key=state_position.get)),
            )
        )
    single_edge_ablation_rows.sort(key=lambda row: (-row["loss"], row["name"]))
    spectral_ablation_summary = {
        "base_spectral_radius": median_spectral_radius,
        "single_codon_orbit_rows": single_codon_orbit_rows,
        "single_codon_top_rows": single_codon_ablation_rows[:10],
        "module_ablation_rows": module_ablation_rows,
        "tail_coupling_ablation": next(row for row in edge_group_ablation_rows if row["name"] == "UUR-CUR"),
        "edge_group_ablation_rows": edge_group_ablation_rows,
        "single_edge_top_rows": single_edge_ablation_rows[:12],
    }
    doob_mu = radial_mu_max + 1.0
    doob_neighbor_matrix = tuple(
        tuple(
            radial_matrix[row][column] + (1 if row == column else 0)
            for column in range(len(radial_matrix))
        )
        for row in range(len(radial_matrix))
    )
    doob_transition_matrix = tuple(
        tuple(
            doob_neighbor_matrix[row][column] * radial_vector[column] / (doob_mu * radial_vector[row])
            for column in range(len(radial_matrix))
        )
        for row in range(len(radial_matrix))
    )
    doob_transition_rows = [
        {
            "state": state,
            "name": radial_state_names[state],
            "transitions": {
                target: doob_transition_matrix[row][column]
                for column, target in enumerate(radial_state_order)
                if doob_transition_matrix[row][column] > 1e-12
            },
            "row_sum": sum(doob_transition_matrix[row]),
        }
        for row, state in enumerate(radial_state_order)
    ]
    doob_drift_rows = [
        {
            "state": state,
            "name": radial_state_names[state],
            "drift": sum(
                (column - row) * doob_transition_matrix[row][column]
                for column in range(len(radial_state_order))
            ),
        }
        for row, state in enumerate(radial_state_order)
    ]
    doob_stationary_denominator = sum(
        radial_lift_sizes[index] * radial_vector[index] * radial_vector[index]
        for index in range(len(radial_state_order))
    )
    doob_stationary_rows = [
        {
            "state": state,
            "name": radial_state_names[state],
            "orbit_size": radial_lift_sizes[index],
            "mass": (
                radial_lift_sizes[index] * radial_vector[index] * radial_vector[index]
                / doob_stationary_denominator
            ),
        }
        for index, state in enumerate(radial_state_order)
    ]
    doob_qsd_comparison_rows = [
        {
            "state": state,
            "name": radial_state_names[state],
            "qsd_mass": radial_qsd_rows[index]["mass"],
            "stationary_mass": doob_stationary_rows[index]["mass"],
        }
        for index, state in enumerate(radial_state_order)
    ]
    doob_flux_rows = []
    for index in range(len(radial_state_order) - 1):
        doob_flux_rows.append(
            {
                "edge_group": f"{radial_state_order[index]}-{radial_state_order[index + 1]}",
                "left": radial_state_order[index],
                "right": radial_state_order[index + 1],
                "left_name": radial_state_names[radial_state_order[index]],
                "right_name": radial_state_names[radial_state_order[index + 1]],
                "flux": doob_stationary_rows[index]["mass"] * doob_transition_matrix[index][index + 1],
            }
        )
    doob_conductance_rows = []
    for index, flux_row in enumerate(doob_flux_rows, start=1):
        prefix_mass = sum(row["mass"] for row in doob_stationary_rows[:index])
        boundary_flux = flux_row["flux"]
        doob_conductance_rows.append(
            {
                "cut": f"{'-'.join(radial_state_order[:index])}|{'-'.join(radial_state_order[index:])}",
                "prefix_states": radial_state_order[:index],
                "suffix_states": radial_state_order[index:],
                "prefix_mass": prefix_mass,
                "boundary_flux": boundary_flux,
                "conductance": boundary_flux / min(prefix_mass, 1.0 - prefix_mass),
            }
        )
    doob_conditioned_summary = {
        "mu": doob_mu,
        "neighbor_matrix": doob_neighbor_matrix,
        "transition_matrix": doob_transition_matrix,
        "transition_rows": doob_transition_rows,
        "drift_rows": doob_drift_rows,
        "stationary_rows": doob_stationary_rows,
        "qsd_comparison_rows": doob_qsd_comparison_rows,
        "anchor_stopstart_stationary_mass": sum(
            row["mass"]
            for row in doob_stationary_rows
            if row["state"] in {"X2", "X1"}
        ),
        "anchor_stopstart_uur_stationary_mass": sum(
            row["mass"]
            for row in doob_stationary_rows
            if row["state"] in {"X2", "X1", "X0"}
        ),
        "flux_rows": doob_flux_rows,
        "central_flux_row": max(doob_flux_rows, key=lambda row: row["flux"]),
        "conductance_rows": doob_conductance_rows,
        "minimum_conductance_row": min(doob_conductance_rows, key=lambda row: row["conductance"]),
    }

    return {
        "support": tuple(sorted(support)),
        "support_size": len(support),
        "exact_motifs": {
            motif: tuple(sorted(codons))
            for motif, codons in exact_sets.items()
        },
        "exact_union": tuple(sorted(exact_union)),
        "exact_formula_matches_support": exact_union == support,
        "internal_subcube_count": len(all_internal_subcubes),
        "prime_implicants": [
            {
                **block,
                "name": subcube_name(block["vertices"]),
                "weight": block_weight(block),
            }
            for block in maximal_internal
        ],
        "minimal_prime_cover_size": len(minimal_prime_covers[0]),
        "minimal_prime_cover_count": len(minimal_prime_covers),
        "minimal_prime_covers": [
            [subcube_name(tuple(block["vertices"])) for block in cover]
            for cover in minimal_prime_covers
        ],
        "minimal_exact_cover_size": len(minimal_exact_covers[0]),
        "minimal_exact_cover_count": len(minimal_exact_covers),
        "minimal_exact_covers": [
            [subcube_name(tuple(block["vertices"])) for block in cover]
            for cover in minimal_exact_covers
        ],
        "common_exact_cover_blocks": sorted(subcube_name(vertices) for vertices in common_exact_blocks),
        "prime_overlap_rows": sorted(prime_overlap_rows, key=lambda row: (row["left"], row["right"])),
        "prime_overlap_weight_totals": dict(sorted(overlap_weight_by_prime.items())),
        "envelope_motifs": {
            motif: tuple(sorted(codons))
            for motif, codons in envelope_sets.items()
        },
        "envelope_union": tuple(sorted(envelope_union)),
        "envelope_false_positives": tuple(sorted(envelope_union - support)),
        "envelope_covers_support": support <= envelope_union,
        "skeleton": {
            "node_count": len(support),
            "edge_count": len(graph_edges),
            "component_count": len(graph_components_list),
            "component_sizes": [len(component) for component in graph_components_list],
            "cyclomatic_number": len(graph_edges) - len(support) + len(graph_components_list),
            "edges": graph_edges,
            "q2_squares": [
                {
                    "name": block["name"],
                    "vertices": block["vertices"],
                    "weight": block["weight"],
                }
                for block in q2_squares
            ],
            "wna": tuple(expand_iupac_motif("WNA")),
            "punctured_wna": tuple(codon for codon in expand_iupac_motif("WNA") if codon != "ACA"),
            "punctured_wna_missing": "ACA",
            "skeleton_formula_matches_support": skeleton_union == support,
            "punctured_wna_edges": punctured_edges,
            "cun_edges": cun_edges,
            "bridge_edges": bridge_edges,
            "leaf_codons": tuple(sorted(codon for codon, neighbors in graph_adjacency.items() if len(neighbors) == 1)),
            "degrees": dict(sorted((codon, len(neighbors)) for codon, neighbors in graph_adjacency.items())),
            "articulation_codons": tuple(row["codon"] for row in articulation_rows),
            "articulation_rows": articulation_rows,
            "biconnected_components": biconnected,
            "largest_biconnected_component": biconnected[0],
            "largest_biconnected_component_weight": sum(codon_weight(codon) for codon in biconnected[0]),
            "random_compactness": {
                "trials": random_trials,
                "seed": random_seed,
                "expected_edge_count": len(all_edges) * len(support) * (len(support) - 1) / (64 * 63),
                "random_mean_edge_count": edge_sum / random_trials,
                "exceed_count": exceed_count,
                "p_value": exceed_count / random_trials,
            },
        },
        "boundary_closure": {
            "boundary_edge_count": len(boundary_edges),
            "boundary_codon_count": len(boundary_neighbors),
            "boundary_edges": tuple(boundary_edges),
            "boundary_rows": boundary_rows,
            "top_boundary_rows": boundary_rows[:9],
            "inactive_envelope_corners": tuple(sorted(envelope_union - support)),
            "q2_completion_face_count": len(q2_completion_faces),
            "q2_completion_frontier": tuple(sorted(completion_frontier)),
            "q2_completion_faces": q2_completion_faces,
            "completion_stages": completion_stages,
            "completion_final_size": len(closed),
            "completion_percolates": len(closed) == 64,
            "boundary_class_rows": boundary_class_rows,
        },
        "inactive_anchor_closure": {
            "inactive_anchors": tuple(sorted(inactive_anchors)),
            "anchor_closure": tuple(sorted(anchor_closure)),
            "anchor_closure_size": len(anchor_closure),
            "formula_motifs": {
                "WNA": tuple(expand_iupac_motif("WNA")),
                "WRR": tuple(expand_iupac_motif("WRR")),
                "CUN": tuple(expand_iupac_motif("CUN")),
            },
            "formula_matches_closure": closure_formula_union == anchor_closure,
            "wna_inter_wrr": tuple(codon for codon in expand_iupac_motif("WRA") if codon in wna_set & wrr_set),
            "wna_inter_wrr_is_wra": wna_set & wrr_set == wra_set,
            "wra_weight": sum(codon_weight(codon) for codon in wra_set),
            "active_complex": active_complex,
            "closure_complex": closure_complex,
            "closure_edges": closure_edges,
            "active_boundary_edge_count": len(boundary_edges),
            "closure_boundary_edge_count": closure_boundary_edge_count,
            "active_isoperimetric_max_edges": edge_isoperimetric_max_edges(6, len(support)),
            "closure_isoperimetric_max_edges": edge_isoperimetric_max_edges(6, len(anchor_closure)),
            "leaf_degree_change": {
                "TAG": {
                    "active_degree": len(graph_adjacency["TAG"]),
                    "closure_degree": closure_degrees["TAG"],
                    "closure_neighbors": tuple(
                        sorted(
                            right if left == "TAG" else left
                            for left, right in closure_edges
                            if "TAG" in (left, right)
                        )
                    ),
                },
                "AGG": {
                    "active_degree": len(graph_adjacency["AGG"]),
                    "closure_degree": closure_degrees["AGG"],
                    "closure_neighbors": tuple(
                        sorted(
                            right if left == "AGG" else left
                            for left, right in closure_edges
                            if "AGG" in (left, right)
                        )
                    ),
                },
            },
        },
        "median_closure": {
            "median_closure": tuple(sorted(median_set)),
            "median_closure_size": len(median_set),
            "median_stages": median_stages,
            "formula_motifs": {
                "WNR": tuple(expand_iupac_motif("WNR")),
                "CUN": tuple(expand_iupac_motif("CUN")),
            },
            "formula_matches_median": median_formula_union == median_set,
            "added_over_support": tuple(sorted(median_set - support)),
            "added_over_anchor_closure": tuple(sorted(median_set - anchor_closure)),
            "wyg": tuple(expand_iupac_motif("WYG")),
            "added_over_anchor_closure_is_wyg": median_set - anchor_closure == wyg_set,
            "closure_chain_sizes": {
                "support": len(support),
                "anchor_closure": len(anchor_closure),
                "median_closure": len(median_set),
                "convex_hull": len(convex_set),
            },
            "convex_hull_size": len(convex_set),
            "convex_hull_is_q6": len(convex_set) == 64,
            "convex_stages": convex_stages,
            "complex": median_complex,
            "maximal_cells": [
                {
                    "name": subcube_name(tuple(cell["vertices"])),
                    "dimension": len(cell["free_bits"]),
                    "vertices": tuple(cell["vertices"]),
                }
                for cell in maximal_median_cells
            ],
            "yur": tuple(expand_iupac_motif("YUR")),
            "yur_inter_wnr": tuple(sorted(yur_set & wnr_set)),
            "yur_inter_cun": tuple(sorted(yur_set & cun)),
            "boundary_edge_count": median_boundary_edges,
        },
        "median_depth_sealing": {
            "stage_count": len(median_stages),
            "stages": median_stages,
            "stage_one_closure": tuple(sorted(median_stage_one)),
            "stage_one_size": len(median_stage_one),
            "stage_one_formula": tuple(sorted(median_stage_one_formula)),
            "stage_one_formula_matches": median_stage_one == median_stage_one_formula,
            "stage_one_missing_from_median": tuple(sorted(median_set - median_stage_one)),
            "stage_one_complex": median_stage_one_complex,
            "median_complex": median_complex,
            "sealing_corner": "ACG",
            "sealing_delta_f": median_stage_delta_f,
            "active_one_step_new": tuple(sorted(active_one_step_medians - support)),
            "active_one_step_contains_sealing_corner": "ACG" in active_one_step_medians,
            "strict_second_order_points": tuple(sorted(median_set - support - (active_one_step_medians - support))),
            "first_step_witnesses": [
                {
                    **row,
                    "median": median_codon(*row["triple"]),
                    "valid": median_codon(*row["triple"]) == row["codon"],
                }
                for row in median_first_step_witnesses
            ],
            "second_step_witness": {
                **median_second_step_witness,
                "median": median_codon(*median_second_step_witness["triple"]),
                "valid": median_codon(*median_second_step_witness["triple"]) == median_second_step_witness["codon"],
            },
        },
        "median_leakage": {
            "active_triple_count": len(active_triple_outputs),
            "closed_triple_count": closed_triple_count,
            "leakage_triple_count": len(leakage_triples),
            "closed_triple_rate": closed_triple_count / len(active_triple_outputs),
            "leakage_triple_rate": len(leakage_triples) / len(active_triple_outputs),
            "one_step_closure": tuple(sorted(support | set(leakage_output_counts))),
            "one_step_closure_size": len(support | set(leakage_output_counts)),
            "leakage_outputs": tuple(sorted(leakage_output_counts)),
            "leakage_output_count": len(leakage_output_counts),
            "leakage_triples": [
                {"triple": row["triple"], "median": row["median"]}
                for row in leakage_triples
            ],
            "median_centrality_rows": median_centrality_rows,
            "leakage_output_rows": leakage_output_rows,
            "leakage_catalyst_rows": leakage_catalyst_rows,
            "random_comparison": {
                "trials": leakage_random_trials,
                "seed": leakage_random_seed,
                "random_mean_closed_triples": random_closed_sum / leakage_random_trials,
                "random_mean_one_step_closure_size": random_one_step_size_sum / leakage_random_trials,
                "random_mean_leakage_output_count": random_leakage_output_sum / leakage_random_trials,
                "closed_triple_exceed_count": random_closed_exceed,
                "closed_triple_p_value": random_closed_exceed / leakage_random_trials,
                "leakage_output_leq_count": random_leakage_output_leq,
                "leakage_output_p_value": random_leakage_output_leq / leakage_random_trials,
            },
            "minimal_inactive_generator_size": minimal_inactive_generator_size,
            "minimal_inactive_generator_count": len(minimal_inactive_generators),
            "minimal_inactive_generators": minimal_inactive_generators,
            "inactive_generator_forced_codons": tuple(
                codon
                for codon in support_tuple
                if all(codon in generator for generator in minimal_inactive_generators)
            ),
            "acg_second_order_triple_count": len(acg_second_order_triples),
            "acg_second_order_triples": acg_second_order_triples,
        },
        "generator_robustness": {
            "minimal_median_generator_size": minimal_median_generator_size,
            "minimal_median_generator_count": len(minimal_median_generators),
            "minimal_median_generators": minimal_median_generators,
            "median_forced_generator_codons": median_forced_generators,
            "median_generator_choice_codons": tuple(
                sorted(set().union(*(set(generator) for generator in minimal_median_generators)) - set(median_forced_generators))
            ),
            "median_deletion_rows": deletion_rows,
            "median_essential_codons": median_essential,
            "median_redundant_codons": median_redundant,
            "complement_pairs": complement_pairs,
            "convex_hull_two_point_witnesses": complement_pairs,
            "q2_single_deletion_rows": q2_deletion_rows,
            "q2_single_deletion_all_percolate": all(row["percolates"] for row in q2_deletion_rows),
            "minimal_q2_percolating_seed_size": minimal_q2_percolating_seed_size,
            "minimal_q2_percolating_seed_count": len(q2_percolating_seeds),
        },
        "symmetry_restoration": {
            "automorphism_group_size": len(automorphisms),
            "weight_stabilizer_size": len(weight_stabilizer_indices_tuple),
            "weight_stabilizer_names": [
                automorphism_name(*automorphisms[index])
                for index in weight_stabilizer_indices_tuple
            ],
            "support_stabilizer_size": len(support_stabilizer_indices),
            "support_stabilizer_names": [
                automorphism_name(*automorphisms[index])
                for index in support_stabilizer_indices
            ],
            "anchor_stabilizer_size": len(anchor_stabilizer_indices),
            "anchor_stabilizer_names": [
                automorphism_name(*automorphisms[index])
                for index in anchor_stabilizer_indices
            ],
            "stage_one_stabilizer_size": len(stage_one_stabilizer_indices),
            "stage_one_stabilizer_names": [
                automorphism_name(*automorphisms[index])
                for index in stage_one_stabilizer_indices
            ],
            "median_stabilizer_size": len(median_stabilizer_indices),
            "median_stabilizer_names": [
                automorphism_name(*automorphisms[index])
                for index in median_stabilizer_indices
            ],
            "median_stabilizer_is_s3_times_c2": len(median_stabilizer_indices) == 12
            and len(median_formula_stabilizer) == 12,
            "tau_generator": "swap(s1,f2)",
            "tau_orbits": tau_orbits,
            "median_orbits": median_orbits,
            "acg_orbit": acg_orbit,
            "acg_orbit_missing_from_stage_one": tuple(sorted(set(acg_orbit) - median_stage_one)),
            "stage_one_is_median_without_acg": median_stage_one == median_set - {"ACG"},
            "symmetry_chain": [
                {"object": "weight", "stabilizer_size": len(weight_stabilizer_indices_tuple), "group": "trivial"},
                {"object": "support", "stabilizer_size": len(support_stabilizer_indices), "group": "C2"},
                {"object": "anchor_closure", "stabilizer_size": len(anchor_stabilizer_indices), "group": "C2"},
                {"object": "median_stage_one", "stabilizer_size": len(stage_one_stabilizer_indices), "group": "C2"},
                {"object": "median_closure", "stabilizer_size": len(median_stabilizer_indices), "group": "S3 x C2"},
            ],
            "tau_weight_violation": {
                "left": "TGA",
                "right": apply_cube_automorphism("TGA", *tau),
                "left_weight": weights_for_symmetry[symmetry_codon_index["TGA"]],
                "right_weight": weights_for_symmetry[symmetry_codon_index[apply_cube_automorphism("TGA", *tau)]],
            },
        },
        "quotient_dynamics": {
            "orbit_rows": orbit_rows,
            "orbit_adjacency_matrix": tuple(tuple(row) for row in orbit_adjacency_matrix),
            "orbit_cross_edges": orbit_cross_edges,
            "quotient_path": ("AGR", "Anchor6", "StopStart6", "UUR", "CUR", "CUY"),
            "median_edge_count": len(median_edges),
            "inactive_layer": tuple(sorted(inactive_layer)),
            "inactive_layer_formula": {
                "WYG": tuple(expand_iupac_motif("WYG")),
                "anchors": ("AAG", "ACA", "TGG"),
            },
            "inactive_layer_formula_matches": inactive_layer == (set(expand_iupac_motif("WYG")) | {"AAG", "ACA", "TGG"}),
            "inactive_edges": inactive_edges,
            "inactive_complex": inactive_complex,
            "active_inactive_edge_count": len(active_inactive_edges),
            "active_inactive_edges": active_inactive_edges,
            "inactive_interface_rows": inactive_interface_rows,
            "active_interface_rows": active_interface_rows,
            "active_interface_gates": tuple(
                row["active_codon"]
                for row in active_interface_rows
                if row["interface_degree"] == active_interface_rows[0]["interface_degree"]
            ),
            "acg_local_neighbors": {
                "inactive_neighbors": tuple(
                    sorted(
                        right if left == "ACG" else left
                        for left, right in inactive_edges
                        if "ACG" in (left, right)
                    )
                ),
                "active_neighbors": tuple(sorted(inactive_interface["ACG"])),
            },
        },
        "quotient_leakage_dynamics": {
            "state_order": path_order,
            "transition_matrix": tuple(
                tuple(fraction_string(value) for value in row)
                for row in transition_matrix
            ),
            "transition_matrix_float": tuple(
                tuple(float(value) for value in row)
                for row in transition_matrix
            ),
            "outside_probabilities": tuple(fraction_string(value) for value in leakage_probabilities),
            "outside_probabilities_float": tuple(float(value) for value in leakage_probabilities),
            "self_retention_probabilities": tuple(
                fraction_string(transition_matrix[index][index])
                for index in range(len(path_order))
            ),
            "expected_exit_times": tuple(fraction_string(value) for value in expected_exit_times),
            "expected_exit_times_float": tuple(float(value) for value in expected_exit_times),
            "closure_retention_rows": closure_retention_rows,
            "acg_stage_one_neighbors": acg_stage_one_neighbors,
            "acg_stage_one_neighbor_count": len(acg_stage_one_neighbors),
            "acg_boundary_delta": acg_boundary_delta,
            "boundary_before_acg": closure_retention_rows[2]["boundary_half_edges"],
            "boundary_after_acg": closure_retention_rows[3]["boundary_half_edges"],
        },
        "spectral_stabilization": {
            "closure_spectral_rows": spectral_rows,
            "median_spectral_radius": median_spectral_radius,
            "median_quasi_lifetime": 1.0 / (1.0 - median_spectral_radius),
            "qsd_rows": qsd_rows,
            "anchor_stopstart_qsd_mass": sum(
                row["mass"]
                for row in qsd_rows
                if row["state"] in {"Anchor6", "StopStart6"}
            ),
            "survival_potential_rows": survival_rows,
            "highest_survival_potential_state": max(
                survival_rows,
                key=lambda row: row["potential"],
            )["state"],
            "exit_prestates": exit_prestates,
            "anchor_stopstart_exit_share": sum(
                row["conditional_probability"]
                for row in exit_prestates
                if row["state"] in {"Anchor6", "StopStart6"}
            ),
            "outside_target_rows": outside_target_rows,
            "first_exit_channels": first_exit_channel_summary,
            "post_median_gate_shell": post_median_gate_shell_summary,
            "antipodal_trigger": antipodal_trigger_summary,
            "acg_spectral_radius_before": spectral_rows[2]["spectral_radius"],
            "acg_spectral_radius_after": spectral_rows[3]["spectral_radius"],
            "acg_retention_before": spectral_rows[2]["retention_float"],
            "acg_retention_after": spectral_rows[3]["retention_float"],
            "acg_boundary_before": closure_retention_rows[2]["boundary_half_edges"],
            "acg_boundary_after": closure_retention_rows[3]["boundary_half_edges"],
        },
        "greedy_spectral_closure": {
            "anchor_triple_search": anchor_triple_spectral_search,
            "support_pair_search": support_pair_spectral_search,
            "first_median_triple_search": first_median_triple_spectral_search,
            "anchor_single_search": anchor_single_spectral_search,
            "anchor_pair_search": anchor_pair_spectral_search,
            "acg_single_search": acg_single_spectral_search,
            "support_single_search": support_single_spectral_search,
            "chain_rows": greedy_spectral_chain_rows,
            "gain_rows": [
                {
                    "step": "support_to_anchor_closure",
                    "gain": anchor_triple_spectral_search["best_gain"],
                },
                {
                    "step": "anchor_closure_to_median_stage_one",
                    "gain": first_median_triple_spectral_search["best_gain"],
                },
                {
                    "step": "median_stage_one_to_median_closure",
                    "gain": acg_single_spectral_search["best_gain"],
                },
            ],
            "fixed_budget_rows": [
                {
                    "budget": 1,
                    "candidate_count": support_single_spectral_search["candidate_count"],
                    "best_count": support_single_spectral_search["best_count"],
                    "best_added_rows": support_single_spectral_search["best_rows"],
                },
                {
                    "budget": 2,
                    "candidate_count": support_pair_spectral_search["candidate_count"],
                    "best_count": support_pair_spectral_search["best_count"],
                    "best_added_rows": support_pair_spectral_search["best_rows"],
                },
                {
                    "budget": 3,
                    "candidate_count": anchor_triple_spectral_search["candidate_count"],
                    "best_count": anchor_triple_spectral_search["best_count"],
                    "best_added_rows": anchor_triple_spectral_search["best_rows"],
                },
                {
                    "budget": 4,
                    "candidate_count": 249900,
                    "best_count": 2,
                    "best_added_rows": support_quad_best_rows,
                },
            ],
            "anchor_budget_rows": [
                {
                    "budget": 1,
                    "candidate_count": anchor_single_spectral_search["candidate_count"],
                    "best_count": anchor_single_spectral_search["best_count"],
                    "best_added_rows": anchor_single_spectral_search["best_rows"],
                },
                {
                    "budget": 2,
                    "candidate_count": anchor_pair_spectral_search["candidate_count"],
                    "best_count": anchor_pair_spectral_search["best_count"],
                    "best_added_rows": anchor_pair_spectral_search["best_rows"],
                },
                {
                    "budget": 3,
                    "candidate_count": first_median_triple_spectral_search["candidate_count"],
                    "best_count": first_median_triple_spectral_search["best_count"],
                    "best_added_rows": first_median_triple_spectral_search["best_rows"],
                },
            ],
            "tau_invariant_frontier_rows": tau_invariant_frontier_rows,
            "fixed_budget_nested_failure": {
                "budget_2": support_pair_spectral_search["best_added"],
                "budget_3": anchor_triple_spectral_search["best_added"],
                "budget_2_subset_budget_3": set(support_pair_spectral_search["best_added"])
                <= set(anchor_triple_spectral_search["best_added"]),
            },
        },
        "wobble_saturation": {
            "bit_coordinates": BIT_COORDINATES,
            "directional_saturation_rows": directional_saturation_rows,
            "f3_saturation": tuple(sorted(f3_saturation)),
            "f3_saturation_added_over_support": tuple(sorted(f3_saturation - support)),
            "f3_saturation_missing_from_median": tuple(sorted(median_set - f3_saturation)),
            "f3_saturation_equals_median_minus_thr_pair": f3_saturation == median_set - {"ACA", "ACG"},
            "f3_completion_points": f3_completion_points,
            "sat_f3_support_aca_equals_median": directional_saturation(support | {"ACA"}, f3_index) == median_set,
            "sat_f3_support_acg_equals_median": directional_saturation(support | {"ACG"}, f3_index) == median_set,
            "direction_boundary_rows": direction_boundary_rows,
            "stage_one_f3_boundary_edges": stage_one_f3_boundary_edges,
            "median_f3_silent": directional_boundary_counts(median_set)[f3_index] == 0,
            "median_boolean_formula_vertices": tuple(sorted(median_boolean_formula_vertices)),
            "median_boolean_formula_matches": median_boolean_formula_vertices == median_set,
            "median_boolean_formula": "(not f1 and s3) or (f1 and not s1 and not s2 and not f2)",
            "quotient": {
                "projection": "delete f3",
                "support": tuple(quotient_label(word) for word in sorted(quotient_support)),
                "median_closure": tuple(quotient_label(word) for word in sorted(quotient_median)),
                "support_is_median_minus_acr": quotient_support == quotient_median - {quotient_label_to_word["ACR"]},
                "missing_support_point": tuple(
                    quotient_label(word)
                    for word in sorted(quotient_median - quotient_support)
                ),
                "median_closure_of_support": tuple(
                    quotient_label(word)
                    for word in sorted(quotient_median_from_support)
                ),
                "median_stages": quotient_median_stages,
                "median_closure_matches_projected_median": quotient_median_from_support == quotient_median,
                "acr_witness": {
                    "triple": ("AGR", "AUR", "UCR"),
                    "median": quotient_label(
                        median_word(
                            quotient_label_to_word["AGR"],
                            quotient_label_to_word["AUR"],
                            quotient_label_to_word["UCR"],
                        )
                    ),
                },
                "complex": quotient_complex,
                "support_complex": quotient_support_complex,
                "edges": tuple(
                    (quotient_label(left), quotient_label(right))
                    for left, right in quotient_edges
                ),
                "product_with_f3_preimage_matches_median": quotient_preimage == median_set,
                "product_f_vector": quotient_product_f_vector,
                "median_f_vector": median_complex["f_vector"][:5],
                "quotient_mu_max": quotient_mu_max,
                "product_spectral_radius": quotient_product_spectral_radius,
                "median_spectral_radius": median_spectral_radius,
                "occupancy_rows": quotient_occupancy_rows,
                "full_active_pairs": tuple(
                    row["quotient"]
                    for row in quotient_occupancy_rows
                    if row["active_occupancy"] == 2
                ),
                "half_active_pairs": tuple(
                    row["quotient"]
                    for row in quotient_occupancy_rows
                    if row["active_occupancy"] == 1
                ),
                "empty_pairs": tuple(
                    row["quotient"]
                    for row in quotient_occupancy_rows
                    if row["active_occupancy"] == 0
                ),
                "radial_spectrum": {
                    "state_order": radial_state_order,
                    "state_names": radial_state_names,
                    "state_codons": radial_state_codons,
                    "lift_orbit_sizes": radial_lift_sizes,
                    "adjacency_matrix": radial_matrix,
                    "characteristic_polynomial_coefficients": radial_characteristic_polynomial,
                    "cubic_in_mu_squared_coefficients": radial_cubic_coefficients,
                    "r_max": radial_r_max,
                    "mu_max": radial_mu_max,
                    "lambda_from_radial": radial_product_lambda,
                    "lambda_matches_median": abs(radial_product_lambda - median_spectral_radius) < 1e-12,
                    "survival_potential_rows": radial_survival_rows,
                    "qsd_rows": radial_qsd_rows,
                    "anchor_stopstart_mass": sum(
                        row["mass"]
                        for row in radial_qsd_rows
                        if row["state"] in {"X2", "X1"}
                    ),
                    "highest_survival_state": max(
                        radial_survival_rows,
                        key=lambda row: row["potential"],
                    )["state"],
                    "self_loop_probability_from_f3": "1/6",
                    "wobble_lambda_gain": 1.0 / 6.0,
                    "lambda_without_wobble_edge": radial_mu_max / 6.0,
                    "spectral_antenna": spectral_antenna_summary,
                    "spectral_ablation": spectral_ablation_summary,
                    "doob_conditioned_dynamics": doob_conditioned_summary,
                },
            },
        },
    }


def module_value_adjacency(states: list[tuple[tuple[str, ...], ...]]) -> dict[int, set[int]]:
    adjacency: dict[int, set[int]] = {index: set() for index in range(len(states))}
    for left, right in itertools.combinations(range(len(states)), 2):
        if sum(a != b for a, b in zip(states[left], states[right])) == 1:
            adjacency[left].add(right)
            adjacency[right].add(left)
    return adjacency


def graph_diameter(adjacency: dict[int, set[int]]) -> int:
    diameter = 0
    for index in adjacency:
        distances = graph_distances(adjacency, index)
        diameter = max(diameter, max(distances.values()))
    return diameter


def target_monotone_reachable(
    standard: tuple[tuple[str, ...], ...],
    target: tuple[tuple[str, ...], ...],
    allowed: set[tuple[tuple[str, ...], ...]],
) -> bool:
    if standard == target:
        return True
    queue = collections.deque([standard])
    seen = {standard}
    while queue:
        state = queue.popleft()
        for index, value in enumerate(state):
            if value == target[index]:
                continue
            if value != standard[index]:
                continue
            candidate = list(state)
            candidate[index] = target[index]
            candidate_tuple = tuple(candidate)
            if candidate_tuple not in allowed or candidate_tuple in seen:
                continue
            if candidate_tuple == target:
                return True
            seen.add(candidate_tuple)
            queue.append(candidate_tuple)
    return False


def latent_completion_summary(tables: dict[int, dict[str, str]]) -> dict[str, object]:
    state_tables: dict[tuple[tuple[str, ...], ...], list[int]] = collections.defaultdict(list)
    for table_id, table in sorted(tables.items()):
        state_tables[module_state(table)].append(table_id)
    observed_states = list(state_tables)
    observed = set(observed_states)
    standard = module_state(tables[1])
    exceptions = [
        state
        for state in observed_states
        if not target_monotone_reachable(standard, state, observed)
    ]

    def graph_stats(states: list[tuple[tuple[str, ...], ...]]) -> dict[str, int]:
        adjacency = module_value_adjacency(states)
        standard_index = states.index(standard)
        standard_distances = graph_distances(adjacency, standard_index)
        observed_indices = [states.index(state) for state in observed_states]
        return {
            "nodes": len(states),
            "edges": sum(len(neighbors) for neighbors in adjacency.values()) // 2,
            "diameter": graph_diameter(adjacency),
            "max_standard_to_observed_distance": max(standard_distances[index] for index in observed_indices),
        }

    with_ss = observed_states + [LATENT_SS]
    with_both = observed_states + [LATENT_SS, LATENT_PARTIAL]
    completed = set(with_both)
    completed_exceptions = [
        state
        for state in observed_states
        if not target_monotone_reachable(standard, state, completed)
    ]
    latent_pool = {
        "L_SS": LATENT_SS,
        "L_N": LATENT_N,
        "L_partial": LATENT_PARTIAL,
        "L_Q_partial": LATENT_Q_PARTIAL,
    }
    minimal_completions: list[tuple[str, ...]] = []
    for size in range(1, len(latent_pool) + 1):
        for names in itertools.combinations(latent_pool, size):
            allowed = observed | {latent_pool[name] for name in names}
            if all(target_monotone_reachable(standard, state, allowed) for state in observed_states):
                minimal_completions.append(names)
        if minimal_completions:
            break

    directed_edges: list[tuple[int, int]] = []
    canonical_states = with_both
    for left, right in itertools.permutations(range(len(canonical_states)), 2):
        source = canonical_states[left]
        target = canonical_states[right]
        different = [index for index, pair in enumerate(zip(source, target)) if pair[0] != pair[1]]
        if len(different) != 1:
            continue
        index = different[0]
        if source[index] == standard[index] and target[index] != standard[index]:
            directed_edges.append((left, right))
    directed_adjacency: dict[int, set[int]] = {index: set() for index in range(len(canonical_states))}
    for left, right in directed_edges:
        directed_adjacency[left].add(right)
    reachable = {canonical_states.index(standard)}
    stack = [canonical_states.index(standard)]
    while stack:
        item = stack.pop()
        for neighbor in directed_adjacency[item]:
            if neighbor not in reachable:
                reachable.add(neighbor)
                stack.append(neighbor)
    observed_reachable = sum(1 for state in observed_states if canonical_states.index(state) in reachable)
    return {
        "observed_exception_count": len(exceptions),
        "observed_exception_tables": [state_tables[state] for state in exceptions],
        "latent_states": {
            "L_SS": "/".join(module_value_key(value) for value in LATENT_SS),
            "L_partial": "/".join(module_value_key(value) for value in LATENT_PARTIAL),
            "L_N": "/".join(module_value_key(value) for value in LATENT_N),
            "L_Q_partial": "/".join(module_value_key(value) for value in LATENT_Q_PARTIAL),
        },
        "minimal_completion_size": len(minimal_completions[0]),
        "minimal_completion_count": len(minimal_completions),
        "minimal_completions": [list(names) for names in minimal_completions],
        "canonical_completion": ["L_SS", "L_partial"],
        "completed_exception_count": len(completed_exceptions),
        "canonical_directed_rewrite": {
            "nodes": len(canonical_states),
            "edges": len(directed_edges),
            "reachable_nodes": len(reachable),
            "reachable_observed_states": observed_reachable,
        },
        "graph_stats": {
            "observed": graph_stats(observed_states),
            "with_L_SS": graph_stats(with_ss),
            "with_both": graph_stats(with_both),
        },
    }


def reassignment_spectrum(tables: dict[int, dict[str, str]], cubes: list[dict[str, object]]) -> dict[str, object]:
    standard = tables[1]
    module_counts: collections.Counter[str] = collections.Counter()
    module_tables: dict[str, set[int]] = collections.defaultdict(set)
    stop_local: collections.Counter[str] = collections.Counter()
    codon_counts: collections.Counter[str] = collections.Counter()
    diffs: list[tuple[int, str, str, str]] = []
    for table_id, table in sorted(tables.items()):
        if table_id == 1:
            continue
        for codon in all_codons():
            if table[codon] == standard[codon]:
                continue
            codon_counts[codon] += 1
            diffs.append((table_id, codon, standard[codon], table[codon]))
            module = "Other"
            for name, codons in MODULES.items():
                if codon in codons:
                    module = name
                    break
            module_counts[module] += 1
            module_tables[module].add(table_id)
            if codon in MODULES["Stop/Trp"]:
                stop_local[codon] += 1
    q3_scores = sorted(
        (
            sum(codon_counts[codon] for codon in cube["vertices"]),
            tuple(cube["vertices"]),
            tuple(cube["free_bits"]),
            cube["pattern"],
        )
        for cube in cubes
    )
    aga_agg_targets = [
        (table_id, table["AGA"], table["AGG"])
        for table_id, table in sorted(tables.items())
        if table_id != 1 and (table["AGA"] != standard["AGA"] or table["AGG"] != standard["AGG"])
    ]
    wrr_states: collections.Counter[tuple[str, ...]] = collections.Counter(
        tuple(table[codon] for codon in WRR_CUBE) for table in tables.values()
    )
    core_states: collections.Counter[tuple[str, ...]] = collections.Counter(
        tuple(table[codon] for codon in CORE_HOTSPOT) for table in tables.values()
    )
    delta_sets: dict[str, set[int]] = {
        codon: {
            table_id
            for table_id, table in tables.items()
            if table_id != 1 and table[codon] != standard[codon]
        }
        for codon in all_codons()
    }
    core_capture = sum(codon_counts[codon] for codon in set(CORE_HOTSPOT))
    return {
        "total": len(diffs),
        "codon_counts": dict(codon_counts),
        "module_counts": dict(module_counts),
        "module_tables": {key: sorted(value) for key, value in module_tables.items()},
        "module_table_counts": {key: len(value) for key, value in module_tables.items()},
        "stop_local": {codon: stop_local[codon] for codon in ("TAA", "TAG", "TGA", "TGG")},
        "wrr_cube": {
            "codon_counts": {codon: codon_counts[codon] for codon in WRR_CUBE},
            "total": sum(codon_counts[codon] for codon in WRR_CUBE),
            "standard_labels": {codon: standard[codon] for codon in WRR_CUBE},
            "distinct_state_count": len(wrr_states),
            "standard_state_tables": [
                table_id
                for table_id, table in sorted(tables.items())
                if tuple(table[codon] for codon in WRR_CUBE)
                == tuple(standard[codon] for codon in WRR_CUBE)
            ],
            "states": {"/".join(state): count for state, count in sorted(wrr_states.items(), key=lambda item: (-item[1], item[0]))},
        },
        "core_hotspot": {
            "codons": CORE_HOTSPOT,
            "capture": core_capture,
            "distinct_state_count": len(core_states),
            "delta_sets": {codon: sorted(delta_sets[codon]) for codon in CORE_HOTSPOT},
            "inclusions": {
                "ATA_subset_TGA": delta_sets["ATA"] <= delta_sets["TGA"],
                "AGA_subset_TGA": delta_sets["AGA"] <= delta_sets["TGA"],
                "AGG_subset_TGA": delta_sets["AGG"] <= delta_sets["TGA"],
                "AAA_subset_TGA_AGA_AGG": delta_sets["AAA"] <= (delta_sets["TGA"] & delta_sets["AGA"] & delta_sets["AGG"]),
            },
            "cooccurrence": {
                "TGA_AGA": len(delta_sets["TGA"] & delta_sets["AGA"]),
                "TGA_AGG": len(delta_sets["TGA"] & delta_sets["AGG"]),
                "AGA_AGG": len(delta_sets["AGA"] & delta_sets["AGG"]),
                "AAA_TGA": len(delta_sets["AAA"] & delta_sets["TGA"]),
                "AAA_AGA": len(delta_sets["AAA"] & delta_sets["AGA"]),
                "AAA_AGG": len(delta_sets["AAA"] & delta_sets["AGG"]),
            },
        },
        "q3_reassignment_scores": [
            {"score": score, "vertices": vertices, "free_bits": free_bits, "standard_pattern": pattern}
            for score, vertices, free_bits, pattern in reversed(q3_scores[-10:])
        ],
        "transfer_square": {
            "standard": {codon: standard[codon] for codon in TRANSFER_SQUARE},
            "table_2": {codon: tables[2][codon] for codon in TRANSFER_SQUARE},
        },
        "arg_satellite": {
            "main_box_counts": {codon: codon_counts[codon] for codon in ARG_MAIN_BOX},
            "satellite_counts": {codon: codon_counts[codon] for codon in ARG_SATELLITE},
            "targets": aga_agg_targets,
        },
        "ser_satellite": {codon: codon_counts[codon] for codon in SER_SATELLITE},
        "aua_to_met_tables": [table_id for table_id, codon, _old, new in diffs if codon == "ATA" and new == "M"],
        "tga_to_trp_tables": [table_id for table_id, codon, _old, new in diffs if codon == "TGA" and new == "W"],
        "ugg_changes": [item for item in diffs if item[1] == "TGG"],
    }


def build_summary() -> dict[str, object]:
    text = fetch_ncbi_page()
    tables = parse_tables(text)
    partial_tables = partial_aware_tables(text)
    standard = tables[1]
    q1_same, q1_diff = q1_spectrum(standard)
    q2_total, q2_geometry, three_one = q2_faces(standard)
    q3_total, cubes = q3_spectrum(standard)
    q4_standard, q4_cubes = q4_spectrum(standard)
    all_q1_totals = collections.Counter(sum(q1_spectrum(table)[0]) for table in tables.values())
    return {
        "table_ids": sorted(tables),
        "q1_standard": {"same_by_direction": q1_same, "diff_by_direction": q1_diff, "same_total": sum(q1_same)},
        "q1_random_baseline": q1_random_baseline(standard),
        "nucleotide_substitution": nucleotide_substitution_spectrum(standard),
        "synonymous_graph": synonymous_graph_summary(standard),
        "class_adjacency": class_adjacency_summary(standard),
        "class_transition": class_transition_summary(standard),
        "q2_standard": {
            "total": dict(q2_total),
            "geometry": {key: dict(value) for key, value in q2_geometry.items()},
            "three_one": three_one,
            "complete_global_tiles": complete_global_tiles(standard),
        },
        "q3_standard": {
            "total": dict(q3_total),
            "stop_trp_neighborhoods": dict(containing_cube_patterns(cubes, MODULES["Stop/Trp"])),
            "ile_met_neighborhoods": dict(containing_cube_patterns(cubes, MODULES["Ile/Met"])),
        },
        "q4_standard": {
            **q4_standard,
            "stop_trp_neighborhoods": containing_q4_neighborhoods(q4_cubes, MODULES["Stop/Trp"]),
            "ile_met_neighborhoods": containing_q4_neighborhoods(q4_cubes, MODULES["Ile/Met"]),
        },
        "q5_control_half_cube": q5_control_half_cube_summary(standard),
        "reassignment": reassignment_spectrum(tables, cubes),
        "partial_aware_core": state_components(partial_tables, CORE_HOTSPOT),
        "active_module_partitions": active_module_partition_summary(partial_tables),
        "module_activation_grammar": module_activation_summary(partial_tables),
        "module_value_grammar": module_value_grammar_summary(partial_tables),
        "latent_completion": latent_completion_summary(partial_tables),
        "tile_patterns": tile_pattern_summary(partial_tables),
        "reassignment_concentration": reassignment_concentration_summary(partial_tables),
        "reassignment_mass_geometry": reassignment_mass_geometry_summary(partial_tables),
        "weighted_deformation_spine": weighted_deformation_spine_summary(partial_tables),
        "reassignment_spectral_compression": reassignment_spectral_compression_summary(partial_tables),
        "support_compression": support_compression_summary(partial_tables),
        "q1_all_tables": dict(sorted(all_q1_totals.items())),
    }


def assert_expected(summary: dict[str, object]) -> None:
    assert summary["q1_standard"]["same_by_direction"] == [0, 2, 0, 1, 17, 30]
    assert summary["q1_standard"]["same_total"] == 50
    assert summary["q1_random_baseline"]["degeneracy_histogram"] == {1: 2, 2: 9, 3: 2, 4: 5, 6: 3}
    assert summary["q1_random_baseline"]["same_pair_count"] == 90
    assert summary["q1_random_baseline"]["total_codon_pairs"] == 2016
    assert summary["q1_random_baseline"]["same_edge_probability"]["numerator"] == 5
    assert summary["q1_random_baseline"]["same_edge_probability"]["denominator"] == 112
    assert summary["q1_random_baseline"]["expected_same_edges"]["numerator"] == 60
    assert summary["q1_random_baseline"]["expected_same_edges"]["denominator"] == 7
    assert summary["q1_random_baseline"]["observed_to_expected_ratio"]["numerator"] == 35
    assert summary["q1_random_baseline"]["observed_to_expected_ratio"]["denominator"] == 6
    assert summary["q1_random_baseline"]["variance"]["numerator"] == 686964
    assert summary["q1_random_baseline"]["variance"]["denominator"] == 92659
    assert round(summary["q1_random_baseline"]["standard_deviation"], 3) == 2.723
    assert round(summary["q1_random_baseline"]["z_score"], 1) == 15.2
    assert summary["nucleotide_substitution"] == {
        "same_by_position": [4, 1, 64],
        "diff_by_position": [92, 95, 32],
        "same_total": 69,
    }
    assert summary["synonymous_graph"]["component_types"] == {
        "1": ["M", "W"],
        "2": ["C", "D", "E", "F", "H", "K", "N", "Q", "Y"],
        "3": ["*", "I"],
        "4": ["A", "G", "P", "T", "V"],
        "4+2": ["R", "S"],
        "6": ["L"],
    }
    for label in ("M", "W"):
        assert summary["synonymous_graph"]["classes"][label] == {
            "size": 1,
            "component_sizes": [1],
            "internal_edges": 0,
            "external_boundary_degree": 6,
        }
    for label in ("F", "Y", "C", "H", "Q", "N", "K", "D", "E"):
        assert summary["synonymous_graph"]["classes"][label] == {
            "size": 2,
            "component_sizes": [2],
            "internal_edges": 1,
            "external_boundary_degree": 10,
        }
    for label in ("I", "*"):
        assert summary["synonymous_graph"]["classes"][label] == {
            "size": 3,
            "component_sizes": [3],
            "internal_edges": 2,
            "external_boundary_degree": 14,
        }
    for label in ("P", "T", "V", "A", "G"):
        assert summary["synonymous_graph"]["classes"][label] == {
            "size": 4,
            "component_sizes": [4],
            "internal_edges": 4,
            "external_boundary_degree": 16,
        }
    for label in ("S", "R"):
        assert summary["synonymous_graph"]["classes"][label] == {
            "size": 6,
            "component_sizes": [4, 2],
            "internal_edges": 5,
            "external_boundary_degree": 26,
        }
    assert summary["synonymous_graph"]["classes"]["L"] == {
        "size": 6,
        "component_sizes": [6],
        "internal_edges": 7,
        "external_boundary_degree": 22,
    }
    assert {
        item["pair"]: item["count"]
        for item in summary["class_adjacency"]["top_inter_class_edges"]
    } == {
        "G-R": 6,
        "S-T": 6,
        "A-G": 4,
        "A-P": 4,
        "A-T": 4,
        "A-V": 4,
        "C-S": 4,
        "F-L": 4,
        "L-P": 4,
        "L-V": 4,
        "P-R": 4,
        "P-S": 4,
    }
    assert summary["class_adjacency"]["control_pair_edges"] == {"I-M": 2, "*-W": 2}
    assert summary["class_transition"]["counts"]["*"] == {
        "*": 4,
        "C": 1,
        "K": 2,
        "L": 2,
        "Q": 2,
        "R": 2,
        "S": 1,
        "W": 2,
        "Y": 2,
    }
    assert summary["class_transition"]["counts"]["W"] == {"*": 2, "C": 1, "R": 2, "S": 1}
    assert summary["class_transition"]["counts"]["I"]["I"] == 4
    assert summary["class_transition"]["counts"]["I"]["M"] == 2
    assert summary["class_transition"]["counts"]["M"] == {"I": 2, "K": 1, "L": 1, "T": 1, "V": 1}
    assert summary["q2_standard"]["total"] == {
        "4": 9,
        "3+1": 4,
        "2+2": 83,
        "2+1+1": 44,
        "1+1+1+1": 100,
    }
    assert len(summary["q2_standard"]["complete_global_tiles"]) == 2
    assert summary["q3_standard"]["total"]["6+2"] == 1
    assert summary["q3_standard"]["stop_trp_neighborhoods"] == {"3+2+2+1": 4}
    assert summary["q3_standard"]["ile_met_neighborhoods"] == {"3+2+2+1": 2, "4+3+1": 2}
    assert summary["q4_standard"]["max_class_size_distribution"] == {2: 17, 3: 15, 4: 23, 6: 5}
    assert summary["q4_standard"]["complete_six_class_occurrences"] == {"L": 3, "R": 1, "S": 1}
    assert len(summary["q4_standard"]["stop_trp_neighborhoods"]) == 6
    assert all(
        neighborhood["class_counts"]["*"] == 3 and neighborhood["class_counts"]["W"] == 1
        for neighborhood in summary["q4_standard"]["stop_trp_neighborhoods"]
    )
    assert len(summary["q4_standard"]["ile_met_neighborhoods"]) == 6
    assert all(
        neighborhood["class_counts"]["I"] == 3 and neighborhood["class_counts"]["M"] == 1
        for neighborhood in summary["q4_standard"]["ile_met_neighborhoods"]
    )
    assert any(
        neighborhood["class_counts"] == {"A": 4, "I": 3, "M": 1, "T": 4, "V": 4}
        for neighborhood in summary["q4_standard"]["ile_met_neighborhoods"]
    )
    assert any(
        neighborhood["class_counts"] == {"F": 2, "I": 3, "L": 6, "M": 1, "V": 4}
        for neighborhood in summary["q4_standard"]["ile_met_neighborhoods"]
    )
    assert summary["q5_control_half_cube"]["shared_fixed_bits"] == [{"bit": 1, "value": "0"}]
    assert summary["q5_control_half_cube"]["class_counts"] == {
        "S": 6,
        "T": 4,
        "*": 3,
        "I": 3,
        "C": 2,
        "F": 2,
        "K": 2,
        "L": 2,
        "N": 2,
        "R": 2,
        "Y": 2,
        "M": 1,
        "W": 1,
    }
    assert summary["q5_control_half_cube"]["control_class_counts"] == {
        "Stop": 3,
        "I": 3,
        "W": 1,
        "M": 1,
    }
    assert summary["reassignment"]["total"] == 65
    assert summary["reassignment"]["module_counts"] == {
        "Stop/Trp": 33,
        "Ile/Met": 5,
        "AGA/AGG": 16,
        "Phe/Leu": 7,
        "Other": 4,
    }
    assert summary["reassignment"]["stop_local"] == {"TAA": 8, "TAG": 10, "TGA": 15, "TGG": 0}
    assert summary["reassignment"]["wrr_cube"]["codon_counts"] == {
        "TAA": 8,
        "TAG": 10,
        "TGA": 15,
        "TGG": 0,
        "AAA": 3,
        "AAG": 0,
        "AGA": 8,
        "AGG": 8,
    }
    assert summary["reassignment"]["wrr_cube"]["total"] == 52
    assert summary["reassignment"]["wrr_cube"]["distinct_state_count"] == 19
    assert summary["reassignment"]["wrr_cube"]["standard_state_tables"] == [1, 11, 12, 23, 26]
    assert summary["reassignment"]["core_hotspot"]["capture"] == 57
    assert summary["reassignment"]["core_hotspot"]["distinct_state_count"] == 21
    assert summary["reassignment"]["core_hotspot"]["inclusions"] == {
        "ATA_subset_TGA": True,
        "AGA_subset_TGA": True,
        "AGG_subset_TGA": True,
        "AAA_subset_TGA_AGA_AGG": True,
    }
    assert summary["reassignment"]["core_hotspot"]["cooccurrence"] == {
        "TGA_AGA": 8,
        "TGA_AGG": 8,
        "AGA_AGG": 8,
        "AAA_TGA": 3,
        "AAA_AGA": 3,
        "AAA_AGG": 3,
    }
    assert summary["partial_aware_core"]["distinct_state_count"] == 22
    assert summary["partial_aware_core"]["standard_state_tables"] == [1, 11, 12, 23, 26]
    assert summary["partial_aware_core"]["component_count"] == 9
    assert summary["partial_aware_core"]["component_sizes"] == [10, 4, 2, 1, 1, 1, 1, 1, 1]
    assert summary["partial_aware_core"]["components"][:3] == [
        [[1, 11, 12, 23, 26], [32], [25], [16, 22], [15], [6], [27], [10], [4], [3]],
        [[5], [21], [9], [14]],
        [[24], [33]],
    ]
    assert summary["active_module_partitions"]["bell_count"] == 877
    assert summary["active_module_partitions"]["connected_partition_count"] == 52
    assert summary["active_module_partitions"]["finest_partition_count"] == 1
    assert summary["active_module_partitions"]["finest_partition"] == (
        ("TAA", "TAG"),
        ("TGA",),
        ("AAA",),
        ("AGA", "AGG"),
        ("ATA",),
    )
    assert summary["active_module_partitions"]["module_edge_count"] == 42
    assert summary["active_module_partitions"]["module_edge_counts"] == {
        "StopArm": 25,
        "UGA": 7,
        "AAA": 1,
        "AGR": 7,
        "AUA": 2,
    }
    assert summary["active_module_partitions"]["standard_degree"] == 9
    assert summary["active_module_partitions"]["standard_distance_distribution"] == {
        0: 1,
        1: 9,
        2: 4,
        3: 5,
        4: 1,
        5: 1,
        6: 1,
    }
    assert summary["active_module_partitions"]["diameter"] == 9
    assert summary["module_activation_grammar"]["observed_pattern_count"] == 11
    assert summary["module_activation_grammar"]["observed_patterns"] == {
        "none": [1, 11, 12, 23, 26],
        "S": [6, 15, 16, 22, 29, 30, 32],
        "U": [4, 10, 25],
        "U+I": [3],
        "U+R": [24],
        "S+U": [27, 28, 31],
        "U+R+I": [2, 5, 13],
        "U+N+R": [9],
        "S+U+R": [33],
        "U+N+R+I": [21],
        "S+U+N+R": [14],
    }
    assert summary["module_activation_grammar"]["grammar_solution_count"] == 11
    assert summary["module_activation_grammar"]["exact_match"] is True
    assert summary["module_activation_grammar"]["constraints"] == {
        "R_implies_U": True,
        "I_implies_U": True,
        "N_implies_R": True,
        "S_disjoint_I": True,
    }
    assert summary["module_value_grammar"]["distinct_state_count"] == 22
    assert summary["module_value_grammar"]["module_value_counts"] == {
        "S": 10,
        "U": 5,
        "N": 2,
        "R": 5,
        "I": 2,
    }
    assert summary["module_value_grammar"]["branch_counts"] == {
        "U_star_stoparm": 7,
        "U_cg_pure": 2,
        "U_partial_boundary": 2,
        "U_w_deep": 11,
    }
    assert summary["module_value_grammar"]["generated_state_count"] == 22
    assert summary["module_value_grammar"]["exact_match"] is True
    assert summary["module_value_grammar"]["constraints"] == {
        "R_nonstandard_implies_U_W": True,
        "I_M_implies_U_W_and_S_standard": True,
        "N_N_implies_U_W_and_R_SS": True,
        "R_stop_or_gly_implies_I_M_S_standard_N_K": True,
        "R_SK_implies_I_I_N_K_U_W": True,
    }
    assert summary["latent_completion"]["observed_exception_count"] == 3
    assert summary["latent_completion"]["observed_exception_tables"] == [[9], [14], [28]]
    assert summary["latent_completion"]["latent_states"] == {
        "L_SS": "(*,*)/W/K/(S,S)/I",
        "L_partial": "(*,*)/*|W/K/(R,R)/I",
        "L_N": "(*,*)/W/N/(R,R)/I",
        "L_Q_partial": "(Q|*,Q|*)/*/K/(R,R)/I",
    }
    assert summary["latent_completion"]["minimal_completion_size"] == 2
    assert summary["latent_completion"]["minimal_completion_count"] == 4
    assert summary["latent_completion"]["minimal_completions"] == [
        ["L_SS", "L_partial"],
        ["L_SS", "L_Q_partial"],
        ["L_N", "L_partial"],
        ["L_N", "L_Q_partial"],
    ]
    assert summary["latent_completion"]["canonical_completion"] == ["L_SS", "L_partial"]
    assert summary["latent_completion"]["completed_exception_count"] == 0
    assert summary["latent_completion"]["canonical_directed_rewrite"] == {
        "nodes": 24,
        "edges": 26,
        "reachable_nodes": 24,
        "reachable_observed_states": 22,
    }
    assert summary["latent_completion"]["graph_stats"] == {
        "observed": {
            "nodes": 22,
            "edges": 42,
            "diameter": 9,
            "max_standard_to_observed_distance": 6,
        },
        "with_L_SS": {
            "nodes": 23,
            "edges": 46,
            "diameter": 7,
            "max_standard_to_observed_distance": 4,
        },
        "with_both": {
            "nodes": 24,
            "edges": 52,
            "diameter": 5,
            "max_standard_to_observed_distance": 4,
        },
    }
    assert summary["tile_patterns"]["ile_met_patterns"] == {
        "I/I/I/M": {"count": 22, "tables": [1, 4, 6, 9, 10, 11, 12, 14, 15, 16, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]},
        "I/I/M/M": {"count": 5, "tables": [2, 3, 5, 13, 21]},
    }
    assert len(summary["tile_patterns"]["stop_trp_patterns"]) == 14
    assert summary["tile_patterns"]["stop_trp_patterns"]["*/*/W/W"]["count"] == 8
    assert summary["tile_patterns"]["stop_trp_patterns"]["*/*/*/W"]["count"] == 5
    assert summary["tile_patterns"]["stop_trp_patterns"]["Q|*/Q|*/*|W/W"]["count"] == 1
    assert summary["reassignment_concentration"]["distinct_reassigned_codon_count"] == 13
    assert summary["reassignment_concentration"]["distinct_reassigned_codons"] == [
        "AAA",
        "AGA",
        "AGG",
        "ATA",
        "CTA",
        "CTC",
        "CTG",
        "CTT",
        "TAA",
        "TAG",
        "TCA",
        "TGA",
        "TTA",
    ]
    assert summary["reassignment_concentration"]["weighted_event_count"] == 65
    assert {
        codon: row["count"]
        for codon, row in summary["reassignment_concentration"]["codon_counts"].items()
    } == {
        "TGA": 15,
        "TAG": 10,
        "AGA": 8,
        "AGG": 8,
        "TAA": 8,
        "ATA": 5,
        "AAA": 3,
        "CTG": 3,
        "CTA": 1,
        "CTC": 1,
        "CTT": 1,
        "TCA": 1,
        "TTA": 1,
    }
    assert summary["reassignment_concentration"]["control_half_cube"] == {
        "fixed_bit": 1,
        "fixed_value": "0",
        "inside_event_count": 59,
        "outside_event_count": 6,
        "inside_fraction": 59 / 65,
        "inside_codons": ["AAA", "AGA", "AGG", "ATA", "TAA", "TAG", "TCA", "TGA", "TTA"],
        "outside_codons": ["CTA", "CTC", "CTG", "CTT"],
    }
    assert summary["reassignment_concentration"]["refined_module_counts"] == {
        "Stop/Trp_X2": 33,
        "AGR": 16,
        "Ile/Met_leaf": 5,
        "AAA_leaf": 3,
        "rare_stop_insertions": 2,
        "CUN_Leu": 6,
    }
    assert summary["reassignment_concentration"]["reassigned_codon_graph"]["node_count"] == 13
    assert summary["reassignment_concentration"]["reassigned_codon_graph"]["edge_count"] == 16
    assert summary["reassignment_concentration"]["reassigned_codon_graph"]["component_count"] == 1
    assert summary["reassignment_concentration"]["reassigned_codon_graph"]["component_sizes"] == [13]
    assert summary["reassignment_concentration"]["q1_all_tables"]["min"] == 47
    assert summary["reassignment_concentration"]["q1_all_tables"]["max"] == 52
    assert round(summary["reassignment_concentration"]["q1_all_tables"]["mean"], 2) == 50.07
    assert summary["reassignment_concentration"]["q1_all_tables"]["direction_ranges"][0] == {
        "min": 0,
        "max": 0,
        "mean": 0.0,
    }
    assert summary["reassignment_concentration"]["q1_all_tables"]["direction_ranges"][5]["min"] == 28
    assert summary["reassignment_concentration"]["q1_all_tables"]["direction_ranges"][5]["max"] == 32
    assert round(summary["reassignment_concentration"]["q1_all_tables"]["direction_ranges"][5]["mean"], 2) == 30.04
    assert round(summary["reassignment_concentration"]["nucleotide_substitution_all_tables"]["same_total_mean"], 2) == 69.04
    assert round(summary["reassignment_concentration"]["nucleotide_substitution_all_tables"]["same_by_position"][0]["mean"], 2) == 3.59
    assert round(summary["reassignment_concentration"]["nucleotide_substitution_all_tables"]["same_by_position"][1]["mean"], 2) == 0.67
    assert round(summary["reassignment_concentration"]["nucleotide_substitution_all_tables"]["same_by_position"][2]["mean"], 2) == 64.78
    assert summary["reassignment_mass_geometry"]["total_mass"] == 65
    assert summary["reassignment_mass_geometry"]["codon_weights"] == {
        "TGA": 15,
        "TAG": 10,
        "AGA": 8,
        "AGG": 8,
        "TAA": 8,
        "ATA": 5,
        "AAA": 3,
        "CTG": 3,
        "CTA": 1,
        "CTC": 1,
        "CTT": 1,
        "TCA": 1,
        "TTA": 1,
    }
    assert summary["reassignment_mass_geometry"]["max_subcubes"]["Q5"]["max_mass"] == 63
    assert summary["reassignment_mass_geometry"]["max_subcubes"]["Q5"]["max_count"] == 1
    assert summary["reassignment_mass_geometry"]["max_subcubes"]["Q5"]["maximizers"][0]["fixed_conditions"] == ((4, "1"),)
    assert summary["reassignment_mass_geometry"]["max_subcubes"]["Q4"]["max_mass"] == 59
    assert summary["reassignment_mass_geometry"]["max_subcubes"]["Q4"]["max_count"] == 1
    assert summary["reassignment_mass_geometry"]["max_subcubes"]["Q4"]["maximizers"][0]["fixed_conditions"] == ((1, "0"), (4, "1"))
    assert summary["reassignment_mass_geometry"]["max_subcubes"]["Q3"]["max_mass"] == 52
    assert summary["reassignment_mass_geometry"]["max_subcubes"]["Q3"]["max_count"] == 1
    assert summary["reassignment_mass_geometry"]["max_subcubes"]["Q3"]["maximizers"][0]["fixed_conditions"] == ((1, "0"), (2, "1"), (4, "1"))
    assert summary["reassignment_mass_geometry"]["max_subcubes"]["Q2"]["max_mass"] == 34
    assert summary["reassignment_mass_geometry"]["max_subcubes"]["Q2"]["max_count"] == 1
    assert summary["reassignment_mass_geometry"]["max_subcubes"]["Q2"]["maximizers"][0]["vertices"] == ("TAA", "TGA", "AAA", "AGA")
    assert summary["reassignment_mass_geometry"]["purine_core_q3"] == {
        "vertices": ("TAA", "TAG", "TGA", "TGG", "AAA", "AAG", "AGA", "AGG"),
        "mass": 52,
        "standard_labels": {
            "TAA": "*",
            "TAG": "*",
            "TGA": "*",
            "TGG": "W",
            "AAA": "K",
            "AAG": "K",
            "AGA": "R",
            "AGG": "R",
        },
        "weights": {"TAA": 8, "TAG": 10, "TGA": 15, "TGG": 0, "AAA": 3, "AAG": 0, "AGA": 8, "AGG": 8},
    }
    assert summary["reassignment_mass_geometry"]["a_ending_square"] == {
        "vertices": ("AAA", "AGA", "TAA", "TGA"),
        "mass": 34,
        "standard_labels": {"AAA": "K", "AGA": "R", "TAA": "*", "TGA": "*"},
        "weights": {"AAA": 3, "AGA": 8, "TAA": 8, "TGA": 15},
    }
    assert summary["reassignment_mass_geometry"]["q2_reassigned_vertex_distribution"] == {
        0: 123,
        1: 60,
        2: 40,
        3: 13,
        4: 4,
    }
    assert [
        (face["vertices"], face["mass"])
        for face in summary["reassignment_mass_geometry"]["full_reassigned_q2_faces"]
    ] == [
        (("TAA", "TGA", "AAA", "AGA"), 34),
        (("TTA", "TCA", "TAA", "TGA"), 25),
        (("TTA", "TAA", "ATA", "AAA"), 17),
        (("CTT", "CTC", "CTA", "CTG"), 6),
    ]
    assert [
        (tuple(item["edge"]), item["weight"])
        for item in summary["reassignment_mass_geometry"]["co_reassignment_edges"]
    ] == [
        (("AGA", "AGG"), 8),
        (("TGA", "AGA"), 8),
        (("TAA", "TAG"), 6),
        (("TAA", "TGA"), 5),
        (("AAA", "AGA"), 3),
        (("ATA", "AAA"), 1),
        (("CTA", "CTG"), 1),
        (("CTC", "CTG"), 1),
        (("CTT", "CTA"), 1),
        (("CTT", "CTC"), 1),
        (("TAA", "AAA"), 1),
    ]
    assert summary["reassignment_mass_geometry"]["positive_co_reassignment_components"] == [
        ["AAA", "AGA", "AGG", "ATA", "TAA", "TAG", "TGA"],
        ["CTA", "CTC", "CTG", "CTT"],
        ["TCA"],
        ["TTA"],
    ]
    assert {
        size: {
            "max_mass": summary["weighted_deformation_spine"]["connected_optima"][size]["max_mass"],
            "optimum_count": summary["weighted_deformation_spine"]["connected_optima"][size]["optimum_count"],
            "optima": summary["weighted_deformation_spine"]["connected_optima"][size]["optima"],
        }
        for size in range(1, 8)
    } == {
        1: {"max_mass": 15, "optimum_count": 1, "optima": [("TGA",)]},
        2: {"max_mass": 23, "optimum_count": 2, "optima": [("AGA", "TGA"), ("TAA", "TGA")]},
        3: {"max_mass": 33, "optimum_count": 1, "optima": [("TAA", "TAG", "TGA")]},
        4: {"max_mass": 41, "optimum_count": 1, "optima": [("AGA", "TAA", "TAG", "TGA")]},
        5: {"max_mass": 49, "optimum_count": 1, "optima": [("AGA", "AGG", "TAA", "TAG", "TGA")]},
        6: {"max_mass": 52, "optimum_count": 1, "optima": [("AAA", "AGA", "AGG", "TAA", "TAG", "TGA")]},
        7: {"max_mass": 57, "optimum_count": 1, "optima": [("AAA", "AGA", "AGG", "ATA", "TAA", "TAG", "TGA")]},
    }
    assert summary["weighted_deformation_spine"]["bit_majority"] == [
        {"bit": 0, "majority_value": "0", "zero_mass": 41, "one_mass": 24, "majority_mass": 41, "majority_fraction": 41 / 65},
        {"bit": 1, "majority_value": "0", "zero_mass": 59, "one_mass": 6, "majority_mass": 59, "majority_fraction": 59 / 65},
        {"bit": 2, "majority_value": "1", "zero_mass": 13, "one_mass": 52, "majority_mass": 52, "majority_fraction": 52 / 65},
        {"bit": 3, "majority_value": "0", "zero_mass": 33, "one_mass": 32, "majority_mass": 33, "majority_fraction": 33 / 65},
        {"bit": 4, "majority_value": "1", "zero_mass": 2, "one_mass": 63, "majority_mass": 63, "majority_fraction": 63 / 65},
        {"bit": 5, "majority_value": "0", "zero_mass": 43, "one_mass": 22, "majority_mass": 43, "majority_fraction": 43 / 65},
    ]
    assert summary["weighted_deformation_spine"]["max_q3_support_count"] == 7
    assert summary["weighted_deformation_spine"]["cardinality_q3_maximizers"] == [
        {
            "free_bits": (0, 2, 3),
            "fixed_conditions": ((1, "0"), (4, "1"), (5, "0")),
            "vertices": ("TTA", "TCA", "TAA", "TGA", "ATA", "ACA", "AAA", "AGA"),
            "support_count": 7,
            "mass": 41,
        }
    ]
    assert summary["weighted_deformation_spine"]["minimal_q2_q3_cover_size"] == 3
    assert summary["weighted_deformation_spine"]["canonical_q2_q3_cover"] == [
        {
            "vertices": ("TAA", "TAG", "TGA", "TGG", "AAA", "AAG", "AGA", "AGG"),
            "covered": ("AAA", "AGA", "AGG", "TAA", "TAG", "TGA"),
            "covered_count": 6,
            "mass": 52,
        },
        {
            "vertices": ("CTT", "CTC", "CTA", "CTG"),
            "covered": ("CTA", "CTC", "CTG", "CTT"),
            "covered_count": 4,
            "mass": 6,
        },
        {
            "vertices": ("TTA", "TCA", "ATA", "ACA"),
            "covered": ("ATA", "TCA", "TTA"),
            "covered_count": 3,
            "mass": 7,
        },
    ]
    assert summary["reassignment_spectral_compression"]["total_weight"] == 65
    assert summary["reassignment_spectral_compression"]["mean_coefficient"] == 65 / 64
    assert summary["reassignment_spectral_compression"]["top_nontrivial_coefficients"] == [
        {"bits": (4,), "coefficient": -0.953125, "abs_coefficient": 0.953125},
        {"bits": (1, 4), "coefficient": -0.890625, "abs_coefficient": 0.890625},
        {"bits": (1,), "coefficient": 0.828125, "abs_coefficient": 0.828125},
        {"bits": (1, 2), "coefficient": -0.796875, "abs_coefficient": 0.796875},
        {"bits": (1, 2, 4), "coefficient": 0.734375, "abs_coefficient": 0.734375},
        {"bits": (2, 4), "coefficient": 0.671875, "abs_coefficient": 0.671875},
        {"bits": (2,), "coefficient": -0.609375, "abs_coefficient": 0.609375},
    ]
    assert {
        degree: round(share, 3)
        for degree, share in summary["reassignment_spectral_compression"]["degree_energy_share"].items()
    } == {
        1: 0.275,
        2: 0.320,
        3: 0.194,
        4: 0.137,
        5: 0.065,
        6: 0.009,
    }
    assert round(summary["reassignment_spectral_compression"]["cumulative_energy_share"][3], 3) == 0.789
    assert round(summary["reassignment_spectral_compression"]["cumulative_energy_share"][4], 3) == 0.926
    assert summary["reassignment_spectral_compression"]["monte_carlo"]["trials"] == 100000
    assert summary["reassignment_spectral_compression"]["monte_carlo"]["seed"] == 20260521
    assert {
        dimension: {
            "observed_max_mass": row["observed_max_mass"],
            "exceed_count": row["exceed_count"],
            "random_mean_max_mass": round(row["random_mean_max_mass"], 2),
            "p_value": round(row["p_value"], 5),
        }
        for dimension, row in summary["reassignment_spectral_compression"]["monte_carlo"]["subcube_maxima"].items()
    } == {
        2: {"observed_max_mass": 34, "exceed_count": 1415, "random_mean_max_mass": 24.97, "p_value": 0.01415},
        3: {"observed_max_mass": 52, "exceed_count": 20, "random_mean_max_mass": 31.46, "p_value": 0.00020},
        4: {"observed_max_mass": 59, "exceed_count": 53, "random_mean_max_mass": 39.82, "p_value": 0.00053},
        5: {"observed_max_mass": 63, "exceed_count": 1003, "random_mean_max_mass": 50.94, "p_value": 0.01003},
    }
    assert summary["support_compression"]["support_size"] == 13
    assert summary["support_compression"]["support"] == (
        "AAA",
        "AGA",
        "AGG",
        "ATA",
        "CTA",
        "CTC",
        "CTG",
        "CTT",
        "TAA",
        "TAG",
        "TCA",
        "TGA",
        "TTA",
    )
    assert summary["support_compression"]["exact_motifs"] == {
        "AGR": ("AGA", "AGG"),
        "CUN": ("CTA", "CTC", "CTG", "CTT"),
        "UAR": ("TAA", "TAG"),
        "UNA": ("TAA", "TCA", "TGA", "TTA"),
        "WWA": ("AAA", "ATA", "TAA", "TTA"),
    }
    assert summary["support_compression"]["exact_formula_matches_support"] is True
    assert summary["support_compression"]["internal_subcube_count"] == 33
    assert [
        {key: prime[key] for key in ("name", "vertices", "dimension", "weight")}
        for prime in summary["support_compression"]["prime_implicants"]
    ] == [
        {"name": "CUN", "vertices": ("CTT", "CTC", "CTA", "CTG"), "dimension": 2, "weight": 6},
        {"name": "WRA", "vertices": ("TAA", "TGA", "AAA", "AGA"), "dimension": 2, "weight": 34},
        {"name": "WWA", "vertices": ("TTA", "TAA", "ATA", "AAA"), "dimension": 2, "weight": 17},
        {"name": "UNA", "vertices": ("TTA", "TCA", "TAA", "TGA"), "dimension": 2, "weight": 25},
        {"name": "AGR", "vertices": ("AGA", "AGG"), "dimension": 1, "weight": 16},
        {"name": "UAR", "vertices": ("TAA", "TAG"), "dimension": 1, "weight": 18},
        {"name": "YUA", "vertices": ("TTA", "CTA"), "dimension": 1, "weight": 2},
    ]
    assert summary["support_compression"]["minimal_prime_cover_size"] == 5
    assert summary["support_compression"]["minimal_prime_cover_count"] == 1
    assert summary["support_compression"]["minimal_prime_covers"] == [
        ["CUN", "WWA", "UNA", "AGR", "UAR"]
    ]
    assert summary["support_compression"]["minimal_exact_cover_size"] == 5
    assert summary["support_compression"]["minimal_exact_cover_count"] == 6
    assert summary["support_compression"]["minimal_exact_covers"] == [
        ["UAG", "USA", "AGR", "WWA", "CUN"],
        ["UAG", "AWA", "AGR", "UNA", "CUN"],
        ["UAG", "AGR", "WWA", "UNA", "CUN"],
        ["USA", "UAR", "AGR", "WWA", "CUN"],
        ["AWA", "UAR", "AGR", "UNA", "CUN"],
        ["UAR", "AGR", "WWA", "UNA", "CUN"],
    ]
    assert summary["support_compression"]["common_exact_cover_blocks"] == ["AGR", "CUN"]
    assert summary["support_compression"]["prime_overlap_weight_totals"] == {
        "AGR": 8,
        "CUN": 1,
        "UAR": 24,
        "UNA": 41,
        "WRA": 50,
        "WWA": 29,
        "YUA": 3,
    }
    assert summary["support_compression"]["prime_overlap_rows"] == [
        {"left": "CUN", "right": "YUA", "overlap": ("CTA",), "weight": 1},
        {"left": "UNA", "right": "UAR", "overlap": ("TAA",), "weight": 8},
        {"left": "UNA", "right": "YUA", "overlap": ("TTA",), "weight": 1},
        {"left": "WRA", "right": "AGR", "overlap": ("AGA",), "weight": 8},
        {"left": "WRA", "right": "UAR", "overlap": ("TAA",), "weight": 8},
        {"left": "WRA", "right": "UNA", "overlap": ("TAA", "TGA"), "weight": 23},
        {"left": "WRA", "right": "WWA", "overlap": ("TAA", "AAA"), "weight": 11},
        {"left": "WWA", "right": "UAR", "overlap": ("TAA",), "weight": 8},
        {"left": "WWA", "right": "UNA", "overlap": ("TTA", "TAA"), "weight": 9},
        {"left": "WWA", "right": "YUA", "overlap": ("TTA",), "weight": 1},
    ]
    assert summary["support_compression"]["envelope_motifs"] == {
        "CUN": ("CTA", "CTC", "CTG", "CTT"),
        "WRR": ("AAA", "AAG", "AGA", "AGG", "TAA", "TAG", "TGA", "TGG"),
        "WYA": ("ACA", "ATA", "TCA", "TTA"),
    }
    assert summary["support_compression"]["envelope_covers_support"] is True
    assert summary["support_compression"]["envelope_false_positives"] == ("AAG", "ACA", "TGG")
    skeleton = summary["support_compression"]["skeleton"]
    assert skeleton["node_count"] == 13
    assert skeleton["edge_count"] == 16
    assert skeleton["component_count"] == 1
    assert skeleton["component_sizes"] == [13]
    assert skeleton["cyclomatic_number"] == 4
    assert skeleton["edges"] == (
        ("TTA", "ATA"),
        ("TAA", "AAA"),
        ("TGA", "AGA"),
        ("TTA", "CTA"),
        ("TTA", "TAA"),
        ("TCA", "TGA"),
        ("ATA", "AAA"),
        ("TTA", "TCA"),
        ("TAA", "TGA"),
        ("AAA", "AGA"),
        ("CTT", "CTA"),
        ("CTC", "CTG"),
        ("TAA", "TAG"),
        ("CTT", "CTC"),
        ("CTA", "CTG"),
        ("AGA", "AGG"),
    )
    assert skeleton["q2_squares"] == [
        {"name": "CUN", "vertices": ("CTT", "CTC", "CTA", "CTG"), "weight": 6},
        {"name": "UNA", "vertices": ("TTA", "TCA", "TAA", "TGA"), "weight": 25},
        {"name": "WRA", "vertices": ("TAA", "TGA", "AAA", "AGA"), "weight": 34},
        {"name": "WWA", "vertices": ("TTA", "TAA", "ATA", "AAA"), "weight": 17},
    ]
    assert skeleton["wna"] == ("TTA", "TCA", "TAA", "TGA", "ATA", "ACA", "AAA", "AGA")
    assert skeleton["punctured_wna"] == ("TTA", "TCA", "TAA", "TGA", "ATA", "AAA", "AGA")
    assert skeleton["punctured_wna_missing"] == "ACA"
    assert skeleton["skeleton_formula_matches_support"] is True
    assert skeleton["punctured_wna_edges"] == (
        ("TTA", "ATA"),
        ("TAA", "AAA"),
        ("TGA", "AGA"),
        ("TTA", "TAA"),
        ("TCA", "TGA"),
        ("ATA", "AAA"),
        ("TTA", "TCA"),
        ("TAA", "TGA"),
        ("AAA", "AGA"),
    )
    assert skeleton["cun_edges"] == (
        ("CTT", "CTA"),
        ("CTC", "CTG"),
        ("CTT", "CTC"),
        ("CTA", "CTG"),
    )
    assert skeleton["bridge_edges"] == (("TTA", "CTA"), ("TAA", "TAG"), ("AGA", "AGG"))
    assert skeleton["leaf_codons"] == ("AGG", "TAG")
    assert skeleton["articulation_codons"] == ("AGA", "CTA", "TAA", "TTA")
    assert skeleton["biconnected_components"] == [
        ("AAA", "AGA", "ATA", "TAA", "TCA", "TGA", "TTA"),
        ("CTA", "CTC", "CTG", "CTT"),
        ("AGA", "AGG"),
        ("CTA", "TTA"),
        ("TAA", "TAG"),
    ]
    assert skeleton["largest_biconnected_component"] == ("AAA", "AGA", "ATA", "TAA", "TCA", "TGA", "TTA")
    assert skeleton["largest_biconnected_component_weight"] == 41
    assert round(skeleton["random_compactness"]["expected_edge_count"], 6) == 7.428571
    assert round(skeleton["random_compactness"]["random_mean_edge_count"], 5) == 7.43122
    assert skeleton["random_compactness"]["trials"] == 100000
    assert skeleton["random_compactness"]["seed"] == 20260522
    assert skeleton["random_compactness"]["exceed_count"] == 19
    assert skeleton["random_compactness"]["p_value"] == 0.00019
    boundary = summary["support_compression"]["boundary_closure"]
    assert boundary["boundary_edge_count"] == 46
    assert boundary["boundary_codon_count"] == 33
    assert boundary["top_boundary_rows"] == [
        {"codon": "TGG", "standard": "W", "boundary_degree": 3, "boundary_pressure": 33, "neighbors": ("AGG", "TAG", "TGA")},
        {"codon": "AAG", "standard": "K", "boundary_degree": 3, "boundary_pressure": 21, "neighbors": ("AAA", "AGG", "TAG")},
        {"codon": "ACA", "standard": "T", "boundary_degree": 3, "boundary_pressure": 14, "neighbors": ("AGA", "ATA", "TCA")},
        {"codon": "TTG", "standard": "L", "boundary_degree": 3, "boundary_pressure": 14, "neighbors": ("CTG", "TAG", "TTA")},
        {"codon": "CAG", "standard": "Q", "boundary_degree": 2, "boundary_pressure": 13, "neighbors": ("CTG", "TAG")},
        {"codon": "CAA", "standard": "Q", "boundary_degree": 2, "boundary_pressure": 9, "neighbors": ("CTA", "TAA")},
        {"codon": "GTA", "standard": "V", "boundary_degree": 2, "boundary_pressure": 6, "neighbors": ("ATA", "CTA")},
        {"codon": "CCA", "standard": "P", "boundary_degree": 2, "boundary_pressure": 2, "neighbors": ("CTA", "TCA")},
        {"codon": "TTT", "standard": "F", "boundary_degree": 2, "boundary_pressure": 2, "neighbors": ("CTT", "TTA")},
    ]
    assert boundary["inactive_envelope_corners"] == ("AAG", "ACA", "TGG")
    assert boundary["q2_completion_face_count"] == 13
    assert boundary["q2_completion_frontier"] == ("AAG", "ACA", "CAA", "CCA", "GTA", "TGG", "TTG", "TTT")
    assert boundary["completion_stages"] == [
        {"stage": 1, "added_count": 8, "added": ("AAG", "ACA", "CAA", "CCA", "GTA", "TGG", "TTG", "TTT"), "total_size": 21},
        {"stage": 2, "added_count": 16, "added": ("ACG", "ATG", "ATT", "CAG", "CAT", "CCG", "CCT", "CGA", "GAA", "GCA", "GTG", "GTT", "TAT", "TCG", "TCT", "TTC"), "total_size": 37},
        {"stage": 3, "added_count": 16, "added": ("AAT", "ACT", "ATC", "CAC", "CCC", "CGG", "CGT", "GAG", "GAT", "GCG", "GCT", "GGA", "GTC", "TAC", "TCC", "TGT"), "total_size": 53},
        {"stage": 4, "added_count": 9, "added": ("AAC", "ACC", "AGT", "CGC", "GAC", "GCC", "GGG", "GGT", "TGC"), "total_size": 62},
        {"stage": 5, "added_count": 2, "added": ("AGC", "GGC"), "total_size": 64},
    ]
    assert boundary["completion_final_size"] == 64
    assert boundary["completion_percolates"] is True
    assert boundary["boundary_class_rows"][:10] == [
        {"class": "W", "boundary_edges": 3, "boundary_pressure": 33, "codons": ("TGG",)},
        {"class": "Q", "boundary_edges": 4, "boundary_pressure": 22, "codons": ("CAA", "CAG")},
        {"class": "T", "boundary_edges": 4, "boundary_pressure": 22, "codons": ("ACA", "ACG")},
        {"class": "K", "boundary_edges": 3, "boundary_pressure": 21, "codons": ("AAG",)},
        {"class": "S", "boundary_edges": 4, "boundary_pressure": 18, "codons": ("AGC", "AGT", "TCG", "TCT")},
        {"class": "Y", "boundary_edges": 2, "boundary_pressure": 18, "codons": ("TAC", "TAT")},
        {"class": "G", "boundary_edges": 2, "boundary_pressure": 16, "codons": ("GGA", "GGG")},
        {"class": "C", "boundary_edges": 1, "boundary_pressure": 15, "codons": ("TGT",)},
        {"class": "R", "boundary_edges": 1, "boundary_pressure": 15, "codons": ("CGA",)},
        {"class": "L", "boundary_edges": 3, "boundary_pressure": 14, "codons": ("TTG",)},
    ]
    closure = summary["support_compression"]["inactive_anchor_closure"]
    assert closure["inactive_anchors"] == ("AAG", "ACA", "TGG")
    assert closure["anchor_closure_size"] == 16
    assert closure["formula_motifs"] == {
        "WNA": ("TTA", "TCA", "TAA", "TGA", "ATA", "ACA", "AAA", "AGA"),
        "WRR": ("TAA", "TAG", "TGA", "TGG", "AAA", "AAG", "AGA", "AGG"),
        "CUN": ("CTT", "CTC", "CTA", "CTG"),
    }
    assert closure["formula_matches_closure"] is True
    assert closure["wna_inter_wrr"] == ("TAA", "TGA", "AAA", "AGA")
    assert closure["wna_inter_wrr_is_wra"] is True
    assert closure["wra_weight"] == 34
    assert closure["active_complex"]["f_vector"] == (13, 16, 4, 0, 0, 0, 0)
    assert closure["active_complex"]["max_dimension"] == 2
    assert closure["active_complex"]["euler_characteristic"] == 1
    assert closure["active_complex"]["boundary_ranks"] == {1: 12, 2: 4, 3: 0, 4: 0, 5: 0, 6: 0}
    assert closure["active_complex"]["betti"] == (1, 0, 0)
    assert closure["closure_complex"]["f_vector"] == (16, 25, 12, 2, 0, 0, 0)
    assert closure["closure_complex"]["max_dimension"] == 3
    assert closure["closure_complex"]["euler_characteristic"] == 1
    assert closure["closure_complex"]["boundary_ranks"] == {1: 15, 2: 10, 3: 2, 4: 0, 5: 0, 6: 0}
    assert closure["closure_complex"]["betti"] == (1, 0, 0, 0)
    assert closure["active_boundary_edge_count"] == 46
    assert closure["closure_boundary_edge_count"] == 46
    assert closure["active_isoperimetric_max_edges"] == 22
    assert closure["closure_isoperimetric_max_edges"] == 32
    assert closure["leaf_degree_change"] == {
        "TAG": {"active_degree": 1, "closure_degree": 3, "closure_neighbors": ("AAG", "TAA", "TGG")},
        "AGG": {"active_degree": 1, "closure_degree": 3, "closure_neighbors": ("AAG", "AGA", "TGG")},
    }
    median = summary["support_compression"]["median_closure"]
    assert median["median_closure_size"] == 20
    assert median["median_closure"] == (
        "AAA", "AAG", "ACA", "ACG", "AGA", "AGG", "ATA", "ATG",
        "CTA", "CTC", "CTG", "CTT", "TAA", "TAG", "TCA", "TCG",
        "TGA", "TGG", "TTA", "TTG",
    )
    assert median["formula_motifs"] == {
        "WNR": (
            "TTA", "TTG", "TCA", "TCG", "TAA", "TAG", "TGA", "TGG",
            "ATA", "ATG", "ACA", "ACG", "AAA", "AAG", "AGA", "AGG",
        ),
        "CUN": ("CTT", "CTC", "CTA", "CTG"),
    }
    assert median["formula_matches_median"] is True
    assert median["added_over_support"] == ("AAG", "ACA", "ACG", "ATG", "TCG", "TGG", "TTG")
    assert median["added_over_anchor_closure"] == ("ACG", "ATG", "TCG", "TTG")
    assert median["wyg"] == ("TTG", "TCG", "ATG", "ACG")
    assert median["added_over_anchor_closure_is_wyg"] is True
    assert median["closure_chain_sizes"] == {
        "support": 13,
        "anchor_closure": 16,
        "median_closure": 20,
        "convex_hull": 64,
    }
    assert median["convex_hull_size"] == 64
    assert median["convex_hull_is_q6"] is True
    assert median["complex"]["f_vector"] == (20, 38, 26, 8, 1, 0, 0)
    assert median["complex"]["max_dimension"] == 4
    assert median["complex"]["euler_characteristic"] == 1
    assert median["complex"]["boundary_ranks"] == {1: 19, 2: 19, 3: 7, 4: 1, 5: 0, 6: 0}
    assert median["complex"]["betti"] == (1, 0, 0, 0, 0)
    assert median["maximal_cells"] == [
        {
            "name": "WNR",
            "dimension": 4,
            "vertices": (
                "TTA", "TTG", "TCA", "TCG", "TAA", "TAG", "TGA", "TGG",
                "ATA", "ATG", "ACA", "ACG", "AAA", "AAG", "AGA", "AGG",
            ),
        },
        {"name": "CUN", "dimension": 2, "vertices": ("CTT", "CTC", "CTA", "CTG")},
        {"name": "YUR", "dimension": 2, "vertices": ("TTA", "TTG", "CTA", "CTG")},
    ]
    assert median["yur"] == ("TTA", "TTG", "CTA", "CTG")
    assert median["yur_inter_wnr"] == ("TTA", "TTG")
    assert median["yur_inter_cun"] == ("CTA", "CTG")
    assert median["boundary_edge_count"] == 44
    sealing = summary["support_compression"]["median_depth_sealing"]
    assert sealing["stage_count"] == 2
    assert sealing["stages"] == [
        {"stage": 1, "added_count": 6, "added": ("AAG", "ACA", "ATG", "TCG", "TGG", "TTG"), "total_size": 19},
        {"stage": 2, "added_count": 1, "added": ("ACG",), "total_size": 20},
    ]
    assert sealing["stage_one_size"] == 19
    assert sealing["stage_one_closure"] == (
        "AAA", "AAG", "ACA", "AGA", "AGG", "ATA", "ATG", "CTA",
        "CTC", "CTG", "CTT", "TAA", "TAG", "TCA", "TCG", "TGA",
        "TGG", "TTA", "TTG",
    )
    assert sealing["stage_one_formula_matches"] is True
    assert sealing["stage_one_missing_from_median"] == ("ACG",)
    assert sealing["stage_one_complex"]["f_vector"] == (19, 34, 20, 4, 0, 0, 0)
    assert sealing["stage_one_complex"]["max_dimension"] == 3
    assert sealing["stage_one_complex"]["euler_characteristic"] == 1
    assert sealing["stage_one_complex"]["boundary_ranks"] == {1: 18, 2: 16, 3: 4, 4: 0, 5: 0, 6: 0}
    assert sealing["stage_one_complex"]["betti"] == (1, 0, 0, 0)
    assert sealing["sealing_corner"] == "ACG"
    assert sealing["sealing_delta_f"] == (1, 4, 6, 4, 1, 0, 0)
    assert sealing["active_one_step_new"] == ("AAG", "ACA", "ATG", "TCG", "TGG", "TTG")
    assert sealing["active_one_step_contains_sealing_corner"] is False
    assert sealing["strict_second_order_points"] == ("ACG",)
    assert sealing["first_step_witnesses"] == [
        {"codon": "ACA", "triple": ("AGA", "ATA", "TCA"), "median": "ACA", "valid": True},
        {"codon": "TGG", "triple": ("AGG", "TAG", "TGA"), "median": "TGG", "valid": True},
        {"codon": "AAG", "triple": ("AAA", "AGG", "TAG"), "median": "AAG", "valid": True},
        {"codon": "ATG", "triple": ("AGG", "ATA", "CTG"), "median": "ATG", "valid": True},
        {"codon": "TCG", "triple": ("AGG", "TCA", "CTC"), "median": "TCG", "valid": True},
        {"codon": "TTG", "triple": ("ATA", "CTG", "TAG"), "median": "TTG", "valid": True},
    ]
    assert sealing["second_step_witness"] == {
        "codon": "ACG",
        "triple": ("TGG", "ATG", "ACA"),
        "median": "ACG",
        "valid": True,
    }
    leakage = summary["support_compression"]["median_leakage"]
    assert leakage["active_triple_count"] == 286
    assert leakage["closed_triple_count"] == 264
    assert leakage["leakage_triple_count"] == 22
    assert leakage["closed_triple_rate"] == 264 / 286
    assert leakage["leakage_triple_rate"] == 22 / 286
    assert leakage["one_step_closure_size"] == 19
    assert leakage["leakage_outputs"] == ("AAG", "ACA", "ATG", "TCG", "TGG", "TTG")
    assert leakage["leakage_output_count"] == 6
    assert leakage["random_comparison"] == {
        "trials": 100000,
        "seed": 20260522,
        "random_mean_closed_triples": 157.49515,
        "random_mean_one_step_closure_size": 43.79654,
        "random_mean_leakage_output_count": 30.79654,
        "closed_triple_exceed_count": 7,
        "closed_triple_p_value": 0.00007,
        "leakage_output_leq_count": 34,
        "leakage_output_p_value": 0.00034,
    }
    assert leakage["median_centrality_rows"] == [
        {"codon": "TTA", "active": True, "median_count": 61},
        {"codon": "TAA", "active": True, "median_count": 46},
        {"codon": "CTA", "active": True, "median_count": 31},
        {"codon": "AAA", "active": True, "median_count": 19},
        {"codon": "TGA", "active": True, "median_count": 19},
        {"codon": "CTG", "active": True, "median_count": 16},
        {"codon": "TAG", "active": True, "median_count": 16},
        {"codon": "AGA", "active": True, "median_count": 14},
        {"codon": "ATA", "active": True, "median_count": 14},
        {"codon": "TCA", "active": True, "median_count": 14},
        {"codon": "CTT", "active": True, "median_count": 8},
        {"codon": "TTG", "active": False, "median_count": 8},
        {"codon": "AAG", "active": False, "median_count": 4},
        {"codon": "TGG", "active": False, "median_count": 4},
        {"codon": "AGG", "active": True, "median_count": 3},
        {"codon": "CTC", "active": True, "median_count": 3},
        {"codon": "ACA", "active": False, "median_count": 2},
        {"codon": "ATG", "active": False, "median_count": 2},
        {"codon": "TCG", "active": False, "median_count": 2},
        {"codon": "ACG", "active": False, "median_count": 0},
    ]
    assert leakage["leakage_output_rows"] == [
        {"codon": "TTG", "median_count": 8},
        {"codon": "AAG", "median_count": 4},
        {"codon": "TGG", "median_count": 4},
        {"codon": "ACA", "median_count": 2},
        {"codon": "ATG", "median_count": 2},
        {"codon": "TCG", "median_count": 2},
    ]
    assert leakage["leakage_catalyst_rows"] == [
        {"codon": "AGG", "leakage_triple_count": 15},
        {"codon": "TAG", "leakage_triple_count": 10},
        {"codon": "CTC", "leakage_triple_count": 8},
        {"codon": "CTG", "leakage_triple_count": 8},
        {"codon": "ATA", "leakage_triple_count": 7},
        {"codon": "TCA", "leakage_triple_count": 7},
        {"codon": "TTA", "leakage_triple_count": 4},
        {"codon": "AAA", "leakage_triple_count": 3},
        {"codon": "TGA", "leakage_triple_count": 3},
        {"codon": "AGA", "leakage_triple_count": 1},
    ]
    assert leakage["minimal_inactive_generator_size"] == 5
    assert leakage["minimal_inactive_generator_count"] == 4
    assert leakage["minimal_inactive_generators"] == [
        ("AGG", "ATA", "CTC", "TAA", "TCA"),
        ("AGG", "ATA", "CTC", "TAG", "TCA"),
        ("AGG", "ATA", "CTG", "TAA", "TCA"),
        ("AGG", "ATA", "CTG", "TAG", "TCA"),
    ]
    assert leakage["inactive_generator_forced_codons"] == ("AGG", "ATA", "TCA")
    assert leakage["acg_second_order_triple_count"] == 12
    assert leakage["acg_second_order_triples"] == (
        ("AAG", "ACA", "TCG"),
        ("ACA", "AGG", "ATG"),
        ("ACA", "AGG", "CTC"),
        ("ACA", "AGG", "CTG"),
        ("ACA", "AGG", "TCG"),
        ("ACA", "AGG", "TTG"),
        ("ACA", "ATG", "TCG"),
        ("ACA", "ATG", "TGG"),
        ("AGA", "ATG", "TCG"),
        ("AGG", "ATA", "TCG"),
        ("AGG", "ATG", "TCA"),
        ("AGG", "ATG", "TCG"),
    )
    robustness = summary["support_compression"]["generator_robustness"]
    assert robustness["minimal_median_generator_size"] == 7
    assert robustness["minimal_median_generator_count"] == 2
    assert robustness["minimal_median_generators"] == [
        ("AGG", "ATA", "CTA", "CTC", "CTT", "TAA", "TCA"),
        ("AGG", "ATA", "CTC", "CTG", "CTT", "TAA", "TCA"),
    ]
    assert robustness["median_forced_generator_codons"] == ("AGG", "ATA", "CTC", "CTT", "TAA", "TCA")
    assert robustness["median_generator_choice_codons"] == ("CTA", "CTG")
    assert robustness["median_essential_codons"] == ("AGG", "ATA", "CTC", "CTT", "TCA")
    assert robustness["median_redundant_codons"] == ("AAA", "AGA", "CTA", "CTG", "TAA", "TAG", "TGA", "TTA")
    assert robustness["median_deletion_rows"] == [
        {"codon": "AAA", "closure_size": 20, "preserves_median": True, "lost": ()},
        {"codon": "AGA", "closure_size": 20, "preserves_median": True, "lost": ()},
        {"codon": "AGG", "closure_size": 14, "preserves_median": False, "lost": ("AAG", "ACG", "AGG", "ATG", "TCG", "TGG")},
        {"codon": "ATA", "closure_size": 16, "preserves_median": False, "lost": ("ACA", "ACG", "ATA", "ATG")},
        {"codon": "CTA", "closure_size": 20, "preserves_median": True, "lost": ()},
        {"codon": "CTC", "closure_size": 19, "preserves_median": False, "lost": ("CTC",)},
        {"codon": "CTG", "closure_size": 20, "preserves_median": True, "lost": ()},
        {"codon": "CTT", "closure_size": 19, "preserves_median": False, "lost": ("CTT",)},
        {"codon": "TAA", "closure_size": 20, "preserves_median": True, "lost": ()},
        {"codon": "TAG", "closure_size": 20, "preserves_median": True, "lost": ()},
        {"codon": "TCA", "closure_size": 16, "preserves_median": False, "lost": ("ACA", "ACG", "TCA", "TCG")},
        {"codon": "TGA", "closure_size": 20, "preserves_median": True, "lost": ()},
        {"codon": "TTA", "closure_size": 20, "preserves_median": True, "lost": ()},
    ]
    assert robustness["complement_pairs"] == (("AGA", "CTC"), ("AGG", "CTT"))
    assert robustness["convex_hull_two_point_witnesses"] == (("AGA", "CTC"), ("AGG", "CTT"))
    assert robustness["q2_single_deletion_all_percolate"] is True
    assert all(row["closure_size"] == 64 and row["percolates"] for row in robustness["q2_single_deletion_rows"])
    assert robustness["minimal_q2_percolating_seed_size"] == 7
    assert robustness["minimal_q2_percolating_seed_count"] == 484
    symmetry = summary["support_compression"]["symmetry_restoration"]
    assert symmetry["automorphism_group_size"] == 46080
    assert symmetry["weight_stabilizer_size"] == 1
    assert symmetry["weight_stabilizer_names"] == ["id"]
    assert symmetry["support_stabilizer_size"] == 2
    assert symmetry["support_stabilizer_names"] == ["id", "swap(s1,f2)"]
    assert symmetry["anchor_stabilizer_size"] == 2
    assert symmetry["anchor_stabilizer_names"] == ["id", "swap(s1,f2)"]
    assert symmetry["stage_one_stabilizer_size"] == 2
    assert symmetry["stage_one_stabilizer_names"] == ["id", "swap(s1,f2)"]
    assert symmetry["median_stabilizer_size"] == 12
    assert symmetry["median_stabilizer_is_s3_times_c2"] is True
    assert symmetry["tau_orbits"] == {
        "support": (
            ("AAA", "TGA"), ("ATA", "TCA"), ("AGA",), ("AGG",), ("CTA",),
            ("CTC",), ("CTG",), ("CTT",), ("TAA",), ("TAG",), ("TTA",),
        ),
        "anchor_closure": (
            ("AAA", "TGA"), ("AAG", "TGG"), ("ATA", "TCA"), ("ACA",),
            ("AGA",), ("AGG",), ("CTA",), ("CTC",), ("CTG",), ("CTT",),
            ("TAA",), ("TAG",), ("TTA",),
        ),
        "stage_one": (
            ("AAA", "TGA"), ("AAG", "TGG"), ("ATA", "TCA"), ("ATG", "TCG"),
            ("ACA",), ("AGA",), ("AGG",), ("CTA",), ("CTC",), ("CTG",),
            ("CTT",), ("TAA",), ("TAG",), ("TTA",), ("TTG",),
        ),
    }
    assert symmetry["median_orbits"] == (
        ("AAA", "AAG", "ACA", "ACG", "TGA", "TGG"),
        ("ATA", "ATG", "TAA", "TAG", "TCA", "TCG"),
        ("AGA", "AGG"),
        ("CTA", "CTG"),
        ("CTC", "CTT"),
        ("TTA", "TTG"),
    )
    assert symmetry["acg_orbit"] == ("AAA", "AAG", "ACA", "ACG", "TGA", "TGG")
    assert symmetry["acg_orbit_missing_from_stage_one"] == ("ACG",)
    assert symmetry["stage_one_is_median_without_acg"] is True
    assert symmetry["symmetry_chain"] == [
        {"object": "weight", "stabilizer_size": 1, "group": "trivial"},
        {"object": "support", "stabilizer_size": 2, "group": "C2"},
        {"object": "anchor_closure", "stabilizer_size": 2, "group": "C2"},
        {"object": "median_stage_one", "stabilizer_size": 2, "group": "C2"},
        {"object": "median_closure", "stabilizer_size": 12, "group": "S3 x C2"},
    ]
    assert symmetry["tau_weight_violation"] == {
        "left": "TGA",
        "right": "AAA",
        "left_weight": 15,
        "right_weight": 3,
    }
    quotient = summary["support_compression"]["quotient_dynamics"]
    assert quotient["orbit_rows"] == [
        {
            "index": 0,
            "name": "Anchor6",
            "codons": ("AAA", "AAG", "ACA", "ACG", "TGA", "TGG"),
            "size": 6,
            "active_codons": ("AAA", "TGA"),
            "inactive_codons": ("AAG", "ACA", "ACG", "TGG"),
            "weight": 18,
        },
        {
            "index": 1,
            "name": "StopStart6",
            "codons": ("ATA", "ATG", "TAA", "TAG", "TCA", "TCG"),
            "size": 6,
            "active_codons": ("ATA", "TAA", "TAG", "TCA"),
            "inactive_codons": ("ATG", "TCG"),
            "weight": 24,
        },
        {"index": 2, "name": "AGR", "codons": ("AGA", "AGG"), "size": 2, "active_codons": ("AGA", "AGG"), "inactive_codons": (), "weight": 16},
        {"index": 3, "name": "UUR", "codons": ("TTA", "TTG"), "size": 2, "active_codons": ("TTA",), "inactive_codons": ("TTG",), "weight": 1},
        {"index": 4, "name": "CUR", "codons": ("CTA", "CTG"), "size": 2, "active_codons": ("CTA", "CTG"), "inactive_codons": (), "weight": 4},
        {"index": 5, "name": "CUY", "codons": ("CTC", "CTT"), "size": 2, "active_codons": ("CTC", "CTT"), "inactive_codons": (), "weight": 2},
    ]
    assert quotient["orbit_adjacency_matrix"] == (
        (3, 12, 6, 0, 0, 0),
        (12, 3, 0, 6, 0, 0),
        (6, 0, 1, 0, 0, 0),
        (0, 6, 0, 1, 2, 0),
        (0, 0, 0, 2, 1, 2),
        (0, 0, 0, 0, 2, 1),
    )
    assert quotient["orbit_cross_edges"] == (
        {"left": "Anchor6", "right": "StopStart6", "weight": 12},
        {"left": "Anchor6", "right": "AGR", "weight": 6},
        {"left": "StopStart6", "right": "UUR", "weight": 6},
        {"left": "UUR", "right": "CUR", "weight": 2},
        {"left": "CUR", "right": "CUY", "weight": 2},
    )
    assert quotient["quotient_path"] == ("AGR", "Anchor6", "StopStart6", "UUR", "CUR", "CUY")
    assert quotient["median_edge_count"] == 38
    assert quotient["inactive_layer"] == ("AAG", "ACA", "ACG", "ATG", "TCG", "TGG", "TTG")
    assert quotient["inactive_layer_formula_matches"] is True
    assert quotient["inactive_edges"] == (
        ("TTG", "ATG"),
        ("TCG", "ACG"),
        ("TCG", "TGG"),
        ("ATG", "AAG"),
        ("TTG", "TCG"),
        ("ATG", "ACG"),
        ("ACA", "ACG"),
    )
    assert quotient["inactive_complex"]["f_vector"] == (7, 7, 1, 0, 0, 0, 0)
    assert quotient["inactive_complex"]["betti"] == (1, 0, 0)
    assert quotient["active_inactive_edge_count"] == 15
    assert quotient["inactive_interface_rows"] == [
        {"inactive_codon": "AAG", "active_neighbors": ("AAA", "AGG", "TAG"), "interface_degree": 3},
        {"inactive_codon": "ACA", "active_neighbors": ("AGA", "ATA", "TCA"), "interface_degree": 3},
        {"inactive_codon": "ACG", "active_neighbors": ("AGG",), "interface_degree": 1},
        {"inactive_codon": "ATG", "active_neighbors": ("ATA",), "interface_degree": 1},
        {"inactive_codon": "TCG", "active_neighbors": ("TCA",), "interface_degree": 1},
        {"inactive_codon": "TGG", "active_neighbors": ("AGG", "TAG", "TGA"), "interface_degree": 3},
        {"inactive_codon": "TTG", "active_neighbors": ("CTG", "TAG", "TTA"), "interface_degree": 3},
    ]
    assert quotient["active_interface_rows"][:9] == [
        {"active_codon": "AGG", "inactive_neighbors": ("AAG", "ACG", "TGG"), "interface_degree": 3},
        {"active_codon": "TAG", "inactive_neighbors": ("AAG", "TGG", "TTG"), "interface_degree": 3},
        {"active_codon": "ATA", "inactive_neighbors": ("ACA", "ATG"), "interface_degree": 2},
        {"active_codon": "TCA", "inactive_neighbors": ("ACA", "TCG"), "interface_degree": 2},
        {"active_codon": "AAA", "inactive_neighbors": ("AAG",), "interface_degree": 1},
        {"active_codon": "AGA", "inactive_neighbors": ("ACA",), "interface_degree": 1},
        {"active_codon": "CTG", "inactive_neighbors": ("TTG",), "interface_degree": 1},
        {"active_codon": "TGA", "inactive_neighbors": ("TGG",), "interface_degree": 1},
        {"active_codon": "TTA", "inactive_neighbors": ("TTG",), "interface_degree": 1},
    ]
    assert quotient["active_interface_gates"] == ("AGG", "TAG")
    assert quotient["acg_local_neighbors"] == {
        "inactive_neighbors": ("ACA", "ATG", "TCG"),
        "active_neighbors": ("AGG",),
    }
    dynamics = summary["support_compression"]["quotient_leakage_dynamics"]
    assert dynamics["state_order"] == ("AGR", "Anchor6", "StopStart6", "UUR", "CUR", "CUY")
    assert dynamics["transition_matrix"] == (
        ("1/6", "1/2", "0", "0", "0", "0"),
        ("1/6", "1/6", "1/3", "0", "0", "0"),
        ("0", "1/3", "1/6", "1/6", "0", "0"),
        ("0", "0", "1/2", "1/6", "1/6", "0"),
        ("0", "0", "0", "1/6", "1/6", "1/6"),
        ("0", "0", "0", "0", "1/6", "1/6"),
    )
    assert dynamics["outside_probabilities"] == ("1/3", "1/3", "1/3", "1/6", "1/2", "2/3")
    assert dynamics["self_retention_probabilities"] == ("1/6", "1/6", "1/6", "1/6", "1/6", "1/6")
    assert dynamics["expected_exit_times"] == (
        "1478/487",
        "4468/1461",
        "4570/1461",
        "1716/487",
        "1088/487",
        "802/487",
    )
    assert tuple(round(value, 3) for value in dynamics["expected_exit_times_float"]) == (
        3.035,
        3.058,
        3.128,
        3.524,
        2.234,
        1.647,
    )
    assert dynamics["closure_retention_rows"] == [
        {"name": "support", "vertices": 13, "internal_edges": 16, "boundary_half_edges": 46, "retention": "16/39", "retention_float": 16 / 39},
        {"name": "anchor_closure", "vertices": 16, "internal_edges": 25, "boundary_half_edges": 46, "retention": "25/48", "retention_float": 25 / 48},
        {"name": "median_stage_one", "vertices": 19, "internal_edges": 34, "boundary_half_edges": 46, "retention": "34/57", "retention_float": 34 / 57},
        {"name": "median_closure", "vertices": 20, "internal_edges": 38, "boundary_half_edges": 44, "retention": "19/30", "retention_float": 19 / 30},
    ]
    assert dynamics["acg_stage_one_neighbors"] == ("ACA", "AGG", "ATG", "TCG")
    assert dynamics["acg_stage_one_neighbor_count"] == 4
    assert dynamics["acg_boundary_delta"] == -2
    assert dynamics["boundary_before_acg"] == 46
    assert dynamics["boundary_after_acg"] == 44
    spectral = summary["support_compression"]["spectral_stabilization"]
    assert [
        (
            row["name"],
            row["vertices"],
            row["internal_edges"],
            row["retention"],
            round(row["spectral_radius"], 4),
            round(row["quasi_lifetime"], 3),
        )
        for row in spectral["closure_spectral_rows"]
    ] == [
        ("support", 13, 16, "16/39", 0.4759, 1.908),
        ("anchor_closure", 16, 25, "25/48", 0.5733, 2.344),
        ("median_stage_one", 19, 34, "34/57", 0.6422, 2.795),
        ("median_closure", 20, 38, "19/30", 0.6752, 3.079),
    ]
    assert round(spectral["median_spectral_radius"], 7) == 0.6752479
    assert round(spectral["median_quasi_lifetime"], 3) == 3.079
    assert [
        (row["state"], round(row["mass"], 4))
        for row in spectral["qsd_rows"]
    ] == [
        ("AGR", 0.1117),
        ("Anchor6", 0.3407),
        ("StopStart6", 0.3524),
        ("UUR", 0.1313),
        ("CUR", 0.0482),
        ("CUY", 0.0158),
    ]
    assert round(spectral["anchor_stopstart_qsd_mass"], 4) == 0.6931
    assert [
        (row["state"], round(row["potential"], 4))
        for row in spectral["survival_potential_rows"]
    ] == [
        ("AGR", 0.8506),
        ("Anchor6", 0.8652),
        ("StopStart6", 0.8948),
        ("UUR", 1.0),
        ("CUR", 0.3671),
        ("CUY", 0.1203),
    ]
    assert spectral["highest_survival_potential_state"] == "UUR"
    assert [
        (row["state"], round(row["conditional_probability"], 4))
        for row in spectral["exit_prestates"]
    ] == [
        ("AGR", 0.1146),
        ("Anchor6", 0.3497),
        ("StopStart6", 0.3617),
        ("UUR", 0.0674),
        ("CUR", 0.0742),
        ("CUY", 0.0324),
    ]
    assert round(spectral["anchor_stopstart_exit_share"], 4) == 0.7114
    assert [
        (row["class"], round(row["probability"], 4))
        for row in spectral["outside_target_rows"]
    ] == [
        ("S", 0.1176),
        ("P", 0.0931),
        ("V", 0.0931),
        ("Q", 0.085),
        ("F", 0.0755),
        ("I", 0.0603),
        ("Y", 0.0603),
        ("A", 0.0583),
        ("C", 0.0583),
        ("E", 0.0583),
        ("N", 0.0583),
        ("R", 0.0583),
        ("T", 0.0583),
        ("G", 0.0573),
        ("H", 0.0081),
    ]
    first_exit = spectral["first_exit_channels"]
    assert [
        (row["state"], round(row["conditional_probability"], 4))
        for row in first_exit["origin_rows"]
    ] == [
        ("AGR", 0.1146),
        ("Anchor6", 0.3497),
        ("StopStart6", 0.3617),
        ("UUR", 0.0674),
        ("CUR", 0.0742),
        ("CUY", 0.0324),
    ]
    assert round(first_exit["anchor_stopstart_origin_share"], 4) == 0.7114
    assert round(first_exit["cun_tail_origin_share"], 4) == 0.1066
    assert [
        (row["bit"], round(row["probability"], 4))
        for row in first_exit["exit_bit_rows"]
    ] == [
        ("s3", 0.4804),
        ("f1", 0.4211),
        ("f2", 0.0328),
        ("s1", 0.0328),
        ("s2", 0.0328),
        ("f3", 0.0),
    ]
    assert round(first_exit["gate_axis_exit_share"], 4) == 0.9015
    assert first_exit["f3_exit_probability"] == 0.0
    assert [
        (
            row["state"],
            round(row["s1"], 4),
            round(row["f1"], 4),
            round(row["s2"], 4),
            round(row["f2"], 4),
            round(row["s3"], 4),
            round(row["f3"], 4),
        )
        for row in first_exit["eventual_exit_bit_rows"]
    ] == [
        ("AGR", 0.0041, 0.4860, 0.0041, 0.0041, 0.5017, 0.0),
        ("Anchor6", 0.0068, 0.4766, 0.0068, 0.0068, 0.5029, 0.0),
        ("StopStart6", 0.0151, 0.4486, 0.0151, 0.0151, 0.5063, 0.0),
        ("UUR", 0.0616, 0.2895, 0.0616, 0.0616, 0.5257, 0.0),
        ("CUR", 0.2628, 0.1020, 0.2628, 0.2628, 0.1095, 0.0),
        ("CUY", 0.2526, 0.2204, 0.2526, 0.2526, 0.0219, 0.0),
    ]
    assert first_exit["has_stop_target"] is False
    assert [
        (row["codon"], row["class"], round(row["probability"], 4))
        for row in first_exit["top_outside_target_codon_rows"]
    ] == [
        ("CAA", "Q", 0.0425),
        ("CAG", "Q", 0.0425),
        ("CCA", "P", 0.0425),
        ("CCG", "P", 0.0425),
        ("GTA", "V", 0.0425),
        ("GTG", "V", 0.0425),
        ("TTC", "F", 0.0377),
        ("TTT", "F", 0.0377),
        ("ATC", "I", 0.0301),
        ("ATT", "I", 0.0301),
        ("TAC", "Y", 0.0301),
        ("TAT", "Y", 0.0301),
        ("TCC", "S", 0.0301),
        ("TCT", "S", 0.0301),
    ]
    gate_shell = spectral["post_median_gate_shell"]
    assert gate_shell["gate_shell"] == ("CAA", "CAG", "CCA", "CCG", "GTA", "GTG")
    assert gate_shell["single_point_candidate_count"] == 44
    assert [
        (row["codon"], row["class"], round(row["spectral_radius"], 9), round(row["gain"], 9))
        for row in gate_shell["best_single_rows"]
    ] == [
        ("CAA", "Q", 0.681004866, 0.005756935),
        ("CAG", "Q", 0.681004866, 0.005756935),
        ("CCA", "P", 0.681004866, 0.005756935),
        ("CCG", "P", 0.681004866, 0.005756935),
        ("GTA", "V", 0.681004866, 0.005756935),
        ("GTG", "V", 0.681004866, 0.005756935),
    ]
    assert gate_shell["external_gamma_orbit_count"] == 10
    assert gate_shell["best_orbit"]["orbit"] == ("CAA", "CAG", "CCA", "CCG", "GTA", "GTG")
    assert gate_shell["best_orbit"]["size"] == 6
    assert round(gate_shell["best_orbit"]["spectral_radius"], 9) == 0.727773877
    assert round(gate_shell["best_orbit"]["gain"], 9) == 0.052525946
    assert [
        (row["pair"], round(row["spectral_radius"], 9), round(row["gain"], 9))
        for row in gate_shell["best_f3_pair_rows"]
    ] == [
        (("CAA", "CAG"), 0.691331504, 0.016083573),
        (("CCA", "CCG"), 0.691331504, 0.016083573),
        (("GTA", "GTG"), 0.691331504, 0.016083573),
    ]
    assert gate_shell["post_median_vertices"] == 26
    assert gate_shell["post_median_internal_edges"] == 53
    assert gate_shell["post_median_retention"] == "53/78"
    assert round(gate_shell["post_median_retention_float"], 6) == 0.679487
    assert round(gate_shell["post_median_spectral_radius"], 9) == 0.727773877
    assert round(gate_shell["post_median_spectral_gain"], 9) == 0.052525946
    assert round(gate_shell["leakage_before"]["CUR"], 6) == 0.5
    assert gate_shell["leakage_after"]["CUR"] == 0.0
    assert gate_shell["stopstart_gate_edges"] == 6
    assert gate_shell["gate_cur_edges"] == 6
    assert gate_shell["cur_neighbors_after"] == {
        "CTA": ("CAA", "CCA", "CTG", "CTT", "GTA", "TTA"),
        "CTG": ("CAG", "CCG", "CTA", "CTC", "GTG", "TTG"),
    }
    antipodal = spectral["antipodal_trigger"]
    assert antipodal["mstar_size"] == 34
    assert antipodal["mstar_is_median_closed"] is True
    assert antipodal["mstar_closure_stage_count"] == 0
    assert [
        (row["shell"], row["size"])
        for row in antipodal["y_shell_rows"]
    ] == [
        ("H0", 2),
        ("H1", 8),
        ("H2", 12),
        ("H3", 8),
        ("H4", 2),
    ]
    assert [
        (
            row["shell"],
            row["start_size"],
            row["closure_size"],
            tuple(stage["added_count"] for stage in row["stage_additions"]),
        )
        for row in antipodal["shell_trigger_rows"]
    ] == [
        ("H1", 42, 64, (12, 10)),
        ("H2", 46, 64, (18,)),
        ("H3", 42, 64, (22,)),
        ("H4", 36, 64, (28,)),
    ]
    assert [
        (row["codon"], row["closure_size"], row["stage_count"], tuple(stage["added_count"] for stage in row["stage_additions"]))
        for row in antipodal["single_antipode_rows"]
    ] == [
        ("AGC", 64, 1, (29,)),
        ("AGT", 64, 1, (29,)),
    ]
    assert [
        (row["shell"], row["median_closure_size"], round(row["spectral_radius"], 6))
        for row in antipodal["single_trigger_rows"]
    ] == [
        ("H1", 36, 0.837956),
        ("H2", 40, 0.837179),
        ("H3", 48, 0.837165),
        ("H4", 64, 0.837156),
    ]
    assert [
        (row["level"], row["size"], row["structure"], round(row["spectral_radius"], 6), round(row["retention_float"], 6))
        for row in antipodal["shell_filling_rows"]
    ] == [
        ("S0", 34, "NNR+H0", 0.836111, 0.813725),
        ("S1", 42, "+H1", 0.859128, 0.81746),
        ("S2", 54, "+H2", 0.921172, 0.895062),
        ("S3", 62, "+H3", 0.978349, 0.973118),
        ("S4", 64, "+H4", 1.0, 1.0),
    ]
    assert antipodal["anchor_subcube_formula_verified"] is True
    assert [
        (row["span_dimension"], row["closure_size"])
        for row in antipodal["span_size_rows"]
    ] == [
        (0, 34),
        (1, 36),
        (2, 40),
        (3, 48),
        (4, 64),
    ]
    assert [
        (row["shell"], row["shell_size"], row["span_dimension"], row["closure_size"])
        for row in antipodal["single_span_rows"]
    ] == [
        ("H1", 8, 1, 36),
        ("H2", 12, 2, 40),
        ("H3", 8, 3, 48),
        ("H4", 2, 4, 64),
    ]
    assert [
        (row["added_size"], row["candidate_count"], row["closure_size_counts"])
        for row in antipodal["trigger_count_rows"]
    ] == [
        (1, 30, {36: 8, 40: 12, 48: 8, 64: 2}),
        (2, 435, {36: 4, 40: 78, 48: 196, 64: 157}),
        (3, 4060, {40: 120, 48: 1216, 64: 2724}),
        (4, 27405, {40: 90, 48: 3824, 64: 23491}),
    ]
    assert antipodal["agy_support"] == ("f1", "f2", "s1", "s2")
    assert len(antipodal["support_pattern_verification_rows"]) == 15
    assert all(row["matches_formula"] for row in antipodal["support_pattern_verification_rows"])
    assert antipodal["coverage_closure_formula_verified"] is True
    assert antipodal["coverage_closure_lattice_verified"] is True
    assert [
        (
            row["rank"],
            row["external_closure_size"],
            row["external_closure_formula_size"],
            row["median_closure_size"],
        )
        for row in antipodal["coverage_closure_rows"]
        if row["support"] in ((), ("s1",), ("s1", "f1"), ("s1", "f1", "s2"), ("s1", "f1", "s2", "f2"))
    ] == [
        (0, 0, 0, 34),
        (1, 2, 2, 36),
        (2, 6, 6, 40),
        (3, 14, 14, 48),
        (4, 30, 30, 64),
    ]
    assert antipodal["coverage_rank_coordinates"] == ("s1", "f1", "s2", "f2")
    assert antipodal["coverage_rank_is_submodular_formula"] == "r(B)=sum_i 1[i in J(B)]"
    assert antipodal["coverage_rank_singleton_witnesses"] == ("AGC", "AGT")
    assert antipodal["boolean_lattice_closure_count"] == 16
    assert antipodal["boolean_lattice_intersection_verified"] is True
    assert antipodal["boolean_lattice_median_join_verified"] is True
    assert [
        (
            row["rank"],
            row["closure_size"],
            row["f_vector"],
            round(row["spectral_radius"], 6),
            row["f_vector_matches_formula"],
        )
        for row in antipodal["boolean_lattice_rank_rows"]
    ] == [
        (0, 34, (34, 83, 81, 40, 10, 1), 0.836111, True),
        (1, 36, (36, 88, 85, 41, 10, 1), 0.840912, True),
        (2, 40, (40, 100, 98, 47, 11, 1), 0.855963, True),
        (3, 48, (48, 128, 136, 72, 19, 2), 0.902369, True),
        (4, 64, (64, 192, 240, 160, 60, 12, 1), 1.0, True),
    ]
    assert [
        (
            row["rank"],
            row["equation"],
            round(row["mu"], 6),
            round(row["lambda_from_mu"], 6),
            row["lambda_matches_rank_radius"],
        )
        for row in antipodal["quotient_spectrum_rows"]
    ] == [
        (0, "mu^6 - 21 mu^4 + 80 mu^2 - 24 = 0", 4.016667, 0.836111, True),
        (1, "mu^4 - 4 mu^3 - 5 mu^2 + 18 mu + 6 = 0", 4.045475, 0.840912, True),
        (2, "mu^4 - 8 mu^3 + 19 mu^2 - 12 mu - 2 = 0", 4.135779, 0.855963, True),
        (3, "mu^2 - 6 mu + 7 = 0", 4.414214, 0.902369, True),
        (4, "mu - 5 = 0", 5.0, 1.0, True),
    ]
    assert [
        (
            row["added_size"],
            row["candidate_count"],
            row["rank_counts"],
            row["full_cube_count"],
            round(row["full_cube_probability"], 4),
            row["counts_sum_to_candidate_count"],
        )
        for row in antipodal["rank_distribution_rows"]
    ] == [
        (1, 30, {1: 8, 2: 12, 3: 8, 4: 2}, 2, 0.0667, True),
        (2, 435, {1: 4, 2: 78, 3: 196, 4: 157}, 157, 0.3609, True),
        (3, 4060, {1: 0, 2: 120, 3: 1216, 4: 2724}, 2724, 0.6709, True),
        (4, 27405, {1: 0, 2: 90, 3: 3824, 4: 23491}, 23491, 0.8572, True),
        (5, 142506, {1: 0, 2: 36, 3: 7936, 4: 134534}, 134534, 0.9441, True),
        (6, 593775, {1: 0, 2: 6, 3: 12000, 4: 581769}, 581769, 0.9798, True),
    ]
    assert antipodal["trigger_count_formula_matches_enumeration"] is True
    assert [
        (row["added_size"], row["full_trigger_count"], round(row["full_trigger_probability"], 4))
        for row in antipodal["random_trigger_probability_rows"]
    ] == [
        (1, 2, 0.0667),
        (2, 157, 0.3609),
        (3, 2724, 0.6709),
        (4, 23491, 0.8572),
        (5, 134534, 0.9441),
        (6, 581769, 0.9798),
        (7, 2022072, 0.9933),
        (8, 5840913, 0.9979),
        (9, 14299142, 0.9994),
        (10, 30041011, 0.9999),
    ]
    assert [
        (row["trigger_time"], round(row["probability"], 4), round(row["hazard"], 4))
        for row in antipodal["trigger_time_rows"]
    ] == [
        (1, 0.0667, 0.0667),
        (2, 0.2943, 0.3153),
        (3, 0.31, 0.4851),
        (4, 0.1862, 0.566),
        (5, 0.0869, 0.6083),
        (6, 0.0357, 0.6386),
        (7, 0.0135, 0.6665),
        (8, 0.0047, 0.6957),
        (9, 0.0015, 0.7273),
        (10, 0.0004, 0.7619),
    ]
    assert round(antipodal["expected_trigger_time"], 5) == 3.12998
    assert [
        (row["quantile"], row["threshold"])
        for row in antipodal["trigger_quantile_rows"]
    ] == [
        (0.5, 3),
        (0.9, 5),
        (0.95, 6),
        (0.99, 7),
    ]
    assert [
        (row["added_size"], round(row["expected_rank"], 4), round(row["formula_value"], 4))
        for row in antipodal["expected_rank_rows"]
    ] == [
        (1, 2.1333, 2.1333),
        (2, 3.1632, 3.1632),
        (3, 3.6414, 3.6414),
        (4, 3.8539, 3.8539),
        (5, 3.9438, 3.9438),
        (6, 3.9798, 3.9798),
        (7, 3.9933, 3.9933),
    ]
    assert [
        (row["added_size"], round(row["expected_closure_size"], 3))
        for row in antipodal["expected_closure_rows"]
    ] == [
        (0, 34.0),
        (1, 42.667),
        (2, 52.23),
        (3, 58.499),
        (4, 61.689),
        (5, 63.103),
        (6, 63.676),
        (7, 63.892),
        (8, 63.967),
        (9, 63.991),
        (10, 63.998),
    ]
    assert [
        (row["added_size"], round(row["expected_spectral_radius"], 6))
        for row in antipodal["expected_spectral_rows"]
    ] == [
        (0, 0.836111),
        (1, 0.873927),
        (2, 0.92872),
        (3, 0.966502),
        (4, 0.985904),
        (5, 0.994527),
        (6, 0.998025),
        (7, 0.999342),
        (8, 0.9998),
        (9, 0.999945),
        (10, 0.999987),
    ]
    assert [
        (
            row["state"],
            {rank: round(probability, 4) for rank, probability in row["transitions"].items()},
            round(row["direct_trigger_probability"], 4),
            round(row["expected_rank_increment"], 4),
            round(row["drift_formula_value"], 4),
            round(row["probability_sum"], 4),
        )
        for row in antipodal["markov_transition_state_rows"]
    ] == [
        ((0, 0), {1: 0.2667, 2: 0.4, 3: 0.2667, 4: 0.0667}, 0.0667, 2.1333, 2.1333, 1.0),
        ((1, 1), {1: 0.0345, 2: 0.4138, 3: 0.4138, 4: 0.1379}, 0.1379, 1.6552, 1.6552, 1.0),
        ((1, 2), {2: 0.1724, 3: 0.5517, 4: 0.2759}, 0.2759, 1.1034, 1.1034, 1.0),
        ((1, 3), {3: 0.4483, 4: 0.5517}, 0.5517, 0.5517, 0.5517, 1.0),
        ((2, 2), {2: 0.1429, 3: 0.5714, 4: 0.2857}, 0.2857, 1.1429, 1.1429, 1.0),
        ((3, 3), {3: 0.4074, 4: 0.5926}, 0.5926, 0.5926, 0.5926, 1.0),
        ((6, 3), {3: 0.3333, 4: 0.6667}, 0.6667, 0.6667, 0.6667, 1.0),
    ]
    assert round(antipodal["markov_expected_trigger_time"], 5) == 3.12998
    assert round(antipodal["trigger_time_variance"], 5) == 1.81588
    assert round(antipodal["trigger_time_standard_deviation"], 5) == 1.34755
    assert [
        (row["state"], round(row["expected_remaining_steps"], 3))
        for row in antipodal["markov_remaining_time_rows"]
    ] == [
        ((0, 0), 3.13),
        ((1, 1), 2.729),
        ((1, 2), 2.329),
        ((1, 3), 1.765),
        ((2, 1), 2.638),
        ((2, 2), 2.252),
        ((2, 3), 1.706),
        ((3, 2), 2.174),
        ((3, 3), 1.647),
        ((6, 2), 1.941),
        ((6, 3), 1.471),
    ]
    assert antipodal["blocker_vertex_count"] == 28
    assert [
        (row["missing_coordinate"], row["motif"], row["size"])
        for row in antipodal["blocker_coordinate_rows"]
    ] == [
        ("s1", "YNY", 14),
        ("f1", "SNY", 14),
        ("s2", "NYY", 14),
        ("f2", "NWY", 14),
    ]
    assert [
        (row["missing_coordinate_count"], row["intersection_sizes"], row["formula_size"])
        for row in antipodal["blocker_intersection_rows"]
    ] == [
        (1, (14, 14, 14, 14), 14),
        (2, (6, 6, 6, 6, 6, 6), 6),
        (3, (2, 2, 2, 2), 2),
        (4, (0,), 0),
    ]
    assert antipodal["blocker_nerve"] == {
        "edge_count": 6,
        "is_tetrahedron_boundary": True,
        "tetrahedron_count": 0,
        "triangle_count": 4,
        "vertex_count": 4,
    }
    assert antipodal["blocker_f_vector"] == (
        28,
        278,
        1336,
        3914,
        7972,
        12006,
        13728,
        12012,
        8008,
        4004,
        1456,
        364,
        56,
        4,
    )
    assert antipodal["blocker_independence_polynomial"] == "4(1+t)^14 - 6(1+t)^6 + 4(1+t)^2 - 1"
    assert antipodal["blocker_independence_coefficients"] == (
        1,
        28,
        278,
        1336,
        3914,
        7972,
        12006,
        13728,
        12012,
        8008,
        4004,
        1456,
        364,
        56,
        4,
    )
    assert antipodal["blocker_dimension"] == 13
    assert antipodal["stanley_reisner_dimension"] == 14
    assert [
        (
            row["intersection_kind"],
            row["vertex_count"],
            row["simplex_dimension"],
            row["multiplicity"],
        )
        for row in antipodal["thickened_sphere_rows"]
    ] == [
        ("facet", 14, 13, 4),
        ("pair", 6, 5, 6),
        ("triple", 2, 1, 4),
        ("quadruple", 0, -1, 1),
    ]
    assert antipodal["blocker_hilbert_series"] == (
        "4/(1-z)^14 - 6/(1-z)^6 + 4/(1-z)^2 - 1"
    )
    assert antipodal["blocker_h_polynomial"] == (
        "4 - 6(1-z)^8 + 4(1-z)^12 - (1-z)^14"
    )
    assert antipodal["blocker_h_vector"] == (
        1,
        14,
        5,
        -180,
        559,
        -830,
        525,
        312,
        -1029,
        1122,
        -737,
        316,
        -87,
        14,
        -1,
    )
    assert antipodal["blocker_is_cohen_macaulay"] is False
    assert antipodal["blocker_non_cm_witness"] == {
        "complex_dimension": 13,
        "homology_degree": 2,
        "reduced_homology_rank": 1,
    }
    assert antipodal["blocker_projective_dimension"] == 27
    assert antipodal["blocker_depth"] == 3
    assert antipodal["blocker_regularity"] == 3
    assert antipodal["blocker_cohen_macaulay_defect"] == 11
    assert antipodal["blocker_hochster_witness"] == {
        "betti_i": 27,
        "betti_j": 30,
        "homology_degree": 2,
        "betti_value": 1,
    }
    assert [
        (
            row["support_rank"],
            row["saturated_face_count"],
            row["saturated_face_sizes"],
            row["link_coordinate_count"],
            row["link_lift_count"],
            row["link_sphere_dimension"],
        )
        for row in antipodal["local_link_stratification_rows"]
    ] == [
        (0, 1, (0,), 4, 2, 2),
        (1, 4, (2,), 3, 4, 1),
        (2, 6, (6,), 2, 8, 0),
        (3, 4, (14,), 1, 16, -1),
    ]
    assert antipodal["local_link_examples"] == {
        "unit_s1_face": ("GTC", "GTT"),
        "unit_s1_link_sphere_dimension": 1,
        "first_base_face": ("ATC", "ATT", "GTC", "GTT", "TTC", "TTT"),
        "first_base_link_sphere_dimension": 0,
    }
    assert antipodal["local_link_non_saturated_links_are_cones"] is True
    assert antipodal["blocker_is_buchsbaum"] is False
    assert antipodal["blocker_buchsbaum_obstruction"] == {
        "face_support_rank": 1,
        "link_complex_dimension": 11,
        "link_homology_dimension": 1,
    }
    assert antipodal["hochster_nerve_vertex_count"] == 4
    assert antipodal["hochster_possible_homology_degrees"] == (-1, 0, 1, 2)
    assert antipodal["hochster_betti_diagonals"] == (0, 1, 2, 3)
    assert antipodal["top_betti_strand_generating_function"] == "(2x+x^2)^4(1+x)^22"
    assert [
        (row["j"], row["i"], row["betti"])
        for row in antipodal["top_betti_strand_rows"]
    ] == [
        (4, 1, 16),
        (5, 2, 384),
        (6, 3, 4424),
        (7, 4, 32568),
        (8, 5, 172041),
        (9, 6, 694254),
        (10, 7, 2224607),
        (11, 8, 5808396),
        (12, 9, 12582427),
        (13, 10, 22907654),
        (14, 11, 35377221),
        (15, 12, 46646368),
        (16, 13, 52738794),
        (17, 14, 51252348),
        (18, 15, 42843366),
        (19, 16, 30778024),
        (20, 17, 18951702),
        (21, 18, 9957596),
        (22, 19, 4434562),
        (23, 20, 1658184),
        (24, 21, 513821),
        (25, 22, 129558),
        (26, 23, 25899),
        (27, 24, 3948),
        (28, 25, 431),
        (29, 26, 30),
        (30, 27, 1),
    ]
    assert [
        (row["diagonal"], row["homology_degree"], row["nonzero_count"])
        for row in antipodal["betti_table_diagonal_rows"]
    ] == [
        (0, -1, 3),
        (1, 0, 17),
        (2, 1, 24),
        (3, 2, 27),
    ]
    assert antipodal["hochster_diagonal_generating_functions"] == {
        -1: "(1+x)^2",
        0: "x^2(x+1)^2(x+2)^2P0(x)",
        1: "x^3(x+1)^10(x+2)^3P1(x)",
        2: "x^4(x+1)^22(x+2)^4",
    }
    assert antipodal["support_lift_substitution"] == "z=(1+x)^2-1=2x+x^2"
    assert antipodal["support_level_betti_generating_functions"] == {
        -1: "1+z",
        0: "z^2(1+z)(4z^6+28z^5+87z^4+152z^3+157z^2+92z+25)",
        1: "z^3(1+z)^5(6z^5+38z^4+99z^3+132z^2+89z+22)",
        2: "z^4(1+z)^11",
    }
    assert [
        (
            row["homology_degree"],
            tuple((degree, coefficient) for degree, coefficient in enumerate(row["coefficients"]) if coefficient),
            row["nonzero_count"],
            row["total_support_mass"],
        )
        for row in antipodal["support_level_betti_rows"]
    ] == [
        (-1, ((0, 1), (1, 1)), 2, 2),
        (
            0,
            (
                (2, 25),
                (3, 117),
                (4, 249),
                (5, 309),
                (6, 239),
                (7, 115),
                (8, 32),
                (9, 4),
            ),
            8,
            1090,
        ),
        (
            1,
            (
                (3, 22),
                (4, 199),
                (5, 797),
                (6, 1869),
                (7, 2853),
                (8, 2973),
                (9, 2149),
                (10, 1067),
                (11, 349),
                (12, 68),
                (13, 6),
            ),
            11,
            12352,
        ),
        (
            2,
            (
                (4, 1),
                (5, 11),
                (6, 55),
                (7, 165),
                (8, 330),
                (9, 462),
                (10, 462),
                (11, 330),
                (12, 165),
                (13, 55),
                (14, 11),
                (15, 1),
            ),
            12,
            2048,
        ),
    ]
    assert antipodal["support_nerve_census_total"] == 32768
    assert antipodal["support_nerve_contractible_count"] == 18680
    assert antipodal["support_nerve_h2_count"] == 2048
    assert [
        (row["signature"], row["support_family_count"])
        for row in antipodal["support_nerve_signature_rows"]
    ] == [
        ((0, 0, 0, 0), 18680),
        ((0, 0, 0, 1), 2048),
        ((0, 0, 1, 0), 9760),
        ((0, 0, 2, 0), 1216),
        ((0, 0, 3, 0), 32),
        ((0, 1, 0, 0), 908),
        ((0, 1, 1, 0), 64),
        ((0, 2, 0, 0), 56),
        ((0, 3, 0, 0), 2),
        ((1, 0, 0, 0), 2),
    ]
    assert antipodal["support_to_nerve_subcomplex_total"] == 167
    assert antipodal["support_to_nerve_fiber_total"] == 32768
    assert antipodal["support_to_nerve_h2_subcomplex_count"] == 1
    assert [
        (row["signature"], row["subcomplex_count"])
        for row in antipodal["support_to_nerve_subcomplex_signature_rows"]
    ] == [
        ((0, 0, 0, 0), 64),
        ((0, 0, 0, 1), 1),
        ((0, 0, 1, 0), 37),
        ((0, 0, 2, 0), 10),
        ((0, 0, 3, 0), 1),
        ((0, 1, 0, 0), 37),
        ((0, 1, 1, 0), 4),
        ((0, 2, 0, 0), 10),
        ((0, 3, 0, 0), 1),
        ((1, 0, 0, 0), 2),
    ]
    assert antipodal["hochster_p0_coefficients_desc"] == (
        4,
        48,
        268,
        920,
        2167,
        3704,
        4736,
        4592,
        3373,
        1844,
        720,
        184,
        25,
    )
    assert antipodal["hochster_p1_coefficients_desc"] == (
        6,
        60,
        278,
        784,
        1491,
        2002,
        1928,
        1320,
        617,
        178,
        22,
    )
    assert [
        (
            row["homology_degree"],
            row["diagonal"],
            tuple((degree, coefficient) for degree, coefficient in enumerate(row["coefficients"]) if coefficient),
            row["nonzero_count"],
            row["total_betti_mass"],
        )
        for row in antipodal["hochster_diagonal_rows"]
    ] == [
        (-1, 0, ((0, 1), (1, 2), (2, 1)), 3, 4),
        (
            0,
            1,
            (
                (2, 100),
                (3, 1036),
                (4, 5413),
                (5, 18558),
                (6, 46109),
                (7, 87320),
                (8, 129681),
                (9, 153426),
                (10, 145609),
                (11, 110844),
                (12, 67243),
                (13, 32074),
                (14, 11763),
                (15, 3200),
                (16, 608),
                (17, 72),
                (18, 4),
            ),
            17,
            813060,
        ),
        (
            1,
            2,
            (
                (3, 176),
                (4, 3448),
                (5, 32004),
                (6, 188174),
                (7, 789384),
                (8, 2519871),
                (9, 6368866),
                (10, 13082137),
                (11, 22229268),
                (12, 31625809),
                (13, 37973894),
                (14, 38665653),
                (15, 33455728),
                (16, 24590925),
                (17, 15312666),
                (18, 8035009),
                (19, 3523300),
                (20, 1275351),
                (21, 374462),
                (22, 86941),
                (23, 15360),
                (24, 1940),
                (25, 156),
                (26, 6),
            ),
            24,
            240150528,
        ),
        (
            2,
            3,
            (
                (4, 16),
                (5, 384),
                (6, 4424),
                (7, 32568),
                (8, 172041),
                (9, 694254),
                (10, 2224607),
                (11, 5808396),
                (12, 12582427),
                (13, 22907654),
                (14, 35377221),
                (15, 46646368),
                (16, 52738794),
                (17, 51252348),
                (18, 42843366),
                (19, 30778024),
                (20, 18951702),
                (21, 9957596),
                (22, 4434562),
                (23, 1658184),
                (24, 513821),
                (25, 129558),
                (26, 25899),
                (27, 3948),
                (28, 431),
                (29, 30),
                (30, 1),
            ),
            27,
            339738624,
        ),
    ]
    assert antipodal["blocker_euler_characteristic"] == 2
    assert [
        (row["added_size"], row["blocker_count"], round(row["full_trigger_probability"], 4))
        for row in antipodal["blocker_probability_tail_rows"]
    ] == [
        (1, 28, 0.0667),
        (2, 278, 0.3609),
        (3, 1336, 0.6709),
        (4, 3914, 0.8572),
        (5, 7972, 0.9441),
        (6, 12006, 0.9798),
        (7, 13728, 0.9933),
        (8, 12012, 0.9979),
        (9, 8008, 0.9994),
        (10, 4004, 0.9999),
    ]
    assert antipodal["alexander_dual_generator_count"] == 4
    assert [
        (row["coordinate"], row["degree"])
        for row in antipodal["alexander_dual_generator_rows"]
    ] == [
        ("s1", 16),
        ("f1", 16),
        ("s2", 16),
        ("f2", 16),
    ]
    assert [
        (row["subset_size"], row["subset_count"], row["lcm_degrees"], row["formula_degree"], row["reliability_coefficient"])
        for row in antipodal["alexander_dual_lcm_rows"]
    ] == [
        (1, 4, (16, 16, 16, 16), 16, 4),
        (2, 6, (24, 24, 24, 24, 24, 24), 24, -6),
        (3, 4, (28, 28, 28, 28), 28, 4),
        (4, 1, (30,), 30, -1),
    ]
    assert antipodal["alexander_dual_betti_pattern"] == (1, 4, 6, 4, 1)
    assert [
        (row["homological_position"], row["rank"], row["shift"])
        for row in antipodal["alexander_dual_resolution_rows"]
    ] == [
        (1, 4, 16),
        (2, 6, 24),
        (3, 4, 28),
        (4, 1, 30),
    ]
    assert antipodal["alexander_dual_resolution_string"] == "0 -> R0(-30) -> R0(-28)^4 -> R0(-24)^6 -> R0(-16)^4 -> J -> 0"
    assert antipodal["alexander_dual_reliability_terms"] == (
        (1, 4, 16),
        (2, -6, 24),
        (3, 4, 28),
        (4, -1, 30),
    )
    assert antipodal["alexander_dual_reliability_polynomial"] == "4q^16 - 6q^24 + 4q^28 - q^30"
    assert [
        (row["trigger_size"], row["quotient_count"], row["codon_count"])
        for row in antipodal["minimal_trigger_rows"]
    ] == [
        (1, 1, 2),
        (2, 25, 100),
        (3, 22, 176),
        (4, 1, 16),
    ]
    assert antipodal["minimal_trigger_quotient_total"] == 49
    assert antipodal["minimal_trigger_codon_total"] == 294
    assert antipodal["minimal_trigger_polynomial_quotient"] == (
        (1, 1),
        (2, 25),
        (3, 22),
        (4, 1),
    )
    assert antipodal["minimal_trigger_polynomial_codon"] == (
        (1, 2),
        (2, 100),
        (3, 176),
        (4, 16),
    )
    assert [
        (
            row["trigger_size"],
            row["homology_degree"],
            row["sphere"],
            row["quotient_count"],
            row["codon_count"],
        )
        for row in antipodal["minimal_trigger_homology_core_rows"]
    ] == [
        (1, -1, "S^-1", 1, 2),
        (2, 0, "S^0", 25, 100),
        (3, 1, "S^1", 22, 176),
        (4, 2, "S^2", 1, 16),
    ]
    assert antipodal["rank_enumerator_formula"] == "sum_d binom(4,d) u^d sum_k (-1)^(d-k) binom(d,k) (1+t)^(2(2^k-1))"
    assert [
        (row["added_size"], row["rank_counts"], row["counts_sum_to_candidate_count"])
        for row in antipodal["rank_enumerator_rows"]
    ] == [
        (0, {0: 1, 1: 0, 2: 0, 3: 0, 4: 0}, True),
        (1, {0: 0, 1: 8, 2: 12, 3: 8, 4: 2}, True),
        (2, {0: 0, 1: 4, 2: 78, 3: 196, 4: 157}, True),
        (3, {0: 0, 1: 0, 2: 120, 3: 1216, 4: 2724}, True),
        (4, {0: 0, 1: 0, 2: 90, 3: 3824, 4: 23491}, True),
    ]
    assert [
        (row["support_size_type"], row["energy"], row["quotient_count"], row["codon_count"])
        for row in antipodal["minimal_trigger_type_rows"]
    ] == [
        ((4,), 4, 1, 2),
        ((1, 3), 4, 4, 16),
        ((2, 2), 4, 3, 12),
        ((2, 3), 5, 12, 48),
        ((3, 3), 6, 6, 24),
        ((1, 1, 2), 4, 6, 48),
        ((1, 2, 2), 5, 12, 96),
        ((2, 2, 2), 6, 4, 32),
        ((1, 1, 1, 1), 4, 1, 16),
    ]
    assert antipodal["trigger_energy_minimum"] == 4
    assert antipodal["trigger_energy_minimum_condition"] == "support partition of Omega"
    assert [
        (row["trigger_size"], row["partition_type"], row["quotient_count"], row["codon_count"])
        for row in antipodal["energy_minimal_trigger_rows"]
    ] == [
        (1, "4", 1, 2),
        (2, "1+3 or 2+2", 7, 28),
        (3, "1+1+2", 6, 48),
        (4, "1+1+1+1", 1, 16),
    ]
    assert antipodal["energy_minimal_quotient_total"] == 15
    assert antipodal["energy_minimal_codon_total"] == 94
    assert [
        (row["energy"], row["quotient_count"], row["codon_count"])
        for row in antipodal["minimal_trigger_energy_rows"]
    ] == [
        (4, 15, 94),
        (5, 24, 144),
        (6, 10, 56),
    ]
    assert antipodal["quotient_bivariate_minimal_trigger_terms"] == (
        (1, 4, 1),
        (2, 4, 4),
        (2, 4, 3),
        (2, 5, 12),
        (2, 6, 6),
        (3, 4, 6),
        (3, 5, 12),
        (3, 6, 4),
        (4, 4, 1),
    )
    assert antipodal["codon_bivariate_minimal_trigger_terms"] == (
        (1, 4, 2),
        (2, 4, 16),
        (2, 4, 12),
        (2, 5, 48),
        (2, 6, 24),
        (3, 4, 48),
        (3, 5, 96),
        (3, 6, 32),
        (4, 4, 16),
    )
    assert antipodal["quotient_bivariate_minimal_trigger_polynomial"] == "z y^4 + z^2(7y^4+12y^5+6y^6) + z^3(6y^4+12y^5+4y^6) + z^4 y^4"
    assert antipodal["codon_bivariate_minimal_trigger_polynomial"] == "2z y^4 + z^2(28y^4+48y^5+24y^6) + z^3(48y^4+96y^5+32y^6) + 16z^4 y^4"
    assert antipodal["stanley_reisner_generator_count"] == 294
    assert [
        (row["degree"], row["minimal_generator_count"])
        for row in antipodal["stanley_reisner_degree_rows"]
    ] == [
        (1, 2),
        (2, 100),
        (3, 176),
        (4, 16),
    ]
    assert antipodal["stanley_reisner_degree_one_generators"] == ("AGC", "AGT")
    assert antipodal["reliability_polynomial"] == "1 - 4q^16 + 6q^24 - 4q^28 + q^30"
    assert [
        (
            row["target_probability"],
            round(row["activation_probability"], 5),
            round(row["expected_selected_codons"], 2),
        )
        for row in antipodal["reliability_threshold_rows"]
    ] == [
        (0.5, 0.08779, 2.63),
        (0.9, 0.19455, 5.84),
        (0.95, 0.23206, 6.96),
        (0.99, 0.30934, 9.28),
    ]
    assert antipodal["energy_biased_total_partition"] == "(1+ty)^8 (1+ty^2)^12 (1+ty^3)^8 (1+ty^4)^2"
    assert antipodal["energy_biased_blocker_partition"] == "4A3(t,y) - 6A2(t,y) + 4A1(t,y) - 1"
    assert antipodal["energy_biased_reliability_formula"] == "1 - (4A3(t,y)-6A2(t,y)+4A1(t,y)-1)/A4(t,y)"
    assert antipodal["energy_biased_low_energy_terms"] == (
        (1, 2),
        (2, 28),
        (3, 48),
        (4, 16),
    )
    assert antipodal["energy_biased_low_energy_polynomial"] == "y^4(2t+28t^2+48t^3+16t^4)"
    assert [
        (
            row["target_probability"],
            row["energy_factor"],
            round(row["activity"], 4),
            round(row["expected_selected_codons"], 2),
        )
        for row in antipodal["energy_biased_threshold_rows"]
    ] == [
        (0.5, 1.0, 0.0962, 2.63),
        (0.5, 0.75, 0.2008, 3.01),
        (0.5, 0.5, 0.5108, 3.53),
        (0.5, 0.25, 1.983, 4.23),
        (0.5, 0.1, 8.5128, 4.69),
        (0.9, 1.0, 0.2415, 5.84),
        (0.9, 0.75, 0.4903, 6.39),
        (0.9, 0.5, 1.2207, 7.04),
        (0.9, 0.25, 4.7581, 7.69),
        (0.9, 0.1, 21.7497, 7.8),
        (0.95, 1.0, 0.3022, 6.96),
        (0.95, 0.75, 0.6114, 7.55),
        (0.95, 0.5, 1.5224, 8.22),
        (0.95, 0.25, 6.0003, 8.8),
        (0.95, 0.1, 28.2281, 8.77),
    ]
    assert antipodal["conditional_trigger_size_formula"] == "t d_t log Z_trig(t,y)"
    assert antipodal["conditional_trigger_energy_formula"] == "y d_y log Z_trig(t,y)"
    assert [
        (
            row["target_probability"],
            row["energy_factor"],
            round(row["activity"], 4),
            round(row["conditional_expected_size"], 3),
            round(row["conditional_expected_energy"], 3),
        )
        for row in antipodal["conditional_trigger_rows"]
    ] == [
        (0.5, 1.0, 0.0962, 3.596, 8.184),
        (0.5, 0.75, 0.2008, 4.013, 8.294),
        (0.5, 0.5, 0.5108, 4.58, 8.308),
        (0.5, 0.25, 1.983, 5.318, 8.008),
        (0.5, 0.1, 8.5128, 5.751, 7.296),
        (0.9, 1.0, 0.2415, 6.144, 13.237),
        (0.9, 0.75, 0.4903, 6.699, 13.271),
        (0.9, 0.5, 1.2207, 7.354, 13.06),
        (0.9, 0.25, 4.7581, 7.989, 12.201),
        (0.9, 0.1, 21.7497, 8.07, 10.71),
    ]
    assert antipodal["low_energy_partition_distribution_formula"] == "a_m t^m / (2t+28t^2+48t^3+16t^4)"
    assert [
        (
            row["activity"],
            tuple(round(row["size_probabilities"][trigger_size], 4) for trigger_size in (1, 2, 3, 4)),
            round(row["expected_size"], 3),
        )
        for row in antipodal["low_energy_partition_rows"]
    ] == [
        (0.1, (0.3776, 0.5287, 0.0906, 0.003), 1.719),
        (0.25, (0.1633, 0.5714, 0.2449, 0.0204), 2.122),
        (0.5, (0.0667, 0.4667, 0.4, 0.0667), 2.467),
        (1.0, (0.0213, 0.2979, 0.5106, 0.1702), 2.83),
        (2.0, (0.0053, 0.1481, 0.5079, 0.3386), 3.18),
        (5.0, (0.0006, 0.0419, 0.3591, 0.5984), 3.555),
        (10.0, (0.0001, 0.0133, 0.2277, 0.7589), 3.745),
    ]
    assert [
        (row["left_size"], row["right_size"], row["activity"])
        for row in antipodal["low_energy_partition_crossover_rows"]
    ] == [
        (1, 2, 1.0 / 14.0),
        (2, 3, 7.0 / 12.0),
        (3, 4, 3.0),
    ]
    universal = antipodal["universal_coverage_trigger"]
    assert universal["coordinate_count"] == 4
    assert universal["lift_count"] == 2
    assert universal["external_size"] == 30
    assert universal["closure_lattice_size"] == 16
    assert [
        (row["rank"], row["external_closure_size"])
        for row in universal["closure_size_by_rank"]
    ] == [
        (0, 0),
        (1, 2),
        (2, 6),
        (3, 14),
        (4, 30),
    ]
    assert universal["blocker_homotopy_sphere_dimension"] == 2
    assert universal["maximal_blocker_size"] == 14
    assert universal["forced_trigger_threshold"] == 15
    assert [
        (row["missing_coordinate_count"], row["intersection_size"])
        for row in universal["blocker_intersection_formula_rows"]
    ] == [
        (1, 14),
        (2, 6),
        (3, 2),
        (4, 0),
    ]
    assert [
        (row["added_size"], row["blocker_count"])
        for row in universal["blocker_count_rows"][:4]
    ] == [
        (1, 28),
        (2, 278),
        (3, 1336),
        (4, 3914),
    ]
    assert [
        (row["missing_coordinate_count"], row["coefficient"], row["exponent"])
        for row in universal["reliability_term_rows"]
    ] == [
        (1, 4, 16),
        (2, -6, 24),
        (3, 4, 28),
        (4, -1, 30),
    ]
    assert universal["markov_drift_numerator_factor"] == 16
    assert [
        (row["rank_increase"], row["numerator_factor"])
        for row in universal["markov_initial_transition_rows"]
    ] == [
        (1, 8),
        (2, 12),
        (3, 8),
        (4, 2),
    ]
    assert universal["alexander_dual_generator_count"] == 4
    assert [
        (row["subset_size"], row["multiplicity"], row["shift"])
        for row in universal["alexander_dual_shift_rows"]
    ] == [
        (1, 4, 16),
        (2, 6, 24),
        (3, 4, 28),
        (4, 1, 30),
    ]
    assert universal["stanley_reisner_dimension_formula"] == 14
    assert universal["homological_core_dimension"] == 2
    assert universal["depth_formula"] == 3
    assert universal["regularity_formula"] == 3
    assert universal["projective_dimension_formula"] == 27
    assert universal["cohen_macaulay_defect_formula"] == 11
    assert universal["hochster_full_vertex_witness"] == {
        "betti_i": 27,
        "betti_j": 30,
        "homology_degree": 2,
        "betti_value": 1,
    }
    assert [
        (
            row["support_rank"],
            row["saturated_face_size"],
            row["link_coordinate_count"],
            row["link_lift_count"],
            row["link_sphere_dimension"],
        )
        for row in universal["local_link_formula_rows"]
    ] == [
        (0, 0, 4, 2, 2),
        (1, 2, 3, 4, 1),
        (2, 6, 2, 8, 0),
        (3, 14, 1, 16, -1),
    ]
    assert universal["top_betti_strand_formula"] == "((1+x)^2-1)^4(1+x)^22"
    assert universal["top_betti_singleton_support_count"] == 4
    assert universal["top_betti_free_element_count"] == 22
    assert universal["energy_minimum"] == 4
    assert [
        (row["trigger_size"], row["stirling_count"], row["lifted_count"])
        for row in universal["energy_minimal_rows"]
    ] == [
        (1, 1, 2),
        (2, 7, 28),
        (3, 6, 48),
        (4, 1, 16),
    ]
    assert universal["energy_minimal_total"] == 94
    assert antipodal["maximum_nontrigger_external_size"] == 14
    assert antipodal["maximum_nontrigger_blocker_count"] == 4
    assert antipodal["forced_full_trigger_threshold"] == 15
    assert round(spectral["acg_spectral_radius_before"], 4) == 0.6422
    assert round(spectral["acg_spectral_radius_after"], 4) == 0.6752
    assert round(spectral["acg_retention_before"], 3) == 0.596
    assert round(spectral["acg_retention_after"], 3) == 0.633
    assert spectral["acg_boundary_before"] == 46
    assert spectral["acg_boundary_after"] == 44
    greedy = summary["support_compression"]["greedy_spectral_closure"]
    assert greedy["anchor_triple_search"]["candidate_count"] == 20825
    assert greedy["anchor_triple_search"]["best_count"] == 1
    assert greedy["anchor_triple_search"]["best_added"] == ("AAG", "ACA", "TGG")
    assert round(greedy["anchor_triple_search"]["base_spectral_radius"], 6) == 0.475879
    assert round(greedy["anchor_triple_search"]["best_spectral_radius"], 6) == 0.573333
    assert round(greedy["anchor_triple_search"]["best_gain"], 6) == 0.097454
    assert [
        (row["added"], round(row["spectral_radius"], 6), row["base_neighbor_count"])
        for row in greedy["anchor_triple_search"]["top_rows"][:5]
    ] == [
        (("AAG", "ACA", "TGG"), 0.573333, 9),
        (("AAG", "ATG", "TTG"), 0.571538, 7),
        (("TCG", "TGG", "TTG"), 0.571538, 7),
        (("CAA", "CAG", "TTG"), 0.568746, 7),
        (("AAG", "TGG", "TTG"), 0.568575, 9),
    ]
    assert greedy["first_median_triple_search"]["candidate_count"] == 17296
    assert greedy["first_median_triple_search"]["best_count"] == 1
    assert greedy["first_median_triple_search"]["best_added"] == ("ATG", "TCG", "TTG")
    assert round(greedy["first_median_triple_search"]["base_spectral_radius"], 6) == 0.573333
    assert round(greedy["first_median_triple_search"]["best_spectral_radius"], 6) == 0.642182
    assert round(greedy["first_median_triple_search"]["best_gain"], 6) == 0.068849
    assert [
        (row["added"], round(row["spectral_radius"], 6), row["base_neighbor_count"])
        for row in greedy["first_median_triple_search"]["top_rows"][:5]
    ] == [
        (("ATG", "TCG", "TTG"), 0.642182, 7),
        (("ACG", "ATG", "TTG"), 0.639317, 7),
        (("ACG", "TCG", "TTG"), 0.639317, 7),
        (("ACG", "ATG", "TCG"), 0.633254, 6),
        (("ATG", "CAA", "TTG"), 0.6289, 7),
    ]
    assert greedy["acg_single_search"]["candidate_count"] == 45
    assert greedy["acg_single_search"]["best_count"] == 1
    assert greedy["acg_single_search"]["best_added"] == ("ACG",)
    assert round(greedy["acg_single_search"]["base_spectral_radius"], 6) == 0.642182
    assert round(greedy["acg_single_search"]["best_spectral_radius"], 6) == 0.675248
    assert round(greedy["acg_single_search"]["best_gain"], 6) == 0.033066
    assert [
        (row["added"], round(row["spectral_radius"], 6), round(row["gain"], 6), row["base_neighbor_count"])
        for row in greedy["acg_single_search"]["top_rows"][:5]
    ] == [
        (("ACG",), 0.675248, 0.033066, 4),
        (("CAA",), 0.650885, 0.008703, 2),
        (("CAG",), 0.650143, 0.007961, 2),
        (("CCA",), 0.649491, 0.00731, 2),
        (("GTA",), 0.649491, 0.00731, 2),
    ]
    assert greedy["support_single_search"]["best_added"] == ("ACA",)
    assert greedy["support_single_search"]["best_count"] == 1
    assert [
        (row["added"], round(row["spectral_radius"], 6), row["base_neighbor_count"])
        for row in greedy["support_single_search"]["top_rows"][:5]
    ] == [
        (("ACA",), 0.523726, 3),
        (("TTG",), 0.513385, 3),
        (("CAA",), 0.506652, 2),
        (("AAG",), 0.506292, 3),
        (("TGG",), 0.506292, 3),
    ]
    assert greedy["support_pair_search"]["candidate_count"] == 1275
    assert greedy["support_pair_search"]["best_count"] == 1
    assert greedy["support_pair_search"]["best_added"] == ("ACA", "TTG")
    assert round(greedy["support_pair_search"]["best_spectral_radius"], 6) == 0.546504
    assert [
        (row["added"], round(row["spectral_radius"], 6), row["base_neighbor_count"])
        for row in greedy["support_pair_search"]["top_rows"][:5]
    ] == [
        (("ACA", "TTG"), 0.546504, 6),
        (("AAG", "ACA"), 0.545591, 6),
        (("ACA", "TGG"), 0.545591, 6),
        (("AAG", "TGG"), 0.54346, 6),
        (("ACA", "CAA"), 0.541681, 5),
    ]
    assert greedy["anchor_single_search"]["candidate_count"] == 48
    assert greedy["anchor_single_search"]["best_count"] == 1
    assert greedy["anchor_single_search"]["best_added"] == ("TTG",)
    assert round(greedy["anchor_single_search"]["best_spectral_radius"], 6) == 0.592944
    assert greedy["anchor_pair_search"]["candidate_count"] == 1128
    assert greedy["anchor_pair_search"]["best_count"] == 2
    assert [
        row["added"] for row in greedy["anchor_pair_search"]["best_rows"]
    ] == [
        ("ATG", "TTG"),
        ("TCG", "TTG"),
    ]
    assert round(greedy["anchor_pair_search"]["best_spectral_radius"], 6) == 0.618387
    assert greedy["fixed_budget_rows"][3]["candidate_count"] == 249900
    assert greedy["fixed_budget_rows"][3]["best_count"] == 2
    assert [
        (row["added"], round(row["spectral_radius"], 6), round(row["gain"], 6), row["base_neighbor_count"])
        for row in greedy["fixed_budget_rows"][3]["best_added_rows"]
    ] == [
        (("AAG", "ACA", "ATG", "TTG"), 0.597078, 0.121199, 10),
        (("ACA", "TCG", "TGG", "TTG"), 0.597078, 0.121199, 10),
    ]
    assert greedy["fixed_budget_nested_failure"] == {
        "budget_2": ("ACA", "TTG"),
        "budget_3": ("AAG", "ACA", "TGG"),
        "budget_2_subset_budget_3": False,
    }
    assert greedy["tau_invariant_frontier_rows"] == [
        {"budget": 1, "best_added": ("ACA",)},
        {"budget": 2, "best_added": ("ACA", "TTG")},
        {"budget": 3, "best_added": ("AAG", "ACA", "TGG")},
        {"budget": 4, "best_added": ("AAG", "ACA", "TGG", "TTG")},
        {"budget": 5, "best_added": ("AAG", "ATG", "TCG", "TGG", "TTG")},
        {"budget": 6, "best_added": ("AAG", "ACA", "ATG", "TCG", "TGG", "TTG")},
        {"budget": 6, "best_added": ("AAG", "ACG", "ATG", "TCG", "TGG", "TTG")},
        {"budget": 7, "best_added": ("AAG", "ACA", "ACG", "ATG", "TCG", "TGG", "TTG")},
    ]
    assert [
        (row["set"], row["added"], row["vertices"], round(row["spectral_radius"], 6))
        for row in greedy["chain_rows"]
    ] == [
        ("support", (), 13, 0.475879),
        ("anchor_closure", ("AAG", "ACA", "TGG"), 16, 0.573333),
        ("median_stage_one", ("ATG", "TCG", "TTG"), 19, 0.642182),
        ("median_closure", ("ACG",), 20, 0.675248),
    ]
    assert [round(row["gain"], 6) for row in greedy["gain_rows"]] == [
        0.097454,
        0.068849,
        0.033066,
    ]
    wobble = summary["support_compression"]["wobble_saturation"]
    assert wobble["bit_coordinates"] == ("s1", "f1", "s2", "f2", "s3", "f3")
    assert [
        (
            row["direction"],
            row["added_count"],
            row["added"],
            row["contained_in_median"],
        )
        for row in wobble["directional_saturation_rows"]
    ] == [
        ("s1", 7, ("AAG", "ACA", "GTA", "GTC", "GTG", "GTT", "TGG"), False),
        ("f1", 11, ("CAA", "CAG", "CCA", "CGA", "GAA", "GGA", "GGG", "GTA", "TTC", "TTG", "TTT"), False),
        ("s2", 7, ("ACA", "ACG", "CAA", "CAC", "CAG", "CAT", "TTG"), False),
        ("f2", 7, ("AAG", "ACA", "CCA", "CCC", "CCG", "CCT", "TGG"), False),
        ("s3", 9, ("AAT", "AGC", "AGT", "ATT", "TAC", "TAT", "TCT", "TGT", "TTT"), False),
        ("f3", 5, ("AAG", "ATG", "TCG", "TGG", "TTG"), True),
    ]
    assert wobble["f3_saturation"] == (
        "AAA",
        "AAG",
        "AGA",
        "AGG",
        "ATA",
        "ATG",
        "CTA",
        "CTC",
        "CTG",
        "CTT",
        "TAA",
        "TAG",
        "TCA",
        "TCG",
        "TGA",
        "TGG",
        "TTA",
        "TTG",
    )
    assert wobble["f3_saturation_added_over_support"] == ("AAG", "ATG", "TCG", "TGG", "TTG")
    assert wobble["f3_saturation_missing_from_median"] == ("ACA", "ACG")
    assert wobble["f3_saturation_equals_median_minus_thr_pair"] is True
    assert wobble["f3_completion_points"] == ("ACA", "ACG")
    assert wobble["sat_f3_support_aca_equals_median"] is True
    assert wobble["sat_f3_support_acg_equals_median"] is True
    assert [
        (row["set"], tuple(row["counts"][coordinate] for coordinate in wobble["bit_coordinates"]), row["total"])
        for row in wobble["direction_boundary_rows"]
    ] == [
        ("support", (7, 11, 7, 7, 9, 5), 46),
        ("anchor_closure", (4, 14, 8, 4, 12, 4), 46),
        ("median_stage_one", (5, 15, 5, 5, 15, 1), 46),
        ("median_closure", (4, 16, 4, 4, 16, 0), 44),
    ]
    assert wobble["stage_one_f3_boundary_edges"] == (("ACA", "ACG"),)
    assert wobble["median_f3_silent"] is True
    assert wobble["median_boolean_formula_matches"] is True
    assert wobble["median_boolean_formula_vertices"] == summary["support_compression"]["median_closure"]["median_closure"]
    quotient = wobble["quotient"]
    assert quotient["support"] == (
        "UUR",
        "UCR",
        "UAR",
        "UGR",
        "CUY",
        "CUR",
        "AUR",
        "AAR",
        "AGR",
    )
    assert quotient["median_closure"] == (
        "UUR",
        "UCR",
        "UAR",
        "UGR",
        "CUY",
        "CUR",
        "AUR",
        "ACR",
        "AAR",
        "AGR",
    )
    assert quotient["support_is_median_minus_acr"] is True
    assert quotient["missing_support_point"] == ("ACR",)
    assert quotient["median_closure_of_support"] == quotient["median_closure"]
    assert quotient["median_stages"] == [
        {"stage": 1, "added_count": 1, "added": ("ACR",), "total_size": 10}
    ]
    assert quotient["median_closure_matches_projected_median"] is True
    assert quotient["acr_witness"] == {"triple": ("AGR", "AUR", "UCR"), "median": "ACR"}
    assert quotient["complex"]["f_vector"] == (10, 14, 6, 1, 0, 0)
    assert quotient["support_complex"]["f_vector"] == (9, 11, 3, 0, 0, 0)
    assert [
        (tuple(cell["free_bits"]), tuple(cell["labels"]))
        for cell in quotient["complex"]["maximal_cells"]
    ] == [
        ((0, 2, 3), ("UUR", "UCR", "UAR", "UGR", "AUR", "ACR", "AAR", "AGR")),
        ((4,), ("CUY", "CUR")),
        ((1,), ("UUR", "CUR")),
    ]
    assert quotient["product_with_f3_preimage_matches_median"] is True
    assert quotient["product_f_vector"] == (20, 38, 26, 8, 1)
    assert quotient["median_f_vector"] == (20, 38, 26, 8, 1)
    assert round(quotient["quotient_mu_max"], 9) == 3.051487585
    assert round(quotient["product_spectral_radius"], 9) == 0.675247931
    assert round(quotient["median_spectral_radius"], 9) == 0.675247931
    assert quotient["occupancy_rows"] == [
        {"quotient": "UUR", "pair": ("UUA", "UUG"), "active_occupancy": 1},
        {"quotient": "UCR", "pair": ("UCA", "UCG"), "active_occupancy": 1},
        {"quotient": "UAR", "pair": ("UAA", "UAG"), "active_occupancy": 2},
        {"quotient": "UGR", "pair": ("UGA", "UGG"), "active_occupancy": 1},
        {"quotient": "AUR", "pair": ("AUA", "AUG"), "active_occupancy": 1},
        {"quotient": "ACR", "pair": ("ACA", "ACG"), "active_occupancy": 0},
        {"quotient": "AAR", "pair": ("AAA", "AAG"), "active_occupancy": 1},
        {"quotient": "AGR", "pair": ("AGA", "AGG"), "active_occupancy": 2},
        {"quotient": "CUR", "pair": ("CUA", "CUG"), "active_occupancy": 2},
        {"quotient": "CUY", "pair": ("CUC", "CUU"), "active_occupancy": 2},
    ]
    assert quotient["full_active_pairs"] == ("UAR", "AGR", "CUR", "CUY")
    assert quotient["half_active_pairs"] == ("UUR", "UCR", "UGR", "AUR", "AAR")
    assert quotient["empty_pairs"] == ("ACR",)
    radial = quotient["radial_spectrum"]
    assert radial["state_order"] == ("X3", "X2", "X1", "X0", "YR", "YY")
    assert radial["state_names"] == {
        "X3": "AGR",
        "X2": "Anchor6",
        "X1": "StopStart6",
        "X0": "UUR",
        "YR": "CUR",
        "YY": "CUY",
    }
    assert radial["state_codons"] == {
        "X3": ("AGR",),
        "X2": ("AAR", "ACR", "UGR"),
        "X1": ("AUR", "UAR", "UCR"),
        "X0": ("UUR",),
        "YR": ("CUR",),
        "YY": ("CUY",),
    }
    assert radial["lift_orbit_sizes"] == (2, 6, 6, 2, 2, 2)
    assert radial["adjacency_matrix"] == (
        (0, 3, 0, 0, 0, 0),
        (1, 0, 2, 0, 0, 0),
        (0, 2, 0, 1, 0, 0),
        (0, 0, 3, 0, 1, 0),
        (0, 0, 0, 1, 0, 1),
        (0, 0, 0, 0, 1, 0),
    )
    assert radial["characteristic_polynomial_coefficients"] == (-9, 0, 26, 0, -12, 0, 1)
    assert radial["cubic_in_mu_squared_coefficients"] == (-9, 26, -12, 1)
    assert round(radial["r_max"], 9) == 9.311576483
    assert round(radial["mu_max"], 9) == 3.051487585
    assert round(radial["lambda_from_radial"], 9) == 0.675247931
    assert radial["lambda_matches_median"] is True
    assert [
        (row["state"], row["name"], round(row["potential"], 4))
        for row in radial["survival_potential_rows"]
    ] == [
        ("X3", "AGR", 0.8506),
        ("X2", "Anchor6", 0.8652),
        ("X1", "StopStart6", 0.8948),
        ("X0", "UUR", 1.0),
        ("YR", "CUR", 0.3671),
        ("YY", "CUY", 0.1203),
    ]
    assert [
        (row["state"], row["name"], row["orbit_size"], round(row["mass"], 4))
        for row in radial["qsd_rows"]
    ] == [
        ("X3", "AGR", 2, 0.1117),
        ("X2", "Anchor6", 6, 0.3407),
        ("X1", "StopStart6", 6, 0.3524),
        ("X0", "UUR", 2, 0.1313),
        ("YR", "CUR", 2, 0.0482),
        ("YY", "CUY", 2, 0.0158),
    ]
    assert round(radial["anchor_stopstart_mass"], 4) == 0.6931
    assert radial["highest_survival_state"] == "X0"
    assert radial["self_loop_probability_from_f3"] == "1/6"
    assert round(radial["wobble_lambda_gain"], 6) == 0.166667
    assert round(radial["lambda_without_wobble_edge"], 9) == 0.508581264
    antenna = radial["spectral_antenna"]
    assert antenna["core"] == {
        "vertices": 16,
        "internal_edges": 32,
        "retention": "2/3",
        "retention_float": 2 / 3,
        "spectral_radius": 2 / 3,
    }
    assert antenna["median"]["vertices"] == 20
    assert antenna["median"]["internal_edges"] == 38
    assert antenna["median"]["retention"] == "19/30"
    assert round(antenna["median"]["retention_float"], 6) == 0.633333
    assert round(antenna["median"]["spectral_radius"], 9) == 0.675247931
    assert antenna["retention_drops"] is True
    assert antenna["spectral_radius_rises"] is True
    assert antenna["tail_self_energy_formula"] == "mu/(mu^2-1)"
    assert round(antenna["tail_self_energy_at_mu_max"], 6) == 0.367137
    assert [
        (
            row["tail_length"],
            round(row["mu_max"], 6),
            round(row["lambda_with_wobble"], 6),
        )
        for row in antenna["tail_length_rows"]
    ] == [
        (0, 3.0, 0.666667),
        (1, 3.045475, 0.674246),
        (2, 3.051488, 0.675248),
        (3, 3.052315, 0.675386),
        (4, 3.05243, 0.675405),
        (5, 3.052446, 0.675408),
    ]
    assert round(antenna["tail_gain_capture_against_length_5"], 4) == 0.9817
    assert round(antenna["tail_qsd_mass"], 4) == 0.064
    assert round(antenna["spectral_gain_over_core"], 6) == 0.008581
    ablation = radial["spectral_ablation"]
    assert round(ablation["base_spectral_radius"], 9) == 0.675247931
    assert [
        (row["state"], row["codons"], round(row["loss"], 6))
        for row in ablation["single_codon_orbit_rows"]
    ] == [
        ("UUR", ("TTA", "TTG"), 0.041994),
        ("StopStart6", ("ATA", "ATG", "TAA", "TAG", "TCA", "TCG"), 0.035931),
        ("Anchor6", ("AAA", "AAG", "ACA", "ACG", "TGA", "TGG"), 0.033066),
        ("AGR", ("AGA", "AGG"), 0.031505),
        ("CUR", ("CTA", "CTG"), 0.005593),
        ("CUY", ("CTC", "CTT"), 0.000643),
    ]
    assert [
        (row["name"], row["size"], round(row["spectral_radius"], 6), round(row["loss"], 6))
        for row in ablation["module_ablation_rows"]
    ] == [
        ("StopStart6", 6, 0.455342, 0.219906),
        ("Anchor6", 6, 0.512386, 0.162862),
        ("UUR", 2, 0.607625, 0.067623),
        ("AGR", 2, 0.62436, 0.050888),
        ("CUR", 2, 0.666667, 0.008581),
        ("CUY", 2, 0.674246, 0.001002),
    ]
    assert ablation["tail_coupling_ablation"]["name"] == "UUR-CUR"
    assert ablation["tail_coupling_ablation"]["edge_count"] == 2
    assert round(ablation["tail_coupling_ablation"]["spectral_radius"], 6) == 0.666667
    assert round(ablation["tail_coupling_ablation"]["loss"], 6) == 0.008581
    assert [
        (row["name"], row["edge_count"], round(row["spectral_radius"], 6), round(row["loss"], 6))
        for row in ablation["edge_group_ablation_rows"]
    ] == [
        ("Anchor6-StopStart6", 12, 0.512386, 0.162862),
        ("StopStart6-UUR", 6, 0.607625, 0.067623),
        ("StopStart6_internal", 3, 0.622672, 0.052576),
        ("AGR-Anchor6", 6, 0.62436, 0.050888),
        ("Anchor6_internal", 3, 0.627825, 0.047423),
        ("UUR_internal", 1, 0.655912, 0.019336),
        ("AGR_internal", 1, 0.661306, 0.013942),
        ("UUR-CUR", 2, 0.666667, 0.008581),
        ("CUR_internal", 1, 0.672777, 0.002471),
        ("CUR-CUY", 2, 0.674246, 0.001002),
        ("CUY_internal", 1, 0.674978, 0.00027),
    ]
    assert [
        (row["name"], tuple(row["edge"]), tuple(row["states"]), round(row["loss"], 6))
        for row in ablation["single_edge_top_rows"][:7]
    ] == [
        ("TTA-TTG", ("TTA", "TTG"), ("UUR", "UUR"), 0.019336),
        ("ATA-TTA", ("ATA", "TTA"), ("StopStart6", "UUR"), 0.017432),
        ("ATG-TTG", ("ATG", "TTG"), ("StopStart6", "UUR"), 0.017432),
        ("TAA-TTA", ("TAA", "TTA"), ("StopStart6", "UUR"), 0.017432),
        ("TAG-TTG", ("TAG", "TTG"), ("StopStart6", "UUR"), 0.017432),
        ("TCA-TTA", ("TCA", "TTA"), ("StopStart6", "UUR"), 0.017432),
        ("TCG-TTG", ("TCG", "TTG"), ("StopStart6", "UUR"), 0.017432),
    ]
    doob = radial["doob_conditioned_dynamics"]
    assert round(doob["mu"], 9) == 4.051487585
    assert [
        [round(value, 4) for value in row]
        for row in doob["transition_matrix"]
    ] == [
        [0.2468, 0.7532, 0.0, 0.0, 0.0, 0.0],
        [0.2427, 0.2468, 0.5105, 0.0, 0.0, 0.0],
        [0.0, 0.4773, 0.2468, 0.2758, 0.0, 0.0],
        [0.0, 0.0, 0.6626, 0.2468, 0.0906, 0.0],
        [0.0, 0.0, 0.0, 0.6723, 0.2468, 0.0809],
        [0.0, 0.0, 0.0, 0.0, 0.7532, 0.2468],
    ]
    assert [round(row["drift"], 4) for row in doob["drift_rows"]] == [
        0.7532,
        0.2679,
        -0.2015,
        -0.5719,
        -0.5914,
        -0.7532,
    ]
    assert [
        (row["state"], round(row["mass"], 4))
        for row in doob["stationary_rows"]
    ] == [
        ("X3", 0.1110),
        ("X2", 0.3444),
        ("X1", 0.3684),
        ("X0", 0.1534),
        ("YR", 0.0207),
        ("YY", 0.0022),
    ]
    assert round(doob["anchor_stopstart_stationary_mass"], 4) == 0.7128
    assert round(doob["anchor_stopstart_uur_stationary_mass"], 4) == 0.8661
    assert [
        (row["state"], round(row["qsd_mass"], 4), round(row["stationary_mass"], 4))
        for row in doob["qsd_comparison_rows"]
    ] == [
        ("X3", 0.1117, 0.1110),
        ("X2", 0.3407, 0.3444),
        ("X1", 0.3524, 0.3684),
        ("X0", 0.1313, 0.1534),
        ("YR", 0.0482, 0.0207),
        ("YY", 0.0158, 0.0022),
    ]
    assert [
        (row["edge_group"], round(row["flux"], 4))
        for row in doob["flux_rows"]
    ] == [
        ("X3-X2", 0.0836),
        ("X2-X1", 0.1758),
        ("X1-X0", 0.1016),
        ("X0-YR", 0.0139),
        ("YR-YY", 0.0017),
    ]
    assert doob["central_flux_row"]["edge_group"] == "X2-X1"
    assert [
        (row["cut"], round(row["prefix_mass"], 4), round(row["boundary_flux"], 4), round(row["conductance"], 4))
        for row in doob["conductance_rows"]
    ] == [
        ("X3|X2-X1-X0-YR-YY", 0.1110, 0.0836, 0.7532),
        ("X3-X2|X1-X0-YR-YY", 0.4554, 0.1758, 0.3861),
        ("X3-X2-X1|X0-YR-YY", 0.8237, 0.1016, 0.5765),
        ("X3-X2-X1-X0|YR-YY", 0.9771, 0.0139, 0.6071),
        ("X3-X2-X1-X0-YR|YY", 0.9978, 0.0017, 0.7532),
    ]
    assert doob["minimum_conductance_row"]["cut"] == "X3-X2|X1-X0-YR-YY"
    assert summary["reassignment"]["q3_reassignment_scores"][0] == {
        "score": 52,
        "vertices": ("TAA", "TAG", "TGA", "TGG", "AAA", "AAG", "AGA", "AGG"),
        "free_bits": (0, 3, 5),
        "standard_pattern": "3+2+2+1",
    }
    assert summary["reassignment"]["q3_reassignment_scores"][1]["score"] == 41
    assert summary["reassignment"]["transfer_square"] == {
        "standard": {"TGA": "*", "TGG": "W", "AGA": "R", "AGG": "R"},
        "table_2": {"TGA": "W", "TGG": "W", "AGA": "*", "AGG": "*"},
    }
    assert summary["reassignment"]["arg_satellite"]["main_box_counts"] == {"CGT": 0, "CGC": 0, "CGA": 0, "CGG": 0}
    assert summary["reassignment"]["arg_satellite"]["satellite_counts"] == {"AGA": 8, "AGG": 8}
    assert summary["reassignment"]["ser_satellite"] == {"AGT": 0, "AGC": 0}
    assert summary["reassignment"]["aua_to_met_tables"] == [2, 3, 5, 13, 21]
    assert set(summary["reassignment"]["aua_to_met_tables"]).issubset(set(summary["reassignment"]["tga_to_trp_tables"]))
    assert summary["reassignment"]["ugg_changes"] == []
    assert summary["q1_all_tables"] == {47: 2, 48: 1, 49: 4, 50: 9, 51: 4, 52: 7}


def main() -> int:
    summary = build_summary()
    assert_expected(summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

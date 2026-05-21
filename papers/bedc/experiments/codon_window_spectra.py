#!/usr/bin/env python3
from __future__ import annotations

import collections
import fractions
import http.client
import itertools
import json
import random
import re
import urllib.request


NCBI_GENETIC_CODES_URL = "https://www.ncbi.nlm.nih.gov/Taxonomy/Utils/wprintgc.cgi?chapter=tgencodes"
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
    request = urllib.request.Request(
        NCBI_GENETIC_CODES_URL,
        headers={"User-Agent": "BEDC-codon-window-spectra", "Accept-Encoding": "identity"},
    )
    try:
        data = urllib.request.urlopen(request, timeout=30).read()
    except http.client.IncompleteRead as exc:
        data = exc.partial
    return data.decode("utf-8", "replace")


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
    for dimension in range(1, 7):
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

    minimal_exact_covers: list[tuple[dict[str, object], ...]] = []
    for cover_size in range(1, 8):
        for blocks in itertools.combinations(maximal_internal, cover_size):
            covered = set().union(*(set(block["vertices"]) for block in blocks))
            if covered == support:
                minimal_exact_covers.append(blocks)
        if minimal_exact_covers:
            break
    envelope_motifs = ("WRR", "CUN", "WYA")
    envelope_sets = {motif: set(expand_iupac_motif(motif)) for motif in envelope_motifs}
    envelope_union = set().union(*envelope_sets.values())
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
        "maximal_internal_subcubes": maximal_internal,
        "minimal_exact_cover_size": len(minimal_exact_covers[0]),
        "minimal_exact_cover_count": len(minimal_exact_covers),
        "minimal_exact_covers": [
            [tuple(block["vertices"]) for block in cover]
            for cover in minimal_exact_covers
        ],
        "envelope_motifs": {
            motif: tuple(sorted(codons))
            for motif, codons in envelope_sets.items()
        },
        "envelope_union": tuple(sorted(envelope_union)),
        "envelope_false_positives": tuple(sorted(envelope_union - support)),
        "envelope_covers_support": support <= envelope_union,
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
    assert summary["support_compression"]["internal_subcube_count"] == 20
    assert summary["support_compression"]["minimal_exact_cover_size"] == 5
    assert summary["support_compression"]["minimal_exact_cover_count"] == 1
    assert summary["support_compression"]["minimal_exact_covers"] == [
        [
            ("CTT", "CTC", "CTA", "CTG"),
            ("TTA", "TAA", "ATA", "AAA"),
            ("TTA", "TCA", "TAA", "TGA"),
            ("AGA", "AGG"),
            ("TAA", "TAG"),
        ]
    ]
    assert summary["support_compression"]["envelope_motifs"] == {
        "CUN": ("CTA", "CTC", "CTG", "CTT"),
        "WRR": ("AAA", "AAG", "AGA", "AGG", "TAA", "TAG", "TGA", "TGG"),
        "WYA": ("ACA", "ATA", "TCA", "TTA"),
    }
    assert summary["support_compression"]["envelope_covers_support"] is True
    assert summary["support_compression"]["envelope_false_positives"] == ("AAG", "ACA", "TGG")
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

#!/usr/bin/env python3
from __future__ import annotations

import collections
import http.client
import itertools
import json
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
    all_q1_totals = collections.Counter(sum(q1_spectrum(table)[0]) for table in tables.values())
    return {
        "table_ids": sorted(tables),
        "q1_standard": {"same_by_direction": q1_same, "diff_by_direction": q1_diff, "same_total": sum(q1_same)},
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
        "reassignment": reassignment_spectrum(tables, cubes),
        "partial_aware_core": state_components(partial_tables, CORE_HOTSPOT),
        "active_module_partitions": active_module_partition_summary(partial_tables),
        "module_activation_grammar": module_activation_summary(partial_tables),
        "q1_all_tables": dict(sorted(all_q1_totals.items())),
    }


def assert_expected(summary: dict[str, object]) -> None:
    assert summary["q1_standard"]["same_by_direction"] == [0, 2, 0, 1, 17, 30]
    assert summary["q1_standard"]["same_total"] == 50
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

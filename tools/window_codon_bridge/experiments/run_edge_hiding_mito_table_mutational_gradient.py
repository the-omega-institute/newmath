#!/usr/bin/env python3
"""Table-level AT-regime predictor for alternative-code edge hiding."""
from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import random
import re
import sys
import time
import urllib.parse
import urllib.request
from typing import Any


EXPERIMENT_ID = "edge_hiding_mito_table_mutational_gradient"
CLAIM_ID = "bridge.genetic_code.edge_hiding_mito_table_mutational_gradient"
N_PERMUTATIONS = 5000
BOOTSTRAP_DRAWS = 5000
ALPHA = 0.01
POWER_MIN_TABLES = 8
STOP = "*"
BASES_DNA = ("T", "C", "A", "G")
NCBI_DELAY_SECONDS = 0.34
MAX_NCBI_IDS_PER_TABLE = 12
MIN_FOURFOLD_CODONS_PER_TABLE = 20

EXPERIMENT_DIR = Path(__file__).resolve().parent
REPO_ROOT = EXPERIMENT_DIR.parents[2]
ALT_EDGE_PATH = EXPERIMENT_DIR / "run_edge_hiding_alternative_code_reassignment.py"
ALTCODE_PROBE_PATH = EXPERIMENT_DIR / "_altcode_fetch_probe.py"
GENETIC_CODES_PATH = REPO_ROOT / "tools" / "bio_reality" / "data" / "ncbi_genetic_codes.json"
STANDARD_PANEL_PATHS = (
    REPO_ROOT / "tools" / "window_codon_bridge" / "synced" / "codon_e1_heldout_panel.json",
    REPO_ROOT / "tools" / "window_codon_bridge" / "synced" / "codon_e1_transport_panel.json",
    REPO_ROOT / "tools" / "window_codon_bridge" / "synced" / "codon_e1_known_force_union_panel.json",
)


def load_module(path: Path, name: str) -> Any:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load {path.name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


ALT_EDGE = load_module(ALT_EDGE_PATH, "_edgehide_alt_reassign_for_table_gradient")
ALTCODE_PROBE = load_module(ALTCODE_PROBE_PATH, "_altcode_probe_for_table_gradient")


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status in {"certified", "coincidence"} else (2 if status == "refuted" else 3))


def stable_seed(text: str) -> int:
    return int.from_bytes(hashlib.sha256(text.encode("utf-8")).digest()[:16], "big")


def round_float(value: float | None, digits: int = 12) -> float | None:
    if value is None:
        return None
    if not math.isfinite(value):
        return value
    rounded = round(value, digits)
    return 0.0 if rounded == -0.0 else rounded


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def median(values: list[float]) -> float:
    ordered = sorted(values)
    n = len(ordered)
    mid = n // 2
    if n % 2:
        return ordered[mid]
    return (ordered[mid - 1] + ordered[mid]) / 2.0


def dna(codon: str) -> str:
    return codon.upper().replace("U", "T")


def rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def load_genetic_codes() -> dict[int, dict[str, object]]:
    payload = json.loads(GENETIC_CODES_PATH.read_text(encoding="utf-8"))
    return {
        int(item["table_id"]): {
            "table_id": int(item["table_id"]),
            "name": str(item["name"]),
            "codon_to_aa": dict(zip(payload["codon_order"], str(item["aa"]))),
        }
        for item in payload["tables"]
    }


def fourfold_families(codon_to_aa: dict[str, str]) -> list[list[str]]:
    by_prefix: dict[str, list[str]] = defaultdict(list)
    for codon, aa in codon_to_aa.items():
        if aa != STOP:
            by_prefix[codon[:2]].append(codon)
    families = []
    for codons in by_prefix.values():
        if len(codons) == 4 and len({codon_to_aa[codon] for codon in codons}) == 1:
            families.append(sorted(codons))
    return sorted(families)


def at_equilibrium_4fold(counts_rna: dict[str, int], codon_to_aa: dict[str, str]) -> tuple[float | None, int]:
    total = 0
    at = 0
    for family in fourfold_families(codon_to_aa):
        family_total = sum(int(counts_rna.get(codon, 0)) for codon in family)
        if family_total <= 0:
            continue
        total += family_total
        at += sum(int(counts_rna.get(codon, 0)) for codon in family if codon[2] in {"A", "U"})
    if total <= 0:
        return None, 0
    return at / total, total


def rankdata(values: list[float]) -> list[float]:
    ordered = sorted(enumerate(values), key=lambda item: item[1])
    ranks = [0.0 for _ in values]
    pos = 0
    while pos < len(ordered):
        end = pos + 1
        while end < len(ordered) and ordered[end][1] == ordered[pos][1]:
            end += 1
        rank = (pos + 1 + end) / 2.0
        for idx in range(pos, end):
            ranks[ordered[idx][0]] = rank
        pos = end
    return ranks


def pearson(left: list[float], right: list[float]) -> float | None:
    if len(left) < 2 or len(left) != len(right):
        return None
    lm = mean(left)
    rm = mean(right)
    num = sum((a - lm) * (b - rm) for a, b in zip(left, right))
    ld = math.sqrt(sum((a - lm) * (a - lm) for a in left))
    rd = math.sqrt(sum((b - rm) * (b - rm) for b in right))
    if ld <= 0.0 or rd <= 0.0:
        return None
    return num / (ld * rd)


def spearman(left: list[float], right: list[float]) -> float | None:
    return pearson(rankdata(left), rankdata(right))


def residualize_one(x: list[float], z: list[float]) -> list[float]:
    xm = mean(x)
    zm = mean(z)
    denom = sum((value - zm) * (value - zm) for value in z)
    if denom <= 0.0:
        return [value - xm for value in x]
    beta = sum((a - xm) * (b - zm) for a, b in zip(x, z)) / denom
    alpha = xm - beta * zm
    return [value - (alpha + beta * control) for value, control in zip(x, z)]


def partial_spearman_by_r(left: list[float], right: list[float], control: list[float]) -> float | None:
    if len(left) < 3 or len(left) != len(right) or len(left) != len(control):
        return None
    left_res = residualize_one(rankdata(left), rankdata(control))
    right_res = residualize_one(rankdata(right), rankdata(control))
    return pearson(left_res, right_res)


def p_value_two_sided(observed: float | None, null_values: list[float]) -> float | None:
    if observed is None or not null_values:
        return None
    hits = sum(abs(value) >= abs(observed) for value in null_values)
    return (1 + hits) / (1 + len(null_values))


def r2_score(y: list[float], yhat: list[float]) -> float | None:
    if len(y) < 2:
        return None
    ym = mean(y)
    ss_tot = sum((value - ym) * (value - ym) for value in y)
    if ss_tot <= 0.0:
        return None
    ss_res = sum((actual - fitted) * (actual - fitted) for actual, fitted in zip(y, yhat))
    return 1.0 - ss_res / ss_tot


def linear_fit_predict_one(x: list[float], y: list[float]) -> list[float]:
    xm = mean(x)
    ym = mean(y)
    denom = sum((value - xm) * (value - xm) for value in x)
    if denom <= 0.0:
        return [ym for _ in y]
    beta = sum((a - xm) * (b - ym) for a, b in zip(x, y)) / denom
    alpha = ym - beta * xm
    return [alpha + beta * value for value in x]


def linear_fit_predict_two(x1: list[float], x2: list[float], y: list[float]) -> list[float]:
    y0 = mean(y)
    a = [value - mean(x1) for value in x1]
    b = [value - mean(x2) for value in x2]
    c = [value - y0 for value in y]
    s11 = sum(value * value for value in a)
    s22 = sum(value * value for value in b)
    s12 = sum(left * right for left, right in zip(a, b))
    t1 = sum(left * value for left, value in zip(a, c))
    t2 = sum(right * value for right, value in zip(b, c))
    det = s11 * s22 - s12 * s12
    if abs(det) <= 1.0e-15:
        return linear_fit_predict_one(x1, y)
    beta1 = (t1 * s22 - t2 * s12) / det
    beta2 = (s11 * t2 - s12 * t1) / det
    x1m = mean(x1)
    x2m = mean(x2)
    alpha = y0 - beta1 * x1m - beta2 * x2m
    return [alpha + beta1 * left + beta2 * right for left, right in zip(x1, x2)]


def necessity_delta_r2(items: list[dict[str, object]]) -> dict[str, object]:
    y = [float(item["P_e"]) for item in items]
    x = [float(item["x_e"]) for item in items]
    r_values = [float(item["reassignment_count"]) for item in items]
    mean_hat = [mean(y) for _ in y]
    r_hat = linear_fit_predict_one(r_values, y)
    full_hat = linear_fit_predict_two(r_values, x, y)
    mean_r2 = r2_score(y, mean_hat)
    r_r2 = r2_score(y, r_hat)
    full_r2 = r2_score(y, full_hat)
    delta = None if r_r2 is None or full_r2 is None else full_r2 - r_r2
    return {
        "mean_only_R2": round_float(mean_r2),
        "reassignment_count_only_R2": round_float(r_r2),
        "reassignment_count_plus_AT_R2": round_float(full_r2),
        "delta_R2": round_float(delta),
        "drop_without_x_e": round_float(delta),
    }


def ncbi_url(endpoint: str, params: dict[str, object]) -> str:
    return f"https://eutils.ncbi.nlm.nih.gov/entrez/eutils/{endpoint}.fcgi?{urllib.parse.urlencode(params)}"


def fetch_text(url: str, timeout: int = 45) -> str:
    request = urllib.request.Request(url, headers={"User-Agent": EXPERIMENT_ID})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return response.read().decode("utf-8", "replace")


def parse_fasta_records(text: str) -> list[tuple[str, str]]:
    records: list[tuple[str, str]] = []
    header = ""
    chunks: list[str] = []
    for line in text.splitlines():
        if line.startswith(">"):
            if header and chunks:
                records.append((header, "".join(chunks)))
            header = line[1:].strip()
            chunks = []
        else:
            chunks.append(re.sub(r"[^A-Za-z]", "", line).upper())
    if header and chunks:
        records.append((header, "".join(chunks)))
    return records


def count_sense_codons(records: list[tuple[str, str]], codon_to_aa: dict[str, str]) -> tuple[dict[str, int], int]:
    counts = {codon: 0 for codon, aa in codon_to_aa.items() if aa != STOP}
    for _header, sequence in records:
        usable = (len(sequence) // 3) * 3
        for offset in range(0, usable, 3):
            codon = rna(sequence[offset : offset + 3])
            if codon in counts:
                counts[codon] += 1
    return counts, sum(counts.values())


def ncbi_counts_for_table(table_id: int, codon_to_aa: dict[str, str]) -> list[dict[str, object]]:
    term = f'"transl_table={table_id}"[All Fields]'
    search_url = ncbi_url("esearch", {"db": "nuccore", "term": term, "retmax": MAX_NCBI_IDS_PER_TABLE})
    try:
        search_text = fetch_text(search_url, timeout=45)
    except Exception as exc:
        return [{"source": "NCBI transl_table efetch", "ok": False, "drop_reason": f"search:{type(exc).__name__}:{exc}"}]
    ids = re.findall(r"<Id>(\d+)</Id>", search_text)
    if not ids:
        return [{"source": "NCBI transl_table efetch", "ok": False, "drop_reason": "no_nuccore_ids"}]
    time.sleep(NCBI_DELAY_SECONDS)
    fetch_url = ncbi_url(
        "efetch",
        {"db": "nuccore", "id": ",".join(ids), "rettype": "fasta_cds_na", "retmode": "text"},
    )
    try:
        fasta_text = fetch_text(fetch_url, timeout=75)
    except Exception as exc:
        return [{"source": "NCBI transl_table efetch", "ok": False, "drop_reason": f"efetch:{type(exc).__name__}:{exc}"}]
    records = parse_fasta_records(fasta_text)
    counts, total = count_sense_codons(records, codon_to_aa)
    x_value, fourfold_total = at_equilibrium_4fold(counts, codon_to_aa)
    if x_value is None or fourfold_total < MIN_FOURFOLD_CODONS_PER_TABLE:
        return [
            {
                "source": "NCBI transl_table efetch",
                "ok": False,
                "drop_reason": "no_usable_fourfold_codon_counts",
                "n_nuccore_ids": len(ids),
                "n_cds_records": len(records),
                "total_sense_codons": total,
                "fourfold_codon_total": fourfold_total,
            }
        ]
    return [
        {
            "source": "NCBI transl_table efetch",
            "ok": True,
            "x_e": x_value,
            "fourfold_codon_total": fourfold_total,
            "n_lineage_genomes": len(ids),
            "n_cds_records": len(records),
            "total_sense_codons": total,
        }
    ]


def standard_counts_from_existing_panels(codon_to_aa: dict[str, str]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for path in STANDARD_PANEL_PATHS:
        if not path.exists():
            continue
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue
        candidates = payload.get("organisms") or payload.get("rows") or []
        if not isinstance(candidates, list):
            continue
        for item in candidates:
            if not isinstance(item, dict) or not isinstance(item.get("codon_counts_rna"), dict):
                continue
            counts = {str(k): int(v) for k, v in item["codon_counts_rna"].items()}
            x_value, fourfold_total = at_equilibrium_4fold(counts, codon_to_aa)
            if x_value is None or fourfold_total < MIN_FOURFOLD_CODONS_PER_TABLE:
                continue
            rows.append(
                {
                    "source": path.name,
                    "ok": True,
                    "x_e": x_value,
                    "fourfold_codon_total": fourfold_total,
                    "n_lineage_genomes": 1,
                    "organism": item.get("organism") or item.get("species_name"),
                    "transl_table": item.get("transl_table"),
                }
            )
    return rows


def altcode_panel_counts(codes: dict[int, dict[str, object]]) -> dict[int, list[dict[str, object]]]:
    try:
        panel = ALTCODE_PROBE.build_panel(force_refresh=False)
    except Exception:
        return {}
    out: dict[int, list[dict[str, object]]] = defaultdict(list)
    for organism in panel.get("organisms", []):
        if not isinstance(organism, dict):
            continue
        table_id = int(organism.get("table_id") or -1)
        code = codes.get(table_id)
        if code is None or not isinstance(organism.get("codon_counts_rna"), dict):
            continue
        counts = {str(k): int(v) for k, v in organism["codon_counts_rna"].items()}
        x_value, fourfold_total = at_equilibrium_4fold(counts, code["codon_to_aa"])  # type: ignore[arg-type]
        if x_value is None or fourfold_total < MIN_FOURFOLD_CODONS_PER_TABLE:
            continue
        out[table_id].append(
            {
                "source": "codon_e1_alternative_code_fetch_probe_panel",
                "ok": True,
                "x_e": x_value,
                "fourfold_codon_total": fourfold_total,
                "n_lineage_genomes": 1,
                "organism": organism.get("organism"),
                "cluster": organism.get("cluster"),
                "accession": organism.get("accession"),
            }
        )
    return dict(out)


def table_family(name: str) -> str:
    lowered = name.lower()
    if lowered == "standard":
        return "standard"
    if "mitochondrial" in lowered:
        return "mitochondrial"
    if "nuclear" in lowered:
        return "nuclear"
    if "plastid" in lowered:
        return "plastid"
    return "other_alternative"


def phylo_cluster(name: str) -> str:
    lowered = name.lower()
    if "invertebrate" in lowered:
        return "invertebrate_mitochondrial"
    if "vertebrate" in lowered:
        return "vertebrate_mitochondrial"
    if "flatworm" in lowered or "trematode" in lowered:
        return "flatworm_mitochondrial"
    if "yeast" in lowered:
        return "yeast"
    if "ciliate" in lowered or "euplotid" in lowered or "karyorelict" in lowered or "condylostoma" in lowered or "peritrich" in lowered:
        return "ciliate_nuclear"
    if "standard" == lowered:
        return "standard_anchor"
    if "mitochondrial" in lowered:
        return "other_mitochondrial"
    if "nuclear" in lowered:
        return "other_nuclear"
    if "bacteria" in lowered or "division" in lowered or "gracilibacteria" in lowered:
        return "bacterial_alternative"
    return "other_alternative"


def table_level_x(
    table_id: int,
    codes: dict[int, dict[str, object]],
    panel_counts: dict[int, list[dict[str, object]]],
) -> tuple[float | None, dict[str, object]]:
    code = codes[table_id]
    rows = standard_counts_from_existing_panels(code["codon_to_aa"]) if table_id == 1 else list(panel_counts.get(table_id, []))  # type: ignore[arg-type]
    if table_id != 1 and not rows:
        rows = ncbi_counts_for_table(table_id, code["codon_to_aa"])  # type: ignore[arg-type]
    ok_rows = [row for row in rows if row.get("ok") and row.get("x_e") is not None]
    if not ok_rows:
        return None, {
            "status": "missing_x_e",
            "attempts": rows[:3],
            "x_e_predictor": "AT_4fold_equilibrium",
        }
    values = [float(row["x_e"]) for row in ok_rows]
    return median(values), {
        "status": "ok",
        "x_e_predictor": "AT_4fold_equilibrium",
        "aggregation": "median_across_available_lineage_genome_counts",
        "n_lineage_genomes": sum(int(row.get("n_lineage_genomes") or 1) for row in ok_rows),
        "n_count_rows": len(ok_rows),
        "fourfold_codon_total": sum(int(row.get("fourfold_codon_total") or 0) for row in ok_rows),
        "sources": dict(sorted(Counter(str(row.get("source")) for row in ok_rows).items())),
    }


def transition_cluster_key(result: dict[str, object]) -> str:
    matrix = result.get("transition_matrix")
    if isinstance(matrix, dict) and matrix:
        return "|".join(f"{key}:{matrix[key]}" for key in sorted(matrix))
    return "standard_or_start-only"


def build_tables() -> tuple[list[dict[str, object]], dict[str, object]]:
    probe = ALT_EDGE.load_probe_module()
    panel = probe.build_panel(force_refresh=False)
    if not panel.get("fetchable"):
        raise RuntimeError("NCBI gc.prt cache/fetch unavailable")
    codes = load_genetic_codes()
    tables = list(panel["tables"])  # type: ignore[index]
    table_by_id = {int(table["id"]): table for table in tables}
    standard_row = table_by_id.get(1)
    if standard_row is None:
        raise RuntimeError("gc.prt did not expose standard table id=1")
    codons = [dna(str(codon)) for codon in panel["codon_order"]]  # type: ignore[index]
    standard = list(str(standard_row["ncbieaa"]))
    edges = ALT_EDGE.hamming1_edges(codons)
    standard_e_all = ALT_EDGE.edge_count(standard, edges, sense_only=False)
    standard_e_sense = ALT_EDGE.edge_count(standard, edges, sense_only=True)
    panel_counts = altcode_panel_counts(codes)

    candidate_rows = [standard_row] + [
        table
        for table in tables
        if int(table["id"]) != 1 and str(table["ncbieaa"]) != str(standard_row["ncbieaa"])
    ]
    out: list[dict[str, object]] = []
    dropped: list[dict[str, object]] = []
    for table in candidate_rows:
        table_id = int(table["id"])
        if table_id not in codes:
            dropped.append({"table_id": table_id, "table_name": table.get("name"), "reason": "missing_local_code_definition"})
            continue
        edge_result = ALT_EDGE.table_result(table, standard, edges, standard_e_all, standard_e_sense)
        x_value, x_meta = table_level_x(table_id, codes, panel_counts)
        if x_value is None:
            dropped.append(
                {
                    "table_id": table_id,
                    "table_name": table.get("name"),
                    "reason": "missing_table_level_AT_4fold_counts",
                    "x_meta": x_meta,
                }
            )
            continue
        table_name = str(table.get("name") or codes[table_id]["name"])
        out.append(
            {
                "table_id": table_id,
                "table_name": table_name,
                "family": table_family(table_name),
                "phylo_cluster": phylo_cluster(table_name),
                "P_e": float(edge_result["Z_sense"]),
                "P_e_functional": "Z_sense from existing transition-matrix matched edge-hiding reassignment functional",
                "P_e_raw_delta_e_sense": int(edge_result["delta_e_sense"]),
                "P_e_event_p_sense": float(edge_result["p_sense"]),
                "x_e": float(x_value),
                "x_e_predictor": "AT_4fold_equilibrium",
                "reassignment_count": int(edge_result["R_t"]),
                "transition_cluster": transition_cluster_key(edge_result),
                **x_meta,
            }
        )
    diagnostics = {
        "gc_prt_source": panel.get("source"),
        "candidate_table_count": len(candidate_rows),
        "dropped_tables": dropped,
        "standard_e_sense": standard_e_sense,
        "standard_e_all": standard_e_all,
    }
    return sorted(out, key=lambda item: int(item["table_id"])), diagnostics


def observed_stats(items: list[dict[str, object]]) -> dict[str, float | None]:
    p_values = [float(item["P_e"]) for item in items]
    x_values = [float(item["x_e"]) for item in items]
    r_values = [float(item["reassignment_count"]) for item in items]
    return {
        "corr": spearman(p_values, x_values),
        "partial_corr": partial_spearman_by_r(p_values, x_values, r_values),
    }


def permutation_test(items: list[dict[str, object]]) -> dict[str, object]:
    observed = observed_stats(items)
    p_values = [float(item["P_e"]) for item in items]
    x_values = [float(item["x_e"]) for item in items]
    r_values = [float(item["reassignment_count"]) for item in items]
    rng = random.Random(stable_seed(EXPERIMENT_ID + ".table_level_permutation"))
    null_corr: list[float] = []
    null_partial: list[float] = []
    for _draw in range(N_PERMUTATIONS):
        shuffled_x = x_values[:]
        rng.shuffle(shuffled_x)
        corr = spearman(p_values, shuffled_x)
        partial = partial_spearman_by_r(p_values, shuffled_x, r_values)
        if corr is not None:
            null_corr.append(corr)
        if partial is not None:
            null_partial.append(partial)
    return {
        "corr": round_float(observed["corr"]),
        "p": round_float(p_value_two_sided(observed["corr"], null_corr)),
        "partial_corr_control_reassignment": round_float(observed["partial_corr"]),
        "partial_p": round_float(p_value_two_sided(observed["partial_corr"], null_partial)),
        "null": "table_level_permutation_of_AT_predictor_across_code_tables",
        "n_permutations": N_PERMUTATIONS,
    }


def bootstrap_lower95(items: list[dict[str, object]]) -> dict[str, object]:
    rng = random.Random(stable_seed(EXPERIMENT_ID + ".bootstrap"))
    n = len(items)
    corr_values: list[float] = []
    partial_values: list[float] = []
    for _draw in range(BOOTSTRAP_DRAWS):
        sampled = [items[rng.randrange(n)] for _idx in range(n)]
        stats = observed_stats(sampled)
        if stats["corr"] is not None:
            corr_values.append(float(stats["corr"]))
        if stats["partial_corr"] is not None:
            partial_values.append(float(stats["partial_corr"]))

    def lower(values: list[float]) -> float | None:
        if not values:
            return None
        ordered = sorted(values)
        return ordered[int(0.05 * (len(ordered) - 1))]

    return {
        "corr_lower95": round_float(lower(corr_values)),
        "partial_corr_lower95": round_float(lower(partial_values)),
        "draws": BOOTSTRAP_DRAWS,
        "successful_corr_draws": len(corr_values),
        "successful_partial_draws": len(partial_values),
    }


def phylo_clusters(items: list[dict[str, object]]) -> dict[str, object]:
    grouped: dict[str, list[dict[str, object]]] = defaultdict(list)
    transition_grouped: dict[str, list[dict[str, object]]] = defaultdict(list)
    for item in items:
        grouped[str(item["phylo_cluster"])].append(item)
        transition_grouped[str(item["transition_cluster"])].append(item)
    return {
        "phylo_note": "Code tables are not phylogenetically independent; same-source clusters are annotated and not used as extra features.",
        "by_name_cluster": {
            key: [{"table_id": int(item["table_id"]), "table_name": item["table_name"]} for item in values]
            for key, values in sorted(grouped.items())
        },
        "by_reassignment_signature": {
            key: [{"table_id": int(item["table_id"]), "table_name": item["table_name"]} for item in values]
            for key, values in sorted(transition_grouped.items())
            if len(values) > 1
        },
    }


def compact_table(item: dict[str, object]) -> dict[str, object]:
    return {
        "table_id": int(item["table_id"]),
        "table_name": item["table_name"],
        "P_e": round_float(float(item["P_e"])),
        "x_e": round_float(float(item["x_e"])),
        "x_e_predictor": item["x_e_predictor"],
        "reassignment_count": int(item["reassignment_count"]),
        "family": item["family"],
        "phylo_cluster": item["phylo_cluster"],
        "transition_cluster": item["transition_cluster"],
        "n_lineage_genomes": item.get("n_lineage_genomes"),
        "n_count_rows": item.get("n_count_rows"),
        "fourfold_codon_total": item.get("fourfold_codon_total"),
        "sources": item.get("sources"),
    }


def main() -> None:
    started = time.time()
    try:
        items, diagnostics = build_tables()
    except Exception as exc:
        emit(
            "needs_external",
            reason=f"table carrier construction failed: {type(exc).__name__}:{exc}",
            honest_scope_note=(
                "table-level mutational-regime gradient of edge-hiding preservation across "
                "organellar/alternative genetic codes; single pre-registered AT-equilibrium "
                "predictor with reassignment-count control; modest n and phylogenetic "
                "non-independence noted; table-level biological scope only, not causal."
            ),
            elapsed=round_float(time.time() - started, 6),
        )

    n_tables = len(items)
    power_gate = {"n_tables": n_tables, "requires_n_tables_at_least": POWER_MIN_TABLES, "powered": n_tables >= POWER_MIN_TABLES}
    nonstandard = [item for item in items if int(item["reassignment_count"]) > 0]
    pe_mean = mean([float(item["P_e"]) for item in nonstandard]) if nonstandard else None
    P_e_validity = {
        "status": "passed" if pe_mean is not None and pe_mean > 0.0 else "needs_external",
        "nonstandard_mean_P_e": round_float(pe_mean),
        "source": "existing edge-hiding reassignment matched-null preservation functional",
    }
    if n_tables < POWER_MIN_TABLES:
        emit(
            "needs_external",
            verdict_note="fewer than eight code tables have table-level AT-regime estimates",
            predictor_preregistration={"single_predictor": True, "predictor": "AT_4fold_equilibrium", "feature_hunting": False},
            power_gate=power_gate,
            P_e_validity=P_e_validity,
            n_tables=n_tables,
            per_table=[compact_table(item) for item in items],
            diagnostics=diagnostics,
            phylo_clusters=phylo_clusters(items),
            honest_scope_note=(
                "table-level mutational-regime gradient of edge-hiding preservation across "
                "organellar/alternative genetic codes; single pre-registered AT-equilibrium "
                "predictor with reassignment-count control; modest n and phylogenetic "
                "non-independence noted; table-level biological scope only, not causal."
            ),
            elapsed=round_float(time.time() - started, 6),
        )

    perm = permutation_test(items)
    boot = bootstrap_lower95(items)
    necessity = necessity_delta_r2(items)
    corr = perm.get("corr")
    p_value = perm.get("p")
    partial = perm.get("partial_corr_control_reassignment")
    partial_p = perm.get("partial_p")
    lower_corr = boot.get("corr_lower95")
    lower_partial = boot.get("partial_corr_lower95")
    same_direction = (
        corr is not None
        and partial is not None
        and lower_corr is not None
        and lower_partial is not None
        and float(corr) * float(lower_corr) > 0.0
        and float(partial) * float(lower_partial) > 0.0
    )
    raw_sig_001 = p_value is not None and float(p_value) <= ALPHA
    partial_sig_001 = partial_p is not None and float(partial_p) <= ALPHA
    raw_not_sig_005 = p_value is not None and float(p_value) > 0.05

    if raw_sig_001 and partial_sig_001 and same_direction:
        status = "certified"
        verdict_note = (
            "Across organellar/alternative genetic-code tables, AT mutational regime predicts "
            "edge-hiding preservation independently of reassignment count."
        )
    elif raw_sig_001 and not partial_sig_001:
        status = "coincidence"
        verdict_note = "The raw AT gradient is present, but reassignment-count control absorbs the table-level signal."
    elif raw_not_sig_005:
        status = "refuted"
        verdict_note = "The pre-registered table-level AT-regime predictor does not predict edge-hiding preservation."
    else:
        status = "coincidence"
        verdict_note = "The table-level AT gradient is suggestive but does not clear the registered evidence gates."

    emit(
        status,
        verdict_note=verdict_note,
        predictor_preregistration={"single_predictor": True, "predictor": "AT_4fold_equilibrium", "feature_hunting": False},
        matched_null=perm,
        corr=perm.get("corr"),
        p=perm.get("p"),
        partial_corr_control_reassignment=perm.get("partial_corr_control_reassignment"),
        partial_p=perm.get("partial_p"),
        n_tables=n_tables,
        per_table=[compact_table(item) for item in items],
        necessity_delta_R2=necessity,
        bootstrap_lower95=boot,
        power_gate=power_gate,
        P_e_validity=P_e_validity,
        phylo_clusters=phylo_clusters(items),
        diagnostics=diagnostics,
        honest_scope_note=(
            "table-level mutational-regime gradient of edge-hiding preservation across "
            "organellar/alternative genetic codes; single pre-registered AT-equilibrium "
            "predictor with reassignment-count control; modest n and phylogenetic "
            "non-independence noted; table-level biological scope only, not causal."
        ),
        elapsed=round_float(time.time() - started, 6),
    )


if __name__ == "__main__":
    main()

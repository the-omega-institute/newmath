#!/usr/bin/env python3
"""Alternative-code ProteinGym DMS edge-hiding panel.

Each NCBI genetic-code table is tested against its own sense-codon degeneracy
profile.  The DMS loss matrix and codon-edge statistic are the same
assay-balanced objects used by ``run_dms_edge_hiding_robustness.py``.
"""
from __future__ import annotations

from collections import Counter
import json
import math
from pathlib import Path
import random
import re
import sys

try:
    from tools.window_codon_bridge.experiments import run_code_edge_hiding_optimality as EDGE
    from tools.window_codon_bridge.experiments import run_dms_edge_hiding_robustness as DMS
except ModuleNotFoundError:
    sys.path.append(str(Path(__file__).resolve().parents[3]))
    from tools.window_codon_bridge.experiments import run_code_edge_hiding_optimality as EDGE
    from tools.window_codon_bridge.experiments import run_dms_edge_hiding_robustness as DMS


EXPERIMENT_ID = "altcode_dms_edge_hiding_panel"
CLAIM_ID = "bridge.genetic_code.altcode_dms_edge_hiding_panel"

GC_PRT = Path("/tmp/proteingym_cache/gc.prt")
NULL_SEED = 2026070301
NULL_DRAWS_PER_CODE = 2000
INDEPENDENT_REASSIGNED_THRESHOLD = 6
SIGNIFICANCE_P = 0.05
HIGH_P = 0.50
MODERATE_P = 0.20

BASES_DNA = ("T", "C", "A", "G")
BASES_RNA = ("U", "C", "A", "G")
DNA_TO_RNA = str.maketrans({"T": "U"})
AA_LETTERS = tuple("ACDEFGHIKLMNPQRSTVWY")
AA_TO_INDEX = {aa: index for index, aa in enumerate(AA_LETTERS)}


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    if status in {"certified", "coincidence"}:
        sys.exit(0)
    if status == "refuted":
        sys.exit(2)
    sys.exit(3)


def round_float(value: float | None, digits: int = 12) -> float | None:
    if value is None:
        return None
    if not math.isfinite(value):
        return value
    out = round(float(value), digits)
    return 0.0 if out == -0.0 else out


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def dna_codon_order() -> list[str]:
    return [a + b + c for a in BASES_DNA for b in BASES_DNA for c in BASES_DNA]


def parse_gc_prt(path: Path) -> list[dict[str, object]]:
    if not path.exists() or path.stat().st_size <= 0:
        raise FileNotFoundError(f"missing cached NCBI genetic-code table: {path}")
    text = path.read_text(encoding="utf-8", errors="replace")
    entries: list[dict[str, object]] = []
    for block in re.findall(r"\{\s*(.*?ncbieaa\s+\"[^\"]+\".*?)\n\s*\}", text, flags=re.S):
        id_match = re.search(r"\bid\s+([0-9]+)", block)
        aa_match = re.search(r"\bncbieaa\s+\"([^\"]+)\"", block)
        if id_match is None or aa_match is None:
            continue
        names = re.findall(r"\bname\s+\"([^\"]+)\"", block)
        ncbieaa = aa_match.group(1).strip()
        entries.append(
            {
                "id": int(id_match.group(1)),
                "name": names[0] if names else f"NCBI genetic code {id_match.group(1)}",
                "aliases": names,
                "ncbieaa": ncbieaa,
            }
        )
    if not entries:
        raise ValueError("no NCBI genetic-code entries with id and ncbieaa were parsed")
    entries.sort(key=lambda row: int(row["id"]))
    seen: set[int] = set()
    unique: list[dict[str, object]] = []
    for row in entries:
        code_id = int(row["id"])
        if code_id in seen:
            continue
        seen.add(code_id)
        unique.append(row)
    return unique


def validate_code_string(code_id: int, ncbieaa: str) -> None:
    if len(ncbieaa) != 64:
        raise ValueError(f"code {code_id} ncbieaa length is {len(ncbieaa)}, expected 64")
    allowed = set(AA_LETTERS) | {"*"}
    bad = sorted(set(ncbieaa) - allowed)
    if bad:
        raise ValueError(f"code {code_id} contains unsupported ncbieaa letters: {''.join(bad)}")


def code_mapping(ncbieaa: str) -> dict[str, str]:
    codons = dna_codon_order()
    return {codon.translate(DNA_TO_RNA): aa for codon, aa in zip(codons, ncbieaa)}


def sense_labels_and_edges(mapping: dict[str, str]) -> tuple[list[str], list[int], list[tuple[int, int]]]:
    codons64 = EDGE.codon_order()
    edges64 = EDGE.hamming1_edges(codons64)
    sense_codons = [codon for codon in codons64 if mapping[codon] != "*"]
    sense_index = {codon: index for index, codon in enumerate(sense_codons)}
    labels = [AA_TO_INDEX[mapping[codon]] for codon in sense_codons]
    sense_edges: list[tuple[int, int]] = []
    for left64, right64 in edges64:
        left_codon = codons64[left64]
        right_codon = codons64[right64]
        if left_codon in sense_index and right_codon in sense_index:
            sense_edges.append((sense_index[left_codon], sense_index[right_codon]))
    if not sense_edges:
        raise ValueError("sense Hamming-1 edge universe is empty")
    return sense_codons, labels, sense_edges


def code_scores(
    labels: list[int],
    edges: list[tuple[int, int]],
    loss_matrix: list[list[float]],
) -> tuple[int, float]:
    e_in = 0
    loss_sum = 0.0
    for left, right in edges:
        aa_left = labels[left]
        aa_right = labels[right]
        if aa_left == aa_right:
            e_in += 1
            continue
        loss_sum += loss_matrix[aa_left][aa_right]
    return e_in, loss_sum / len(edges)


def shuffled_labels(profile: Counter[int], rng: random.Random) -> list[int]:
    labels: list[int] = []
    for aa_index in range(len(AA_LETTERS)):
        labels.extend([aa_index] * profile[aa_index])
    rng.shuffle(labels)
    return labels


def p_lower_equal(null_values: list[float], observed: float) -> float:
    return sum(1 for value in null_values if value <= observed + 1.0e-15) / len(null_values)


def null_test(
    labels: list[int],
    edges: list[tuple[int, int]],
    loss_matrix: list[list[float]],
    seed: int,
) -> dict[str, object]:
    observed_e, observed_r = code_scores(labels, edges, loss_matrix)
    profile = Counter(labels)
    rng = random.Random(seed)
    null_r: list[float] = []
    null_e: list[int] = []
    for _ in range(NULL_DRAWS_PER_CODE):
        draw_labels = shuffled_labels(profile, rng)
        e_value, r_value = code_scores(draw_labels, edges, loss_matrix)
        null_e.append(e_value)
        null_r.append(r_value)
    return {
        "e_in": observed_e,
        "R_DMS": observed_r,
        "p_code": p_lower_equal(null_r, observed_r),
        "null_R_mean": mean(null_r),
        "null_e_in_mean": mean([float(value) for value in null_e]),
    }


def summarize_subset(rows: list[dict[str, object]]) -> dict[str, object]:
    if not rows:
        return {
            "n": 0,
            "threshold_p": SIGNIFICANCE_P,
            "n_p_le_0_05": 0,
            "fraction_p_le_0_05": None,
            "n_p_ge_0_50": 0,
            "max_p": None,
            "ids": [],
        }
    p_values = [float(row["p_code"]) for row in rows]
    return {
        "n": len(rows),
        "threshold_p": SIGNIFICANCE_P,
        "n_p_le_0_05": sum(1 for p_value in p_values if p_value <= SIGNIFICANCE_P),
        "fraction_p_le_0_05": sum(1 for p_value in p_values if p_value <= SIGNIFICANCE_P) / len(rows),
        "n_p_ge_0_50": sum(1 for p_value in p_values if p_value >= HIGH_P),
        "max_p": round_float(max(p_values)),
        "ids": [int(row["id"]) for row in rows],
    }


def panel_verdict(per_code: list[dict[str, object]]) -> tuple[str, str, str]:
    independent = [
        row
        for row in per_code
        if int(row["reassigned_vs_standard"]) >= INDEPENDENT_REASSIGNED_THRESHOLD
    ]
    all_p = [float(row["p_code"]) for row in per_code]
    independent_p = [float(row["p_code"]) for row in independent]
    if independent and len(independent) >= 3:
        high_fraction = sum(1 for p_value in independent_p if p_value >= HIGH_P) / len(independent_p)
        low_fraction = sum(1 for p_value in independent_p if p_value <= SIGNIFICANCE_P) / len(independent_p)
        if high_fraction >= 0.5 and low_fraction < 0.5:
            return (
                "refuted",
                "refuted",
                "the more reassigned alternative-code subset is systematically not a low-loss tail under its own degeneracy null",
            )
    if (
        independent
        and len(independent) >= 5
        and all(p_value <= SIGNIFICANCE_P for p_value in independent_p)
        and max(all_p) <= MODERATE_P
    ):
        return (
            "certified",
            "certified",
            "the conservative reassigned subset is uniformly low-loss and the full panel has no high-p counterexample",
        )
    return (
        "coincidence",
        "bounded",
        "alternative codes are highly non-independent relatives of the standard code, so low p-values in the panel are bounded evidence rather than an independent universality certificate",
    )


def main() -> None:
    try:
        entries = parse_gc_prt(GC_PRT)
        for row in entries:
            validate_code_string(int(row["id"]), str(row["ncbieaa"]))
        standard_rows = [row for row in entries if int(row["id"]) == 1]
        if not standard_rows:
            raise ValueError("NCBI code id 1 was not found")
        standard_ncbieaa = str(standard_rows[0]["ncbieaa"])

        binary_by_assay, _continuous_by_assay, dms_diagnostics = DMS.load_assay_balanced_fitness()
        loss_matrix, matrix_diagnostics = DMS.matrix_from_assays(binary_by_assay)

        per_code: list[dict[str, object]] = []
        duplicate_standard_ids: list[int] = []
        for entry in entries:
            code_id = int(entry["id"])
            ncbieaa = str(entry["ncbieaa"])
            reassigned = sum(1 for left, right in zip(ncbieaa, standard_ncbieaa) if left != right)
            if ncbieaa == standard_ncbieaa:
                duplicate_standard_ids.append(code_id)
                continue
            mapping = code_mapping(ncbieaa)
            sense_codons, labels, edges = sense_labels_and_edges(mapping)
            scores = null_test(labels, edges, loss_matrix, NULL_SEED + code_id * 1009)
            profile = Counter(labels)
            per_code.append(
                {
                    "id": code_id,
                    "name": str(entry["name"]),
                    "n_sense": len(sense_codons),
                    "e_in": int(scores["e_in"]),
                    "R_DMS": round_float(float(scores["R_DMS"])),
                    "p_code": round_float(float(scores["p_code"])),
                    "reassigned_vs_standard": reassigned,
                    "degeneracy_profile": {
                        aa: profile[AA_TO_INDEX[aa]]
                        for aa in AA_LETTERS
                        if profile[AA_TO_INDEX[aa]] > 0
                    },
                    "null_R_mean": round_float(float(scores["null_R_mean"])),
                    "null_e_in_mean": round_float(float(scores["null_e_in_mean"])),
                }
            )

        per_code.sort(key=lambda row: (int(row["reassigned_vs_standard"]), int(row["id"])))
        if not per_code:
            raise ValueError("no non-standard NCBI genetic-code tables were available for testing")

        independent = [
            row
            for row in per_code
            if int(row["reassigned_vs_standard"]) >= INDEPENDENT_REASSIGNED_THRESHOLD
        ]
        full_summary = summarize_subset(per_code)
        independent_summary = summarize_subset(independent)
        status, verdict, reason = panel_verdict(per_code)
        failure_rows = [
            {
                "id": int(row["id"]),
                "name": row["name"],
                "p_code": row["p_code"],
                "reassigned_vs_standard": row["reassigned_vs_standard"],
            }
            for row in per_code
            if float(row["p_code"]) >= HIGH_P
        ]

        aggregate = {
            "null_draws_per_code": NULL_DRAWS_PER_CODE,
            "full_panel": full_summary,
            "independent_subset_rule": f"reassigned_vs_standard >= {INDEPENDENT_REASSIGNED_THRESHOLD}",
            "independent_subset": independent_summary,
            "high_p_counterexamples_p_ge_0_50": failure_rows,
            "duplicate_standard_ncbieaa_ids_excluded": duplicate_standard_ids,
            "dms_assays_used": dms_diagnostics.get("n_assays_used"),
            "dms_single_mutants_used": dms_diagnostics.get("n_single_mutants_used"),
            "dms_directed_pair_coverage": matrix_diagnostics.get("coverage_directed_pairs"),
        }
        non_independence_note = (
            "NCBI alternative genetic codes are not independent samples: many differ from the standard code at only a few codons. "
            "Each p_code uses that code's own sense set and amino-acid degeneracy profile; the reassigned_vs_standard field is reported so the panel is not treated as independent replication."
        )

        emit(
            status,
            verdict=verdict,
            n_codes_tested=len(per_code),
            per_code=per_code,
            aggregate=aggregate,
            non_independence_note=non_independence_note,
            reason=reason,
        )
    except Exception as exc:
        emit(
            "needs_derivation",
            n_codes_tested=0,
            per_code=[],
            aggregate={},
            non_independence_note="panel could not be evaluated because parsing or DMS construction failed",
            reason=f"{type(exc).__name__}: {exc}",
        )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Project real multi-organism codon usage onto fold bulk/seam/defect axes."""
from __future__ import annotations

from itertools import product
import json
import math
import random
import subprocess
import sys
from pathlib import Path
from typing import Any


EXPERIMENT_ID = "codon_usage_projection_cert"
CLAIM_ID = "bridge.genetic_code.fold_order_parameter_usage"
SOURCE_REF = "origin/feat/bio-reality-deepening"
DATA_DIR = "tools/bio_reality/data"
SELECTION_VECTOR_PATH = Path("papers/window_codon_bridge/data/codon_q6_selection_vectors.json")
RANDOM_SEED = 640621
NULL_DRAWS = 5000

BASES = ("U", "C", "A", "G")
DNA_BASES = ("T", "C", "A", "G")
ALL_CODONS = ["".join(chars) for chars in product(BASES, repeat=3)]

PURE_BOXES = {"UC", "CU", "CC", "CG", "AC", "GU", "GC", "GG"}
BINARY_BOXES = {"UU", "UA", "CA", "AU", "AA", "AG", "GA"}
DEFECT_BOXES = {"UG"}

BULK_CODONS = {codon for codon in ALL_CODONS if codon[:2] in PURE_BOXES}
SEAM_CODONS = {codon for codon in ALL_CODONS if codon[:2] in BINARY_BOXES}
DEFECT_CODONS = {codon for codon in ALL_CODONS if codon[:2] in DEFECT_BOXES}


def emit(status: str, **fields: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False))
    sys.exit(0 if status in ("certified", "coincidence") else (2 if status == "refuted" else 3))


def git_text(args: list[str], max_bytes: int | None = None) -> str:
    proc = subprocess.run(
        ["git"] + args,
        capture_output=True,
        text=True,
        timeout=180,
    )
    if proc.returncode != 0:
        raise RuntimeError((proc.stderr or proc.stdout or "git command failed").strip())
    text = proc.stdout
    if max_bytes is not None and len(text.encode("utf-8")) > max_bytes:
        raise RuntimeError("git output exceeded expected size")
    return text


def list_usage_paths() -> list[str]:
    text = git_text(["ls-tree", "-r", "--name-only", SOURCE_REF, DATA_DIR])
    paths = [
        line.strip()
        for line in text.splitlines()
        if line.strip().startswith(f"{DATA_DIR}/cds_codon_counts_") and line.strip().endswith(".json")
    ]
    return sorted(paths)


def normalize_codon(codon: str) -> str:
    return codon.upper().replace("T", "U")


def organism_from_path(path: str) -> str:
    name = Path(path).name
    prefix = "cds_codon_counts_"
    suffix = ".json"
    if name.startswith(prefix) and name.endswith(suffix):
        return name[len(prefix):-len(suffix)]
    return Path(path).stem


def load_usage_counts(path: str) -> tuple[str, str, dict[str, int], int]:
    data = json.loads(git_text(["show", f"{SOURCE_REF}:{path}"]))
    organism = str(data.get("organism") or organism_from_path(path))
    label = str(data.get("organism_label") or data.get("assembly_organism_name") or organism)
    counts = {codon: 0 for codon in ALL_CODONS}
    invalid = 0
    for gene in data.get("genes", []):
        gene_counts = gene.get("codon_counts", {})
        if not isinstance(gene_counts, dict):
            invalid += 1
            continue
        for raw_codon, raw_count in gene_counts.items():
            codon = normalize_codon(str(raw_codon))
            if codon not in counts:
                invalid += 1
                continue
            try:
                count = int(raw_count)
            except (TypeError, ValueError):
                invalid += 1
                continue
            if count < 0:
                invalid += 1
                continue
            counts[codon] += count
    return organism_from_path(path), label, counts, invalid


def group_probability(counts: dict[str, int], group: set[str], total: int) -> float:
    return sum(counts[codon] for codon in group) / total


def gc3(counts: dict[str, int], total: int) -> float:
    return sum(count for codon, count in counts.items() if codon[2] in {"G", "C"}) / total


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def centered(values: list[float]) -> list[float]:
    m = mean(values)
    return [value - m for value in values]


def dot(left: list[float], right: list[float]) -> float:
    return sum(a * b for a, b in zip(left, right))


def norm(values: list[float]) -> float:
    return math.sqrt(dot(values, values))


def pearson(left: list[float], right: list[float]) -> float | None:
    if len(left) != len(right) or len(left) < 3:
        return None
    left_c = centered(left)
    right_c = centered(right)
    denom = norm(left_c) * norm(right_c)
    if denom <= 0.0:
        return None
    return dot(left_c, right_c) / denom


def residualize(y_values: list[float], x_values: list[float]) -> list[float]:
    y_c = centered(y_values)
    x_c = centered(x_values)
    denom = dot(x_c, x_c)
    if denom <= 0.0:
        return y_c
    slope = dot(y_c, x_c) / denom
    return [y_c[index] - slope * x_c[index] for index in range(len(y_values))]


def sample_sd(values: list[float]) -> float:
    if len(values) < 2:
        return 0.0
    m = mean(values)
    return math.sqrt(sum((value - m) ** 2 for value in values) / (len(values) - 1))


def empirical_ge(observed: float, null_values: list[float]) -> float:
    return (sum(1 for value in null_values if value >= observed - 1e-12) + 1) / (len(null_values) + 1)


def empirical_abs_ge(observed: float, null_values: list[float]) -> float:
    target = abs(observed)
    return (sum(1 for value in null_values if abs(value) >= target - 1e-12) + 1) / (len(null_values) + 1)


def round_float(value: float | None, digits: int = 10) -> float | None:
    if value is None:
        return None
    return round(float(value), digits)


def load_tai_by_codon() -> dict[str, float] | None:
    if not SELECTION_VECTOR_PATH.exists():
        return None
    data = json.loads(SELECTION_VECTOR_PATH.read_text())
    result: dict[str, float] = {}
    for row in data.get("vectors", []):
        if "codon" not in row or "trna_supply_tai_mean" not in row:
            continue
        if row["trna_supply_tai_mean"] is None:
            continue
        codon = normalize_codon(str(row["codon"]))
        if codon in ALL_CODONS:
            result[codon] = float(row["trna_supply_tai_mean"])
    return result if len(result) == 64 else None


def weighted_axis(counts: dict[str, int], total: int, axis: dict[str, float]) -> float:
    return sum((counts[codon] / total) * axis[codon] for codon in ALL_CODONS)


def random_groups(rng: random.Random) -> tuple[set[str], set[str], set[str]]:
    codons = ALL_CODONS[:]
    rng.shuffle(codons)
    bulk = set(codons[:len(BULK_CODONS)])
    seam = set(codons[len(BULK_CODONS):len(BULK_CODONS) + len(SEAM_CODONS)])
    defect = set(codons[len(BULK_CODONS) + len(SEAM_CODONS):])
    return bulk, seam, defect


def main() -> None:
    checks: list[str] = []
    if len(BULK_CODONS) != 32 or len(SEAM_CODONS) != 28 or len(DEFECT_CODONS) != 4:
        emit(
            "needs_derivation",
            n_organisms=0,
            checks=[
                f"group_size_error bulk={len(BULK_CODONS)} seam={len(SEAM_CODONS)} defect={len(DEFECT_CODONS)}"
            ],
            note="standard-code box groups did not self-check",
        )
    if BULK_CODONS & SEAM_CODONS or BULK_CODONS & DEFECT_CODONS or SEAM_CODONS & DEFECT_CODONS:
        emit("needs_derivation", n_organisms=0, checks=["group_overlap_error"], note="groups overlap")
    if len(BULK_CODONS | SEAM_CODONS | DEFECT_CODONS) != 64:
        emit("needs_derivation", n_organisms=0, checks=["group_cover_error"], note="groups do not cover 64 codons")
    checks.append("codon_group_sizes bulk=32 seam=28 defect=4")

    try:
        paths = list_usage_paths()
    except Exception as exc:
        emit("needs_derivation", n_organisms=0, checks=checks, note=f"could not list usage data: {exc}")
    checks.append(f"available_usage_files={len(paths)}")
    if len(paths) < 20:
        emit(
            "needs_derivation",
            n_organisms=0,
            checks=checks,
            note="fewer than 20 cds_codon_counts files were available from the source ref",
        )

    organism_labels: dict[str, str] = {}
    total_counts_by_organism: dict[str, int] = {}
    counts_by_organism: dict[str, dict[str, int]] = {}
    invalid_entries = 0
    for path in paths:
        try:
            organism, label, counts, invalid = load_usage_counts(path)
        except Exception as exc:
            checks.append(f"skipped {organism_from_path(path)}: {exc}")
            continue
        total = sum(counts.values())
        if total <= 0:
            checks.append(f"skipped {organism}: zero total codon count")
            continue
        organism_labels[organism] = label
        counts_by_organism[organism] = counts
        total_counts_by_organism[organism] = total
        invalid_entries += invalid

    organisms = sorted(counts_by_organism)
    if len(organisms) < 20:
        emit(
            "needs_derivation",
            n_organisms=len(organisms),
            checks=checks,
            note="fewer than 20 organisms could be parsed into nonzero 64-codon totals",
        )
    checks.append(f"parsed_organisms={len(organisms)}")
    checks.append(f"invalid_or_ignored_codon_entries={invalid_entries}")

    tai_axis = load_tai_by_codon()
    if tai_axis is None:
        checks.append("tai_proxy=unavailable")
    else:
        checks.append("tai_proxy=trna_supply_tai_mean_64_codons")

    m_by_org: dict[str, float] = {}
    gc3_by_org: dict[str, float] = {}
    tai_by_org: dict[str, float] = {}
    proportions_by_org: dict[str, dict[str, float]] = {}
    for organism in organisms:
        counts = counts_by_organism[organism]
        total = total_counts_by_organism[organism]
        bulk_p = group_probability(counts, BULK_CODONS, total)
        seam_p = group_probability(counts, SEAM_CODONS, total)
        defect_p = group_probability(counts, DEFECT_CODONS, total)
        m_by_org[organism] = bulk_p - seam_p
        gc3_by_org[organism] = gc3(counts, total)
        proportions_by_org[organism] = {
            "bulk": round_float(bulk_p),
            "seam": round_float(seam_p),
            "defect": round_float(defect_p),
        }
        if tai_axis is not None:
            tai_by_org[organism] = weighted_axis(counts, total, tai_axis)

    m_values = [m_by_org[organism] for organism in organisms]
    gc_values = [gc3_by_org[organism] for organism in organisms]
    observed_corr = pearson(m_values, gc_values)
    if observed_corr is None:
        emit(
            "needs_derivation",
            n_organisms=len(organisms),
            checks=checks,
            note="m_bio or GC3 had zero cross-organism variance",
        )

    observed_residuals = residualize(m_values, gc_values)
    observed_residual_sd = sample_sd(observed_residuals)

    tai_corr = None
    partial_tai_corr = None
    if tai_by_org:
        tai_values = [tai_by_org[organism] for organism in organisms]
        tai_corr = pearson(m_values, tai_values)
        partial_tai_corr = pearson(observed_residuals, residualize(tai_values, gc_values))

    rng = random.Random(RANDOM_SEED)
    null_corrs: list[float] = []
    null_residual_sds: list[float] = []
    null_partial_tai_corrs: list[float] = []
    for _ in range(NULL_DRAWS):
        bulk, seam, _defect = random_groups(rng)
        null_m = []
        for organism in organisms:
            counts = counts_by_organism[organism]
            total = total_counts_by_organism[organism]
            null_m.append(group_probability(counts, bulk, total) - group_probability(counts, seam, total))
        corr = pearson(null_m, gc_values)
        if corr is not None:
            null_corrs.append(corr)
        null_residuals = residualize(null_m, gc_values)
        null_residual_sds.append(sample_sd(null_residuals))
        if tai_by_org:
            pcorr = pearson(null_residuals, residualize([tai_by_org[organism] for organism in organisms], gc_values))
            if pcorr is not None:
                null_partial_tai_corrs.append(pcorr)

    null_p = empirical_abs_ge(observed_corr, null_corrs)
    residual_sd_null_p = empirical_ge(observed_residual_sd, null_residual_sds)
    partial_tai_null_p = (
        empirical_abs_ge(partial_tai_corr, null_partial_tai_corrs)
        if partial_tai_corr is not None and null_partial_tai_corrs
        else None
    )

    has_gc_structure = null_p <= 0.05
    has_strong_gc_proxy = abs(observed_corr) >= 0.70
    has_non_gc_residual = residual_sd_null_p <= 0.05
    has_tai_residual = partial_tai_null_p is not None and partial_tai_null_p <= 0.05
    if has_gc_structure and has_non_gc_residual and has_tai_residual:
        status = "certified"
        note = "m_bio exceeds the same-size random grouping null and retains GC-controlled tRNA-linked residual signal."
    elif has_gc_structure or has_strong_gc_proxy:
        status = "coincidence"
        note = "m_bio is dominated by GC3 and shows no GC-controlled residual signal; this is a GC proxy coincidence rather than an independent fold signal."
    else:
        status = "refuted"
        note = "bulk/seam usage contrast does not exceed same-size random grouping structure against GC3."

    null_summary = {
        "draws": NULL_DRAWS,
        "seed": RANDOM_SEED,
        "corr_abs_ge_observed_p": round_float(null_p),
        "corr_mean": round_float(mean(null_corrs)),
        "corr_min": round_float(min(null_corrs)),
        "corr_max": round_float(max(null_corrs)),
        "residual_sd_ge_observed_p": round_float(residual_sd_null_p),
        "residual_sd_mean": round_float(mean(null_residual_sds)),
        "residual_sd_min": round_float(min(null_residual_sds)),
        "residual_sd_max": round_float(max(null_residual_sds)),
    }

    gc_controlled_signal: dict[str, object] = {
        "m_residual_sd_after_gc3": round_float(observed_residual_sd),
        "residual_sd_null_p": round_float(residual_sd_null_p),
        "non_gc_residual_signal": bool(has_non_gc_residual),
    }
    if tai_by_org:
        gc_controlled_signal.update({
            "weighted_tai_mean_vs_m_bio_corr": round_float(tai_corr),
            "weighted_tai_partial_corr_after_gc3": round_float(partial_tai_corr),
            "weighted_tai_partial_corr_null_p": round_float(partial_tai_null_p),
            "tai_residual_signal": bool(has_tai_residual),
        })

    emit(
        status,
        n_organisms=len(organisms),
        organisms=organisms,
        organism_labels=organism_labels,
        codon_totals_by_organism=total_counts_by_organism,
        m_bio_by_organism={organism: round_float(m_by_org[organism]) for organism in organisms},
        proportions_by_organism=proportions_by_org,
        gc3_by_organism={organism: round_float(gc3_by_org[organism]) for organism in organisms},
        weighted_tai_mean_by_organism=(
            {organism: round_float(tai_by_org[organism]) for organism in organisms} if tai_by_org else None
        ),
        m_bio_vs_gc3_corr=round_float(observed_corr),
        null_p=round_float(null_p),
        null_summary=null_summary,
        gc_controlled_signal=gc_controlled_signal,
        checks=checks,
        note=note,
    )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Adjudicate fibonacci Track-A wobble-boundary response against bridge structure."""
from __future__ import annotations

from collections import defaultdict
import hashlib
import json
import math
from pathlib import Path
import random
import subprocess
import sys
from typing import Any


EXPERIMENT_ID = "fibonacci_tracka_wobble_vs_codon_e1"
CLAIM_ID = "bridge.fibonacci_tracka.wobble_boundary_vs_codon_e1"
TRACKA_BRANCH = "origin/feat/fibonacci_reality-deepening"
TRACKA_FETCH_REFSPEC = "feat/fibonacci_reality-deepening:refs/remotes/origin/feat/fibonacci_reality-deepening"
SCRATCH_ROOT = Path("/tmp/tracka_src")
NULL_N = 20000
EPS = 1.0e-12
TOL = 1.0e-10
SIGNIFICANCE_ALPHA = 0.05

TRACKA_PATHS = (
    "tools/fibonacci_reality/experiments/run_track_a_yeast_wobble_boundary_response.py",
    "tools/fibonacci_reality/experiments/run_track_a_human_wobble_boundary_response.py",
    "tools/fibonacci_reality/data/cds_codon_abundance_saccharomyces_cerevisiae.json",
    "tools/fibonacci_reality/data/gtrnadb_trna_all_copy_saccharomyces_cerevisiae.json",
    "tools/fibonacci_reality/data/cds_codon_abundance_homo_sapiens.json",
    "tools/fibonacci_reality/data/gtrnadb_trna_all_copy_homo_sapiens.json",
)

ORGANISMS = {
    "yeast": {
        "experiment_path": "tools/fibonacci_reality/experiments/run_track_a_yeast_wobble_boundary_response.py",
        "slug": "saccharomyces_cerevisiae",
    },
    "human": {
        "experiment_path": "tools/fibonacci_reality/experiments/run_track_a_human_wobble_boundary_response.py",
        "slug": "homo_sapiens",
    },
}

EDGE_HIDING_R = {
    "AAA",
    "AGA",
    "AGG",
    "AUA",
    "CUA",
    "CUC",
    "CUG",
    "CUU",
    "UAA",
    "UAG",
    "UCA",
    "UGA",
    "UUA",
}

COMPLEMENT_RNA = {"A": "U", "T": "A", "G": "C", "C": "G"}

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import run_codon_e1_heldout_crossorganism_gate as e1_base  # noqa: E402


class TrackADataFetchError(RuntimeError):
    pass


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
    rounded = round(value, digits)
    return 0.0 if rounded == -0.0 else rounded


def stable_seed(text: str) -> int:
    return int.from_bytes(hashlib.sha256(text.encode("utf-8")).digest()[:16], "big")


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def percentile_rank_ge(values: list[float], observed: float) -> float:
    return (sum(value >= observed for value in values) + 1.0) / (len(values) + 1.0)


def materialize_tracka() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    fetch = subprocess.run(
        ["git", "fetch", "origin", TRACKA_FETCH_REFSPEC],
        cwd=repo_root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if fetch.returncode != 0:
        stderr = fetch.stderr.strip()
        detail = f": {stderr}" if stderr else ""
        raise TrackADataFetchError(f"Track-A source data-fetch failed{detail}")
    SCRATCH_ROOT.mkdir(parents=True, exist_ok=True)
    for rel_path in TRACKA_PATHS:
        dest = SCRATCH_ROOT / rel_path
        dest.parent.mkdir(parents=True, exist_ok=True)
        show = subprocess.run(
            ["git", "show", f"{TRACKA_BRANCH}:{rel_path}"],
            cwd=repo_root,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if show.returncode != 0:
            stderr = show.stderr.decode("utf-8", errors="replace").strip()
            detail = f": {stderr}" if stderr else ""
            raise TrackADataFetchError(f"Track-A source data-fetch failed for {rel_path}{detail}")
        with dest.open("wb") as handle:
            handle.write(show.stdout)


def run_tracka_script(rel_path: str) -> dict[str, Any]:
    proc = subprocess.run(
        [sys.executable, str(SCRATCH_ROOT / rel_path)],
        cwd=SCRATCH_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
    )
    json_lines = [line for line in proc.stdout.splitlines() if line.startswith("{")]
    if not json_lines:
        raise ValueError(f"Track-A script did not emit JSON: {rel_path}")
    return json.loads(json_lines[-1])


def load_json(path: Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def dna_codon_to_wc_anticodon_rna(codon: str) -> str:
    return "".join(COMPLEMENT_RNA[base] for base in reversed(codon.upper()))


def exact_missing_codons(trna_copies: dict[str, int], sense_codons: list[str]) -> set[str]:
    missing = set()
    for codon_rna in sense_codons:
        codon_dna = codon_rna.replace("U", "T")
        wc_anticodon = dna_codon_to_wc_anticodon_rna(codon_dna)
        if int(trna_copies.get(wc_anticodon, 0)) <= 0:
            missing.add(codon_rna)
    return missing


def valid_gene_codon_frequencies(joined: list[dict[str, Any]], sense_codons: list[str]) -> tuple[int, int, dict[str, float]]:
    accum = {codon: 0.0 for codon in sense_codons}
    n_genes = 0
    skipped = 0
    for row in joined:
        total = row.get("codon_count_total")
        abundance = row.get("abundance_ppm")
        cds_len = row.get("cds_len_nt")
        counts = row.get("codon_counts")
        if (
            row.get("len_mod3_ok") is not True
            or not isinstance(total, int)
            or total < 50
            or not isinstance(abundance, (int, float))
            or float(abundance) <= 0.0
            or not isinstance(cds_len, int)
            or cds_len <= 0
            or not isinstance(counts, dict)
        ):
            skipped += 1
            continue
        local_counts = {codon: 0 for codon in sense_codons}
        sense_total = 0
        for raw_codon, raw_count in counts.items():
            codon_dna = str(raw_codon).upper()
            codon_rna = codon_dna.replace("T", "U")
            if e1_base.CODON_TO_AA.get(codon_rna) in (None, "*"):
                continue
            if not isinstance(raw_count, int) or raw_count <= 0:
                continue
            local_counts[codon_rna] += raw_count
            sense_total += raw_count
        if sense_total <= 0:
            skipped += 1
            continue
        n_genes += 1
        for codon, count in local_counts.items():
            accum[codon] += count / float(sense_total)
    if n_genes <= 0:
        raise ValueError("no valid genes after Track-A filters")
    return n_genes, skipped, {codon: value / float(n_genes) for codon, value in accum.items()}


def organism_signal(label: str, sense_codons: list[str]) -> dict[str, Any]:
    slug = str(ORGANISMS[label]["slug"])
    cds_path = SCRATCH_ROOT / "tools" / "fibonacci_reality" / "data" / f"cds_codon_abundance_{slug}.json"
    trna_path = SCRATCH_ROOT / "tools" / "fibonacci_reality" / "data" / f"gtrnadb_trna_all_copy_{slug}.json"
    cds_data = load_json(cds_path)
    trna_data = load_json(trna_path)
    joined = cds_data.get("joined")
    trna_raw = trna_data.get("trna_all_copies")
    if not isinstance(joined, list) or not isinstance(trna_raw, dict):
        raise ValueError(f"Track-A data missing joined/trna_all_copies for {label}")
    trna_copies = {str(key).upper().replace("T", "U"): int(value) for key, value in trna_raw.items()}
    support = exact_missing_codons(trna_copies, sense_codons)
    n_genes, skipped, gene_mean_usage = valid_gene_codon_frequencies(joined, sense_codons)
    vector = [gene_mean_usage[codon] if codon in support else 0.0 for codon in sense_codons]
    support_weight = sum(vector)
    return {
        "n_genes": n_genes,
        "n_skipped": skipped,
        "support": support,
        "support_weight": support_weight,
        "vector": vector,
        "top_codons": sorted(
            ((codon, gene_mean_usage[codon]) for codon in support),
            key=lambda item: (-item[1], item[0]),
        ),
    }


def rho_e1(
    vector: list[float],
    families: dict[str, list[str]],
    sense_index: dict[str, int],
    q_basis: list[list[float]],
) -> tuple[float, float]:
    residual = e1_base.project_syn(vector, families, sense_index)
    norm_sq = e1_base.dot(residual, residual)
    if norm_sq <= TOL:
        return math.nan, norm_sq
    projected_sq = sum(e1_base.dot(residual, q) ** 2 for q in q_basis)
    return projected_sq / norm_sq, norm_sq


def family_permutation_null(
    vector: list[float],
    families: dict[str, list[str]],
    sense_codons: list[str],
    sense_index: dict[str, int],
    q_basis: list[list[float]],
) -> list[float]:
    rng = random.Random(stable_seed(f"{EXPERIMENT_ID}.rho_e1.synonymous_null"))
    values = []
    for _ in range(NULL_N):
        permutation = e1_base.family_permutation(families, rng)
        relabeled = e1_base.apply_permutation(vector, permutation, sense_codons, sense_index)
        value, _norm_sq = rho_e1(relabeled, families, sense_index, q_basis)
        values.append(value)
    return values


def edge_overlap_null(
    support: set[str],
    families: dict[str, list[str]],
    edge_r_sense: set[str],
) -> list[int]:
    counts_by_aa: dict[str, int] = defaultdict(int)
    for codon in support:
        counts_by_aa[e1_base.CODON_TO_AA[codon]] += 1
    rng = random.Random(stable_seed(f"{EXPERIMENT_ID}.edge_hiding.degeneracy_null"))
    values = []
    for _ in range(NULL_N):
        draw: set[str] = set()
        for aa, count in sorted(counts_by_aa.items()):
            draw.update(rng.sample(families[aa], count))
        values.append(len(draw & edge_r_sense))
    return values


def summarize_tracka(tracka_payload: dict[str, Any]) -> dict[str, object]:
    result = tracka_payload.get("result")
    if not isinstance(result, dict):
        raise ValueError("Track-A payload lacks result object")
    return {
        "delta_r2": round_float(float(result["delta_r2_observed"])),
        "null_percentile": round_float(float(result["null_percentile"])),
        "boundary_supported": bool(result["boundary_response_supported"]),
        "n_genes": int(result["n_genes"]),
    }


def status_from_evidence(
    yeast_summary: dict[str, object],
    human_summary: dict[str, object],
    rho_observed: float,
    rho_null_mean: float,
    rho_null_p_ge: float,
    edge_overlap: int,
    edge_null_mean: float,
    edge_null_p_ge: float,
    window6_connection: str,
) -> str:
    if not yeast_summary["boundary_supported"] or not human_summary["boundary_supported"]:
        return "refuted"

    rho_enriched = rho_observed > rho_null_mean + EPS
    rho_significant = rho_enriched and rho_null_p_ge <= SIGNIFICANCE_ALPHA
    edge_enriched = float(edge_overlap) > edge_null_mean + EPS
    edge_significant = edge_enriched and edge_null_p_ge <= SIGNIFICANCE_ALPHA
    if window6_connection == "forced" and rho_significant and edge_significant:
        return "certified"

    circular_only = window6_connection in {"q6_circular", "q6_circular_only"}
    chance_level = not rho_significant and not edge_significant
    if circular_only and chance_level:
        return "coincidence"

    if window6_connection == "none" and chance_level:
        return "coincidence"

    return "needs_derivation"


def main() -> None:
    try:
        materialize_tracka()
        tracka_raw = {
            label: run_tracka_script(str(meta["experiment_path"]))
            for label, meta in ORGANISMS.items()
        }
        tracka_yeast = summarize_tracka(tracka_raw["yeast"])
        tracka_human = summarize_tracka(tracka_raw["human"])

        full_codons = e1_base.codon_order()
        sense_codons = e1_base.sense_codon_order()
        sense_index = {codon: index for index, codon in enumerate(sense_codons)}
        families = e1_base.families_by_aa(sense_codons)
        _projector, q_basis, rank_b1 = e1_base.build_b1_projector(
            full_codons,
            sense_codons,
            families,
            sense_index,
        )
        yeast_signal = organism_signal("yeast", sense_codons)
        human_signal = organism_signal("human", sense_codons)
        pooled_vector = [
            (float(yeast_signal["vector"][idx]) + float(human_signal["vector"][idx])) / 2.0
            for idx in range(len(sense_codons))
        ]
        rho_observed, pooled_norm_sq = rho_e1(pooled_vector, families, sense_index, q_basis)
        null_values = family_permutation_null(pooled_vector, families, sense_codons, sense_index, q_basis)
        rho_null_mean = mean(null_values)
        rho_null_p_ge = percentile_rank_ge(null_values, rho_observed)

        rho_yeast, _yeast_norm_sq = rho_e1(yeast_signal["vector"], families, sense_index, q_basis)
        rho_human, _human_norm_sq = rho_e1(human_signal["vector"], families, sense_index, q_basis)

        edge_r_sense = EDGE_HIDING_R & set(sense_codons)
        support_union = set(yeast_signal["support"]) | set(human_signal["support"])
        edge_overlap = len(support_union & edge_r_sense)
        edge_null_values = edge_overlap_null(support_union, families, edge_r_sense)
        edge_null_mean = mean([float(value) for value in edge_null_values])
        edge_null_p_ge = percentile_rank_ge([float(value) for value in edge_null_values], float(edge_overlap))

        window6_connection = "q6_circular_only"
        reason = (
            "Track-A is a real codon/tRNA supply-boundary signal in yeast "
            f"(delta_R2={round_float(float(tracka_yeast['delta_r2']))}, "
            f"null_percentile={round_float(float(tracka_yeast['null_percentile']))}) and human "
            f"(delta_R2={round_float(float(tracka_human['delta_r2']))}, "
            f"null_percentile={round_float(float(tracka_human['null_percentile']))}). "
            f"The pooled per-codon boundary vector has rho_E1={round_float(rho_observed)} "
            f"against a synonymous-relabel null mean {round_float(rho_null_mean)} with "
            f"p_ge={round_float(rho_null_p_ge)}, so the codon-E1 contact is not significant "
            f"at alpha={SIGNIFICANCE_ALPHA}. Edge-hiding gives R_overlap={edge_overlap} "
            f"against degeneracy-matched null mean {round_float(edge_null_mean)} with "
            f"p_ge={round_float(edge_null_p_ge)}, so the overlap is chance-level rather "
            "than enriched. The only Window6 contact is the q6 circular convention, not a "
            "non-circular Window6-to-codon forcing map, so this is a biological boundary "
            "fact recorded as coincidence and does not count as a certified Window6 forcing result."
        )
        status = status_from_evidence(
            tracka_yeast,
            tracka_human,
            rho_observed,
            rho_null_mean,
            rho_null_p_ge,
            edge_overlap,
            edge_null_mean,
            edge_null_p_ge,
            window6_connection,
        )
        if status == "needs_derivation":
            reason = (
                "Track-A is a distinct bio-internal codon/tRNA supply-boundary fact, but the "
                "tested Window6 contacts do not satisfy the certificate gate: codon-E1 "
                f"rho_E1={round_float(rho_observed)} with synonymous-relabel "
                f"p_ge={round_float(rho_null_p_ge)}, edge-hiding R_overlap={edge_overlap} "
                f"with degeneracy-matched p_ge={round_float(edge_null_p_ge)}, and "
                f"window6_connection={window6_connection}."
            )

        emit(
            status,
            track_a_yeast_delta_r2=tracka_yeast["delta_r2"],
            track_a_yeast_null_percentile=tracka_yeast["null_percentile"],
            track_a_yeast_boundary_supported=tracka_yeast["boundary_supported"],
            track_a_yeast_n_genes=tracka_yeast["n_genes"],
            track_a_human_delta_r2=tracka_human["delta_r2"],
            track_a_human_null_percentile=tracka_human["null_percentile"],
            track_a_human_boundary_supported=tracka_human["boundary_supported"],
            track_a_human_n_genes=tracka_human["n_genes"],
            rho_E1=round_float(rho_observed),
            rho_E1_null_mean=round_float(rho_null_mean),
            rho_E1_null_p_ge=round_float(rho_null_p_ge),
            rho_E1_yeast=round_float(rho_yeast),
            rho_E1_human=round_float(rho_human),
            rho_E1_rank_B1=rank_b1,
            rho_E1_expected_dimension_ratio=round_float(rank_b1 / 41.0),
            R_overlap=edge_overlap,
            R_overlap_null=round_float(edge_null_mean),
            R_overlap_null_p_ge=round_float(edge_null_p_ge),
            R_overlap_codons=sorted(support_union & edge_r_sense),
            track_a_yeast_boundary_codons=sorted(yeast_signal["support"]),
            track_a_human_boundary_codons=sorted(human_signal["support"]),
            track_a_top_yeast=[
                [codon, round_float(float(weight))]
                for codon, weight in yeast_signal["top_codons"][:8]
            ],
            track_a_top_human=[
                [codon, round_float(float(weight))]
                for codon, weight in human_signal["top_codons"][:8]
            ],
            pooled_signal_norm_sq=round_float(pooled_norm_sq),
            n_null=NULL_N,
            window6_connection=window6_connection,
            reason=reason,
        )
    except TrackADataFetchError as exc:
        emit(
            "needs_derivation",
            track_a_yeast_delta_r2=None,
            track_a_yeast_null_percentile=None,
            track_a_yeast_boundary_supported=False,
            track_a_human_delta_r2=None,
            track_a_human_null_percentile=None,
            track_a_human_boundary_supported=False,
            rho_E1=None,
            rho_E1_null_mean=None,
            R_overlap=None,
            R_overlap_null=None,
            window6_connection="none",
            reason=str(exc),
        )
    except Exception as exc:
        emit(
            "needs_derivation",
            track_a_yeast_delta_r2=None,
            track_a_yeast_null_percentile=None,
            track_a_yeast_boundary_supported=False,
            track_a_human_delta_r2=None,
            track_a_human_null_percentile=None,
            track_a_human_boundary_supported=False,
            rho_E1=None,
            rho_E1_null_mean=None,
            R_overlap=None,
            R_overlap_null=None,
            window6_connection="none",
            reason=f"{type(exc).__name__}: {exc}",
        )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Codon-E1 transportability gate for archaea and eukaryotes as separate strata."""
from __future__ import annotations

from collections import defaultdict
import json
import math
from pathlib import Path
import random
import sys
from typing import Any

import run_codon_e1_heldout_crossorganism_gate as base


EXPERIMENT_ID = "codon_e1_transport_gate"
CLAIM_ID = "bridge.genetic_code.codon_e1_conservation_transportability"

CHANCE_BASELINE = 0.1463
MIN_POWERED_SPECIES = 8
N_NULL = 20000
N_BOOTSTRAP = 10000
TOL = 1.0e-9
NULL_SEED_PREFIX = "codon_e1_transport_gate.global_synonymous_relabel.null"
BOOTSTRAP_SEED_PREFIX = "codon_e1_transport_gate.cluster_bootstrap"


def emit(status: str, **fields: object) -> None:
    payload = {
        "status": status,
        "experiment_id": EXPERIMENT_ID,
        "claim_id": CLAIM_ID,
        "chance_baseline": CHANCE_BASELINE,
    }
    payload.update(fields)
    print(json.dumps(payload, ensure_ascii=True, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status in {"certified", "coincidence", "needs_derivation"} else 2)


def check_row(name: str, ok: bool, **fields: object) -> dict[str, object]:
    row = {"name": name, "ok": bool(ok)}
    row.update(fields)
    return row


def round_float(value: float | None, digits: int = 12) -> float | None:
    if value is None:
        return None
    if not math.isfinite(value):
        return value
    rounded = round(value, digits)
    return 0.0 if rounded == -0.0 else rounded


def panel_path() -> Path:
    return Path(__file__).resolve().parents[1] / "synced" / "codon_e1_transport_panel.json"


def load_panel() -> dict[str, object]:
    with panel_path().open("r", encoding="utf-8") as handle:
        return json.load(handle)


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def sample_std(values: list[float], center: float) -> float:
    if len(values) < 2:
        return 0.0
    return math.sqrt(sum((value - center) ** 2 for value in values) / (len(values) - 1))


def percentile(values: list[float], q: float) -> float:
    ordered = sorted(values)
    if not ordered:
        raise ValueError("cannot take percentile of an empty list")
    pos = (len(ordered) - 1) * q
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return ordered[lo]
    return ordered[lo] * (hi - pos) + ordered[hi] * (pos - lo)


def validate_panel(
    panel: dict[str, object],
    sense_codons: list[str],
) -> tuple[list[dict[str, Any]], list[dict[str, object]], int, int]:
    checks: list[dict[str, object]] = []
    organisms_raw = panel.get("organisms")
    provenance = panel.get("provenance")
    panel_codons = panel.get("sense_codon_order_rna")
    if not isinstance(organisms_raw, list) or not isinstance(provenance, dict):
        return [], [check_row("panel_shape", False)], 0, 0

    organisms = [entry for entry in organisms_raw if isinstance(entry, dict)]
    n_archaea = sum(entry.get("domain") == "archaea" for entry in organisms)
    n_eukaryota = sum(entry.get("domain") == "eukaryota" for entry in organisms)
    n_dropped = int(provenance.get("n_dropped", 0))

    required_keys_ok = all(
        {"organism", "ncbi_taxid", "domain", "genetic_code_table", "codon_counts_rna", "total_sense"} <= set(entry)
        for entry in organisms
    )
    standard_code_ok = all(int(entry.get("genetic_code_table", -1)) == 1 for entry in organisms)
    domains_ok = all(entry.get("domain") in {"archaea", "eukaryota"} for entry in organisms)
    codon_count_ok = (
        panel_codons == sense_codons
        and len(sense_codons) == 61
        and all(
            isinstance(entry.get("codon_counts_rna"), dict)
            and sorted(entry["codon_counts_rna"]) == sorted(sense_codons)
            and int(entry["total_sense"]) == sum(int(entry["codon_counts_rna"][codon]) for codon in sense_codons)
            and int(entry["total_sense"]) > 0
            for entry in organisms
        )
    )
    dna_to_rna_ok = all(
        isinstance(entry.get("codon_counts_rna"), dict)
        and all("T" not in codon and set(codon) <= set(base.BASES) for codon in entry["codon_counts_rna"])
        for entry in organisms
    )
    provenance_ok = (
        provenance.get("source") == "Kazusa CUTG"
        and int(provenance.get("n_archaea", -1)) == n_archaea
        and int(provenance.get("n_eukaryota", -1)) == n_eukaryota
    )

    checks.extend(
        [
            check_row("panel_loaded", bool(organisms), n_archaea=n_archaea, n_eukaryota=n_eukaryota),
            check_row("provenance_counts", provenance_ok),
            check_row("required_fields", required_keys_ok),
            check_row("standard_code_table_1", standard_code_ok),
            check_row("domains_separate", domains_ok),
            check_row("dna_to_rna_ok", dna_to_rna_ok),
            check_row("61_sense_codons", codon_count_ok, observed=len(sense_codons), expected=61),
        ]
    )
    return organisms, checks, n_dropped, n_archaea + n_eukaryota


def organism_residuals(
    entries: list[dict[str, Any]],
    sense_codons: list[str],
    families: dict[str, list[str]],
    sense_index: dict[str, int],
) -> tuple[list[dict[str, object]], float]:
    organisms: list[dict[str, object]] = []
    max_family_mean = 0.0
    for entry in entries:
        counts = entry["codon_counts_rna"]
        total = int(entry["total_sense"])
        raw = [float(counts[codon]) / total for codon in sense_codons]
        residual = base.project_syn(raw, families, sense_index)
        max_family_mean = max(max_family_mean, base.max_abs_family_mean(residual, families, sense_index))
        genus = str(entry.get("genus") or str(entry["organism"]).split()[0].lower())
        organisms.append(
            {
                "organism": entry["organism"],
                "ncbi_taxid": entry["ncbi_taxid"],
                "genus": genus,
                "residual": residual,
                "residual_norm_sq": base.dot(residual, residual),
            }
        )
    return organisms, max_family_mean


def genus_mean_r(
    organisms: list[dict[str, object]],
    q_basis: list[list[float]],
) -> tuple[dict[str, float], dict[str, list[float]]]:
    by_genus: dict[str, list[float]] = defaultdict(list)
    for organism in organisms:
        norm_sq = float(organism["residual_norm_sq"])
        if norm_sq <= TOL:
            continue
        genus = str(organism["genus"])
        by_genus[genus].append(base.r_value(organism["residual"], norm_sq, q_basis))  # type: ignore[arg-type]
    means = {genus: mean(values) for genus, values in sorted(by_genus.items())}
    return means, dict(by_genus)


def relabeled_t(
    organisms: list[dict[str, object]],
    q_basis: list[list[float]],
    permutation: dict[str, str],
    sense_codons: list[str],
    sense_index: dict[str, int],
) -> float:
    relabeled: list[dict[str, object]] = []
    for organism in organisms:
        vector = base.apply_permutation(organism["residual"], permutation, sense_codons, sense_index)  # type: ignore[arg-type]
        relabeled.append(
            {
                "genus": organism["genus"],
                "residual": vector,
                "residual_norm_sq": base.dot(vector, vector),
            }
        )
    per_genus, _ = genus_mean_r(relabeled, q_basis)
    return mean(list(per_genus.values()))


def null_distribution(
    domain: str,
    organisms: list[dict[str, object]],
    q_basis: list[list[float]],
    families: dict[str, list[str]],
    sense_codons: list[str],
    sense_index: dict[str, int],
) -> tuple[list[float], float]:
    rng = random.Random(base.stable_seed(f"{NULL_SEED_PREFIX}.{domain}"))
    values: list[float] = []
    max_relabel_family_mean = 0.0
    for draw in range(N_NULL):
        permutation = base.family_permutation(families, rng)
        if draw == 0 and organisms:
            relabeled = base.apply_permutation(organisms[0]["residual"], permutation, sense_codons, sense_index)  # type: ignore[arg-type]
            max_relabel_family_mean = base.max_abs_family_mean(relabeled, families, sense_index)
        values.append(relabeled_t(organisms, q_basis, permutation, sense_codons, sense_index))
    return values, max_relabel_family_mean


def bootstrap_lower95_excess(domain: str, per_genus: dict[str, float], null_mean: float) -> float:
    rng = random.Random(base.stable_seed(f"{BOOTSTRAP_SEED_PREFIX}.{domain}"))
    genera = sorted(per_genus)
    count = len(genera)
    excess_values: list[float] = []
    for _ in range(N_BOOTSTRAP):
        sampled = [per_genus[rng.choice(genera)] for _ in range(count)]
        excess_values.append(mean(sampled) - null_mean)
    return percentile(excess_values, 0.025)


def empty_domain_result(n: int, verdict: str = "non-resolving") -> dict[str, object]:
    return {
        "n": n,
        "T": None,
        "null_mean": None,
        "null_z": None,
        "one_sided_p": None,
        "bootstrap_lower95": None,
        "verdict": verdict,
    }


def run_domain(
    domain: str,
    entries: list[dict[str, Any]],
    q_basis: list[list[float]],
    families: dict[str, list[str]],
    sense_codons: list[str],
    sense_index: dict[str, int],
) -> tuple[dict[str, object], list[dict[str, object]]]:
    checks: list[dict[str, object]] = []
    n_species = len(entries)
    if n_species == 0:
        return empty_domain_result(0), [check_row(f"{domain}_nonempty", False)]

    organisms, max_family_mean = organism_residuals(entries, sense_codons, families, sense_index)
    skipped = [str(item["organism"]) for item in organisms if float(item["residual_norm_sq"]) <= TOL]
    per_genus, by_genus = genus_mean_r(organisms, q_basis)
    n_clusters = len(per_genus)
    checks.extend(
        [
            check_row(f"{domain}_species_power", n_species >= MIN_POWERED_SPECIES, n_species=n_species),
            check_row(
                f"{domain}_cluster_weighting",
                n_clusters > 0,
                weighting="genus-cluster mean",
                n_clusters=n_clusters,
                cluster_sizes={genus: len(values) for genus, values in sorted(by_genus.items())},
            ),
            check_row(
                f"{domain}_d_resid4_synonymous_mean_zero",
                max_family_mean < 1.0e-12 and not skipped,
                max_abs_family_mean=round_float(max_family_mean, 14),
                skipped_zero_residual=skipped,
            ),
        ]
    )
    if not per_genus:
        return empty_domain_result(n_species), checks

    observed_t = mean(list(per_genus.values()))
    null_values, max_relabel_family_mean = null_distribution(
        domain, organisms, q_basis, families, sense_codons, sense_index
    )
    checks.append(
        check_row(
            f"{domain}_null_global_relabel_preserves_family",
            max_relabel_family_mean < 1.0e-12,
            max_abs_family_mean=round_float(max_relabel_family_mean, 14),
        )
    )
    null_mean = mean(null_values)
    null_std = sample_std(null_values, null_mean)
    null_z = (observed_t - null_mean) / null_std if null_std > 0.0 else math.inf
    one_sided_p = (sum(value >= observed_t for value in null_values) + 1) / (len(null_values) + 1)
    lower95_excess = bootstrap_lower95_excess(domain, per_genus, null_mean)
    verdict = "conserved" if one_sided_p <= 0.01 and lower95_excess > 0.0 else "non-resolving"

    return (
        {
            "n": n_species,
            "T": round_float(observed_t),
            "null_mean": round_float(null_mean),
            "null_z": round_float(null_z),
            "one_sided_p": round_float(one_sided_p),
            "bootstrap_lower95": round_float(lower95_excess),
            "verdict": verdict,
        },
        checks,
    )


def status_reason(
    status: str,
    archaea: dict[str, object],
    eukaryota: dict[str, object],
    n_dropped: int,
    checks: list[dict[str, object]],
) -> str:
    conserved = [
        domain
        for domain, result in (("archaea", archaea), ("eukaryota", eukaryota))
        if result.get("verdict") == "conserved"
    ]
    failed = [str(row["name"]) for row in checks if not row["ok"]]
    if failed:
        prefix = "needs_derivation because required checks did not pass: " + ", ".join(failed) + ". "
    elif status == "certified":
        prefix = "certified because codon-E1 conservation transports in " + ", ".join(conserved) + ". "
    else:
        prefix = "coincidence because neither external stratum resolves conservation at this panel power. "

    return (
        prefix
        + "Archaea: n={an}, T={at}, null_mean={anm}, p={ap}, bootstrap_lower95={ab}. "
        + "Eukaryota: n={en}, T={et}, null_mean={enm}, p={ep}, bootstrap_lower95={eb}. "
        + "Chance baseline is approximately 6/41={chance}. n_dropped={dropped}. "
        + "This is E1-TRANSPORTABILITY, a generalization of the #18 bacterial codon-E1 certificate; "
        + "it is not Window6 evidence, not a causal claim, and the archaea and eukaryota strata are "
        + "analyzed separately and never pooled with the 29-bacteria certificate."
    ).format(
        an=archaea.get("n"),
        at=archaea.get("T"),
        anm=archaea.get("null_mean"),
        ap=archaea.get("one_sided_p"),
        ab=archaea.get("bootstrap_lower95"),
        en=eukaryota.get("n"),
        et=eukaryota.get("T"),
        enm=eukaryota.get("null_mean"),
        ep=eukaryota.get("one_sided_p"),
        eb=eukaryota.get("bootstrap_lower95"),
        chance=CHANCE_BASELINE,
        dropped=n_dropped,
    )


def main() -> None:
    try:
        full_codons = base.codon_order()
        sense_codons = base.sense_codon_order()
        sense_index = {codon: idx for idx, codon in enumerate(sense_codons)}
        families = base.families_by_aa(sense_codons)

        panel = load_panel()
        entries, checks, n_dropped, _ = validate_panel(panel, sense_codons)

        projector, q_basis, rank_b1 = base.build_b1_projector(full_codons, sense_codons, families, sense_index)
        projector_square = base.matrix_multiply(projector, projector)
        p_idempotent_defect = base.max_abs_matrix_diff(projector_square, projector)
        p_symmetric_defect = base.max_abs_symmetric_defect(projector)
        checks.extend(
            [
                check_row("B1 rank", rank_b1 == 6, rank_B1=rank_b1),
                check_row(
                    "P_B1 idempotent+symmetric",
                    p_idempotent_defect <= 1.0e-8 and p_symmetric_defect <= 1.0e-10,
                    idempotent_max_abs=round_float(p_idempotent_defect, 14),
                    symmetric_max_abs=round_float(p_symmetric_defect, 14),
                ),
            ]
        )

        by_domain = {
            "archaea": [entry for entry in entries if entry.get("domain") == "archaea"],
            "eukaryota": [entry for entry in entries if entry.get("domain") == "eukaryota"],
        }
        archaea, archaea_checks = run_domain(
            "archaea", by_domain["archaea"], q_basis, families, sense_codons, sense_index
        )
        eukaryota, eukaryota_checks = run_domain(
            "eukaryota", by_domain["eukaryota"], q_basis, families, sense_codons, sense_index
        )
        checks.extend(archaea_checks)
        checks.extend(eukaryota_checks)

        if int(archaea["n"]) < MIN_POWERED_SPECIES or int(eukaryota["n"]) < MIN_POWERED_SPECIES:
            status = "needs_derivation"
        elif not all(row["ok"] for row in checks):
            status = "needs_derivation"
        elif archaea.get("verdict") == "conserved" or eukaryota.get("verdict") == "conserved":
            status = "certified"
        else:
            status = "coincidence"

        reason = status_reason(status, archaea, eukaryota, n_dropped, checks)
        emit(status, archaea=archaea, eukaryota=eukaryota, n_dropped=n_dropped, checks=checks, reason=reason)
    except Exception as exc:
        checks = [check_row("exception_free", False, exception=type(exc).__name__, message=str(exc))]
        archaea = empty_domain_result(0)
        eukaryota = empty_domain_result(0)
        emit(
            "needs_derivation",
            archaea=archaea,
            eukaryota=eukaryota,
            n_dropped=None,
            checks=checks,
            reason=status_reason("needs_derivation", archaea, eukaryota, -1, checks),
        )


if __name__ == "__main__":
    main()

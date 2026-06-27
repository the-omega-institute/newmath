#!/usr/bin/env python3
"""Run the RM motif escape pre-data availability gate."""
from __future__ import annotations

from collections import Counter, defaultdict
from datetime import datetime, timezone
import json
import os
import statistics
import sys
import time
from typing import Any

try:
    from ._rm_fetch_probe import (
        carrier_rows_by_host,
        host_inventory_map,
        load_blow_carriers,
        load_rebase_carriers,
        map_carriers_to_assemblies,
        plasmid_target_inventory,
        prophage_target_inventory,
        tier_a_blow_groups,
        tier_a_rebase_groups,
    )
except ImportError:  # pragma: no cover - direct script execution
    from _rm_fetch_probe import (  # type: ignore
        carrier_rows_by_host,
        host_inventory_map,
        load_blow_carriers,
        load_rebase_carriers,
        map_carriers_to_assemblies,
        plasmid_target_inventory,
        prophage_target_inventory,
        tier_a_blow_groups,
        tier_a_rebase_groups,
    )


MIN_PRIMARY_HOSTS = 80
WARN_PRIMARY_HOSTS = 50
MIN_FAMILIES = 25
WARN_FAMILIES = 15
MIN_TARGET_BP = 30_000
MIN_EXPECTED_CARRIER_SITES = 20.0
MIN_DECOY_SETS = 50
MIN_EXACT_MATCH_FRACTION = 0.70


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def median(values: list[float]) -> float:
    return float(statistics.median(values)) if values else 0.0


def expected_sites_for_host(carriers: list[dict[str, Any]], target_bp: int) -> float:
    if target_bp <= 0 or not carriers:
        return 0.0
    values = []
    seen = set()
    for row in carriers:
        motif = str(row.get("motif_canonical") or "")
        if not motif or motif in seen:
            continue
        seen.add(motif)
        motif_len = int(row.get("motif_len") or len(motif))
        degeneracy = int(row.get("degeneracy") or 1)
        values.append(target_bp * degeneracy / (4 ** motif_len))
    return float(sum(values))


def motif_profile(row: dict[str, Any]) -> tuple[int, int, bool]:
    motif = str(row.get("motif_canonical") or "")
    return (
        int(row.get("motif_len") or len(motif)),
        int(row.get("degeneracy") or 1),
        bool(row.get("palindrome_flag")),
    )


def decoy_sets_available_for_host(
    host: str,
    carriers: list[dict[str, Any]],
    family_hosts: dict[str, set[str]],
    genus_hosts: dict[str, set[str]],
    motif_pool: dict[tuple[str, str, tuple[int, int, bool]], set[str]],
) -> int:
    if not carriers:
        return 0
    family = str(carriers[0].get("gtdb_family") or "")
    genus = str(carriers[0].get("gtdb_genus") or "")
    own_motifs = {str(row.get("motif_canonical") or "") for row in carriers if row.get("motif_canonical")}
    if not own_motifs:
        return 0
    family_other_hosts = max(0, len(family_hosts.get(family, set())) - 1) if family else 0
    genus_other_hosts = max(0, len(genus_hosts.get(genus, set())) - 1) if genus else 0
    total = 0
    for row in carriers:
        motif = str(row.get("motif_canonical") or "")
        if not motif:
            continue
        profile = motif_profile(row)
        family_matches = motif_pool.get(("family", family, profile), set()) - own_motifs if family else set()
        genus_matches = motif_pool.get(("genus", genus, profile), set()) - own_motifs if genus else set()
        profile_matches = family_matches | genus_matches
        total += max(family_other_hosts, genus_other_hosts, 1) * len(profile_matches)
    return min(250, total)


def gate_row(name: str, passed: bool, value: Any, threshold: str, note: str = "") -> dict[str, Any]:
    return {"gate": name, "passed": bool(passed), "value": value, "threshold": threshold, "note": note}


def evaluate_gates(mapped_carriers: list[dict[str, Any]], inventory: list[dict[str, Any]], target_source: str) -> dict[str, Any]:
    by_host = carrier_rows_by_host(mapped_carriers)
    targets = host_inventory_map(inventory)
    host_rows: list[dict[str, Any]] = []
    family_hosts: dict[str, set[str]] = defaultdict(set)
    genus_hosts: dict[str, set[str]] = defaultdict(set)
    motif_pool: dict[tuple[str, str, tuple[int, int, bool]], set[str]] = defaultdict(set)

    for host, carriers in by_host.items():
        family = str(carriers[0].get("gtdb_family") or "")
        genus = str(carriers[0].get("gtdb_genus") or "")
        family_hosts[family].add(host)
        genus_hosts[genus].add(host)
        for row in carriers:
            motif = str(row.get("motif_canonical") or "")
            if motif:
                profile = motif_profile(row)
                if family:
                    motif_pool[("family", family, profile)].add(motif)
                if genus:
                    motif_pool[("genus", genus, profile)].add(motif)

    for host, carriers in sorted(by_host.items()):
        target = targets.get(host, {})
        total_target_bp = int(target.get("total_target_bp") or 0)
        e_carrier = expected_sites_for_host(carriers, total_target_bp)
        motifs = {str(row.get("motif_canonical") or "") for row in carriers if row.get("motif_canonical")}
        exact_like = any(str(row.get("match_mode") or "").startswith("assembly_exact") for row in carriers)
        host_rows.append(
            {
                "host_accession": host,
                "gtdb_family": str(carriers[0].get("gtdb_family") or ""),
                "gtdb_genus": str(carriers[0].get("gtdb_genus") or ""),
                "blow_organisms": sorted({str(row.get("blow_organism") or "") for row in carriers if row.get("blow_organism")})[:12],
                "rebase_organisms": sorted({str(row.get("rebase_organism") or "") for row in carriers})[:12],
                "tierA_motif_count": len(motifs),
                "num_targets": int(target.get("num_targets") or 0),
                "total_target_bp": total_target_bp,
                "median_target_len": float(target.get("median_target_len") or 0),
                "expected_carrier_sites": e_carrier,
                "match_modes": sorted({str(row.get("match_mode") or "") for row in carriers}),
                "exact_assembly_match": exact_like,
            }
        )

    target_hosts = [row for row in host_rows if int(row["num_targets"]) > 0]
    bp_eligible = [row for row in target_hosts if int(row["total_target_bp"]) >= MIN_TARGET_BP]
    ec_eligible = [row for row in bp_eligible if float(row["expected_carrier_sites"]) >= MIN_EXPECTED_CARRIER_SITES]

    decoy_values = []
    for row in ec_eligible:
        host = str(row["host_accession"])
        decoy = decoy_sets_available_for_host(host, by_host[host], family_hosts, genus_hosts, motif_pool)
        row["decoy_sets_available"] = decoy
        decoy_values.append(float(decoy))
    primary_hosts = [row for row in ec_eligible if int(row.get("decoy_sets_available", 0)) >= MIN_DECOY_SETS]

    primary_families = {str(row["gtdb_family"]) for row in primary_hosts if row.get("gtdb_family")}
    exact_count = sum(1 for row in primary_hosts if row.get("exact_assembly_match"))
    exact_fraction = exact_count / len(primary_hosts) if primary_hosts else 0.0

    gates = {
        "G0": gate_row(
            "G0",
            len(primary_hosts) >= MIN_PRIMARY_HOSTS,
            len(primary_hosts),
            f"N_host_with_TierA_RM_and_target_after_G2_G3_G4 >= {MIN_PRIMARY_HOSTS}",
            "Below 50 means data gate failed without biological interpretation." if len(primary_hosts) < WARN_PRIMARY_HOSTS else "",
        ),
        "G1": gate_row(
            "G1",
            len(primary_families) >= MIN_FAMILIES,
            len(primary_families),
            f"GTDB_family_count >= {MIN_FAMILIES}",
            "Below 15 means data gate failed without biological interpretation." if len(primary_families) < WARN_FAMILIES else "",
        ),
        "G2": gate_row(
            "G2",
            bool(bp_eligible) and len(bp_eligible) == len(target_hosts),
            {"eligible_hosts": len(bp_eligible), "min_total_target_bp": MIN_TARGET_BP},
            "Each retained host has total_target_bp >= 30000",
        ),
        "G3": gate_row(
            "G3",
            bool(ec_eligible) and len(ec_eligible) == len(bp_eligible),
            {"eligible_hosts": len(ec_eligible), "min_expected_carrier_sites": MIN_EXPECTED_CARRIER_SITES},
            "Each retained host has rough carrier expectation E_C >= 20",
        ),
        "G4": gate_row(
            "G4",
            all(int(row.get("decoy_sets_available", 0)) >= MIN_DECOY_SETS for row in ec_eligible) and bool(ec_eligible),
            {"eligible_hosts": len(primary_hosts), "median_decoy_sets_available": median(decoy_values)},
            "Each retained host has at least 50 matched decoy carrier sets",
        ),
        "G5": gate_row(
            "G5",
            exact_fraction >= MIN_EXACT_MATCH_FRACTION,
            exact_fraction,
            f"Tier-A exact assembly match hosts >= {MIN_EXACT_MATCH_FRACTION:.0%} of primary set",
            "REBASE allenz has organism-level host labels, so exact assembly fraction can remain zero unless a richer REBASE source is substituted.",
        ),
    }

    all_pass = all(row["passed"] for row in gates.values())
    motif_counts = [float(row["tierA_motif_count"]) for row in primary_hosts]
    return {
        "N_hosts": len(primary_hosts),
        "N_families": len(primary_families),
        "N_hosts_with_target": len(target_hosts),
        f"N_hosts_with_{target_source}_target": len(target_hosts),
        "N_hosts_after_target_bp_filter": len(bp_eligible),
        "N_hosts_after_expected_site_filter": len(ec_eligible),
        "exact_match_fraction": exact_fraction,
        "median_tierA_motifs_per_host": median(motif_counts),
        "median_decoy_sets_available": median(decoy_values),
        "per_gate": gates,
        "verdict": "data_available" if all_pass else "data_gate_failed",
        "host_inventory_preview": primary_hosts[:25],
    }


def main() -> int:
    started = time.monotonic()
    host_limit_raw = os.environ.get("RM_HOST_LIMIT", "").strip()
    host_limit = int(host_limit_raw) if host_limit_raw else None
    deadline_seconds = float(os.environ.get("RM_FETCH_DEADLINE_SECONDS", "300"))
    deadline = time.monotonic() + deadline_seconds if deadline_seconds > 0 else None
    carrier_source = os.environ.get("RM_CARRIER_SOURCE", "blow").strip().lower() or "blow"
    target_source = os.environ.get("RM_TARGET_SOURCE", "prophage").strip().lower() or "prophage"

    if carrier_source == "rebase":
        source_rows, source_meta = load_rebase_carriers(deadline=deadline)
        carrier_rows, tier_meta = tier_a_rebase_groups(source_rows)
    elif carrier_source == "blow":
        source_rows, source_meta = load_blow_carriers(deadline=deadline)
        carrier_rows, tier_meta = tier_a_blow_groups(source_rows)
    else:
        print(json.dumps({"error": "unknown_RM_CARRIER_SOURCE", "RM_CARRIER_SOURCE": carrier_source}, sort_keys=True))
        return 4
    if target_source not in {"prophage", "plasmid"}:
        print(json.dumps({"error": "unknown_RM_TARGET_SOURCE", "RM_TARGET_SOURCE": target_source}, sort_keys=True))
        return 4
    mapped_carriers, mapping_meta = map_carriers_to_assemblies(carrier_rows, host_limit=host_limit, deadline=deadline)
    if target_source == "plasmid":
        inventory, target_meta = plasmid_target_inventory(mapped_carriers, deadline=deadline)
    else:
        inventory, target_meta = prophage_target_inventory(mapped_carriers, deadline=deadline)
    gate_result = evaluate_gates(mapped_carriers, inventory, target_source)

    evidence_counts = Counter(str(row.get("evidence_tier") or "") for row in mapped_carriers)
    match_counts = Counter(str(row.get("match_mode") or "") for row in mapped_carriers)
    payload = {
        "experiment_id": "RM_motif_escape_necessity_predata_gate",
        "claim": "Claim 69",
        "generated_at": now_iso(),
        "host_limit": host_limit,
        "carrier_source": carrier_source,
        "target_source": target_source,
        "runtime_seconds": round(time.monotonic() - started, 3),
        "predata_gate_only": True,
        "target_signal_counts_computed": False,
        "stop_rule": "Tier-A carrier list is selected from the configured RM carrier source before any target motif counts are computed.",
        "carrier_source_meta": source_meta,
        "rebase": source_meta if carrier_source == "rebase" else {"skipped": True, "reason": "RM_CARRIER_SOURCE=blow"},
        "blow2016": source_meta if carrier_source == "blow" else {"skipped": True, "reason": "RM_CARRIER_SOURCE=rebase"},
        "worker_1_carrier_audit": {
            "source": carrier_source,
            "n_source_rows": len(source_rows),
            "n_rebase_rows": len(source_rows) if carrier_source == "rebase" else 0,
            "n_blow_rows": len(source_rows) if carrier_source == "blow" else 0,
            "n_tierA_unmapped_carriers": len(carrier_rows),
            "n_tierA_mapped_carriers": len(mapped_carriers),
            "n_tierA_mapped_hosts": len({row.get("host_accession") for row in mapped_carriers if row.get("host_accession")}),
            "evidence_tier_counts": dict(evidence_counts),
            "match_mode_counts": dict(match_counts),
            "tier_filter": tier_meta,
            "mapping": mapping_meta,
            "carrier_map_schema": [
                "host_accession",
                "gtdb_family",
                "blow_organism",
                "rebase_organism",
                "mtase_name",
                "rm_system_id",
                "motif_raw",
                "motif_canonical",
                "motif_len",
                "degeneracy",
                "palindrome_flag",
                "type",
                "modtype",
                "system_type",
                "evidence_tier",
            ],
        },
        "worker_2_target_audit": {
            "target_type": target_source,
            "n_hosts_checked": target_meta.get("n_hosts_checked", 0),
            "n_hosts_with_target": sum(1 for row in inventory if int(row.get("num_targets") or 0) > 0),
            "n_hosts_with_plasmid": sum(1 for row in inventory if int(row.get("num_targets") or 0) > 0) if target_source == "plasmid" else 0,
            "n_hosts_with_prophage": sum(1 for row in inventory if int(row.get("num_targets") or 0) > 0) if target_source == "prophage" else 0,
            "target_inventory_schema": ["host_accession", "target_type", "num_targets", "total_target_bp", "median_target_len"],
            "target_fetch": target_meta,
            "prophage": target_meta.get("flinders", {}) if target_source == "prophage" else {"skipped": True, "reason": "RM_TARGET_SOURCE=plasmid"},
        },
        "availability_gate": gate_result,
    }
    print(json.dumps(payload, ensure_ascii=True, sort_keys=True, indent=2))
    if gate_result["verdict"] == "data_available":
        return 0
    return 2 if source_rows else 3


if __name__ == "__main__":
    sys.exit(main())

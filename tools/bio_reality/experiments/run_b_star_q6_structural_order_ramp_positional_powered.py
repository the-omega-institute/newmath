#!/usr/bin/env python3
"""Position-split f3_stress test for structural-order signal localization.

This experiment asks whether the translation-conditioned f3_stress ->
structural_order signal is concentrated in the 5' ramp window or is instead
carried by the CDS body.  For each gene with ordered CDS, TE, abundance, and
structural-order data, it computes:

    f3_ramp = f3_stress coordinate over first N sense codons
    f3_body = f3_stress coordinate over remaining sense codons

and measures held-out R2 increments after the same X3 full controls:

    translation + protein length + 20 amino-acid composition + GC3

The primary window is N=50 codons, with N=30 and N=70 sensitivity reports.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import math
import pathlib
import sys
from types import ModuleType
from typing import Any


sys.dont_write_bytecode = True

EXPERIMENT_ID = "b_star_q6_structural_order_ramp_positional_powered"
CLAIM_ID = "h3.cross_layer_relation.structural_order_ramp_positional.b_star_q6_powered"

SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
DATA_DIR = pathlib.Path("/Users/lexa/Desktop/lexa/omega/newmath/tools/bio_reality/data")
CODON_TOPOLOGY_REFS = DATA_DIR / "codon_topology_refs.py"
X3_SIBLING = SCRIPT_DIR / "run_b_star_q6_translation_conditioned_structural_order_boundary_powered.py"

FOLD_COUNT = 5
SEED = f"sha256:{hashlib.sha256(EXPERIMENT_ID.encode('utf-8')).hexdigest()}"
EPS = 1e-12
MIN_JOINED = 300
MIN_PRIMARY_ORGANISMS = 2
SIGNIFICANCE_ALPHA = 0.05
LOCALIZATION_MARGIN = 0.0005
PRIMARY_RAMP_N = 50
SENSITIVITY_RAMP_NS = [30, 50, 70]

ORGANISMS = [
    {
        "organism": "saccharomyces_cerevisiae",
        "label": "Saccharomyces cerevisiae",
    },
    {
        "organism": "escherichia_coli_k12_mg1655",
        "label": "Escherichia coli K-12 MG1655",
    },
]


def emit(status: str, **kw: object) -> None:
    payload = {"status": status, "experiment_id": EXPERIMENT_ID, "claim_id": CLAIM_ID}
    payload.update(kw)
    print(json.dumps(payload, sort_keys=False, separators=(",", ":")))
    sys.exit(0 if status == "passed" else (2 if status == "failed" else 3))


def import_module_from_path(name: str, path: pathlib.Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot import {name} from {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def stable_hash_int(text: str) -> int:
    digest = hashlib.sha256(f"{SEED}|{text}".encode("utf-8")).digest()
    return int.from_bytes(digest[:8], "big")


def deterministic_folds(rows: list[dict[str, object]], organism: str, readout: str, fold_count: int = FOLD_COUNT) -> list[int]:
    order = sorted(
        range(len(rows)),
        key=lambda idx: stable_hash_int(f"fold|{organism}|{readout}|{rows[idx]['stable_id']}|{idx}"),
    )
    folds = [0 for _ in rows]
    for rank, index in enumerate(order):
        folds[index] = rank % fold_count
    return folds


def patch_x3_seed_and_folds(x3: ModuleType) -> None:
    x3.SEED = SEED
    x3.FOLD_COUNT = FOLD_COUNT
    x3.deterministic_folds = deterministic_folds


def load_json(path: pathlib.Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def mean(values: list[float]) -> float | None:
    return None if not values else sum(values) / len(values)


def median(values: list[float]) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    mid = len(ordered) // 2
    if len(ordered) % 2:
        return ordered[mid]
    return 0.5 * (ordered[mid - 1] + ordered[mid])


def summarize_numbers(values: list[float]) -> dict[str, object]:
    return {
        "n": len(values),
        "mean": mean(values),
        "median": median(values),
        "min": min(values) if values else None,
        "max": max(values) if values else None,
        "positive_count": sum(1 for value in values if value > 0.0),
        "negative_count": sum(1 for value in values if value < 0.0),
    }


def percentile_nearest_rank(values: list[float], probability: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    index = max(0, min(len(ordered) - 1, math.ceil(probability * len(ordered)) - 1))
    return ordered[index]


def signflip_null(values: list[float]) -> dict[str, object]:
    nonzero = [abs(value) for value in values if abs(value) > EPS]
    observed_sum = sum(values)
    n = len(nonzero)
    if n == 0:
        return {
            "n_nonzero": 0,
            "observed_sum": observed_sum,
            "observed_mean": mean(values),
            "null_mean_sum": 0.0,
            "null95_sum": None,
            "null95_mean": None,
            "p_greater_zero": None,
        }
    if n > 22:
        positives = sum(1 for value in values if value > 0.0)
        p_value = sum(math.comb(n, k) for k in range(positives, n + 1)) / (2 ** n)
        return {
            "n_nonzero": n,
            "observed_sum": observed_sum,
            "observed_mean": mean(values),
            "null_mean_sum": 0.0,
            "null95_sum": None,
            "null95_mean": None,
            "p_greater_zero": p_value,
            "large_n_approximation": "binomial sign-count tail; exact magnitude enumeration skipped for n>22",
        }
    null_sums: list[float] = []
    extreme = 0
    total = 1 << n
    for mask in range(total):
        signed = 0.0
        for bit, magnitude in enumerate(nonzero):
            signed += magnitude if (mask >> bit) & 1 else -magnitude
        null_sums.append(signed)
        if signed >= observed_sum - EPS:
            extreme += 1
    null95_sum = percentile_nearest_rank(null_sums, 0.95)
    return {
        "n_nonzero": n,
        "observed_sum": observed_sum,
        "observed_mean": mean(values),
        "null_mean_sum": mean(null_sums),
        "null95_sum": null95_sum,
        "null95_mean": None if null95_sum is None else null95_sum / n,
        "p_greater_zero": extreme / total,
    }


def delta_r2(newer: dict[str, object], older: dict[str, object]) -> float | None:
    r2_new = newer.get("held_out_r2")
    r2_old = older.get("held_out_r2")
    if isinstance(r2_new, float) and isinstance(r2_old, float):
        return r2_new - r2_old
    return None


def fold_deltas(newer: dict[str, object], older: dict[str, object]) -> list[float]:
    newer_folds = newer.get("fold_metrics")
    older_folds = older.get("fold_metrics")
    if not isinstance(newer_folds, list) or not isinstance(older_folds, list):
        return []
    out: list[float] = []
    for n_item, o_item in zip(newer_folds, older_folds):
        if not isinstance(n_item, dict) or not isinstance(o_item, dict):
            continue
        n_r2 = n_item.get("held_out_r2")
        o_r2 = o_item.get("held_out_r2")
        if isinstance(n_r2, float) and isinstance(o_r2, float):
            out.append(n_r2 - o_r2)
    return out


def dna_to_rna(codon: str) -> str:
    return codon.upper().replace("T", "U")


def load_q_vectors(x3: ModuleType, codons: list[str]) -> tuple[dict[str, dict[str, float]], dict[str, object]]:
    refs_available = CODON_TOPOLOGY_REFS.exists()
    refs_has_q_vectors = False
    refs_error = None
    if refs_available:
        try:
            refs = import_module_from_path("codon_topology_refs_ramp_positional", CODON_TOPOLOGY_REFS)
            refs_has_q_vectors = hasattr(refs, "q_vectors")
            if refs_has_q_vectors:
                raw = refs.q_vectors(codons)  # type: ignore[attr-defined]
                return raw, {
                    "requested_source": str(CODON_TOPOLOGY_REFS),
                    "used_source": "codon_topology_refs.q_vectors",
                    "codon_topology_refs_present": True,
                    "codon_topology_refs_has_q_vectors": True,
                }
        except Exception as exc:  # pragma: no cover - reported in payload
            refs_error = str(exc)
    return x3.q_vectors(codons), {
        "requested_source": str(CODON_TOPOLOGY_REFS),
        "used_source": "X3 sibling embedded q_vectors fallback",
        "fallback_source": str(X3_SIBLING),
        "codon_topology_refs_present": refs_available,
        "codon_topology_refs_has_q_vectors": refs_has_q_vectors,
        "codon_topology_refs_error": refs_error,
        "fallback_note": "local codon_topology_refs.py did not expose q_vectors; using X3 f3_stress definition verbatim",
    }


def ordered_cds_index(organism: str, sense_codons: set[str]) -> tuple[dict[str, list[str]], dict[str, object]]:
    payload = load_json(DATA_DIR / f"cds_ordered_sequences_{organism}.json")
    if not isinstance(payload, dict) or not isinstance(payload.get("cds"), list):
        raise ValueError(f"{organism} ordered CDS payload malformed")
    out: dict[str, list[str]] = {}
    skipped = {
        "non_object": 0,
        "missing_gene_id": 0,
        "codons_not_list": 0,
        "empty_sense_sequence": 0,
        "duplicate_gene_id": 0,
    }
    for row_index, item in enumerate(payload["cds"]):
        if not isinstance(item, dict):
            skipped["non_object"] += 1
            continue
        gene_id = item.get("gene_id")
        raw_codons = item.get("codons")
        if not isinstance(gene_id, str) or not gene_id:
            skipped["missing_gene_id"] += 1
            continue
        if not isinstance(raw_codons, list):
            skipped["codons_not_list"] += 1
            continue
        key = gene_id.upper() if organism == "saccharomyces_cerevisiae" else gene_id
        seq = [dna_to_rna(str(codon)) for codon in raw_codons if dna_to_rna(str(codon)) in sense_codons]
        if not seq:
            skipped["empty_sense_sequence"] += 1
            continue
        if key in out:
            skipped["duplicate_gene_id"] += 1
            continue
        out[key] = seq
    return out, {
        "path": str(DATA_DIR / f"cds_ordered_sequences_{organism}.json"),
        "organism": payload.get("organism"),
        "organism_label": payload.get("organism_label"),
        "n_cds_reported": payload.get("n_cds"),
        "n_ordered_sense_sequences_indexed": len(out),
        "sha256": payload.get("sha256"),
        "source_name": payload.get("source_name"),
        "skipped_ordered_cds_records": skipped,
    }


def row_join_keys(row: dict[str, object], organism: str) -> list[str]:
    keys: list[str] = []
    for field in ["cds_match_id", "gene_key", "locus_tag"]:
        value = row.get(field)
        if isinstance(value, str) and value:
            keys.append(value)
    protein_id = row.get("protein_id")
    if isinstance(protein_id, str) and "." in protein_id:
        keys.append(protein_id.rsplit(".", 1)[-1])
    paxdb_gene_name = row.get("paxdb_gene_name")
    if isinstance(paxdb_gene_name, str) and paxdb_gene_name:
        keys.append(paxdb_gene_name)

    seen: set[str] = set()
    out: list[str] = []
    for key in keys:
        normalized = key.upper() if organism == "saccharomyces_cerevisiae" else key
        if normalized not in seen:
            out.append(normalized)
            seen.add(normalized)
    return out


def coordinate_from_sequence(seq: list[str], q: dict[str, float], codons: list[str]) -> float | None:
    counts = {codon: 0 for codon in codons}
    total = 0
    for codon in seq:
        if codon in counts:
            counts[codon] += 1
            total += 1
    if total <= 0:
        return None
    frequencies = {codon: counts[codon] / total for codon in codons}
    denom = math.sqrt(sum(q[codon] * q[codon] for codon in codons))
    if denom <= EPS:
        raise ValueError("f3_stress vector has zero norm")
    return sum(frequencies[codon] * q[codon] for codon in codons) / denom


def attach_position_f3(
    rows: list[dict[str, object]],
    *,
    organism: str,
    ordered: dict[str, list[str]],
    f3_projected: dict[str, float],
    codons: list[str],
    ramp_n: int,
) -> tuple[list[dict[str, object]], dict[str, object]]:
    out: list[dict[str, object]] = []
    skipped = {
        "missing_ordered_cds": 0,
        "duplicate_ordered_join_key": 0,
        "ramp_empty": 0,
        "body_empty": 0,
        "coordinate_failed": 0,
    }
    ramp_lengths: list[float] = []
    body_lengths: list[float] = []
    total_lengths: list[float] = []
    seen_keys: set[str] = set()

    for row in rows:
        join_key = next((key for key in row_join_keys(row, organism) if key in ordered), None)
        if join_key is None:
            skipped["missing_ordered_cds"] += 1
            continue
        if join_key in seen_keys:
            skipped["duplicate_ordered_join_key"] += 1
            continue
        seq = ordered[join_key]
        ramp_seq = seq[:ramp_n]
        body_seq = seq[ramp_n:]
        if not ramp_seq:
            skipped["ramp_empty"] += 1
            continue
        if not body_seq:
            skipped["body_empty"] += 1
            continue
        ramp_value = coordinate_from_sequence(ramp_seq, f3_projected, codons)
        body_value = coordinate_from_sequence(body_seq, f3_projected, codons)
        if ramp_value is None or body_value is None:
            skipped["coordinate_failed"] += 1
            continue
        updated = dict(row)
        updated["ordered_gene_id"] = join_key
        updated["f3_ramp"] = [ramp_value]
        updated["f3_body"] = [body_value]
        updated["f3_ramp_plus_body"] = [ramp_value, body_value]
        updated["ordered_cds_sense_codons"] = len(seq)
        updated["f3_ramp_codons"] = len(ramp_seq)
        updated["f3_body_codons"] = len(body_seq)
        out.append(updated)
        seen_keys.add(join_key)
        ramp_lengths.append(float(len(ramp_seq)))
        body_lengths.append(float(len(body_seq)))
        total_lengths.append(float(len(seq)))

    return out, {
        "ramp_n": ramp_n,
        "n_after_ordered_cds_join": len(out),
        "skipped_position_join": skipped,
        "ramp_length_summary": summarize_numbers(ramp_lengths),
        "body_length_summary": summarize_numbers(body_lengths),
        "total_sense_cds_length_summary": summarize_numbers(total_lengths),
        "position_definition": "sense codons after stop/non-sense filtering; f3_ramp is first N sense codons and f3_body is all remaining sense codons",
    }


def feature_key(kind: str, ramp_n: int) -> str:
    return f"{kind}_N{ramp_n}"


def evaluate_window(
    x3: ModuleType,
    rows: list[dict[str, object]],
    organism: str,
    ramp_n: int,
) -> dict[str, object]:
    readout = f"structural_order_rampN{ramp_n}"
    full_controls = x3.cross_validated_ridge(rows, ["translation", "composition_controls"], organism, readout)
    ramp_model = x3.cross_validated_ridge(rows, ["translation", "composition_controls", "f3_ramp"], organism, readout)
    body_model = x3.cross_validated_ridge(rows, ["translation", "composition_controls", "f3_body"], organism, readout)
    joint_model = x3.cross_validated_ridge(rows, ["translation", "composition_controls", "f3_ramp_plus_body"], organism, readout)

    ramp_folds = fold_deltas(ramp_model, full_controls)
    body_folds = fold_deltas(body_model, full_controls)
    joint_folds = fold_deltas(joint_model, full_controls)
    paired = [r - b for r, b in zip(ramp_folds, body_folds)]
    ramp_delta = delta_r2(ramp_model, full_controls)
    body_delta = delta_r2(body_model, full_controls)
    joint_delta = delta_r2(joint_model, full_controls)
    return {
        "ramp_n": ramp_n,
        "metrics": {
            "translation_plus_length_aa_gc_controls": full_controls,
            "full_controls_plus_f3_ramp": ramp_model,
            "full_controls_plus_f3_body": body_model,
            "full_controls_plus_f3_ramp_and_body": joint_model,
        },
        "increments": {
            "f3_ramp_given_full_controls": {
                "delta_held_out_r2": ramp_delta,
                "fold_delta_held_out_r2": ramp_folds,
                "signflip_null": signflip_null(ramp_folds),
            },
            "f3_body_given_full_controls": {
                "delta_held_out_r2": body_delta,
                "fold_delta_held_out_r2": body_folds,
                "signflip_null": signflip_null(body_folds),
            },
            "f3_ramp_plus_body_given_full_controls": {
                "delta_held_out_r2": joint_delta,
                "fold_delta_held_out_r2": joint_folds,
                "signflip_null": signflip_null(joint_folds),
            },
            "f3_ramp_minus_body": {
                "delta_held_out_r2_difference": None
                if not isinstance(ramp_delta, float) or not isinstance(body_delta, float)
                else ramp_delta - body_delta,
                "paired_fold_delta_difference": paired,
                "paired_signflip_null": signflip_null(paired),
            },
        },
    }


def run_organism(
    *,
    x3: ModuleType,
    organism: str,
    label: str,
    code: dict[str, str],
    codons: list[str],
    aa_order: list[str],
    q_projected: dict[str, dict[str, float]],
    q_names: list[str],
) -> dict[str, object]:
    rows, data_summary = x3.joined_rows(
        organism=organism,
        label=label,
        code=code,
        codons=codons,
        aa_order=aa_order,
        q_projected=q_projected,
        q_names=q_names,
    )
    ordered, ordered_summary = ordered_cds_index(organism, set(codons))
    base = {
        "organism": organism,
        "label": label,
        "readout": "structural_order",
        "base_x3_join_rows": len(rows),
        "data_summary": data_summary,
        "ordered_cds_summary": ordered_summary,
    }
    by_window: dict[str, dict[str, object]] = {}
    primary_powered = False
    for ramp_n in SENSITIVITY_RAMP_NS:
        positioned_rows, position_summary = attach_position_f3(
            rows,
            organism=organism,
            ordered=ordered,
            f3_projected=q_projected["f3_stress"],
            codons=codons,
            ramp_n=ramp_n,
        )
        powered = len(positioned_rows) >= MIN_JOINED
        window_result: dict[str, object] = {
            "ramp_n": ramp_n,
            "status": "computed" if powered else "needs_data",
            "powered": powered,
            "n_model_rows": len(positioned_rows),
            "position_summary": position_summary,
            "power_note": None if powered else f"交集不足 n={len(positioned_rows)} < {MIN_JOINED}；该窗口不进入 headline aggregate。",
        }
        if powered:
            window_result.update(evaluate_window(x3, positioned_rows, organism, ramp_n))
        if ramp_n == PRIMARY_RAMP_N:
            primary_powered = powered
        by_window[str(ramp_n)] = window_result
    return {
        **base,
        "status": "computed" if primary_powered else "needs_data",
        "powered": primary_powered,
        "n_model_rows": by_window[str(PRIMARY_RAMP_N)]["n_model_rows"],
        "windows": by_window,
    }


def compact_window(window: dict[str, object]) -> dict[str, object]:
    out = {
        "ramp_n": window.get("ramp_n"),
        "status": window.get("status"),
        "powered": window.get("powered"),
        "n_model_rows": window.get("n_model_rows"),
        "power_note": window.get("power_note"),
        "position_summary": window.get("position_summary"),
    }
    increments = window.get("increments")
    if isinstance(increments, dict):
        out["increments"] = {
            key: {
                "delta_held_out_r2": value.get("delta_held_out_r2") if isinstance(value, dict) else None,
                "delta_held_out_r2_difference": value.get("delta_held_out_r2_difference") if isinstance(value, dict) else None,
                "fold_delta_held_out_r2": value.get("fold_delta_held_out_r2") if isinstance(value, dict) else None,
                "paired_fold_delta_difference": value.get("paired_fold_delta_difference") if isinstance(value, dict) else None,
                "signflip_null": value.get("signflip_null") if isinstance(value, dict) else None,
                "paired_signflip_null": value.get("paired_signflip_null") if isinstance(value, dict) else None,
            }
            for key, value in increments.items()
            if isinstance(value, dict)
        }
    return out


def compact_per_organism(results: dict[str, dict[str, object]]) -> dict[str, object]:
    out: dict[str, object] = {}
    for organism, result in results.items():
        windows = result.get("windows")
        out[organism] = {
            "status": result.get("status"),
            "powered": result.get("powered"),
            "base_x3_join_rows": result.get("base_x3_join_rows"),
            "primary_n_model_rows": result.get("n_model_rows"),
            "ordered_cds_summary": result.get("ordered_cds_summary"),
            "windows": {
                key: compact_window(window)
                for key, window in windows.items()
                if isinstance(windows, dict) and isinstance(window, dict)
            } if isinstance(windows, dict) else {},
        }
    return out


def aggregate_window(results: list[dict[str, object]], ramp_n: int) -> dict[str, object]:
    total_rows = 0
    weighted_ramp = 0.0
    weighted_body = 0.0
    weighted_joint = 0.0
    weighted_diff = 0.0
    ramp_deltas: list[float] = []
    body_deltas: list[float] = []
    joint_deltas: list[float] = []
    diff_deltas: list[float] = []
    ramp_fold_values: list[float] = []
    body_fold_values: list[float] = []
    joint_fold_values: list[float] = []
    paired_fold_values: list[float] = []
    positive_ramp_count = 0
    positive_body_count = 0
    ramp_gt_body_count = 0
    per_organism: dict[str, object] = {}

    for result in results:
        windows = result.get("windows")
        if not isinstance(windows, dict):
            continue
        window = windows.get(str(ramp_n))
        if not isinstance(window, dict) or window.get("powered") is not True:
            continue
        n_rows = int(window.get("n_model_rows", 0))
        increments = window.get("increments")
        if not isinstance(increments, dict):
            continue
        ramp = increments.get("f3_ramp_given_full_controls")
        body = increments.get("f3_body_given_full_controls")
        joint = increments.get("f3_ramp_plus_body_given_full_controls")
        diff = increments.get("f3_ramp_minus_body")
        if not all(isinstance(item, dict) for item in [ramp, body, joint, diff]):
            continue
        ramp_delta = ramp.get("delta_held_out_r2")  # type: ignore[union-attr]
        body_delta = body.get("delta_held_out_r2")  # type: ignore[union-attr]
        joint_delta = joint.get("delta_held_out_r2")  # type: ignore[union-attr]
        diff_delta = diff.get("delta_held_out_r2_difference")  # type: ignore[union-attr]
        if isinstance(ramp_delta, float) and isinstance(body_delta, float) and isinstance(joint_delta, float) and isinstance(diff_delta, float):
            total_rows += n_rows
            weighted_ramp += n_rows * ramp_delta
            weighted_body += n_rows * body_delta
            weighted_joint += n_rows * joint_delta
            weighted_diff += n_rows * diff_delta
            ramp_deltas.append(ramp_delta)
            body_deltas.append(body_delta)
            joint_deltas.append(joint_delta)
            diff_deltas.append(diff_delta)
            if ramp_delta > 0.0:
                positive_ramp_count += 1
            if body_delta > 0.0:
                positive_body_count += 1
            if ramp_delta > body_delta:
                ramp_gt_body_count += 1
        ramp_folds = [float(value) for value in ramp.get("fold_delta_held_out_r2", []) if isinstance(value, (int, float))]  # type: ignore[union-attr]
        body_folds = [float(value) for value in body.get("fold_delta_held_out_r2", []) if isinstance(value, (int, float))]  # type: ignore[union-attr]
        joint_folds = [float(value) for value in joint.get("fold_delta_held_out_r2", []) if isinstance(value, (int, float))]  # type: ignore[union-attr]
        paired_folds = [float(value) for value in diff.get("paired_fold_delta_difference", []) if isinstance(value, (int, float))]  # type: ignore[union-attr]
        ramp_fold_values.extend(ramp_folds)
        body_fold_values.extend(body_folds)
        joint_fold_values.extend(joint_folds)
        paired_fold_values.extend(paired_folds)
        per_organism[str(result["organism"])] = {
            "n_model_rows": n_rows,
            "f3_ramp_delta_held_out_r2": ramp_delta,
            "f3_body_delta_held_out_r2": body_delta,
            "f3_ramp_plus_body_delta_held_out_r2": joint_delta,
            "ramp_minus_body_delta_held_out_r2": diff_delta,
            "f3_ramp_signflip_null": ramp.get("signflip_null"),  # type: ignore[union-attr]
            "f3_body_signflip_null": body.get("signflip_null"),  # type: ignore[union-attr]
            "ramp_minus_body_paired_signflip_null": diff.get("paired_signflip_null"),  # type: ignore[union-attr]
        }

    ramp_null = signflip_null(ramp_fold_values)
    body_null = signflip_null(body_fold_values)
    joint_null = signflip_null(joint_fold_values)
    paired_null = signflip_null(paired_fold_values)
    weighted_ramp_delta = None if total_rows <= 0 else weighted_ramp / total_rows
    weighted_body_delta = None if total_rows <= 0 else weighted_body / total_rows
    weighted_joint_delta = None if total_rows <= 0 else weighted_joint / total_rows
    weighted_diff_delta = None if total_rows <= 0 else weighted_diff / total_rows
    return {
        "ramp_n": ramp_n,
        "n_primary_organisms": len(per_organism),
        "n_total_rows": total_rows,
        "weighted_f3_ramp_delta_held_out_r2": weighted_ramp_delta,
        "weighted_f3_body_delta_held_out_r2": weighted_body_delta,
        "weighted_f3_ramp_plus_body_delta_held_out_r2": weighted_joint_delta,
        "weighted_ramp_minus_body_delta_held_out_r2": weighted_diff_delta,
        "organism_ramp_delta_summary": summarize_numbers(ramp_deltas),
        "organism_body_delta_summary": summarize_numbers(body_deltas),
        "organism_joint_delta_summary": summarize_numbers(joint_deltas),
        "organism_ramp_minus_body_summary": summarize_numbers(diff_deltas),
        "fold_ramp_delta_summary": summarize_numbers(ramp_fold_values),
        "fold_body_delta_summary": summarize_numbers(body_fold_values),
        "fold_joint_delta_summary": summarize_numbers(joint_fold_values),
        "paired_fold_ramp_minus_body_summary": summarize_numbers(paired_fold_values),
        "f3_ramp_signflip_null": ramp_null,
        "f3_body_signflip_null": body_null,
        "f3_ramp_plus_body_signflip_null": joint_null,
        "ramp_minus_body_paired_signflip_null": paired_null,
        "positive_ramp_primary_organism_count": positive_ramp_count,
        "positive_body_primary_organism_count": positive_body_count,
        "ramp_gt_body_primary_organism_count": ramp_gt_body_count,
        "per_organism": per_organism,
    }


def verdict_from_primary(primary: dict[str, object]) -> dict[str, object]:
    n_org = int(primary.get("n_primary_organisms", 0))
    weighted_ramp = primary.get("weighted_f3_ramp_delta_held_out_r2")
    weighted_body = primary.get("weighted_f3_body_delta_held_out_r2")
    weighted_diff = primary.get("weighted_ramp_minus_body_delta_held_out_r2")
    ramp_p = primary.get("f3_ramp_signflip_null")
    body_p = primary.get("f3_body_signflip_null")
    paired_p = primary.get("ramp_minus_body_paired_signflip_null")
    ramp_p_value = ramp_p.get("p_greater_zero") if isinstance(ramp_p, dict) else None
    body_p_value = body_p.get("p_greater_zero") if isinstance(body_p, dict) else None
    paired_p_value = paired_p.get("p_greater_zero") if isinstance(paired_p, dict) else None
    ramp_gt_body_count = int(primary.get("ramp_gt_body_primary_organism_count", 0))
    positive_ramp_count = int(primary.get("positive_ramp_primary_organism_count", 0))
    positive_body_count = int(primary.get("positive_body_primary_organism_count", 0))

    ramp_signal = (
        n_org >= MIN_PRIMARY_ORGANISMS
        and positive_ramp_count >= MIN_PRIMARY_ORGANISMS
        and isinstance(weighted_ramp, float)
        and weighted_ramp > 0.0
        and isinstance(ramp_p_value, float)
        and ramp_p_value <= SIGNIFICANCE_ALPHA
    )
    body_signal = (
        n_org >= MIN_PRIMARY_ORGANISMS
        and positive_body_count >= MIN_PRIMARY_ORGANISMS
        and isinstance(weighted_body, float)
        and weighted_body > 0.0
        and isinstance(body_p_value, float)
        and body_p_value <= SIGNIFICANCE_ALPHA
    )
    ramp_localized = (
        ramp_signal
        and ramp_gt_body_count >= MIN_PRIMARY_ORGANISMS
        and isinstance(weighted_diff, float)
        and weighted_diff >= LOCALIZATION_MARGIN
        and isinstance(paired_p_value, float)
        and paired_p_value <= SIGNIFICANCE_ALPHA
    )
    body_dominant = (
        body_signal
        and isinstance(weighted_diff, float)
        and weighted_diff <= -LOCALIZATION_MARGIN
    )

    if ramp_localized:
        conclusion = "structural_order_signal_is_ramp_localized"
        reason = "primary N=50 f3_ramp full-control increment is positive/sign-flip significant and exceeds f3_body in the paired fold comparison"
    elif body_dominant:
        conclusion = "body_dominant"
        reason = "primary N=50 f3_body full-control increment is stronger than f3_ramp by the configured margin"
    elif ramp_signal and body_signal:
        conclusion = "uniform_along_cds"
        reason = "both ramp and body carry positive full-control increments without a significant ramp>body paired contrast"
    elif ramp_signal:
        conclusion = "ramp_positive_but_not_localized"
        reason = "f3_ramp is positive/sign-flip significant, but the paired ramp-body localization gate did not pass"
    elif body_signal:
        conclusion = "body_positive_not_ramp_localized"
        reason = "f3_body is positive/sign-flip significant while ramp localization did not pass"
    else:
        conclusion = "no_detectable_positional_f3_structural_order_signal"
        reason = "neither position-split f3 coordinate passed the cross-organism full-control sign-flip gate"

    return {
        "conclusion": conclusion,
        "reason": reason,
        "primary_ramp_n": PRIMARY_RAMP_N,
        "ramp_signal": ramp_signal,
        "body_signal": body_signal,
        "ramp_localized_gate": ramp_localized,
        "body_dominant_gate": body_dominant,
        "weighted_f3_ramp_delta_held_out_r2": weighted_ramp,
        "weighted_f3_body_delta_held_out_r2": weighted_body,
        "weighted_ramp_minus_body_delta_held_out_r2": weighted_diff,
        "f3_ramp_signflip_p_greater_zero": ramp_p_value,
        "f3_body_signflip_p_greater_zero": body_p_value,
        "ramp_minus_body_paired_signflip_p_greater_zero": paired_p_value,
        "positive_ramp_primary_organism_count": positive_ramp_count,
        "positive_body_primary_organism_count": positive_body_count,
        "ramp_gt_body_primary_organism_count": ramp_gt_body_count,
    }


def sensitivity_summary(aggregates: dict[str, dict[str, object]]) -> dict[str, object]:
    out: dict[str, object] = {}
    for ramp_n in SENSITIVITY_RAMP_NS:
        item = aggregates[str(ramp_n)]
        out[str(ramp_n)] = {
            "ramp_n": ramp_n,
            "weighted_f3_ramp_delta_held_out_r2": item.get("weighted_f3_ramp_delta_held_out_r2"),
            "weighted_f3_body_delta_held_out_r2": item.get("weighted_f3_body_delta_held_out_r2"),
            "weighted_ramp_minus_body_delta_held_out_r2": item.get("weighted_ramp_minus_body_delta_held_out_r2"),
            "f3_ramp_signflip_p_greater_zero": item.get("f3_ramp_signflip_null", {}).get("p_greater_zero") if isinstance(item.get("f3_ramp_signflip_null"), dict) else None,
            "f3_body_signflip_p_greater_zero": item.get("f3_body_signflip_null", {}).get("p_greater_zero") if isinstance(item.get("f3_body_signflip_null"), dict) else None,
            "ramp_minus_body_paired_signflip_p_greater_zero": item.get("ramp_minus_body_paired_signflip_null", {}).get("p_greater_zero") if isinstance(item.get("ramp_minus_body_paired_signflip_null"), dict) else None,
            "ramp_gt_body_primary_organism_count": item.get("ramp_gt_body_primary_organism_count"),
        }
    return out


def cannot_claim() -> list[str]:
    return [
        "这是横截面 held-out 预测定位实验，不是共翻译折叠或延伸速度的因果证明。",
        "structural_order 是本地 AlphaFold mean-pLDDT 派生 proxy；不是实验结构、有序度、功能或适应度测量。",
        "f3_ramp/f3_body 只按 ordered CDS 的 sense codon 位置切分；N=50 是主分析，N=30/70 是敏感性，不应外推为精确生物边界。",
        "全控为 translation + length + amino-acid composition + GC3；translation 控制来自同一批 measured TE/protein abundance/mRNA/footprint，不能证明翻译层完全观测。",
        "sign-flip null 是 fold-level 确定性符号翻转诊断；两个物种、十个 folds 的跨物种 power 有限。",
        "若 verdict 非 ramp-localized，应照实解释为本数据和此模型下未支持 5'-ramp 局部化，不等于真实共翻译折叠机制不存在。",
    ]


def main() -> None:
    required = [DATA_DIR / "ncbi_genetic_codes.json", X3_SIBLING]
    for item in ORGANISMS:
        organism = str(item["organism"])
        required.extend(
            [
                DATA_DIR / f"cds_codon_abundance_{organism}.json",
                DATA_DIR / f"cds_ordered_sequences_{organism}.json",
                DATA_DIR / f"ribosome_te_{organism}.json",
                DATA_DIR / f"structural_order_{organism}.json",
            ]
        )
    missing = [str(path) for path in required if not path.exists()]
    if missing:
        emit("needs_data", reason="required local sibling/data files not present", missing_required_data=missing)

    try:
        x3 = import_module_from_path("route_x3_structural_order_boundary", X3_SIBLING)
        patch_x3_seed_and_folds(x3)

        code = x3.standard_code()
        codons = [codon for codon in sorted(code) if code[codon] != "*"]
        fibers = x3.fibers_for(code, codons)
        aa_order = x3.standard_amino_acids(code, codons)
        raw_q, q_source = load_q_vectors(x3, codons)
        q_projected = {name: x3.project_syn(vector, fibers) for name, vector in raw_q.items()}
        q_names = list(q_projected)
        if "f3_stress" not in q_projected:
            raise ValueError("f3_stress coordinate missing from B*_Q6 q vectors")

        all_results: dict[str, dict[str, object]] = {}
        primary_results: list[dict[str, object]] = []
        for item in ORGANISMS:
            organism = str(item["organism"])
            result = run_organism(
                x3=x3,
                organism=organism,
                label=str(item["label"]),
                code=code,
                codons=codons,
                aa_order=aa_order,
                q_projected=q_projected,
                q_names=q_names,
            )
            if result.get("powered") is True:
                primary_results.append(result)
            all_results[organism] = result

        if len(primary_results) < MIN_PRIMARY_ORGANISMS:
            emit(
                "needs_data",
                reason=f"primary ordered-CDS/structural-order/CDS/translation overlap powered organisms < {MIN_PRIMARY_ORGANISMS}",
                per_organism=compact_per_organism(all_results),
                checks=[
                    {"name": "ramp_body_f3_computed", "passed": False},
                    {"name": "ramp_vs_body_structural_increment", "passed": False},
                    {"name": "ramp_localization_verdict", "passed": False},
                ],
            )

        aggregates = {str(ramp_n): aggregate_window(primary_results, ramp_n) for ramp_n in SENSITIVITY_RAMP_NS}
        primary = aggregates[str(PRIMARY_RAMP_N)]
        verdict = verdict_from_primary(primary)
        sensitivity = sensitivity_summary(aggregates)

        ramp_body_ok = all(
            aggregate.get("n_primary_organisms") == len(primary_results)
            and isinstance(aggregate.get("weighted_f3_ramp_delta_held_out_r2"), float)
            and isinstance(aggregate.get("weighted_f3_body_delta_held_out_r2"), float)
            for aggregate in aggregates.values()
        )
        increment_ok = (
            isinstance(primary.get("f3_ramp_signflip_null"), dict)
            and isinstance(primary.get("f3_body_signflip_null"), dict)
            and isinstance(primary.get("ramp_minus_body_paired_signflip_null"), dict)
            and isinstance(primary.get("weighted_ramp_minus_body_delta_held_out_r2"), float)
        )
        verdict_ok = verdict.get("conclusion") in {
            "structural_order_signal_is_ramp_localized",
            "uniform_along_cds",
            "body_dominant",
            "ramp_positive_but_not_localized",
            "body_positive_not_ramp_localized",
            "no_detectable_positional_f3_structural_order_signal",
        }

        checks = [
            {
                "name": "ramp_body_f3_computed",
                "passed": ramp_body_ok,
                "expected": "f3_ramp and f3_body computed from ordered CDS for primary N=50 plus N=30/70 sensitivity in both organisms",
                "actual": {
                    ramp_n: {
                        "n_primary_organisms": aggregate.get("n_primary_organisms"),
                        "weighted_f3_ramp_delta_held_out_r2": aggregate.get("weighted_f3_ramp_delta_held_out_r2"),
                        "weighted_f3_body_delta_held_out_r2": aggregate.get("weighted_f3_body_delta_held_out_r2"),
                    }
                    for ramp_n, aggregate in aggregates.items()
                },
            },
            {
                "name": "ramp_vs_body_structural_increment",
                "passed": increment_ok,
                "expected": "N=50 f3_ramp and f3_body full-control held-out increments plus paired ramp-body sign-flip null computed",
                "actual": {
                    "weighted_f3_ramp_delta_held_out_r2": primary.get("weighted_f3_ramp_delta_held_out_r2"),
                    "weighted_f3_body_delta_held_out_r2": primary.get("weighted_f3_body_delta_held_out_r2"),
                    "weighted_ramp_minus_body_delta_held_out_r2": primary.get("weighted_ramp_minus_body_delta_held_out_r2"),
                    "f3_ramp_signflip_p_greater_zero": primary.get("f3_ramp_signflip_null", {}).get("p_greater_zero") if isinstance(primary.get("f3_ramp_signflip_null"), dict) else None,
                    "f3_body_signflip_p_greater_zero": primary.get("f3_body_signflip_null", {}).get("p_greater_zero") if isinstance(primary.get("f3_body_signflip_null"), dict) else None,
                    "ramp_minus_body_paired_signflip_p_greater_zero": primary.get("ramp_minus_body_paired_signflip_null", {}).get("p_greater_zero") if isinstance(primary.get("ramp_minus_body_paired_signflip_null"), dict) else None,
                },
            },
            {
                "name": "ramp_localization_verdict",
                "passed": verdict_ok,
                "expected": "explicit localization verdict from primary N=50 aggregate",
                "actual": verdict,
            },
        ]

        emit(
            "passed" if all(check["passed"] for check in checks) else "failed",
            conclusion=verdict["conclusion"],
            verdict=verdict,
            seed=SEED,
            fold_count=FOLD_COUNT,
            min_joined=MIN_JOINED,
            primary_ramp_n=PRIMARY_RAMP_N,
            sensitivity_ramp_ns=SENSITIVITY_RAMP_NS,
            q_vector_source=q_source,
            controls={
                "translation": ["log10 protein abundance ppm", "log10 measured TE", "log10 measured mRNA", "log10 ribosome footprint"],
                "full_control_addons": ["natural log CDS length nt", "20 amino-acid composition fractions in sorted one-letter AA order", "GC3 fraction"],
                "aa_order": aa_order,
                "position_predictors": ["f3_ramp", "f3_body", "f3_ramp_plus_body"],
                "f3_coordinate": "synonymous-projected f3_stress coordinate from B*_Q6, evaluated on ordered-CDS position windows",
            },
            readout_policy={
                "configured_organisms": ORGANISMS,
                "headline_aggregate_unit": "one structural_order readout per organism",
                "readout": "structural_order from structural_order_<organism>.json",
                "readout_transform": "raw structural_order on 0..100; no log/logit transform",
                "readout_boundary": "AlphaFold mean-pLDDT derived structural-order proxy, not experimental phenotype",
            },
            aggregate_primary_N50=primary,
            sensitivity_by_N=sensitivity,
            aggregate_by_N=aggregates,
            per_organism=compact_per_organism(all_results),
            checks=checks,
            null={
                "ramp_and_body_null": "exact one-sided fold-level sign-flip null over full-control delta R2 values pooled across primary organisms",
                "ramp_minus_body_null": "exact one-sided fold-level sign-flip null over paired per-fold (ramp delta R2 - body delta R2) values pooled across primary organisms",
                "localization_gate": {
                    "requires_primary_organisms_at_least": MIN_PRIMARY_ORGANISMS,
                    "requires_ramp_positive_in_all_primary_organisms": True,
                    "requires_weighted_ramp_delta_gt_zero": True,
                    "requires_ramp_signflip_p_lte": SIGNIFICANCE_ALPHA,
                    "requires_weighted_ramp_minus_body_delta_at_least": LOCALIZATION_MARGIN,
                    "requires_paired_ramp_minus_body_signflip_p_lte": SIGNIFICANCE_ALPHA,
                },
            },
            cannot_claim=cannot_claim(),
        )
    except Exception as exc:
        emit("failed", checks=[], error=str(exc), reason="invalid or unreadable positional f3 structural-order input or fit")


if __name__ == "__main__":
    main()

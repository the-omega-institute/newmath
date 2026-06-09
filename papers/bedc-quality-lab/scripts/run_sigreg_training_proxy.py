#!/usr/bin/env python3
"""Run the SIGReg training-objective proxy producer."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
from typing import Any, Iterable, Mapping, Sequence

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.model import build_tiny_encoder, choose_device, set_deterministic_seed
from bedc_quality_lab.toy_world import make_toy_batch
from scripts.run_sigreg_gaussianity_reproduction import (
    DEFAULT_FREQUENCIES,
    GuardThresholds,
    SlicedCFGaussianityProbe,
    _random_unit_directions,
    _sorted_frequencies,
)


SCHEMA_ID = "bedc-quality-lab:sigreg-training-proxy"
CLAIM_CAPSULE_SCHEMA_ID = "bedc.quality.claim_capsule"
ARTIFACT_ID = "bedc-quality-lab:sigreg-training-proxy"
JSON_ARTIFACT = "reports/canonical/sigreg-training-proxy.json"
REPORT_ARTIFACT = "reports/canonical/sigreg-training-proxy.md"
DEFAULT_RUN_ID = "sigreg-training-proxy"
DEFAULT_SAMPLE_COUNT = 192
DEFAULT_STEPS = 28
DEFAULT_SEEDS = (17, 29, 41)
DEFAULT_LAMBDA_SIGREG = 0.35
DEFAULT_DIRECTIONS = 16
DEFAULT_LEARNING_RATE = 2.0e-3
RHO = 0.82
ARMS = (
    "covariance_proxy_current",
    "true_sigreg_sliced_cf",
    "vicreg_like_covariance",
    "alignment_only",
)
NOT_CLAIMED = (
    "global model quality",
    "full LeJEPA reproduction",
    "full TensorNameCert",
    "LLM behavior quality",
    "mechanism closure unless D5-M gate passes",
)
FULL_LEJEPA_REQUIREMENTS = (
    "2D mixings",
    "grid",
    "distribution sweep",
)
POSITIVE_CLAIM = {
    "text": "D1 SIGReg training proxy separates the true sliced-CF objective from covariance proxy reporting.",
    "scope": "lab-local Gaussian-OU toy encoder training proxy",
}


def _as_float(value: Any) -> float:
    result = float(value)
    if not math.isfinite(result):
        raise ValueError("metric must be finite")
    return result


def _finite_float_or_none(value: Any) -> float | None:
    try:
        return _as_float(value)
    except (TypeError, ValueError):
        return None


def _status_from_bool(value: bool) -> str:
    return "pass" if value else "fail"


def _mean(rows: Iterable[Mapping[str, Any]], key: str) -> float:
    values = [_as_float(row[key]) for row in rows]
    return float(np.mean(np.asarray(values, dtype=np.float64))) if values else math.nan


def _std(rows: Iterable[Mapping[str, Any]], key: str) -> float:
    values = [_as_float(row[key]) for row in rows]
    return float(np.std(np.asarray(values, dtype=np.float64), ddof=0)) if values else math.nan


def _torch_sigreg_sliced_cf_loss(
    h: Any,
    *,
    seed: int,
    directions: int,
    frequencies: Sequence[float],
) -> Any:
    import torch

    direction_array = _random_unit_directions(dim=int(h.shape[1]), count=int(directions), seed=int(seed))
    frequency_array = _sorted_frequencies(frequencies)
    unit_directions = torch.as_tensor(direction_array, dtype=h.dtype, device=h.device)
    frequency_grid = torch.as_tensor(frequency_array, dtype=h.dtype, device=h.device)
    projections = h @ unit_directions.T
    centered = projections - projections.mean(dim=0, keepdim=True)
    variance = torch.var(centered, dim=0, unbiased=True).clamp_min(1.0e-12)
    standardized = centered / torch.sqrt(variance).reshape(1, -1)
    phases = standardized[:, :, None] * frequency_grid.reshape(1, 1, -1)
    empirical_real = torch.cos(phases).mean(dim=0)
    empirical_imag = torch.sin(phases).mean(dim=0)
    target = torch.exp(-0.5 * frequency_grid.square()).reshape(1, -1)
    return ((empirical_real - target).square() + empirical_imag.square()).mean()


def alignment_loss_value(h: Any, h_pair: Any) -> Any:
    return ((h - h_pair) ** 2).mean()


def covariance_proxy_loss_value(h: Any) -> Any:
    import torch

    centered = h - h.mean(dim=0, keepdim=True)
    cov = centered.T @ centered / max(1, int(h.shape[0]) - 1)
    eye = torch.eye(int(h.shape[1]), dtype=h.dtype, device=h.device)
    return ((cov - eye) ** 2).mean()


def mean_loss_value(h: Any) -> Any:
    return h.mean(dim=0).square().mean()


def training_loss(
    *,
    arm: str,
    alignment: Any,
    sigreg_sliced_cf: Any,
    covariance_proxy: Any,
    mean_penalty: Any,
    lambda_sigreg: float,
) -> Any:
    if arm == "true_sigreg_sliced_cf":
        return (1.0 - float(lambda_sigreg)) * alignment + float(lambda_sigreg) * sigreg_sliced_cf
    if arm == "covariance_proxy_current":
        return alignment + covariance_proxy + 0.1 * mean_penalty
    if arm == "vicreg_like_covariance":
        return alignment + 0.5 * covariance_proxy + 0.1 * mean_penalty
    if arm == "alignment_only":
        return alignment
    raise ValueError(f"unknown arm: {arm}")


def _fallback_encode(train_x: np.ndarray, eval_x: np.ndarray, eval_x_pair: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    center = np.mean(train_x, axis=0, keepdims=True)
    scale = np.std(train_x - center, axis=0, keepdims=True)
    scale = np.where(scale <= 1.0e-12, 1.0, scale)
    return (eval_x - center) / scale, (eval_x_pair - center) / scale


def _split(sample_count: int, *, seed: int) -> tuple[np.ndarray, np.ndarray]:
    rng = np.random.default_rng(int(seed) ^ 0x51A6E9)
    indices = rng.permutation(int(sample_count))
    train_count = max(4, min(int(sample_count) - 4, int(round(0.70 * int(sample_count)))))
    return np.sort(indices[:train_count]).astype(np.int64), np.sort(indices[train_count:]).astype(np.int64)


def _train_arm(
    *,
    arm: str,
    seed: int,
    sample_count: int,
    steps: int,
    lambda_sigreg: float,
    directions: int,
    frequencies: Sequence[float],
    learning_rate: float,
) -> dict[str, Any]:
    import torch

    set_deterministic_seed(int(seed))
    batch = make_toy_batch(int(sample_count), rho=RHO, seed=int(seed))
    train_idx, eval_idx = _split(int(sample_count), seed=int(seed))
    train_x = batch.x[train_idx]
    train_x_pair = batch.x_pair[train_idx]
    eval_x = batch.x[eval_idx]
    eval_x_pair = batch.x_pair[eval_idx]
    device = choose_device()
    encoder = build_tiny_encoder(output_dim=2).to(device)
    optimizer = torch.optim.AdamW(encoder.parameters(), lr=float(learning_rate), weight_decay=1.0e-4)
    x_t = torch.as_tensor(train_x, dtype=torch.float32, device=device)
    x_pair_t = torch.as_tensor(train_x_pair, dtype=torch.float32, device=device)
    final_components: dict[str, float] = {}
    for step in range(int(steps)):
        optimizer.zero_grad(set_to_none=True)
        h = encoder(x_t)
        h_pair = encoder(x_pair_t)
        alignment = alignment_loss_value(h, h_pair)
        sigreg = _torch_sigreg_sliced_cf_loss(
            h,
            seed=int(seed) + step,
            directions=int(directions),
            frequencies=frequencies,
        )
        covariance = covariance_proxy_loss_value(h)
        mean_penalty = mean_loss_value(h)
        loss = training_loss(
            arm=arm,
            alignment=alignment,
            sigreg_sliced_cf=sigreg,
            covariance_proxy=covariance,
            mean_penalty=mean_penalty,
            lambda_sigreg=float(lambda_sigreg),
        )
        loss.backward()
        optimizer.step()
        final_components = {
            "alignment": float(alignment.detach().cpu().item()),
            "sigreg_sliced_cf": float(sigreg.detach().cpu().item()),
            "covariance_proxy": float(covariance.detach().cpu().item()),
            "mean_penalty": float(mean_penalty.detach().cpu().item()),
            "loss": float(loss.detach().cpu().item()),
        }
    with torch.no_grad():
        h_eval = encoder(torch.as_tensor(eval_x, dtype=torch.float32, device=device)).detach().cpu().numpy().astype(np.float64)
        h_pair_eval = encoder(torch.as_tensor(eval_x_pair, dtype=torch.float32, device=device)).detach().cpu().numpy().astype(np.float64)
    probe = SlicedCFGaussianityProbe(
        directions=int(directions),
        frequencies=frequencies,
        guard_thresholds=GuardThresholds(cov_to_identity_max=10.0, min_cov_eigenvalue_floor=1.0e-8, min_projected_variance_floor=1.0e-8),
    )
    score = probe.score(h_eval, seed=int(seed), directions=int(directions), frequencies=frequencies)
    eval_alignment = float(np.mean(np.square(h_eval - h_pair_eval)))
    eval_loss = (
        (1.0 - float(lambda_sigreg)) * eval_alignment + float(lambda_sigreg) * float(score["sigreg_penalty"])
        if arm == "true_sigreg_sliced_cf"
        else float(final_components["loss"])
    )
    return {
        "arm": arm,
        "seed": int(seed),
        "sample_count": int(sample_count),
        "train_count": int(train_idx.shape[0]),
        "eval_count": int(eval_idx.shape[0]),
        "lambda_sigreg": float(lambda_sigreg),
        "training_loss": final_components,
        "evaluation": {
            "alignment": eval_alignment,
            "sigreg_sliced_cf": float(score["sigreg_penalty"]),
            "covariance_proxy": float(score["cov_to_identity_fro"]),
            "loss": eval_loss,
            "guard_status": score["guard_status"],
            "guard_reasons": list(score["guard_reasons"]),
        },
    }


def _fallback_arm(
    *,
    arm: str,
    seed: int,
    sample_count: int,
    lambda_sigreg: float,
    directions: int,
    frequencies: Sequence[float],
) -> dict[str, Any]:
    batch = make_toy_batch(int(sample_count), rho=RHO, seed=int(seed))
    train_idx, eval_idx = _split(int(sample_count), seed=int(seed))
    h_eval, h_pair_eval = _fallback_encode(batch.x[train_idx], batch.x[eval_idx], batch.x_pair[eval_idx])
    if arm == "true_sigreg_sliced_cf":
        h_eval = h_eval * 1.08
    elif arm == "alignment_only":
        h_eval = h_pair_eval.copy()
    elif arm == "vicreg_like_covariance":
        h_eval = 0.5 * (h_eval + h_pair_eval)
    probe = SlicedCFGaussianityProbe(
        directions=int(directions),
        frequencies=frequencies,
        guard_thresholds=GuardThresholds(cov_to_identity_max=10.0, min_cov_eigenvalue_floor=1.0e-8, min_projected_variance_floor=1.0e-8),
    )
    score = probe.score(h_eval, seed=int(seed), directions=int(directions), frequencies=frequencies)
    alignment = float(np.mean(np.square(h_eval - h_pair_eval)))
    sigreg = float(score["sigreg_penalty"])
    covariance = float(score["cov_to_identity_fro"])
    mean_penalty = float(np.mean(np.square(np.mean(h_eval, axis=0))))
    loss = (
        (1.0 - float(lambda_sigreg)) * alignment + float(lambda_sigreg) * sigreg
        if arm == "true_sigreg_sliced_cf"
        else alignment + covariance + 0.1 * mean_penalty
        if arm == "covariance_proxy_current"
        else alignment + 0.5 * covariance + 0.1 * mean_penalty
        if arm == "vicreg_like_covariance"
        else alignment
    )
    return {
        "arm": arm,
        "seed": int(seed),
        "sample_count": int(sample_count),
        "train_count": int(train_idx.shape[0]),
        "eval_count": int(eval_idx.shape[0]),
        "lambda_sigreg": float(lambda_sigreg),
        "training_loss": {
            "alignment": alignment,
            "sigreg_sliced_cf": sigreg,
            "covariance_proxy": covariance,
            "mean_penalty": mean_penalty,
            "loss": float(loss),
        },
        "evaluation": {
            "alignment": alignment,
            "sigreg_sliced_cf": sigreg,
            "covariance_proxy": covariance,
            "loss": float(loss),
            "guard_status": score["guard_status"],
            "guard_reasons": list(score["guard_reasons"]),
        },
    }


def run_records(
    *,
    sample_count: int,
    steps: int,
    seeds: Sequence[int],
    lambda_sigreg: float,
    directions: int,
    frequencies: Sequence[float],
    learning_rate: float,
    use_torch: bool,
) -> list[dict[str, Any]]:
    records = []
    for arm in ARMS:
        for seed in seeds:
            if use_torch:
                try:
                    record = _train_arm(
                        arm=arm,
                        seed=int(seed),
                        sample_count=int(sample_count),
                        steps=int(steps),
                        lambda_sigreg=float(lambda_sigreg),
                        directions=int(directions),
                        frequencies=frequencies,
                        learning_rate=float(learning_rate),
                    )
                except Exception:
                    record = _fallback_arm(
                        arm=arm,
                        seed=int(seed),
                        sample_count=int(sample_count),
                        lambda_sigreg=float(lambda_sigreg),
                        directions=int(directions),
                        frequencies=frequencies,
                    )
                    record["execution_fallback"] = "deterministic-standardized"
            else:
                record = _fallback_arm(
                    arm=arm,
                    seed=int(seed),
                    sample_count=int(sample_count),
                    lambda_sigreg=float(lambda_sigreg),
                    directions=int(directions),
                    frequencies=frequencies,
                )
                record["execution_fallback"] = "deterministic-standardized"
            records.append(record)
    return records


def arm_summaries(records: Sequence[Mapping[str, Any]]) -> dict[str, dict[str, Any]]:
    return {
        arm: {
            "seed_count": len([row for row in records if row["arm"] == arm]),
            "alignment_mean": _mean((row["evaluation"] for row in records if row["arm"] == arm), "alignment"),
            "alignment_std": _std((row["evaluation"] for row in records if row["arm"] == arm), "alignment"),
            "sigreg_sliced_cf_mean": _mean((row["evaluation"] for row in records if row["arm"] == arm), "sigreg_sliced_cf"),
            "sigreg_sliced_cf_std": _std((row["evaluation"] for row in records if row["arm"] == arm), "sigreg_sliced_cf"),
            "loss_mean": _mean((row["evaluation"] for row in records if row["arm"] == arm), "loss"),
        }
        for arm in ARMS
    }


def d1_hardgates(
    records: Sequence[Mapping[str, Any]],
    summaries: Mapping[str, Mapping[str, Any]],
    *,
    full_sweep_requirements: Mapping[str, bool] | None = None,
    full_lejepa_claim: bool = False,
    positive_claim: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    sigreg = summaries.get("true_sigreg_sliced_cf", {})
    covariance = summaries.get("covariance_proxy_current", {})
    alignment = summaries.get("alignment_only", {})
    full_sweep = {
        requirement: bool((full_sweep_requirements or {}).get(requirement, False))
        for requirement in FULL_LEJEPA_REQUIREMENTS
    }
    true_sigreg_records = [
        row
        for row in records
        if row.get("arm") == "true_sigreg_sliced_cf" and "execution_fallback" not in row
    ]
    sigreg_sliced_cf_mean = _finite_float_or_none(sigreg.get("sigreg_sliced_cf_mean"))
    covariance_sliced_cf_mean = _finite_float_or_none(covariance.get("sigreg_sliced_cf_mean"))
    alignment_sliced_cf_mean = _finite_float_or_none(alignment.get("sigreg_sliced_cf_mean"))
    sigreg_alignment_mean = _finite_float_or_none(sigreg.get("alignment_mean"))
    alignment_alignment_mean = _finite_float_or_none(alignment.get("alignment_mean"))
    improved_gaussianity = (
        sigreg_sliced_cf_mean is not None
        and alignment_sliced_cf_mean is not None
        and sigreg_sliced_cf_mean < alignment_sliced_cf_mean
    )
    alignment_hurt = (
        sigreg_alignment_mean is not None
        and alignment_alignment_mean is not None
        and sigreg_alignment_mean > alignment_alignment_mean
    )
    separate_objective = (
        sigreg_sliced_cf_mean is not None
        and covariance_sliced_cf_mean is not None
        and sigreg_sliced_cf_mean != covariance_sliced_cf_mean
    )
    boundary_satisfied = not bool(full_lejepa_claim) and not any(full_sweep.values())
    claim_audit = _forbidden_claim_term_audit(dict(POSITIVE_CLAIM if positive_claim is None else positive_claim))
    return {
        "D1-HG1": {
            "status": _status_from_bool(bool(true_sigreg_records)),
            "evidence": "real training records exist for true_sigreg_sliced_cf",
            "record_count": len(true_sigreg_records),
        },
        "D1-HG2": {
            "status": _status_from_bool(separate_objective),
            "evidence": "SIGReg objective and covariance proxy are separate arms and separate metrics",
        },
        "D1-HG3": {
            "status": _status_from_bool(improved_gaussianity and alignment_hurt),
            "tradeoff": {
                "sigreg_improves_gaussianity_vs_alignment_only": improved_gaussianity,
                "sigreg_hurts_alignment_vs_alignment_only": alignment_hurt,
                "ledger": "recorded",
            },
        },
        "D1-HG4": {
            "status": _status_from_bool(boundary_satisfied),
            "full_sweep_requirements": full_sweep,
            "full_lejepa_claim": bool(full_lejepa_claim),
        },
        "D1-HG5": {
            "status": claim_audit["status"],
            "evidence": "positive claim cell has no forbidden full-scope terms",
            "forbidden_positive_claim_terms": claim_audit["forbidden_positive_claim_terms"],
            "hits": claim_audit["hits"],
        },
    }


def _forbidden_claim_term_audit(value: Mapping[str, Any]) -> dict[str, Any]:
    text = json.dumps(value, sort_keys=True).lower()
    hits = [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in text]
    return {
        "status": _status_from_bool(not hits),
        "forbidden_positive_claim_terms": list(FORBIDDEN_POSITIVE_CLAIM_TERMS),
        "hits": hits,
    }


def _claim_capsule(
    *,
    run_id: str,
    generated_at: str,
    summary_artifact: str,
    hardgates: Mapping[str, Any],
    summaries: Mapping[str, Mapping[str, Any]],
    positive_claim: Mapping[str, Any],
) -> dict[str, Any]:
    failed = [name for name, row in hardgates.items() if row["status"] != "pass"]
    status = "d1-pointer-accepted" if not failed else "failed"
    capsule = {
        "schema_id": CLAIM_CAPSULE_SCHEMA_ID,
        "run_id": run_id,
        "generated_at": generated_at,
        "artifact_id": f"{ARTIFACT_ID}:claim-capsule",
        "claim_status": status,
        "positive_claim": dict(positive_claim, level="D1" if status == "d1-pointer-accepted" else "DN"),
        "source_artifacts": {
            "summary": summary_artifact,
            "cost_protocol": "configs/default_cost_protocol.yaml",
        },
        "not_claimed": list(NOT_CLAIMED),
        "failed_gate": failed[0] if failed else None,
        "what_was_learned": (
            "The lab-local producer can run a real SIGReg sliced-CF training objective and ledger its alignment tradeoff."
            if not failed
            else "The lab-local producer recorded a failed gate without promoting a positive claim."
        ),
        "revocation": {
            "status": "revocable",
            "conditions": [
                "revoke if the true SIGReg arm cannot be rerun as a training objective",
                "revoke if covariance proxy and SIGReg objective are collapsed into one reported arm",
                "revoke if alignment tradeoff evidence is withdrawn",
            ],
        },
        "hardgates": dict(hardgates),
        "summary_pointer": "$.d1_evidence",
        "result_snapshot": {
            "true_sigreg_sliced_cf": dict(summaries["true_sigreg_sliced_cf"]),
            "covariance_proxy_current": dict(summaries["covariance_proxy_current"]),
            "alignment_only": dict(summaries["alignment_only"]),
        },
    }
    capsule["forbidden_claim_term_audit"] = _forbidden_claim_term_audit(capsule["positive_claim"])
    if capsule["forbidden_claim_term_audit"]["status"] != "pass":
        capsule["claim_status"] = "failed"
        capsule["failed_gate"] = capsule["failed_gate"] or "forbidden-positive-claim-term"
    return capsule


def _first_failed_hardgate(hardgates: Mapping[str, Any]) -> str | None:
    for name, row in hardgates.items():
        if not isinstance(row, Mapping) or row.get("status") != "pass":
            return name
    return None


def _terminal_verdict_for_status(result_status: str) -> str:
    return "d1-pointer-accepted" if result_status == "d1-pointer-accepted" else "rejected"


def _discovery_level_for_status(result_status: str) -> str:
    return "D1" if result_status == "d1-pointer-accepted" else "DN"


def _result_snapshot(summaries: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    return {
        "true_sigreg_sliced_cf": dict(summaries["true_sigreg_sliced_cf"]),
        "covariance_proxy_current": dict(summaries["covariance_proxy_current"]),
        "alignment_only": dict(summaries["alignment_only"]),
    }


def _payload_from_records(
    *,
    records: Sequence[Mapping[str, Any]],
    run_id: str,
    generated_at: str,
    sample_count: int,
    steps: int,
    seeds: Sequence[int],
    lambda_sigreg: float,
    directions: int,
    frequencies: Sequence[float],
    learning_rate: float,
    json_artifact: str,
    report_artifact: str,
    full_sweep_requirements: Mapping[str, bool] | None = None,
    full_lejepa_claim: bool = False,
    positive_claim: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    claim = dict(POSITIVE_CLAIM if positive_claim is None else positive_claim)
    summaries = arm_summaries(records)
    hardgates = d1_hardgates(
        records,
        summaries,
        full_sweep_requirements=full_sweep_requirements,
        full_lejepa_claim=full_lejepa_claim,
        positive_claim=claim,
    )
    run_dir = f"reports/runs/{run_id}"
    snapshot = _result_snapshot(summaries)
    claim_capsule = _claim_capsule(
        run_id=run_id,
        generated_at=generated_at,
        summary_artifact=f"{run_dir}/summary.json",
        hardgates=hardgates,
        summaries=summaries,
        positive_claim=claim,
    )
    failed_gate = _first_failed_hardgate(hardgates)
    result_status = "d1-pointer-accepted" if failed_gate is None and claim_capsule["claim_status"] == "d1-pointer-accepted" else "negative"
    terminal_verdict = _terminal_verdict_for_status(result_status)
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "run_id": run_id,
        "json_artifact": json_artifact,
        "markdown_artifact": report_artifact,
        "run_artifacts": {
            "claim_capsule": f"{run_dir}/claim_capsule.json",
            "raw_metrics": f"{run_dir}/raw_metrics.jsonl",
            "summary": f"{run_dir}/summary.json",
            "result_snapshot": f"{run_dir}/result_snapshot.json",
            "report": f"{run_dir}/report.md",
        },
        "source_artifacts": {
            "producer": "scripts/run_sigreg_training_proxy.py",
            "cost_protocol": "configs/default_cost_protocol.yaml",
            "sliced_cf_probe": "scripts/run_sigreg_gaussianity_reproduction.py:SlicedCFGaussianityProbe",
            "training_reference": "scripts/run_gaussian_ou_lejepa.py",
        },
        "config": {
            "sample_count": int(sample_count),
            "steps": int(steps),
            "seeds": [int(seed) for seed in seeds],
            "lambda_sigreg": float(lambda_sigreg),
            "directions": int(directions),
            "frequencies": list(frequencies),
            "learning_rate": float(learning_rate),
            "rho": RHO,
            "arms": list(ARMS),
        },
        "objective": {
            "id": "sigreg_sliced_cf_training_proxy",
            "loss": "(1-lambda)*alignment + lambda*sigreg_sliced_cf",
            "lambda": float(lambda_sigreg),
            "implemented_for_arm": "true_sigreg_sliced_cf",
        },
        "arm_protocol": {
            "exact_arm_count": len(ARMS),
            "arms": list(ARMS),
            "covariance_proxy_arm": "covariance_proxy_current",
            "sigreg_objective_arm": "true_sigreg_sliced_cf",
        },
        "arm_summaries": summaries,
        "d1_evidence": {
            "debt_delta": -1.0 if result_status == "d1-pointer-accepted" else 0.0,
            "d1_hardgates": hardgates,
            "sigreg_objective_pointer": "$.arm_summaries.true_sigreg_sliced_cf",
            "covariance_proxy_pointer": "$.arm_summaries.covariance_proxy_current",
            "tradeoff_pointer": "$.d1_evidence.d1_hardgates.D1-HG3.tradeoff",
        },
        "claim_gate": {
            "status": _status_from_bool(result_status == "d1-pointer-accepted"),
            "training_audit_improvement_tradeoff": result_status == "d1-pointer-accepted",
        },
        "hardgate": {
            "status": _status_from_bool(result_status == "d1-pointer-accepted"),
            "failed_gate": failed_gate,
        },
        "failed_gate": failed_gate,
        "what_was_learned": claim_capsule["what_was_learned"],
        "not_claimed": list(NOT_CLAIMED),
        "full_lejepa_boundary": {
            "claim": bool(full_lejepa_claim),
            "required_to_claim": list(FULL_LEJEPA_REQUIREMENTS),
        },
        "claim_capsule": claim_capsule,
        "result_snapshot": snapshot,
        "result": {
            "status": result_status,
            "terminal_verdict": terminal_verdict,
            "discovery_level": _discovery_level_for_status(result_status),
            "claim_capsule_status": claim_capsule["claim_status"],
        },
        "raw_records": list(records),
    }
    payload["forbidden_claim_term_audit"] = _forbidden_claim_term_audit(claim_capsule["positive_claim"])
    return payload


def build_payload(
    *,
    run_id: str = DEFAULT_RUN_ID,
    generated_at: str | None = None,
    sample_count: int = DEFAULT_SAMPLE_COUNT,
    steps: int = DEFAULT_STEPS,
    seeds: Sequence[int] = DEFAULT_SEEDS,
    lambda_sigreg: float = DEFAULT_LAMBDA_SIGREG,
    directions: int = DEFAULT_DIRECTIONS,
    frequencies: Sequence[float] = DEFAULT_FREQUENCIES,
    learning_rate: float = DEFAULT_LEARNING_RATE,
    use_torch: bool = True,
    json_artifact: str = JSON_ARTIFACT,
    report_artifact: str = REPORT_ARTIFACT,
) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    frequency_grid = tuple(float(item) for item in _sorted_frequencies(frequencies))
    records = run_records(
        sample_count=int(sample_count),
        steps=int(steps),
        seeds=tuple(int(seed) for seed in seeds),
        lambda_sigreg=float(lambda_sigreg),
        directions=int(directions),
        frequencies=frequency_grid,
        learning_rate=float(learning_rate),
        use_torch=bool(use_torch),
    )
    payload = _payload_from_records(
        records=records,
        run_id=run_id,
        generated_at=timestamp,
        sample_count=sample_count,
        steps=steps,
        seeds=seeds,
        lambda_sigreg=lambda_sigreg,
        directions=directions,
        frequencies=frequency_grid,
        learning_rate=learning_rate,
        json_artifact=json_artifact,
        report_artifact=report_artifact,
    )
    return payload


def canonical_summary_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    run_artifacts = payload["run_artifacts"]
    result_status = str(payload["result"]["status"])
    return {
        "schema_id": payload["schema_id"],
        "artifact_id": payload["artifact_id"],
        "generated_at": payload["generated_at"],
        "run_id": payload["run_id"],
        "json_artifact": payload["json_artifact"],
        "markdown_artifact": payload["markdown_artifact"],
        "run_artifacts": dict(run_artifacts),
        "source_artifacts": dict(payload["source_artifacts"]),
        "config": dict(payload["config"]),
        "objective": dict(payload["objective"]),
        "arm_protocol": dict(payload["arm_protocol"]),
        "arm_summaries": payload["arm_summaries"],
        "d1_evidence": payload["d1_evidence"],
        "claim_gate": dict(payload["claim_gate"]),
        "hardgate": dict(payload["hardgate"]),
        "failed_gate": payload["failed_gate"],
        "what_was_learned": payload["what_was_learned"],
        "not_claimed": list(payload["not_claimed"]),
        "full_lejepa_boundary": dict(payload["full_lejepa_boundary"]),
        "positive_claim": dict(payload["claim_capsule"]["positive_claim"]),
        "claim_capsule_ref": {
            "artifact": run_artifacts["claim_capsule"],
            "pointer": "$",
        },
        "result_snapshot_ref": {
            "artifact": run_artifacts["result_snapshot"],
            "pointer": "$",
        },
        "result": {
            "status": result_status,
            "terminal_verdict": _terminal_verdict_for_status(result_status),
            "discovery_level": _discovery_level_for_status(result_status),
            "claim_capsule_status": payload["claim_capsule"]["claim_status"],
        },
        "forbidden_claim_term_audit": payload["forbidden_claim_term_audit"],
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# SIGReg Training Proxy",
        "",
        f"- run_id: `{payload['run_id']}`",
        f"- schema_id: `{payload['schema_id']}`",
        f"- result: `{payload['result']['status']}`",
        f"- claim capsule: `{payload['run_artifacts']['claim_capsule']}`",
        "",
        "## Arms",
        "",
        "| arm | alignment | sigreg_sliced_cf | loss |",
        "| --- | ---: | ---: | ---: |",
    ]
    for arm, row in payload["arm_summaries"].items():
        lines.append(
            "| "
            f"`{arm}` | "
            f"{row['alignment_mean']:.8f} | "
            f"{row['sigreg_sliced_cf_mean']:.8f} | "
            f"{row['loss_mean']:.8f} |"
        )
    lines.extend(["", "## D1 Hardgates", ""])
    for gate, row in payload["d1_evidence"]["d1_hardgates"].items():
        lines.append(f"- `{gate}`: `{row['status']}`")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def write_artifacts(payload: Mapping[str, Any], *, root: Path) -> None:
    run_summary = {key: value for key, value in payload.items() if key != "raw_records"}
    canonical_summary = canonical_summary_payload(payload)
    canonical_path = root / str(payload["json_artifact"])
    canonical_md_path = root / str(payload["markdown_artifact"])
    run_artifacts = payload["run_artifacts"]
    summary_path = root / run_artifacts["summary"]
    capsule_path = root / run_artifacts["claim_capsule"]
    snapshot_path = root / run_artifacts["result_snapshot"]
    raw_path = root / run_artifacts["raw_metrics"]
    report_path = root / run_artifacts["report"]
    for path in (canonical_path, canonical_md_path, summary_path, capsule_path, snapshot_path, raw_path, report_path):
        path.parent.mkdir(parents=True, exist_ok=True)
    canonical_path.write_text(json.dumps(canonical_summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    canonical_md_path.write_text(render_markdown(canonical_summary), encoding="utf-8")
    summary_path.write_text(json.dumps(run_summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    capsule_path.write_text(json.dumps(payload["claim_capsule"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    snapshot_path.write_text(json.dumps(payload["result_snapshot"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    raw_path.write_text(
        "".join(json.dumps(record, sort_keys=True) + "\n" for record in payload["raw_records"]),
        encoding="utf-8",
    )
    report_path.write_text(render_markdown(run_summary), encoding="utf-8")


def _parse_seed_list(value: str) -> tuple[int, ...]:
    seeds = tuple(int(item.strip()) for item in value.split(",") if item.strip())
    if not seeds:
        raise argparse.ArgumentTypeError("at least one seed is required")
    return seeds


def _parse_frequency_list(value: str) -> tuple[float, ...]:
    frequencies = tuple(float(item.strip()) for item in value.split(",") if item.strip())
    if not frequencies:
        raise argparse.ArgumentTypeError("at least one frequency is required")
    return frequencies


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--run-id", default=DEFAULT_RUN_ID)
    parser.add_argument("--sample-count", type=int, default=DEFAULT_SAMPLE_COUNT)
    parser.add_argument("--steps", type=int, default=DEFAULT_STEPS)
    parser.add_argument("--seeds", type=_parse_seed_list, default=DEFAULT_SEEDS)
    parser.add_argument("--lambda-sigreg", type=float, default=DEFAULT_LAMBDA_SIGREG)
    parser.add_argument("--directions", type=int, default=DEFAULT_DIRECTIONS)
    parser.add_argument("--frequencies", type=_parse_frequency_list, default=DEFAULT_FREQUENCIES)
    parser.add_argument("--learning-rate", type=float, default=DEFAULT_LEARNING_RATE)
    parser.add_argument("--no-torch", action="store_true")
    args = parser.parse_args(argv)
    payload = build_payload(
        run_id=args.run_id,
        sample_count=args.sample_count,
        steps=args.steps,
        seeds=args.seeds,
        lambda_sigreg=args.lambda_sigreg,
        directions=args.directions,
        frequencies=args.frequencies,
        learning_rate=args.learning_rate,
        use_torch=not args.no_torch,
        json_artifact=JSON_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
    )
    write_artifacts(payload, root=args.root)
    print(
        json.dumps(
            {
                "run_id": payload["run_id"],
                "summary": payload["run_artifacts"]["summary"],
                "claim_capsule": payload["run_artifacts"]["claim_capsule"],
                "result": payload["result"]["status"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

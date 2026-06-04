#!/usr/bin/env python3
"""Classify training-choice ledger risk as h-observable or ledger-only."""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
from typing import Any, Mapping

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.debt import assess_debt
from bedc_quality_lab.mixing import DEFAULT_MIXING, mix_latents
from bedc_quality_lab.toy_world import make_toy_batch
from scripts import run_gaussian_ou_distinction_head as distinction
from scripts import run_gap_head_robustness_sweep as robustness
from scripts.experiment_stats import metric_stats
from scripts.run_gaussian_ou_gap_ledger_head import (
    BETA,
    GAP_CHANNELS,
    PRIMARY_EPSILON,
    PRIMARY_TAU,
    _fit_gap_head,
    _metrics_for_arm,
    _predict_gap_head,
    _primary_gap_sound,
)
from scripts.run_gap_ledger_head_on_h import (
    FORBIDDEN_INFERENCE_COLUMNS,
    MATCHED_RANDOM_ARM,
    QUALITY_COLUMNS,
    _assert_inference_columns,
    _build_inference_features,
    _matched_random_gap_labels,
)


LOCAL_SCHEMA_ID = "bedc-quality-lab:training-choice-observability-sidecar"
ARTIFACT_ID = "bedc-quality-lab:training-choice-observability"
JSON_ARTIFACT = "runs/training_choice_observability.json"
REPORT_ARTIFACT = "runs/training_choice_observability.md"
CANONICAL_ROLE = "sidecar_not_in_" + "CANONICAL" + "_REPORTS"
SAMPLE_COUNT = 384
RHO = 0.82
SEEDS = (11, 23, 37, 53, 71, 89)
REFERENCE_ARM_ID = "deterministic_standardization_reference"
TORCH_REFERENCE_STEPS = 80
UNDERTRAINED_STEPS = 8
LR = 2.0e-3
WEIGHT_DECAY = 1.0e-4
EPS = 1.0e-12

NOT_CLAIMED = (
    "no formal BEDC closure claim",
    "no global optimizer behavior claim",
    "no full LeJEPA conclusion",
    "no all-model or behavior conclusion",
    "no universal training-choice claim",
    "no promotion claim",
    "no total score, rank, grade, or hidden cost weight",
)
REVOKE_CONDITIONS = (
    "revoke observed-debt if learned-vs-matched-random CI separation disappears",
    "revoke observed-debt if matched-random crosses the positive ceiling",
    "revoke observed-debt if learned unlogged-error reduction is not above control",
    "revoke any claim if forbidden-feature audit fails",
    "revoke any claim if seed, split, source, or declared training-choice pairing fails",
)


@dataclass(frozen=True)
class TrainingChoiceArmSpec:
    arm_id: str
    role: str
    training_family: str
    optimizer_family: str
    steps: int
    lr: float
    weight_decay: float
    use_torch: bool
    ledger_certificate_steps: int
    boundary_when_unavailable: bool = False
    declared_training_choice_axis: str = "steps"


@dataclass(frozen=True)
class ProtocolFingerprint:
    seed: int
    sample_count: int
    rho: float
    train_index_checksum: int
    eval_index_checksum: int
    train_count: int
    eval_count: int
    overlap_count: int
    source_name: str = "gaussian-ou-toy-world"
    latent_distribution: str = "gaussian"
    mixing: str = DEFAULT_MIXING
    model_loss_family: str = "tiny-encoder-representation-loss-or-deterministic-standardization"
    inference_feature_builder: str = "scripts/run_gap_ledger_head_on_h.py::_build_inference_features"


def training_choice_arms() -> tuple[TrainingChoiceArmSpec, ...]:
    return (
        TrainingChoiceArmSpec(
            arm_id=REFERENCE_ARM_ID,
            role="reference",
            training_family="deterministic-standardization",
            optimizer_family="none",
            steps=0,
            lr=0.0,
            weight_decay=0.0,
            use_torch=False,
            ledger_certificate_steps=0,
            boundary_when_unavailable=False,
            declared_training_choice_axis="training_family",
        ),
        TrainingChoiceArmSpec(
            arm_id="adamw_reference",
            role="torch_reference",
            training_family="align-cov-mean",
            optimizer_family="AdamW",
            steps=TORCH_REFERENCE_STEPS,
            lr=LR,
            weight_decay=WEIGHT_DECAY,
            use_torch=True,
            ledger_certificate_steps=TORCH_REFERENCE_STEPS,
            boundary_when_unavailable=True,
        ),
        TrainingChoiceArmSpec(
            arm_id="adamw_undertrained",
            role="training_choice_candidate",
            training_family="align-cov-mean",
            optimizer_family="AdamW",
            steps=UNDERTRAINED_STEPS,
            lr=LR,
            weight_decay=WEIGHT_DECAY,
            use_torch=True,
            ledger_certificate_steps=UNDERTRAINED_STEPS,
            boundary_when_unavailable=True,
        ),
    )


def _index_checksum(indices: np.ndarray) -> int:
    weights = np.arange(1, indices.shape[0] + 1, dtype=np.int64)
    return int(np.sum((indices.astype(np.int64) + 1) * weights))


def _standardize_fit(x: np.ndarray) -> dict[str, np.ndarray]:
    value = np.asarray(x, dtype=np.float64)
    mean = np.mean(value, axis=0, keepdims=True)
    scale = np.std(value, axis=0, keepdims=True)
    scale = np.where(scale <= EPS, 1.0, scale)
    return {"mean": mean, "scale": scale}


def _standardize_apply(x: np.ndarray, state: Mapping[str, np.ndarray]) -> np.ndarray:
    return ((np.asarray(x, dtype=np.float64) - state["mean"]) / state["scale"]).astype(np.float64)


def _encode_deterministic(
    *,
    train_x: np.ndarray,
    all_x: np.ndarray,
    all_x_pair: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    state = _standardize_fit(train_x)
    return _standardize_apply(all_x, state), _standardize_apply(all_x_pair, state)


def _encode_torch(
    *,
    train_x: np.ndarray,
    train_x_pair: np.ndarray,
    all_x: np.ndarray,
    all_x_pair: np.ndarray,
    seed: int,
    steps: int,
    lr: float,
    weight_decay: float,
) -> tuple[np.ndarray, np.ndarray]:
    from bedc_quality_lab.model import (
        build_tiny_encoder,
        choose_device,
        representation_loss,
        set_deterministic_seed,
    )

    import torch

    set_deterministic_seed(seed)
    device = choose_device()
    encoder = build_tiny_encoder().to(device)
    optimizer = torch.optim.AdamW(
        encoder.parameters(),
        lr=float(lr),
        weight_decay=float(weight_decay),
    )
    x_t = torch.as_tensor(train_x, dtype=torch.float32, device=device)
    x_pair_t = torch.as_tensor(train_x_pair, dtype=torch.float32, device=device)
    for _ in range(int(steps)):
        optimizer.zero_grad(set_to_none=True)
        h = encoder(x_t)
        h_pair = encoder(x_pair_t)
        loss = representation_loss(h, h_pair)
        loss.backward()
        optimizer.step()
    with torch.no_grad():
        all_t = torch.as_tensor(all_x, dtype=torch.float32, device=device)
        all_pair_t = torch.as_tensor(all_x_pair, dtype=torch.float32, device=device)
        h_all = encoder(all_t).detach().cpu().numpy().astype(np.float64)
        h_pair_all = encoder(all_pair_t).detach().cpu().numpy().astype(np.float64)
    return h_all, h_pair_all


def _quality_scalars_for_arm(spec: TrainingChoiceArmSpec) -> np.ndarray:
    certificate_ratio = min(1.0, max(0.0, float(spec.ledger_certificate_steps) / 2000.0))
    step_ratio = min(1.0, max(0.0, float(spec.steps) / float(TORCH_REFERENCE_STEPS)))
    deterministic_flag = 0.0 if spec.use_torch else 1.0
    lr_scale = 0.0 if spec.lr <= 0.0 else min(1.0, math.log10(1.0 + spec.lr * 1000.0) / 2.0)
    return np.array(
        [certificate_ratio, step_ratio, deterministic_flag, lr_scale],
        dtype=np.float64,
    )


def _probe_blocks(
    *,
    probes: Mapping[str, Any],
    h: np.ndarray,
    h_pair: np.ndarray,
) -> dict[str, np.ndarray]:
    scores = []
    margins = []
    transitions = []
    for name in distinction.DISTINCTIONS:
        pred = distinction._predict_probe(probes[name], h)
        pair_pred = distinction._predict_probe(probes[name], h_pair)
        scores.append(pred["probabilities"])
        margins.append(np.abs(pred["logits"]))
        transitions.append(np.abs(pred["probabilities"] - pair_pred["probabilities"]))
    return {
        "score": np.column_stack(scores).astype(np.float64),
        "margin": np.column_stack(margins).astype(np.float64),
        "transition_delta": np.column_stack(transitions).astype(np.float64),
    }


def _feature_audit(columns: list[str]) -> dict[str, Any]:
    forbidden_present = [
        column
        for column in columns
        if column in FORBIDDEN_INFERENCE_COLUMNS
        or column.split(":", 1)[0] in FORBIDDEN_INFERENCE_COLUMNS
    ]
    try:
        _assert_inference_columns(columns)
    except ValueError as exc:
        return {
            "status": "fail",
            "reason": str(exc),
            "forbidden_present": forbidden_present,
            "forbidden_inference_columns": list(FORBIDDEN_INFERENCE_COLUMNS),
        }
    return {
        "status": "pass",
        "reason": "inference columns exclude forbidden ground-truth and label channels",
        "forbidden_present": forbidden_present,
        "forbidden_inference_columns": list(FORBIDDEN_INFERENCE_COLUMNS),
    }


def _optimizer_ledger_item(spec: TrainingChoiceArmSpec) -> dict[str, Any]:
    source_spec = {
        "name": "gaussian-ou-toy-world",
        "latent_dim": 2,
        "sample_count": SAMPLE_COUNT,
        "rho": RHO,
        "latent_distribution": "gaussian",
        "mixing": DEFAULT_MIXING,
        "transition_kernel": {"isotropic": True, "anisotropy_gap": 0.0},
        "action_transition_identified": True,
    }
    classifier_spec = {
        "name": spec.arm_id,
        "output_dim": 2,
        "training": spec.training_family,
        "optimizer_family": spec.optimizer_family,
        "optimizer_certificate_steps": int(spec.ledger_certificate_steps),
    }
    assessment = assess_debt(
        {},
        source_spec,
        classifier_spec,
        {"name": "fixed-seed-paired-source", "multi_seed": True},
    )
    for item in assessment.items:
        if item.kind == "classifier" and item.residue == "optimizer-certificate":
            return asdict(item)
    raise RuntimeError("optimizer-certificate debt row missing")


def _surface_for_seed(*, spec: TrainingChoiceArmSpec, seed: int) -> dict[str, Any]:
    batch = make_toy_batch(SAMPLE_COUNT, rho=RHO, seed=seed)
    z = distinction._require_finite("z", batch.z)
    z_pair = distinction._require_finite("z_pair", batch.z_pair)
    train_idx, eval_idx = distinction._train_eval_split(z.shape[0], seed=seed)
    if spec.use_torch:
        h, h_pair = _encode_torch(
            train_x=batch.x[train_idx],
            train_x_pair=batch.x_pair[train_idx],
            all_x=batch.x,
            all_x_pair=batch.x_pair,
            seed=seed,
            steps=spec.steps,
            lr=spec.lr,
            weight_decay=spec.weight_decay,
        )
    else:
        h, h_pair = _encode_deterministic(
            train_x=batch.x[train_idx],
            all_x=batch.x,
            all_x_pair=batch.x_pair,
        )

    high_threshold = distinction._high_energy_threshold(z, train_idx)
    labels = {
        name: distinction._label_truth(name, z, high_energy_threshold=high_threshold)
        for name in distinction.DISTINCTIONS
    }
    pair_labels = {
        name: distinction._label_truth(name, z_pair, high_energy_threshold=high_threshold)
        for name in distinction.DISTINCTIONS
    }
    probes = {
        name: distinction._fit_probe(h[train_idx], label[train_idx])
        for name, label in labels.items()
    }
    blocks = _probe_blocks(probes=probes, h=h, h_pair=h_pair)

    errors = []
    transition_changed = []
    for name in distinction.DISTINCTIONS:
        pred = distinction._predict_probe(probes[name], h)
        errors.append((pred["predictions"] != labels[name]).astype(np.float64))
        transition_changed.append((labels[name] != pair_labels[name]).astype(np.float64))
    prediction_error = np.max(np.column_stack(errors), axis=1)
    transition_unstable = np.max(np.column_stack(transition_changed), axis=1)

    min_margin = np.min(blocks["margin"], axis=1)
    margin_threshold = float(np.quantile(min_margin[train_idx], 0.30))
    low_margin = (min_margin <= margin_threshold).astype(np.float64)

    off_target_rows = []
    for target in distinction.DISTINCTIONS:
        z_changed = distinction._intervene(target, z, z_pair)
        h_changed, _ = (
            _encode_deterministic(
                train_x=batch.x[train_idx],
                all_x=mix_latents(z_changed, DEFAULT_MIXING),
                all_x_pair=batch.x_pair,
            )
            if not spec.use_torch
            else (h, h_pair)
        )
        target_off_target = np.zeros(z.shape[0], dtype=np.float64)
        for name in distinction.DISTINCTIONS:
            if name == target:
                continue
            before = distinction._predict_probe(probes[name], h)["predictions"]
            after = distinction._predict_probe(probes[name], h_changed)["predictions"]
            target_off_target = np.maximum(target_off_target, (before != after).astype(np.float64))
        off_target_rows.append(target_off_target)
    off_target_intervention = np.max(np.column_stack(off_target_rows), axis=1)

    gap_labels = np.column_stack(
        [prediction_error, low_margin, transition_unstable, off_target_intervention]
    ).astype(np.float64)
    features, feature_columns = _build_inference_features(
        h=h,
        score=blocks["score"],
        margin=blocks["margin"],
        transition_delta=blocks["transition_delta"],
        quality_scalars=_quality_scalars_for_arm(spec),
    )
    protocol = ProtocolFingerprint(
        seed=int(seed),
        sample_count=SAMPLE_COUNT,
        rho=RHO,
        train_index_checksum=_index_checksum(train_idx),
        eval_index_checksum=_index_checksum(eval_idx),
        train_count=int(train_idx.shape[0]),
        eval_count=int(eval_idx.shape[0]),
        overlap_count=int(np.intersect1d(train_idx, eval_idx).shape[0]),
    )
    return {
        "features": features,
        "feature_columns": feature_columns,
        "feature_audit": _feature_audit(feature_columns),
        "gap_labels": gap_labels,
        "prediction_error": prediction_error,
        "train_idx": train_idx,
        "eval_idx": eval_idx,
        "protocol": asdict(protocol),
        "gap_label_rates": {
            channel: float(np.mean(gap_labels[:, index]))
            for index, channel in enumerate(GAP_CHANNELS)
        },
        "eval_gap_label_rates": {
            channel: float(np.mean(gap_labels[eval_idx, index]))
            for index, channel in enumerate(GAP_CHANNELS)
        },
    }


def _metric_projection(metrics: Mapping[str, Any]) -> dict[str, Any]:
    primary = _primary_gap_sound(metrics["gap_sound_scan"])
    return {
        "arm": metrics["arm"],
        "failure_detection_auroc": metrics["failure_detection_auroc"],
        "ece": metrics["ece"],
        "unlogged_error_rate": float(metrics["unlogged_error_rate"]),
        "critical_unlogged_error_rate": float(metrics["critical_unlogged_error_rate"]),
        "prediction_error_rate": float(metrics["prediction_error_rate"]),
        "gap_score_mean": float(metrics["gap_score_mean"]),
        "critical_gap_score_mean": float(metrics["critical_gap_score_mean"]),
        "primary_gap_sound": {
            "tau": float(primary["tau"]),
            "epsilon": float(primary["epsilon"]),
            "low_gap_implies_error_within_epsilon": float(
                primary["low_gap_implies_error_within_epsilon"]
            ),
            "error_above_epsilon_implies_gap_at_least_tau": float(
                primary["error_above_epsilon_implies_gap_at_least_tau"]
            ),
            "low_gap_count": int(primary["low_gap_count"]),
            "failure_count": int(primary["failure_count"]),
        },
        "loss": metrics["loss"],
    }


def _run_record(*, spec: TrainingChoiceArmSpec, seed: int, seed_index: int) -> dict[str, Any]:
    surface = _surface_for_seed(spec=spec, seed=seed)
    train_idx = surface["train_idx"]
    eval_idx = surface["eval_idx"]
    heads = _fit_gap_head(surface["features"][train_idx], surface["gap_labels"][train_idx])
    eval_probabilities = _predict_gap_head(heads, surface["features"][eval_idx])
    randomized_labels = _matched_random_gap_labels(surface["gap_labels"], seed=seed)
    random_heads = _fit_gap_head(surface["features"][train_idx], randomized_labels[train_idx])
    random_eval_probabilities = _predict_gap_head(random_heads, surface["features"][eval_idx])
    eval_labels = surface["gap_labels"][eval_idx]
    eval_error = surface["prediction_error"][eval_idx]
    vanilla_probabilities = np.zeros_like(eval_probabilities, dtype=np.float64)
    vanilla_metrics = _metrics_for_arm(
        arm="vanilla",
        probabilities=vanilla_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    learned_metrics = _metrics_for_arm(
        arm="learned_gap_head_on_h",
        probabilities=eval_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    random_metrics = _metrics_for_arm(
        arm=MATCHED_RANDOM_ARM,
        probabilities=random_eval_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    return {
        "seed_index": int(seed_index),
        "seed": int(seed),
        "arm_id": spec.arm_id,
        "protocol": surface["protocol"],
        "feature_audit": surface["feature_audit"],
        "feature_column_count": len(surface["feature_columns"]),
        "feature_columns": list(surface["feature_columns"]),
        "gap_label_rates": surface["gap_label_rates"],
        "eval_gap_label_rates": surface["eval_gap_label_rates"],
        "matched_random_control": {
            "arm": MATCHED_RANDOM_ARM,
            "label_protocol": "seed_deterministic_per_channel_permutation",
            "same_feature_columns": True,
            "same_split": True,
            "same_metric_helper": True,
            "randomized_gap_label_rates": {
                channel: float(np.mean(randomized_labels[:, index]))
                for index, channel in enumerate(GAP_CHANNELS)
            },
        },
        "arms": {
            "vanilla": _metric_projection(vanilla_metrics),
            "learned_gap_head_on_h": _metric_projection(learned_metrics),
            MATCHED_RANDOM_ARM: _metric_projection(random_metrics),
        },
        "comparison": {
            "unlogged_error_reduction_learned": float(
                vanilla_metrics["unlogged_error_rate"] - learned_metrics["unlogged_error_rate"]
            ),
            "unlogged_error_reduction_matched_random": float(
                vanilla_metrics["unlogged_error_rate"] - random_metrics["unlogged_error_rate"]
            ),
        },
    }


def _stats_from_records(records: list[dict[str, Any]], getter: Any) -> dict[str, Any]:
    return metric_stats(float(getter(record)) for record in records)


def _aggregate(records: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "record_count": int(len(records)),
        "seed_order": [int(record["seed"]) for record in records],
        "by_arm": {
            "vanilla": {
                "failure_detection_auroc": _stats_from_records(
                    records, lambda record: record["arms"]["vanilla"]["failure_detection_auroc"]["value"]
                ),
                "unlogged_error_rate": _stats_from_records(
                    records, lambda record: record["arms"]["vanilla"]["unlogged_error_rate"]
                ),
            },
            "learned_gap_head_on_h": {
                "failure_detection_auroc": _stats_from_records(
                    records,
                    lambda record: record["arms"]["learned_gap_head_on_h"]["failure_detection_auroc"]["value"],
                ),
                "unlogged_error_rate": _stats_from_records(
                    records, lambda record: record["arms"]["learned_gap_head_on_h"]["unlogged_error_rate"]
                ),
                "unlogged_error_reduction": _stats_from_records(
                    records, lambda record: record["comparison"]["unlogged_error_reduction_learned"]
                ),
            },
            MATCHED_RANDOM_ARM: {
                "failure_detection_auroc": _stats_from_records(
                    records,
                    lambda record: record["arms"][MATCHED_RANDOM_ARM]["failure_detection_auroc"]["value"],
                ),
                "unlogged_error_rate": _stats_from_records(
                    records, lambda record: record["arms"][MATCHED_RANDOM_ARM]["unlogged_error_rate"]
                ),
                "unlogged_error_reduction": _stats_from_records(
                    records,
                    lambda record: record["comparison"]["unlogged_error_reduction_matched_random"],
                ),
            },
        },
    }


def _protocol_audit(
    reference_protocols: Mapping[int, Mapping[str, Any]],
    candidate_protocols: Mapping[int, Mapping[str, Any]],
    reference_spec: TrainingChoiceArmSpec,
    candidate_spec: TrainingChoiceArmSpec,
) -> dict[str, Any]:
    if set(reference_protocols) != set(candidate_protocols):
        return {"status": "fail", "reason": "seed grid differs"}
    mismatches = []
    for seed in sorted(reference_protocols):
        ref = dict(reference_protocols[seed])
        candidate = dict(candidate_protocols[seed])
        if ref != candidate:
            mismatches.append({"seed": int(seed), "reference": ref, "candidate": candidate})
    changed = []
    for field in ("training_family", "optimizer_family", "steps", "lr", "weight_decay", "use_torch"):
        if getattr(reference_spec, field) != getattr(candidate_spec, field):
            changed.append(field)
    allowed = {"steps"} if candidate_spec.declared_training_choice_axis == "steps" else {
        candidate_spec.declared_training_choice_axis
    }
    axis_ok = set(changed).issubset(allowed) and bool(changed)
    status = "pass" if not mismatches and axis_ok else "fail"
    return {
        "status": status,
        "reason": "paired source/split with only declared training-choice axis varied"
        if status == "pass"
        else "pairing or training-choice axis audit failed",
        "seed_count": len(reference_protocols),
        "protocol_mismatches": mismatches,
        "changed_training_choice_fields": changed,
        "declared_training_choice_axis": candidate_spec.declared_training_choice_axis,
        "allowed_changed_fields": sorted(allowed),
    }


def _control_verdict(aggregate: Mapping[str, Any]) -> dict[str, Any]:
    matched = aggregate["by_arm"][MATCHED_RANDOM_ARM]
    auroc = float(matched["failure_detection_auroc"]["mean"])
    positive = (
        auroc >= robustness.AUROC_POSITIVE_THRESHOLD
        or float(matched["failure_detection_auroc"]["ci95_high"])
        > robustness.MATCHED_RANDOM_AUROC_CEILING
    )
    return {
        "positive": bool(positive),
        "checks": {
            "auroc_mean_below_positive_threshold": auroc < robustness.AUROC_POSITIVE_THRESHOLD,
            "auroc_ci95_high_at_or_below_ceiling": float(
                matched["failure_detection_auroc"]["ci95_high"]
            )
            <= robustness.MATCHED_RANDOM_AUROC_CEILING,
        },
    }


def _hardgates(
    *,
    protocol_audit: Mapping[str, Any],
    aggregate: Mapping[str, Any],
    feature_audit: Mapping[str, Any],
) -> dict[str, Any]:
    learned = aggregate["by_arm"]["learned_gap_head_on_h"]
    matched = aggregate["by_arm"][MATCHED_RANDOM_ARM]
    learned_auroc = learned["failure_detection_auroc"]
    matched_auroc = matched["failure_detection_auroc"]
    learned_reduction = learned["unlogged_error_reduction"]
    matched_reduction = matched["unlogged_error_reduction"]
    control = _control_verdict(aggregate)
    hg2_pass = (
        float(learned_auroc["ci95_low"]) > float(matched_auroc["ci95_high"])
        and float(learned_auroc["mean"]) >= robustness.AUROC_POSITIVE_THRESHOLD
        and float(matched_auroc["ci95_high"]) <= robustness.MATCHED_RANDOM_AUROC_CEILING
    )
    hg3_pass = (
        float(learned_reduction["ci95_low"]) > float(matched_reduction["ci95_high"])
        and float(learned_reduction["mean"]) > 0.0
    )
    return {
        "HG-TCO-1": {
            "status": protocol_audit["status"],
            "criterion": "seed, split, source, feature builder, and model/loss are paired; only declared training-choice axis varies",
            "audit": dict(protocol_audit),
        },
        "HG-TCO-2": {
            "status": "pass" if hg2_pass else "fail",
            "criterion": (
                "learned AUROC ci95_low > matched-random AUROC ci95_high, learned "
                f"mean >= {robustness.AUROC_POSITIVE_THRESHOLD}, and matched-random "
                f"ci95_high <= {robustness.MATCHED_RANDOM_AUROC_CEILING}"
            ),
            "learned_auroc": learned_auroc,
            "matched_random_auroc": matched_auroc,
        },
        "HG-TCO-3": {
            "status": "pass" if hg3_pass else "fail",
            "criterion": "learned unlogged-error reduction ci95_low > matched-random ci95_high and learned mean reduction > 0",
            "learned_unlogged_error_reduction": learned_reduction,
            "matched_random_unlogged_error_reduction": matched_reduction,
        },
        "HG-TCO-4": {
            "status": feature_audit["status"],
            "criterion": "inference features exclude z, z_pair, gap labels, prediction_error, and eval_gap_labels",
            "audit": dict(feature_audit),
        },
        "HG-TCO-5": {
            "status": "pass"
            if (not control["positive"] and protocol_audit["status"] == "pass" and feature_audit["status"] == "pass")
            else "fail",
            "criterion": "strict positivity is conjunction-only and matched-random is non-positive",
            "control_verdict": control,
        },
    }


def _classification(*, hardgates: Mapping[str, Mapping[str, Any]], ledger_item: Mapping[str, Any]) -> str:
    failed = [name for name, gate in hardgates.items() if gate["status"] != "pass"]
    control = hardgates["HG-TCO-5"]["control_verdict"]
    if control["positive"] or hardgates["HG-TCO-4"]["status"] != "pass":
        return "invalid_non_claim"
    if not failed:
        return "observed-debt"
    if ledger_item.get("status") in {"open", "partial"}:
        return "ledger-risk-only"
    return "no-ledger-risk-non-claim"


def _boundary_arm_result(spec: TrainingChoiceArmSpec, reason: str) -> dict[str, Any]:
    return {
        "arm_id": spec.arm_id,
        "arm_spec": asdict(spec),
        "classification": "boundary-only",
        "reason": reason,
        "ledger_item": _optimizer_ledger_item(spec),
        "hardgates": {
            f"HG-TCO-{index}": {"status": "boundary", "criterion": "torch arm unavailable"}
            for index in range(1, 6)
        },
        "records": [],
    }


def _arm_result(
    *,
    spec: TrainingChoiceArmSpec,
    reference_spec: TrainingChoiceArmSpec,
    reference_protocols: Mapping[int, Mapping[str, Any]],
) -> dict[str, Any]:
    try:
        records = [
            _run_record(spec=spec, seed=int(seed), seed_index=index)
            for index, seed in enumerate(SEEDS)
        ]
    except Exception as exc:
        if spec.boundary_when_unavailable:
            return _boundary_arm_result(spec, f"torch arm unavailable or failed: {exc}")
        raise
    aggregate = _aggregate(records)
    protocols = {int(record["seed"]): dict(record["protocol"]) for record in records}
    feature_statuses = [record["feature_audit"]["status"] for record in records]
    feature_audit = {
        "status": "pass" if all(status == "pass" for status in feature_statuses) else "fail",
        "seed_feature_audit_count": len(feature_statuses),
        "forbidden_present": sorted(
            {
                column
                for record in records
                for column in record["feature_audit"].get("forbidden_present", [])
            }
        ),
        "forbidden_inference_columns": list(FORBIDDEN_INFERENCE_COLUMNS),
    }
    protocol_audit = _protocol_audit(reference_protocols, protocols, reference_spec, spec)
    ledger_item = _optimizer_ledger_item(spec)
    if spec.role == "torch_reference":
        return {
            "arm_id": spec.arm_id,
            "arm_spec": asdict(spec),
            "classification": "reference-only",
            "ledger_item": ledger_item,
            "hardgates": {
                "HG-TCO-1": {
                    "status": "reference",
                    "criterion": "fixed current AdamW reference arm is not a positive observed-debt candidate",
                    "audit": protocol_audit,
                }
            },
            "aggregate": aggregate,
            "records": records,
        }
    gates = _hardgates(
        protocol_audit=protocol_audit,
        aggregate=aggregate,
        feature_audit=feature_audit,
    )
    classification = _classification(hardgates=gates, ledger_item=ledger_item)
    return {
        "arm_id": spec.arm_id,
        "arm_spec": asdict(spec),
        "classification": classification,
        "ledger_item": ledger_item,
        "hardgates": gates,
        "aggregate": aggregate,
        "records": records,
    }


def _forbidden_claim_term_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    text = json.dumps(payload, sort_keys=True).lower()
    hits = [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in text]
    return {
        "status": "pass" if not hits else "fail",
        "hits": hits,
        "forbidden_positive_claim_terms_pointer": "bedc_quality_lab.claim_terms.FORBIDDEN_POSITIVE_CLAIM_TERMS",
    }


def build_payload(*, generated_at: str | None = None) -> dict[str, Any]:
    arms = training_choice_arms()
    reference_spec = arms[0]
    reference_records = [
        _run_record(spec=reference_spec, seed=int(seed), seed_index=index)
        for index, seed in enumerate(SEEDS)
    ]
    reference_protocols = {
        int(record["seed"]): dict(record["protocol"])
        for record in reference_records
    }
    reference_result = {
        "arm_id": reference_spec.arm_id,
        "arm_spec": asdict(reference_spec),
        "classification": "reference-only",
        "ledger_item": _optimizer_ledger_item(reference_spec),
        "aggregate": _aggregate(reference_records),
        "records": reference_records,
    }
    arm_results = [
        _arm_result(
            spec=spec,
            reference_spec=arms[1] if spec.use_torch else reference_spec,
            reference_protocols=reference_protocols,
        )
        for spec in arms[1:]
    ]
    all_results = [reference_result, *arm_results]
    boundary_ledger = [
        {
            "arm_id": result["arm_id"],
            "kind": result["classification"],
            "reason": result.get("reason", "hardgate result prevents positive observed-debt"),
            "ledger_status": result["ledger_item"]["status"],
            "failed_gates": [
                name
                for name, gate in result.get("hardgates", {}).items()
                if gate["status"] not in {"pass"}
            ],
            "evidence_pointer": "$.training_choice_observability.arms[*].hardgates",
        }
        for result in arm_results
        if result["classification"] not in {"observed-debt", "reference-only"}
    ]
    summary = {
        "status": "pointer-only",
        "observed_debt_arm_count": sum(
            1 for result in arm_results if result["classification"] == "observed-debt"
        ),
        "ledger_risk_only_arm_count": sum(
            1 for result in arm_results if result["classification"] == "ledger-risk-only"
        ),
        "boundary_or_invalid_arm_count": sum(
            1
            for result in arm_results
            if result["classification"] in {"boundary-only", "invalid_non_claim"}
        ),
    }
    payload: dict[str, Any] = {
        "schema_id": LOCAL_SCHEMA_ID,
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at or datetime.now(timezone.utc).isoformat(),
        "status": "pointer-only",
        "canonical_role": CANONICAL_ROLE,
        "training_choice_observability": {
            **summary,
            "arms": all_results,
            "classification_rule": "all HG-TCO gates pass gives observed-debt; ledger open or partial with any hardgate fail gives ledger-risk-only; matched-random positive or forbidden feature gives invalid non-claim",
        },
        "boundary_ledger": boundary_ledger,
        "not_claimed": list(NOT_CLAIMED),
        "revoke_conditions": list(REVOKE_CONDITIONS),
        "config": {
            "source_surface": "Gaussian-OU",
            "sample_count": SAMPLE_COUNT,
            "rho": RHO,
            "seeds": list(SEEDS),
            "train_eval_split": "scripts/run_gaussian_ou_distinction_head.py::_train_eval_split",
            "auroc_positive_threshold": robustness.AUROC_POSITIVE_THRESHOLD,
            "matched_random_auroc_ceiling": robustness.MATCHED_RANDOM_AUROC_CEILING,
            "gap_channels": list(GAP_CHANNELS),
            "quality_columns": list(QUALITY_COLUMNS),
        },
        "source_artifacts": {
            "generation_script": "scripts/run_training_choice_observability.py",
            "canonical_torch_reference": "scripts/run_gaussian_ou_lejepa.py::_torch_encoder",
            "h_feature_builder": "scripts/run_gap_ledger_head_on_h.py::_build_inference_features",
            "forbidden_column_audit": "scripts/run_gap_ledger_head_on_h.py::_assert_inference_columns",
            "matched_random_control": "scripts/run_gap_ledger_head_on_h.py::_matched_random_gap_labels",
            "gap_head_metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm",
            "distinction_probe_helper": "scripts/run_gaussian_ou_distinction_head.py",
            "optimizer_ledger_scorer": "bedc_quality_lab.debt.assess_debt",
            "claim_terms": "bedc_quality_lab.claim_terms.FORBIDDEN_POSITIVE_CLAIM_TERMS",
        },
    }
    payload["forbidden_claim_term_audit"] = _forbidden_claim_term_audit(payload)
    return payload


def _render_stats(stats: Mapping[str, Any]) -> str:
    return (
        f"mean={float(stats['mean']):.3f}, "
        f"ci95=[{float(stats['ci95_low']):.3f}, {float(stats['ci95_high']):.3f}]"
    )


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Training Choice Observability",
        "",
        f"- status: {payload['status']}",
        f"- canonical_role: {payload['canonical_role']}",
        f"- local_schema_id: {payload['schema_id']}",
        f"- artifact_id: {payload['artifact_id']}",
        "",
        "## Classifications",
        "",
        "| arm | classification | ledger status | HG-TCO failed | learned AUROC | matched AUROC | learned reduction | matched reduction |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for arm in payload["training_choice_observability"]["arms"]:
        gates = arm.get("hardgates", {})
        failed = ",".join(name for name, gate in gates.items() if gate["status"] != "pass") or "none"
        if "aggregate" in arm:
            learned = arm["aggregate"]["by_arm"]["learned_gap_head_on_h"]
            matched = arm["aggregate"]["by_arm"][MATCHED_RANDOM_ARM]
            learned_auroc = _render_stats(learned["failure_detection_auroc"])
            matched_auroc = _render_stats(matched["failure_detection_auroc"])
            learned_reduction = _render_stats(learned["unlogged_error_reduction"])
            matched_reduction = _render_stats(matched["unlogged_error_reduction"])
        else:
            learned_auroc = matched_auroc = learned_reduction = matched_reduction = "boundary"
        lines.append(
            f"| {arm['arm_id']} | {arm['classification']} | {arm['ledger_item']['status']} | "
            f"{failed} | {learned_auroc} | {matched_auroc} | {learned_reduction} | {matched_reduction} |"
        )
    lines.extend(
        [
            "",
            "## Not Claimed",
            "",
            *[f"- {item}" for item in payload["not_claimed"]],
            "",
            "## Revoke Conditions",
            "",
            *[f"- {item}" for item in payload["revoke_conditions"]],
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(payload: Mapping[str, Any], *, root: Path) -> None:
    json_path = root / JSON_ARTIFACT
    report_path = root / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default=".", help="bedc-quality-lab root")
    args = parser.parse_args(argv)
    root = Path(args.root).resolve()
    payload = build_payload()
    write_artifacts(payload, root=root)
    summary = payload["training_choice_observability"]
    print(
        "training_choice_observability: "
        f"observed={summary['observed_debt_arm_count']} "
        f"ledger_only={summary['ledger_risk_only_arm_count']} "
        f"boundary_or_invalid={summary['boundary_or_invalid_arm_count']} "
        f"artifact={JSON_ARTIFACT}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

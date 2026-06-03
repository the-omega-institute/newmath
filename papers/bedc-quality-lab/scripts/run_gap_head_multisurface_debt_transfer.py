#!/usr/bin/env python3
"""Run gap-head-on-h observed-debt transfer over multiple source surfaces."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
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
from bedc_quality_lab.latent_distribution import LatentDistributionSpec
from bedc_quality_lab.mixing import DEFAULT_MIXING, mix_latents
from bedc_quality_lab.toy_world import make_toy_batch
from bedc_quality_lab.transition import TransitionKernelSpec
from scripts import run_gap_head_observed_debt_transfer as observed_transfer
from scripts import run_gap_head_robustness_sweep as robustness
from scripts import run_gap_ledger_head_on_h as producer
from scripts import run_observed_debt_sweep as observed_debt
from scripts.experiment_stats import metric_stats


JSON_ARTIFACT = "runs/gap_head_multisurface_debt_transfer.json"
REPORT_ARTIFACT = "runs/gap_head_multisurface_debt_transfer.md"
ARTIFACT_ID = "bedc-quality-lab:gap-head-multisurface-debt-transfer"
TRANSFER_STATUS_POINTER = "$.gap_head_multisurface_debt_transfer.multi_surface_status"
COUNTABLE_SURFACE_COUNT = 4
NOT_CLAIMED = (
    "no mechanism closure claim",
    "no D5-M promotion",
    "no global quality conclusion",
    "no full LeJEPA conclusion",
    "no claim outside the listed countable runnable surfaces",
    "no inference-time use of z, z_pair, gap_label, prediction_error, or eval_gap_labels",
)


@dataclass(frozen=True)
class MultiSurfaceSpec:
    surface_id: str
    role: str
    countable_hg_a2_2: bool
    sample_count: int
    seeds: tuple[int, ...]
    rho: float
    transition_kernel: TransitionKernelSpec | None = None
    latent_distribution: LatentDistributionSpec | None = None
    mixing: str = DEFAULT_MIXING
    boundary_reason: str | None = None
    evidence_pointer: str | None = None

    def registry_row(self) -> dict[str, Any]:
        return {
            "surface_id": self.surface_id,
            "role": self.role,
            "countable_hg_a2_2": bool(self.countable_hg_a2_2),
            "sample_count": int(self.sample_count),
            "seed_count": int(len(self.seeds)),
            "rho": float(self.rho),
            "transition_kernel": self.transition_kernel.to_source_spec()
            if self.transition_kernel is not None
            else None,
            "latent_distribution": self.latent_distribution.to_source_spec()
            if self.latent_distribution is not None
            else LatentDistributionSpec.gaussian().to_source_spec(),
            "mixing": self.mixing,
            "boundary_reason": self.boundary_reason,
            "evidence_pointer": self.evidence_pointer,
        }


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _default_seeds() -> tuple[int, ...]:
    return tuple(
        int(seed)
        for seed in observed_debt._seeds(
            "C3",
            observed_debt.DEFAULT_SEED_COUNT_BY_AXIS["C3"],
        )
    )


def _surface_registry() -> tuple[MultiSurfaceSpec, ...]:
    seeds = _default_seeds()
    baseline_sample_count = int(observed_debt.BASELINE_SAMPLE_COUNT)
    return (
        MultiSurfaceSpec(
            surface_id="clean-gaussian-ou",
            role="runnable",
            countable_hg_a2_2=True,
            sample_count=baseline_sample_count,
            seeds=seeds,
            rho=observed_debt.RHO,
            evidence_pointer="bedc_quality_lab.toy_world.make_toy_batch",
        ),
        MultiSurfaceSpec(
            surface_id="anisotropic-rho-0p95-0p30",
            role="runnable",
            countable_hg_a2_2=True,
            sample_count=baseline_sample_count,
            seeds=seeds,
            rho=observed_debt.RHO,
            transition_kernel=TransitionKernelSpec(rho_by_axis=(0.95, 0.30)),
            evidence_pointer="bedc_quality_lab.transition.TransitionKernelSpec",
        ),
        MultiSurfaceSpec(
            surface_id="laplace-latent",
            role="runnable",
            countable_hg_a2_2=True,
            sample_count=baseline_sample_count,
            seeds=seeds,
            rho=observed_debt.RHO,
            latent_distribution=LatentDistributionSpec.laplace(),
            evidence_pointer="bedc_quality_lab.latent_distribution.LatentDistributionSpec.laplace",
        ),
        MultiSurfaceSpec(
            surface_id="sample-count-1024",
            role="runnable",
            countable_hg_a2_2=True,
            sample_count=1024,
            seeds=seeds,
            rho=observed_debt.RHO,
            evidence_pointer="scripts/run_observed_debt_sweep.py::C3 sample_count surface",
        ),
        MultiSurfaceSpec(
            surface_id="student-t-latent",
            role="deferred",
            countable_hg_a2_2=False,
            sample_count=baseline_sample_count,
            seeds=seeds,
            rho=observed_debt.RHO,
            latent_distribution=LatentDistributionSpec.student_t(df=3),
            boundary_reason=(
                "student-t latent is declared in the registry but deferred outside the first-pass "
                "HG-A2-2 countable pool"
            ),
            evidence_pointer="bedc_quality_lab.latent_distribution.LatentDistributionSpec.student_t",
        ),
        MultiSurfaceSpec(
            surface_id="realnvp-spiral-mixing",
            role="boundary_only",
            countable_hg_a2_2=False,
            sample_count=baseline_sample_count,
            seeds=seeds,
            rho=observed_debt.RHO,
            mixing="realnvp_coupling",
            boundary_reason=(
                "the legal source API accepts one mixing family; two-stage realnvp-to-spiral "
                "composition would require a sidecar implementation boundary and is recorded only"
            ),
            evidence_pointer="bedc_quality_lab.mixing.mix_latents",
        ),
        MultiSurfaceSpec(
            surface_id="undertrain-boundary",
            role="not_runnable",
            countable_hg_a2_2=False,
            sample_count=baseline_sample_count,
            seeds=seeds,
            rho=observed_debt.RHO,
            boundary_reason=(
                "no legal training-budget knob exists in the reused gap-head-on-h producer; this "
                "points to the existing C2 observed-debt exclusion"
            ),
            evidence_pointer="scripts/run_gap_head_observed_debt_transfer.py::_boundary_ledger",
        ),
    )


def _require_finite(name: str, array: np.ndarray, *, ndim: int | None = None) -> np.ndarray:
    value = np.asarray(array, dtype=np.float64)
    if ndim is not None and value.ndim != ndim:
        raise ValueError(f"{name} must be {ndim}-dimensional")
    if value.shape[0] == 0:
        raise ValueError(f"{name} must not be empty")
    if not np.all(np.isfinite(value)):
        raise ValueError(f"{name} contains non-finite values")
    return value


def _linear_identifiability_r2(h: np.ndarray, z: np.ndarray) -> float:
    h_value = _require_finite("h", h, ndim=2)
    z_value = _require_finite("z", z, ndim=2)
    if h_value.shape[0] != z_value.shape[0]:
        raise ValueError("h and z must align")
    design = np.column_stack([h_value, np.ones(h_value.shape[0], dtype=np.float64)])
    coef, *_ = np.linalg.lstsq(design, z_value, rcond=None)
    pred = design @ coef
    ss_res = float(np.sum(np.square(z_value - pred)))
    centered = z_value - np.mean(z_value, axis=0, keepdims=True)
    ss_tot = float(np.sum(np.square(centered)))
    if ss_tot <= 0.0:
        return 0.0
    return float(max(0.0, min(1.0, 1.0 - ss_res / ss_tot)))


def _quality_scalars_for_surface(h: np.ndarray, z: np.ndarray, eval_idx: np.ndarray) -> np.ndarray:
    r2 = _linear_identifiability_r2(h[eval_idx], z[eval_idx])
    margin = float(r2 - 0.5)
    return np.array([r2, margin, r2, r2], dtype=np.float64)


def _surface_for_seed(*, spec: MultiSurfaceSpec, seed: int) -> dict[str, Any]:
    batch = make_toy_batch(
        spec.sample_count,
        rho=spec.rho,
        seed=seed,
        transition_kernel=spec.transition_kernel,
        latent_distribution=spec.latent_distribution,
        mixing=spec.mixing,
    )
    z = _require_finite("z", batch.z, ndim=2)
    z_pair = _require_finite("z_pair", batch.z_pair, ndim=2)
    train_idx, eval_idx = producer.distinction._train_eval_split(z.shape[0], seed=seed)
    state = producer._fit_representation(batch.x[train_idx])
    h = producer._apply_representation(batch.x, state)
    h_pair = producer._apply_representation(batch.x_pair, state)

    high_threshold = producer.distinction._high_energy_threshold(z, train_idx)
    labels = {
        name: producer.distinction._label_truth(name, z, high_energy_threshold=high_threshold)
        for name in producer.DISTINCTIONS
    }
    pair_labels = {
        name: producer.distinction._label_truth(name, z_pair, high_energy_threshold=high_threshold)
        for name in producer.DISTINCTIONS
    }
    probes = {
        name: producer.distinction._fit_probe(h[train_idx], label[train_idx])
        for name, label in labels.items()
    }
    blocks = producer._probe_blocks(probes=probes, h=h, h_pair=h_pair)

    errors = []
    transition_changed = []
    for name in producer.DISTINCTIONS:
        pred = producer.distinction._predict_probe(probes[name], h)
        errors.append((pred["predictions"] != labels[name]).astype(np.float64))
        transition_changed.append((labels[name] != pair_labels[name]).astype(np.float64))
    prediction_error = np.max(np.column_stack(errors), axis=1)
    transition_unstable = np.max(np.column_stack(transition_changed), axis=1)

    min_margin = np.min(blocks["margin"], axis=1)
    margin_threshold = float(np.quantile(min_margin[train_idx], 0.30))
    low_margin = (min_margin <= margin_threshold).astype(np.float64)

    off_target_rows = []
    for target in producer.DISTINCTIONS:
        z_changed = producer.distinction._intervene(target, z, z_pair)
        h_changed = producer._apply_representation(mix_latents(z_changed, spec.mixing), state)
        target_off_target = np.zeros(z.shape[0], dtype=np.float64)
        for name in producer.DISTINCTIONS:
            if name == target:
                continue
            before = producer.distinction._predict_probe(probes[name], h)["predictions"]
            after = producer.distinction._predict_probe(probes[name], h_changed)["predictions"]
            target_off_target = np.maximum(
                target_off_target,
                (before != after).astype(np.float64),
            )
        off_target_rows.append(target_off_target)
    off_target_intervention = np.max(np.column_stack(off_target_rows), axis=1)

    gap_labels = np.column_stack(
        [prediction_error, low_margin, transition_unstable, off_target_intervention]
    ).astype(np.float64)
    features, feature_columns = producer._build_inference_features(
        h=h,
        score=blocks["score"],
        margin=blocks["margin"],
        transition_delta=blocks["transition_delta"],
        quality_scalars=_quality_scalars_for_surface(h, z, eval_idx),
    )
    return {
        "features": features,
        "feature_columns": feature_columns,
        "gap_labels": gap_labels,
        "prediction_error": prediction_error,
        "train_idx": train_idx,
        "eval_idx": eval_idx,
        "high_energy_threshold": float(high_threshold),
        "low_margin_threshold": float(margin_threshold),
    }


def _forbidden_feature_audit(feature_columns: list[str]) -> dict[str, Any]:
    try:
        producer._assert_inference_columns(feature_columns)
        forbidden_present: list[str] = []
        status = "pass"
    except ValueError:
        forbidden = set(producer.FORBIDDEN_INFERENCE_COLUMNS)
        forbidden_present = [
            column
            for column in feature_columns
            if column in forbidden or column.split(":", 1)[0] in forbidden
        ]
        status = "fail"
    return {
        "status": status,
        "feature_columns": list(feature_columns),
        "forbidden_inference_columns": list(producer.FORBIDDEN_INFERENCE_COLUMNS),
        "forbidden_present": sorted(set(forbidden_present)),
    }


def _metric_projection(metrics: dict[str, Any]) -> dict[str, Any]:
    return producer._metric_projection(metrics)


def _seed_summary(*, spec: MultiSurfaceSpec, seed: int, seed_index: int) -> dict[str, Any]:
    surface = _surface_for_seed(spec=spec, seed=int(seed))
    audit = _forbidden_feature_audit(list(surface["feature_columns"]))
    train_idx = surface["train_idx"]
    eval_idx = surface["eval_idx"]
    features = surface["features"]
    labels = surface["gap_labels"]
    prediction_error = surface["prediction_error"]

    heads = producer._fit_gap_head(features[train_idx], labels[train_idx])
    probabilities = producer._predict_gap_head(heads, features[eval_idx])
    randomized_labels = producer._matched_random_gap_labels(labels, seed=int(seed))
    random_heads = producer._fit_gap_head(features[train_idx], randomized_labels[train_idx])
    random_probabilities = producer._predict_gap_head(random_heads, features[eval_idx])

    eval_labels = labels[eval_idx]
    eval_error = prediction_error[eval_idx]
    vanilla_probabilities = np.zeros_like(probabilities, dtype=np.float64)
    vanilla = producer._metrics_for_arm(
        arm="vanilla",
        probabilities=vanilla_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    learned = producer._metrics_for_arm(
        arm="learned_gap_head_on_h",
        probabilities=probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    matched = producer._metrics_for_arm(
        arm=producer.MATCHED_RANDOM_ARM,
        probabilities=random_probabilities,
        labels=eval_labels,
        prediction_error=eval_error,
    )
    return {
        "seed": int(seed),
        "seed_index": int(seed_index),
        "feature_column_count": int(len(surface["feature_columns"])),
        "forbidden_feature_audit": audit,
        "arms": {
            "vanilla": _metric_projection(vanilla),
            "learned_gap_head_on_h": _metric_projection(learned),
            producer.MATCHED_RANDOM_ARM: _metric_projection(matched),
        },
    }


def _stats_from_summaries(summaries: list[dict[str, Any]], getter: Any) -> dict[str, Any]:
    return metric_stats(float(getter(summary)) for summary in summaries)


def _arm_stats(summaries: list[dict[str, Any]], arm: str) -> dict[str, Any]:
    return {
        "failure_detection_auroc": _stats_from_summaries(
            summaries,
            lambda summary: summary["arms"][arm]["failure_detection_auroc"]["value"],
        ),
        "unlogged_error_rate": _stats_from_summaries(
            summaries,
            lambda summary: summary["arms"][arm]["unlogged_error_rate"],
        ),
        "critical_unlogged_error_rate": _stats_from_summaries(
            summaries,
            lambda summary: summary["arms"][arm]["critical_unlogged_error_rate"],
        ),
        "prediction_error_rate": _stats_from_summaries(
            summaries,
            lambda summary: summary["arms"][arm]["prediction_error_rate"],
        ),
    }


def _surface_metrics(summaries: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "vanilla": _arm_stats(summaries, "vanilla"),
        "learned_gap_head_on_h": _arm_stats(summaries, "learned_gap_head_on_h"),
        producer.MATCHED_RANDOM_ARM: _arm_stats(summaries, producer.MATCHED_RANDOM_ARM),
    }


def _surface_forbidden_audit(summaries: list[dict[str, Any]]) -> dict[str, Any]:
    producer_audit = producer._forbidden_column_audit()
    forbidden_present = sorted(
        {
            column
            for summary in summaries
            for column in summary["forbidden_feature_audit"]["forbidden_present"]
        }
    )
    status = (
        "pass"
        if producer_audit["status"] == "pass"
        and all(summary["forbidden_feature_audit"]["status"] == "pass" for summary in summaries)
        else "fail"
    )
    return {
        "status": status,
        "producer_forbidden_column_audit": producer_audit,
        "seed_feature_audit_count": int(len(summaries)),
        "forbidden_inference_columns": list(producer.FORBIDDEN_INFERENCE_COLUMNS),
        "forbidden_present": forbidden_present,
    }


def _surface_hardgates(
    *,
    metrics: Mapping[str, Any],
    forbidden_audit: Mapping[str, Any],
) -> dict[str, Any]:
    learned_auroc = metrics["learned_gap_head_on_h"]["failure_detection_auroc"]
    matched_auroc = metrics[producer.MATCHED_RANDOM_ARM]["failure_detection_auroc"]
    comparison_pass = (
        float(learned_auroc["ci95_low"]) > float(matched_auroc["ci95_high"])
        and float(learned_auroc["mean"]) >= robustness.AUROC_POSITIVE_THRESHOLD
        and float(matched_auroc["ci95_high"]) <= robustness.MATCHED_RANDOM_AUROC_CEILING
    )
    return {
        "HG-A2-1": {
            "status": "pass" if comparison_pass and forbidden_audit["status"] == "pass" else "fail",
            "criterion": (
                "learned AUROC ci95_low > matched-random AUROC ci95_high, learned AUROC "
                f"mean >= {robustness.AUROC_POSITIVE_THRESHOLD}, matched-random AUROC "
                f"ci95_high <= {robustness.MATCHED_RANDOM_AUROC_CEILING}, and forbidden-feature audit pass"
            ),
            "learned_auroc": learned_auroc,
            "matched_random_auroc": matched_auroc,
            "forbidden_feature_audit": dict(forbidden_audit),
        }
    }


def _surface_verdict(hardgates: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    failed = [name for name, gate in hardgates.items() if gate["status"] != "pass"]
    return {
        "status": "pass" if not failed else "failed",
        "passed_gates": [name for name in hardgates if name not in failed],
        "failed_gates": failed,
        "reason": "HG-A2-1 passed" if not failed else "HG-A2-1 failed",
    }


def _surface_result(spec: MultiSurfaceSpec) -> dict[str, Any]:
    summaries = [
        _seed_summary(spec=spec, seed=int(seed), seed_index=index)
        for index, seed in enumerate(spec.seeds)
    ]
    metrics = _surface_metrics(summaries)
    forbidden_audit = _surface_forbidden_audit(summaries)
    hardgates = _surface_hardgates(metrics=metrics, forbidden_audit=forbidden_audit)
    return {
        "surface_id": spec.surface_id,
        "role": spec.role,
        "countable_hg_a2_2": bool(spec.countable_hg_a2_2),
        "sample_count": int(spec.sample_count),
        "seed_count": int(len(spec.seeds)),
        "seeds": [int(seed) for seed in spec.seeds],
        "rho": float(spec.rho),
        "transition_kernel": spec.transition_kernel.to_source_spec()
        if spec.transition_kernel is not None
        else None,
        "latent_distribution": spec.latent_distribution.to_source_spec()
        if spec.latent_distribution is not None
        else LatentDistributionSpec.gaussian().to_source_spec(),
        "mixing": spec.mixing,
        "metrics": metrics,
        "hardgates": hardgates,
        "verdict": _surface_verdict(hardgates),
    }


def _multi_surface_status(pass_count: int) -> str:
    if int(pass_count) >= 2:
        return "pass"
    if int(pass_count) == 1:
        return "single_surface_only"
    return "failed"


def _hardgate_evidence(surfaces: list[dict[str, Any]]) -> dict[str, Any]:
    countable = [surface for surface in surfaces if surface["countable_hg_a2_2"]]
    pass_surface_ids = [
        surface["surface_id"] for surface in countable if surface["verdict"]["status"] == "pass"
    ]
    status = _multi_surface_status(len(pass_surface_ids))
    return {
        "HG-A2-1": {
            "status": "pass"
            if all(surface["hardgates"]["HG-A2-1"]["status"] == "pass" for surface in countable)
            else "fail",
            "criterion": "each countable runnable surface has learned AUROC CI-low above matched-random CI-high with forbidden-feature audit pass",
            "surface_statuses": [
                {
                    "surface_id": surface["surface_id"],
                    "status": surface["hardgates"]["HG-A2-1"]["status"],
                }
                for surface in countable
            ],
        },
        "HG-A2-2": {
            "status": status,
            "criterion": "multi_surface_status is pass iff at least two countable runnable surfaces pass HG-A2-1",
            "pass_surface_ids": pass_surface_ids,
            "pass_surface_count": int(len(pass_surface_ids)),
            "countable_surface_count": int(len(countable)),
        },
        "HG-A2-3": {
            "status": "pass",
            "criterion": "each deferred, boundary_only, or not_runnable registry row appears in boundary_ledger",
            "ledger_pointer": "$.boundary_ledger",
        },
    }


def _boundary_ledger(registry: tuple[MultiSurfaceSpec, ...]) -> list[dict[str, Any]]:
    rows = []
    for spec in registry:
        if spec.countable_hg_a2_2:
            continue
        rows.append(
            {
                "surface_id": spec.surface_id,
                "kind": spec.role,
                "reason": spec.boundary_reason or "outside countable HG-A2-2 pool",
                "evidence_pointer": spec.evidence_pointer,
            }
        )
    return rows


def _forbidden_claim_term_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    text = json.dumps(
        {
            "gap_head_multisurface_debt_transfer": payload.get(
                "gap_head_multisurface_debt_transfer"
            ),
            "mechanism_status": payload.get("mechanism_status"),
            "d5m_status": payload.get("d5m_status"),
            "not_claimed": payload.get("not_claimed"),
        },
        sort_keys=True,
    ).lower()
    hits = [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in text]
    return {
        "status": "fail" if hits else "pass",
        "forbidden_positive_claim_terms_pointer": (
            "bedc_quality_lab.claim_terms.FORBIDDEN_POSITIVE_CLAIM_TERMS"
        ),
        "hits": hits,
        "reason": "forbidden positive claim term present" if hits else "no forbidden positive claim terms in claim fields",
    }


def build_payload(*, generated_at: str | None = None) -> dict[str, Any]:
    registry = _surface_registry()
    runnable_specs = [spec for spec in registry if spec.countable_hg_a2_2]
    surfaces = [_surface_result(spec) for spec in runnable_specs]
    hardgates = _hardgate_evidence(surfaces)
    pass_count = int(hardgates["HG-A2-2"]["pass_surface_count"])
    multi_surface_status = _multi_surface_status(pass_count)
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": generated_at or datetime.now(timezone.utc).isoformat(),
        "status": "pointer-only",
        "mechanism_status": "not_claimed",
        "d5m_status": "not_claimed",
        "source_artifacts": {
            "generation_script": "scripts/run_gap_head_multisurface_debt_transfer.py",
            "single_surface_transfer_reference": "scripts/run_gap_head_observed_debt_transfer.py",
            "gap_head_surface_owner": "scripts/run_gap_ledger_head_on_h.py",
            "gap_head_training": "scripts/run_gap_ledger_head_on_h.py::_fit_gap_head",
            "matched_random_control": "scripts/run_gap_ledger_head_on_h.py::_matched_random_gap_labels",
            "metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm",
            "toy_world": "bedc_quality_lab.toy_world.make_toy_batch",
            "transition_kernel": "bedc_quality_lab.transition.TransitionKernelSpec",
            "latent_distribution": "bedc_quality_lab.latent_distribution.LatentDistributionSpec",
            "mixing": "bedc_quality_lab.mixing.mix_latents",
            "stats_helper": "scripts.experiment_stats.metric_stats",
            "claim_terms": "bedc_quality_lab.claim_terms.FORBIDDEN_POSITIVE_CLAIM_TERMS",
        },
        "config": {
            "transfer_status_pointer": TRANSFER_STATUS_POINTER,
            "countable_surface_threshold": 2,
            "countable_surface_count": COUNTABLE_SURFACE_COUNT,
            "registry_surface_count": len(registry),
            "auroc_positive_threshold": robustness.AUROC_POSITIVE_THRESHOLD,
            "matched_random_auroc_ceiling": robustness.MATCHED_RANDOM_AUROC_CEILING,
            "control_arm": producer.MATCHED_RANDOM_ARM,
            "same_split_threshold_budget_metric_helper": True,
        },
        "surface_registry": [spec.registry_row() for spec in registry],
        "gap_head_multisurface_debt_transfer": {
            "multi_surface_status": multi_surface_status,
            "pass_surface_count": pass_count,
            "countable_surface_count": COUNTABLE_SURFACE_COUNT,
            "registry_surface_count": len(registry),
            "discovery_map_pointer": TRANSFER_STATUS_POINTER,
            "mechanism_status": "not_claimed",
            "d5m_status": "not_claimed",
        },
        "surfaces": surfaces,
        "hardgate_evidence": hardgates,
        "boundary_ledger": _boundary_ledger(registry),
        "not_claimed": list(NOT_CLAIMED),
    }
    payload["forbidden_claim_term_audit"] = _forbidden_claim_term_audit(payload)
    payload["hardgate_evidence"]["HG-A2-3"]["status"] = (
        "pass"
        if sorted(row["surface_id"] for row in payload["boundary_ledger"])
        == sorted(spec.surface_id for spec in registry if not spec.countable_hg_a2_2)
        else "fail"
    )
    return payload


def render_markdown(payload: Mapping[str, Any]) -> str:
    transfer = payload["gap_head_multisurface_debt_transfer"]
    lines = [
        "# Gap-Head Multi-Surface Debt Transfer",
        "",
        f"- JSON artifact pointer: `{payload['artifact']}`",
        f"- Report artifact pointer: `{payload['report']}`",
        f"- Artifact id pointer: `$.artifact_id`",
        f"- Transfer status pointer: `{TRANSFER_STATUS_POINTER}`",
        f"- Surface registry pointer: `$.surface_registry`",
        f"- Surface verdict pointer: `$.surfaces[*].verdict`",
        f"- Hardgate evidence pointer: `$.hardgate_evidence`",
        f"- Boundary ledger pointer: `$.boundary_ledger`",
        f"- Mechanism status: `{payload['mechanism_status']}`",
        f"- D5-M status: `{payload['d5m_status']}`",
        "",
        "## Status",
        "",
        "| field | value | pointer |",
        "| --- | --- | --- |",
        f"| multi-surface status | `{transfer['multi_surface_status']}` | `{TRANSFER_STATUS_POINTER}` |",
        f"| pass surface count | `{transfer['pass_surface_count']}` | `$.gap_head_multisurface_debt_transfer.pass_surface_count` |",
        f"| countable surface count | `{transfer['countable_surface_count']}` | `$.gap_head_multisurface_debt_transfer.countable_surface_count` |",
        "",
        "## Countable Surfaces",
        "",
        "| surface | verdict | learned AUROC mean | matched-random AUROC mean | pointer |",
        "| --- | --- | ---: | ---: | --- |",
    ]
    for surface in payload["surfaces"]:
        learned = surface["metrics"]["learned_gap_head_on_h"]["failure_detection_auroc"]
        matched = surface["metrics"][producer.MATCHED_RANDOM_ARM]["failure_detection_auroc"]
        lines.append(
            "| "
            f"`{surface['surface_id']}` | "
            f"`{surface['verdict']['status']}` | "
            f"{_format_float(float(learned['mean']))} | "
            f"{_format_float(float(matched['mean']))} | "
            "`$.surfaces[*]` |"
        )
    lines.extend(["", "## Boundary Ledger", "", "| surface | kind | pointer |", "| --- | --- | --- |"])
    for row in payload["boundary_ledger"]:
        lines.append(
            f"| `{row['surface_id']}` | `{row['kind']}` | `{row['evidence_pointer']}` |"
        )
    lines.extend(["", "## Not Claimed", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def _write_payload(payload: Mapping[str, Any], *, root: Path = ROOT) -> None:
    json_path = root / JSON_ARTIFACT
    report_path = root / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="Run gap-head multi-surface debt transfer.")
    parser.add_argument("--root", type=Path, default=ROOT, help="quality-lab root for artifact output")
    args = parser.parse_args(argv)
    payload = build_payload()
    _write_payload(payload, root=args.root)
    transfer = payload["gap_head_multisurface_debt_transfer"]
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"multi_surface_status {transfer['multi_surface_status']}")
    print(f"pass_surface_count {transfer['pass_surface_count']}")
    print(f"boundary_ledger_count {len(payload['boundary_ledger'])}")


if __name__ == "__main__":
    main()

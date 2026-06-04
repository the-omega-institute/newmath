#!/usr/bin/env python3
"""Run the gap-head transfer atlas over observed-debt source surfaces."""

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
from scripts import run_gap_ledger_head_on_h as producer
from scripts import run_observed_debt_sweep as observed_debt
from scripts.experiment_stats import metric_stats


JSON_ARTIFACT = "reports/canonical/gap_head_transfer_atlas.json"
REPORT_ARTIFACT = "reports/canonical/gap_head_transfer_atlas.md"
ARTIFACT_ID = "bedc-quality-lab:gap-head-transfer-atlas"
CLAIM_CAPSULE_SCHEMA_ID = "bedc.quality.claim_capsule"
TRANSFER_STATUS_POINTER = "$.multi_surface_d5_o.decision"
CLAIM_CAPSULE_ARTIFACT = "reports/runs/{run_id}/claim_capsule.json"
RUN_SUMMARY_ARTIFACT = "reports/runs/{run_id}/summary.json"
RUN_ID_PREFIX = "gap-head-transfer-atlas"
COUNTABLE_PASS_THRESHOLD = 3
PRIOR_OBSERVATION_PACKET_POINTER = "$.prior_observation_packet"
ARMS = ("vanilla", "learned_gap_head_on_h", producer.MATCHED_RANDOM_ARM)
OBSERVED_DEBT_SURFACE_KIND = "observed_debt"
NOT_CLAIMED = (
    "lab-local multi-surface transfer evidence",
    "not global model quality",
    "not full LeJEPA",
    "not full TensorNameCert",
    "not LLM behavior",
    "not mechanism closure",
    "revocable under rerun or boundary expansion",
)


@dataclass(frozen=True)
class AtlasSurfaceSpec:
    surface_id: str
    label: str
    surface_kind: str
    sample_count: int
    seeds: tuple[int, ...]
    rho: float
    transition_kernel: TransitionKernelSpec | None = None
    latent_distribution: LatentDistributionSpec | None = None
    mixing: str = DEFAULT_MIXING
    prior_observation: str | None = None
    source_evidence_note: str | None = None

    def registry_row(self) -> dict[str, Any]:
        return {
            "surface_id": self.surface_id,
            "label": self.label,
            "surface_kind": self.surface_kind,
            "countable_for_multi_surface_d5_o": self.countable_for_multi_surface_d5_o,
            "sample_count": int(self.sample_count),
            "seed_count": int(len(self.seeds)),
            "rho": float(self.rho),
            "transition_kernel": self.transition_kernel.to_source_spec()
            if self.transition_kernel is not None
            else TransitionKernelSpec.isotropic(self.rho, latent_dim=2).to_source_spec(),
            "latent_distribution": self.latent_distribution.to_source_spec()
            if self.latent_distribution is not None
            else LatentDistributionSpec.gaussian().to_source_spec(),
            "mixing": self.mixing,
            "prior_observation": self.prior_observation,
            "source_evidence": self.source_evidence(),
        }

    @property
    def countable_for_multi_surface_d5_o(self) -> bool:
        return self.surface_kind == OBSERVED_DEBT_SURFACE_KIND

    def source_evidence(self) -> dict[str, Any] | None:
        if self.prior_observation is None and self.source_evidence_note is None:
            return None
        return {
            "status": "prior_observation",
            "counts_as_a2_hg_pass_evidence": False,
            "packet_pointer": PRIOR_OBSERVATION_PACKET_POINTER,
            "observation_pointer": f"{PRIOR_OBSERVATION_PACKET_POINTER}.observations.{self.label}",
            "known_fact": self.prior_observation,
            "note": self.source_evidence_note,
        }


def _default_seeds() -> tuple[int, ...]:
    return tuple(
        int(seed)
        for seed in observed_debt._seeds(
            "C3",
            observed_debt.DEFAULT_SEED_COUNT_BY_AXIS["C3"],
        )
    )


def surface_registry() -> tuple[AtlasSurfaceSpec, ...]:
    seeds = _default_seeds()
    baseline = int(observed_debt.BASELINE_SAMPLE_COUNT)
    rho = float(observed_debt.RHO)
    return (
        AtlasSurfaceSpec(
            surface_id="S0",
            label="clean_gaussian_ou",
            surface_kind="clean",
            sample_count=baseline,
            seeds=seeds,
            rho=rho,
            prior_observation="clean pass; clean is not countable for multi-surface D5-O",
        ),
        AtlasSurfaceSpec(
            surface_id="S1",
            label="sample_count_1024",
            surface_kind=OBSERVED_DEBT_SURFACE_KIND,
            sample_count=1024,
            seeds=seeds,
            rho=rho,
            prior_observation="sample-count pass under the prior observation packet",
        ),
        AtlasSurfaceSpec(
            surface_id="S2",
            label="sample_count_256",
            surface_kind=OBSERVED_DEBT_SURFACE_KIND,
            sample_count=256,
            seeds=seeds,
            rho=rho,
        ),
        AtlasSurfaceSpec(
            surface_id="S3",
            label="anisotropic_rho_0p95_0p30",
            surface_kind=OBSERVED_DEBT_SURFACE_KIND,
            sample_count=baseline,
            seeds=seeds,
            rho=rho,
            transition_kernel=TransitionKernelSpec(rho_by_axis=(0.95, 0.30)),
            prior_observation="anisotropic pass under the prior observation packet",
        ),
        AtlasSurfaceSpec(
            surface_id="S4",
            label="anisotropic_rho_0p90_0p60",
            surface_kind=OBSERVED_DEBT_SURFACE_KIND,
            sample_count=baseline,
            seeds=seeds,
            rho=rho,
            transition_kernel=TransitionKernelSpec(rho_by_axis=(0.90, 0.60)),
        ),
        AtlasSurfaceSpec(
            surface_id="S5",
            label="laplace_latent",
            surface_kind=OBSERVED_DEBT_SURFACE_KIND,
            sample_count=baseline,
            seeds=seeds,
            rho=rho,
            latent_distribution=LatentDistributionSpec.laplace(),
            prior_observation="Laplace fail under the prior observation packet",
            source_evidence_note="Laplace remains retained as boundary evidence when the current A2 run fails.",
        ),
        AtlasSurfaceSpec(
            surface_id="S6",
            label="student_t_df3_latent",
            surface_kind=OBSERVED_DEBT_SURFACE_KIND,
            sample_count=baseline,
            seeds=seeds,
            rho=rho,
            latent_distribution=LatentDistributionSpec.student_t(df=3),
        ),
        AtlasSurfaceSpec(
            surface_id="S7",
            label="uniform_latent",
            surface_kind=OBSERVED_DEBT_SURFACE_KIND,
            sample_count=baseline,
            seeds=seeds,
            rho=rho,
            latent_distribution=LatentDistributionSpec.uniform(),
        ),
        AtlasSurfaceSpec(
            surface_id="S8",
            label="generalized_normal_alpha_0p5",
            surface_kind=OBSERVED_DEBT_SURFACE_KIND,
            sample_count=baseline,
            seeds=seeds,
            rho=rho,
            latent_distribution=LatentDistributionSpec.generalized_normal(alpha=0.5),
        ),
        AtlasSurfaceSpec(
            surface_id="S9",
            label="generalized_normal_alpha_4",
            surface_kind=OBSERVED_DEBT_SURFACE_KIND,
            sample_count=baseline,
            seeds=seeds,
            rho=rho,
            latent_distribution=LatentDistributionSpec.generalized_normal(alpha=4),
        ),
        AtlasSurfaceSpec(
            surface_id="S10",
            label="mixing_shift_spiral",
            surface_kind=OBSERVED_DEBT_SURFACE_KIND,
            sample_count=baseline,
            seeds=seeds,
            rho=rho,
            mixing="spiral",
        ),
        AtlasSurfaceSpec(
            surface_id="S11",
            label="mixing_shift_realnvp",
            surface_kind=OBSERVED_DEBT_SURFACE_KIND,
            sample_count=baseline,
            seeds=seeds,
            rho=rho,
            mixing="realnvp_coupling",
        ),
        AtlasSurfaceSpec(
            surface_id="S12",
            label="optimizer_undertraining",
            surface_kind=OBSERVED_DEBT_SURFACE_KIND,
            sample_count=baseline,
            seeds=seeds,
            rho=rho,
            source_evidence_note="The legal producer has no optimizer-budget arm; the surface is evaluated with the stable shared head helper.",
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


def _surface_for_seed(*, spec: AtlasSurfaceSpec, seed: int) -> dict[str, Any]:
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


def _seed_summary(*, spec: AtlasSurfaceSpec, seed: int, seed_index: int) -> dict[str, Any]:
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
            "vanilla": producer._metric_projection(vanilla),
            "learned_gap_head_on_h": producer._metric_projection(learned),
            producer.MATCHED_RANDOM_ARM: producer._metric_projection(matched),
        },
    }


def _stats_from_summaries(summaries: list[dict[str, Any]], getter: Any) -> dict[str, Any]:
    return metric_stats(float(getter(summary)) for summary in summaries)


def _arm_stats(summaries: list[dict[str, Any]], arm: str) -> dict[str, Any]:
    return {
        "AUROC": _stats_from_summaries(
            summaries,
            lambda summary: summary["arms"][arm]["failure_detection_auroc"]["value"],
        ),
        "UnloggedErrorRate": _stats_from_summaries(
            summaries,
            lambda summary: summary["arms"][arm]["unlogged_error_rate"],
        ),
        "CriticalUnloggedErrorRate": _stats_from_summaries(
            summaries,
            lambda summary: summary["arms"][arm]["critical_unlogged_error_rate"],
        ),
        "PredictionErrorRate": _stats_from_summaries(
            summaries,
            lambda summary: summary["arms"][arm]["prediction_error_rate"],
        ),
    }


def _surface_metrics(summaries: list[dict[str, Any]]) -> dict[str, Any]:
    return {arm: _arm_stats(summaries, arm) for arm in ARMS}


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


def _reduction_stats(summaries: list[dict[str, Any]], arm: str) -> dict[str, Any]:
    return metric_stats(
        (
            float(summary["arms"]["vanilla"]["unlogged_error_rate"])
            - float(summary["arms"][arm]["unlogged_error_rate"])
        )
        for summary in summaries
    )


def _surface_hardgates(
    *,
    metrics: Mapping[str, Any],
    uer_reductions: Mapping[str, Any],
    forbidden_audit: Mapping[str, Any],
) -> dict[str, Any]:
    learned_auroc = metrics["learned_gap_head_on_h"]["AUROC"]
    matched_auroc = metrics[producer.MATCHED_RANDOM_ARM]["AUROC"]
    learned_reduction = uer_reductions["learned_gap_head_on_h"]
    matched_reduction = uer_reductions[producer.MATCHED_RANDOM_ARM]
    matched_positive = (
        float(matched_auroc["ci95_low"]) > float(learned_auroc["ci95_high"])
        or float(matched_reduction["ci95_low"]) > float(learned_reduction["ci95_high"])
    )
    return {
        "A2-HG1": {
            "status": "pass"
            if float(learned_auroc["ci95_low"]) > float(matched_auroc["ci95_high"])
            else "fail",
            "learned_auroc": learned_auroc,
            "matched_random_auroc": matched_auroc,
        },
        "A2-HG2": {
            "status": "pass"
            if float(learned_reduction["ci95_low"]) > float(matched_reduction["ci95_high"])
            else "fail",
            "learned_uer_reduction": learned_reduction,
            "matched_random_uer_reduction": matched_reduction,
        },
        "A2-HG3": {
            "status": "pass" if not matched_positive else "fail",
            "matched_random_positive": bool(matched_positive),
        },
        "A2-HG4": {
            "status": "pass" if forbidden_audit["status"] == "pass" else "fail",
            "forbidden_column_audit": dict(forbidden_audit),
        },
    }


def _surface_verdict(spec: AtlasSurfaceSpec, hardgates: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    failed = [name for name, gate in hardgates.items() if gate["status"] != "pass"]
    current_pass = not failed
    counts_for_decision = current_pass and spec.countable_for_multi_surface_d5_o
    return {
        "status": "pass" if current_pass else "failed",
        "counts_for_multi_surface_d5_o": bool(counts_for_decision),
        "passed_gates": [name for name in hardgates if name not in failed],
        "failed_gates": failed,
        "reason": "A2 surface gates passed" if current_pass else "A2 surface gates failed",
    }


def _surface_delta_count(metrics: Mapping[str, Any]) -> int:
    learned = metrics["learned_gap_head_on_h"]
    matched = metrics[producer.MATCHED_RANDOM_ARM]
    return int(
        float(learned["AUROC"]["mean"]) > float(matched["AUROC"]["mean"])
    ) + int(
        float(learned["UnloggedErrorRate"]["mean"]) < float(matched["UnloggedErrorRate"]["mean"])
    )


def _net_information(metrics: Mapping[str, Any], reductions: Mapping[str, Any]) -> float:
    auroc_delta = (
        float(metrics["learned_gap_head_on_h"]["AUROC"]["mean"])
        - float(metrics[producer.MATCHED_RANDOM_ARM]["AUROC"]["mean"])
    )
    reduction_delta = (
        float(reductions["learned_gap_head_on_h"]["mean"])
        - float(reductions[producer.MATCHED_RANDOM_ARM]["mean"])
    )
    return float(auroc_delta + reduction_delta)


def _discovery_level(spec: AtlasSurfaceSpec, verdict: Mapping[str, Any]) -> str:
    if spec.label == "clean_gaussian_ou":
        return "D4-clean-control" if verdict["status"] == "pass" else "DN"
    if verdict["counts_for_multi_surface_d5_o"]:
        return "D5-O-surface"
    return "DN"


def _surface_result(spec: AtlasSurfaceSpec) -> dict[str, Any]:
    summaries = [
        _seed_summary(spec=spec, seed=int(seed), seed_index=index)
        for index, seed in enumerate(spec.seeds)
    ]
    metrics = _surface_metrics(summaries)
    reductions = {
        "learned_gap_head_on_h": _reduction_stats(summaries, "learned_gap_head_on_h"),
        producer.MATCHED_RANDOM_ARM: _reduction_stats(summaries, producer.MATCHED_RANDOM_ARM),
    }
    forbidden_audit = _surface_forbidden_audit(summaries)
    hardgates = _surface_hardgates(
        metrics=metrics,
        uer_reductions=reductions,
        forbidden_audit=forbidden_audit,
    )
    verdict = _surface_verdict(spec, hardgates)
    return {
        "surface_id": spec.surface_id,
        "label": spec.label,
        "surface_kind": spec.surface_kind,
        "countable_for_multi_surface_d5_o": spec.countable_for_multi_surface_d5_o,
        "sample_count": int(spec.sample_count),
        "seed_count": int(len(spec.seeds)),
        "seeds": [int(seed) for seed in spec.seeds],
        "rho": float(spec.rho),
        "arms": list(ARMS),
        "transition_kernel": spec.transition_kernel.to_source_spec()
        if spec.transition_kernel is not None
        else TransitionKernelSpec.isotropic(spec.rho, latent_dim=2).to_source_spec(),
        "latent_distribution": spec.latent_distribution.to_source_spec()
        if spec.latent_distribution is not None
        else LatentDistributionSpec.gaussian().to_source_spec(),
        "mixing": spec.mixing,
        "metrics": metrics,
        "uer_reduction_vs_vanilla": reductions,
        "MatchedRandomPositive": hardgates["A2-HG3"]["matched_random_positive"],
        "ForbiddenColumnAudit": forbidden_audit,
        "SurfaceDeltaCount": _surface_delta_count(metrics),
        "NetInformation": _net_information(metrics, reductions),
        "DiscoveryLevel": _discovery_level(spec, verdict),
        "hardgates": hardgates,
        "verdict": verdict,
        "source_evidence": spec.source_evidence(),
    }


def _pass_surface_ids(surfaces: list[dict[str, Any]]) -> list[str]:
    return [
        str(surface["label"])
        for surface in surfaces
        if surface["verdict"]["counts_for_multi_surface_d5_o"] is True
    ]


def _boundary_ledger(surfaces: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for surface_index, surface in enumerate(surfaces):
        if surface["verdict"]["status"] == "pass":
            continue
        failed_gates = list(surface["verdict"]["failed_gates"])
        evidence_pointer = {
            gate: f"$.surfaces.{surface_index}.hardgates.{gate}"
            for gate in failed_gates
        }
        rows.append(
            {
                "surface_id": surface["surface_id"],
                "label": surface["label"],
                "kind": "failed_surface",
                "failed_gates": failed_gates,
                "current_a2_metrics": {
                    "learned_auroc": surface["metrics"]["learned_gap_head_on_h"]["AUROC"],
                    "matched_random_auroc": surface["metrics"][producer.MATCHED_RANDOM_ARM]["AUROC"],
                    "learned_uer_reduction": surface["uer_reduction_vs_vanilla"]["learned_gap_head_on_h"],
                    "matched_random_uer_reduction": surface["uer_reduction_vs_vanilla"][producer.MATCHED_RANDOM_ARM],
                },
                "source_evidence": surface.get("source_evidence"),
                "evidence_pointer": evidence_pointer,
            }
        )
    return rows


def _hardgate_evidence(surfaces: list[dict[str, Any]], boundary_ledger: list[dict[str, Any]]) -> dict[str, Any]:
    pass_surface_ids = _pass_surface_ids(surfaces)
    pass_surfaces = [
        surface
        for surface in surfaces
        if surface["verdict"]["counts_for_multi_surface_d5_o"] is True
    ]
    failed_surface_ids = {
        str(surface["surface_id"])
        for surface in surfaces
        if surface["verdict"]["status"] != "pass"
    }
    boundary_surface_ids = {str(row["surface_id"]) for row in boundary_ledger}
    laplace_rows = [row for row in boundary_ledger if row["label"] == "laplace_latent"]
    return {
        "A2-HG1": {
            "status": "pass"
            if pass_surfaces
            and all(surface["hardgates"]["A2-HG1"]["status"] == "pass" for surface in pass_surfaces)
            else "fail",
            "aggregation": "counted pass surfaces; failed surfaces are carried by boundary_ledger",
            "surface_statuses": [
                {"label": surface["label"], "status": surface["hardgates"]["A2-HG1"]["status"]}
                for surface in surfaces
            ],
        },
        "A2-HG2": {
            "status": "pass"
            if pass_surfaces
            and all(surface["hardgates"]["A2-HG2"]["status"] == "pass" for surface in pass_surfaces)
            else "fail",
            "aggregation": "counted pass surfaces; failed surfaces are carried by boundary_ledger",
            "surface_statuses": [
                {"label": surface["label"], "status": surface["hardgates"]["A2-HG2"]["status"]}
                for surface in surfaces
            ],
        },
        "A2-HG3": {
            "status": "pass"
            if pass_surfaces
            and all(surface["hardgates"]["A2-HG3"]["status"] == "pass" for surface in pass_surfaces)
            else "fail",
            "aggregation": "counted pass surfaces; failed surfaces are carried by boundary_ledger",
            "matched_random_positive": {
                surface["label"]: bool(surface["MatchedRandomPositive"])
                for surface in surfaces
            },
        },
        "A2-HG4": {
            "status": "pass"
            if pass_surfaces
            and all(surface["hardgates"]["A2-HG4"]["status"] == "pass" for surface in pass_surfaces)
            else "fail",
            "aggregation": "counted pass surfaces; failed surfaces are carried by boundary_ledger",
            "forbidden_column_audit": {
                surface["label"]: surface["ForbiddenColumnAudit"]["status"]
                for surface in surfaces
            },
        },
        "A2-HG5": {
            "status": "pass" if len(pass_surface_ids) >= COUNTABLE_PASS_THRESHOLD else "fail",
            "pass_surface_ids": pass_surface_ids,
            "pass_surface_count": int(len(pass_surface_ids)),
            "threshold": COUNTABLE_PASS_THRESHOLD,
            "clean_counted": False,
        },
        "A2-HG6": {
            "status": "pass" if failed_surface_ids <= boundary_surface_ids else "fail",
            "failed_surface_ids": sorted(failed_surface_ids),
            "boundary_surface_ids": sorted(boundary_surface_ids),
        },
        "A2-HG7": {
            "status": "pass" if laplace_rows or "S5" not in failed_surface_ids else "fail",
            "laplace_failed": "S5" in failed_surface_ids,
            "laplace_boundary_rows": laplace_rows,
        },
    }


def _multi_surface_decision(hardgates: Mapping[str, Any]) -> dict[str, Any]:
    pass_count = int(hardgates["A2-HG5"]["pass_surface_count"])
    gate_statuses = {
        name: str(gate.get("status"))
        for name, gate in hardgates.items()
        if name.startswith("A2-HG")
    }
    failed_gates = sorted(name for name, status in gate_statuses.items() if status != "pass")
    decision = "pass" if not failed_gates else "failed"
    return {
        "decision": decision,
        "discovery_level": "D5-O" if decision == "pass" else "DN",
        "pass_surface_count": pass_count,
        "threshold": COUNTABLE_PASS_THRESHOLD,
        "pass_surface_ids": list(hardgates["A2-HG5"]["pass_surface_ids"]),
        "gate_statuses": gate_statuses,
        "failed_gates": failed_gates,
        "clean_surface_counted": False,
        "not_claimed": list(NOT_CLAIMED),
    }


def _forbidden_claim_term_audit(payload: Mapping[str, Any]) -> dict[str, Any]:
    text = json.dumps(
        {
            "multi_surface_d5_o": payload.get("multi_surface_d5_o"),
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
    }


def _prior_observation_packet(registry: tuple[AtlasSurfaceSpec, ...]) -> dict[str, Any]:
    observations = {
        spec.label: {
            "surface_id": spec.surface_id,
            "label": spec.label,
            "known_fact": spec.prior_observation,
            "counts_as_a2_hg_pass_evidence": False,
            "note": spec.source_evidence_note,
        }
        for spec in registry
        if spec.prior_observation is not None or spec.source_evidence_note is not None
    }
    return {
        "status": "prior_observation",
        "counts_as_a2_hg_pass_evidence": False,
        "packet_pointer": PRIOR_OBSERVATION_PACKET_POINTER,
        "observation_count": int(len(observations)),
        "observations": observations,
    }


def _externalize_local_pointers(value: Any, *, artifact: str = JSON_ARTIFACT) -> Any:
    if isinstance(value, str) and value.startswith("$."):
        return f"{artifact}:{value}"
    if isinstance(value, dict):
        return {
            key: _externalize_local_pointers(cell, artifact=artifact)
            for key, cell in value.items()
        }
    if isinstance(value, list):
        return [_externalize_local_pointers(cell, artifact=artifact) for cell in value]
    return value


def build_payload(*, run_id: str, generated_at: str | None = None) -> dict[str, Any]:
    registry = surface_registry()
    surfaces = [_surface_result(spec) for spec in registry]
    boundary = _boundary_ledger(surfaces)
    hardgates = _hardgate_evidence(surfaces, boundary)
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "run_id": run_id,
        "generated_at": generated_at or datetime.now(timezone.utc).isoformat(),
        "producer": "scripts/run_gap_head_transfer_atlas.py",
        "status": "canonical",
        "source_artifacts": {
            "generation_script": "scripts/run_gap_head_transfer_atlas.py",
            "gap_head_surface_owner": "scripts/run_gap_ledger_head_on_h.py",
            "gap_head_training": "scripts/run_gap_ledger_head_on_h.py::_fit_gap_head",
            "matched_random_control": "scripts/run_gap_ledger_head_on_h.py::_matched_random_gap_labels",
            "metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm",
            "toy_world": "bedc_quality_lab.toy_world.make_toy_batch",
            "transition_kernel": "bedc_quality_lab.transition.TransitionKernelSpec",
            "latent_distribution": "bedc_quality_lab.latent_distribution.LatentDistributionSpec",
            "mixing": "bedc_quality_lab.mixing.mix_latents",
            "stats_helper": "scripts.experiment_stats.metric_stats",
        },
        "config": {
            "surface_count": len(registry),
            "arms": list(ARMS),
            "countable_pass_threshold": COUNTABLE_PASS_THRESHOLD,
            "control_arm": producer.MATCHED_RANDOM_ARM,
            "same_split_threshold_budget_metric_helper": True,
            "claim_capsule_artifact": CLAIM_CAPSULE_ARTIFACT.format(run_id=run_id),
            "summary_artifact": RUN_SUMMARY_ARTIFACT.format(run_id=run_id),
        },
        "surface_registry": [spec.registry_row() for spec in registry],
        "prior_observation_packet": _prior_observation_packet(registry),
        "surfaces": surfaces,
        "boundary_ledger": boundary,
        "hardgate_evidence": hardgates,
        "multi_surface_d5_o": _multi_surface_decision(hardgates),
        "not_claimed": list(NOT_CLAIMED),
    }
    payload["forbidden_claim_term_audit"] = _forbidden_claim_term_audit(payload)
    return payload


def build_summary(payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "artifact_id": "bedc-quality-lab:gap-head-transfer-atlas-run-summary",
        "run_id": payload["run_id"],
        "generated_at": payload["generated_at"],
        "producer": payload["producer"],
        "canonical_artifact": JSON_ARTIFACT,
        "canonical_report": REPORT_ARTIFACT,
        "surface_count": int(payload["config"]["surface_count"]),
        "arms": list(ARMS),
        "multi_surface_d5_o": dict(payload["multi_surface_d5_o"]),
        "hardgate_evidence": _externalize_local_pointers(payload["hardgate_evidence"]),
        "boundary_ledger": _externalize_local_pointers(payload["boundary_ledger"]),
        "not_claimed": list(payload["not_claimed"]),
    }


def build_claim_capsule(payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": CLAIM_CAPSULE_SCHEMA_ID,
        "artifact_id": "bedc-quality-lab:gap-head-transfer-atlas-claim-capsule",
        "run_id": payload["run_id"],
        "generated_at": payload["generated_at"],
        "producer": payload["producer"],
        "canonical_artifact": JSON_ARTIFACT,
        "canonical_report": REPORT_ARTIFACT,
        "claim": {
            "name": "multi_surface_d5_o",
            "decision": payload["multi_surface_d5_o"]["decision"],
            "discovery_level": payload["multi_surface_d5_o"]["discovery_level"],
            "evidence_pointer": f"{JSON_ARTIFACT}:{TRANSFER_STATUS_POINTER}",
            "revocable": True,
        },
        "source_evidence": _externalize_local_pointers(payload["prior_observation_packet"]),
        "prior_observations": [
            _externalize_local_pointers(row)
            for row in payload["surface_registry"]
            if isinstance(row.get("source_evidence"), dict)
        ],
        "boundary_ledger": _externalize_local_pointers(payload["boundary_ledger"]),
        "not_claimed": list(payload["not_claimed"]),
    }


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def render_markdown(payload: Mapping[str, Any]) -> str:
    decision = payload["multi_surface_d5_o"]
    lines = [
        "# Gap-Head Transfer Atlas",
        "",
        f"- JSON artifact pointer: `{payload['artifact']}`",
        f"- Report artifact pointer: `{payload['report']}`",
        f"- Run id: `{payload['run_id']}`",
        f"- Surface registry pointer: `$.surface_registry`",
        f"- Surface verdict nodes: `$.surfaces.<index>.verdict`",
        f"- Hardgate evidence pointer: `$.hardgate_evidence`",
        f"- Boundary ledger pointer: `$.boundary_ledger`",
        f"- Claim capsule pointer: `{CLAIM_CAPSULE_ARTIFACT.format(run_id=payload['run_id'])}`",
        "",
        "## Decision",
        "",
        "| field | value | pointer |",
        "| --- | --- | --- |",
        f"| decision | `{decision['decision']}` | `{TRANSFER_STATUS_POINTER}` |",
        f"| discovery level | `{decision['discovery_level']}` | `$.multi_surface_d5_o.discovery_level` |",
        f"| pass surface count | `{decision['pass_surface_count']}` | `$.multi_surface_d5_o.pass_surface_count` |",
        f"| threshold | `{decision['threshold']}` | `$.multi_surface_d5_o.threshold` |",
        "",
        "## Surfaces",
        "",
        "| surface | kind | verdict | learned AUROC | matched AUROC | learned UER reduction | matched UER reduction |",
        "| --- | --- | --- | ---: | ---: | ---: | ---: |",
    ]
    for surface in payload["surfaces"]:
        learned = surface["metrics"]["learned_gap_head_on_h"]["AUROC"]
        matched = surface["metrics"][producer.MATCHED_RANDOM_ARM]["AUROC"]
        learned_reduction = surface["uer_reduction_vs_vanilla"]["learned_gap_head_on_h"]
        matched_reduction = surface["uer_reduction_vs_vanilla"][producer.MATCHED_RANDOM_ARM]
        lines.append(
            "| "
            f"`{surface['label']}` | "
            f"`{surface['surface_kind']}` | "
            f"`{surface['verdict']['status']}` | "
            f"{_format_float(float(learned['mean']))} | "
            f"{_format_float(float(matched['mean']))} | "
            f"{_format_float(float(learned_reduction['mean']))} | "
            f"{_format_float(float(matched_reduction['mean']))} |"
        )
    lines.extend(["", "## Boundary Ledger", "", "| surface | failed gates | pointers |", "| --- | --- | --- |"])
    for row in payload["boundary_ledger"]:
        pointer_text = ", ".join(
            f"{gate}: {row['evidence_pointer'][gate]}"
            for gate in row["failed_gates"]
        )
        lines.append(
            f"| `{row['label']}` | `{', '.join(row['failed_gates'])}` | `{pointer_text}` |"
        )
    lines.extend(["", "## Not Claimed", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def _write_json_atomic(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_text_atomic(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def write_outputs(payload: Mapping[str, Any], *, root: Path = ROOT) -> dict[str, Path]:
    json_path = root / JSON_ARTIFACT
    report_path = root / REPORT_ARTIFACT
    summary_path = root / RUN_SUMMARY_ARTIFACT.format(run_id=payload["run_id"])
    capsule_path = root / CLAIM_CAPSULE_ARTIFACT.format(run_id=payload["run_id"])
    _write_json_atomic(json_path, payload)
    _write_text_atomic(report_path, render_markdown(payload))
    _write_json_atomic(summary_path, build_summary(payload))
    _write_json_atomic(capsule_path, build_claim_capsule(payload))
    return {
        "json": json_path,
        "report": report_path,
        "summary": summary_path,
        "claim_capsule": capsule_path,
    }


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="Run the gap-head transfer atlas.")
    parser.add_argument("--root", type=Path, default=ROOT, help="quality-lab root for artifact output")
    parser.add_argument("--run-id", default=RUN_ID_PREFIX, help="run id for reports/runs artifacts")
    args = parser.parse_args(argv)
    payload = build_payload(run_id=args.run_id)
    paths = write_outputs(payload, root=args.root)
    decision = payload["multi_surface_d5_o"]
    print(f"wrote {paths['json'].relative_to(args.root)}")
    print(f"wrote {paths['report'].relative_to(args.root)}")
    print(f"wrote {paths['summary'].relative_to(args.root)}")
    print(f"wrote {paths['claim_capsule'].relative_to(args.root)}")
    print(f"multi_surface_d5_o {decision['decision']}")
    print(f"pass_surface_count {decision['pass_surface_count']}")
    print(f"boundary_ledger_count {len(payload['boundary_ledger'])}")


if __name__ == "__main__":
    main()

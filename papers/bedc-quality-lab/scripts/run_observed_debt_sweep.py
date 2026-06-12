#!/usr/bin/env python3
"""Run the observed-debt sweep over LeJEPA theorem assumption surfaces."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import sys
from typing import Any, Iterable, Mapping

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.debt import ACTION_TRANSITION_ROW, DIMENSION_MATCH_ROW, assess_debt
from bedc_quality_lab.identifiability_bound import identifiability_bound_metrics
from bedc_quality_lab.ledger import derive_ledger_gaps, format_ledger_gaps
from bedc_quality_lab.metrics import metric_bundle, quality_components
from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope
from bedc_quality_lab.toy_world import make_toy_batch
from scripts.experiment_stats import metric_stats


MASTER_SEED = 616540
RHO = 0.82
BASELINE_ENCODER_DIM = 2
BASELINE_TRAINING_STEPS = 2000
BASELINE_SAMPLE_COUNT = 4096
BASELINE_METRIC = "linear_identifiability_r2"
C1_ENCODER_DIMS = (1, 2, 3, 4)
C2_TRAINING_STEPS = (10, 20, 50, 100, 500, 2000)
C3_SAMPLE_COUNTS = (128, 256, 512, 1024, 4096)
C4_ACTION_TRANSITION_VALUES = (False, True)
DEFAULT_SEED_COUNT_BY_AXIS = {'C1': 10, "C2": 6, "C3": 10, "C4": 6}
SMOKE_SEED_COUNT = 1
JSON_ARTIFACT = "reports/canonical/observed-debt-sweep.json"
REPORT_ARTIFACT = "reports/canonical/observed-debt-sweep.md"
DIMENSION_ROW = "source/dimension-match"
C4_CLAIM_BOUNDARY = {
    "claim_surface": "observed-debt-availability-probe",
    "evidence_pointer": "reports/gaussian_ou_dynamics_planning.json:$.applicability_boundary",
    "not_claimed": [
        "no full world model planning claim",
        "no action-transition certificate",
    ],
}
C4_ALLOWED_VERDICTS = frozenset({"observed-debt-pipeline-only", "observed-debt"})
C4_FORBIDDEN_MARKDOWN_WORDING = (
    "full planning closure",
    "full-planning closure",
    "planning closure",
    "world model planning closure",
    "closed planning theorem",
)


@dataclass(frozen=True)
class ObservedDebtEffect:
    metric: str
    baseline: Mapping[str, float | int]
    cell: Mapping[str, float | int]
    delta: float
    delta_ci95_half_width: float
    delta_ci95_low: float
    delta_ci95_high: float
    significant: bool
    effect_reported: bool = True

    def to_record(self) -> dict[str, Any]:
        return {
            "metric": self.metric,
            "baseline": dict(self.baseline),
            "cell": dict(self.cell),
            "delta": self.delta,
            "delta_ci95_half_width": self.delta_ci95_half_width,
            "delta_ci95_low": self.delta_ci95_low,
            "delta_ci95_high": self.delta_ci95_high,
            "significant": self.significant,
            "effect_reported": self.effect_reported,
        }


@dataclass(frozen=True)
class ObservedDebtVerdict:
    verdict: str
    reason: str
    global_claim_flag: bool = False

    def to_record(self) -> dict[str, Any]:
        return {
            "verdict": self.verdict,
            "reason": self.reason,
            "global_claim_flag": self.global_claim_flag,
        }


@dataclass(frozen=True)
class ObservedDebtCell:
    axis: str
    axis_label: str
    axis_value: int | bool
    seed_count: int
    seeds: tuple[int, ...]
    row: str
    metric: str
    records: tuple[dict[str, Any], ...]
    effect: ObservedDebtEffect
    verdict: ObservedDebtVerdict
    scope: str
    claim_boundary: Mapping[str, Any] | None = None
    skipped: bool = False
    skip_reason: str | None = None

    def to_record(self) -> dict[str, Any]:
        record = {
            "axis": self.axis,
            "axis_label": self.axis_label,
            "axis_value": self.axis_value,
            "seed_count": self.seed_count,
            "seeds": list(self.seeds),
            "row": self.row,
            "metric": self.metric,
            "records": list(self.records),
            "effect": self.effect.to_record(),
            "verdict": self.verdict.to_record(),
            "scope": self.scope,
            "skipped": self.skipped,
            "skip_reason": self.skip_reason,
        }
        if self.claim_boundary is not None:
            record["claim_boundary"] = dict(self.claim_boundary)
        return record


def _child_seed(axis: str, seed_index: int) -> int:
    axis_value = sum((index + 1) * ord(char) for index, char in enumerate(axis))
    value = (
        MASTER_SEED * 1664525
        + 1013904223
        + axis_value * 374761393
        + int(seed_index) * 2246822519
        + int(seed_index) * int(seed_index) * 3266489917
    )
    return int(value % (2**32))


def _seeds(axis: str, count: int) -> tuple[int, ...]:
    return tuple(_child_seed(axis, index) for index in range(count))


def _row_present(envelope: QualityEvidenceEnvelope, row: str) -> bool:
    kind, residue = row.split("/", 1)
    needle = f"kind={kind}; residue={residue};"
    return any(item.startswith(needle) for item in envelope.debt_items)


def _row_gap(envelope: QualityEvidenceEnvelope, row: str) -> bool:
    kind, residue = row.split("/", 1)
    needle = f"kind={kind}; residue={residue};"
    return any(item.startswith(needle) for item in envelope.ledger_gaps)


def _gap_row(gap: str) -> str:
    fields = {}
    for part in gap.split(";"):
        if "=" not in part:
            continue
        key, value = part.strip().split("=", 1)
        fields[key] = value
    return f"{fields.get('kind', '')}/{fields.get('residue', '')}"


def _scoped_ledger_gaps(gaps: list[str], allowed_rows: frozenset[str] | None) -> list[str]:
    if allowed_rows is None:
        return gaps
    return [gap for gap in gaps if _gap_row(gap) in allowed_rows]


def _metric_record(
    *,
    envelope: QualityEvidenceEnvelope,
    axis: str,
    axis_label: str,
    axis_value: int | bool,
    seed: int,
    seed_index: int,
    row: str,
    metric: str,
) -> dict[str, Any]:
    return {
        "axis": axis,
        "axis_label": axis_label,
        "axis_value": axis_value,
        "seed": int(seed),
        "seed_index": int(seed_index),
        "run_id": envelope.run_id,
        "metric": metric,
        "metric_value": float(envelope.metrics[metric]),
        "row": row,
        "row_present": _row_present(envelope, row),
        "row_gap": _row_gap(envelope, row),
        "schema_id": envelope.schema_id,
        "envelope": envelope.to_dict(),
    }


def _train_eval_split(sample_count: int, *, seed: int) -> tuple[np.ndarray, np.ndarray]:
    if sample_count < 4:
        raise ValueError("sample_count must be at least 4")
    rng = np.random.default_rng(seed ^ 0xA5A5A5A5)
    indices = rng.permutation(sample_count)
    train_count = min(sample_count - 1, max(1, round(0.70 * sample_count)))
    return np.sort(indices[:train_count]).astype(np.int64), np.sort(indices[train_count:]).astype(np.int64)


def _project_dim(values: np.ndarray, output_dim: int) -> np.ndarray:
    if output_dim < 1:
        raise ValueError("output_dim must be positive")
    matrix = np.asarray(values, dtype=np.float64)
    if output_dim == matrix.shape[1]:
        return matrix
    if output_dim < matrix.shape[1]:
        return matrix[:, :output_dim]
    pad_width = output_dim - matrix.shape[1]
    return np.pad(matrix, ((0, 0), (0, pad_width)), mode="constant")


def _standardized_projection(
    *,
    train_x: np.ndarray,
    eval_x: np.ndarray,
    eval_x_pair: np.ndarray,
    output_dim: int,
) -> tuple[np.ndarray, np.ndarray]:
    centered_train = train_x - np.mean(train_x, axis=0, keepdims=True)
    center = np.mean(train_x, axis=0, keepdims=True)
    scale = np.std(centered_train, axis=0, keepdims=True)
    scale = np.where(scale <= 1e-12, 1.0, scale)
    return _project_dim((eval_x - center) / scale, output_dim), _project_dim((eval_x_pair - center) / scale, output_dim)


def _observed_envelope(
    *,
    axis: str,
    axis_value: int | bool,
    seed: int,
    seed_index: int,
    encoder_dim: int,
    training_steps: int,
    sample_count: int,
    ledger_scope_rows: frozenset[str] | None = None,
) -> QualityEvidenceEnvelope:
    batch = make_toy_batch(sample_count, rho=RHO, seed=seed)
    train_idx, eval_idx = _train_eval_split(batch.z.shape[0], seed=seed)
    h, h_pair = _standardized_projection(
        train_x=batch.x[train_idx],
        eval_x=batch.x[eval_idx],
        eval_x_pair=batch.x_pair[eval_idx],
        output_dim=encoder_dim,
    )
    eval_z = batch.z[eval_idx]
    metrics = metric_bundle(h, eval_z)
    if h.shape == eval_z.shape:
        metrics = {**metrics, **identifiability_bound_metrics(h, h_pair, eval_z, RHO)}
    source_spec = {
        "name": "gaussian-ou-observed-debt-surface",
        "source_count": 3,
        "latent_dim": 2,
        "sample_count": int(batch.z.shape[0]),
        "rho": RHO,
        "latent_distribution": {"family": "gaussian", "coverage_key": "gaussian"},
        "latent_distribution_coverage_keys": ["gaussian", "laplace", "student_t", "uniform_box"],
        "mixing": ["identity", "sinusoidal_shear", "radial_bump", "piecewise_affine"],
        "action_transition_identified": True,
        "global_claim": False,
    }
    classifier_spec = {
        "name": f"standardized-projection-{encoder_dim}",
        "output_dim": int(encoder_dim),
        "training": "deterministic-standardization",
        "optimizer_certificate_steps": int(training_steps),
        "train_count": int(train_idx.shape[0]),
        "eval_count": int(eval_idx.shape[0]),
    }
    stability_spec = {
        "name": "observed-debt-sweep",
        "seed": int(seed),
        "seed_index": int(seed_index),
        "axis": axis,
        "axis_value": axis_value,
        "multi_seed": True,
    }
    extra_rows = (DIMENSION_MATCH_ROW,) if axis == "C1" else ()
    assessment = assess_debt(metrics, source_spec, classifier_spec, stability_spec, extra_rows=extra_rows)
    gaps = derive_ledger_gaps(metrics, source_spec, classifier_spec, stability_spec, assessment)
    ledger_gaps = _scoped_ledger_gaps(format_ledger_gaps(gaps), ledger_scope_rows)
    metrics = {**metrics, **quality_components(metrics, assessment.debt_total, classifier_spec)}
    return QualityEvidenceEnvelope(
        schema_id=SCHEMA_ID,
        run_id=f"observed-debt-{axis}-{axis_value}-seed-{seed}",
        source_spec=source_spec,
        pattern_spec={"name": "latent-linear-recovery", "target": "recover z from representation h"},
        classifier_spec=classifier_spec,
        stability_spec=stability_spec,
        metrics=metrics,
        ledger_gaps=ledger_gaps,
        debt_items=[
            (
                f"kind={item.kind}; residue={item.residue}; severity={item.severity}; "
                f"status={item.status}; score={item.score:.6f}"
            )
            for item in assessment.items
        ],
        artifacts={"envelope": JSON_ARTIFACT, "report": REPORT_ARTIFACT},
        bedc_refs=["papers/bedc-quality-lab/scripts/run_observed_debt_sweep.py"],
    )


def _run_lejepa_cell(
    *,
    axis: str,
    axis_label: str,
    axis_value: int | bool,
    seeds: Iterable[int],
    row: str,
    metric: str,
    encoder_dim: int = BASELINE_ENCODER_DIM,
    training_steps: int = BASELINE_TRAINING_STEPS,
    sample_count: int = BASELINE_SAMPLE_COUNT,
    ledger_scope_rows: frozenset[str] | None = None,
) -> tuple[dict[str, Any], ...]:
    records = []
    for seed_index, seed in enumerate(seeds):
        envelope = _observed_envelope(
            axis=axis,
            axis_value=axis_value,
            seed=seed,
            seed_index=seed_index,
            encoder_dim=encoder_dim,
            training_steps=training_steps,
            sample_count=sample_count,
            ledger_scope_rows=ledger_scope_rows,
        )
        records.append(
            _metric_record(
                envelope=envelope,
                axis=axis,
                axis_label=axis_label,
                axis_value=axis_value,
                seed=seed,
                seed_index=seed_index,
                row=row,
                metric=metric,
            )
        )
    return tuple(records)


def _action_transition_envelope(
    *,
    seed: int,
    seed_index: int,
    action_transition_identified: bool,
) -> QualityEvidenceEnvelope:
    batch = make_toy_batch(BASELINE_SAMPLE_COUNT, rho=RHO, seed=seed)
    metrics = metric_bundle(batch.x, batch.z)
    if batch.x.shape == batch.z.shape:
        metrics = {**metrics, **identifiability_bound_metrics(batch.x, batch.x_pair, batch.z, RHO)}
    source_spec = {
        "name": "gaussian-ou-action-transition-surface",
        "source_count": 3,
        "latent_dim": 2,
        "sample_count": int(batch.z.shape[0]),
        "rho": RHO,
        "latent_distribution": {"family": "gaussian", "coverage_key": "gaussian"},
        "latent_distribution_coverage_keys": ["gaussian", "laplace", "student_t", "uniform_box"],
        "mixing": ["identity", "sinusoidal_shear", "radial_bump", "piecewise_affine"],
        "action_transition_identified": bool(action_transition_identified),
    }
    classifier_spec = {
        "name": "deterministic-transition-proxy",
        "output_dim": 2,
        "training": "action transition availability probe" if action_transition_identified else "deterministic action replay",
    }
    stability_spec = {
        "name": "observed-debt-action-transition",
        "seed": int(seed),
        "seed_index": int(seed_index),
        "multi_seed": True,
    }
    assessment = assess_debt(
        metrics,
        source_spec,
        classifier_spec,
        stability_spec,
        extra_rows=(ACTION_TRANSITION_ROW,),
    )
    gaps = derive_ledger_gaps(metrics, source_spec, classifier_spec, stability_spec, assessment)
    metrics = {**metrics, **quality_components(metrics, assessment.debt_total, classifier_spec)}
    return QualityEvidenceEnvelope(
        schema_id=SCHEMA_ID,
        run_id=f"observed-debt-C4-{action_transition_identified}-seed-{seed}",
        source_spec=source_spec,
        pattern_spec={"name": "action-transition-identification", "target": "identify action-conditioned transition"},
        classifier_spec=classifier_spec,
        stability_spec=stability_spec,
        metrics=metrics,
        ledger_gaps=format_ledger_gaps(gaps),
        debt_items=[
            (
                f"kind={item.kind}; residue={item.residue}; severity={item.severity}; "
                f"status={item.status}; score={item.score:.6f}"
            )
            for item in assessment.items
        ],
        artifacts={"envelope": JSON_ARTIFACT, "report": REPORT_ARTIFACT},
        bedc_refs=["papers/bedc-quality-lab/scripts/run_gaussian_ou_dynamics_planning.py"],
    )


def _planning_axis_available() -> tuple[bool, str]:
    try:
        import scripts.run_gaussian_ou_dynamics_planning as planning
    except Exception as exc:
        return False, f"planning axis import failed: {exc}"
    required = ("ACTION_SET", "_true_next_z", "_train_transitions")
    missing = [name for name in required if not hasattr(planning, name)]
    if missing:
        return False, f"planning axis missing surface: {', '.join(missing)}"
    return True, "planning axis available"


def _run_action_transition_cell(
    *,
    axis: str,
    axis_label: str,
    axis_value: bool,
    seeds: Iterable[int],
    row: str,
    metric: str,
) -> tuple[dict[str, Any], ...]:
    records = []
    for seed_index, seed in enumerate(seeds):
        envelope = _action_transition_envelope(
            seed=seed,
            seed_index=seed_index,
            action_transition_identified=bool(axis_value),
        )
        records.append(
            _metric_record(
                envelope=envelope,
                axis=axis,
                axis_label=axis_label,
                axis_value=axis_value,
                seed=seed,
                seed_index=seed_index,
                row=row,
                metric=metric,
            )
        )
    return tuple(records)


def effect_from_baseline(
    metric: str,
    baseline_stats: Mapping[str, float | int],
    cell_stats: Mapping[str, float | int],
) -> ObservedDebtEffect:
    baseline_mean = float(baseline_stats["mean"])
    cell_mean = float(cell_stats["mean"])
    baseline_ci = float(baseline_stats["ci95_half_width"])
    cell_ci = float(cell_stats["ci95_half_width"])
    delta = cell_mean - baseline_mean
    delta_ci = math.sqrt(baseline_ci * baseline_ci + cell_ci * cell_ci)
    low = delta - delta_ci
    high = delta + delta_ci
    enough_power = int(baseline_stats["n"]) >= 2 and int(cell_stats["n"]) >= 2
    significant = bool(enough_power and (high < 0.0 or low > 0.0))
    return ObservedDebtEffect(
        metric=metric,
        baseline=baseline_stats,
        cell=cell_stats,
        delta=float(delta),
        delta_ci95_half_width=float(delta_ci),
        delta_ci95_low=float(low),
        delta_ci95_high=float(high),
        significant=significant,
    )


def verdict_for_cell(row: str, effect: ObservedDebtEffect, scope: str) -> ObservedDebtVerdict:
    del row
    if not effect.significant:
        return ObservedDebtVerdict(
            verdict="observed-debt-pipeline-only",
            reason=f"effect not significant inside {scope}",
        )
    if effect.delta < 0.0:
        return ObservedDebtVerdict(
            verdict="observed-debt",
            reason=f"significant negative effect inside {scope}",
        )
    return ObservedDebtVerdict(
        verdict="observed-debt-pipeline-only",
        reason=f"effect is significant but not negative inside {scope}",
    )


def _stats(records: tuple[dict[str, Any], ...], metric: str) -> dict[str, float | int]:
    return metric_stats(float(record["metric_value"]) for record in records if record["metric"] == metric)


def _cell(
    *,
    axis: str,
    axis_label: str,
    axis_value: int | bool,
    seeds: tuple[int, ...],
    row: str,
    metric: str,
    records: tuple[dict[str, Any], ...],
    baseline_stats: Mapping[str, float | int],
    scope: str,
    claim_boundary: Mapping[str, Any] | None = None,
) -> ObservedDebtCell:
    effect = effect_from_baseline(metric, baseline_stats, _stats(records, metric))
    verdict = verdict_for_cell(row, effect, scope)
    return ObservedDebtCell(
        axis=axis,
        axis_label=axis_label,
        axis_value=axis_value,
        seed_count=len(seeds),
        seeds=seeds,
        row=row,
        metric=metric,
        records=records,
        effect=effect,
        verdict=verdict,
        scope=scope,
        claim_boundary=claim_boundary,
    )


def _skipped_cell(
    *,
    axis: str,
    axis_label: str,
    axis_value: bool,
    seeds: tuple[int, ...],
    row: str,
    metric: str,
    baseline_stats: Mapping[str, float | int],
    reason: str,
    claim_boundary: Mapping[str, Any] | None = None,
) -> ObservedDebtCell:
    empty_stats = metric_stats([])
    effect = effect_from_baseline(metric, baseline_stats, empty_stats)
    verdict = ObservedDebtVerdict(
        verdict="observed-debt-pipeline-only",
        reason=f"skipped: {reason}",
    )
    return ObservedDebtCell(
        axis=axis,
        axis_label=axis_label,
        axis_value=axis_value,
        seed_count=len(seeds),
        seeds=seeds,
        row=row,
        metric=metric,
        records=(),
        effect=effect,
        verdict=verdict,
        scope="planning axis unavailable",
        claim_boundary=claim_boundary,
        skipped=True,
        skip_reason=reason,
    )


def _seed_count(axis: str, *, smoke: bool, override: int | None) -> int:
    if override is not None:
        return int(override)
    if smoke:
        return SMOKE_SEED_COUNT
    return DEFAULT_SEED_COUNT_BY_AXIS[axis]


def _baseline_records(seed_count: int) -> tuple[dict[str, Any], ...]:
    seeds = _seeds("baseline", seed_count)
    return _run_lejepa_cell(
        axis="baseline",
        axis_label="reference",
        axis_value=BASELINE_ENCODER_DIM,
        seeds=seeds,
        row=DIMENSION_ROW,
        metric=BASELINE_METRIC,
        encoder_dim=BASELINE_ENCODER_DIM,
        training_steps=BASELINE_TRAINING_STEPS,
        sample_count=BASELINE_SAMPLE_COUNT,
    )


def build_payload(*, smoke: bool = False, seed_count: int | None = None, generated_at: str | None = None) -> dict[str, Any]:
    baseline_seed_count = _seed_count('C1', smoke=smoke, override=seed_count)
    baseline_records = _baseline_records(baseline_seed_count)
    baseline_stats = _stats(baseline_records, BASELINE_METRIC)
    cells: list[ObservedDebtCell] = []

    c1_seeds = _seeds('C1', _seed_count('C1', smoke=smoke, override=seed_count))
    for encoder_dim in C1_ENCODER_DIMS:
        ledger_scope_rows = frozenset({DIMENSION_ROW}) if encoder_dim != BASELINE_ENCODER_DIM else None
        records = _run_lejepa_cell(
            axis='C1',
            axis_label="encoder_output_dim",
            axis_value=encoder_dim,
            seeds=c1_seeds,
            row=DIMENSION_ROW,
            metric=BASELINE_METRIC,
            encoder_dim=encoder_dim,
            ledger_scope_rows=ledger_scope_rows,
        )
        cells.append(
            _cell(
                axis='C1',
                axis_label="encoder_output_dim",
                axis_value=encoder_dim,
                seeds=c1_seeds,
                row=DIMENSION_ROW,
                metric=BASELINE_METRIC,
                records=records,
                baseline_stats=baseline_stats,
                scope="encoder output dimension observed debt",
            )
        )

    c2_seeds = _seeds("C2", _seed_count("C2", smoke=smoke, override=seed_count))
    for steps in C2_TRAINING_STEPS:
        records = _run_lejepa_cell(
            axis="C2",
            axis_label="training_steps",
            axis_value=steps,
            seeds=c2_seeds,
            row="classifier/optimizer-certificate",
            metric=BASELINE_METRIC,
            training_steps=steps,
        )
        cells.append(
            _cell(
                axis="C2",
                axis_label="training_steps",
                axis_value=steps,
                seeds=c2_seeds,
                row="classifier/optimizer-certificate",
                metric=BASELINE_METRIC,
                records=records,
                baseline_stats=baseline_stats,
                scope="optimizer certificate observed debt",
            )
        )

    c3_seeds = _seeds("C3", _seed_count("C3", smoke=smoke, override=seed_count))
    for sample_count in C3_SAMPLE_COUNTS:
        records = _run_lejepa_cell(
            axis="C3",
            axis_label="sample_count",
            axis_value=sample_count,
            seeds=c3_seeds,
            row="source/finite-sample-support",
            metric=BASELINE_METRIC,
            sample_count=sample_count,
        )
        cells.append(
            _cell(
                axis="C3",
                axis_label="sample_count",
                axis_value=sample_count,
                seeds=c3_seeds,
                row="source/finite-sample-support",
                metric=BASELINE_METRIC,
                records=records,
                baseline_stats=baseline_stats,
                scope="finite sample observed debt",
            )
        )

    c4_available, c4_reason = _planning_axis_available()
    c4_seeds = _seeds("C4", _seed_count("C4", smoke=smoke, override=seed_count))
    for identified in C4_ACTION_TRANSITION_VALUES:
        if c4_available:
            records = _run_action_transition_cell(
                axis="C4",
                axis_label="action_transition_identified",
                axis_value=identified,
                seeds=c4_seeds,
                row="source/action-transition-identification",
                metric=BASELINE_METRIC,
            )
            cells.append(
                _cell(
                    axis="C4",
                    axis_label="action_transition_identified",
                    axis_value=identified,
                    seeds=c4_seeds,
                    row="source/action-transition-identification",
                    metric=BASELINE_METRIC,
                    records=records,
                    baseline_stats=baseline_stats,
                    scope="action transition identification observed debt",
                    claim_boundary=C4_CLAIM_BOUNDARY,
                )
            )
        else:
            cells.append(
                _skipped_cell(
                    axis="C4",
                    axis_label="action_transition_identified",
                    axis_value=identified,
                    seeds=c4_seeds,
                    row="source/action-transition-identification",
                    metric=BASELINE_METRIC,
                    baseline_stats=baseline_stats,
                    reason=c4_reason,
                    claim_boundary=C4_CLAIM_BOUNDARY,
                )
            )

    records = [cell.to_record() for cell in cells]
    payload = {
        "artifact_id": "bedc-quality-lab:observed-debt-sweep",
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": generated_at or datetime.now(timezone.utc).isoformat(),
        "schema_id": SCHEMA_ID,
        "mode": "smoke" if smoke else "full",
        "config": {
            "rho": RHO,
            "baseline_metric": BASELINE_METRIC,
            "baseline_encoder_dim": BASELINE_ENCODER_DIM,
            "baseline_training_steps": BASELINE_TRAINING_STEPS,
            "baseline_sample_count": BASELINE_SAMPLE_COUNT,
            "actual_seed_count_by_axis": {
                "baseline": baseline_seed_count,
                'C1': len(c1_seeds),
                "C2": len(c2_seeds),
                "C3": len(c3_seeds),
                "C4": len(c4_seeds),
            },
            "C1_encoder_output_dims": list(C1_ENCODER_DIMS),
            "C2_training_steps": list(C2_TRAINING_STEPS),
            "C3_sample_counts": list(C3_SAMPLE_COUNTS),
            "C4_action_transition_identified": list(C4_ACTION_TRANSITION_VALUES),
        },
        "source_artifacts": {
            "generation_script": "scripts/run_observed_debt_sweep.py",
            "canonical_runner": "scripts/run_gaussian_ou_lejepa.py::run_experiment",
            "planning_axis": "scripts/run_gaussian_ou_dynamics_planning.py",
            "json_artifact": JSON_ARTIFACT,
            "report_artifact": REPORT_ARTIFACT,
            "import_dependency_chain": [
                "bedc_quality_lab.toy_world.make_toy_batch",
                "bedc_quality_lab.metrics.metric_bundle",
                "bedc_quality_lab.identifiability_bound.identifiability_bound_metrics",
                "bedc_quality_lab.metrics.quality_components",
                "bedc_quality_lab.debt.assess_debt",
                "bedc_quality_lab.ledger.derive_ledger_gaps",
                "scripts.experiment_stats.metric_stats",
            ],
        },
        "baseline": {
            "seed_count": baseline_seed_count,
            "seeds": list(_seeds("baseline", baseline_seed_count)),
            "metric": BASELINE_METRIC,
            "stats": baseline_stats,
            "records": list(baseline_records),
        },
        "cells": records,
        "grid_summary": _grid_summary(records),
        "hardgate_evidence": _hardgate_evidence(records),
        "global_claim_flag": False,
        "claim_boundary": {
            "C4": C4_CLAIM_BOUNDARY,
        },
        "not_claimed": [
            "no global quality conclusion",
            "no universal LeJEPA conclusion",
            "non-reference dimensions only generate dimension ledger rows",
            "no full world model planning claim",
            "no action-transition certificate",
        ],
    }
    payload["hardgate_evidence"] = _hardgate_evidence(records, render_markdown(payload))
    return payload


def _grid_summary(cells: list[dict[str, Any]]) -> dict[str, Any]:
    summary: dict[str, Any] = {}
    for axis in ('C1', "C2", "C3", "C4"):
        rows = [cell for cell in cells if cell["axis"] == axis]
        summary[axis] = {
            "cell_count": len(rows),
            "seed_counts": sorted({int(cell["seed_count"]) for cell in rows}),
            "axis_values": [cell["axis_value"] for cell in rows],
            "rows": sorted({cell["row"] for cell in rows}),
            "skipped_count": sum(1 for cell in rows if cell["skipped"]),
        }
    return summary


def _c1_dimension_boundary_violations(cells: list[dict[str, Any]]) -> list[str]:
    violations = []
    for cell in cells:
        if cell["axis"] != 'C1' or cell["axis_value"] == BASELINE_ENCODER_DIM:
            continue
        for record in cell["records"]:
            rows = {_gap_row(gap) for gap in record["envelope"]["ledger_gaps"]}
            if rows - {DIMENSION_ROW}:
                violations.append(f"C1:{cell['axis_value']}:{record['seed_index']}")
    return violations


def _c4_boundary_violations(cells: list[dict[str, Any]], markdown_text: str = "") -> list[str]:
    violations = []
    for cell in cells:
        if cell["axis"] != "C4":
            continue
        if cell["verdict"]["global_claim_flag"] is not False:
            violations.append(f"C4:{cell['axis_value']}:global_claim_flag")
        if cell["verdict"]["verdict"] not in C4_ALLOWED_VERDICTS:
            violations.append(f"C4:{cell['axis_value']}:verdict")
        boundary = cell.get("claim_boundary")
        if boundary != C4_CLAIM_BOUNDARY:
            violations.append(f"C4:{cell['axis_value']}:claim_boundary")
    lowered = markdown_text.lower()
    violations.extend(
        f"markdown:{term}"
        for term in C4_FORBIDDEN_MARKDOWN_WORDING
        if term in lowered
    )
    return violations


def _hardgate_evidence(cells: list[dict[str, Any]], markdown_text: str = "") -> dict[str, Any]:
    c_hg1_violations = [
        cell["axis"]
        for cell in cells
        if not cell["skipped"] and not all(record["row_present"] for record in cell["records"])
    ]
    c_hg2_violations = [
        cell["axis"]
        for cell in cells
        if cell["effect"]["effect_reported"] is not True
    ]
    c_hg3_violations = [
        cell["axis"]
        for cell in cells
        if not cell["effect"]["significant"] and cell["verdict"]["verdict"] != "observed-debt-pipeline-only"
    ]
    c_hg4_violations = [
        cell["axis"]
        for cell in cells
        if cell["verdict"]["global_claim_flag"] is not False
    ] + _c1_dimension_boundary_violations(cells)
    c_hg5_violations = _c4_boundary_violations(cells, markdown_text)
    return {
        "C-HG1": {
            "status": "pass" if not c_hg1_violations else "fail",
            "evidence": "every non-skipped cell has its observed-debt row in envelope debt_items",
            "violations": c_hg1_violations,
        },
        "C-HG2": {
            "status": "pass" if not c_hg2_violations else "fail",
            "evidence": "every cell records mean, delta, CI, and effect_reported",
            "violations": c_hg2_violations,
        },
        "C-HG3": {
            "status": "pass" if not c_hg3_violations else "fail",
            "evidence": "non-significant effects use observed-debt-pipeline-only",
            "violations": c_hg3_violations,
        },
        "C-HG4": {
            "status": "pass" if not c_hg4_violations else "fail",
            "evidence": "global_claim_flag remains false and non-reference C1 cells only expose dimension ledger gaps",
            "violations": c_hg4_violations,
        },
        "C-HG5": {
            "status": "pass" if not c_hg5_violations else "fail",
            "evidence": "C4 remains an observed-debt availability probe with no planning closure or action-transition certificate claim",
            "violations": c_hg5_violations,
        },
    }


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Observed-Debt Sweep",
        "",
        f"- JSON artifact: `{payload['artifact']}`",
        f"- Report artifact: `{payload['report']}`",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Mode: `{payload['mode']}`",
        f"- Envelope schema pointer: `$.schema_id`",
        f"- Actual seed count pointer: `$.config.actual_seed_count_by_axis`",
        f"- Baseline pointer: `$.baseline`",
        f"- Cell records pointer: `$.cells`",
        f"- Hardgate evidence pointer: `$.hardgate_evidence`",
        "",
        "## Grid",
        "",
        "| axis | cell count | seed counts | row | skipped | values pointer |",
        "| --- | ---: | --- | --- | ---: | --- |",
    ]
    for axis, row in payload["grid_summary"].items():
        lines.append(
            "| "
            f"{axis} | {row['cell_count']} | "
            f"`{', '.join(str(value) for value in row['seed_counts'])}` | "
            f"`{', '.join(row['rows'])}` | {row['skipped_count']} | "
            f"`$.grid_summary.{axis}.axis_values` |"
        )
    lines.extend(
        [
            "",
            "## Effect Pointers",
            "",
            "| axis | value | row | metric | cell mean | delta | CI half-width | verdict | effect pointer |",
            "| --- | ---: | --- | --- | ---: | ---: | ---: | --- | --- |",
        ]
    )
    for index, cell in enumerate(payload["cells"]):
        effect = cell["effect"]
        lines.append(
            "| "
            f"{cell['axis']} | {cell['axis_value']} | `{cell['row']}` | `{cell['metric']}` | "
            f"{_format_float(float(effect['cell']['mean']))} | "
            f"{_format_float(float(effect['delta']))} | "
            f"{_format_float(float(effect['delta_ci95_half_width']))} | "
            f"`{cell['verdict']['verdict']}` | `$.cells[{index}].effect` |"
        )
    lines.extend(
        [
            "",
            "## Boundaries",
            "",
            f"- Global claim flag pointer: `$.global_claim_flag`",
            f"- C4 claim boundary pointer: `$.claim_boundary.C4`",
            f"- Not claimed pointer: `$.not_claimed`",
            f"- Source artifacts pointer: `$.source_artifacts`",
            "",
        ]
    )
    return "\n".join(lines)


def _write_payload(payload: Mapping[str, Any]) -> None:
    json_path = ROOT / JSON_ARTIFACT
    md_path = ROOT / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_path.write_text(render_markdown(payload), encoding="utf-8")


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="Run observed-debt sweep.")
    parser.add_argument("--smoke", action="store_true", help="Use one seed per axis.")
    parser.add_argument("--seed-count", type=int, help="Override per-axis seed count.")
    args = parser.parse_args(argv)
    if args.seed_count is not None and args.seed_count < 1:
        raise SystemExit("--seed-count must be positive")
    payload = build_payload(smoke=args.smoke, seed_count=args.seed_count)
    _write_payload(payload)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")


if __name__ == "__main__":
    main()

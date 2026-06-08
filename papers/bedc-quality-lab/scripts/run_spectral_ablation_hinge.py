#!/usr/bin/env python3
"""Run the spectral-ablation hinge report."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import json
import math
from pathlib import Path
import statistics
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.schema import SCHEMA_ID
from bedc_quality_lab.transition import TransitionKernelSpec
from scripts.run_gaussian_ou_lejepa import run_experiment


REPORT_SCHEMA_ID = "bedc-quality-lab:spectral-ablation-hinge-report"
BASE_RHO_BY_AXIS = (0.92, 0.64)
DAMP_FACTOR = 0.38
SAMPLE_COUNT = 384
SEED = 851
METRIC_NAMES = (
    "linear_identifiability_r2",
    "actual_recovery_error",
    "theorem3_bound",
    "bound_margin",
    "quality_q",
    "quality_margin",
)
REPORT_JSON = ROOT / "reports" / "spectral_ablation_hinge.json"
REPORT_MD = ROOT / "reports" / "spectral_ablation_hinge.md"
JSON_ARTIFACT = "reports/spectral_ablation_hinge.json"
REPORT_ARTIFACT = "reports/spectral_ablation_hinge.md"
SPECTRAL_JET_JSON_ARTIFACT = "reports/canonical/spectral_jet_report.json"
NONGAUSSIAN_SWEEP_JSON_ARTIFACT = "reports/canonical/nongaussian-distribution-sweep.json"
USE_TORCH = False


@dataclass(frozen=True)
class _HingeArm:
    name: str
    family: str
    deletion_axes: tuple[int, ...]
    damp_factor: float
    mixing: str
    seed_offset: int
    control_for: str | None = None
    note: str = ""


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _rho_key(rho_by_axis: tuple[float, ...]) -> str:
    return "rho_axes_" + "_".join(str(value).replace(".", "p") for value in rho_by_axis)


def _apply_axis_damp(
    spec: TransitionKernelSpec,
    deletion_axes: tuple[int, ...],
    damp_factor: float,
) -> TransitionKernelSpec:
    if not deletion_axes:
        return TransitionKernelSpec(rho_by_axis=tuple(spec.rho_by_axis))
    if damp_factor <= 0.0 or damp_factor >= 1.0 or not math.isfinite(damp_factor):
        raise ValueError("damp_factor must be finite and in (0, 1)")
    rho = list(spec.rho_by_axis)
    for axis in deletion_axes:
        if axis < 0 or axis >= len(rho):
            raise ValueError("deletion axis out of range")
        rho[axis] = float(rho[axis] * damp_factor)
    return TransitionKernelSpec(rho_by_axis=tuple(rho))


def _hinge_row(
    *,
    spec: TransitionKernelSpec,
    deletion_axes: tuple[int, ...],
    damp_factor: float,
    row_type: str,
) -> dict[str, Any]:
    killed = _apply_axis_damp(spec, deletion_axes, damp_factor)
    losses = [
        float(abs(before * before - after * after))
        for before, after in zip(spec.rho_by_axis, killed.rho_by_axis, strict=True)
    ]
    spectral_loss = float(sum(losses[axis] for axis in deletion_axes)) if deletion_axes else 0.0
    if len(deletion_axes) == 1:
        orbit_module = f"axis-{deletion_axes[0]}-orbit"
    elif len(deletion_axes) == len(spec.rho_by_axis):
        orbit_module = "full-latent-module"
    else:
        orbit_module = "partial-latent-module"
    tail_coupling = "tail-sensitive" if spectral_loss >= 0.30 else "tail-local"
    return {
        "row_id": "delete-" + "-".join(str(axis) for axis in deletion_axes) if deletion_axes else "delete-none",
        "row_type": row_type,
        "deletion": {"axes": list(deletion_axes), "axis_count": len(deletion_axes), "damp_factor": damp_factor},
        "killed_transition": {"rho_by_axis": list(killed.rho_by_axis), "rho_key": _rho_key(killed.rho_by_axis)},
        "eigenvalue_loss": {
            "axis_losses": losses,
            "spectral_loss_proxy": spectral_loss,
            "loss_formula": "sum selected abs(rho_before^2 - rho_after^2)",
        },
        "orbit_module": orbit_module,
        "tail_coupling": tail_coupling,
    }


def _build_hinge_ledger(spec: TransitionKernelSpec) -> list[dict[str, Any]]:
    single_rows = [
        _hinge_row(spec=spec, deletion_axes=(axis,), damp_factor=DAMP_FACTOR, row_type="single-axis")
        for axis in range(len(spec.rho_by_axis))
    ]
    rows = sorted(
        single_rows,
        key=lambda row: (
            -float(row["eigenvalue_loss"]["spectral_loss_proxy"]),
            tuple(row["deletion"]["axes"]),
        ),
    )
    rows.append(
        _hinge_row(
            spec=spec,
            deletion_axes=tuple(range(len(spec.rho_by_axis))),
            damp_factor=DAMP_FACTOR,
            row_type="module-analogue",
        )
    )
    for rank, row in enumerate(rows, start=1):
        row["hinge_rank"] = rank
    return rows


def _matched_random_controls(ledger: list[dict[str, Any]], *, seed: int) -> list[_HingeArm]:
    controls: list[_HingeArm] = []
    axis_rows = [row for row in ledger if row["row_type"] == "single-axis"]
    if axis_rows:
        treatment_axes = tuple(int(axis) for axis in axis_rows[0]["deletion"]["axes"])
        alternative_rows = [
            row for row in axis_rows if tuple(int(axis) for axis in row["deletion"]["axes"]) != treatment_axes
        ]
        chosen = alternative_rows[seed % len(alternative_rows)] if alternative_rows else axis_rows[0]
        note = "" if alternative_rows else "no alternative single-axis control exists"
        controls.append(
            _HingeArm(
                name="matched-random-single-axis",
                family="matched-random-control",
                deletion_axes=tuple(int(axis) for axis in chosen["deletion"]["axes"]),
                damp_factor=float(chosen["deletion"]["damp_factor"]),
                mixing="sinusoidal_shear",
                seed_offset=113,
                control_for="hinge-ranked-treatment",
                note=note,
            )
        )
    module_rows = [row for row in ledger if row["row_type"] == "module-analogue"]
    if module_rows:
        row = module_rows[0]
        controls.append(
            _HingeArm(
                name="matched-random-module",
                family="matched-random-control",
                deletion_axes=tuple(reversed(tuple(int(axis) for axis in row["deletion"]["axes"]))),
                damp_factor=float(row["deletion"]["damp_factor"]),
                mixing="sinusoidal_shear",
                seed_offset=127,
                control_for="two-axis-module-analogue",
                note="same axis count and damp factor",
            )
        )
    return controls


def _degradation_from_baseline(baseline: dict[str, float], metrics: dict[str, float]) -> dict[str, float]:
    return {
        "linear_identifiability_r2": float(baseline["linear_identifiability_r2"] - metrics["linear_identifiability_r2"]),
        "actual_recovery_error": float(metrics["actual_recovery_error"] - baseline["actual_recovery_error"]),
        "bound_margin": float(baseline["bound_margin"] - metrics["bound_margin"]),
        "quality_q": float(baseline["quality_q"] - metrics["quality_q"]),
    }


def _observed_degradation_score(delta: dict[str, float]) -> float:
    return float(
        delta["linear_identifiability_r2"]
        + delta["actual_recovery_error"]
        + delta["bound_margin"]
        + delta["quality_q"]
    )


def _rankdata(values: list[float], *, reverse: bool) -> list[float]:
    indexed = sorted(enumerate(values), key=lambda item: item[1], reverse=reverse)
    ranks = [0.0 for _ in values]
    cursor = 0
    while cursor < len(indexed):
        next_cursor = cursor + 1
        while next_cursor < len(indexed) and indexed[next_cursor][1] == indexed[cursor][1]:
            next_cursor += 1
        rank = float((cursor + 1 + next_cursor) / 2.0)
        for index, _ in indexed[cursor:next_cursor]:
            ranks[index] = rank
        cursor = next_cursor
    return ranks


def _pearson(xs: list[float], ys: list[float]) -> float:
    if len(xs) < 2 or len(ys) < 2:
        return math.nan
    x_mean = statistics.fmean(xs)
    y_mean = statistics.fmean(ys)
    x_centered = [value - x_mean for value in xs]
    y_centered = [value - y_mean for value in ys]
    x_norm = math.sqrt(sum(value * value for value in x_centered))
    y_norm = math.sqrt(sum(value * value for value in y_centered))
    if x_norm == 0.0 or y_norm == 0.0:
        return math.nan
    return float(sum(x * y for x, y in zip(x_centered, y_centered, strict=True)) / (x_norm * y_norm))


def _kendall_tau(xs: list[float], ys: list[float]) -> float:
    concordant = 0
    discordant = 0
    for left in range(len(xs)):
        for right in range(left + 1, len(xs)):
            x_diff = xs[left] - xs[right]
            y_diff = ys[left] - ys[right]
            if x_diff == 0.0 or y_diff == 0.0:
                continue
            if x_diff * y_diff > 0.0:
                concordant += 1
            else:
                discordant += 1
    total = concordant + discordant
    if total == 0:
        return math.nan
    return float((concordant - discordant) / total)


def _rank_correlation(ledger: list[dict[str, Any]], arms: list[dict[str, Any]]) -> dict[str, Any]:
    by_axes = {
        tuple(int(axis) for axis in row["deletion"]["axes"]): row
        for row in ledger
    }
    pairs = []
    for arm in arms:
        axes = tuple(int(axis) for axis in arm["deletion_axes"])
        if axes in by_axes and arm["family"] != "matched-random-control":
            row = by_axes[axes]
            pairs.append(
                {
                    "arm": arm["name"],
                    "ledger_row_id": str(row["row_id"]),
                    "deletion_axes": list(axes),
                    "hinge_rank": int(row["hinge_rank"]),
                    "spectral_loss_proxy": float(row["eigenvalue_loss"]["spectral_loss_proxy"]),
                    "observed_degradation_score": float(arm["observed_degradation_score"]),
                }
            )
    spectral_losses = [pair["spectral_loss_proxy"] for pair in pairs]
    observed = [pair["observed_degradation_score"] for pair in pairs]
    spearman = _pearson(_rankdata(spectral_losses, reverse=True), _rankdata(observed, reverse=True))
    kendall = _kendall_tau(spectral_losses, observed)
    ci_width = math.nan if len(pairs) < 3 or math.isnan(spearman) else min(1.0, 1.96 / math.sqrt(len(pairs)))
    return {
        "n": len(pairs),
        "method": "ledger-rank-vs-observed-degradation",
        "spearman": spearman,
        "kendall": kendall,
        "ci95": {
            "low": math.nan if math.isnan(ci_width) else max(-1.0, spearman - ci_width),
            "high": math.nan if math.isnan(ci_width) else min(1.0, spearman + ci_width),
        },
        "pairs": pairs,
        "ordering_note": "observed metrics are read after arm execution and do not alter hinge ledger rank",
    }


def _negative_control_summary(arms: list[dict[str, Any]]) -> dict[str, Any]:
    treatment = next(arm for arm in arms if arm["name"] == "hinge-ranked-treatment")
    controls = [arm for arm in arms if arm["family"] == "matched-random-control"]
    treatment_score = float(treatment["observed_degradation_score"])
    control_scores = [float(arm["observed_degradation_score"]) for arm in controls]
    max_control = max(control_scores) if control_scores else math.nan
    better_than_random = bool(control_scores and treatment_score > max_control)
    return {
        "comparison": "hinge-ranked-treatment vs matched-random-control",
        "metric": "observed_degradation_score",
        "treatment_score": treatment_score,
        "max_control_score": max_control,
        "control_scores": control_scores,
        "treatment_better_than_all_controls": better_than_random,
        "control_count": len(controls),
    }


def _hardening_coverage(
    *,
    arms: list[dict[str, Any]],
    hinge_ledger: list[dict[str, Any]],
    rank_correlation: dict[str, Any],
    negative_control: dict[str, Any],
) -> dict[str, Any]:
    same_class_equivalence = any(
        tuple(left["deletion_axes"]) == tuple(right["deletion_axes"])
        and left["name"] != right["name"]
        and left["family"] != right["family"]
        for index, left in enumerate(arms)
        for right in arms[index + 1 :]
        if left["deletion_axes"] and right["deletion_axes"]
    )
    margin_stability = all(
        math.isfinite(float(arm["metrics"]["bound_margin"]))
        and math.isfinite(float(arm["metrics"]["quality_margin"]))
        for arm in arms
    )
    ledger_rows = {str(row["row_id"]) for row in hinge_ledger}
    covered_rows = {
        str(pair["ledger_row_id"])
        for pair in rank_correlation["pairs"]
        if "ledger_row_id" in pair
    }
    finite_ledger_coverage = bool(ledger_rows) and ledger_rows <= covered_rows
    missing_row_negative_example = bool(
        negative_control["control_count"] > 0
        and negative_control["treatment_better_than_all_controls"] is False
    )
    items = [
        {
            "name": "sameClass equivalence",
            "recorded": same_class_equivalence,
            "source": "$.arms",
        },
        {
            "name": "margin stability",
            "recorded": margin_stability,
            "source": "$.arms",
        },
        {
            "name": "finite ledger coverage",
            "recorded": finite_ledger_coverage,
            "source": "$.rank_correlation.pairs",
        },
        {
            "name": "missing-row negative example",
            "recorded": missing_row_negative_example,
            "source": "$.negative_control_summary",
        },
    ]
    return {
        "recorded": sum(1 for item in items if item["recorded"] is True),
        "required": len(items),
        "items": items,
    }


def _ledger_summary(
    rank_correlation: dict[str, Any],
    negative_control: dict[str, Any],
    *,
    arms: list[dict[str, Any]],
    hinge_ledger: list[dict[str, Any]],
) -> dict[str, Any]:
    spearman = float(rank_correlation["spearman"]) if not math.isnan(float(rank_correlation["spearman"])) else math.nan
    positive = bool(
        negative_control["treatment_better_than_all_controls"]
        and not math.isnan(spearman)
        and spearman > 0.0
    )
    return {
        "status": "closed" if positive else "open-or-partial",
        "claim": "hinge-ranked deletion predicts observed quality degradation",
        "positive_prediction": positive,
        "basis": {
            "hardening_coverage": _hardening_coverage(
                arms=arms,
                hinge_ledger=hinge_ledger,
                rank_correlation=rank_correlation,
                negative_control=negative_control,
            ),
            "negative_control": negative_control,
            "rank_correlation": rank_correlation,
        },
    }


def _spectral_jet(hinge_ledger: list[dict[str, Any]]) -> dict[str, Any]:
    high_order_rows = [
        {
            "row_id": str(row["row_id"]),
            "row_pointer": f"$.hinge_ledger[{index}]",
            "penalty_role": "high-order spectral penalty",
            "axis_count": int(row["deletion"]["axis_count"]),
            "spectral_loss_pointer": f"$.hinge_ledger[{index}].eigenvalue_loss.spectral_loss_proxy",
        }
        for index, row in enumerate(hinge_ledger)
        if int(row["deletion"]["axis_count"]) >= 2
    ]
    return {
        "status": "projection",
        "scope_pointer": "$.applicability_boundary",
        "hinge_ledger_pointer": "$.hinge_ledger",
        "ledger_summary_pointer": "$.ledger_summary",
        "spectral_basis": "selected abs(rho_before^2 - rho_after^2) ledger projection",
        "high_order_penalty_rows": high_order_rows,
        "not_claimed": [
            "No global task-general jet claim.",
            "No non-Gaussian evidence is restated by this projection.",
        ],
    }


def _arm_rows(base_spec: TransitionKernelSpec, ledger: list[dict[str, Any]]) -> list[_HingeArm]:
    top_row = next(row for row in ledger if row["row_type"] == "single-axis")
    module_row = next(row for row in ledger if row["row_type"] == "module-analogue")
    arms = [
        _HingeArm(
            name="vanilla",
            family="baseline",
            deletion_axes=(),
            damp_factor=1.0,
            mixing="sinusoidal_shear",
            seed_offset=0,
        ),
        _HingeArm(
            name="hinge-ranked-treatment",
            family="hinge-ranked-treatment",
            deletion_axes=tuple(int(axis) for axis in top_row["deletion"]["axes"]),
            damp_factor=float(top_row["deletion"]["damp_factor"]),
            mixing="sinusoidal_shear",
            seed_offset=0,
        ),
        _HingeArm(
            name="two-axis-module-analogue",
            family="hinge-ranked-treatment",
            deletion_axes=tuple(int(axis) for axis in module_row["deletion"]["axes"]),
            damp_factor=float(module_row["deletion"]["damp_factor"]),
            mixing="sinusoidal_shear",
            seed_offset=0,
        ),
        _HingeArm(
            name="tail-mixing-perturbation",
            family="tail-mixing-perturbation",
            deletion_axes=tuple(int(axis) for axis in top_row["deletion"]["axes"]),
            damp_factor=float(top_row["deletion"]["damp_factor"]),
            mixing="realnvp_coupling",
            seed_offset=0,
        ),
    ]
    return arms + _matched_random_controls(ledger, seed=SEED + len(base_spec.rho_by_axis))


def _run_arm(base_spec: TransitionKernelSpec, arm: _HingeArm) -> dict[str, Any]:
    spec = _apply_axis_damp(base_spec, arm.deletion_axes, arm.damp_factor)
    envelope = run_experiment(
        use_torch=USE_TORCH,
        sample_count=SAMPLE_COUNT,
        seed=SEED + arm.seed_offset,
        rho=float(statistics.fmean(spec.rho_by_axis)),
        transition_kernel=spec,
        mixing=arm.mixing,
        run_id=f"spectral-ablation-hinge-{arm.name}-{_rho_key(spec.rho_by_axis)}",
        envelope_artifact=JSON_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
    )
    return {
        "name": arm.name,
        "family": arm.family,
        "control_for": arm.control_for,
        "note": arm.note,
        "deletion_axes": list(arm.deletion_axes),
        "damp_factor": arm.damp_factor,
        "mixing": arm.mixing,
        "seed": SEED + arm.seed_offset,
        "transition_source_spec": envelope.source_spec["transition_kernel"],
        "metrics": {name: float(envelope.metrics[name]) for name in METRIC_NAMES},
        "envelope_projection": {
            "schema_id": envelope.schema_id,
            "run_id": envelope.run_id,
            "source_spec": envelope.source_spec,
            "classifier_spec": envelope.classifier_spec,
            "stability_spec": envelope.stability_spec,
            "metrics": {name: float(envelope.metrics[name]) for name in METRIC_NAMES},
            "ledger_gaps": envelope.ledger_gaps,
            "debt_items": envelope.debt_items,
        },
    }


def _payload() -> dict[str, Any]:
    base_spec = TransitionKernelSpec(rho_by_axis=BASE_RHO_BY_AXIS)
    hinge_ledger = _build_hinge_ledger(base_spec)
    arms = [_run_arm(base_spec, arm) for arm in _arm_rows(base_spec, hinge_ledger)]
    baseline_metrics = next(arm["metrics"] for arm in arms if arm["name"] == "vanilla")
    for arm in arms:
        delta = _degradation_from_baseline(baseline_metrics, arm["metrics"])
        arm["degradation_delta_vs_vanilla"] = delta
        arm["observed_degradation_score"] = _observed_degradation_score(delta)
    rank_correlation = _rank_correlation(hinge_ledger, arms)
    negative_control = _negative_control_summary(arms)
    return {
        "report_schema_id": REPORT_SCHEMA_ID,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "config": {
            "schema_id": SCHEMA_ID,
            "base_rho_by_axis": list(BASE_RHO_BY_AXIS),
            "damp_factor": DAMP_FACTOR,
            "sample_count": SAMPLE_COUNT,
            "seed": SEED,
            "use_torch": USE_TORCH,
            "metric_names": list(METRIC_NAMES),
            "max_envelope_calls": 9,
            "actual_envelope_calls": len(arms),
        },
        "source_artifacts": {
            "transition_surface": "bedc_quality_lab/transition.py",
            "canonical_runner": "scripts/run_gaussian_ou_lejepa.py",
            "evidence_schema": "bedc_quality_lab/schema.py",
        },
        "arms": arms,
        "hinge_ledger": hinge_ledger,
        "spectral_jet": _spectral_jet(hinge_ledger),
        "rank_correlation": rank_correlation,
        "negative_control_summary": negative_control,
        "ledger_summary": _ledger_summary(
            rank_correlation,
            negative_control,
            arms=arms,
            hinge_ledger=hinge_ledger,
        ),
        "applicability_boundary": {
            "claimed_scope": "Gaussian 2D latent + diagonal Gaussian OU transition + runner-local hinge ledger.",
            "not_claimed": "This report does not claim full biological killed-walk coverage or formal BEDC closure.",
            "bedc_refs": [
                "papers/bedc/parts/concrete_instances/108564_spectral_ablation_hinge_namecert_construction.tex",
            ],
        },
    }


def _spectral_jet_report_payload(payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:spectral-jet-report-sidecar",
        "artifact_id": "bedc-quality-lab:spectral-jet-report",
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "owner_report": "spectral-ablation-hinge",
        "owner_artifact": JSON_ARTIFACT,
        "generated_at": payload["generated_at"],
        "status": "pointer-only",
        "source_pointer": f"{JSON_ARTIFACT}:$",
        "scope_pointer": f"{JSON_ARTIFACT}:$.applicability_boundary",
        "applicability_boundary_pointer": f"{JSON_ARTIFACT}:$.applicability_boundary",
        "hinge_ledger_pointer": f"{JSON_ARTIFACT}:$.hinge_ledger",
        "ledger_summary_pointer": f"{JSON_ARTIFACT}:$.ledger_summary",
        "spectral_jet_pointer": f"{JSON_ARTIFACT}:$.spectral_jet",
        "high_order_penalty_row_pointers": [
            f"{JSON_ARTIFACT}:{row['row_pointer']}"
            for row in payload["spectral_jet"]["high_order_penalty_rows"]
        ],
        "nongaussian_sweep_references": [
            {
                "artifact": NONGAUSSIAN_SWEEP_JSON_ARTIFACT,
                "pointer": "$.records",
                "role": "out-of-scope latent-distribution cases",
            },
            {
                "artifact": NONGAUSSIAN_SWEEP_JSON_ARTIFACT,
                "pointer": "$.not_claimed",
                "role": "non-Gaussian boundary statement",
            },
        ],
        "not_claimed": [
            "This sidecar does not assert global task-general behavior.",
            "This sidecar does not restate non-Gaussian sweep evidence.",
            "This sidecar does not assert theorem closure, terminal verdicts, or discovery level.",
        ],
    }


def _render_markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# Spectral-ablation hinge report",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Report schema id: `{payload['report_schema_id']}`",
        f"- Envelope schema id: `{payload['config']['schema_id']}`",
        f"- Base rho by axis: `{payload['config']['base_rho_by_axis']}`",
        f"- Damp factor: `{payload['config']['damp_factor']}`",
        f"- Envelope calls: `{payload['config']['actual_envelope_calls']}`",
        f"- Ledger status: `{payload['ledger_summary']['status']}`",
        "",
        "## Hinge ledger",
        "",
        "| rank | row | axes | spectral loss | orbit module | tail coupling | killed rho |",
        "| ---: | --- | --- | ---: | --- | --- | --- |",
    ]
    for row in payload["hinge_ledger"]:
        axes = ", ".join(str(axis) for axis in row["deletion"]["axes"])
        killed = ", ".join(_format_float(float(value)) for value in row["killed_transition"]["rho_by_axis"])
        lines.append(
            "| "
            f"{row['hinge_rank']} | `{row['row_type']}` | `({axes})` | "
            f"{_format_float(float(row['eigenvalue_loss']['spectral_loss_proxy']))} | "
            f"`{row['orbit_module']}` | `{row['tail_coupling']}` | `({killed})` |"
        )
    lines.extend(
        [
            "",
            "## Arms",
            "",
            "| arm | family | axes | mixing | degradation score | linear R2 delta | recovery error delta | quality_q delta |",
            "| --- | --- | --- | --- | ---: | ---: | ---: | ---: |",
        ]
    )
    for arm in payload["arms"]:
        axes = ", ".join(str(axis) for axis in arm["deletion_axes"])
        delta = arm["degradation_delta_vs_vanilla"]
        lines.append(
            "| "
            f"`{arm['name']}` | `{arm['family']}` | `({axes})` | `{arm['mixing']}` | "
            f"{_format_float(float(arm['observed_degradation_score']))} | "
            f"{_format_float(float(delta['linear_identifiability_r2']))} | "
            f"{_format_float(float(delta['actual_recovery_error']))} | "
            f"{_format_float(float(delta['quality_q']))} |"
        )
    corr = payload["rank_correlation"]
    neg = payload["negative_control_summary"]
    lines.extend(
        [
            "",
            "## Rank correlation",
            "",
            f"- Spearman: `{_format_float(float(corr['spearman']))}`",
            f"- Kendall: `{_format_float(float(corr['kendall']))}`",
            f"- CI95: `[{_format_float(float(corr['ci95']['low']))}, {_format_float(float(corr['ci95']['high']))}]`",
            f"- Ordering note: {corr['ordering_note']}",
            "",
            "## Negative-control audit",
            "",
            f"- Comparison: `{neg['comparison']}`",
            f"- Treatment score: `{_format_float(float(neg['treatment_score']))}`",
            f"- Max control score: `{_format_float(float(neg['max_control_score']))}`",
            f"- Treatment better than all controls: `{neg['treatment_better_than_all_controls']}`",
            f"- Ledger status: `{payload['ledger_summary']['status']}`",
            "",
            "## Spectral jet",
            "",
            f"- Status: `{payload['spectral_jet']['status']}`",
            f"- Scope pointer: `{payload['spectral_jet']['scope_pointer']}`",
            f"- Hinge ledger pointer: `{payload['spectral_jet']['hinge_ledger_pointer']}`",
            f"- High-order penalty rows: `{len(payload['spectral_jet']['high_order_penalty_rows'])}`",
            "",
            "## Applicability boundary",
            "",
            f"- Claimed scope: `{payload['applicability_boundary']['claimed_scope']}`",
            f"- Not claimed: {payload['applicability_boundary']['not_claimed']}",
            "",
        ]
    )
    return "\n".join(lines)


def _write_payload(payload: dict[str, Any]) -> None:
    REPORT_JSON.parent.mkdir(parents=True, exist_ok=True)
    REPORT_JSON.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    REPORT_MD.write_text(_render_markdown(payload), encoding="utf-8")
    spectral_jet_path = ROOT / SPECTRAL_JET_JSON_ARTIFACT
    spectral_jet_path.parent.mkdir(parents=True, exist_ok=True)
    spectral_jet_path.write_text(
        json.dumps(_spectral_jet_report_payload(payload), indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def main() -> None:
    payload = _payload()
    _write_payload(payload)
    print(f"wrote {REPORT_JSON.relative_to(ROOT)}")
    print(f"wrote {REPORT_MD.relative_to(ROOT)}")


if __name__ == "__main__":
    main()

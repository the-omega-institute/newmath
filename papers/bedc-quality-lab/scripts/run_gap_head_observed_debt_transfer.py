#!/usr/bin/env python3
"""Run gap-head-on-h transfer checks on observed-debt surfaces."""

from __future__ import annotations

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

from scripts.experiment_stats import metric_stats
from scripts import run_gap_ledger_head_on_h as producer
from scripts import run_gap_head_robustness_sweep as robustness
from scripts import run_observed_debt_sweep as observed_debt


JSON_ARTIFACT = "reports/canonical/gap-head-observed-debt-transfer.json"
REPORT_ARTIFACT = "reports/canonical/gap-head-observed-debt-transfer.md"
ARTIFACT_ID = "bedc-quality-lab:gap-head-observed-debt-transfer"
TRANSFER_STATUS_POINTER = "$.gap_head_on_h_observed_debt_transfer.status"
DEFAULT_AXIS = "C3"
DEFAULT_AXIS_LABEL = "sample_count"
DEFAULT_AXIS_VALUE = 1024
DEFAULT_ROW = "source/finite-sample-support"
DEFAULT_SCOPE = "finite sample observed debt"


@dataclass(frozen=True)
class TransferSurfaceSpec:
    surface_id: str
    observed_debt_axis: str
    axis_label: str
    axis_value: int | bool
    observed_debt_row: str
    observed_debt_metric: str
    observed_debt_scope: str
    sample_count: int
    seeds: tuple[int, ...]
    rho: float
    use_torch: bool


def _format_float(value: float) -> str:
    if math.isnan(value):
        return "nan"
    return f"{value:.6f}"


def _default_surface_specs() -> tuple[TransferSurfaceSpec, ...]:
    seeds = observed_debt._seeds(DEFAULT_AXIS, observed_debt.DEFAULT_SEED_COUNT_BY_AXIS[DEFAULT_AXIS])
    return (
        TransferSurfaceSpec(
            surface_id=f"observed-debt-{DEFAULT_AXIS.lower()}-{DEFAULT_AXIS_VALUE}",
            observed_debt_axis=DEFAULT_AXIS,
            axis_label=DEFAULT_AXIS_LABEL,
            axis_value=DEFAULT_AXIS_VALUE,
            observed_debt_row=DEFAULT_ROW,
            observed_debt_metric=observed_debt.BASELINE_METRIC,
            observed_debt_scope=DEFAULT_SCOPE,
            sample_count=DEFAULT_AXIS_VALUE,
            seeds=tuple(int(seed) for seed in seeds),
            rho=observed_debt.RHO,
            use_torch=False,
        ),
    )


def _config_for_surface(spec: TransferSurfaceSpec) -> producer.GapHeadRunConfig:
    return producer.GapHeadRunConfig(
        sample_count=int(spec.sample_count),
        seeds=tuple(int(seed) for seed in spec.seeds),
        rho=float(spec.rho),
        use_torch=bool(spec.use_torch),
        json_artifact=JSON_ARTIFACT,
        report_artifact=REPORT_ARTIFACT,
        run_id_prefix=f"gap-head-observed-debt-transfer-{spec.surface_id}",
        source_artifact_label="gap-head-observed-debt-transfer",
        seed_grid_kind=f"observed-debt-{spec.observed_debt_axis}",
    )


def _forbidden_feature_audit(feature_columns: list[str]) -> dict[str, Any]:
    return producer._forbidden_column_audit(feature_columns)


def _metric_projection(metrics: dict[str, Any]) -> dict[str, Any]:
    return producer._metric_projection(metrics)


def _seed_summary(*, seed: int, seed_index: int, config: producer.GapHeadRunConfig) -> dict[str, Any]:
    surface = producer._surface_for_seed(seed=int(seed), config=config)
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
        "comparison": {
            "unlogged_error_reduction_learned": float(
                vanilla["unlogged_error_rate"] - learned["unlogged_error_rate"]
            ),
            "unlogged_error_reduction_matched_random": float(
                vanilla["unlogged_error_rate"] - matched["unlogged_error_rate"]
            ),
        },
    }


def _stats_from_summaries(summaries: list[dict[str, Any]], getter: Any) -> dict[str, Any]:
    return metric_stats(float(getter(summary)) for summary in summaries)


def _arm_stats(summaries: list[dict[str, Any]], arm: str) -> dict[str, Any]:
    return {
        "failure_detection_auroc": _stats_from_summaries(
            summaries, lambda summary: summary["arms"][arm]["failure_detection_auroc"]["value"]
        ),
        "unlogged_error_rate": _stats_from_summaries(
            summaries, lambda summary: summary["arms"][arm]["unlogged_error_rate"]
        ),
        "critical_unlogged_error_rate": _stats_from_summaries(
            summaries, lambda summary: summary["arms"][arm]["critical_unlogged_error_rate"]
        ),
        "prediction_error_rate": _stats_from_summaries(
            summaries, lambda summary: summary["arms"][arm]["prediction_error_rate"]
        ),
    }


def _producer_verdict_aggregate(summaries: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "by_arm": {
            "vanilla": _arm_stats(summaries, "vanilla"),
            "learned_gap_head_on_h": _arm_stats(summaries, "learned_gap_head_on_h"),
            producer.MATCHED_RANDOM_ARM: _arm_stats(summaries, producer.MATCHED_RANDOM_ARM),
        }
    }


def _surface_metrics(summaries: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "vanilla": _arm_stats(summaries, "vanilla"),
        "learned_gap_head_on_h": {
            **_arm_stats(summaries, "learned_gap_head_on_h"),
            "unlogged_error_reduction": _stats_from_summaries(
                summaries, lambda summary: summary["comparison"]["unlogged_error_reduction_learned"]
            ),
        },
        producer.MATCHED_RANDOM_ARM: {
            **_arm_stats(summaries, producer.MATCHED_RANDOM_ARM),
            "unlogged_error_reduction": _stats_from_summaries(
                summaries,
                lambda summary: summary["comparison"]["unlogged_error_reduction_matched_random"],
            ),
        },
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
    control_verdict: Mapping[str, Any],
    forbidden_audit: Mapping[str, Any],
) -> dict[str, Any]:
    learned_auroc = metrics["learned_gap_head_on_h"]["failure_detection_auroc"]
    matched_auroc = metrics[producer.MATCHED_RANDOM_ARM]["failure_detection_auroc"]
    learned_reduction = metrics["learned_gap_head_on_h"]["unlogged_error_reduction"]
    matched_reduction = metrics[producer.MATCHED_RANDOM_ARM]["unlogged_error_reduction"]
    return {
        "HG-A1": {
            "status": "pass"
            if (
                float(learned_auroc["ci95_low"]) > float(matched_auroc["ci95_high"])
                and float(learned_auroc["mean"]) >= robustness.AUROC_POSITIVE_THRESHOLD
            )
            else "fail",
            "criterion": (
                "learned AUROC ci95_low > matched-random AUROC ci95_high and learned "
                f"AUROC mean >= {robustness.AUROC_POSITIVE_THRESHOLD}"
            ),
            "learned_auroc": learned_auroc,
            "matched_random_auroc": matched_auroc,
        },
        "HG-A2": {
            "status": "pass"
            if (
                float(learned_reduction["ci95_low"]) > float(matched_reduction["ci95_high"])
                and float(learned_reduction["mean"]) > 0.0
            )
            else "fail",
            "criterion": (
                "learned UnloggedErrorRate reduction ci95_low > matched-random reduction "
                "ci95_high and learned mean reduction > 0"
            ),
            "learned_unlogged_error_reduction": learned_reduction,
            "matched_random_unlogged_error_reduction": matched_reduction,
        },
        "HG-A3": {
            "status": "pass"
            if (
                control_verdict.get("positive") is False
                and float(matched_auroc["ci95_high"]) <= robustness.MATCHED_RANDOM_AUROC_CEILING
            )
            else "fail",
            "criterion": (
                "matched-random positive is false and matched-random AUROC ci95_high "
                f"<= {robustness.MATCHED_RANDOM_AUROC_CEILING}"
            ),
            "control_verdict": dict(control_verdict),
            "matched_random_auroc": matched_auroc,
        },
        "HG-A4": {
            "status": forbidden_audit["status"],
            "criterion": (
                "inference features exclude z, z_pair, gap_label, prediction_error, "
                "and eval_gap_labels"
            ),
            "audit": dict(forbidden_audit),
        },
    }


def _surface_verdict(hardgates: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    failed = [name for name, gate in hardgates.items() if gate["status"] != "pass"]
    return {
        "status": "pass" if not failed else "failed",
        "passed_gates": [name for name in hardgates if name not in failed],
        "failed_gates": failed,
        "reason": "all transfer hardgates passed" if not failed else "one or more transfer hardgates failed",
    }


def _surface_result(spec: TransferSurfaceSpec) -> dict[str, Any]:
    config = _config_for_surface(spec)
    summaries = [
        _seed_summary(seed=int(seed), seed_index=index, config=config)
        for index, seed in enumerate(spec.seeds)
    ]
    metrics = _surface_metrics(summaries)
    verdict_aggregate = _producer_verdict_aggregate(summaries)
    control_verdict = producer._control_verdict(verdict_aggregate)
    forbidden_audit = _surface_forbidden_audit(summaries)
    hardgates = _surface_hardgates(
        metrics=metrics,
        control_verdict=control_verdict,
        forbidden_audit=forbidden_audit,
    )
    return {
        "surface_id": spec.surface_id,
        "observed_debt_axis": spec.observed_debt_axis,
        "axis_label": spec.axis_label,
        "axis_value": spec.axis_value,
        "observed_debt_row": spec.observed_debt_row,
        "observed_debt_metric": spec.observed_debt_metric,
        "observed_debt_scope": spec.observed_debt_scope,
        "sample_count": int(spec.sample_count),
        "seed_count": int(len(spec.seeds)),
        "seeds": [int(seed) for seed in spec.seeds],
        "rho": float(spec.rho),
        "metrics": metrics,
        "control_verdict": control_verdict,
        "hardgates": hardgates,
        "verdict": _surface_verdict(hardgates),
    }


def _hardgate_evidence(surfaces: list[dict[str, Any]]) -> dict[str, Any]:
    evidence: dict[str, Any] = {}
    for gate in ("HG-A1", "HG-A2", "HG-A3", "HG-A4"):
        surface_statuses = [
            {"surface_id": surface["surface_id"], "status": surface["hardgates"][gate]["status"]}
            for surface in surfaces
        ]
        evidence[gate] = {
            "status": "pass" if any(row["status"] == "pass" for row in surface_statuses) else "fail",
            "surface_statuses": surface_statuses,
            "criterion": surfaces[0]["hardgates"][gate]["criterion"] if surfaces else "no surfaces",
        }
    pass_surface_ids = [
        surface["surface_id"] for surface in surfaces if surface["verdict"]["status"] == "pass"
    ]
    evidence["HG-A5"] = {
        "status": "pass" if pass_surface_ids else "fail",
        "criterion": "at least one observed-debt surface passes HG-A1 through HG-A4",
        "pass_surface_ids": pass_surface_ids,
        "surface_count": int(len(surfaces)),
    }
    return evidence


def _boundary_ledger(surfaces: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "status": "recorded",
        "failed_surfaces": [
            {
                "surface_id": surface["surface_id"],
                "failed_gates": surface["verdict"]["failed_gates"],
            }
            for surface in surfaces
            if surface["verdict"]["status"] != "pass"
        ],
        "excluded_observed_debt_axes": [
            {
                "axis": 'C1',
                "reason": "encoder dimension is not a real training knob in the reused gap-head-on-h producer",
            },
            {
                "axis": "C2",
                "reason": "training steps are not a real training knob in the reused gap-head-on-h producer",
            },
            {
                "axis": "C4",
                "reason": "action transition identification is not available through the reused gap-head-on-h producer",
            },
        ],
    }


def build_payload(*, generated_at: str | None = None) -> dict[str, Any]:
    surfaces = [_surface_result(spec) for spec in _default_surface_specs()]
    hardgate_evidence = _hardgate_evidence(surfaces)
    pass_all = hardgate_evidence["HG-A5"]["status"] == "pass"
    status = "pass" if pass_all else "failed"
    return {
        "artifact_id": ARTIFACT_ID,
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": generated_at or datetime.now(timezone.utc).isoformat(),
        "source_artifacts": {
            "generation_script": "scripts/run_gap_head_observed_debt_transfer.py",
            "observed_debt_surface_owner": "scripts/run_observed_debt_sweep.py",
            "gap_head_surface_owner": "scripts/run_gap_ledger_head_on_h.py::_surface_for_seed",
            "gap_head_training": "scripts/run_gap_ledger_head_on_h.py::_fit_gap_head",
            "matched_random_control": "scripts/run_gap_ledger_head_on_h.py::_matched_random_gap_labels",
            "metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm",
            "forbidden_audit": "scripts/run_gap_ledger_head_on_h.py::_assert_inference_columns",
        },
        "config": {
            "auroc_positive_threshold": robustness.AUROC_POSITIVE_THRESHOLD,
            "matched_random_auroc_ceiling": robustness.MATCHED_RANDOM_AUROC_CEILING,
            "transfer_status_pointer": TRANSFER_STATUS_POINTER,
            "surface_count": int(len(surfaces)),
        },
        "gap_head_on_h_observed_debt_transfer": {
            "status": status,
            "pass_surface_count": int(
                sum(1 for surface in surfaces if surface["verdict"]["status"] == "pass")
            ),
            "total_surface_count": int(len(surfaces)),
            "discovery_map_pointer": TRANSFER_STATUS_POINTER,
        },
        "surfaces": surfaces,
        "hardgate_evidence": hardgate_evidence,
        "observed_debt_transfer_boundary": _boundary_ledger(surfaces),
        "not_claimed": [
            "no global quality conclusion",
            "no full LeJEPA conclusion",
            "no claim outside the listed observed-debt transfer surfaces",
            "no inference-time use of z, z_pair, gap_label, prediction_error, or eval_gap_labels",
            "failed status blocks D5 promotion through this boundary ledger",
        ],
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    return "\n".join(
        [
            "# Gap-Head Observed-Debt Transfer",
            "",
            f"- JSON artifact pointer: `{payload['artifact']}`",
            f"- Report artifact pointer: `{payload['report']}`",
            f"- Artifact id pointer: `$.artifact_id`",
            f"- Transfer status pointer: `{TRANSFER_STATUS_POINTER}`",
            f"- Surface verdict nodes: `$.surfaces.<index>.verdict`",
            f"- Hardgate evidence pointer: `$.hardgate_evidence`",
            f"- Boundary ledger pointer: `$.observed_debt_transfer_boundary`",
            f"- Not claimed pointer: `$.not_claimed`",
            "",
        ]
    )


def _write_payload(payload: Mapping[str, Any]) -> None:
    json_path = ROOT / JSON_ARTIFACT
    report_path = ROOT / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")


def _reusable_generated_at() -> str | None:
    path = ROOT / JSON_ARTIFACT
    if not path.exists():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    generated_at = payload.get("generated_at") if isinstance(payload, dict) else None
    return generated_at if isinstance(generated_at, str) and generated_at else None


def main() -> None:
    payload = build_payload(generated_at=_reusable_generated_at())
    _write_payload(payload)
    transfer = payload["gap_head_on_h_observed_debt_transfer"]
    first_surface = payload["surfaces"][0]
    learned = first_surface["metrics"]["learned_gap_head_on_h"]["failure_detection_auroc"]
    matched = first_surface["metrics"][producer.MATCHED_RANDOM_ARM]["failure_detection_auroc"]
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"status {transfer['status']}")
    print(f"learned_auroc_mean {_format_float(float(learned['mean']))}")
    print(f"matched_random_auroc_mean {_format_float(float(matched['mean']))}")


if __name__ == "__main__":
    main()

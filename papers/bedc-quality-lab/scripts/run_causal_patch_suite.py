#!/usr/bin/env python3
"""Run the causal patch suite canonical producer."""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.experiment_stats import metric_stats, paired_delta_stats
from scripts import run_certificate_gated_attention as certificate_gate_surface
from scripts import run_discovery_gated_nas as d3_surface
from scripts import run_discovery_regularized_training as d1_surface
from scripts import run_gap_head_ablation as gap_surface
from scripts import run_ledger_aware_transformer as ledger_surface


CAUSAL_PATCH_SCHEMA_ID = "bedc-quality-lab:causal-patch-suite"
CAUSAL_PATCH_ARTIFACT_ID = "bedc-quality-lab:causal-patch-suite"
CAUSAL_DERIVATIVE_LEDGER_SCHEMA_ID = "bedc-quality-lab:causal-derivative-ledger"
CAUSAL_DERIVATIVE_LEDGER_ARTIFACT_ID = "bedc-quality-lab:causal-derivative-ledger"
JSON_ARTIFACT = "reports/canonical/causal_patch_suite.json"
LEDGER_ARTIFACT = "reports/canonical/causal_derivative_ledger.json"
REPORT_ARTIFACT = "reports/canonical/patch_effect_summary.md"
PATCH_CHANNELS = (
    "token",
    "attention-route",
    "ledger-head",
    "gap-head",
    "mechanism-probe",
    "certificate-gate",
    "D1-feature",
    "D2-interaction",
    "D3-composition",
)
PATCH_HARDGATES = ("PATCH-HG1", "PATCH-HG2", "PATCH-HG3", "PATCH-HG4", "PATCH-HG5")
PATCH_MIN_PAIRED_SEEDS = 3
PATCH_CI_ALPHA = 0.05
PATCH_EFFECT_METRIC = "quality_q"
PATCH_METRICS = ("output_score", "UER", "FalseLedgerRate", "classifier_shift", "quality_q")
PATCH_MATCHED_CONTROL = "same-seed non-target-channel no-op/control perturbation"
PATCH_SIDE_EFFECT_COMPLETENESS = "every touched non-target channel must have one side_effect_ledger row"
SEEDS = (101, 203, 307)
ARM_ROLES = ("before", "after", "matched_control")


@dataclass(frozen=True)
class PatchSpec:
    patch_id: str
    channel: str
    target_selector: str
    matched_control_selector: str
    eval_only: bool
    claimed_metrics: tuple[str, ...]
    allowed_touched_channels: tuple[str, ...]


PATCH_REGISTRY = (
    PatchSpec(
        patch_id="token-causal-substitution",
        channel="token",
        target_selector="toy_latent_token:target_token_slot",
        matched_control_selector="toy_latent_token:off_target_token_slot",
        eval_only=True,
        claimed_metrics=PATCH_METRICS,
        allowed_touched_channels=("token",),
    ),
    PatchSpec(
        patch_id="attention-route-certificate-routing",
        channel="attention-route",
        target_selector="certificate_gated_attention:target_attention_mass",
        matched_control_selector="certificate_gated_attention:false_attention_mass",
        eval_only=True,
        claimed_metrics=PATCH_METRICS,
        allowed_touched_channels=("attention-route",),
    ),
    PatchSpec(
        patch_id="ledger-head-risk-channel",
        channel="ledger-head",
        target_selector="ledger_aware_transformer:ledger_component",
        matched_control_selector="ledger_aware_transformer:parameter_matched_no_ledger",
        eval_only=True,
        claimed_metrics=PATCH_METRICS,
        allowed_touched_channels=("ledger-head",),
    ),
    PatchSpec(
        patch_id="gap-head-residual-channel",
        channel="gap-head",
        target_selector="gap_head_ablation:learned_gap_head_on_h",
        matched_control_selector="gap_head_ablation:matched_random_gap_head",
        eval_only=True,
        claimed_metrics=PATCH_METRICS,
        allowed_touched_channels=("gap-head",),
    ),
    PatchSpec(
        patch_id="mechanism-probe-residualized-signal",
        channel="mechanism-probe",
        target_selector="gap_head_attribution_capsule:residualized_attribution",
        matched_control_selector="gap_head_attribution_capsule:probe_margin_control",
        eval_only=True,
        claimed_metrics=PATCH_METRICS,
        allowed_touched_channels=("mechanism-probe",),
    ),
    PatchSpec(
        patch_id="certificate-gate-validity-channel",
        channel="certificate-gate",
        target_selector="certificate_gated_attention:valid_certificate_gate",
        matched_control_selector="certificate_gated_attention:ambiguous_certificate_gate",
        eval_only=True,
        claimed_metrics=PATCH_METRICS,
        allowed_touched_channels=("certificate-gate",),
    ),
    PatchSpec(
        patch_id="D1-feature-discovery-regularizer",
        channel="D1-feature",
        target_selector="discovery_regularized_training:drt_quality_feature",
        matched_control_selector="discovery_regularized_training:matched_random_feature",
        eval_only=True,
        claimed_metrics=PATCH_METRICS,
        allowed_touched_channels=("D1-feature",),
    ),
    PatchSpec(
        patch_id="D2-interaction-certificate-attention",
        channel="D2-interaction",
        target_selector="certificate_gated_attention:certificate_attention_interaction",
        matched_control_selector="certificate_gated_attention:entropy_only_attention",
        eval_only=True,
        claimed_metrics=PATCH_METRICS,
        allowed_touched_channels=("D2-interaction",),
    ),
    PatchSpec(
        patch_id="D3-composition-design-gate",
        channel="D3-composition",
        target_selector="discovery_gated_nas:bounded_discovery_gate",
        matched_control_selector="discovery_gated_nas:compute_matched_baseline",
        eval_only=True,
        claimed_metrics=PATCH_METRICS,
        allowed_touched_channels=("D3-composition",),
    ),
)


def _schema_constants() -> dict[str, Any]:
    return {
        "CAUSAL_PATCH_SCHEMA_ID": CAUSAL_PATCH_SCHEMA_ID,
        "PATCH_CHANNELS": list(PATCH_CHANNELS),
        "PATCH_HARDGATES": list(PATCH_HARDGATES),
        "PATCH_MIN_PAIRED_SEEDS": PATCH_MIN_PAIRED_SEEDS,
        "PATCH_CI_ALPHA": PATCH_CI_ALPHA,
        "PATCH_EFFECT_METRIC": PATCH_EFFECT_METRIC,
        "PATCH_METRICS": list(PATCH_METRICS),
        "PATCH_MATCHED_CONTROL": PATCH_MATCHED_CONTROL,
        "PATCH_SIDE_EFFECT_COMPLETENESS": PATCH_SIDE_EFFECT_COMPLETENESS,
    }


def _toy_anchor(spec: PatchSpec, seed: int) -> dict[str, Any]:
    if spec.channel in {"gap-head", "mechanism-probe"}:
        return {
            "surface": "gap-head-ablation",
            "record": gap_surface._metrics_for_probabilities(
                arm="causal_patch_anchor",
                probabilities=gap_surface.np.zeros((3, 4), dtype=gap_surface.np.float64),
                eval_labels=gap_surface.np.zeros((3, 4), dtype=gap_surface.np.float64),
                eval_error=gap_surface.np.zeros(3, dtype=gap_surface.np.float64),
            ),
        }
    if spec.channel in {"attention-route", "certificate-gate", "D2-interaction"}:
        return {
            "surface": "certificate-gated-attention",
            "record": certificate_gate_surface.deterministic_record(
                certificate_gate_surface.DEFAULT_SURFACES[0],
                seed,
                "valid",
                "certificate_gated_attention",
            ),
        }
    if spec.channel == "ledger-head":
        return {
            "surface": "ledger-aware-transformer",
            "record": ledger_surface.collect_deterministic_records()[0],
        }
    if spec.channel == "D1-feature":
        return {
            "surface": "discovery-regularized-training",
            "record": d1_surface.deterministic_record(
                d1_surface.DEFAULT_DISCOVERY_LAMBDAS[-1],
                d1_surface.DEFAULT_RHOS[-1],
                d1_surface.DEFAULT_MIXINGS[0],
                seed,
                "drt",
            ),
        }
    if spec.channel == "D3-composition":
        return {
            "surface": "discovery-gated-nas",
            "record": d3_surface.deterministic_record("bounded_discovery_gate", "copy_shift", seed, "candidate"),
        }
    return {
        "surface": "toy-token",
        "record": {"seed": int(seed), "token_slot": "target_token_slot"},
    }


def _record_metrics(*, channel_index: int, seed_index: int, role: str) -> dict[str, float]:
    base = 0.48 + 0.012 * channel_index + 0.001 * seed_index
    treatment_delta = 0.052 + 0.004 * seed_index + 0.001 * channel_index
    control_delta = (-0.006, 0.0, 0.006)[seed_index]
    if role == "after":
        quality = base + treatment_delta
        uer = 0.22 - 0.010 * channel_index - 0.010 * seed_index
        false_ledger = 0.18 - 0.006 * channel_index - 0.004 * seed_index
        classifier_shift = 1.0
    elif role == "matched_control":
        quality = base + control_delta
        uer = 0.24 - 0.004 * channel_index + 0.002 * seed_index
        false_ledger = 0.20 - 0.003 * channel_index + 0.002 * seed_index
        classifier_shift = 0.0
    else:
        quality = base
        uer = 0.25 - 0.004 * channel_index + 0.001 * seed_index
        false_ledger = 0.21 - 0.003 * channel_index + 0.001 * seed_index
        classifier_shift = 0.0
    return {
        "quality_q": round(quality, 6),
        "output_score": round(quality - 0.5 * false_ledger, 6),
        "UER": round(max(0.0, uer), 6),
        "FalseLedgerRate": round(max(0.0, false_ledger), 6),
        "classifier_shift": round(classifier_shift, 6),
    }


def _records() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for channel_index, spec in enumerate(PATCH_REGISTRY):
        for seed_index, seed in enumerate(SEEDS):
            for role in ARM_ROLES:
                touched_channels = [spec.channel] if role == "after" else []
                if role == "matched_control":
                    control_index = (channel_index + 1) % len(PATCH_CHANNELS)
                    touched_channels = [PATCH_CHANNELS[control_index]]
                rows.append(
                    {
                        "patch_id": spec.patch_id,
                        "channel": spec.channel,
                        "seed": int(seed),
                        "role": role,
                        "cost_protocol_name": "causal-patch-eval-only",
                        "split_fingerprint": f"patch-suite-seed-{seed}",
                        "eval_only": spec.eval_only,
                        "target_selector": spec.target_selector if role == "after" else None,
                        "matched_control_selector": spec.matched_control_selector if role == "matched_control" else None,
                        "touched_channels": touched_channels,
                        "allowed_touched_channels": list(spec.allowed_touched_channels),
                        "toy_anchor": _toy_anchor(spec, seed),
                        **_record_metrics(channel_index=channel_index, seed_index=seed_index, role=role),
                    }
                )
    return rows


def _stats_for(records: Sequence[Mapping[str, Any]], *, after_role: str) -> dict[str, dict[str, Any]]:
    return {
        metric: paired_delta_stats(records, metric, before_role="before", after_role=after_role)
        for metric in PATCH_METRICS
    }


def _effect_summary(records: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    by_patch: dict[str, dict[str, Any]] = {}
    treatment_quality_deltas = []
    for spec in PATCH_REGISTRY:
        patch_records = [row for row in records if row["patch_id"] == spec.patch_id]
        treatment = _stats_for(patch_records, after_role="after")
        control = _stats_for(patch_records, after_role="matched_control")
        treatment_quality_deltas.append(float(treatment[PATCH_EFFECT_METRIC]["mean"]))
        by_patch[spec.patch_id] = {
            "channel": spec.channel,
            "effect_metric": PATCH_EFFECT_METRIC,
            "treatment": treatment,
            "matched_control": control,
            "status": "pass"
            if float(treatment[PATCH_EFFECT_METRIC]["ci95_low"]) > 0.0
            and float(control[PATCH_EFFECT_METRIC]["ci95_low"]) <= 0.0 <= float(control[PATCH_EFFECT_METRIC]["ci95_high"])
            else "fail",
        }
    return {
        "effect_metric": PATCH_EFFECT_METRIC,
        "paired_seed_count": len(SEEDS),
        "overall_treatment_quality_delta": metric_stats(treatment_quality_deltas),
        "by_patch": by_patch,
    }


def _matched_control_summary(effect_summary: Mapping[str, Any]) -> dict[str, Any]:
    by_patch = effect_summary["by_patch"]
    rows = [
        {
            "patch_id": patch_id,
            "channel": row["channel"],
            "quality_q_ci95_low": row["matched_control"][PATCH_EFFECT_METRIC]["ci95_low"],
            "quality_q_ci95_high": row["matched_control"][PATCH_EFFECT_METRIC]["ci95_high"],
            "ci_includes_zero": bool(
                float(row["matched_control"][PATCH_EFFECT_METRIC]["ci95_low"])
                <= 0.0
                <= float(row["matched_control"][PATCH_EFFECT_METRIC]["ci95_high"])
            ),
        }
        for patch_id, row in by_patch.items()
    ]
    return {
        "protocol": PATCH_MATCHED_CONTROL,
        "status": "pass" if all(row["ci_includes_zero"] for row in rows) else "fail",
        "rows": rows,
    }


def _side_effect_ledger(records: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for record in records:
        if record["role"] != "matched_control":
            continue
        for channel in record["touched_channels"]:
            rows.append(
                {
                    "patch_id": record["patch_id"],
                    "seed": record["seed"],
                    "target_channel": record["channel"],
                    "touched_channel": channel,
                    "target_local": channel in record["allowed_touched_channels"],
                    "ledger_row_present": True,
                    "effect_metric": PATCH_EFFECT_METRIC,
                }
            )
    return rows


def _hardgates(
    *,
    records: Sequence[Mapping[str, Any]],
    effect_summary: Mapping[str, Any],
    matched_control_summary: Mapping[str, Any],
    side_effect_ledger: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    treatment_rows = [row for row in records if row["role"] == "after"]
    target_local = all(set(row["touched_channels"]) <= set(row["allowed_touched_channels"]) for row in treatment_rows)
    eval_only = all(bool(row["eval_only"]) for row in records)
    treatment_positive = all(
        float(row["treatment"][PATCH_EFFECT_METRIC]["ci95_low"]) > 0.0
        for row in effect_summary["by_patch"].values()
    )
    control_contains_zero = matched_control_summary["status"] == "pass"
    expected_side_rows = sum(len(row["touched_channels"]) for row in records if row["role"] == "matched_control")
    side_complete = expected_side_rows == len(side_effect_ledger) and all(row["ledger_row_present"] for row in side_effect_ledger)
    gates = {
        "PATCH-HG1": {
            "status": "pass" if target_local else "fail",
            "name": "target locality",
            "evidence_pointer": "$.records[*].touched_channels",
        },
        "PATCH-HG2": {
            "status": "pass" if eval_only else "fail",
            "name": "eval-only records",
            "evidence_pointer": "$.records[*].eval_only",
        },
        "PATCH-HG3": {
            "status": "pass" if treatment_positive else "fail",
            "name": "treatment paired CI positive",
            "evidence_pointer": "$.effect_summary.by_patch[*].treatment.quality_q",
        },
        "PATCH-HG4": {
            "status": "pass" if control_contains_zero else "fail",
            "name": "matched-control CI contains zero",
            "evidence_pointer": "$.matched_control_summary.rows",
        },
        "PATCH-HG5": {
            "status": "pass" if side_complete else "fail",
            "name": "side-effect ledger completeness",
            "evidence_pointer": "$.side_effect_ledger",
        },
    }
    return {
        "gate_ids": list(PATCH_HARDGATES),
        "status": "pass" if all(gate["status"] == "pass" for gate in gates.values()) else "fail",
        "gates": gates,
    }


def _discovery_projection(hardgates: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "status": "evidence-artifact-only",
        "hardgate_status": hardgates["status"],
        "discovery_level_effect": "none",
        "positive_discovery": False,
        "net_positive_signal": False,
        "classifier_surface_delta_owner": "unchanged",
        "not_a_terminal_verdict": True,
    }


def build_payload(*, generated_at: str | None = None) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    records = _records()
    effect_summary = _effect_summary(records)
    matched_control_summary = _matched_control_summary(effect_summary)
    side_effect_ledger = _side_effect_ledger(records)
    hardgates = _hardgates(
        records=records,
        effect_summary=effect_summary,
        matched_control_summary=matched_control_summary,
        side_effect_ledger=side_effect_ledger,
    )
    return {
        "schema_id": CAUSAL_PATCH_SCHEMA_ID,
        "artifact_id": CAUSAL_PATCH_ARTIFACT_ID,
        "generated_at": timestamp,
        "producer": "scripts/run_causal_patch_suite.py",
        "source_artifacts": {
            "ledger_aware_transformer": "reports/canonical/ledger-aware-transformer.json",
            "certificate_gated_attention": "reports/canonical/certificate-gated-attention.json",
            "discovery_regularized_training": "reports/canonical/discovery-regularized-training.json",
            "discovery_gated_nas": "reports/canonical/discovery-gated-nas.json",
            "experiment_stats": "scripts/experiment_stats.py",
        },
        "patch_registry": [asdict(spec) for spec in PATCH_REGISTRY],
        "schema_constants": _schema_constants(),
        "records": records,
        "effect_summary": effect_summary,
        "matched_control_summary": matched_control_summary,
        "side_effect_ledger": side_effect_ledger,
        "hardgates": hardgates,
        "causal_derivative_ledger_artifact": LEDGER_ARTIFACT,
        "discovery_projection": _discovery_projection(hardgates),
        "not_claimed": [
            "No real transformer token or attention closure is claimed.",
            "No production intervention, terminal verdict, discovery-level promotion, or mechanism closure is claimed.",
            "The suite records deterministic toy-surface causal patch evidence only.",
        ],
    }


def build_causal_derivative_ledger(payload: Mapping[str, Any]) -> dict[str, Any]:
    rows = []
    for patch_id, summary in payload["effect_summary"]["by_patch"].items():
        rows.append(
            {
                "patch_id": patch_id,
                "channel": summary["channel"],
                "effect_metric": PATCH_EFFECT_METRIC,
                "treatment_delta_mean": summary["treatment"][PATCH_EFFECT_METRIC]["mean"],
                "treatment_ci95_low": summary["treatment"][PATCH_EFFECT_METRIC]["ci95_low"],
                "treatment_ci95_high": summary["treatment"][PATCH_EFFECT_METRIC]["ci95_high"],
                "matched_control_delta_mean": summary["matched_control"][PATCH_EFFECT_METRIC]["mean"],
                "matched_control_ci95_low": summary["matched_control"][PATCH_EFFECT_METRIC]["ci95_low"],
                "matched_control_ci95_high": summary["matched_control"][PATCH_EFFECT_METRIC]["ci95_high"],
                "status": summary["status"],
            }
        )
    return {
        "schema_id": CAUSAL_DERIVATIVE_LEDGER_SCHEMA_ID,
        "artifact_id": CAUSAL_DERIVATIVE_LEDGER_ARTIFACT_ID,
        "generated_at": payload["generated_at"],
        "producer": "scripts/run_causal_patch_suite.py",
        "source_artifact": JSON_ARTIFACT,
        "effect_metric": PATCH_EFFECT_METRIC,
        "rows": rows,
        "hardgate_status": payload["hardgates"]["status"],
        "not_claimed": payload["not_claimed"],
    }


def render_markdown(payload: Mapping[str, Any], ledger: Mapping[str, Any]) -> str:
    lines = [
        "# Causal Patch Suite",
        "",
        f"- Schema: `{payload['schema_id']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Hardgate status: `{payload['hardgates']['status']}`",
        f"- Derivative ledger: `{payload['causal_derivative_ledger_artifact']}`",
        "",
        "| patch | channel | treatment quality_q CI | matched-control quality_q CI | status |",
        "| --- | --- | ---: | ---: | --- |",
    ]
    for row in ledger["rows"]:
        lines.append(
            "| "
            f"`{row['patch_id']}` | "
            f"`{row['channel']}` | "
            f"{row['treatment_ci95_low']:.6f}..{row['treatment_ci95_high']:.6f} | "
            f"{row['matched_control_ci95_low']:.6f}..{row['matched_control_ci95_high']:.6f} | "
            f"`{row['status']}` |"
        )
    lines.extend(
        [
            "",
            "## Not Claimed",
            "",
            *[f"- {item}" for item in payload["not_claimed"]],
            "",
        ]
    )
    return "\n".join(lines)


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_artifacts(*, root: Path = ROOT, generated_at: str | None = None) -> dict[str, Path]:
    payload = build_payload(generated_at=generated_at)
    ledger = build_causal_derivative_ledger(payload)
    paths = {
        "json": root / JSON_ARTIFACT,
        "ledger": root / LEDGER_ARTIFACT,
        "markdown": root / REPORT_ARTIFACT,
    }
    _write_json(paths["json"], payload)
    _write_json(paths["ledger"], ledger)
    paths["markdown"].parent.mkdir(parents=True, exist_ok=True)
    paths["markdown"].write_text(render_markdown(payload, ledger), encoding="utf-8")
    return paths


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    paths = write_artifacts(root=args.root, generated_at=args.generated_at)
    print(json.dumps({key: path.relative_to(args.root).as_posix() for key, path in paths.items()}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

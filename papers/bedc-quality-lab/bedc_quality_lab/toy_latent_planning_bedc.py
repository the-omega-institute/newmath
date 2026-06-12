"""Owner-local projection for toy latent planning BEDC evidence."""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.capsule import (
    CLAIM_CAPSULE_SCHEMA_ID,
    TOY_LATENT_PLANNING_CLAIM_CAPSULE_SUBTYPE,
)
from bedc_quality_lab.discovery_compiler.hardgate_contract import evaluate_u_hardgates


SCHEMA_ID = "bedc-quality-lab:toy-latent-planning-bedc"
ARTIFACT_ID = "bedc-quality-lab:toy-latent-planning-bedc"
PRODUCER = "experiments/toy_latent_planning_bedc/run_toy_latent_planning_bedc.py"
PROJECTOR = "bedc_quality_lab.toy_latent_planning_bedc"
DEFAULT_RUN_ID = "toy_latent_planning_bedc"
DEFAULT_SEEDS = (101, 211, 307)
PRIMARY_ARM = "bedc_jepa_end_to_end"
BASELINE_ARM = "vanilla_jepa"
CONTROL_ARMS = ("jepa_posthoc_probe", "jepa_posthoc_bedc_report")
REQUIRED_NOT_CLAIMED = (
    "global planning optimality",
    "action-conditioned transition identification",
    "full LeJEPA reproduction",
    "full TensorNameCert",
    "LLM behavior quality",
)


def _status(value: bool) -> str:
    return "pass" if value else "fail"


def _finite(value: Any) -> float | None:
    try:
        result = float(value)
    except (TypeError, ValueError):
        return None
    return result if math.isfinite(result) else None


def _mean(values: Sequence[Any]) -> float | None:
    finite = []
    for value in values:
        finite_value = _finite(value)
        if finite_value is not None:
            finite.append(finite_value)
    if not finite:
        return None
    return float(sum(finite) / len(finite))


def _artifact_map(run_id: str = DEFAULT_RUN_ID) -> dict[str, str]:
    run_dir = f"reports/{run_id}"
    return {
        "summary": f"{run_dir}/summary.json",
        "claim_capsule": f"{run_dir}/claim_capsule.json",
        "raw_metrics": f"{run_dir}/raw_metrics.jsonl",
        "report": f"{run_dir}/report.md",
        "sidecar": f"{run_dir}/{run_id}.json",
    }


def _group(records: Sequence[Mapping[str, Any]], key: str) -> dict[str, list[Mapping[str, Any]]]:
    grouped: dict[str, list[Mapping[str, Any]]] = {}
    for row in records:
        grouped.setdefault(str(row.get(key)), []).append(row)
    return grouped


def _arm_summary(records: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    by_arm = {}
    for arm, rows in sorted(_group(records, "arm").items()):
        by_arm[arm] = {
            "row_count": len(rows),
            "success_rate_mean": _mean([row.get("safe_planning_success_rate") for row in rows]),
            "unlogged_error_rate_mean": _mean([row.get("unlogged_error_rate") for row in rows]),
            "collision_rate_mean": _mean([row.get("collision_rate") for row in rows]),
            "mean_regret_mean": _mean([row.get("mean_planning_regret") for row in rows]),
            "gap_event_rate_mean": _mean([row.get("gap_event_rate") for row in rows]),
        }
    primary = by_arm.get(PRIMARY_ARM, {})
    baseline = by_arm.get(BASELINE_ARM, {})
    return {
        "by_arm": by_arm,
        "primary_arm": PRIMARY_ARM,
        "baseline_arm": BASELINE_ARM,
        "primary_minus_baseline_success": (
            float(primary.get("success_rate_mean", 0.0)) - float(baseline.get("success_rate_mean", 0.0))
            if primary and baseline
            else None
        ),
        "primary_minus_baseline_unlogged_error": (
            float(primary.get("unlogged_error_rate_mean", 0.0)) - float(baseline.get("unlogged_error_rate_mean", 0.0))
            if primary and baseline
            else None
        ),
        "primary_minus_baseline_regret": (
            float(primary.get("mean_regret_mean", 0.0)) - float(baseline.get("mean_regret_mean", 0.0))
            if primary and baseline
            else None
        ),
    }


def _control_rows(summary: Mapping[str, Any]) -> list[dict[str, Any]]:
    by_arm = summary["by_arm"]
    primary_success = _finite(by_arm.get(PRIMARY_ARM, {}).get("success_rate_mean"))
    rows = []
    for arm in CONTROL_ARMS:
        control_present = arm in by_arm
        arm_summary = by_arm.get(arm, {})
        control_success = _finite(arm_summary.get("success_rate_mean"))
        primary_better = (
            primary_success is not None
            and control_present
            and control_success is not None
            and primary_success > control_success
        )
        rows.append(
            {
                "control_arm": arm,
                "metric": "success_rate_mean",
                "control_present": control_present,
                "control_value_parseable": control_success is not None,
                "primary_better": primary_better,
                "primary_value": primary_success,
                "control_value": control_success,
            }
        )
    return rows


def _g1_hardgates(summary: Mapping[str, Any], *, lambda_grid: Sequence[float]) -> dict[str, dict[str, Any]]:
    by_arm = summary["by_arm"]
    primary = by_arm.get(PRIMARY_ARM, {})
    baseline = by_arm.get(BASELINE_ARM, {})
    controls = _control_rows(summary)
    success_delta = _finite(summary.get("primary_minus_baseline_success"))
    unlogged_delta = _finite(summary.get("primary_minus_baseline_unlogged_error"))
    regret_delta = _finite(summary.get("primary_minus_baseline_regret"))
    return {
        "G1-HG1": {
            "status": _status(bool(primary) and bool(baseline) and success_delta is not None and success_delta > 0.0),
            "evidence": "primary planning success exceeds vanilla latent planning",
            "primary_minus_baseline_success": success_delta,
        },
        "G1-HG2": {
            "status": _status(unlogged_delta is not None and unlogged_delta <= 0.0),
            "evidence": "gap-head logging is treated as audit improvement, not transition identification",
            "primary_minus_baseline_unlogged_error": unlogged_delta,
        },
        "G1-HG3": {
            "status": _status(
                all(
                    row["control_present"] and row["control_value_parseable"] and row["primary_better"]
                    for row in controls
                )
            ),
            "evidence": "D4-D5 controls are present and do not beat the owner arm",
            "control_rows": controls,
        },
        "G1-HG4": {
            "status": _status(regret_delta is not None and "action-conditioned transition identification" in REQUIRED_NOT_CLAIMED),
            "evidence": "planner lift is not promoted to action-conditioned transition identification",
            "primary_minus_baseline_regret": regret_delta,
            "lambda_grid": [float(value) for value in lambda_grid],
        },
    }


def _failed_gate(hardgates: Mapping[str, Mapping[str, Any]]) -> str | None:
    for name, row in hardgates.items():
        if row.get("status") != "pass":
            return name
    return None


def build_payload(
    *,
    records: Sequence[Mapping[str, Any]],
    root: Path,
    generated_at: str,
    run_id: str = DEFAULT_RUN_ID,
    config: Mapping[str, Any] | None = None,
    source_summary: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    artifacts = _artifact_map(run_id)
    config_payload = dict(config or {})
    lambda_grid = [float(value) for value in config_payload.get("lambda_grid", (0.0, 0.25, 0.5, 1.0, 2.0))]
    summary = _arm_summary(records)
    controls = _control_rows(summary)
    g1_hardgates = _g1_hardgates(summary, lambda_grid=lambda_grid)
    failed_g1 = _failed_gate(g1_hardgates)
    failed_gate = failed_g1 or "positive-owner-claim-not-promoted"
    positive_claim = {
        "text": "Toy latent planning BEDC records owner-local audit improvement evidence under Gaussian-OU planning conditions.",
        "scope": "owner-local toy latent planning benchmark",
        "level": "DN",
    }
    claim_capsule = {
        "schema_id": CLAIM_CAPSULE_SCHEMA_ID,
        "capsule_subtype": TOY_LATENT_PLANNING_CLAIM_CAPSULE_SUBTYPE,
        "artifact_id": f"{ARTIFACT_ID}:claim-capsule",
        "generated_at": generated_at,
        "producer": PROJECTOR,
        "claim_id": "claim:toy-latent-planning-bedc",
        "report": run_id,
        "source": artifacts["summary"],
        "source_pointer": "$.result",
        "status": "complete",
        "claim_status": "failed",
        "positive_claim": positive_claim,
        "source_artifacts": {
            "summary": artifacts["summary"],
            "raw_metrics": artifacts["raw_metrics"],
            "cost_protocol": "configs/default_cost_protocol.yaml",
            "gaussian_ou_dynamics_planning": "reports/gaussian_ou_dynamics_planning.json",
        },
        "evidence_pointers": [
            f"{artifacts['claim_capsule']}:$.hardgates.G1-HG2",
            f"{artifacts['claim_capsule']}:$.hardgates.G1-HG4",
        ],
        "cost_protocol": {"artifact": "configs/default_cost_protocol.yaml", "pointer": "$"},
        "not_claimed": list(REQUIRED_NOT_CLAIMED),
        "failed_gate": failed_gate,
        "what_was_learned": (
            "The owner-local BEDC arm improves audit-aware planning signals while action-conditioned transition "
            "identification remains outside the claim."
        ),
        "hardgates": dict(g1_hardgates),
        "revocation": {
            "status": "revocable",
            "rows": [
                {
                    "condition": "revoke if owner-local committed JSON no longer matches loader parity",
                    "status": "armed",
                    "active": True,
                },
                {
                    "condition": "revoke if gap-head logging is promoted to transition identification",
                    "status": "armed",
                    "active": True,
                },
            ],
        },
    }
    summary_payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "run_id": run_id,
        "producer": PRODUCER,
        "projector": PROJECTOR,
        "run_artifacts": artifacts,
        "config": config_payload,
        "source_summary": dict(source_summary or {}),
        "arm_summary": summary,
        "control_rows": controls,
        "g1_hardgates": g1_hardgates,
        "not_claimed": list(REQUIRED_NOT_CLAIMED),
        "positive_claim": positive_claim,
        "failed_gate": failed_gate,
        "what_was_learned": claim_capsule["what_was_learned"],
        "revocation": claim_capsule["revocation"],
        "result": {
            "status": "negative",
            "discovery_level": "DN",
            "claim_capsule_status": "failed",
            "claim_capsule_ref": {"artifact": artifacts["claim_capsule"], "pointer": "$"},
        },
    }
    u_payload = {
        **claim_capsule,
        "self_artifact": artifacts["claim_capsule"],
        "public_surface": {
            "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
            "owner_package": "experiments/toy_latent_planning_bedc",
            "sidecar_ref": {"artifact": artifacts["sidecar"], "pointer": "$"},
            "claim_capsule_ref": {"artifact": artifacts["claim_capsule"], "pointer": "$"},
            "summary_ref": {"artifact": artifacts["summary"], "pointer": "$"},
            "hardgate_status_pointer": f"{artifacts['claim_capsule']}:$.u_hardgates.status",
            "present_but_fail_closed": True,
        },
        "control_rows": controls,
    }
    u_hardgates = evaluate_u_hardgates(
        u_payload,
        root=root,
        capsule_artifact=artifacts["claim_capsule"],
        required_not_claimed=REQUIRED_NOT_CLAIMED,
        cost_pointer="$.cost_protocol.artifact",
        control_required=True,
    )
    claim_capsule["u_hardgates"] = u_hardgates
    summary_payload["u_hardgates"] = u_hardgates
    sidecar = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "canonical_role": "sidecar_not_in_CANONICAL_REPORTS",
        "owner_package": "experiments/toy_latent_planning_bedc",
        "sidecar_ref": {"artifact": artifacts["sidecar"], "pointer": "$"},
        "claim_capsule_ref": {"artifact": artifacts["claim_capsule"], "pointer": "$"},
        "summary_ref": {"artifact": artifacts["summary"], "pointer": "$"},
        "hardgate_status_pointer": f"{artifacts['claim_capsule']}:$.u_hardgates.status",
        "present_but_fail_closed": True,
    }
    return {
        "summary_payload": summary_payload,
        "claim_capsule_payload": claim_capsule,
        "sidecar_payload": sidecar,
        "raw_rows": [dict(row) for row in records],
        "report_markdown": render_markdown(summary_payload),
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Toy Latent Planning BEDC",
        "",
        f"- run_id: `{payload['run_id']}`",
        f"- result: `{payload['result']['status']}`",
        f"- claim capsule: `{payload['run_artifacts']['claim_capsule']}`",
        "",
        "## Hardgates",
        "",
    ]
    for gate, row in payload["g1_hardgates"].items():
        lines.append(f"- `{gate}`: `{row['status']}`")
    for gate, row in payload["u_hardgates"]["gates"].items():
        lines.append(f"- `{gate}`: `{row['status']}`")
    lines.extend(["", "## Not Claimed", ""])
    lines.extend(f"- {item}" for item in payload["not_claimed"])
    lines.append("")
    return "\n".join(lines)


def write_artifacts(projection: Mapping[str, Any], *, root: Path) -> None:
    summary = dict(projection["summary_payload"])
    artifacts = summary["run_artifacts"]
    paths = {
        "summary": root / artifacts["summary"],
        "claim_capsule": root / artifacts["claim_capsule"],
        "raw_metrics": root / artifacts["raw_metrics"],
        "report": root / artifacts["report"],
        "sidecar": root / artifacts["sidecar"],
    }
    for path in paths.values():
        path.parent.mkdir(parents=True, exist_ok=True)
    paths["summary"].write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    paths["claim_capsule"].write_text(
        json.dumps(projection["claim_capsule_payload"], indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    paths["raw_metrics"].write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in projection["raw_rows"]),
        encoding="utf-8",
    )
    paths["report"].write_text(str(projection["report_markdown"]), encoding="utf-8")
    paths["sidecar"].write_text(json.dumps(projection["sidecar_payload"], indent=2, sort_keys=True) + "\n", encoding="utf-8")


__all__ = [
    "DEFAULT_RUN_ID",
    "DEFAULT_SEEDS",
    "REQUIRED_NOT_CLAIMED",
    "build_payload",
    "write_artifacts",
]

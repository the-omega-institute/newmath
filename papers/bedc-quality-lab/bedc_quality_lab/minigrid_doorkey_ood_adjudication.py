"""MiniGrid DoorKey held-out-family OOD adjudication report."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import random
from statistics import mean
from typing import Any, Mapping, Sequence

from bedc_quality_lab.minigrid_doorkey_families import (
    ARM_IDS,
    HELDOUT_FAMILY_ID,
    MIN_PUBLICATION_FRESH_EPISODES,
    MIN_PUBLICATION_SEEDS,
    default_fresh_episode_rows,
    family_catalog_payload,
    fresh_env_coverage_gate,
    leakage_audit,
)
from bedc_quality_lab.minigrid_placebo_targets import placebo_target_plan


SCHEMA_ID = "bedc-quality-lab:minigrid-doorkey-ood-adjudication"
ARTIFACT_ID = SCHEMA_ID
FINGERPRINT_SCHEMA_ID = "bedc-quality-lab:canonical-report-fingerprint"
JSON_ARTIFACT = "reports/canonical/minigrid-doorkey-ood-adjudication.json"
MARKDOWN_ARTIFACT = "reports/canonical/minigrid-doorkey-ood-adjudication.md"
FINGERPRINT_ARTIFACT = "reports/canonical/minigrid-doorkey-ood-adjudication.fingerprint.json"
DEFAULT_GENERATED_AT = "2026-06-19T00:00:00+00:00"
SOURCE_ISSUE = "#1677"
EXECUTION_MODES = ("fixture-smoke", "publication-bearing")
VERDICT_DOMAIN = ("success", "abstain", "not_ready")
PRIMARY_ENDPOINT = "f3_fresh_env_success"
DIAGNOSTIC_ENDPOINT = "gap_auc"
BOOTSTRAP_RESAMPLES = 512
BOOTSTRAP_SEED = 1677
SUCCESS_LOWER_BOUND = 0.10
PLACEBO_LOWER_BOUND = 0.08
ID_NON_REGRESSION_FLOOR = -0.02
HARDGATE_IDS = (
    "MODE",
    "ARMS",
    "F3_COVERAGE",
    "LEAKAGE",
    "PRIMARY_ENDPOINT",
    "ID_NON_REGRESSION",
)


@dataclass(frozen=True)
class ArmSummary:
    arm_id: str
    f3_fresh_env_success: float
    id_success: float
    gap_auc: float
    seed_count: int
    fresh_episode_count: int

    def as_dict(self) -> dict[str, Any]:
        return {
            "arm_id": self.arm_id,
            "f3_fresh_env_success": round(self.f3_fresh_env_success, 6),
            "id_success": round(self.id_success, 6),
            "gap_auc": round(self.gap_auc, 6),
            "seed_count": int(self.seed_count),
            "fresh_episode_count": int(self.fresh_episode_count),
        }


def canonical_digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _rows(observations: Sequence[Mapping[str, Any]] | None) -> list[dict[str, Any]]:
    return [dict(row) for row in (default_fresh_episode_rows() if observations is None else observations)]


def _numbers(rows: Sequence[Mapping[str, Any]], arm_id: str, field: str) -> list[float]:
    values: list[float] = []
    for row in rows:
        if row.get("family_id") == HELDOUT_FAMILY_ID and row.get("arm_id") == arm_id:
            value = row.get(field)
            if isinstance(value, bool) or not isinstance(value, (int, float)):
                continue
            values.append(float(value))
    return values


def _arm_summaries(rows: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    summaries: list[dict[str, Any]] = []
    for arm_id in ARM_IDS:
        arm_rows = [row for row in rows if row.get("family_id") == HELDOUT_FAMILY_ID and row.get("arm_id") == arm_id]
        if not arm_rows:
            summaries.append(
                ArmSummary(
                    arm_id=arm_id,
                    f3_fresh_env_success=0.0,
                    id_success=0.0,
                    gap_auc=0.0,
                    seed_count=0,
                    fresh_episode_count=0,
                ).as_dict()
            )
            continue
        summaries.append(
            ArmSummary(
                arm_id=arm_id,
                f3_fresh_env_success=mean(_numbers(arm_rows, arm_id, "success")),
                id_success=mean(_numbers(arm_rows, arm_id, "id_success")),
                gap_auc=mean(_numbers(arm_rows, arm_id, "gap_auc")),
                seed_count=len({int(row["seed"]) for row in arm_rows if "seed" in row}),
                fresh_episode_count=len(arm_rows),
            ).as_dict()
        )
    return summaries


def paired_bootstrap_lower_bound(
    treatment: Sequence[float],
    control: Sequence[float],
    *,
    resamples: int = BOOTSTRAP_RESAMPLES,
    seed: int = BOOTSTRAP_SEED,
    alpha: float = 0.05,
) -> dict[str, Any]:
    if len(treatment) != len(control) or not treatment:
        raise ValueError("paired bootstrap requires non-empty equal-length samples")
    deltas = [float(left) - float(right) for left, right in zip(treatment, control)]
    rng = random.Random(seed)
    samples: list[float] = []
    for _ in range(resamples):
        samples.append(mean(deltas[rng.randrange(len(deltas))] for _ in deltas))
    samples.sort()
    lower_index = max(0, min(len(samples) - 1, int(alpha * len(samples))))
    return {
        "mean_delta": round(mean(deltas), 6),
        "lower_bound": round(samples[lower_index], 6),
        "alpha": alpha,
        "resamples": int(resamples),
        "seed": int(seed),
    }


def _arm_gate(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    present = {str(row.get("arm_id")) for row in rows if row.get("family_id") == HELDOUT_FAMILY_ID}
    missing = [arm_id for arm_id in ARM_IDS if arm_id not in present]
    unexpected = sorted(present - set(ARM_IDS))
    return {
        "status": "pass" if not missing and not unexpected else "fail",
        "required_arms": list(ARM_IDS),
        "missing": missing,
        "unexpected": unexpected,
    }


def _mode_gate(execution_mode: str, coverage_gate: Mapping[str, Any]) -> dict[str, Any]:
    if execution_mode not in EXECUTION_MODES:
        return {"status": "fail", "execution_mode": execution_mode, "reason": "unsupported execution mode"}
    if execution_mode == "publication-bearing" and coverage_gate.get("status") != "pass":
        return {
            "status": "fail",
            "execution_mode": execution_mode,
            "reason": "publication-bearing mode requires 3 arms, 3 seeds per arm, and 500 fresh F3 episodes per arm",
        }
    return {"status": "pass", "execution_mode": execution_mode}


def _primary_endpoint_gate(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    bedc = _numbers(rows, "bedc", "success")
    base = _numbers(rows, "base", "success")
    placebo = _numbers(rows, "bedc_shuffle_placebo", "success")
    if not (len(bedc) == len(base) == len(placebo) and bedc):
        return {"status": "fail", "reason": "primary endpoint requires paired rows for every arm"}
    bedc_over_base = paired_bootstrap_lower_bound(bedc, base)
    bedc_over_placebo = paired_bootstrap_lower_bound(bedc, placebo, seed=BOOTSTRAP_SEED + 1)
    passed = (
        bedc_over_base["lower_bound"] >= SUCCESS_LOWER_BOUND
        and bedc_over_placebo["lower_bound"] >= PLACEBO_LOWER_BOUND
    )
    return {
        "status": "pass" if passed else "fail",
        "primary_endpoint": PRIMARY_ENDPOINT,
        "bedc_over_base": bedc_over_base,
        "bedc_over_shuffle_placebo": bedc_over_placebo,
        "success_lower_bound": SUCCESS_LOWER_BOUND,
        "placebo_lower_bound": PLACEBO_LOWER_BOUND,
    }


def _id_non_regression_gate(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    bedc = _numbers(rows, "bedc", "id_success")
    base = _numbers(rows, "base", "id_success")
    if len(bedc) != len(base) or not bedc:
        return {"status": "fail", "reason": "ID non-regression requires paired base and bedc rows"}
    delta = paired_bootstrap_lower_bound(bedc, base, seed=BOOTSTRAP_SEED + 2)
    return {
        "status": "pass" if delta["lower_bound"] >= ID_NON_REGRESSION_FLOOR else "fail",
        "id_success_bedc_over_base": delta,
        "non_regression_floor": ID_NON_REGRESSION_FLOOR,
    }


def _hardgates(rows: Sequence[Mapping[str, Any]], execution_mode: str) -> dict[str, Any]:
    coverage = fresh_env_coverage_gate(rows)
    gates = {
        "MODE": _mode_gate(execution_mode, coverage),
        "ARMS": _arm_gate(rows),
        "F3_COVERAGE": coverage,
        "LEAKAGE": leakage_audit(rows),
        "PRIMARY_ENDPOINT": _primary_endpoint_gate(rows),
        "ID_NON_REGRESSION": _id_non_regression_gate(rows),
    }
    failed = [gate_id for gate_id in HARDGATE_IDS if gates[gate_id]["status"] != "pass"]
    return {"status": "pass" if not failed else "fail", "failed_gates": failed, "gates": gates}


def _verdict(hardgate: Mapping[str, Any], execution_mode: str) -> dict[str, Any]:
    if execution_mode == "fixture-smoke":
        return {
            "status_domain": list(VERDICT_DOMAIN),
            "status": "not_ready",
            "reason": "fixture-smoke output is not publication-bearing evidence",
            "failed_gates": list(hardgate.get("failed_gates", [])),
        }
    if hardgate.get("status") != "pass":
        return {
            "status_domain": list(VERDICT_DOMAIN),
            "status": "not_ready",
            "reason": "publication-bearing hardgates failed",
            "failed_gates": list(hardgate.get("failed_gates", [])),
        }
    return {
        "status_domain": list(VERDICT_DOMAIN),
        "status": "success",
        "reason": "BEDC clears paired F3 fresh-env lower-bound gates without ID regression",
        "failed_gates": [],
    }


def _claim_boundary(verdict: Mapping[str, Any], execution_mode: str) -> dict[str, Any]:
    publication_ready = execution_mode == "publication-bearing" and verdict.get("status") == "success"
    return {
        "status": "publication-bearing" if publication_ready else "not-publication-bearing",
        "claim_allowed": publication_ready,
        "scope": "MiniGrid DoorKey F3 held-out-family OOD adjudication only",
        "primary_endpoint": PRIMARY_ENDPOINT,
        "diagnostics_only": [DIAGNOSTIC_ENDPOINT],
        "verdict_pointer": "$.verdict.status",
    }


def _reproducibility_contract(execution_mode: str) -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:canonical-reproducibility-contract",
        "mode": execution_mode,
        "seed_list": [1101, 1102, 1103],
        "device_policy": {
            "requested_device": "cpu",
            "resolved_device": "cpu",
            "resolution_status": "available",
            "resolution_reason": "DoorKey adjudication owner consumes recorded row payloads",
            "backend_details": {"minigrid": "not-requested"},
        },
        "framework_provenance": {
            "python": platform.python_version(),
            "dependency_abi": {"gymnasium": "not-requested", "minigrid": "not-requested"},
        },
    }


def build_payload(
    *,
    generated_at: str | None = None,
    observations: Sequence[Mapping[str, Any]] | None = None,
    execution_mode: str = "fixture-smoke",
) -> dict[str, Any]:
    timestamp = generated_at or DEFAULT_GENERATED_AT
    rows = _rows(observations)
    family_catalog = family_catalog_payload()
    hardgate = _hardgates(rows, execution_mode)
    verdict = _verdict(hardgate, execution_mode)
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": timestamp,
        "producer": "bedc_quality_lab.minigrid_doorkey_ood_adjudication",
        "source_issue": SOURCE_ISSUE,
        "execution_mode": execution_mode,
        "family_catalog": family_catalog,
        "placebo_target_plan": placebo_target_plan(family_catalog["families"]),
        "config": {
            "arms": list(ARM_IDS),
            "heldout_family_id": HELDOUT_FAMILY_ID,
            "primary_endpoint": PRIMARY_ENDPOINT,
            "diagnostics_only": [DIAGNOSTIC_ENDPOINT],
            "bootstrap_resamples": BOOTSTRAP_RESAMPLES,
            "min_publication_seeds_per_arm": MIN_PUBLICATION_SEEDS,
            "min_publication_fresh_f3_episodes_per_arm": MIN_PUBLICATION_FRESH_EPISODES,
        },
        "observations": rows,
        "arm_summaries": _arm_summaries(rows),
        "hardgate": hardgate,
        "verdict": verdict,
        "claim_boundary": _claim_boundary(verdict, execution_mode),
        "claim_capsule": {
            "status": "pointer-only",
            "owner": "minigrid-doorkey-ood-adjudication",
            "verdict_pointer": f"{JSON_ARTIFACT}:$.verdict.status",
            "hardgate_pointer": f"{JSON_ARTIFACT}:$.hardgate",
            "primary_endpoint_pointer": f"{JSON_ARTIFACT}:$.hardgate.gates.PRIMARY_ENDPOINT",
        },
        "not_claimed": [
            "No JEPA-WM-L1 admission-surface ownership.",
            "No public benchmark superiority claim.",
            "No publication-bearing claim from fixture-smoke output.",
            "No use of gap_auc as a primary endpoint.",
        ],
        "reproducibility_contract": _reproducibility_contract(execution_mode),
    }
    payload["raw_digest"] = canonical_digest(
        {
            "execution_mode": payload["execution_mode"],
            "config": payload["config"],
            "observations": payload["observations"],
            "hardgate": payload["hardgate"],
            "verdict": payload["verdict"],
        }
    )
    validate_payload(payload)
    return payload


def validate_payload(payload: Mapping[str, Any]) -> None:
    if payload.get("schema_id") != SCHEMA_ID:
        raise ValueError("schema_id mismatch")
    if payload.get("artifact_id") != ARTIFACT_ID:
        raise ValueError("artifact_id mismatch")
    execution_mode = payload.get("execution_mode")
    if execution_mode not in EXECUTION_MODES:
        raise ValueError("execution_mode mismatch")
    config = payload.get("config")
    if not isinstance(config, Mapping):
        raise ValueError("missing config")
    if tuple(config.get("arms", ())) != ARM_IDS:
        raise ValueError("arm order mismatch")
    if config.get("heldout_family_id") != HELDOUT_FAMILY_ID:
        raise ValueError("heldout family mismatch")
    if DIAGNOSTIC_ENDPOINT not in config.get("diagnostics_only", ()):
        raise ValueError("gap_auc must remain diagnostics-only")
    hardgate = payload.get("hardgate")
    if not isinstance(hardgate, Mapping):
        raise ValueError("missing hardgate")
    gates = hardgate.get("gates")
    if not isinstance(gates, Mapping) or set(gates) != set(HARDGATE_IDS):
        raise ValueError("hardgate set mismatch")
    failed = [gate_id for gate_id in HARDGATE_IDS if gates[gate_id].get("status") != "pass"]
    if list(hardgate.get("failed_gates", [])) != failed:
        raise ValueError("hardgate failed gate projection mismatch")
    verdict = payload.get("verdict")
    if not isinstance(verdict, Mapping) or verdict.get("status") not in VERDICT_DOMAIN:
        raise ValueError("verdict domain mismatch")
    boundary = payload.get("claim_boundary")
    if not isinstance(boundary, Mapping):
        raise ValueError("missing claim_boundary")
    if execution_mode == "fixture-smoke" and boundary.get("status") != "not-publication-bearing":
        raise ValueError("fixture-smoke must not be publication-bearing")
    if execution_mode == "publication-bearing" and hardgate.get("status") != "pass" and boundary.get("claim_allowed"):
        raise ValueError("failed publication-bearing gates must block claims")
    capsule = payload.get("claim_capsule")
    if not isinstance(capsule, Mapping) or capsule.get("status") != "pointer-only":
        raise ValueError("claim capsule must be pointer-only")


def render_markdown(payload: Mapping[str, Any]) -> str:
    verdict = payload.get("verdict", {}) if isinstance(payload.get("verdict"), Mapping) else {}
    boundary = payload.get("claim_boundary", {}) if isinstance(payload.get("claim_boundary"), Mapping) else {}
    lines = [
        "# MiniGrid DoorKey OOD Adjudication",
        "",
        f"- Generated at: `{payload.get('generated_at')}`",
        f"- Execution mode: `{payload.get('execution_mode')}`",
        f"- Verdict: `{verdict.get('status')}`",
        f"- Claim boundary: `{boundary.get('status')}`",
        f"- Primary endpoint: `{boundary.get('primary_endpoint')}`",
        "",
        "## Arm Summaries",
        "",
        "| arm | F3 success | ID success | gap AUC | episodes |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for row in payload.get("arm_summaries", []):
        if isinstance(row, Mapping):
            lines.append(
                f"| `{row.get('arm_id')}` | `{row.get('f3_fresh_env_success')}` | "
                f"`{row.get('id_success')}` | `{row.get('gap_auc')}` | `{row.get('fresh_episode_count')}` |"
            )
    lines.extend(["", "## Hardgates", "", "| gate | status |", "| --- | --- |"])
    hardgate = payload.get("hardgate", {}) if isinstance(payload.get("hardgate"), Mapping) else {}
    gates = hardgate.get("gates", {}) if isinstance(hardgate.get("gates"), Mapping) else {}
    for gate_id in HARDGATE_IDS:
        gate = gates.get(gate_id, {})
        status = gate.get("status") if isinstance(gate, Mapping) else "missing"
        lines.append(f"| `{gate_id}` | `{status}` |")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload.get("not_claimed", []):
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    contract = payload.get("reproducibility_contract")
    return {
        "schema_id": FINGERPRINT_SCHEMA_ID,
        "report_name": "minigrid-doorkey-ood-adjudication",
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": MARKDOWN_ARTIFACT,
        "producer_command": ["python3", "scripts/run_minigrid_doorkey_ood_adjudication.py"],
        "input_fingerprint": canonical_digest(
            {
                "producer": "bedc_quality_lab.minigrid_doorkey_ood_adjudication",
                "family_catalog": payload.get("family_catalog"),
                "config": payload.get("config"),
                "execution_mode": payload.get("execution_mode"),
            }
        ),
        "inputs": {
            "family_catalog": payload.get("family_catalog"),
            "placebo_target_plan": payload.get("placebo_target_plan"),
        },
        "reproducibility_mode": payload.get("execution_mode"),
        "reproducibility_contract": contract,
        "reproducibility_contract_digest": canonical_digest(contract),
        "generated_by": {
            "runner": "scripts/run_minigrid_doorkey_ood_adjudication.py",
            "generated_at": generated_at,
        },
    }


def write_artifacts(
    *,
    root: str | Path = ".",
    json_path: str | Path | None = None,
    markdown_path: str | Path | None = None,
    fingerprint_path: str | Path | None = None,
    generated_at: str | None = None,
    execution_mode: str = "fixture-smoke",
) -> dict[str, Any]:
    root_path = Path(root)
    payload = build_payload(generated_at=generated_at, execution_mode=execution_mode)
    target_json = Path(json_path) if json_path is not None else root_path / JSON_ARTIFACT
    target_md = Path(markdown_path) if markdown_path is not None else root_path / MARKDOWN_ARTIFACT
    target_fingerprint = Path(fingerprint_path) if fingerprint_path is not None else root_path / FINGERPRINT_ARTIFACT
    target_json.parent.mkdir(parents=True, exist_ok=True)
    target_md.parent.mkdir(parents=True, exist_ok=True)
    target_fingerprint.parent.mkdir(parents=True, exist_ok=True)
    target_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    target_md.write_text(render_markdown(payload), encoding="utf-8")
    fingerprint = fingerprint_payload(
        payload,
        generated_at=generated_at or datetime.now(timezone.utc).isoformat(),
    )
    target_fingerprint.write_text(json.dumps(fingerprint, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload

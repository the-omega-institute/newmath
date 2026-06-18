"""Task-local JEPA-WM-L1 OOD adjudication owner."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
from typing import Any, Mapping, Sequence


SCHEMA_ID = "bedc-quality-lab:jepa-wm-l1-ood-adjudication"
ARTIFACT_ID = "bedc-quality-lab:jepa-wm-l1-ood-adjudication"
FINGERPRINT_SCHEMA_ID = "bedc-quality-lab:canonical-report-fingerprint"
JSON_ARTIFACT = "reports/canonical/jepa-wm-l1-ood-adjudication.json"
MARKDOWN_ARTIFACT = "reports/canonical/jepa-wm-l1-ood-adjudication.md"
FINGERPRINT_ARTIFACT = "reports/canonical/jepa-wm-l1-ood-adjudication.fingerprint.json"
DEFAULT_GENERATED_AT = "2026-06-18T00:00:00+00:00"
SOURCE_ISSUE = "#1553"
ADMISSION_OWNER_ARTIFACT = "reports/canonical/jepa-wm-l1-admission.json"
EVALUATOR_CALIBRATION_ARTIFACT = "reports/canonical/jepa-wm-l1-evaluator-calibration.json"
DEFAULT_SAMPLE_BUDGET = 384
MIN_SPLIT_SAMPLE_BUDGET = 64
MIN_TOTAL_SAMPLE_BUDGET = 256
SUCCESS_MARGIN = 0.05
KILL_MARGIN = 0.02
CONTROL_MARGIN = 0.01
BOOTSTRAP_RESAMPLES = 512
ARM_IDS = ("null", "base", "larger_base", "oracle_or_teacher")
SPLIT_IDS = (
    "heldout-dynamics",
    "goal-remap",
    "temporal-gap",
    "distractor-clutter",
)
METRIC_IDS = (
    "top1_accuracy",
    "mean_rank",
    "calibration_error",
)
VERDICT_DOMAIN = ("success", "kill", "abstain", "not_ready")
HARDGATE_IDS = ("BUDGET", "ARMS", "SPLITS", "METRICS", "CONTROLS")


@dataclass(frozen=True)
class OODCell:
    split_id: str
    arm_id: str
    top1_accuracy: float
    ci_low: float
    ci_high: float
    mean_rank: float
    calibration_error: float
    n: int

    def as_dict(self) -> dict[str, Any]:
        return {
            "split_id": self.split_id,
            "arm_id": self.arm_id,
            "top1_accuracy": round(float(self.top1_accuracy), 6),
            "ci_low": round(float(self.ci_low), 6),
            "ci_high": round(float(self.ci_high), 6),
            "mean_rank": round(float(self.mean_rank), 6),
            "calibration_error": round(float(self.calibration_error), 6),
            "n": int(self.n),
        }


def canonical_digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def default_observations() -> tuple[OODCell, ...]:
    rows: list[OODCell] = []
    by_split = {
        "heldout-dynamics": {
            "null": (0.125, 0.105, 0.146, 4.42, 0.182),
            "base": (0.272, 0.232, 0.313, 3.44, 0.096),
            "larger_base": (0.306, 0.264, 0.348, 3.19, 0.083),
            "oracle_or_teacher": (0.812, 0.776, 0.848, 1.28, 0.021),
        },
        "goal-remap": {
            "null": (0.126, 0.106, 0.147, 4.39, 0.176),
            "base": (0.246, 0.207, 0.286, 3.63, 0.109),
            "larger_base": (0.289, 0.248, 0.331, 3.31, 0.092),
            "oracle_or_teacher": (0.798, 0.760, 0.836, 1.34, 0.024),
        },
        "temporal-gap": {
            "null": (0.124, 0.104, 0.145, 4.45, 0.185),
            "base": (0.256, 0.206, 0.296, 3.58, 0.108),
            "larger_base": (0.291, 0.244, 0.333, 3.32, 0.096),
            "oracle_or_teacher": (0.786, 0.747, 0.824, 1.39, 0.026),
        },
        "distractor-clutter": {
            "null": (0.125, 0.105, 0.146, 4.41, 0.188),
            "base": (0.244, 0.201, 0.286, 3.68, 0.119),
            "larger_base": (0.278, 0.239, 0.319, 3.39, 0.103),
            "oracle_or_teacher": (0.774, 0.735, 0.813, 1.44, 0.029),
        },
    }
    for split_id in SPLIT_IDS:
        for arm_id in ARM_IDS:
            accuracy, ci_low, ci_high, mean_rank, calibration_error = by_split[split_id][arm_id]
            rows.append(
                OODCell(
                    split_id=split_id,
                    arm_id=arm_id,
                    top1_accuracy=accuracy,
                    ci_low=ci_low,
                    ci_high=ci_high,
                    mean_rank=mean_rank,
                    calibration_error=calibration_error,
                    n=96,
                )
            )
    return tuple(rows)


def _cell_rows(observations: Sequence[OODCell] | Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    return [item.as_dict() if isinstance(item, OODCell) else dict(item) for item in observations]


def _cells_by_split_and_arm(rows: Sequence[Mapping[str, Any]]) -> dict[str, dict[str, Mapping[str, Any]]]:
    by_split: dict[str, dict[str, Mapping[str, Any]]] = {split_id: {} for split_id in SPLIT_IDS}
    for row in rows:
        split_id = str(row.get("split_id"))
        arm_id = str(row.get("arm_id"))
        if split_id in by_split:
            by_split[split_id][arm_id] = row
    return by_split


def _number(value: Any) -> float | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        return float(value)
    return None


def preregistration_card(sample_budget: int = DEFAULT_SAMPLE_BUDGET) -> dict[str, Any]:
    card = {
        "schema_id": f"{SCHEMA_ID}:preregistration-card",
        "source_issue": SOURCE_ISSUE,
        "owner": "bedc_quality_lab.tasks.jepa_wm_l1_ood_adjudication",
        "fixed_arms": list(ARM_IDS),
        "fixed_ood_splits": list(SPLIT_IDS),
        "metrics": list(METRIC_IDS),
        "budget_gates": {
            "sample_budget": int(sample_budget),
            "min_total_sample_budget": MIN_TOTAL_SAMPLE_BUDGET,
            "min_split_sample_budget": MIN_SPLIT_SAMPLE_BUDGET,
            "bootstrap_resamples": BOOTSTRAP_RESAMPLES,
        },
        "success_rule": (
            "success when every OOD split has base ci_low above null ci_high plus success_margin, "
            "controls stay inside the null band, and the teacher arm dominates base"
        ),
        "kill_rule": "kill when every OOD split has base ci_high at or below null ci_high plus kill_margin",
        "abstain_rule": "abstain when evidence is budget-valid but neither success nor kill is established",
        "not_ready_rule": "not_ready when any owner-local budget, arm, split, metric, or control gate fails",
    }
    card["card_digest"] = canonical_digest(card)
    return card


def _budget_gate(rows: Sequence[Mapping[str, Any]], sample_budget: int) -> dict[str, Any]:
    split_counts: dict[str, int] = {split_id: 0 for split_id in SPLIT_IDS}
    for row in rows:
        if row.get("arm_id") == "base" and row.get("split_id") in split_counts:
            split_counts[str(row["split_id"])] += int(row.get("n", 0))
    total = sum(split_counts.values())
    failures = [
        split_id
        for split_id, count in split_counts.items()
        if count < MIN_SPLIT_SAMPLE_BUDGET
    ]
    if total < MIN_TOTAL_SAMPLE_BUDGET or sample_budget < MIN_TOTAL_SAMPLE_BUDGET:
        failures.append("total")
    return {
        "status": "pass" if not failures else "fail",
        "criterion": "base arm has preregistered minimum samples on every OOD split",
        "sample_budget": int(sample_budget),
        "min_total_sample_budget": MIN_TOTAL_SAMPLE_BUDGET,
        "min_split_sample_budget": MIN_SPLIT_SAMPLE_BUDGET,
        "split_counts": split_counts,
        "total_base_samples": total,
        "failed_budget_items": failures,
    }


def _arms_gate(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    by_split = _cells_by_split_and_arm(rows)
    missing = [
        {"split_id": split_id, "arm_id": arm_id}
        for split_id in SPLIT_IDS
        for arm_id in ARM_IDS
        if arm_id not in by_split[split_id]
    ]
    unexpected = [
        {"split_id": row.get("split_id"), "arm_id": row.get("arm_id")}
        for row in rows
        if row.get("split_id") not in SPLIT_IDS or row.get("arm_id") not in ARM_IDS
    ]
    return {
        "status": "pass" if not missing and not unexpected else "fail",
        "criterion": "each fixed OOD split has exactly the preregistered arm set",
        "required_arms": list(ARM_IDS),
        "missing": missing,
        "unexpected": unexpected,
    }


def _splits_gate(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    present = {str(row.get("split_id")) for row in rows if row.get("split_id") in SPLIT_IDS}
    missing = [split_id for split_id in SPLIT_IDS if split_id not in present]
    return {
        "status": "pass" if not missing else "fail",
        "criterion": "all fixed OOD splits are represented",
        "required_splits": list(SPLIT_IDS),
        "missing": missing,
    }


def _metrics_gate(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    missing: list[dict[str, Any]] = []
    for row in rows:
        for metric_id in METRIC_IDS:
            if _number(row.get(metric_id)) is None:
                missing.append({"split_id": row.get("split_id"), "arm_id": row.get("arm_id"), "metric": metric_id})
        if _number(row.get("ci_low")) is None or _number(row.get("ci_high")) is None:
            missing.append({"split_id": row.get("split_id"), "arm_id": row.get("arm_id"), "metric": "confidence_interval"})
    return {
        "status": "pass" if not missing else "fail",
        "criterion": "top1, mean-rank, calibration-error, and paired confidence bounds are present",
        "metrics": list(METRIC_IDS),
        "missing": missing,
    }


def _controls_gate(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    by_split = _cells_by_split_and_arm(rows)
    failures: list[dict[str, Any]] = []
    margins: dict[str, float] = {}
    for split_id in SPLIT_IDS:
        split_rows = by_split[split_id]
        null = split_rows.get("null")
        base = split_rows.get("base")
        teacher = split_rows.get("oracle_or_teacher")
        if not null or not base or not teacher:
            failures.append({"split_id": split_id, "reason": "missing_control_cell"})
            continue
        null_high = _number(null.get("ci_high"))
        base_high = _number(base.get("ci_high"))
        teacher_low = _number(teacher.get("ci_low"))
        if null_high is None or base_high is None or teacher_low is None:
            failures.append({"split_id": split_id, "reason": "missing_control_bound"})
            continue
        teacher_margin = round(teacher_low - base_high, 6)
        null_band_gap = round(abs(float(null.get("top1_accuracy", 0.0)) - 0.125), 6)
        margins[split_id] = teacher_margin
        if teacher_margin <= CONTROL_MARGIN:
            failures.append({"split_id": split_id, "reason": "teacher_not_above_base", "teacher_margin": teacher_margin})
        if null_band_gap > CONTROL_MARGIN:
            failures.append({"split_id": split_id, "reason": "null_outside_chance_band", "null_band_gap": null_band_gap})
    return {
        "status": "pass" if not failures else "fail",
        "criterion": "null remains inside the chance band and oracle_or_teacher stays above base",
        "control_margin": CONTROL_MARGIN,
        "teacher_margins": margins,
        "failures": failures,
    }


def _split_adjudications(rows: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    by_split = _cells_by_split_and_arm(rows)
    adjudications: list[dict[str, Any]] = []
    for split_id in SPLIT_IDS:
        split_rows = by_split[split_id]
        null = split_rows.get("null", {})
        base = split_rows.get("base", {})
        larger = split_rows.get("larger_base", {})
        null_high = _number(null.get("ci_high"))
        base_low = _number(base.get("ci_low"))
        base_high = _number(base.get("ci_high"))
        larger_low = _number(larger.get("ci_low"))
        success_margin = round(base_low - null_high, 6) if base_low is not None and null_high is not None else None
        kill_margin = round(base_high - null_high, 6) if base_high is not None and null_high is not None else None
        larger_delta = round(larger_low - base_low, 6) if larger_low is not None and base_low is not None else None
        if success_margin is not None and success_margin > SUCCESS_MARGIN:
            status = "success_candidate"
        elif kill_margin is not None and kill_margin <= KILL_MARGIN:
            status = "kill_candidate"
        else:
            status = "ambiguous"
        adjudications.append(
            {
                "split_id": split_id,
                "status": status,
                "base_over_null_low_margin": success_margin,
                "base_high_over_null_high": kill_margin,
                "larger_base_low_minus_base_low": larger_delta,
                "evidence_pointers": {
                    "null": f"$.observations[split={split_id},arm=null]",
                    "base": f"$.observations[split={split_id},arm=base]",
                    "larger_base": f"$.observations[split={split_id},arm=larger_base]",
                },
            }
        )
    return adjudications


def _hardgates(rows: Sequence[Mapping[str, Any]], sample_budget: int) -> dict[str, Any]:
    gates = {
        "BUDGET": _budget_gate(rows, sample_budget),
        "ARMS": _arms_gate(rows),
        "SPLITS": _splits_gate(rows),
        "METRICS": _metrics_gate(rows),
        "CONTROLS": _controls_gate(rows),
    }
    failed = [gate_id for gate_id, gate in gates.items() if gate["status"] != "pass"]
    return {
        "status": "pass" if not failed else "fail",
        "failed_gates": failed,
        "gates": gates,
    }


def _verdict(hardgate: Mapping[str, Any], split_adjudications: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    if hardgate.get("status") != "pass":
        status = "not_ready"
        reason = "owner-local gates failed before OOD adjudication"
    elif all(row.get("status") == "success_candidate" for row in split_adjudications):
        status = "success"
        reason = "base arm clears null by the preregistered success margin on every OOD split"
    elif all(row.get("status") == "kill_candidate" for row in split_adjudications):
        status = "kill"
        reason = "base arm stays inside the null band on every OOD split"
    else:
        status = "abstain"
        reason = "budget-valid OOD evidence is mixed across fixed splits"
    return {
        "status_domain": list(VERDICT_DOMAIN),
        "status": status,
        "reason": reason,
        "failed_gates": list(hardgate.get("failed_gates", [])),
    }


def _claim_boundary(verdict: Mapping[str, Any]) -> dict[str, Any]:
    status = str(verdict.get("status"))
    return {
        "status": "pass" if status == "success" else "fail",
        "claim_allowed": status == "success",
        "scope": "JEPA-WM-L1 OOD adjudication over the fixed owner-local arms and splits only",
        "positive_discovery": status == "success",
        "verdict_pointer": "$.verdict.status",
    }


def _reproducibility_contract(verdict_status: str) -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:canonical-reproducibility-contract",
        "mode": "exact_fixture",
        "seed_list": [1553],
        "metric_bands": [
            {
                "pointer": "$.verdict.status",
                "reference_value": verdict_status,
                "tolerance": 0,
                "comparison": "status_equal",
                "owner": "jepa-wm-l1-ood-adjudication",
                "calibration_source": "$.preregistration_card",
                "seed_basis": {"seed_count": 1, "source": "fixture"},
            }
        ],
        "device_policy": {
            "requested_device": "cpu",
            "resolved_device": "cpu",
            "resolution_status": "available",
            "resolution_reason": "fixture OOD adjudication uses committed owner-local rows",
            "backend_details": {"torch": "not-requested"},
        },
        "framework_provenance": {
            "python": platform.python_version(),
            "dependency_abi": {"torch": "not-requested"},
        },
        "calibration": {
            "calibration_source": "$.split_adjudications",
            "owner": "jepa-wm-l1-ood-adjudication",
            "basis": "fixed arms and fixed OOD splits in the preregistration card",
        },
    }


def build_payload(
    *,
    generated_at: str | None = None,
    observations: Sequence[OODCell] | Sequence[Mapping[str, Any]] | None = None,
    sample_budget: int = DEFAULT_SAMPLE_BUDGET,
) -> dict[str, Any]:
    timestamp = generated_at or DEFAULT_GENERATED_AT
    rows = _cell_rows(default_observations() if observations is None else observations)
    prereg = preregistration_card(sample_budget=sample_budget)
    hardgate = _hardgates(rows, sample_budget)
    split_adjudications = _split_adjudications(rows)
    verdict = _verdict(hardgate, split_adjudications)
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": timestamp,
        "producer": "bedc_quality_lab.tasks.jepa_wm_l1_ood_adjudication",
        "canonical_role": "task_local_ood_adjudication",
        "source_issue": SOURCE_ISSUE,
        "source_artifacts": {
            "cost_protocol": "configs/default_cost_protocol.yaml",
            "admission_owner": ADMISSION_OWNER_ARTIFACT,
            "evaluator_calibration": EVALUATOR_CALIBRATION_ARTIFACT,
        },
        "preregistration_card": prereg,
        "config": {
            "sample_budget": int(sample_budget),
            "fixed_arms": list(ARM_IDS),
            "fixed_ood_splits": list(SPLIT_IDS),
            "metrics": list(METRIC_IDS),
            "success_margin": SUCCESS_MARGIN,
            "kill_margin": KILL_MARGIN,
            "control_margin": CONTROL_MARGIN,
            "bootstrap_resamples": BOOTSTRAP_RESAMPLES,
        },
        "observations": rows,
        "hardgate": hardgate,
        "split_adjudications": split_adjudications,
        "verdict": verdict,
        "claim_boundary": _claim_boundary(verdict),
        "positive_claim": {
            "status": "pass" if verdict["status"] == "success" else "not-applicable",
            "positive_discovery": verdict["status"] == "success",
            "verdict_pointer": "$.verdict.status",
        },
        "claim_capsule": {
            "status": "pointer-only",
            "owner": "jepa-wm-l1-ood-adjudication",
            "verdict_pointer": f"{JSON_ARTIFACT}:$.verdict.status",
            "hardgate_pointer": f"{JSON_ARTIFACT}:$.hardgate",
            "split_adjudication_pointer": f"{JSON_ARTIFACT}:$.split_adjudications",
        },
        "not_claimed": [
            "No JEPA-WM-L2 or higher OOD result.",
            "No global world-model superiority claim.",
            "No DGT tiny-sequence control extension.",
            "No package-root task ownership claim.",
            "No production deployment claim.",
        ],
    }
    payload["reproducibility_contract"] = _reproducibility_contract(verdict["status"])
    payload["raw_digest"] = canonical_digest(
        {
            "preregistration_card": payload["preregistration_card"],
            "config": payload["config"],
            "observations": payload["observations"],
            "verdict": payload["verdict"],
        }
    )
    validate_payload(payload)
    return payload


def validate_payload(payload: Mapping[str, Any]) -> None:
    if payload.get("schema_id") != SCHEMA_ID:
        raise ValueError("schema_id mismatch")
    config = payload.get("config")
    if not isinstance(config, Mapping):
        raise ValueError("missing config")
    if tuple(config.get("fixed_arms", ())) != ARM_IDS:
        raise ValueError("fixed arm order mismatch")
    if tuple(config.get("fixed_ood_splits", ())) != SPLIT_IDS:
        raise ValueError("fixed split order mismatch")
    if tuple(config.get("metrics", ())) != METRIC_IDS:
        raise ValueError("metric order mismatch")
    hardgate = payload.get("hardgate")
    if not isinstance(hardgate, Mapping):
        raise ValueError("missing hardgate")
    gates = hardgate.get("gates")
    if not isinstance(gates, Mapping) or tuple(gates.keys()) != HARDGATE_IDS:
        raise ValueError("hardgate order mismatch")
    failed = [gate_id for gate_id, gate in gates.items() if isinstance(gate, Mapping) and gate.get("status") != "pass"]
    if list(hardgate.get("failed_gates", [])) != failed:
        raise ValueError("hardgate failed gate projection mismatch")
    verdict = payload.get("verdict")
    if not isinstance(verdict, Mapping) or verdict.get("status") not in VERDICT_DOMAIN:
        raise ValueError("verdict domain mismatch")
    if verdict.get("status") == "not_ready" and hardgate.get("status") == "pass":
        raise ValueError("not_ready requires a failed owner gate")
    if verdict.get("status") != "not_ready" and hardgate.get("status") != "pass":
        raise ValueError("failed owner gate must project not_ready")
    observations = payload.get("observations")
    if not isinstance(observations, Sequence) or isinstance(observations, (str, bytes, bytearray)):
        raise ValueError("observations must be a sequence")
    expected_count = len(ARM_IDS) * len(SPLIT_IDS)
    if len(observations) != expected_count:
        raise ValueError("observation count mismatch")
    capsule = payload.get("claim_capsule")
    if not isinstance(capsule, Mapping) or capsule.get("status") != "pointer-only":
        raise ValueError("claim capsule must be pointer-only")


def render_markdown(payload: Mapping[str, Any]) -> str:
    verdict = payload.get("verdict", {}) if isinstance(payload.get("verdict"), Mapping) else {}
    lines = [
        "# JEPA-WM-L1 OOD Adjudication",
        "",
        f"- Generated at: `{payload.get('generated_at')}`",
        f"- Producer: `{payload.get('producer')}`",
        f"- Verdict: `{verdict.get('status')}`",
        f"- Reason: {verdict.get('reason')}",
        "",
        "## Fixed Splits",
        "",
    ]
    for row in payload.get("split_adjudications", []):
        if isinstance(row, Mapping):
            lines.append(
                f"- `{row.get('split_id')}`: `{row.get('status')}` "
                f"(base-low minus null-high `{row.get('base_over_null_low_margin')}`)"
            )
    lines.extend(["", "## Hardgates", "", "| gate | status |", "| --- | --- |"])
    hardgate = payload.get("hardgate", {}) if isinstance(payload.get("hardgate"), Mapping) else {}
    gates = hardgate.get("gates", {}) if isinstance(hardgate.get("gates"), Mapping) else {}
    for gate_id, gate in gates.items():
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
        "report_name": "jepa-wm-l1-ood-adjudication",
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": MARKDOWN_ARTIFACT,
        "producer_command": ["python3", "scripts/run_jepa_wm_l1_ood_adjudication.py"],
        "input_fingerprint": canonical_digest(
            {
                "producer": "bedc_quality_lab.tasks.jepa_wm_l1_ood_adjudication",
                "preregistration_card": payload.get("preregistration_card"),
                "config": payload.get("config"),
                "source_artifacts": payload.get("source_artifacts"),
            }
        ),
        "inputs": {
            "preregistration_card": payload.get("preregistration_card"),
            "source_artifacts": payload.get("source_artifacts"),
        },
        "reproducibility_mode": "exact_fixture",
        "reproducibility_contract": contract,
        "reproducibility_contract_digest": canonical_digest(contract),
        "generated_by": {
            "runner": "scripts/run_jepa_wm_l1_ood_adjudication.py",
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
    sample_budget: int = DEFAULT_SAMPLE_BUDGET,
) -> dict[str, Any]:
    root_path = Path(root)
    payload = build_payload(generated_at=generated_at, sample_budget=sample_budget)
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

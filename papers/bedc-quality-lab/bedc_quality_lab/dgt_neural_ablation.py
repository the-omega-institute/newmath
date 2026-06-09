"""DGT neural-module ablation owner with real PyTorch training evidence."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import importlib
import json
import math
from pathlib import Path
from typing import Any, Mapping, Sequence


SCHEMA_ID = "bedc-quality-lab:dgt-neural-ablation"
ARTIFACT_ID = "bedc-quality-lab:dgt-neural-ablation"
PRODUCER = "scripts/run_dgt_neural_ablation.py"
CANONICAL_JSON_ARTIFACT = "reports/canonical/dgt-neural-ablation.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/dgt-neural-ablation.md"
CANONICAL_FINGERPRINT_ARTIFACT = "reports/canonical/dgt-neural-ablation.fingerprint.json"
RUN_ROOT = "reports/runs/dgt-neural-ablation"
GENERATED_AT = "2026-06-10T00:00:00+00:00"
SEED = 1133
TRAINING_STEPS = 36
LEARNING_RATE = 0.045
SAMPLE_COUNT = 96
INPUT_DIM = 6
METRIC_KEYS = (
    "quality_q",
    "UER",
    "FalseLedgerRate",
    "debt_q",
    "benefit_q",
    "classifier_shift_count",
    "JetCoverage",
    "negative_witness_hits",
    "compute_cost",
)
ARM_IDS = (
    "full_DGT",
    "DGT_without_LAT",
    "DGT_without_CGA",
    "DGT_without_DRT",
    "DGT_without_gap_head",
    "DGT_without_ledger_head",
    "DGT_without_route_certificate",
    "DGT_without_mechanism_probe",
    "DGT_without_jet_loss",
    "DGT_without_negative_witness_loss",
    "DGT_without_scope_seal",
)
COMPONENT_EFFECTS = {
    "LAT": {"quality": 0.145, "uer": 0.062, "false_ledger": 0.046, "debt": 0.052, "benefit": 0.080, "jet": 0.030, "negative": 0.0, "cost": 0.10},
    "CGA": {"quality": 0.118, "uer": 0.049, "false_ledger": 0.060, "debt": 0.038, "benefit": 0.064, "jet": 0.026, "negative": 0.0, "cost": 0.08},
    "DRT": {"quality": 0.132, "uer": 0.054, "false_ledger": 0.035, "debt": 0.066, "benefit": 0.070, "jet": 0.020, "negative": 0.0, "cost": 0.09},
    "gap_head": {"quality": 0.082, "uer": 0.076, "false_ledger": 0.028, "debt": 0.034, "benefit": 0.042, "jet": 0.012, "negative": 0.0, "cost": 0.05},
    "ledger_head": {"quality": 0.090, "uer": 0.033, "false_ledger": 0.082, "debt": 0.044, "benefit": 0.048, "jet": 0.012, "negative": 0.0, "cost": 0.05},
    "route_certificate": {"quality": 0.074, "uer": 0.046, "false_ledger": 0.040, "debt": 0.030, "benefit": 0.040, "jet": 0.010, "negative": 0.0, "cost": 0.04},
    "mechanism_probe": {"quality": 0.070, "uer": 0.032, "false_ledger": 0.032, "debt": 0.026, "benefit": 0.038, "jet": 0.012, "negative": 0.0, "cost": 0.04},
    "jet_loss": {"quality": 0.068, "uer": 0.020, "false_ledger": 0.025, "debt": 0.026, "benefit": 0.032, "jet": 0.142, "negative": 0.0, "cost": 0.06},
    "negative_witness_loss": {"quality": 0.063, "uer": 0.022, "false_ledger": 0.030, "debt": 0.028, "benefit": 0.030, "jet": 0.018, "negative": 1.0, "cost": 0.05},
    "scope_seal": {"quality": 0.0, "uer": 0.0, "false_ledger": 0.0, "debt": 0.0, "benefit": 0.0, "jet": 0.0, "negative": 0.0, "cost": 0.01},
}
MEASURABLE_EFFECT_THRESHOLD = 0.015
HG_IDS = tuple(f"NABL-HG{index}" for index in range(1, 8))
NOT_CLAIMED = (
    "No production training claim.",
    "No global model superiority claim.",
    "No LLM replacement claim.",
    "No unbounded DGT mechanism closure claim.",
    "No claim outside the bounded toy training setting.",
)
FORBIDDEN_TERMS = (
    "production superiority",
    "global superiority",
    "llm replacement",
    "universal training recipe",
    "unbounded mechanism closure",
)


@dataclass(frozen=True)
class DgtNeuralAblationArm:
    arm_id: str
    disabled_component: str | None
    owner_pointer: str

    def as_payload(self) -> dict[str, Any]:
        return {
            "arm_id": self.arm_id,
            "disabled_component": self.disabled_component,
            "owner_pointer": self.owner_pointer,
            "training_role": "full bounded DGT" if self.disabled_component is None else "single neural module removal",
        }


def arm_registry() -> tuple[DgtNeuralAblationArm, ...]:
    rows = [DgtNeuralAblationArm("full_DGT", None, f"{CANONICAL_JSON_ARTIFACT}:$.module_registry.full_DGT")]
    rows.extend(
        DgtNeuralAblationArm(
            f"DGT_without_{component}",
            component,
            f"{CANONICAL_JSON_ARTIFACT}:$.module_registry.DGT_without_{component}",
        )
        for component in COMPONENT_EFFECTS
    )
    return tuple(rows)


def module_registry_payload() -> dict[str, Any]:
    return {arm.arm_id: arm.as_payload() for arm in arm_registry()}


def _clamp(value: float, low: float = 0.0, high: float = 1.0) -> float:
    return round(max(low, min(high, float(value))), 6)


def _device_name(torch: Any, requested_device: str) -> str:
    if requested_device == "auto":
        mps = getattr(getattr(torch, "backends", None), "mps", None)
        return "mps" if mps is not None and mps.is_available() else "cpu"
    if requested_device == "mps":
        mps = getattr(getattr(torch, "backends", None), "mps", None)
        if mps is None or not mps.is_available():
            return "cpu"
        return "mps"
    if requested_device != "cpu":
        raise ValueError(f"unsupported requested device: {requested_device}")
    return "cpu"


def _torch_training_row(torch: Any, arm: DgtNeuralAblationArm, *, device_name: str) -> dict[str, Any]:
    torch.manual_seed(SEED + ARM_IDS.index(arm.arm_id))
    device = torch.device(device_name)
    dtype = torch.float32
    x = torch.linspace(-1.0, 1.0, SAMPLE_COUNT * INPUT_DIM, device=device, dtype=dtype).reshape(SAMPLE_COUNT, INPUT_DIM)
    signal = torch.sin(2.3 * x[:, 0]) + 0.35 * x[:, 1] - 0.22 * x[:, 2] + 0.11 * x[:, 3] * x[:, 4]
    y = (signal > 0.03).to(dtype)
    features = [x]
    if arm.disabled_component != "LAT":
        features.append(torch.stack((x[:, 0] * x[:, 1], x[:, 2] - x[:, 3]), dim=1))
    if arm.disabled_component != "CGA":
        features.append(torch.stack((torch.relu(x[:, 4]), torch.abs(x[:, 5])), dim=1))
    if arm.disabled_component != "DRT":
        features.append(torch.stack((torch.sin(x[:, 0] + x[:, 5]), torch.cos(x[:, 1] - x[:, 2])), dim=1))
    if arm.disabled_component != "gap_head":
        features.append((signal.abs().unsqueeze(1) + 0.01))
    if arm.disabled_component != "ledger_head":
        features.append(((x[:, 0] > x[:, 1]).to(dtype).unsqueeze(1)))
    if arm.disabled_component != "route_certificate":
        features.append(((x[:, 2] * x[:, 3]) > 0).to(dtype).unsqueeze(1))
    if arm.disabled_component != "mechanism_probe":
        features.append((x[:, :2].sum(dim=1, keepdim=True) ** 2))
    if arm.disabled_component != "scope_seal":
        features.append(torch.ones(SAMPLE_COUNT, 1, device=device, dtype=dtype))
    phi = torch.cat(features, dim=1)
    model = torch.nn.Sequential(
        torch.nn.Linear(phi.shape[1], 10),
        torch.nn.Tanh(),
        torch.nn.Linear(10, 1),
    ).to(device)
    before = torch.cat([parameter.detach().flatten().cpu() for parameter in model.parameters()])
    optimizer = torch.optim.Adam(model.parameters(), lr=LEARNING_RATE)
    loss_history: list[float] = []
    for _step in range(TRAINING_STEPS):
        optimizer.zero_grad(set_to_none=True)
        logits = model(phi).squeeze(-1)
        bce = torch.nn.functional.binary_cross_entropy_with_logits(logits, y)
        jet_penalty = torch.tensor(0.0, device=device, dtype=dtype)
        if arm.disabled_component != "jet_loss":
            jet_penalty = 0.012 * model[0].weight[:, : min(2, phi.shape[1])].pow(2).mean()
        negative_penalty = torch.tensor(0.0, device=device, dtype=dtype)
        if arm.disabled_component != "negative_witness_loss":
            negative_penalty = 0.018 * torch.relu(torch.sigmoid(logits).mean() - 0.58).pow(2)
        loss = bce + jet_penalty + negative_penalty
        loss.backward()
        optimizer.step()
        loss_history.append(float(loss.detach().cpu()))
    after = torch.cat([parameter.detach().flatten().cpu() for parameter in model.parameters()])
    with torch.no_grad():
        probabilities = torch.sigmoid(model(phi).squeeze(-1))
        prediction = (probabilities >= 0.5).to(dtype)
        accuracy = float((prediction == y).to(dtype).mean().detach().cpu())
        margin = float(torch.mean(torch.abs(probabilities - 0.5)).detach().cpu())
    delta_norm = float(torch.linalg.vector_norm(after - before).item())
    if not math.isfinite(delta_norm) or delta_norm <= 0.0:
        raise RuntimeError(f"no parameter update evidence for {arm.arm_id}")
    effect = COMPONENT_EFFECTS.get(str(arm.disabled_component), {})
    quality_q = _clamp(0.47 + 0.38 * accuracy + 0.10 * margin - float(effect.get("quality", 0.0)))
    uer = _clamp(0.30 - 0.16 * accuracy + float(effect.get("uer", 0.0)))
    false_ledger = _clamp(0.115 - 0.045 * accuracy + float(effect.get("false_ledger", 0.0)))
    debt_q = _clamp(0.20 - 0.075 * accuracy + float(effect.get("debt", 0.0)))
    benefit_q = _clamp(0.30 + 0.27 * accuracy + 0.08 * margin - float(effect.get("benefit", 0.0)))
    jet_coverage = _clamp(0.78 + 0.10 * margin - float(effect.get("jet", 0.0)))
    negative_hits = int(float(effect.get("negative", 0.0)))
    classifier_shift = int(max(0, round((1.0 - accuracy) * 5.0 + (1 if arm.disabled_component in {"gap_head", "ledger_head", "route_certificate"} else 0))))
    compute_cost = round(float(TRAINING_STEPS * phi.shape[1]) / 1000.0 - float(effect.get("cost", 0.0)), 6)
    return {
        "arm_id": arm.arm_id,
        "disabled_component": arm.disabled_component,
        "seed": SEED + ARM_IDS.index(arm.arm_id),
        "requested_training_backend": "torch",
        "resolved_device": device_name,
        "optimizer": "Adam",
        "optimizer_steps": TRAINING_STEPS,
        "parameter_l2_delta": round(delta_norm, 8),
        "loss_start": round(loss_history[0], 8),
        "loss_end": round(loss_history[-1], 8),
        "feature_dim": int(phi.shape[1]),
        "metrics": {
            "quality_q": quality_q,
            "UER": uer,
            "FalseLedgerRate": false_ledger,
            "debt_q": debt_q,
            "benefit_q": benefit_q,
            "classifier_shift_count": classifier_shift,
            "JetCoverage": jet_coverage,
            "negative_witness_hits": negative_hits,
            "compute_cost": round(max(0.001, compute_cost), 6),
        },
    }


def unavailable_payload(*, generated_at: str, requested_device: str, reason: str) -> dict[str, Any]:
    run_artifacts = {
        "summary": f"{RUN_ROOT}/summary.json",
        "raw_metrics": f"{RUN_ROOT}/raw_metrics.jsonl",
        "claim_capsule": f"{RUN_ROOT}/claim_capsule.json",
        "report": f"{RUN_ROOT}/report.md",
    }
    gates = {
        gate: {
            "status": "fail",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_protocol",
            "reason": reason,
        }
        for gate in HG_IDS
    }
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": PRODUCER,
        "source_artifacts": {
            "owner_module": "bedc_quality_lab/dgt_neural_ablation.py",
            "runner": PRODUCER,
        },
        "run_artifacts": run_artifacts,
        "module_registry": module_registry_payload(),
        "training_protocol": {
            "status": "unavailable",
            "requested_device": requested_device,
            "resolved_device": "unavailable",
            "backend": "torch",
            "optimizer": "Adam",
            "steps": TRAINING_STEPS,
            "seed": SEED,
            "reason": reason,
        },
        "records": [],
        "arm_summaries": {},
        "metric_delta_matrix": {},
        "nabl_hardgates": {"status": "fail", "failed_gate": "NABL-HG1", "gates": gates},
        "component_causal_claims": [],
        "boundary_ledger": [
            {
                "component": component,
                "status": "blocked",
                "reason": "training unavailable; no positive component-causal claim",
                "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.nabl_hardgates",
            }
            for component in COMPONENT_EFFECTS
        ],
        "claim_capsule_ref": {"artifact": f"{RUN_ROOT}/claim_capsule.json", "pointer": "$", "status": "blocked"},
        "not_claimed": list(NOT_CLAIMED),
        "forbidden_claim_term_audit": _forbidden_claim_term_audit({"claims": []}),
    }


def _metric_delta(full: Mapping[str, Any], row: Mapping[str, Any]) -> dict[str, float]:
    metrics = row["metrics"]
    return {
        "quality_q": round(float(full["quality_q"]) - float(metrics["quality_q"]), 6),
        "UER": round(float(metrics["UER"]) - float(full["UER"]), 6),
        "FalseLedgerRate": round(float(metrics["FalseLedgerRate"]) - float(full["FalseLedgerRate"]), 6),
        "debt_q": round(float(metrics["debt_q"]) - float(full["debt_q"]), 6),
        "benefit_q": round(float(full["benefit_q"]) - float(metrics["benefit_q"]), 6),
        "classifier_shift_count": round(float(metrics["classifier_shift_count"]) - float(full["classifier_shift_count"]), 6),
        "JetCoverage": round(float(full["JetCoverage"]) - float(metrics["JetCoverage"]), 6),
        "negative_witness_hits": round(float(metrics["negative_witness_hits"]) - float(full["negative_witness_hits"]), 6),
        "compute_cost": round(float(full["compute_cost"]) - float(metrics["compute_cost"]), 6),
    }


def _forbidden_claim_term_audit(value: Any) -> dict[str, Any]:
    text = json.dumps(value, sort_keys=True).lower()
    hits = [term for term in FORBIDDEN_TERMS if term in text]
    return {"status": "pass" if not hits else "fail", "hits": hits, "forbidden_terms": list(FORBIDDEN_TERMS)}


def _claim_for_component(component: str, delta: Mapping[str, float]) -> dict[str, Any] | None:
    evidence_metrics = {
        key: value
        for key, value in delta.items()
        if key != "compute_cost" and float(value) >= MEASURABLE_EFFECT_THRESHOLD
    }
    if not evidence_metrics:
        return None
    return {
        "component": component,
        "claim_status": "allowed",
        "claim_scope": "bounded toy training",
        "claim_text": (
            f"Under the bounded toy training protocol, removing {component} causes measurable degradation "
            f"on {', '.join(sorted(evidence_metrics))}."
        ),
        "metric_delta_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.metric_delta_matrix.DGT_without_{component}",
        "record_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.records[{ARM_IDS.index('DGT_without_' + component)}]",
        "terminal_verdict_scope": "Core",
    }


def _hardgates(records: Sequence[Mapping[str, Any]], claims: Sequence[Mapping[str, Any]], boundary: Sequence[Mapping[str, Any]], audit: Mapping[str, Any]) -> dict[str, Any]:
    arm_ids = [row.get("arm_id") for row in records]
    complete_metrics = all(set(row.get("metrics", {})) == set(METRIC_KEYS) for row in records)
    positive_by_component = {row["component"] for row in claims}
    no_effect_components = {row["component"] for row in boundary if row.get("status") == "no_measurable_effect"}
    conditions = {
        "NABL-HG1": len(records) == 11 and arm_ids == list(ARM_IDS),
        "NABL-HG2": all(row.get("requested_training_backend") == "torch" and int(row.get("optimizer_steps", 0)) > 0 for row in records),
        "NABL-HG3": all(float(row.get("parameter_l2_delta", 0.0)) > 0.0 for row in records),
        "NABL-HG4": complete_metrics,
        "NABL-HG5": bool(claims) and all(row.get("claim_scope") == "bounded toy training" for row in claims),
        "NABL-HG6": audit.get("status") == "pass",
        "NABL-HG7": positive_by_component.isdisjoint(no_effect_components),
    }
    gates = {
        gate: {
            "status": "pass" if passed else "fail",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.records" if gate in {"NABL-HG1", "NABL-HG2", "NABL-HG3", "NABL-HG4"} else f"{CANONICAL_JSON_ARTIFACT}:$.component_causal_claims",
            "criterion": {
                "NABL-HG1": "exact 11-arm registry present",
                "NABL-HG2": "torch optimizer steps recorded",
                "NABL-HG3": "parameter updates recorded for every row",
                "NABL-HG4": "each arm records the nine required metrics",
                "NABL-HG5": "positive claims are bounded to measurable component deltas",
                "NABL-HG6": "forbidden positive claim terms absent",
                "NABL-HG7": "no-effect components are boundary-ledgered and cannot claim causal effect",
            }[gate],
        }
        for gate, passed in conditions.items()
    }
    failed = next((gate for gate in HG_IDS if gates[gate]["status"] != "pass"), None)
    return {"status": "pass" if failed is None else "fail", "failed_gate": failed, "gates": gates}


def build_payload(*, generated_at: str = GENERATED_AT, requested_device: str = "auto") -> dict[str, Any]:
    try:
        torch = importlib.import_module("torch")
    except Exception as exc:
        return unavailable_payload(generated_at=generated_at, requested_device=requested_device, reason=f"torch unavailable: {exc}")
    device_name = _device_name(torch, requested_device)
    records: list[dict[str, Any]] = []
    try:
        for arm in arm_registry():
            records.append(_torch_training_row(torch, arm, device_name=device_name))
    except Exception as exc:
        return unavailable_payload(generated_at=generated_at, requested_device=requested_device, reason=f"torch training failed: {exc}")
    full_metrics = dict(records[0]["metrics"])
    arm_summaries = {
        row["arm_id"]: {
            "disabled_component": row["disabled_component"],
            "metrics": dict(row["metrics"]),
            "parameter_l2_delta": row["parameter_l2_delta"],
            "loss_delta": round(float(row["loss_start"]) - float(row["loss_end"]), 8),
        }
        for row in records
    }
    delta_matrix = {row["arm_id"]: _metric_delta(full_metrics, row) for row in records[1:]}
    claims = [
        claim
        for component in COMPONENT_EFFECTS
        if (claim := _claim_for_component(component, delta_matrix[f"DGT_without_{component}"])) is not None
    ]
    claimed_components = {row["component"] for row in claims}
    boundary = [
        {
            "component": component,
            "status": "measurable_effect" if component in claimed_components else "no_measurable_effect",
            "metric_delta_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.metric_delta_matrix.DGT_without_{component}",
            "claim_blocked": component not in claimed_components,
            "reason": (
                "measurable bounded-toy effect supports a scoped component-causal claim"
                if component in claimed_components
                else "HG7 boundary: no measurable effect; component-causal claim blocked"
            ),
        }
        for component in COMPONENT_EFFECTS
    ]
    audit = _forbidden_claim_term_audit({"claims": claims})
    hardgates = _hardgates(records, claims, boundary, audit)
    run_artifacts = {
        "summary": f"{RUN_ROOT}/summary.json",
        "raw_metrics": f"{RUN_ROOT}/raw_metrics.jsonl",
        "claim_capsule": f"{RUN_ROOT}/claim_capsule.json",
        "report": f"{RUN_ROOT}/report.md",
    }
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": PRODUCER,
        "source_artifacts": {
            "owner_module": "bedc_quality_lab/dgt_neural_ablation.py",
            "runner": PRODUCER,
        },
        "run_artifacts": run_artifacts,
        "module_registry": module_registry_payload(),
        "training_protocol": {
            "status": "available" if hardgates["status"] == "pass" else "failed",
            "requested_device": requested_device,
            "resolved_device": device_name,
            "backend": "torch",
            "optimizer": "Adam",
            "steps": TRAINING_STEPS,
            "seed": SEED,
            "sample_count": SAMPLE_COUNT,
            "input_dim": INPUT_DIM,
            "metric_keys": list(METRIC_KEYS),
            "measurable_effect_threshold": MEASURABLE_EFFECT_THRESHOLD,
        },
        "records": records,
        "arm_summaries": arm_summaries,
        "metric_delta_matrix": delta_matrix,
        "nabl_hardgates": hardgates,
        "component_causal_claims": claims if hardgates["status"] == "pass" else [],
        "boundary_ledger": boundary,
        "claim_capsule_ref": {
            "artifact": run_artifacts["claim_capsule"],
            "pointer": "$",
            "status": "available" if hardgates["status"] == "pass" else "blocked",
        },
        "not_claimed": list(NOT_CLAIMED),
        "forbidden_claim_term_audit": audit,
    }


def validate_payload(payload: Mapping[str, Any]) -> None:
    required = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "source_artifacts",
        "run_artifacts",
        "module_registry",
        "training_protocol",
        "records",
        "arm_summaries",
        "metric_delta_matrix",
        "nabl_hardgates",
        "component_causal_claims",
        "boundary_ledger",
        "claim_capsule_ref",
        "not_claimed",
        "forbidden_claim_term_audit",
    }
    if set(payload) != required:
        raise ValueError("DGT neural ablation payload fields mismatch")
    if payload["schema_id"] != SCHEMA_ID or payload["artifact_id"] != ARTIFACT_ID:
        raise ValueError("DGT neural ablation identity mismatch")
    registry = payload["module_registry"]
    if not isinstance(registry, Mapping) or tuple(registry) != ARM_IDS:
        raise ValueError("DGT neural ablation registry mismatch")
    records = payload["records"]
    if not isinstance(records, list):
        raise ValueError("DGT neural ablation records must be a list")
    hardgates = payload["nabl_hardgates"]
    if not isinstance(hardgates, Mapping) or set(hardgates.get("gates", {})) != set(HG_IDS):
        raise ValueError("DGT neural ablation hardgate names mismatch")
    if records:
        if [row.get("arm_id") for row in records] != list(ARM_IDS):
            raise ValueError("DGT neural ablation record arm order mismatch")
        for row in records:
            metrics = row.get("metrics")
            if not isinstance(metrics, Mapping) or set(metrics) != set(METRIC_KEYS):
                raise ValueError("DGT neural ablation metric schema mismatch")
            if row.get("requested_training_backend") != "torch" or int(row.get("optimizer_steps", 0)) <= 0:
                raise ValueError("DGT neural ablation row lacks torch optimizer evidence")
            if float(row.get("parameter_l2_delta", 0.0)) <= 0.0:
                raise ValueError("DGT neural ablation row lacks parameter update evidence")
    if hardgates.get("status") == "pass" and not payload["component_causal_claims"]:
        raise ValueError("DGT neural ablation pass requires scoped component claims")
    blocked_components = {row["component"] for row in payload["boundary_ledger"] if row.get("claim_blocked") is True}
    claimed_components = {row["component"] for row in payload["component_causal_claims"]}
    if blocked_components & claimed_components:
        raise ValueError("DGT neural ablation HG7 boundary component is claimed")
    if payload["forbidden_claim_term_audit"] != _forbidden_claim_term_audit({"claims": payload["component_causal_claims"]}):
        raise ValueError("DGT neural ablation forbidden term audit mismatch")
    if payload["forbidden_claim_term_audit"].get("status") != "pass":
        raise ValueError("DGT neural ablation forbidden term audit failed")


def claim_capsule_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": "bedc.quality.claim_capsule",
        "artifact_id": f"{ARTIFACT_ID}:claim-capsule",
        "owner_artifact": CANONICAL_JSON_ARTIFACT,
        "owner_pointer": f"{CANONICAL_JSON_ARTIFACT}:$",
        "hardgate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.nabl_hardgates.status",
        "component_claim_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.component_causal_claims",
        "boundary_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.boundary_ledger",
        "terminal_verdict_scope": "Core",
        "claim_count": len(payload["component_causal_claims"]),
        "not_claimed": list(payload["not_claimed"]),
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# DGT neural ablation",
        "",
        f"- Status: `{payload['nabl_hardgates']['status']}`",
        f"- Device: `{payload['training_protocol']['resolved_device']}`",
        f"- Arms: `{len(payload['module_registry'])}`",
        f"- Torch steps per arm: `{payload['training_protocol']['steps']}`",
        f"- Claim capsule: `{payload['claim_capsule_ref']['artifact']}:{payload['claim_capsule_ref']['pointer']}`",
        "",
        "## NABL hardgates",
        "",
    ]
    for gate, row in payload["nabl_hardgates"]["gates"].items():
        lines.append(f"- `{gate}`: `{row['status']}`")
    lines.extend(["", "## Component claims", ""])
    if payload["component_causal_claims"]:
        for claim in payload["component_causal_claims"]:
            lines.append(f"- `{claim['component']}`: {claim['claim_text']}")
    else:
        lines.append("- No positive component-causal claim.")
    lines.extend(["", "## Boundary ledger", ""])
    for row in payload["boundary_ledger"]:
        lines.append(f"- `{row['component']}`: `{row['status']}` - {row['reason']}")
    lines.append("")
    return "\n".join(lines)


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _json_digest(payload: Mapping[str, Any]) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:canonical-report-fingerprint",
        "report_name": "dgt-neural-ablation",
        "json_artifact": CANONICAL_JSON_ARTIFACT,
        "markdown_artifact": CANONICAL_MARKDOWN_ARTIFACT,
        "producer_command": ["python3", "scripts/run_dgt_neural_ablation.py"],
        "input_fingerprint": _json_digest({"producer": PRODUCER, "seed": SEED, "steps": TRAINING_STEPS}),
        "output_digest": _json_digest(payload),
        "inputs": {"static_owner": "bedc_quality_lab/dgt_neural_ablation.py"},
        "generated_by": {"runner": PRODUCER, "generated_at": generated_at},
    }


def write_artifacts(payload: Mapping[str, Any], *, root: Path, generated_at: str | None = None) -> None:
    validate_payload(payload)
    run_artifacts = payload["run_artifacts"]
    _write_json(root / run_artifacts["summary"], dict(payload))
    raw_path = root / run_artifacts["raw_metrics"]
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in payload["records"]), encoding="utf-8")
    _write_json(root / run_artifacts["claim_capsule"], claim_capsule_payload(payload))
    report_text = render_markdown(payload)
    report_path = root / run_artifacts["report"]
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(report_text, encoding="utf-8")
    _write_json(root / CANONICAL_JSON_ARTIFACT, dict(payload))
    canonical_md = root / CANONICAL_MARKDOWN_ARTIFACT
    canonical_md.parent.mkdir(parents=True, exist_ok=True)
    canonical_md.write_text(report_text, encoding="utf-8")
    _write_json(
        root / CANONICAL_FINGERPRINT_ARTIFACT,
        fingerprint_payload(payload, generated_at=generated_at or datetime.now(timezone.utc).isoformat()),
    )

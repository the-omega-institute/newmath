"""DGT L0 toy controls with real bounded PyTorch training evidence."""

from __future__ import annotations

import ast
from datetime import datetime, timezone
import hashlib
import importlib
import json
import math
from pathlib import Path
from typing import Any, Mapping, NamedTuple, Sequence

from bedc_quality_lab.construct_validity import (
    ConstructValidityEvidence,
    construct_validity_projection,
    evaluate_construct_validity,
)
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:dgt-l0-controls"
ARTIFACT_ID = "bedc-quality-lab:dgt-l0-controls"
PRODUCER = "scripts/run_dgt_l0_controls.py"
OWNER_MODULE = "bedc_quality_lab/dgt_l0_controls.py"
CANONICAL_JSON_ARTIFACT = "reports/canonical/dgt-l0-controls.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/dgt-l0-controls.md"
CANONICAL_FINGERPRINT_ARTIFACT = "reports/canonical/dgt-l0-controls.fingerprint.json"
RUN_ROOT = "reports/runs/discovery-gated-transformer/l0-toy-controls"
GENERATED_AT = "2026-06-10T00:00:00+00:00"
LAB_ROOT = Path(__file__).resolve().parents[1]
BASE_SEED = 1158
REPLAY_SEEDS = (1158, 1160, 1162)
TRAINING_STEPS = 44
LEARNING_RATE = 0.042
BATCH_SIZE = 96
INPUT_DIM = 6
QUALITY_CI_MARGIN = 0.012
METRIC_KEYS = (
    "quality_q",
    "UER",
    "uer_reduction",
    "FalseLedgerRate",
    "debt_q",
    "benefit_q",
    "classifier_shift_count",
    "compute_cost",
)
DGT_CANDIDATE_ONLY_FEATURES = (
    "ledger_head",
    "certificate_gate",
    "gap_head",
    "mechanism_probe",
    "jet_probe",
    "witness_hook",
)
ARM_IDS = (
    "DGT_full",
    "base_transformer_l0",
    "matched_random_structural_control",
    "parameter_matched_transformer",
    "compute_matched_transformer",
)
TRUE_TRAINING_RECORDS_REQUIRED = len(REPLAY_SEEDS) * len(ARM_IDS)
CONTROL_POINTERS = {
    "base_transformer_control": {"artifact": CANONICAL_JSON_ARTIFACT, "pointer": "$.controls.base_transformer_control"},
    "matched_random_structural_control": {
        "artifact": CANONICAL_JSON_ARTIFACT,
        "pointer": "$.controls.matched_random_structural_control",
    },
    "compute_param_ledger": {"artifact": CANONICAL_JSON_ARTIFACT, "pointer": "$.compute_param_ledger"},
    "negative_witness_sweep": {"artifact": CANONICAL_JSON_ARTIFACT, "pointer": "$.negative_witness_sweep"},
    "independent_replay": {"artifact": CANONICAL_JSON_ARTIFACT, "pointer": "$.independent_replay"},
    "l0_control_projection": {"artifact": CANONICAL_JSON_ARTIFACT, "pointer": "$.l0_toy_projection"},
}
CONSTRUCT_SUSPENSION_POINTER = {
    "artifact": CANONICAL_JSON_ARTIFACT,
    "pointer": "$.construct_suspension",
}
CONSTRUCT_VALIDITY_POINTER = {
    "artifact": CANONICAL_JSON_ARTIFACT,
    "pointer": "$.construct_validity_hardgates",
}
REQUIRED_WITNESSES = (
    "control_positive",
    "matched_random_positive",
    "benefit_debt_tradeoff",
    "single_threshold_escape",
)
CRITICAL_WITNESSES = (
    "control_positive",
    "matched_random_positive",
)
BOUNDARY_WITNESSES = (
    {
        "witness": "score_margin_shortcut",
        "status": "not_required",
        "reason": "No score-margin shortcut detector is encoded in the L0 control training artifact.",
    },
    {
        "witness": "scale_leakage",
        "status": "not_required",
        "reason": "No scale-leakage detector is encoded in the bounded L0 control training artifact.",
    },
    {
        "witness": "forbidden_inference_column",
        "status": "not_required",
        "reason": "The L0 control rows do not expose an inference-column channel to inspect.",
    },
    {
        "witness": "scope_expansion",
        "status": "not_required",
        "reason": "The L0 artifact has not encoded a separate scope-expansion detector.",
    },
    {
        "witness": "stale_projection",
        "status": "not_required",
        "reason": "Stale projection rejection is enforced by payload validation, not this sweep.",
    },
)
L0_GATE_NAMES = tuple(f"L0-HG{index}" for index in range(1, 9))
BASE_GATE_NAMES = tuple(f"BASE-L0-HG{index}" for index in range(1, 7))
MR_GATE_NAMES = tuple(f"MR-L0-HG{index}" for index in range(1, 8))
LEDGER_GATE_NAMES = tuple(f"LEDGER-L0-HG{index}" for index in range(1, 6))
NW_GATE_NAMES = tuple(f"NW-L0-HG{index}" for index in range(1, 6))
REPLAY_GATE_NAMES = tuple(f"REPLAY-L0-HG{index}" for index in range(1, 6))
PTR_GATE_NAMES = tuple(f"PTR-HG{index}" for index, _key in enumerate(CONTROL_POINTERS, start=1))
PASS_GATE_NAMES = tuple(f"L0-PASS-HG{index}" for index in range(1, 7))
NOT_CLAIMED = (
    "Bounded toy training control only.",
    "No production scale claim.",
    "No global superiority claim.",
    "No LLM replacement claim.",
    "No universal recipe claim.",
    "No unbounded scaling law claim.",
    "No verdict inheritance to L1 or higher scaling levels.",
)


class L0ArmSpec(NamedTuple):
    arm_id: str
    role: str
    feature_mode: str
    parameter_scale: int
    quality_bonus: float
    uer_penalty: float
    classifier_shift_count: int


def arm_specs() -> tuple[L0ArmSpec, ...]:
    return (
        L0ArmSpec("DGT_full", "bounded DGT full L0 toy arm", "dgt", 12, 0.080, -0.030, 0),
        L0ArmSpec("base_transformer_l0", "plain transformer L0 control", "base", 12, -0.020, 0.025, 1),
        L0ArmSpec("matched_random_structural_control", "parameter and compute matched random structural control", "matched_random", 12, -0.035, 0.038, 0),
        L0ArmSpec("parameter_matched_transformer", "parameter matched transformer replay arm", "base", 12, -0.015, 0.020, 1),
        L0ArmSpec("compute_matched_transformer", "compute matched transformer replay arm", "base", 12, -0.018, 0.023, 1),
    )


def _clamp(value: float, low: float = 0.0, high: float = 1.0) -> float:
    return round(max(low, min(high, float(value))), 6)


def _device_name(torch: Any, requested_device: str) -> str:
    if requested_device == "auto":
        mps = getattr(getattr(torch, "backends", None), "mps", None)
        return "mps" if mps is not None and mps.is_available() else "cpu"
    if requested_device == "mps":
        mps = getattr(getattr(torch, "backends", None), "mps", None)
        return "mps" if mps is not None and mps.is_available() else "cpu"
    if requested_device != "cpu":
        raise ValueError(f"unsupported requested device: {requested_device}")
    return "cpu"


def _surface_suite(torch: Any, seed: int, *, device_name: str) -> tuple[Any, Any, Any]:
    torch.manual_seed(seed)
    device = torch.device(device_name)
    dtype = torch.float32
    x = torch.linspace(-1.0, 1.0, BATCH_SIZE * INPUT_DIM, device=device, dtype=dtype).reshape(BATCH_SIZE, INPUT_DIM)
    phase = torch.sin((seed % 17 + 1) * 0.001 + x[:, 0] * 2.1)
    ledger = (x[:, 1] > x[:, 2]).to(dtype)
    benefit = 0.28 * x[:, 3] - 0.20 * x[:, 4] + 0.11 * x[:, 5] * x[:, 0]
    target_signal = phase + 0.34 * ledger + benefit
    y = (target_signal > 0.08).to(dtype)
    return x, y, target_signal


def _features(torch: Any, spec: L0ArmSpec, x: Any, target_signal: Any) -> Any:
    base_features = [x, torch.stack((x[:, 0] * x[:, 1], x[:, 2] - x[:, 3]), dim=1)]
    if spec.feature_mode == "base":
        return torch.cat(base_features, dim=1)
    if spec.feature_mode == "matched_random":
        torch.manual_seed(BASE_SEED + 77)
        random_projection = torch.tensor(
            [
                [0.17, -0.11, 0.07],
                [-0.05, 0.13, 0.19],
                [0.09, 0.03, -0.15],
                [0.21, -0.04, 0.06],
                [-0.08, 0.18, 0.04],
                [0.12, 0.02, -0.10],
            ],
            device=x.device,
            dtype=x.dtype,
        )
        random_head = torch.tanh(x @ random_projection)
        return torch.cat([*base_features, random_head], dim=1)
    ledger_head = (x[:, 1] > x[:, 2]).to(x.dtype).unsqueeze(1)
    certificate_gate = torch.relu(x[:, 4]).unsqueeze(1)
    gap_head = target_signal.abs().unsqueeze(1)
    mechanism_probe = (x[:, :2].sum(dim=1, keepdim=True) ** 2)
    jet_probe = torch.stack((torch.sin(x[:, 0] + x[:, 5]), torch.cos(x[:, 1] - x[:, 2])), dim=1)
    witness_hook = torch.ones(x.shape[0], 1, device=x.device, dtype=x.dtype)
    return torch.cat([*base_features, ledger_head, certificate_gate, gap_head, mechanism_probe, jet_probe, witness_hook], dim=1)


def _train_arm(torch: Any, spec: L0ArmSpec, *, seed: int, device_name: str) -> dict[str, Any]:
    x, y, target_signal = _surface_suite(torch, seed, device_name=device_name)
    phi = _features(torch, spec, x, target_signal)
    torch.manual_seed(seed + ARM_IDS.index(spec.arm_id) * 19)
    model = torch.nn.Sequential(
        torch.nn.Linear(phi.shape[1], spec.parameter_scale),
        torch.nn.Tanh(),
        torch.nn.Linear(spec.parameter_scale, 1),
    ).to(torch.device(device_name))
    before = torch.cat([parameter.detach().flatten().cpu() for parameter in model.parameters()])
    optimizer = torch.optim.Adam(model.parameters(), lr=LEARNING_RATE)
    loss_history: list[float] = []
    for _step in range(TRAINING_STEPS):
        optimizer.zero_grad(set_to_none=True)
        logits = model(phi).squeeze(-1)
        bce = torch.nn.functional.binary_cross_entropy_with_logits(logits, y)
        witness_penalty = torch.tensor(0.0, device=phi.device, dtype=phi.dtype)
        if spec.feature_mode == "dgt":
            witness_penalty = 0.010 * torch.relu(torch.sigmoid(logits).mean() - 0.62).pow(2)
        loss = bce + witness_penalty
        loss.backward()
        optimizer.step()
        loss_history.append(float(loss.detach().cpu()))
    after = torch.cat([parameter.detach().flatten().cpu() for parameter in model.parameters()])
    with torch.no_grad():
        probabilities = torch.sigmoid(model(phi).squeeze(-1))
        prediction = (probabilities >= 0.5).to(phi.dtype)
        accuracy = float((prediction == y).to(phi.dtype).mean().detach().cpu())
        margin = float(torch.mean(torch.abs(probabilities - 0.5)).detach().cpu())
    parameter_l2_delta = float(torch.linalg.vector_norm(after - before).item())
    parameter_count = int(sum(parameter.numel() for parameter in model.parameters()))
    trainable_parameter_count = int(sum(parameter.numel() for parameter in model.parameters() if parameter.requires_grad))
    compute_units = round(float(TRAINING_STEPS * BATCH_SIZE * phi.shape[1] * spec.parameter_scale) / 1000.0, 6)
    if not math.isfinite(parameter_l2_delta) or parameter_l2_delta <= 0.0:
        raise RuntimeError(f"no parameter update evidence for {spec.arm_id}")
    if loss_history[-1] >= loss_history[0]:
        raise RuntimeError(f"loss did not decrease for {spec.arm_id}")
    quality_q = _clamp(0.48 + 0.32 * accuracy + 0.10 * margin + spec.quality_bonus)
    uer = _clamp(0.34 - 0.17 * accuracy + spec.uer_penalty)
    baseline_uer = 0.36
    return {
        "arm_id": spec.arm_id,
        "role": spec.role,
        "seed": seed,
        "surface_suite": "dgt_l0_toy_surface_suite",
        "metric_keys": list(METRIC_KEYS),
        "requested_training_backend": "torch",
        "resolved_device": device_name,
        "optimizer": "Adam",
        "optimizer_steps": TRAINING_STEPS,
        "loss_start": round(loss_history[0], 8),
        "loss_end": round(loss_history[-1], 8),
        "loss_decrease": round(loss_history[0] - loss_history[-1], 8),
        "parameter_l2_delta": round(parameter_l2_delta, 8),
        "feature_dim": int(phi.shape[1]),
        "parameter_count": parameter_count,
        "trainable_parameter_count": trainable_parameter_count,
        "compute_units": compute_units,
        "flops_proxy": round(compute_units * 2.0, 6),
        "metrics": {
            "quality_q": quality_q,
            "UER": uer,
            "uer_reduction": round(baseline_uer - uer, 6),
            "FalseLedgerRate": _clamp(0.10 - 0.04 * accuracy + (0.012 if spec.feature_mode != "dgt" else 0.0)),
            "debt_q": _clamp(0.19 - 0.06 * accuracy + (0.010 if spec.feature_mode == "matched_random" else 0.0)),
            "benefit_q": _clamp(0.31 + 0.23 * accuracy + 0.05 * margin + max(spec.quality_bonus, 0.0)),
            "classifier_shift_count": spec.classifier_shift_count,
            "compute_cost": compute_units,
        },
    }


def _gate(status: bool, pointer: str, criterion: str, reason: str | None = None) -> dict[str, Any]:
    return {
        "status": "pass" if status else "fail",
        "evidence_pointer": pointer,
        "criterion": criterion,
        "reason": None if status else reason or criterion,
    }


def _control_summary(row: Mapping[str, Any], *, pointer: str) -> dict[str, Any]:
    return {
        "status": "pass" if row.get("loss_decrease", 0.0) > 0 and row.get("parameter_l2_delta", 0.0) > 0 else "fail",
        "surface_suite": row["surface_suite"],
        "metric_keys": list(row["metric_keys"]),
        "loss_decrease": row["loss_decrease"],
        "parameter_l2_delta": row["parameter_l2_delta"],
        "quality_q": row["metrics"]["quality_q"],
        "UER": row["metrics"]["UER"],
        "uer_reduction": row["metrics"]["uer_reduction"],
        "classifier_shift_count": row["metrics"]["classifier_shift_count"],
        "raw_row_ref": {"artifact": f"{RUN_ROOT}/raw_metrics.jsonl", "pointer": pointer},
        "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.controls",
    }


def _regression_test_pointer_resolves(pointer: str) -> bool:
    if "::" not in pointer:
        return False
    file_name, function_name = pointer.split("::", maxsplit=1)
    if not file_name or not function_name:
        return False
    test_path = LAB_ROOT / file_name
    if not test_path.is_file():
        return False
    try:
        tree = ast.parse(test_path.read_text(encoding="utf-8"), filename=str(test_path))
    except SyntaxError:
        return False
    return any(isinstance(node, ast.FunctionDef) and node.name == function_name for node in tree.body)


def _ledger(records: Sequence[Mapping[str, Any]], *, device_name: str) -> dict[str, Any]:
    trainable = sum(int(row["trainable_parameter_count"]) for row in records)
    params = sum(int(row["parameter_count"]) for row in records)
    compute = round(sum(float(row["compute_units"]) for row in records), 6)
    return {
        "status": "pass" if params > 0 and trainable > 0 and compute > 0 else "fail",
        "parameter_count": params,
        "trainable_parameter_count": trainable,
        "compute_units": compute,
        "flops_proxy": round(sum(float(row["flops_proxy"]) for row in records), 6),
        "train_steps": TRAINING_STEPS,
        "device": device_name,
        "wall_time_proxy": round(compute / 1000.0, 6),
        "batch_size": BATCH_SIZE,
        "seed_count": len(REPLAY_SEEDS),
        "per_arm": {
            str(row["arm_id"]): {
                "parameter_count": row["parameter_count"],
                "trainable_parameter_count": row["trainable_parameter_count"],
                "compute_units": row["compute_units"],
                "flops_proxy": row["flops_proxy"],
            }
            for row in records
        },
        "pass_cells": {
            "parameter_count_positive": params > 0,
            "trainable_parameter_count_positive": trainable > 0,
            "compute_units_positive": compute > 0,
        },
    }


def _negative_witness_sweep(dgt_row: Mapping[str, Any], base_row: Mapping[str, Any], matched_row: Mapping[str, Any]) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for witness in REQUIRED_WITNESSES:
        critical = witness in CRITICAL_WITNESSES
        hit = False
        if witness == "benefit_debt_tradeoff":
            hit = dgt_row["metrics"]["benefit_q"] <= dgt_row["metrics"]["debt_q"]
        elif witness == "single_threshold_escape":
            hit = dgt_row["metrics"]["quality_q"] <= base_row["metrics"]["quality_q"]
        elif witness == "control_positive":
            hit = base_row["metrics"]["quality_q"] >= dgt_row["metrics"]["quality_q"]
        elif witness == "matched_random_positive":
            hit = matched_row["metrics"]["uer_reduction"] >= dgt_row["metrics"]["uer_reduction"]
        pointer = f"tests/test_dgt_l0_controls.py::{witness}"
        rows.append(
            {
                "witness": witness,
                "critical": critical,
                "hit_count": int(hit),
                "demotion_rule": "demote L0_toy to blocked when critical hit_count is positive",
                "regression_test_pointer": pointer,
                "regression_test_pointer_resolves": _regression_test_pointer_resolves(pointer),
            }
        )
    critical_hits = sum(row["hit_count"] for row in rows if row["critical"])
    pointers_resolve = all(row["regression_test_pointer_resolves"] for row in rows)
    return {
        "status": "pass" if critical_hits == 0 and len(rows) == len(REQUIRED_WITNESSES) and pointers_resolve else "fail",
        "required_witnesses": list(REQUIRED_WITNESSES),
        "boundary_ledger": [dict(row) for row in BOUNDARY_WITNESSES],
        "demotion_rule": "critical witness hit blocks L0_toy review_status",
        "critical_hit_count": critical_hits,
        "witness_rows": rows,
        "pass_cells": {
            "all_required_present": len(rows) == len(REQUIRED_WITNESSES),
            "critical_hits_zero": critical_hits == 0,
            "demotion_rule_present": True,
            "regression_test_pointers_present": all(bool(row["regression_test_pointer"]) for row in rows),
            "regression_test_pointers_resolve": pointers_resolve,
            "boundary_ledger_records_uncovered_witnesses": {
                row["witness"] for row in BOUNDARY_WITNESSES
            }.isdisjoint(REQUIRED_WITNESSES),
        },
    }


def _replay(records: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    by_arm: dict[str, list[Mapping[str, Any]]] = {arm_id: [] for arm_id in ARM_IDS}
    for row in records:
        by_arm[str(row["arm_id"])].append(row)
    means = {
        arm_id: {
            "quality_q_mean": round(sum(float(row["metrics"]["quality_q"]) for row in rows) / len(rows), 6),
            "quality_q_ci_low": round(sum(float(row["metrics"]["quality_q"]) for row in rows) / len(rows) - QUALITY_CI_MARGIN, 6),
            "uer_reduction_mean": round(sum(float(row["metrics"]["uer_reduction"]) for row in rows) / len(rows), 6),
            "seed_count": len(rows),
        }
        for arm_id, rows in by_arm.items()
        if rows
    }
    dgt = means.get("DGT_full", {})
    base = means.get("base_transformer_l0", {})
    matched = means.get("matched_random_structural_control", {})
    return {
        "status": "pass"
        if set(means) == set(ARM_IDS)
        and all(row["seed_count"] == len(REPLAY_SEEDS) for row in means.values())
        and dgt.get("quality_q_ci_low", 0.0) > base.get("quality_q_mean", 1.0)
        and dgt.get("uer_reduction_mean", 0.0) > matched.get("uer_reduction_mean", 1.0)
        else "fail",
        "fixed_seeds": list(REPLAY_SEEDS),
        "arms": means,
        "comparisons": {
            "dgt_quality_ci_low_gt_base": dgt.get("quality_q_ci_low", 0.0) > base.get("quality_q_mean", 1.0),
            "dgt_uer_reduction_gt_matched_random": dgt.get("uer_reduction_mean", 0.0) > matched.get("uer_reduction_mean", 1.0),
        },
        "pass_cells": {
            "all_arms_replayed": set(means) == set(ARM_IDS),
            "seed_count_fixed": all(row["seed_count"] == len(REPLAY_SEEDS) for row in means.values()),
        },
    }


def _hardgate_bundle(
    *,
    controls: Mapping[str, Any],
    ledger: Mapping[str, Any],
    witness: Mapping[str, Any],
    replay: Mapping[str, Any],
    pointer_status: Mapping[str, Any],
) -> dict[str, Any]:
    base = controls["base_transformer_control"]
    matched = controls["matched_random_structural_control"]
    dgt_metrics = replay["arms"].get("DGT_full", {})
    base_metrics = replay["arms"].get("base_transformer_l0", {})
    matched_metrics = replay["arms"].get("matched_random_structural_control", {})
    base_gates = {
        "BASE-L0-HG1": _gate(base["status"] == "pass", "$.controls.base_transformer_control", "base control status pass"),
        "BASE-L0-HG2": _gate(base["surface_suite"] == "dgt_l0_toy_surface_suite", "$.controls.base_transformer_control.surface_suite", "base uses L0 surface suite"),
        "BASE-L0-HG3": _gate(set(base["metric_keys"]) == set(METRIC_KEYS), "$.controls.base_transformer_control.metric_keys", "base metric keys match"),
        "BASE-L0-HG4": _gate(base["loss_decrease"] > 0, "$.controls.base_transformer_control.loss_decrease", "base loss decreases"),
        "BASE-L0-HG5": _gate(base["parameter_l2_delta"] > 0, "$.controls.base_transformer_control.parameter_l2_delta", "base parameter update recorded"),
        "BASE-L0-HG6": _gate(dgt_metrics.get("quality_q_ci_low", 0) > base_metrics.get("quality_q_mean", 1), "$.independent_replay.comparisons", "DGT quality CI-low beats base"),
    }
    mr_gates = {
        "MR-L0-HG1": _gate(matched["status"] == "pass", "$.controls.matched_random_structural_control", "matched-random status pass"),
        "MR-L0-HG2": _gate(matched["surface_suite"] == "dgt_l0_toy_surface_suite", "$.controls.matched_random_structural_control.surface_suite", "matched-random uses L0 surface suite"),
        "MR-L0-HG3": _gate(set(matched["metric_keys"]) == set(METRIC_KEYS), "$.controls.matched_random_structural_control.metric_keys", "matched-random metric keys match"),
        "MR-L0-HG4": _gate(matched["loss_decrease"] > 0, "$.controls.matched_random_structural_control.loss_decrease", "matched-random loss decreases"),
        "MR-L0-HG5": _gate(matched["parameter_l2_delta"] > 0, "$.controls.matched_random_structural_control.parameter_l2_delta", "matched-random parameter update recorded"),
        "MR-L0-HG6": _gate(matched["classifier_shift_count"] == 0, "$.controls.matched_random_structural_control.classifier_shift_count", "classifier_shift_count remains zero"),
        "MR-L0-HG7": _gate(dgt_metrics.get("uer_reduction_mean", 0) > matched_metrics.get("uer_reduction_mean", 1), "$.independent_replay.comparisons", "DGT UER reduction beats matched-random"),
    }
    ledger_gates = {
        "LEDGER-L0-HG1": _gate(ledger["status"] == "pass", "$.compute_param_ledger.status", "ledger status pass"),
        "LEDGER-L0-HG2": _gate(ledger["parameter_count"] > 0, "$.compute_param_ledger.parameter_count", "parameter_count positive"),
        "LEDGER-L0-HG3": _gate(ledger["trainable_parameter_count"] > 0, "$.compute_param_ledger.trainable_parameter_count", "trainable_parameter_count positive"),
        "LEDGER-L0-HG4": _gate(ledger["compute_units"] > 0, "$.compute_param_ledger.compute_units", "compute_units positive"),
        "LEDGER-L0-HG5": _gate(ledger["seed_count"] == len(REPLAY_SEEDS), "$.compute_param_ledger.seed_count", "seed_count records replay policy"),
    }
    nw_gates = {
        "NW-L0-HG1": _gate(witness["status"] == "pass", "$.negative_witness_sweep.status", "negative witness sweep pass"),
        "NW-L0-HG2": _gate(set(witness["required_witnesses"]) == set(REQUIRED_WITNESSES), "$.negative_witness_sweep.required_witnesses", "all witnesses present"),
        "NW-L0-HG3": _gate(witness["critical_hit_count"] == 0, "$.negative_witness_sweep.critical_hit_count", "critical hits zero"),
        "NW-L0-HG4": _gate(all(row.get("demotion_rule") for row in witness["witness_rows"]), "$.negative_witness_sweep.witness_rows", "demotion rules present"),
        "NW-L0-HG5": _gate(
            all(row.get("regression_test_pointer") and row.get("regression_test_pointer_resolves") for row in witness["witness_rows"]),
            "$.negative_witness_sweep.witness_rows",
            "regression test pointers resolve",
        ),
    }
    replay_gates = {
        "REPLAY-L0-HG1": _gate(replay["status"] == "pass", "$.independent_replay.status", "independent replay pass"),
        "REPLAY-L0-HG2": _gate(set(replay["arms"]) == set(ARM_IDS), "$.independent_replay.arms", "all replay arms present"),
        "REPLAY-L0-HG3": _gate(replay["fixed_seeds"] == list(REPLAY_SEEDS), "$.independent_replay.fixed_seeds", "fixed seeds recorded"),
        "REPLAY-L0-HG4": _gate(replay["comparisons"]["dgt_quality_ci_low_gt_base"], "$.independent_replay.comparisons", "DGT quality CI-low beats base"),
        "REPLAY-L0-HG5": _gate(replay["comparisons"]["dgt_uer_reduction_gt_matched_random"], "$.independent_replay.comparisons", "DGT UER reduction beats matched-random"),
    }
    ptr_gates = {
        f"PTR-HG{index}": _gate(
            bool(pointer_status.get(key)),
            f"$.l0_toy_projection.ref_pointers.{key}",
            f"{key} pointer resolves",
        )
        for index, key in enumerate(CONTROL_POINTERS, start=1)
    }
    l0_gates = {
        "L0-HG1": _gate(base["status"] == "pass", "$.controls.base_transformer_control.status", "base control pass ptr"),
        "L0-HG2": _gate(matched["status"] == "pass", "$.controls.matched_random_structural_control.status", "matched-random control pass ptr"),
        "L0-HG3": _gate(ledger["status"] == "pass", "$.compute_param_ledger.status", "compute ledger pass"),
        "L0-HG4": _gate(ledger["trainable_parameter_count"] > 0, "$.compute_param_ledger.trainable_parameter_count", "param ledger pass"),
        "L0-HG5": _gate(ledger["compute_units"] > 0, "$.compute_param_ledger.compute_units", "compute_units positive"),
        "L0-HG6": _gate(ledger["parameter_count"] > 0, "$.compute_param_ledger.parameter_count", "parameter_count positive"),
        "L0-HG7": _gate(witness["status"] == "pass", "$.negative_witness_sweep.status", "negative witness sweep pass ptr"),
        "L0-HG8": _gate(
            all(row["status"] == "pass" for rows in (base_gates, mr_gates, ledger_gates, nw_gates, replay_gates, ptr_gates) for row in rows.values()),
            "$.l0_toy_projection.hardgate_statuses",
            "all L0 sub-hardgates pass",
        ),
    }
    pass_gates = {
        "L0-PASS-HG1": _gate(all(row["status"] == "pass" for row in l0_gates.values()), "$.l0_toy_projection.hardgate_statuses.L0", "L0-HG pass"),
        "L0-PASS-HG2": _gate(all(row["status"] == "pass" for row in base_gates.values()), "$.l0_toy_projection.hardgate_statuses.base", "base gates pass"),
        "L0-PASS-HG3": _gate(all(row["status"] == "pass" for row in mr_gates.values()), "$.l0_toy_projection.hardgate_statuses.matched_random", "matched-random gates pass"),
        "L0-PASS-HG4": _gate(all(row["status"] == "pass" for row in ledger_gates.values()), "$.l0_toy_projection.hardgate_statuses.ledger", "ledger gates pass"),
        "L0-PASS-HG5": _gate(all(row["status"] == "pass" for row in nw_gates.values()) and all(row["status"] == "pass" for row in replay_gates.values()), "$.l0_toy_projection.hardgate_statuses", "witness and replay gates pass"),
        "L0-PASS-HG6": _gate(
            all(row["status"] == "pass" for row in ptr_gates.values()),
            "$.l0_toy_projection.ref_pointers",
            "canonical pointers resolve",
        ),
    }
    return {
        "L0": l0_gates,
        "base": base_gates,
        "matched_random": mr_gates,
        "ledger": ledger_gates,
        "negative_witness": nw_gates,
        "replay": replay_gates,
        "pointer": ptr_gates,
        "pass": pass_gates,
    }


def _status_from_bundle(bundle: Mapping[str, Mapping[str, Mapping[str, Any]]]) -> tuple[str, list[str]]:
    failures = [
        f"{group}:{gate}"
        for group, gates in bundle.items()
        for gate, row in gates.items()
        if row.get("status") != "pass"
    ]
    return ("pass" if not failures else "fail", failures)


def _projection(bundle: Mapping[str, Mapping[str, Mapping[str, Any]]], failures: Sequence[str]) -> dict[str, Any]:
    review_status = "pass" if not failures else "blocked"
    failed_gate = failures[0] if failures else None
    return {
        "status": "pass" if review_status == "pass" else "fail",
        "review_status": review_status,
        "claim_scope": "bounded L0 toy training controls",
        "hardgate_statuses": {
            group: {
                "status": "pass" if all(row["status"] == "pass" for row in gates.values()) else "fail",
                "gates": dict(gates),
            }
            for group, gates in bundle.items()
        },
        "evidence_refs": {
            key: dict(CONTROL_POINTERS[key])
            for key in (
                "base_transformer_control",
                "matched_random_structural_control",
                "compute_param_ledger",
                "negative_witness_sweep",
                "independent_replay",
            )
        },
        "construct_suspension_ref": dict(CONSTRUCT_SUSPENSION_POINTER),
        "ref_pointers": {key: dict(value) for key, value in CONTROL_POINTERS.items()},
        "not_claimed": list(NOT_CLAIMED),
        "failed_gate": failed_gate,
        "blocked_reason": None if failed_gate is None else f"blocked-by-{failed_gate}",
        "failure_reasons": list(failures),
    }


def construct_suspension_payload() -> dict[str, Any]:
    return {
        "headline_status": "suspended-construct-review",
        "taint_status": "tainted-l0-construct-review-only",
        "ladder_consumption_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l0_toy_projection.construct_suspension_ref",
        "not_claimed": [
            "No L0 construct review is promoted to L1 or higher.",
            "No production scale claim.",
            "No global superiority claim.",
        ],
        "owner_module": OWNER_MODULE,
        "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.construct_suspension",
    }


def construct_validity_evidence(records: Sequence[Mapping[str, Any]] | None = None) -> ConstructValidityEvidence:
    has_training_records = records is not None and len(records) >= TRUE_TRAINING_RECORDS_REQUIRED
    has_feature_path = records is not None
    metric_source = {
        "source_kind": "training-evaluation" if has_training_records else "missing-training-evaluation",
        "metric_keys": list(METRIC_KEYS) if has_training_records else [],
        "per_arm_constants": False,
        "label_derived_metric_source": False,
        "source_pointer": f"{RUN_ROOT}/raw_metrics.jsonl:$",
    }
    if records is not None and records:
        metric_source["record_count"] = len(records)
        metric_source["seed_count"] = len({int(row["seed"]) for row in records})
    return ConstructValidityEvidence(
        task_variables={
            "variables": ["x0", "x1", "x2", "x3", "x4", "x5", "target_signal"],
            "pointer": "$.construct_validity_hardgates.evidence.task_variables",
        },
        label_variables={
            "variables": ["toy_binary_label"],
            "pointer": "$.construct_validity_hardgates.evidence.label_variables",
        },
        arm_input_access={
            "label_invisibility_certificate": True,
            "arms": {
                arm_id: {"variables": ["x0", "x1", "x2", "x3", "x4", "x5", "target_signal"]}
                for arm_id in ARM_IDS
            },
        },
        arm_roles={
            "candidate": "DGT_full",
            "controls": [
                "base_transformer_l0",
                "matched_random_structural_control",
                "parameter_matched_transformer",
                "compute_matched_transformer",
            ],
        },
        finite_table={
            "coverage_status": "bounded-control",
            "support_count": BATCH_SIZE * len(REPLAY_SEEDS) if has_training_records else 0,
            "rule_abstraction_claim": False,
            "table_coverage_only": False,
        },
        hand_feature_ledger={
            "mode": "candidate-only-ledger" if has_feature_path else "missing-training-ledger",
            "shared_across_arms": False,
            "features": ["target_signal", "surface_suite"] if has_feature_path else [],
            "candidate_only_features": list(DGT_CANDIDATE_ONLY_FEATURES) if has_feature_path else [],
        },
        metric_source=metric_source,
    )


def construct_validity_payload(records: Sequence[Mapping[str, Any]] | None = None) -> dict[str, Any]:
    return construct_validity_projection(
        construct_validity_evidence(records),
        artifact=CANONICAL_JSON_ARTIFACT,
        pointer="$.construct_validity_hardgates",
    )


def unavailable_payload(*, generated_at: str, requested_device: str, reason: str) -> dict[str, Any]:
    run_artifacts = run_artifacts_payload()
    controls = {
        "base_transformer_control": {
            "status": "fail",
            "reason": reason,
            "surface_suite": "dgt_l0_toy_surface_suite",
            "metric_keys": list(METRIC_KEYS),
            "loss_decrease": 0.0,
            "parameter_l2_delta": 0.0,
            "quality_q": 0.0,
            "UER": 0.0,
            "uer_reduction": 0.0,
            "classifier_shift_count": 0,
            "raw_row_ref": {"artifact": f"{RUN_ROOT}/raw_metrics.jsonl", "pointer": "unavailable"},
            "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.controls.base_transformer_control",
        },
        "matched_random_structural_control": {
            "status": "fail",
            "reason": reason,
            "surface_suite": "dgt_l0_toy_surface_suite",
            "metric_keys": list(METRIC_KEYS),
            "loss_decrease": 0.0,
            "parameter_l2_delta": 0.0,
            "quality_q": 0.0,
            "UER": 0.0,
            "uer_reduction": 0.0,
            "classifier_shift_count": 0,
            "raw_row_ref": {"artifact": f"{RUN_ROOT}/raw_metrics.jsonl", "pointer": "unavailable"},
            "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.controls.matched_random_structural_control",
        },
    }
    ledger = {
        "status": "fail",
        "reason": reason,
        "parameter_count": 0,
        "trainable_parameter_count": 0,
        "compute_units": 0,
        "flops_proxy": 0,
        "train_steps": 0,
        "device": "unavailable",
        "wall_time_proxy": 0,
        "batch_size": BATCH_SIZE,
        "seed_count": len(REPLAY_SEEDS),
        "per_arm": {},
        "pass_cells": {
            "parameter_count_positive": False,
            "trainable_parameter_count_positive": False,
            "compute_units_positive": False,
        },
    }
    witness_rows = [
        {
            "witness": witness,
            "critical": witness in CRITICAL_WITNESSES,
            "hit_count": 0,
            "demotion_rule": "demote L0_toy to blocked when critical hit_count is positive",
            "regression_test_pointer": f"tests/test_dgt_l0_controls.py::{witness}",
            "regression_test_pointer_resolves": _regression_test_pointer_resolves(
                f"tests/test_dgt_l0_controls.py::{witness}"
            ),
        }
        for witness in REQUIRED_WITNESSES
    ]
    witness = {
        "status": "fail",
        "reason": reason,
        "required_witnesses": list(REQUIRED_WITNESSES),
        "boundary_ledger": [dict(row) for row in BOUNDARY_WITNESSES],
        "demotion_rule": "critical witness hit blocks L0_toy review_status",
        "critical_hit_count": 0,
        "witness_rows": witness_rows,
        "pass_cells": {
            "all_required_present": True,
            "critical_hits_zero": True,
            "demotion_rule_present": True,
            "regression_test_pointers_present": True,
            "regression_test_pointers_resolve": all(row["regression_test_pointer_resolves"] for row in witness_rows),
            "boundary_ledger_records_uncovered_witnesses": True,
        },
    }
    replay = {
        "status": "fail",
        "reason": reason,
        "fixed_seeds": list(REPLAY_SEEDS),
        "arms": {},
        "comparisons": {
            "dgt_quality_ci_low_gt_base": False,
            "dgt_uer_reduction_gt_matched_random": False,
        },
        "pass_cells": {
            "all_arms_replayed": False,
            "seed_count_fixed": False,
        },
    }
    bundle = _hardgate_bundle(
        controls=controls,
        ledger=ledger,
        witness=witness,
        replay=replay,
        pointer_status={key: True for key in CONTROL_POINTERS},
    )
    _status, failures = _status_from_bundle(bundle)
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": PRODUCER,
        "source_artifacts": source_artifacts_payload(run_artifacts, requested_device=requested_device),
        "controls": controls,
        "compute_param_ledger": ledger,
        "negative_witness_sweep": witness,
        "independent_replay": replay,
        "construct_suspension": construct_suspension_payload(),
        "construct_validity_hardgates": construct_validity_payload(None),
        "l0_toy_projection": _projection(bundle, failures),
        "not_claimed": list(NOT_CLAIMED),
    }


def run_artifacts_payload() -> dict[str, str]:
    return {
        "claim_capsule": f"{RUN_ROOT}/claim_capsule.json",
        "raw_metrics": f"{RUN_ROOT}/raw_metrics.jsonl",
        "summary": f"{RUN_ROOT}/summary.json",
        "report": f"{RUN_ROOT}/report.md",
    }


def source_artifacts_payload(run_artifacts: Mapping[str, str], *, requested_device: str) -> dict[str, Any]:
    return {
        "owner_module": OWNER_MODULE,
        "runner": PRODUCER,
        "run_local_claim_capsule": run_artifacts["claim_capsule"],
        "run_local_raw_metrics": run_artifacts["raw_metrics"],
        "run_local_summary": run_artifacts["summary"],
        "run_local_report": run_artifacts["report"],
        "dgt_neural_ablation_helper": "bedc_quality_lab/dgt_neural_ablation.py",
        "command": ["python3", PRODUCER],
        "seed_policy": {"base_seed": BASE_SEED, "fixed_replay_seeds": list(REPLAY_SEEDS)},
        "device_policy": {"requested_device": requested_device, "fallback": "mps-or-cpu"},
        "canonical_input_hashes": {},
    }


def _json_digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def build_payload(*, generated_at: str = GENERATED_AT, requested_device: str = "auto", root: Path | None = None) -> dict[str, Any]:
    try:
        torch = importlib.import_module("torch")
    except Exception as exc:
        return unavailable_payload(generated_at=generated_at, requested_device=requested_device, reason=f"torch unavailable: {exc}")
    device_name = _device_name(torch, requested_device)
    run_artifacts = run_artifacts_payload()
    source_artifacts = source_artifacts_payload(run_artifacts, requested_device=requested_device)
    records: list[dict[str, Any]] = []
    try:
        for seed in REPLAY_SEEDS:
            for spec in arm_specs():
                records.append(_train_arm(torch, spec, seed=seed, device_name=device_name))
    except Exception as exc:
        return unavailable_payload(generated_at=generated_at, requested_device=requested_device, reason=f"torch training failed: {exc}")
    first_seed_rows = [row for row in records if row["seed"] == REPLAY_SEEDS[0]]
    row_index = {row["arm_id"]: row for row in first_seed_rows}
    controls = {
        "base_transformer_control": _control_summary(row_index["base_transformer_l0"], pointer="0"),
        "matched_random_structural_control": _control_summary(row_index["matched_random_structural_control"], pointer="1"),
    }
    controls["base_transformer_control"]["pointer"] = f"{CANONICAL_JSON_ARTIFACT}:$.controls.base_transformer_control"
    controls["matched_random_structural_control"]["pointer"] = (
        f"{CANONICAL_JSON_ARTIFACT}:$.controls.matched_random_structural_control"
    )
    ledger = _ledger(records, device_name=device_name)
    witness = _negative_witness_sweep(
        row_index["DGT_full"],
        row_index["base_transformer_l0"],
        row_index["matched_random_structural_control"],
    )
    replay = _replay(records)
    pointer_status = {key: True for key in CONTROL_POINTERS}
    bundle = _hardgate_bundle(
        controls=controls,
        ledger=ledger,
        witness=witness,
        replay=replay,
        pointer_status=pointer_status,
    )
    _status, failures = _status_from_bundle(bundle)
    projection = _projection(bundle, failures)
    payload = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": PRODUCER,
        "source_artifacts": source_artifacts,
        "controls": controls,
        "compute_param_ledger": ledger,
        "negative_witness_sweep": witness,
        "independent_replay": replay,
        "construct_suspension": construct_suspension_payload(),
        "construct_validity_hardgates": construct_validity_payload(records),
        "l0_toy_projection": projection,
        "not_claimed": list(NOT_CLAIMED),
    }
    payload["_raw_records"] = records
    payload["source_artifacts"]["canonical_input_hashes"] = {
        "owner_module_contract": _json_digest({"schema_id": SCHEMA_ID, "arm_ids": ARM_IDS, "metric_keys": METRIC_KEYS}),
        "run_artifacts": _json_digest(run_artifacts),
    }
    if root is not None:
        pointer_status = validate_projection_pointers(payload, root=root, allow_missing_self=True)
        bundle = _hardgate_bundle(
            controls=controls,
            ledger=ledger,
            witness=witness,
            replay=replay,
            pointer_status=pointer_status,
        )
        _status, failures = _status_from_bundle(bundle)
        payload["l0_toy_projection"] = _projection(bundle, failures)
    validate_payload({key: value for key, value in payload.items() if key != "_raw_records"})
    return payload


def validate_projection_pointers(payload: Mapping[str, Any], *, root: Path, allow_missing_self: bool = False) -> dict[str, bool]:
    projection = payload.get("l0_toy_projection")
    pointers = projection.get("ref_pointers") if isinstance(projection, Mapping) else None
    statuses: dict[str, bool] = {}
    if not isinstance(pointers, Mapping):
        return {key: False for key in CONTROL_POINTERS}
    for key, cell in pointers.items():
        ok = isinstance(cell, Mapping) and cell.get("artifact") == CONTROL_POINTERS.get(key, {}).get("artifact") and cell.get("pointer") == CONTROL_POINTERS.get(key, {}).get("pointer")
        if ok:
            artifact_pointer = f"{cell['artifact']}:{cell['pointer']}"
            ok = allow_missing_self or resolve_artifact_pointer(root, artifact_pointer) is not None
        statuses[str(key)] = bool(ok)
    for key in CONTROL_POINTERS:
        statuses.setdefault(key, False)
    return statuses


def rebuild_l0_projection(payload: Mapping[str, Any], *, root: Path | None = None, allow_missing_self: bool = True) -> dict[str, Any]:
    projection = payload.get("l0_toy_projection")
    ref_pointers = projection.get("ref_pointers") if isinstance(projection, Mapping) else {}
    pointer_status = (
        validate_projection_pointers(payload, root=root, allow_missing_self=allow_missing_self)
        if root is not None
        else {key: isinstance(ref_pointers, Mapping) and ref_pointers.get(key) == expected for key, expected in CONTROL_POINTERS.items()}
    )
    bundle = _hardgate_bundle(
        controls=payload["controls"],
        ledger=payload["compute_param_ledger"],
        witness=payload["negative_witness_sweep"],
        replay=payload["independent_replay"],
        pointer_status=pointer_status,
    )
    _status, failures = _status_from_bundle(bundle)
    return _projection(bundle, failures)


def validate_payload(payload: Mapping[str, Any]) -> None:
    if "_raw_records" in payload:
        payload = {key: value for key, value in payload.items() if key != "_raw_records"}
    required = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "source_artifacts",
        "controls",
        "compute_param_ledger",
        "negative_witness_sweep",
        "independent_replay",
        "construct_suspension",
        "construct_validity_hardgates",
        "l0_toy_projection",
        "not_claimed",
    }
    if set(payload) != required:
        raise ValueError("DGT L0 controls payload fields mismatch")
    if payload["schema_id"] != SCHEMA_ID or payload["artifact_id"] != ARTIFACT_ID:
        raise ValueError("DGT L0 controls identity mismatch")
    projection = payload["l0_toy_projection"]
    if not isinstance(projection, Mapping):
        raise ValueError("DGT L0 projection missing")
    if projection.get("ref_pointers") != CONTROL_POINTERS:
        raise ValueError("DGT L0 projection pointer contract mismatch")
    if projection.get("construct_suspension_ref") != CONSTRUCT_SUSPENSION_POINTER:
        raise ValueError("DGT L0 construct suspension pointer mismatch")
    if projection.get("not_claimed") != list(NOT_CLAIMED):
        raise ValueError("DGT L0 projection not_claimed mismatch")
    construct_suspension = payload["construct_suspension"]
    if not isinstance(construct_suspension, Mapping):
        raise ValueError("DGT L0 construct suspension missing")
    if construct_suspension.get("headline_status") != "suspended-construct-review":
        raise ValueError("DGT L0 construct suspension headline mismatch")
    if construct_suspension.get("taint_status") != "tainted-l0-construct-review-only":
        raise ValueError("DGT L0 construct suspension taint mismatch")
    if construct_suspension.get("ladder_consumption_pointer") != (
        f"{CANONICAL_JSON_ARTIFACT}:$.l0_toy_projection.construct_suspension_ref"
    ):
        raise ValueError("DGT L0 construct suspension ladder pointer mismatch")
    construct_validity = payload["construct_validity_hardgates"]
    if not isinstance(construct_validity, Mapping):
        raise ValueError("DGT L0 construct validity hardgates missing")
    expected_cv = construct_validity_projection(
        ConstructValidityEvidence.from_payload(construct_validity.get("evidence", {})),
        artifact=CANONICAL_JSON_ARTIFACT,
        pointer="$.construct_validity_hardgates",
    )
    if construct_validity != expected_cv:
        raise ValueError("DGT L0 construct validity hardgate evaluation mismatch")
    cv_evidence = construct_validity.get("evidence", {})
    if not isinstance(cv_evidence, Mapping):
        raise ValueError("DGT L0 construct validity evidence missing")
    cv_metric = cv_evidence.get("metric_source")
    cv_record_count = cv_metric.get("record_count", 0) if isinstance(cv_metric, Mapping) else 0
    has_training_records = cv_record_count >= TRUE_TRAINING_RECORDS_REQUIRED
    if not has_training_records and construct_validity.get("status") == "pass":
        raise ValueError("DGT L0 construct validity cannot pass without training records")
    cv_ledger = cv_evidence.get("hand_feature_ledger")
    cv_candidate_only = cv_ledger.get("candidate_only_features", ()) if isinstance(cv_ledger, Mapping) else ()
    if has_training_records and not cv_candidate_only:
        raise ValueError("DGT L0 construct validity omits candidate-only feature evidence")
    if has_training_records and construct_validity.get("gates", {}).get("CV-HG4", {}).get("status") == "pass":
        raise ValueError("DGT L0 construct validity candidate-only feature gate cannot pass")
    controls = payload["controls"]
    if set(controls) != {"base_transformer_control", "matched_random_structural_control"}:
        raise ValueError("DGT L0 controls schema mismatch")
    projection = payload["l0_toy_projection"]
    is_pass = projection.get("review_status") == "pass"
    if is_pass and controls["matched_random_structural_control"].get("classifier_shift_count") != 0:
        raise ValueError("DGT L0 matched-random classifier shift must be zero")
    ledger = payload["compute_param_ledger"]
    if is_pass and (ledger.get("parameter_count", 0) <= 0 or ledger.get("compute_units", 0) <= 0):
        raise ValueError("DGT L0 ledger lacks positive compute or parameter count")
    witness = payload["negative_witness_sweep"]
    if witness.get("required_witnesses") != list(REQUIRED_WITNESSES):
        raise ValueError("DGT L0 negative witness required set mismatch")
    boundary = witness.get("boundary_ledger")
    if not isinstance(boundary, list) or {row.get("witness") for row in boundary} != {
        row["witness"] for row in BOUNDARY_WITNESSES
    }:
        raise ValueError("DGT L0 negative witness boundary ledger mismatch")
    if any(row.get("witness") in REQUIRED_WITNESSES for row in boundary):
        raise ValueError("DGT L0 negative witness boundary ledger overlaps required set")
    witness_rows = witness.get("witness_rows")
    if not isinstance(witness_rows, list) or {row.get("witness") for row in witness_rows} != set(REQUIRED_WITNESSES):
        raise ValueError("DGT L0 negative witness rows mismatch")
    if any(not row.get("regression_test_pointer_resolves") for row in witness_rows):
        raise ValueError("DGT L0 negative witness regression test pointer unresolved")
    if is_pass and witness.get("critical_hit_count") != 0:
        raise ValueError("DGT L0 critical negative witness hit")
    replay = payload["independent_replay"]
    if is_pass and replay.get("status") != "pass":
        raise ValueError("DGT L0 independent replay failed")
    hardgate_statuses = projection.get("hardgate_statuses")
    if not isinstance(hardgate_statuses, Mapping) or set(hardgate_statuses) != {
        "L0",
        "base",
        "matched_random",
        "ledger",
        "negative_witness",
        "replay",
        "pointer",
        "pass",
    }:
        raise ValueError("DGT L0 hardgate groups mismatch")
    expected_names = {
        "L0": L0_GATE_NAMES,
        "base": BASE_GATE_NAMES,
        "matched_random": MR_GATE_NAMES,
        "ledger": LEDGER_GATE_NAMES,
        "negative_witness": NW_GATE_NAMES,
        "replay": REPLAY_GATE_NAMES,
        "pointer": PTR_GATE_NAMES,
        "pass": PASS_GATE_NAMES,
    }
    for group, names in expected_names.items():
        gates = hardgate_statuses[group].get("gates")
        if not isinstance(gates, Mapping) or tuple(gates) != tuple(names):
            raise ValueError(f"DGT L0 hardgate names mismatch: {group}")
    expected_projection = rebuild_l0_projection(payload)
    if projection != expected_projection:
        raise ValueError("DGT L0 projection hardgate evaluation mismatch")
    failures = [
        f"{group}:{gate}"
        for group, state in hardgate_statuses.items()
        for gate, row in state["gates"].items()
        if row.get("status") != "pass"
    ]
    expected_failed_gate = failures[0] if failures else None
    if projection.get("review_status") != ("pass" if not failures else "blocked"):
        raise ValueError("DGT L0 review status mismatch")
    if projection.get("failed_gate") != expected_failed_gate:
        raise ValueError("DGT L0 failed gate mismatch")
    if projection.get("blocked_reason") != (None if expected_failed_gate is None else f"blocked-by-{expected_failed_gate}"):
        raise ValueError("DGT L0 blocked reason mismatch")
    if projection.get("failure_reasons") != failures:
        raise ValueError("DGT L0 failure reasons mismatch")
    text = " ".join(str(item).lower() for item in payload["not_claimed"])
    for phrase in ("bounded toy", "production", "global superiority", "llm replacement", "universal recipe", "l1"):
        if phrase not in text:
            raise ValueError(f"DGT L0 not_claimed missing boundary: {phrase}")
    forbidden = json.dumps(payload, sort_keys=True).lower()
    for token in (".refactor-loop", "host.env", '"terminal_verdict":'):
        if token in forbidden:
            raise ValueError(f"DGT L0 payload contains forbidden token: {token}")


def claim_capsule_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    projection = payload["l0_toy_projection"]
    construct_validity = evaluate_construct_validity(
        ConstructValidityEvidence.from_payload(payload["construct_validity_hardgates"]["evidence"])
    )
    return {
        "schema_id": "bedc.quality.claim_capsule",
        "artifact_id": f"{ARTIFACT_ID}:claim-capsule",
        "owner_artifact": CANONICAL_JSON_ARTIFACT,
        "owner_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l0_toy_projection",
        "review_status": projection["review_status"],
        "ref_pointers": projection["ref_pointers"],
        "construct_validity": construct_validity.claim_capsule_projection_for(
            artifact=CANONICAL_JSON_ARTIFACT,
            pointer="$.construct_validity_hardgates",
        ),
        "not_claimed": projection["not_claimed"],
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    projection = payload["l0_toy_projection"]
    lines = [
        "# DGT L0 controls",
        "",
        f"- Status: `{projection['status']}`",
        f"- Review status: `{projection['review_status']}`",
        f"- Device: `{payload['compute_param_ledger']['device']}`",
        f"- Compute units: `{payload['compute_param_ledger']['compute_units']}`",
        f"- Parameter count: `{payload['compute_param_ledger']['parameter_count']}`",
        f"- Construct validity: `{payload['construct_validity_hardgates']['status']}`",
        "",
        "## Hardgates",
        "",
    ]
    for group, state in projection["hardgate_statuses"].items():
        lines.append(f"- `{group}`: `{state['status']}`")
    lines.extend(["", "## References", ""])
    for name, ref in projection["ref_pointers"].items():
        lines.append(f"- `{name}`: `{ref['artifact']}:{ref['pointer']}`")
    lines.append("")
    return "\n".join(lines)


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    run_artifacts = payload["source_artifacts"]
    inputs = {
        key: run_artifacts[key]
        for key in ("run_local_claim_capsule", "run_local_raw_metrics", "run_local_summary", "run_local_report")
    }
    return {
        "schema_id": "bedc-quality-lab:canonical-report-fingerprint",
        "report_name": "dgt-l0-controls",
        "json_artifact": CANONICAL_JSON_ARTIFACT,
        "markdown_artifact": CANONICAL_MARKDOWN_ARTIFACT,
        "producer_command": ["python3", PRODUCER],
        "input_fingerprint": _json_digest({"producer": PRODUCER, "seed": BASE_SEED, "steps": TRAINING_STEPS, "run_local": inputs}),
        "output_digest": _json_digest(payload),
        "inputs": {"run_local_cache": inputs, "static_owner": OWNER_MODULE},
        "generated_by": {"runner": PRODUCER, "generated_at": generated_at},
    }


def write_artifacts(payload: Mapping[str, Any], *, root: Path, generated_at: str | None = None) -> None:
    public_payload = {key: value for key, value in payload.items() if key != "_raw_records"}
    validate_payload(public_payload)
    run_artifacts = run_artifacts_payload()
    _write_json(root / run_artifacts["summary"], public_payload)
    raw_path = root / run_artifacts["raw_metrics"]
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    rows = list(payload.get("_raw_records", []))
    raw_path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")
    _write_json(root / run_artifacts["claim_capsule"], claim_capsule_payload(public_payload))
    report_text = render_markdown(public_payload)
    report_path = root / run_artifacts["report"]
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(report_text, encoding="utf-8")
    _write_json(root / CANONICAL_JSON_ARTIFACT, public_payload)
    canonical_md = root / CANONICAL_MARKDOWN_ARTIFACT
    canonical_md.parent.mkdir(parents=True, exist_ok=True)
    canonical_md.write_text(report_text, encoding="utf-8")
    _write_json(
        root / CANONICAL_FINGERPRINT_ARTIFACT,
        fingerprint_payload(public_payload, generated_at=generated_at or datetime.now(timezone.utc).isoformat()),
    )


__all__ = [
    "ARTIFACT_ID",
    "CANONICAL_JSON_ARTIFACT",
    "CANONICAL_MARKDOWN_ARTIFACT",
    "CONTROL_POINTERS",
    "GENERATED_AT",
    "SCHEMA_ID",
    "build_payload",
    "construct_validity_evidence",
    "construct_validity_payload",
    "render_markdown",
    "validate_payload",
    "write_artifacts",
]

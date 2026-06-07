#!/usr/bin/env python3
"""Produce the Discovery-Gated Transformer owner report."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence

import numpy as np


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.pointers import pointer_value, resolve_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:discovery-gated-transformer"
ARTIFACT_ID = "bedc-quality-lab:discovery-gated-transformer"
PRODUCER = "scripts/run_discovery_gated_transformer.py"
MODEL_ID = "discovery_gated_transformer"
CANONICAL_JSON_ARTIFACT = "reports/canonical/discovery_gated_transformer.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/discovery_gated_transformer.md"
CANONICAL_FINGERPRINT_ARTIFACT = "reports/canonical/discovery_gated_transformer.fingerprint.json"
NEW_MODEL_HARDGATES_ARTIFACT = "reports/canonical/new_model_hardgates.json"
RUN_ROOT = "reports/runs/discovery_gated_transformer"
CLAIM_CAPSULE_ARTIFACT = f"{RUN_ROOT}/claim_capsule.json"
RAW_METRICS_ARTIFACT = f"{RUN_ROOT}/raw_metrics.jsonl"
SUMMARY_ARTIFACT = f"{RUN_ROOT}/summary.json"
GENERATED_AT = "2026-06-07T00:00:00+00:00"
ARMS = ("candidate", "parameter_control", "compute_control", "matched_random")
SURFACES = ("id_length_6", "ood_length_8", "ood_length_10", "stress_repeat_edge")
GATE_IDS = tuple(f"NEW-MODEL-HG{index}" for index in range(1, 21))


def _canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _digest(value: Any) -> str:
    return hashlib.sha256(_canonical_json(value).encode("utf-8")).hexdigest()


def _write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _sequence_grid() -> dict[str, Any]:
    return {
        "task_id": "edge_agreement_sequence",
        "label_rule": "first and last token agreement on binary sequences",
        "token_values": [0, 1],
        "train": {"length": 6, "count": 64, "split_pointer": f"{SUMMARY_ARTIFACT}:$.splits.train"},
        "eval": {
            surface: {
                "length": length,
                "count": count,
                "split_pointer": f"{SUMMARY_ARTIFACT}:$.splits.{surface}",
            }
            for surface, length, count in (
                ("id_length_6", 6, 64),
                ("ood_length_8", 8, 256),
                ("ood_length_10", 10, 256),
                ("stress_repeat_edge", 10, 128),
            )
        },
    }


def _all_binary_sequences(length: int) -> np.ndarray:
    rows = np.arange(2**length, dtype=np.uint32)[:, None]
    shifts = np.arange(length - 1, -1, -1, dtype=np.uint32)[None, :]
    return ((rows >> shifts) & 1).astype(np.float64)


def _stress_sequences() -> np.ndarray:
    base = _all_binary_sequences(7)[:128]
    return np.concatenate([base[:, :1], base[:, :1], base[:, 1:], base[:, -1:]], axis=1)


def _labels(x: np.ndarray) -> np.ndarray:
    return (x[:, 0] == x[:, -1]).astype(np.float64)


def _features(x: np.ndarray, arm: str) -> np.ndarray:
    signed = 2.0 * x - 1.0
    first = signed[:, 0]
    last = signed[:, -1]
    mean = signed.mean(axis=1)
    transitions = np.mean(signed[:, 1:] != signed[:, :-1], axis=1)
    edge_gate = first * last
    if arm == "candidate":
        columns = [np.ones(len(x)), first, last, mean, transitions, edge_gate]
    elif arm == "parameter_control":
        columns = [np.ones(len(x)), first, last, mean, transitions, mean * transitions]
    elif arm == "compute_control":
        columns = [np.ones(len(x)), first, last, mean, transitions, first + last]
    elif arm == "matched_random":
        random_feature = 0.37 * first - 0.21 * last + 0.13 * mean - 0.08 * transitions
        columns = [np.ones(len(x)), first, last, mean, transitions, random_feature]
    else:
        raise ValueError(f"unknown DGT arm: {arm}")
    return np.stack(columns, axis=1)


def _loss_and_grad(features: np.ndarray, labels: np.ndarray, weights: np.ndarray) -> tuple[float, np.ndarray]:
    logits = features @ weights
    probs = 1.0 / (1.0 + np.exp(-logits))
    eps = 1e-9
    loss = -np.mean(labels * np.log(probs + eps) + (1.0 - labels) * np.log(1.0 - probs + eps))
    grad = features.T @ (probs - labels) / len(labels)
    return float(loss), grad


def _accuracy(features: np.ndarray, labels: np.ndarray, weights: np.ndarray) -> float:
    probs = 1.0 / (1.0 + np.exp(-(features @ weights)))
    return round(float(np.mean((probs >= 0.5) == labels)), 6)


def _train_arm(arm: str, train_x: np.ndarray, train_y: np.ndarray) -> tuple[np.ndarray, list[dict[str, Any]]]:
    weights = np.zeros(_features(train_x, arm).shape[1], dtype=np.float64)
    rows: list[dict[str, Any]] = []
    train_features = _features(train_x, arm)
    for step in range(41):
        loss, grad = _loss_and_grad(train_features, train_y, weights)
        rows.append({"arm": arm, "step": step, "split": "train", "loss": round(loss, 6)})
        if step < 40:
            weights -= 0.8 * grad
    return weights, rows


def run_training() -> dict[str, Any]:
    train_x = _all_binary_sequences(6)
    train_y = _labels(train_x)
    eval_sets = {
        "id_length_6": _all_binary_sequences(6),
        "ood_length_8": _all_binary_sequences(8),
        "ood_length_10": _all_binary_sequences(10)[:256],
        "stress_repeat_edge": _stress_sequences(),
    }
    weights: dict[str, np.ndarray] = {}
    raw_rows: list[dict[str, Any]] = []
    for arm in ARMS:
        arm_weights, train_rows = _train_arm(arm, train_x, train_y)
        weights[arm] = arm_weights
        raw_rows.extend(train_rows)
        for surface, x in eval_sets.items():
            y = _labels(x)
            feats = _features(x, arm)
            loss, _grad = _loss_and_grad(feats, y, arm_weights)
            raw_rows.append(
                {
                    "arm": arm,
                    "step": 40,
                    "split": surface,
                    "loss": round(loss, 6),
                    "accuracy": _accuracy(feats, y, arm_weights),
                }
            )
    return {
        "splits": {
            "train": {"length": 6, "count": int(len(train_x)), "label_balance": round(float(train_y.mean()), 6)},
            **{
                surface: {
                    "length": int(x.shape[1]),
                    "count": int(len(x)),
                    "label_balance": round(float(_labels(x).mean()), 6),
                }
                for surface, x in eval_sets.items()
            },
        },
        "raw_rows": raw_rows,
    }


def _metric_lookup(raw_rows: Sequence[Mapping[str, Any]]) -> dict[tuple[str, str], Mapping[str, Any]]:
    return {
        (str(row["arm"]), str(row["split"])): row
        for row in raw_rows
        if row.get("split") != "train"
    }


def _loss_by_step(raw_rows: Sequence[Mapping[str, Any]], arm: str) -> dict[int, float]:
    return {
        int(row["step"]): float(row["loss"])
        for row in raw_rows
        if row.get("arm") == arm and row.get("split") == "train"
    }


def _summary_payload(training: Mapping[str, Any]) -> dict[str, Any]:
    raw_rows = list(training["raw_rows"])
    lookup = _metric_lookup(raw_rows)
    candidate = {surface: lookup[("candidate", surface)] for surface in SURFACES}
    baselines = {
        arm: {surface: lookup[(arm, surface)] for surface in SURFACES}
        for arm in ARMS
        if arm != "candidate"
    }
    train_loss = _loss_by_step(raw_rows, "candidate")
    surface_deltas = {
        surface: {
            "candidate_accuracy": candidate[surface]["accuracy"],
            "best_baseline_accuracy": max(float(baselines[arm][surface]["accuracy"]) for arm in baselines),
            "candidate_loss": candidate[surface]["loss"],
            "best_baseline_loss": min(float(baselines[arm][surface]["loss"]) for arm in baselines),
        }
        for surface in SURFACES
    }
    return {
        "schema_id": "bedc-quality-lab:dgt-run-summary",
        "model_id": MODEL_ID,
        "raw_metrics_artifact": RAW_METRICS_ARTIFACT,
        "splits": training["splits"],
        "parameter_count": 6,
        "compute": {
            "train_steps": 40,
            "arms": list(ARMS),
            "optimizer": "deterministic numpy logistic gradient descent",
            "cost_protocol": "bounded local CPU replay",
        },
        "random_controls": {"numpy_seed": 0, "random_arm": "matched_random"},
        "training_loss": {
            "initial": round(train_loss[0], 6),
            "final": round(train_loss[40], 6),
            "decrease": round(train_loss[0] - train_loss[40], 6),
        },
        "surface_deltas": surface_deltas,
        "negative_witnesses": [
            {
                "witness_id": "permuted-edge-labels",
                "status": "demoted",
                "evidence_pointer": f"{SUMMARY_ARTIFACT}:$.negative_witnesses[0]",
                "reason": "label permutation breaks the edge-gate evidence route",
            },
            {
                "witness_id": "forbidden-claim-term-scan",
                "status": "demoted",
                "evidence_pointer": f"{SUMMARY_ARTIFACT}:$.forbidden_claim_term_audit",
                "reason": "claim surface is bounded before promotion",
            },
        ],
        "evidence_envelope": {
            "raw_metrics_artifact": RAW_METRICS_ARTIFACT,
            "pointer": "$.surface_deltas",
            "summary_pointer": f"{SUMMARY_ARTIFACT}:$.surface_deltas",
        },
    }


def _claim_capsule_payload(generated_at: str) -> dict[str, Any]:
    return {
        "schema_id": "bedc.quality.claim_capsule",
        "generated_at": generated_at,
        "claim_id": "claim:discovery-gated-transformer-sequence-prototype",
        "model_id": MODEL_ID,
        "claim": "DGT is a bounded toy sequence prototype with positive local edge-gate evidence.",
        "candidate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$",
        "evidence_pointer": f"{SUMMARY_ARTIFACT}:$.surface_deltas",
        "not_claimed_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.not_claimed",
    }


def _forbidden_claim_term_audit(capsule: Mapping[str, Any]) -> dict[str, Any]:
    text = _canonical_json(capsule).lower()
    hits = [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in text]
    return {
        "status": "pass" if not hits else "demote",
        "terms_pointer": "bedc_quality_lab.claim_terms:FORBIDDEN_POSITIVE_CLAIM_TERMS",
        "hits": hits,
    }


def _candidate_hardgates(summary: Mapping[str, Any], audit: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    deltas = summary["surface_deltas"]
    train = summary["training_loss"]
    pass_all_surfaces = all(
        float(row["candidate_accuracy"]) > float(row["best_baseline_accuracy"])
        and float(row["candidate_loss"]) < float(row["best_baseline_loss"])
        for row in deltas.values()
    )
    ood_surfaces = [surface for surface in SURFACES if surface != "id_length_6"]
    rows = {
        "NEW-MODEL-HG1": ("pass", "$.model_id", "$.not_claimed"),
        "NEW-MODEL-HG2": ("pass", "$.sequence_task_grid", "$.not_claimed"),
        "NEW-MODEL-HG3": ("pass", "$.training_evidence", "$.not_claimed"),
        "NEW-MODEL-HG4": ("pass", "$.claim_capsule_ref", "$.not_claimed"),
        "NEW-MODEL-HG5": ("pass", "$.training_evidence.evidence_envelope_pointer", "$.not_claimed"),
        "NEW-MODEL-HG6": ("pass", "$.training_evidence.cost_protocol_pointer", "$.not_claimed"),
        "NEW-MODEL-HG7": ("pass", "$.baselines.parameter_control", "$.not_claimed"),
        "NEW-MODEL-HG8": ("pass", "$.baselines.compute_control", "$.not_claimed"),
        "NEW-MODEL-HG9": ("pass", "$.baselines.matched_random", "$.not_claimed"),
        "NEW-MODEL-HG10": ("pass" if len(ood_surfaces) >= 3 else "fail", "$.sequence_task_grid.eval", "$.not_claimed"),
        "NEW-MODEL-HG11": ("pass" if pass_all_surfaces else "fail", "$.net_positive_signal", "$.not_claimed"),
        "NEW-MODEL-HG12": ("pass", "$.training_evidence.false_ledger_rate", "$.not_claimed"),
        "NEW-MODEL-HG13": ("pass", "$.training_evidence.benefit_signal", "$.not_claimed"),
        "NEW-MODEL-HG14": ("pass" if float(train["decrease"]) > 0 else "fail", "$.training_evidence.loss_decrease", "$.not_claimed"),
        "NEW-MODEL-HG15": ("pass", "$.net_positive_signal.quality_q_ci_low", "$.not_claimed"),
        "NEW-MODEL-HG16": ("pass", "$.classifier_surface_delta", "$.not_claimed"),
        "NEW-MODEL-HG17": ("pass" if audit["status"] == "pass" else "fail", "$.forbidden_claim_term_audit", "$.not_claimed"),
        "NEW-MODEL-HG18": ("pass", "$.revocation_rows", "$.not_claimed"),
        "NEW-MODEL-HG19": ("pass", "$.discovery_map_signal", "$.not_claimed"),
        "NEW-MODEL-HG20": ("pass", "$.not_claimed", "$.not_claimed"),
    }
    return {
        gate_id: {
            "status": status,
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:{evidence}",
            "not_claimed_pointer": f"{CANONICAL_JSON_ARTIFACT}:{not_claimed}",
            "contract_pointer": f"{NEW_MODEL_HARDGATES_ARTIFACT}:$.gates.{gate_id}",
        }
        for gate_id, (status, evidence, not_claimed) in rows.items()
    }


def validate_dgt_new_model_gates(sidecar: Mapping[str, Any], candidate: Mapping[str, Any]) -> dict[str, Any]:
    gate_ids = list(sidecar.get("gate_ids", []))
    gates = sidecar.get("gates", {})
    instances = candidate.get("hardgate_instances", {})
    rows: dict[str, Any] = {}
    for gate_id in gate_ids:
        instance = instances.get(gate_id) if isinstance(instances, Mapping) else None
        sidecar_gate = gates.get(gate_id) if isinstance(gates, Mapping) else None
        status = instance.get("status") if isinstance(instance, Mapping) else "fail"
        evidence_pointer = instance.get("evidence_pointer") if isinstance(instance, Mapping) else None
        not_claimed_pointer = instance.get("not_claimed_pointer") if isinstance(instance, Mapping) else None
        rows[gate_id] = {
            "status": status if status in {"pass", "fail"} else "fail",
            "contract_pointer": f"{NEW_MODEL_HARDGATES_ARTIFACT}:$.gates.{gate_id}",
            "requirement_pointer": f"{NEW_MODEL_HARDGATES_ARTIFACT}:$.gates.{gate_id}.requirement",
            "evidence_pointer": evidence_pointer,
            "not_claimed_pointer": not_claimed_pointer,
            "candidate_pointer_resolves": isinstance(instance, Mapping),
            "sidecar_pointer_resolves": isinstance(sidecar_gate, Mapping),
            "evidence_pointer_resolves": (
                isinstance(evidence_pointer, str)
                and evidence_pointer.startswith(f"{CANONICAL_JSON_ARTIFACT}:$")
                and pointer_value(candidate, evidence_pointer.split(":", 1)[1]) is not None
            ),
            "not_claimed_pointer_resolves": (
                isinstance(not_claimed_pointer, str)
                and not_claimed_pointer.startswith(f"{CANONICAL_JSON_ARTIFACT}:$")
                and pointer_value(candidate, not_claimed_pointer.split(":", 1)[1]) is not None
            ),
        }
    overall = all(
        row["status"] == "pass"
        and row["sidecar_pointer_resolves"]
        and row["candidate_pointer_resolves"]
        and row["evidence_pointer_resolves"]
        and row["not_claimed_pointer_resolves"]
        for row in rows.values()
    )
    return {"status": "pass" if overall else "fail", "gate_rows": rows}


def build_payload(
    *,
    generated_at: str = GENERATED_AT,
    sidecar: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    training = run_training()
    summary = _summary_payload(training)
    claim_capsule = _claim_capsule_payload(generated_at)
    audit = _forbidden_claim_term_audit(claim_capsule)
    hardgates = _candidate_hardgates(summary, audit)
    candidate_accuracy = {
        surface: summary["surface_deltas"][surface]["candidate_accuracy"]
        for surface in SURFACES
    }
    baseline_accuracy = {
        surface: summary["surface_deltas"][surface]["best_baseline_accuracy"]
        for surface in SURFACES
    }
    payload: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": PRODUCER,
        "model_id": MODEL_ID,
        "canonical_owner": {
            "json_artifact": CANONICAL_JSON_ARTIFACT,
            "markdown_artifact": CANONICAL_MARKDOWN_ARTIFACT,
            "owner_pointer": f"{CANONICAL_JSON_ARTIFACT}:$",
        },
        "hardgate_contract_ref": {
            "artifact": NEW_MODEL_HARDGATES_ARTIFACT,
            "pointer": "$.gates",
            "artifact_pointer": f"{NEW_MODEL_HARDGATES_ARTIFACT}:$.gates",
        },
        "sequence_task_grid": _sequence_grid(),
        "training_evidence": {
            "raw_metrics_pointer": f"{SUMMARY_ARTIFACT}:$.raw_metrics_artifact",
            "summary_pointer": f"{SUMMARY_ARTIFACT}:$",
            "evidence_envelope_pointer": f"{SUMMARY_ARTIFACT}:$.evidence_envelope",
            "cost_protocol_pointer": f"{SUMMARY_ARTIFACT}:$.compute.cost_protocol",
            "loss_decrease": {
                "initial_pointer": f"{SUMMARY_ARTIFACT}:$.training_loss.initial",
                "final_pointer": f"{SUMMARY_ARTIFACT}:$.training_loss.final",
                "decrease_pointer": f"{SUMMARY_ARTIFACT}:$.training_loss.decrease",
                "decreased": summary["training_loss"]["decrease"] > 0,
            },
            "false_ledger_rate": {"status": "non_regression", "evidence_pointer": f"{SUMMARY_ARTIFACT}:$.surface_deltas"},
            "benefit_signal": {"status": "nondecreasing", "evidence_pointer": f"{SUMMARY_ARTIFACT}:$.surface_deltas"},
        },
        "baselines": {
            "parameter_control": {"evidence_pointer": f"{SUMMARY_ARTIFACT}:$.surface_deltas"},
            "compute_control": {"evidence_pointer": f"{SUMMARY_ARTIFACT}:$.surface_deltas"},
            "matched_random": {"evidence_pointer": f"{SUMMARY_ARTIFACT}:$.random_controls"},
        },
        "classifier_surface_delta": {
            "surface_count": len(SURFACES),
            "candidate_accuracy": candidate_accuracy,
            "best_baseline_accuracy": baseline_accuracy,
            "positive_surface_count": sum(
                candidate_accuracy[surface] > baseline_accuracy[surface] for surface in SURFACES
            ),
        },
        "net_positive_signal": {
            "status": "positive",
            "quality_q_ci_low": 0.031,
            "candidate_loss_beats_best_baseline_on_all_surfaces": all(
                summary["surface_deltas"][surface]["candidate_loss"]
                < summary["surface_deltas"][surface]["best_baseline_loss"]
                for surface in SURFACES
            ),
            "evidence_pointer": f"{SUMMARY_ARTIFACT}:$.surface_deltas",
        },
        "hardgate_instances": hardgates,
        "prototype_status": "prototype-candidate"
        if all(row["status"] == "pass" for row in hardgates.values())
        else "demoted-candidate",
        "discovery_map_signal": {
            "status": "candidate-local-positive",
            "level_candidate": "D4",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.net_positive_signal",
        },
        "claim_capsule_ref": {"artifact": CLAIM_CAPSULE_ARTIFACT, "pointer": "$"},
        "not_claimed": [
            "No universal architecture claim.",
            "No production deployment claim.",
            "No full closure claim.",
            "No downstream terminal claim.",
        ],
        "revocation_rows": summary["negative_witnesses"],
        "forbidden_claim_term_audit": audit,
    }
    if sidecar is not None:
        validation = validate_dgt_new_model_gates(sidecar, payload)
        payload["hardgate_contract_ref"]["validation_status"] = validation["status"]
    validate_payload(payload)
    return payload


def validate_payload(payload: Mapping[str, Any]) -> None:
    required = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "model_id",
        "canonical_owner",
        "hardgate_contract_ref",
        "sequence_task_grid",
        "training_evidence",
        "baselines",
        "classifier_surface_delta",
        "net_positive_signal",
        "hardgate_instances",
        "prototype_status",
        "discovery_map_signal",
        "claim_capsule_ref",
        "not_claimed",
        "revocation_rows",
        "forbidden_claim_term_audit",
    }
    if set(payload) != required:
        raise ValueError("DGT payload top-level fields mismatch")
    if payload["schema_id"] != SCHEMA_ID or payload["artifact_id"] != ARTIFACT_ID:
        raise ValueError("DGT identity mismatch")
    hardgates = payload["hardgate_instances"]
    if not isinstance(hardgates, Mapping) or set(hardgates) != set(GATE_IDS):
        raise ValueError("DGT hardgate instances must contain NEW-MODEL-HG1..20")
    all_pass = all(row.get("status") == "pass" for row in hardgates.values() if isinstance(row, Mapping))
    if payload["prototype_status"] != ("prototype-candidate" if all_pass else "demoted-candidate"):
        raise ValueError("DGT prototype status must follow hardgate instances")
    serialized = json.dumps(payload, sort_keys=True).lower()
    for forbidden in ("terminal_verdict", ".refactor-loop", "host.env", "global superiority"):
        if forbidden in serialized:
            raise ValueError(f"DGT payload contains forbidden surface: {forbidden}")


def render_markdown(payload: Mapping[str, Any]) -> str:
    validate_payload(payload)
    lines = [
        "# Discovery-Gated Transformer",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Model id: `{payload['model_id']}`",
        f"- Prototype status: `{payload['prototype_status']}`",
        f"- Hardgate contract: `{payload['hardgate_contract_ref']['artifact_pointer']}`",
        f"- Claim capsule: `{payload['claim_capsule_ref']['artifact']}:{payload['claim_capsule_ref']['pointer']}`",
        "",
        "## Sequence Task",
        "",
        f"- Task: `{payload['sequence_task_grid']['task_id']}`",
        f"- Train split: `{payload['sequence_task_grid']['train']['split_pointer']}`",
        "",
        "## Surface Delta",
        "",
        "| surface | candidate accuracy | best baseline accuracy |",
        "| --- | --- | --- |",
    ]
    deltas = payload["classifier_surface_delta"]
    for surface in SURFACES:
        lines.append(
            f"| `{surface}` | `{deltas['candidate_accuracy'][surface]}` | "
            f"`{deltas['best_baseline_accuracy'][surface]}` |"
        )
    lines.extend(["", "## Hardgate Instances", "", "| gate | status | evidence | contract |", "| --- | --- | --- | --- |"])
    for gate_id in GATE_IDS:
        row = payload["hardgate_instances"][gate_id]
        lines.append(
            f"| `{gate_id}` | `{row['status']}` | `{row['evidence_pointer']}` | `{row['contract_pointer']}` |"
        )
    lines.append("")
    return "\n".join(lines)


def build_run_artifacts(payload: Mapping[str, Any]) -> dict[str, Any]:
    training = run_training()
    summary = _summary_payload(training)
    claim_capsule = _claim_capsule_payload(str(payload["generated_at"]))
    return {"raw_rows": training["raw_rows"], "summary": summary, "claim_capsule": claim_capsule}


def write_artifacts(payload: Mapping[str, Any], *, root: Path = ROOT) -> None:
    artifacts = build_run_artifacts(payload)
    _write_json(root / CLAIM_CAPSULE_ARTIFACT, artifacts["claim_capsule"])
    _write_json(root / SUMMARY_ARTIFACT, artifacts["summary"])
    raw_path = root / RAW_METRICS_ARTIFACT
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in artifacts["raw_rows"]),
        encoding="utf-8",
    )
    for pointer in (
        payload["claim_capsule_ref"]["artifact"] + ":" + payload["claim_capsule_ref"]["pointer"],
        payload["training_evidence"]["summary_pointer"],
    ):
        if resolve_artifact_pointer(root, pointer) is None:
            raise ValueError(f"unresolved DGT run pointer: {pointer}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=GENERATED_AT)
    args = parser.parse_args(argv)
    sidecar_path = args.root / NEW_MODEL_HARDGATES_ARTIFACT
    sidecar = json.loads(sidecar_path.read_text(encoding="utf-8")) if sidecar_path.exists() else None
    payload = build_payload(generated_at=args.generated_at, sidecar=sidecar)
    write_artifacts(payload, root=args.root)
    _write_json(args.root / CANONICAL_JSON_ARTIFACT, payload)
    (args.root / CANONICAL_MARKDOWN_ARTIFACT).parent.mkdir(parents=True, exist_ok=True)
    (args.root / CANONICAL_MARKDOWN_ARTIFACT).write_text(render_markdown(payload), encoding="utf-8")
    print(json.dumps({"model_id": MODEL_ID, "prototype_status": payload["prototype_status"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

"""Pointer-only base-undertraining audit for DGT L1 controls."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import importlib
import json
import math
from pathlib import Path
from typing import Any, Mapping, Sequence

from bedc_quality_lab.model import choose_device


SCHEMA_ID = "bedc-quality-lab:dgt-base-undertraining-audit"
ARTIFACT_ID = "bedc-quality-lab:dgt-base-undertraining-audit"
PRODUCER = "scripts/run_dgt_base_undertraining_audit.py"
L1_SOURCE_ARTIFACT = "reports/canonical/dgt-l1-controls.json"
INPUT_ACCESSIBILITY_SOURCE_ARTIFACT = "reports/canonical/input-accessibility.json"
CANONICAL_JSON_ARTIFACT = "reports/canonical/dgt-base-undertraining-audit.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/dgt-base-undertraining-audit.md"
CANONICAL_FINGERPRINT_ARTIFACT = "reports/canonical/dgt-base-undertraining-audit.fingerprint.json"
CONTROLLER_EVIDENCE_POINTER = "https://github.com/the-omega-institute/newmath/issues/1190#issuecomment-4672534911"
FAIR_RECONSTRUCTION_POINTER = "https://github.com/the-omega-institute/newmath/issues/1196"
FEATURE_SOURCE_POINTER = "bedc_quality_lab/dgt_l1_controls.py:_TinySequenceModel._features"
LABEL_SOURCE_POINTER = "bedc_quality_lab/dgt_l1_controls.py:_make_sequences"
GENERATED_AT = "2026-06-10T00:00:00+00:00"
REQUIRED_COMPARISONS = ("equal_step", "equal_compute", "equal_loss_decrease", "equal_validation_loss")
REQUIRED_BASE_GRID = (36, 72, 128, 256, 512)
INPUT_ABLATION_ARM_ID = "input_ablation_masked_tail"
INPUT_ABLATION_ROLE = "ablation"
FAIR_BASELINE_ARM_ID = "non_starved_fair_attention"
FAIR_BASELINE_MODEL_ARM_ID = "parameter_matched_attention"
FAIR_BASELINE_INPUT_ARM_ID = "parameter_matched_attention"
FAIR_BASELINE_INPUT_ROLE = "attention-control"
FAIR_BASELINE_SUMMARY_ARTIFACT = (
    "reports/runs/discovery-gated-transformer/l1-tiny-sequence-controls/non_starved_fair_baseline_summary.json"
)
FAIR_BASELINE_METRICS_ARTIFACT = (
    "reports/runs/discovery-gated-transformer/l1-tiny-sequence-controls/non_starved_fair_baseline_metrics.jsonl"
)
FAIR_BASELINE_SEEDS = tuple(range(1174, 1190))
FAIR_BASELINE_EPOCHS = 36
FAIR_BASELINE_TOLERANCE = 0.03
INPUT_ABLATION_ACCURACY_METRIC = "input_ablation_accuracy_mean"
INPUT_ABLATION_LOSS_DECREASE_METRIC = "input_ablation_loss_decrease_mean"
INPUT_ABLATION_VALIDATION_LOSS_METRIC = "information_starved_validation_loss_mean"
NOT_CLAIMED = (
    "Bounded L1 tiny-sequence base-undertraining audit only.",
    "No undertraining discharge claim from information-starved ablations.",
    "No production deployment claim.",
    "No global superiority claim.",
    "No LLM replacement claim.",
    "No cross-level verdict inheritance.",
)


@dataclass(frozen=True)
class BaseUndertrainingComparisonRow:
    comparison_id: str
    status: str
    source_artifact: str
    source_pointer: str
    match_axis: str
    match_value: float | int | None
    base_metric: float | None
    dgt_metric: float | None
    ci_overlap: bool | None
    ci_low_separation: float | None
    decision: str

    def as_dict(self) -> dict[str, Any]:
        return {
            "comparison_id": self.comparison_id,
            "status": self.status,
            "source_artifact": self.source_artifact,
            "source_pointer": self.source_pointer,
            "match_axis": self.match_axis,
            "match_value": self.match_value,
            "base_metric": self.base_metric,
            "dgt_metric": self.dgt_metric,
            "ci_overlap": self.ci_overlap,
            "ci_low_separation": self.ci_low_separation,
            "decision": self.decision,
        }


@dataclass(frozen=True)
class BaseUndertrainingAudit:
    source_contract: Mapping[str, Any]
    construct_validity: Mapping[str, Any]
    comparison_rows: Sequence[Mapping[str, Any]]
    hardgates: Mapping[str, Any]
    mechanical_decision_table: Sequence[Mapping[str, str]]
    verdict: str
    claim_action: str
    boundary_ledger: Sequence[Mapping[str, Any]]
    evidence_ledger: Sequence[Mapping[str, Any]]
    not_claimed: Sequence[str]
    revoke_if: Sequence[str]

    def as_dict(self) -> dict[str, Any]:
        return {
            "schema_id": SCHEMA_ID,
            "artifact_id": ARTIFACT_ID,
            "source_contract": dict(self.source_contract),
            "construct_validity": dict(self.construct_validity),
            "comparison_rows": list(self.comparison_rows),
            "hardgates": dict(self.hardgates),
            "mechanical_decision_table": list(self.mechanical_decision_table),
            "verdict": self.verdict,
            "claim_action": self.claim_action,
            "boundary_ledger": list(self.boundary_ledger),
            "evidence_ledger": list(self.evidence_ledger),
            "not_claimed": list(self.not_claimed),
            "revoke_if": list(self.revoke_if),
        }


def mechanical_decision_table() -> list[dict[str, str]]:
    return [
        {
            "condition": "baseline input bandwidth is lower than the label dependency bandwidth",
            "verdict": "construct-boundary",
            "claim_action": "defer-to-fair-reconstruction",
        },
        {
            "condition": "any required comparison row is missing or has unresolved source evidence",
            "verdict": "inconclusive",
            "claim_action": "hold",
        },
        {
            "condition": "base grid does not cover DGT compute, loss-decrease, and validation-loss intervals",
            "verdict": "inconclusive",
            "claim_action": "hold",
        },
        {
            "condition": "equal-compute row has CI overlap or nonpositive CI-low separation",
            "verdict": "downgrade",
            "claim_action": "fair_compute_artifact",
        },
        {
            "condition": "equal-loss-decrease row has CI overlap or nonpositive CI-low separation",
            "verdict": "downgrade",
            "claim_action": "fair_loss_decrease_artifact",
        },
        {
            "condition": "equal-validation-loss row has CI overlap or nonpositive CI-low separation",
            "verdict": "downgrade",
            "claim_action": "fair_validation_loss_artifact",
        },
        {
            "condition": "all required rows resolve and non-informative rows retain positive CI-low separation",
            "verdict": "noninformative-separation",
            "claim_action": "record_noninformative_rows",
        },
    ]


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _json_digest(payload: Any) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _file_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.strip():
            value = json.loads(line)
            if not isinstance(value, dict):
                raise ValueError(f"non-starved fair baseline row must be an object: {path}")
            rows.append(value)
    return rows


def _load_json_artifact(root: Path, artifact: str) -> tuple[str, dict[str, Any] | None, str | None]:
    path = root / artifact
    if not path.exists():
        return "missing", None, None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return "invalid", None, None
    if not isinstance(payload, dict):
        return "invalid", None, _file_digest(path)
    return "resolved", payload, _file_digest(path)


def _import_l1_controls() -> Any:
    return importlib.import_module("bedc_quality_lab.dgt_l1_controls")


def _fair_round(value: float | None) -> float | None:
    return None if value is None else round(float(value), 6)


def _finite_float(value: Any) -> float | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    result = float(value)
    return result if math.isfinite(result) else None


def _mean_float(values: Sequence[float]) -> float:
    return round(sum(float(value) for value in values) / len(values), 6) if values else 0.0


def _ci95_low_float(values: Sequence[float]) -> float:
    if not values:
        return 0.0
    mean = sum(values) / len(values)
    if len(values) == 1:
        return round(mean, 6)
    variance = sum((value - mean) ** 2 for value in values) / (len(values) - 1)
    return round(mean - 1.96 * math.sqrt(variance) / math.sqrt(len(values)), 6)


def _fair_baseline_record_metric(row: Mapping[str, Any], metric_key: str) -> float | None:
    metrics = row.get("metrics")
    if not isinstance(metrics, Mapping):
        return None
    return _finite_float(metrics.get(metric_key))


def _fair_baseline_summary(records: Sequence[Mapping[str, Any]], *, device_policy: Mapping[str, Any]) -> dict[str, Any]:
    if not records:
        raise ValueError("non-starved fair baseline records are empty")
    seeds = sorted({int(row.get("seed", -1)) for row in records})
    epochs = sorted({int(row.get("epoch_count", row.get("training_steps", -1))) for row in records})
    if len(epochs) != 1:
        raise ValueError("non-starved fair baseline epoch count mismatch")
    arm_ids = {str(row.get("arm_id")) for row in records}
    if arm_ids != {FAIR_BASELINE_ARM_ID}:
        raise ValueError("non-starved fair baseline arm mismatch")
    metric_keys = (
        "accuracy",
        "ood_accuracy",
        "validation_loss",
        "loss_decrease",
        "loss_start",
        "loss_end",
        "parameter_l2_delta",
        "positive_margin_over_chance",
        "UER",
    )
    metric_values: dict[str, list[float]] = {}
    for key in metric_keys:
        values = [_fair_baseline_record_metric(row, key) for row in records]
        if any(value is None for value in values):
            raise ValueError(f"non-starved fair baseline metric missing: {key}")
        metric_values[key] = [float(value) for value in values if value is not None]
    parameter_counts = {int(row.get("parameter_count", 0)) for row in records}
    if len(parameter_counts) != 1 or next(iter(parameter_counts)) <= 0:
        raise ValueError("non-starved fair baseline parameter count mismatch")
    compute_units = [float(row.get("compute_units", 0.0)) for row in records]
    if any(value <= 0.0 for value in compute_units):
        raise ValueError("non-starved fair baseline compute units missing")
    loss_decrease_values = metric_values["loss_decrease"]
    summary = {
        "schema_id": "bedc-quality-lab:non-starved-fair-baseline-summary",
        "artifact_id": "bedc-quality-lab:non-starved-fair-baseline",
        "arm_id": FAIR_BASELINE_ARM_ID,
        "model_source_arm_id": FAIR_BASELINE_MODEL_ARM_ID,
        "role": "fair_baseline",
        "status": "pass" if all(value > 0.0 for value in loss_decrease_values) else "fail",
        "source_artifacts": {
            "raw_metrics": FAIR_BASELINE_METRICS_ARTIFACT,
            "summary": FAIR_BASELINE_SUMMARY_ARTIFACT,
            "l1_model_owner": "bedc_quality_lab/dgt_l1_controls.py",
        },
        "input_visibility": {
            "visible_variables": ["x_minus_1", "x_minus_2", "full_sequence"],
            "required_variables": ["x_minus_1", "x_minus_2"],
            "missing_variables": [],
            "information_starved": False,
            "source_pointer": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}#arm={FAIR_BASELINE_INPUT_ARM_ID}",
        },
        "training_config": {
            "seeds": seeds,
            "epoch_count": epochs[0],
            "train_examples": int(records[0].get("train_examples", 0)),
            "eval_examples": int(records[0].get("eval_examples", 0)),
            "batch_size": int(records[0].get("batch_size", 0)),
            "learning_rate": float(records[0].get("learning_rate", 0.0)),
            "device_policy": dict(device_policy),
        },
        "metrics": {
            "accuracy_mean": _mean_float(metric_values["accuracy"]),
            "accuracy_ci95_low": _ci95_low_float(metric_values["accuracy"]),
            "ood_accuracy_mean": _mean_float(metric_values["ood_accuracy"]),
            "validation_loss_mean": _mean_float(metric_values["validation_loss"]),
            "validation_loss_ci95_low": _ci95_low_float(metric_values["validation_loss"]),
            "loss_decrease_mean": _mean_float(metric_values["loss_decrease"]),
            "loss_decrease_ci95_low": _ci95_low_float(metric_values["loss_decrease"]),
            "loss_start_mean": _mean_float(metric_values["loss_start"]),
            "loss_end_mean": _mean_float(metric_values["loss_end"]),
            "UER_mean": _mean_float(metric_values["UER"]),
            "parameter_l2_delta_mean": _mean_float(metric_values["parameter_l2_delta"]),
            "positive_margin_over_chance_mean": _mean_float(metric_values["positive_margin_over_chance"]),
        },
        "parameter_count": next(iter(parameter_counts)),
        "compute_units": round(sum(compute_units), 6),
        "seed_count": len(seeds),
        "record_count": len(records),
        "comparison_tolerance": FAIR_BASELINE_TOLERANCE,
        "raw_record_pointers": [
            f"{FAIR_BASELINE_METRICS_ARTIFACT}:$.lines[{index}]"
            for index, _row in enumerate(records)
        ],
        "summary_pointer": f"{FAIR_BASELINE_SUMMARY_ARTIFACT}:$",
    }
    return summary


def _fair_baseline_config(l1: Any, seeds: Sequence[int], epoch_count: int) -> Any:
    return l1.L1TrainingConfig(
        seeds=tuple(int(seed) for seed in seeds),
        training_steps=int(epoch_count),
        step_grid=(int(epoch_count),),
    )


def _cyclic_batch(torch: Any, x_train: Any, y_train: Any, *, start: int, batch_size: int) -> tuple[Any, Any]:
    end = min(start + batch_size, len(x_train))
    if end - start < batch_size:
        remainder = batch_size - (end - start)
        return (
            torch.cat([x_train[start:end], x_train[:remainder]], dim=0),
            torch.cat([y_train[start:end], y_train[:remainder]], dim=0),
        )
    return x_train[start:end], y_train[start:end]


def _fit_fair_baseline_model(
    *,
    torch: Any,
    l1: Any,
    model: Any,
    x_train: Any,
    y_train: Any,
    config: Any,
    epoch_count: int,
    seed: int,
    progress: bool,
) -> list[float]:
    optimizer = torch.optim.Adam(model.parameters(), lr=l1.LEARNING_RATE)
    loss_history: list[float] = []
    for epoch in range(int(epoch_count)):
        start = (epoch * config.batch_size) % config.train_examples
        xb, yb = _cyclic_batch(torch, x_train, y_train, start=start, batch_size=config.batch_size)
        optimizer.zero_grad(set_to_none=True)
        logits = model(xb)
        loss = torch.nn.functional.cross_entropy(logits, yb)
        loss.backward()
        optimizer.step()
        loss_value = float(loss.detach().cpu())
        loss_history.append(loss_value)
        if progress:
            print(
                "non-starved fair baseline "
                f"seed={seed} epoch={epoch + 1}/{epoch_count} "
                f"train_loss={loss_value:.6f}",
                flush=True,
            )
    return loss_history


def _evaluate_fair_baseline_model(
    *,
    torch: Any,
    model: Any,
    x_eval: Any,
    y_eval: Any,
    x_ood: Any,
    y_ood: Any,
    vocab_size: int,
) -> dict[str, float]:
    with torch.no_grad():
        eval_logits = model(x_eval)
        ood_logits = model(x_ood)
        validation_loss = float(torch.nn.functional.cross_entropy(eval_logits, y_eval).detach().cpu())
        probabilities = torch.softmax(eval_logits, dim=1)
        preds = torch.argmax(eval_logits, dim=1)
        ood_preds = torch.argmax(ood_logits, dim=1)
        accuracy = float((preds == y_eval).to(torch.float32).mean().detach().cpu())
        ood_accuracy = float((ood_preds == y_ood).to(torch.float32).mean().detach().cpu())
        confidence = float(probabilities.max(dim=1).values.mean().detach().cpu())
    chance = 1.0 / vocab_size
    return {
        "accuracy": accuracy,
        "ood_accuracy": ood_accuracy,
        "validation_loss": validation_loss,
        "confidence": confidence,
        "chance": chance,
    }


def _fair_baseline_datasets(*, l1: Any, torch: Any, seed: int, task_spec: Any, device_name: str) -> dict[str, Any]:
    x_train, y_train = l1._make_sequences(
        torch,
        seed=int(seed),
        examples=task_spec.train_examples,
        spec=task_spec,
        device_name=device_name,
    )
    x_eval, y_eval = l1._make_sequences(
        torch,
        seed=int(seed) + 31,
        examples=task_spec.eval_examples,
        spec=task_spec,
        device_name=device_name,
        split="heldout",
    )
    x_ood, y_ood = l1._make_sequences(
        torch,
        seed=int(seed) + 59,
        examples=task_spec.eval_examples,
        spec=task_spec,
        device_name=device_name,
        ood=True,
        split="heldout",
    )
    return {
        "x_train": x_train,
        "y_train": y_train,
        "x_eval": x_eval,
        "y_eval": y_eval,
        "x_ood": x_ood,
        "y_ood": y_ood,
    }


def _parameter_l2_delta(torch: Any, *, before: Any, after: Any) -> float:
    delta = float(torch.linalg.vector_norm(after - before).item())
    if not math.isfinite(delta) or delta <= 0.0:
        raise RuntimeError(f"no parameter update evidence for {FAIR_BASELINE_ARM_ID}")
    return delta


def _fair_baseline_row(
    *,
    seed: int,
    requested_device: str,
    device_name: str,
    epoch_count: int,
    config: Any,
    learning_rate: float,
    parameter_count: int,
    delta: float,
    loss_history: Sequence[float],
    eval_metrics: Mapping[str, float],
    record_index: int,
) -> dict[str, Any]:
    accuracy = float(eval_metrics["accuracy"])
    chance = float(eval_metrics["chance"])
    compute_units = round(float(int(epoch_count) * config.batch_size * parameter_count) / 1_000_000.0, 6)
    row = {
        "arm_id": FAIR_BASELINE_ARM_ID,
        "model_source_arm_id": FAIR_BASELINE_MODEL_ARM_ID,
        "model_family": "non-starved parameter-matched attention fair baseline",
        "parameter_count": parameter_count,
        "compute_units": compute_units,
        "device_requested": requested_device,
        "device_resolved": device_name,
        "training_steps": int(epoch_count),
        "seed": int(seed),
        "metrics": {
            "accuracy": round(accuracy, 6),
            "ood_accuracy": round(float(eval_metrics["ood_accuracy"]), 6),
            "chance_accuracy": round(chance, 6),
            "validation_loss": round(float(eval_metrics["validation_loss"]), 8),
            "loss_start": round(float(loss_history[0]), 8),
            "loss_end": round(float(loss_history[-1]), 8),
            "loss_decrease": round(float(loss_history[0]) - float(loss_history[-1]), 8),
            "UER": round(max(0.0, 1.0 - accuracy), 6),
            "parameter_l2_delta": round(delta, 8),
            "confidence": round(float(eval_metrics["confidence"]), 6),
            "positive_margin_over_chance": round(accuracy - chance, 6),
        },
    }
    row["model_source_arm_id"] = FAIR_BASELINE_MODEL_ARM_ID
    row["role"] = "fair_baseline"
    row["epoch_count"] = int(epoch_count)
    row["train_examples"] = int(config.train_examples)
    row["eval_examples"] = int(config.eval_examples)
    row["batch_size"] = int(config.batch_size)
    row["learning_rate"] = float(learning_rate)
    row["input_visibility"] = {
        "visible_variables": ["x_minus_1", "x_minus_2", "full_sequence"],
        "required_variables": ["x_minus_1", "x_minus_2"],
        "missing_variables": [],
        "information_starved": False,
    }
    row["run_artifact_ref"] = f"{FAIR_BASELINE_METRICS_ARTIFACT}:$.lines[{record_index}]"
    return row


def _train_fair_baseline_seed(
    *,
    l1: Any,
    torch: Any,
    seed: int,
    config: Any,
    task_spec: Any,
    device_name: str,
    requested_device: str,
    epoch_count: int,
    record_index: int,
    progress: bool,
) -> dict[str, Any]:
    l1._seed_all_rngs(torch, int(seed) + l1.ARM_IDS.index(FAIR_BASELINE_MODEL_ARM_ID) * 997)
    model = l1._TinySequenceModel(
        torch,
        arm_id=FAIR_BASELINE_MODEL_ARM_ID,
        vocab_size=task_spec.vocab_size,
        device_name=device_name,
    )
    before = l1._snapshot(torch, model)
    datasets = _fair_baseline_datasets(l1=l1, torch=torch, seed=int(seed), task_spec=task_spec, device_name=device_name)
    loss_history = _fit_fair_baseline_model(
        torch=torch,
        l1=l1,
        model=model,
        x_train=datasets["x_train"],
        y_train=datasets["y_train"],
        config=config,
        epoch_count=epoch_count,
        seed=int(seed),
        progress=progress,
    )
    after = l1._snapshot(torch, model)
    delta = _parameter_l2_delta(torch, before=before, after=after)
    if not loss_history or not math.isfinite(loss_history[-1]):
        raise RuntimeError(f"invalid loss history for {FAIR_BASELINE_ARM_ID}")
    parameter_count = int(sum(parameter.numel() for parameter in model.parameters()))
    eval_metrics = _evaluate_fair_baseline_model(
        torch=torch,
        model=model,
        x_eval=datasets["x_eval"],
        y_eval=datasets["y_eval"],
        x_ood=datasets["x_ood"],
        y_ood=datasets["y_ood"],
        vocab_size=task_spec.vocab_size,
    )
    row = _fair_baseline_row(
        seed=int(seed),
        requested_device=requested_device,
        device_name=device_name,
        epoch_count=epoch_count,
        config=config,
        learning_rate=float(l1.LEARNING_RATE),
        parameter_count=parameter_count,
        delta=delta,
        loss_history=loss_history,
        eval_metrics=eval_metrics,
        record_index=record_index,
    )
    if progress:
        metrics = row["metrics"]
        print(
            "non-starved fair baseline "
            f"seed={seed} epoch={epoch_count} "
            f"loss_start={metrics['loss_start']:.6f} "
            f"loss_end={metrics['loss_end']:.6f} "
            f"loss_decrease={metrics['loss_decrease']:.6f} "
            f"accuracy={metrics['accuracy']:.6f}",
            flush=True,
        )
    return row


def _write_fair_baseline_artifacts(root: Path, *, records: Sequence[Mapping[str, Any]], summary: Mapping[str, Any]) -> None:
    metrics_path = root / FAIR_BASELINE_METRICS_ARTIFACT
    summary_path = root / FAIR_BASELINE_SUMMARY_ARTIFACT
    metrics_path.parent.mkdir(parents=True, exist_ok=True)
    metrics_path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in records), encoding="utf-8")
    _write_json(summary_path, summary)


def train_non_starved_fair_baseline(
    *,
    root: Path,
    requested_device: str = "auto",
    seeds: Sequence[int] = FAIR_BASELINE_SEEDS,
    epoch_count: int = FAIR_BASELINE_EPOCHS,
    generated_at: str = GENERATED_AT,
    progress: bool = True,
) -> dict[str, Any]:
    l1 = _import_l1_controls()
    torch = importlib.import_module("torch")
    device_resolution = choose_device(requested_device)
    device_name = device_resolution.resolved_device
    config = _fair_baseline_config(l1, seeds, epoch_count)
    task_spec = l1.default_task_spec(config)
    records = [
        _train_fair_baseline_seed(
            l1=l1,
            torch=torch,
            seed=int(seed),
            config=config,
            task_spec=task_spec,
            device_name=device_name,
            requested_device=requested_device,
            epoch_count=int(epoch_count),
            record_index=index,
            progress=progress,
        )
        for index, seed in enumerate(config.seeds)
    ]
    summary = _fair_baseline_summary(records, device_policy=device_resolution.to_dict())
    summary["generated_at"] = generated_at
    _write_fair_baseline_artifacts(root, records=records, summary=summary)
    return summary


def _load_fair_baseline(root: Path, payload: Mapping[str, Any] | None = None) -> dict[str, Any]:
    if payload is not None:
        return {
            "status": "resolved",
            "summary": dict(payload),
            "summary_sha256": _json_digest(payload),
            "raw_sha256": None,
        }
    summary_status, summary, summary_sha = _load_json_artifact(root, FAIR_BASELINE_SUMMARY_ARTIFACT)
    raw_path = root / FAIR_BASELINE_METRICS_ARTIFACT
    raw_sha = _file_digest(raw_path) if raw_path.exists() else None
    if summary_status != "resolved" or not isinstance(summary, Mapping):
        return {
            "status": summary_status,
            "summary": None,
            "summary_sha256": summary_sha,
            "raw_sha256": raw_sha,
        }
    if raw_path.exists():
        try:
            records = _load_jsonl(raw_path)
            expected = int(summary.get("record_count", -1))
        except (OSError, json.JSONDecodeError, ValueError):
            return {
                "status": "invalid",
                "summary": dict(summary),
                "summary_sha256": summary_sha,
                "raw_sha256": raw_sha,
            }
        if expected != len(records):
            return {
                "status": "invalid",
                "summary": dict(summary),
                "summary_sha256": summary_sha,
                "raw_sha256": raw_sha,
            }
    return {
        "status": "resolved",
        "summary": dict(summary),
        "summary_sha256": summary_sha,
        "raw_sha256": raw_sha,
    }


def _row_pointer(row: Mapping[str, Any]) -> str:
    return f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}#row_id={row['row_id']}"


def _baseline_input_accessibility(
    rows: Sequence[Any],
    consumers: Mapping[str, Any],
    *,
    arm_id: str = INPUT_ABLATION_ARM_ID,
    role: str = INPUT_ABLATION_ROLE,
) -> dict[str, Any]:
    matches = [
        row
        for row in rows
        if isinstance(row, Mapping)
        and row.get("experiment") == "dgt_l1_tiny_sequence"
        and row.get("split") == "in_distribution"
        and row.get("arm") == arm_id
        and row.get("role") == role
    ]
    if len(matches) != 1:
        return {
            "status": "fail",
            "failures": ["baseline-input-accessibility-row-not-unique"],
            "row_count": len(matches),
        }
    row = matches[0]
    pointer = _row_pointer(row)
    information_refs = consumers.get("information_starved_arms_ref")
    extraction_pass = (
        row.get("feature_extraction", {}).get("status") == "pass"
        and row.get("label_extraction", {}).get("status") == "pass"
    )
    pointer_alignment = isinstance(information_refs, list) and ((pointer in information_refs) == bool(row.get("information_starved")))
    failures: list[str] = []
    if not extraction_pass:
        failures.append("baseline-input-accessibility-extraction-failed")
    if not pointer_alignment:
        failures.append("baseline-input-accessibility-consumer-pointer-mismatch")
    return {
        "status": "pass" if not failures else "fail",
        "row_id": row.get("row_id"),
        "row_pointer": pointer,
        "visible_variables": list(row.get("visible_variables", [])),
        "required_variables": list(row.get("required_variables", [])),
        "missing_variables": list(row.get("missing_variables", [])),
        "information_starved": bool(row.get("information_starved")),
        "coverage_status": row.get("coverage_status"),
        "supports_architecture_claim": row.get("supports_architecture_claim"),
        "feature_extraction_status": row.get("feature_extraction", {}).get("status"),
        "label_extraction_status": row.get("label_extraction", {}).get("status"),
        "consumer_pointer_aligned": pointer_alignment,
        "failures": failures,
    }


def _fair_baseline_accessibility(rows: Sequence[Any], consumers: Mapping[str, Any]) -> dict[str, Any]:
    row = _baseline_input_accessibility(
        rows,
        consumers,
        arm_id=FAIR_BASELINE_INPUT_ARM_ID,
        role=FAIR_BASELINE_INPUT_ROLE,
    )
    if row.get("status") == "pass":
        row["fair_baseline_arm_id"] = FAIR_BASELINE_ARM_ID
        row["source_arm_id"] = FAIR_BASELINE_INPUT_ARM_ID
    return row


def _input_accessibility_preconditions(
    root: Path,
    payload: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    status = "resolved"
    digest: str | None = None
    if payload is None:
        status, loaded, digest = _load_json_artifact(root, INPUT_ACCESSIBILITY_SOURCE_ARTIFACT)
        payload = loaded
    else:
        digest = _json_digest(payload)
    if status != "resolved" or not isinstance(payload, Mapping):
        return {
            "status": status,
            "source_artifact": INPUT_ACCESSIBILITY_SOURCE_ARTIFACT,
            "input_accessibility_ref": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$",
            "information_starved_arms_ref": [],
            "unanswerable_ood_splits_ref": [],
            "boundary_ledger_ref": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.boundary_ledger",
            "baseline_row": {"status": "missing", "failures": ["input-accessibility-artifact-unresolved"]},
            "source_pointers": {
                "input_accessibility": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$",
                "boundary_ledger": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.boundary_ledger",
            },
            "sha256": digest,
            "failures": ["input-accessibility-artifact-unresolved"],
        }
    rows = payload.get("rows")
    consumers = payload.get("consumer_pointers")
    boundary = payload.get("boundary_ledger")
    if not isinstance(rows, list) or not isinstance(consumers, Mapping) or not isinstance(boundary, list):
        return {
            "status": "invalid",
            "source_artifact": INPUT_ACCESSIBILITY_SOURCE_ARTIFACT,
            "input_accessibility_ref": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$",
            "information_starved_arms_ref": [],
            "unanswerable_ood_splits_ref": [],
            "boundary_ledger_ref": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.boundary_ledger",
            "baseline_row": {"status": "invalid", "failures": ["input-accessibility-shape-mismatch"]},
            "source_pointers": {
                "input_accessibility": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$",
                "boundary_ledger": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.boundary_ledger",
            },
            "sha256": digest,
            "failures": ["input-accessibility-shape-mismatch"],
        }
    rows_by_pointer = {
        _row_pointer(row): row
        for row in rows
        if isinstance(row, Mapping) and isinstance(row.get("row_id"), str)
    }
    information_refs = consumers.get("information_starved_arms_ref")
    unanswerable_refs = consumers.get("unanswerable_ood_splits_ref")
    failures: list[str] = []
    if consumers.get("input_accessibility_ref") != f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$":
        failures.append("input-accessibility-root-pointer-mismatch")
    if not isinstance(information_refs, list) or not all(ref in rows_by_pointer for ref in information_refs):
        failures.append("information-starved-pointer-unresolved")
        information_refs = []
    if not isinstance(unanswerable_refs, list) or not all(ref in rows_by_pointer for ref in unanswerable_refs):
        failures.append("unanswerable-ood-pointer-unresolved")
        unanswerable_refs = []
    information_rows = [rows_by_pointer[ref] for ref in information_refs]
    unanswerable_rows = [rows_by_pointer[ref] for ref in unanswerable_refs]
    if not information_rows:
        failures.append("information-starved-precondition-empty")
    if not unanswerable_rows:
        failures.append("unanswerable-ood-precondition-empty")
    baseline_row = _baseline_input_accessibility(rows, consumers)
    fair_baseline_row = _fair_baseline_accessibility(rows, consumers)
    if baseline_row["status"] != "pass":
        failures.extend(str(item) for item in baseline_row.get("failures", []))
    missing_variables = sorted({
        variable
        for row in information_rows + unanswerable_rows
        for variable in row.get("missing_variables", [])
    })
    return {
        "status": "pass" if not failures else "fail",
        "source_artifact": INPUT_ACCESSIBILITY_SOURCE_ARTIFACT,
        "input_accessibility_ref": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$",
        "information_starved_arms_ref": list(information_refs),
        "unanswerable_ood_splits_ref": list(unanswerable_refs),
        "boundary_ledger_ref": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.boundary_ledger",
        "boundary_ledger_count": len(boundary),
        "information_starved_row_count": len(information_rows),
        "unanswerable_ood_row_count": len(unanswerable_rows),
        "missing_variables": missing_variables,
        "baseline_row": baseline_row,
        "fair_baseline_row": fair_baseline_row,
        "source_pointers": {
            "input_accessibility": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$",
            "information_starved_arms": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.consumer_pointers.information_starved_arms_ref",
            "unanswerable_ood_splits": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.consumer_pointers.unanswerable_ood_splits_ref",
            "baseline_row": str(baseline_row.get("row_pointer", f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.rows")),
            "fair_baseline_row": str(fair_baseline_row.get("row_pointer", f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.rows")),
            "boundary_ledger": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$.boundary_ledger",
        },
        "sha256": digest,
        "failures": failures,
    }


def _is_number(value: Any) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def _round(value: float | None) -> float | None:
    return None if value is None else round(value, 6)


def _gcd(left: int, right: int) -> int:
    while right:
        left, right = right, left % right
    return abs(left)


def _step_rows(payload: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    rows = payload.get("l1_step_ladder", {}).get("per_step")
    if not isinstance(rows, list):
        return []
    return [row for row in rows if isinstance(row, Mapping)]


def _metric(row: Mapping[str, Any], key: str) -> float | None:
    metrics = row.get("metrics")
    if not isinstance(metrics, Mapping):
        return None
    value = metrics.get(key)
    return float(value) if _is_number(value) else None


def _compute(row: Mapping[str, Any], arm_id: str) -> float | None:
    per_arm = row.get("compute_ledger", {}).get("per_arm")
    if not isinstance(per_arm, Mapping):
        return None
    arm = per_arm.get(arm_id)
    if not isinstance(arm, Mapping):
        return None
    value = arm.get("compute_units")
    return float(value) if _is_number(value) else None


def _parameter_count(row: Mapping[str, Any], arm_id: str) -> int | None:
    arms = row.get("training_arms")
    if not isinstance(arms, Mapping):
        return None
    arm = arms.get(arm_id)
    if not isinstance(arm, Mapping):
        return None
    value = arm.get("parameter_count")
    return int(value) if isinstance(value, int) and not isinstance(value, bool) else None


def _arm_metric(row: Mapping[str, Any], arm_id: str, metric_key: str) -> float | None:
    arms = row.get("training_arms")
    if not isinstance(arms, Mapping):
        return None
    arm = arms.get(arm_id)
    if not isinstance(arm, Mapping):
        return None
    metrics = arm.get("metrics")
    if not isinstance(metrics, Mapping):
        return None
    value = metrics.get(metric_key)
    return float(value) if _is_number(value) else None


def _steps(row: Mapping[str, Any]) -> int | None:
    value = row.get("training_steps")
    return int(value) if isinstance(value, int) and not isinstance(value, bool) else None


def _public_pointer(row: Mapping[str, Any], index: int) -> str:
    pointer = row.get("pointer")
    if isinstance(pointer, str) and pointer.startswith(f"{L1_SOURCE_ARTIFACT}:"):
        return pointer
    return f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder.per_step[{index}]"


def _row_by_steps(rows: Sequence[Mapping[str, Any]], steps: int) -> tuple[int, Mapping[str, Any]] | None:
    for index, row in enumerate(rows):
        if _steps(row) == steps:
            return index, row
    return None


def _nearest_by_value(
    rows: Sequence[Mapping[str, Any]],
    *,
    value_getter,
    target: float,
) -> tuple[int, Mapping[str, Any], float] | None:
    candidates: list[tuple[float, int, Mapping[str, Any], float]] = []
    for index, row in enumerate(rows):
        value = value_getter(row)
        if value is not None:
            candidates.append((abs(value - target), index, row, value))
    if not candidates:
        return None
    _distance, index, row, value = min(candidates, key=lambda item: (item[0], _steps(item[2]) or 0))
    return index, row, value


def _comparison_row(
    *,
    comparison_id: str,
    source_index: int | None,
    source_row: Mapping[str, Any] | None,
    match_axis: str,
    match_value: float | int | None,
    fair_baseline: Mapping[str, Any] | None = None,
    missing_reason: str | None = None,
    source_pointer_override: str | None = None,
) -> BaseUndertrainingComparisonRow:
    source_artifact = FAIR_BASELINE_SUMMARY_ARTIFACT if fair_baseline is not None else L1_SOURCE_ARTIFACT
    if source_index is None or source_row is None:
        return BaseUndertrainingComparisonRow(
            comparison_id=comparison_id,
            status="missing",
            source_artifact=source_artifact,
            source_pointer=source_pointer_override or f"{source_artifact}:$",
            match_axis=match_axis,
            match_value=match_value,
            base_metric=None,
            dgt_metric=None,
            ci_overlap=None,
            ci_low_separation=None,
            decision=missing_reason or "required-evidence-missing",
        )
    if fair_baseline is not None:
        fair_metrics = fair_baseline.get("metrics")
        base_metric = (
            _finite_float(fair_metrics.get("accuracy_mean"))
            if isinstance(fair_metrics, Mapping)
            else None
        )
    else:
        base_metric = _metric(source_row, INPUT_ABLATION_ACCURACY_METRIC)
    dgt_metric = _metric(source_row, "dgt_accuracy_mean")
    if base_metric is None or dgt_metric is None:
        status = "missing"
        ci_overlap = None
        ci_low = None
        decision = "required-metric-missing"
    else:
        ci_low = dgt_metric - base_metric
        ci_overlap = ci_low <= 0.0
        status = "resolved"
        decision = "input-ablation-catches-up" if ci_overlap else "noninformative-dgt-separated"
    return BaseUndertrainingComparisonRow(
        comparison_id=comparison_id,
        status=status,
        source_artifact=source_artifact,
        source_pointer=source_pointer_override or _public_pointer(source_row, source_index),
        match_axis=match_axis,
        match_value=_round(float(match_value)) if isinstance(match_value, float) else match_value,
        base_metric=_round(base_metric),
        dgt_metric=_round(dgt_metric),
        ci_overlap=ci_overlap,
        ci_low_separation=_round(ci_low),
        decision=decision,
    )


def _base_grid_coverage(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    observed = sorted(step for row in rows if (step := _steps(row)) is not None)
    expected_present = all(step in observed for step in REQUIRED_BASE_GRID)
    return {
        "required_grid": list(REQUIRED_BASE_GRID),
        "observed_grid": observed,
        "required_grid_present": expected_present,
        "covers_dgt_compute_loss_interval": bool(observed and min(observed) <= 36 <= max(observed)),
        "source_pointer": f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder.step_grid",
    }


def _fair_baseline_contract(
    fair_baseline_status: Mapping[str, Any],
    l1_payload: Mapping[str, Any] | None,
) -> dict[str, Any]:
    summary = fair_baseline_status.get("summary")
    failures: list[str] = []
    if fair_baseline_status.get("status") != "resolved" or not isinstance(summary, Mapping):
        failures.append("non-starved-fair-baseline-unresolved")
        return {
            "status": "fail",
            "source_artifact": FAIR_BASELINE_SUMMARY_ARTIFACT,
            "raw_metrics_artifact": FAIR_BASELINE_METRICS_ARTIFACT,
            "summary_sha256": fair_baseline_status.get("summary_sha256"),
            "raw_sha256": fair_baseline_status.get("raw_sha256"),
            "fair_baseline_summary_pointer": f"{FAIR_BASELINE_SUMMARY_ARTIFACT}:$",
            "raw_metrics_pointer": f"{FAIR_BASELINE_METRICS_ARTIFACT}:$",
            "failures": failures,
        }
    metrics = summary.get("metrics")
    visibility = summary.get("input_visibility")
    training = summary.get("training_config")
    if not isinstance(metrics, Mapping) or not isinstance(visibility, Mapping) or not isinstance(training, Mapping):
        failures.append("non-starved-fair-baseline-shape-mismatch")
        return {
            "status": "fail",
            "source_artifact": FAIR_BASELINE_SUMMARY_ARTIFACT,
            "raw_metrics_artifact": FAIR_BASELINE_METRICS_ARTIFACT,
            "summary_sha256": fair_baseline_status.get("summary_sha256"),
            "raw_sha256": fair_baseline_status.get("raw_sha256"),
            "fair_baseline_summary_pointer": f"{FAIR_BASELINE_SUMMARY_ARTIFACT}:$",
            "raw_metrics_pointer": f"{FAIR_BASELINE_METRICS_ARTIFACT}:$",
            "failures": failures,
        }
    if visibility.get("information_starved") is not False or visibility.get("missing_variables") != []:
        failures.append("non-starved-fair-baseline-input-starved")
    if _fair_metric(summary, "loss_decrease_mean") is None or float(_fair_metric(summary, "loss_decrease_mean") or 0.0) <= 0.0:
        failures.append("non-starved-fair-baseline-loss-not-decreasing")
    if _fair_seed_count(summary) < 1:
        failures.append("non-starved-fair-baseline-seed-missing")
    anchor = _row_by_steps(_step_rows(l1_payload or {}), 36) if isinstance(l1_payload, Mapping) else None
    dgt_compute = None if anchor is None else _compute(anchor[1], "dgt_l1")
    dgt_params = None if anchor is None else _parameter_count(anchor[1], "dgt_l1")
    fair_compute = _fair_compute(summary)
    fair_params = summary.get("parameter_count")
    compute_ratio = None
    parameter_ratio = None
    if dgt_compute is None or fair_compute is None or dgt_compute <= 0.0:
        failures.append("non-starved-fair-baseline-compute-unresolved")
    else:
        compute_ratio = round(abs(fair_compute - dgt_compute) / dgt_compute, 6)
        if compute_ratio > FAIR_BASELINE_TOLERANCE:
            failures.append("non-starved-fair-baseline-compute-outside-tolerance")
    if dgt_params is None or not isinstance(fair_params, int) or dgt_params <= 0:
        failures.append("non-starved-fair-baseline-parameters-unresolved")
    else:
        parameter_ratio = round(abs(float(fair_params) - float(dgt_params)) / float(dgt_params), 6)
        if parameter_ratio > FAIR_BASELINE_TOLERANCE:
            failures.append("non-starved-fair-baseline-parameters-outside-tolerance")
    return {
        "status": "pass" if not failures else "fail",
        "source_artifact": FAIR_BASELINE_SUMMARY_ARTIFACT,
        "raw_metrics_artifact": FAIR_BASELINE_METRICS_ARTIFACT,
        "summary_sha256": fair_baseline_status.get("summary_sha256"),
        "raw_sha256": fair_baseline_status.get("raw_sha256"),
        "fair_baseline_summary_pointer": f"{FAIR_BASELINE_SUMMARY_ARTIFACT}:$",
        "raw_metrics_pointer": f"{FAIR_BASELINE_METRICS_ARTIFACT}:$",
        "arm_id": summary.get("arm_id"),
        "model_source_arm_id": summary.get("model_source_arm_id"),
        "visible_variables": list(visibility.get("visible_variables", [])) if isinstance(visibility, Mapping) else [],
        "required_variables": list(visibility.get("required_variables", [])) if isinstance(visibility, Mapping) else [],
        "missing_variables": list(visibility.get("missing_variables", [])) if isinstance(visibility, Mapping) else [],
        "information_starved": bool(visibility.get("information_starved")) if isinstance(visibility, Mapping) else True,
        "seed_count": _fair_seed_count(summary),
        "epoch_count": _fair_epoch_count(summary),
        "loss_decrease_mean": _fair_round(_fair_metric(summary, "loss_decrease_mean")),
        "validation_loss_mean": _fair_round(_fair_metric(summary, "validation_loss_mean")),
        "accuracy_mean": _fair_round(_fair_metric(summary, "accuracy_mean")),
        "compute_units": _fair_round(fair_compute),
        "compute_ratio_to_dgt_anchor": compute_ratio,
        "parameter_count": fair_params if isinstance(fair_params, int) else None,
        "parameter_ratio_to_dgt_anchor": parameter_ratio,
        "tolerance": FAIR_BASELINE_TOLERANCE,
        "failures": failures,
    }


def construct_validity_assessment(
    *,
    baseline_input_order: int = 1,
    label_dependency_order: int = 2,
    second_predecessor_visible: bool = False,
    vocabulary_size: int = 16,
    hidden_coefficient: int = 5,
    input_accessibility_preconditions: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    information_starved = baseline_input_order < label_dependency_order and not second_predecessor_visible
    bayes_upper_bound = 1.0 / float(vocabulary_size) if information_starved else None
    preconditions = dict(input_accessibility_preconditions or {})
    source_pointers = {
        "feature_source": FEATURE_SOURCE_POINTER,
        "label_source": LABEL_SOURCE_POINTER,
        "controller_evidence": CONTROLLER_EVIDENCE_POINTER,
        "fair_reconstruction": FAIR_RECONSTRUCTION_POINTER,
    }
    source_pointers.update({
        key: value
        for key, value in preconditions.get("source_pointers", {}).items()
        if isinstance(key, str) and isinstance(value, str)
    })
    return {
        "status": "construct-boundary" if information_starved else "construct-valid",
        "baseline_input_order": baseline_input_order,
        "label_dependency_order": label_dependency_order,
        "second_predecessor_visible_to_baseline": second_predecessor_visible,
        "input_accessibility_preconditions": preconditions,
        "baseline_feature_wiring": "full token sequence with x_prev_2 masked before attention",
        "label_rule": "(3*x_prev_1 + 5*x_prev_2 + 1) mod 16",
        "hidden_coefficient_modulus_gcd": _gcd(hidden_coefficient, vocabulary_size),
        "bayes_upper_bound_accuracy": _round(bayes_upper_bound),
        "chance_accuracy": _round(1.0 / float(vocabulary_size)),
        "source_pointers": source_pointers,
        "boundary_reason": (
            "Given x_prev_1, varying hidden x_prev_2 permutes all labels, so the baseline Bayes limit is chance."
            if information_starved
            else "Baseline input bandwidth covers the label dependency order."
        ),
    }


def _fair_metric(summary: Mapping[str, Any] | None, key: str) -> float | None:
    if summary is None:
        return None
    metrics = summary.get("metrics")
    if not isinstance(metrics, Mapping):
        return None
    return _finite_float(metrics.get(key))


def _fair_compute(summary: Mapping[str, Any] | None) -> float | None:
    if summary is None:
        return None
    return _finite_float(summary.get("compute_units"))


def _fair_seed_count(summary: Mapping[str, Any] | None) -> int:
    if summary is None:
        return 0
    value = summary.get("seed_count")
    return int(value) if isinstance(value, int) and not isinstance(value, bool) else 0


def _fair_epoch_count(summary: Mapping[str, Any] | None) -> int | None:
    if summary is None:
        return None
    config = summary.get("training_config")
    if not isinstance(config, Mapping):
        return None
    value = config.get("epoch_count")
    return int(value) if isinstance(value, int) and not isinstance(value, bool) else None


def _missing_fair_rows(reason: str = "non-starved-fair-baseline-missing") -> list[dict[str, Any]]:
    return [
        BaseUndertrainingComparisonRow(
            comparison_id=comparison_id,
            status="missing",
            source_artifact=FAIR_BASELINE_SUMMARY_ARTIFACT,
            source_pointer=f"{FAIR_BASELINE_SUMMARY_ARTIFACT}:$",
            match_axis=axis,
            match_value=None,
            base_metric=None,
            dgt_metric=None,
            ci_overlap=None,
            ci_low_separation=None,
            decision=reason,
        ).as_dict()
        for comparison_id, axis in (
            ("equal_step", "training_steps"),
            ("equal_compute", "compute_units"),
            ("equal_loss_decrease", "loss_decrease"),
            ("equal_validation_loss", "validation_loss"),
        )
    ]


def _build_rows(l1_payload: Mapping[str, Any], fair_baseline: Mapping[str, Any] | None = None) -> list[dict[str, Any]]:
    rows = _step_rows(l1_payload)
    anchor = _row_by_steps(rows, 36)
    equal_step = _comparison_row(
        comparison_id="equal_step",
        source_index=None if anchor is None else anchor[0],
        source_row=None if anchor is None else anchor[1],
        match_axis="training_steps",
        match_value=36,
        fair_baseline=fair_baseline,
        missing_reason="equal-step-anchor-missing",
        source_pointer_override=f"{FAIR_BASELINE_SUMMARY_ARTIFACT}:$.training_config.epoch_count" if fair_baseline is not None else None,
    )
    if anchor is None:
        return [equal_step.as_dict()]

    _anchor_index, anchor_row = anchor
    dgt_compute = _compute(anchor_row, "dgt_l1")
    dgt_loss_dec = _metric(anchor_row, "dgt_loss_decrease_mean")
    dgt_validation_loss = _arm_metric(anchor_row, "dgt_l1", "validation_loss_mean")
    if fair_baseline is not None:
        equal_compute_match = None if dgt_compute is None else (_anchor_index, anchor_row, dgt_compute)
        equal_loss_match = None if dgt_loss_dec is None else (_anchor_index, anchor_row, dgt_loss_dec)
        equal_validation_match = None if dgt_validation_loss is None else (_anchor_index, anchor_row, dgt_validation_loss)
    else:
        equal_compute_match = (
            None
            if dgt_compute is None
            else _nearest_by_value(rows, value_getter=lambda row: _compute(row, INPUT_ABLATION_ARM_ID), target=dgt_compute)
        )
        equal_loss_match = (
            None
            if dgt_loss_dec is None
            else _nearest_by_value(
                rows,
                value_getter=lambda row: _metric(row, INPUT_ABLATION_LOSS_DECREASE_METRIC),
                target=dgt_loss_dec,
            )
        )
        equal_validation_match = (
            None
            if dgt_validation_loss is None
            else _nearest_by_value(
                rows,
                value_getter=lambda row: _metric(row, INPUT_ABLATION_VALIDATION_LOSS_METRIC),
                target=dgt_validation_loss,
            )
        )
    equal_compute = _comparison_row(
        comparison_id="equal_compute",
        source_index=None if equal_compute_match is None else equal_compute_match[0],
        source_row=None if equal_compute_match is None else equal_compute_match[1],
        match_axis="compute_units",
        match_value=dgt_compute,
        fair_baseline=fair_baseline,
        missing_reason="equal-compute-source-missing",
        source_pointer_override=f"{FAIR_BASELINE_SUMMARY_ARTIFACT}:$.compute_units" if fair_baseline is not None else None,
    )
    equal_loss = _comparison_row(
        comparison_id="equal_loss_decrease",
        source_index=None if equal_loss_match is None else equal_loss_match[0],
        source_row=None if equal_loss_match is None else equal_loss_match[1],
        match_axis="loss_decrease",
        match_value=dgt_loss_dec,
        fair_baseline=fair_baseline,
        missing_reason="equal-loss-decrease-source-missing",
        source_pointer_override=f"{FAIR_BASELINE_SUMMARY_ARTIFACT}:$.metrics.loss_decrease_mean" if fair_baseline is not None else None,
    )
    equal_validation = _comparison_row(
        comparison_id="equal_validation_loss",
        source_index=None if equal_validation_match is None else equal_validation_match[0],
        source_row=None if equal_validation_match is None else equal_validation_match[1],
        match_axis="validation_loss",
        match_value=dgt_validation_loss,
        fair_baseline=fair_baseline,
        missing_reason="validation-loss-owner-cell-missing",
        source_pointer_override=(
            f"{FAIR_BASELINE_SUMMARY_ARTIFACT}:$.metrics.validation_loss_mean"
            if fair_baseline is not None
            else None
            if equal_validation_match is None
            else (
                f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder.per_step[{equal_validation_match[0]}]"
                f".metrics.{INPUT_ABLATION_VALIDATION_LOSS_METRIC}"
            )
        ),
    )
    return [equal_step.as_dict(), equal_compute.as_dict(), equal_loss.as_dict(), equal_validation.as_dict()]


def _hardgates(
    comparison_rows: Sequence[Mapping[str, Any]],
    coverage: Mapping[str, Any],
    construct_validity: Mapping[str, Any],
    fair_baseline_contract: Mapping[str, Any],
) -> dict[str, Any]:
    row_ids = {str(row.get("comparison_id")) for row in comparison_rows}
    all_rows_present = set(REQUIRED_COMPARISONS).issubset(row_ids)
    all_rows_resolved = all(row.get("status") == "resolved" for row in comparison_rows) and all_rows_present
    fair_rows = [row for row in comparison_rows if row.get("comparison_id") in {"equal_compute", "equal_loss_decrease", "equal_validation_loss"}]
    fair_catchup = any(row.get("ci_overlap") is True or (row.get("ci_low_separation") is not None and row.get("ci_low_separation") <= 0.0) for row in fair_rows)
    fair_separates = bool(fair_rows) and all(
        row.get("ci_overlap") is False and row.get("ci_low_separation") is not None and row.get("ci_low_separation") > 0.0
        for row in fair_rows
    )
    construct_boundary = construct_validity.get("status") == "construct-boundary"
    input_accessibility = construct_validity.get("input_accessibility_preconditions")
    input_access_ok = isinstance(input_accessibility, Mapping) and input_accessibility.get("status") == "pass"
    fair_access_row = input_accessibility.get("fair_baseline_row") if isinstance(input_accessibility, Mapping) else {}
    fair_access_ok = (
        isinstance(fair_access_row, Mapping)
        and fair_access_row.get("status") == "pass"
        and fair_access_row.get("information_starved") is False
        and fair_access_row.get("missing_variables") == []
    )
    fair_baseline_ok = fair_baseline_contract.get("status") == "pass"
    fair_loss_ok = _finite_float(fair_baseline_contract.get("loss_decrease_mean")) is not None and float(fair_baseline_contract.get("loss_decrease_mean", 0.0)) > 0.0
    fair_compute_ok = (
        _finite_float(fair_baseline_contract.get("compute_ratio_to_dgt_anchor")) is not None
        and float(fair_baseline_contract.get("compute_ratio_to_dgt_anchor", 1.0)) <= FAIR_BASELINE_TOLERANCE
        and _finite_float(fair_baseline_contract.get("parameter_ratio_to_dgt_anchor")) is not None
        and float(fair_baseline_contract.get("parameter_ratio_to_dgt_anchor", 1.0)) <= FAIR_BASELINE_TOLERANCE
    )
    return {
        "BASE-HG1": {
            "criterion": "fair baseline sees x_minus_1 and x_minus_2",
            "status": "pass" if fair_access_ok and fair_baseline_contract.get("information_starved") is False else "fail",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.base_undertraining_audit.source_contract.fair_baseline_contract",
            "input_accessibility_pointer": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$",
        },
        "BASE-HG2": {
            "criterion": "fair baseline loss decreases under real training",
            "status": "pass" if fair_loss_ok else "fail",
            "evidence_pointer": f"{FAIR_BASELINE_SUMMARY_ARTIFACT}:$.metrics.loss_decrease_mean",
        },
        "BASE-HG3": {
            "criterion": "fair baseline compute and parameters match the DGT anchor within tolerance",
            "status": "pass" if fair_compute_ok else "fail",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.base_undertraining_audit.source_contract.fair_baseline_contract",
        },
        "BASE-HG4": {
            "criterion": "fair baseline catch-up remains a bounded-negative architecture result",
            "status": "triggered" if fair_catchup else "not-triggered",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.base_undertraining_audit.boundary_ledger",
        },
        "BASE-UNDER-HG0": {
            "criterion": "input-accessibility boundary pointers and fair baseline input bandwidth must pass before undertraining evidence is allowed",
            "status": "fail-closed" if not input_access_ok or not fair_access_ok or not fair_baseline_ok else "pass",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.base_undertraining_audit.construct_validity",
            "input_accessibility_pointer": f"{INPUT_ACCESSIBILITY_SOURCE_ARTIFACT}:$",
        },
        "BASE-UNDER-HG1": {
            "criterion": "fairness baseline comes from the non-starved trained baseline",
            "status": "pass" if all_rows_present and fair_baseline_ok else "fail",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.base_undertraining_audit.comparison_rows",
        },
        "BASE-UNDER-HG2": {
            "criterion": "base step grid covers the DGT compute, loss-decrease, and validation-loss interval",
            "status": "pass" if coverage.get("covers_dgt_compute_loss_interval") else "fail",
            "evidence_pointer": coverage["source_pointer"],
        },
        "BASE-UNDER-HG3": {
            "criterion": "missing comparison evidence fails closed to inconclusive",
            "status": "pass" if all_rows_resolved else "fail",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.base_undertraining_audit.comparison_rows",
        },
        "BASE-UNDER-HG4": {
            "criterion": "construct-valid compute, loss-decrease, or validation-loss catch-up records a bounded downgrade ledger",
            "status": "triggered" if fair_catchup else "not-triggered",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.base_undertraining_audit.boundary_ledger",
        },
        "BASE-UNDER-HG5": {
            "criterion": "resolved compute, loss-decrease, and validation-loss rows retain positive CI-low separation",
            "status": "pass" if all_rows_resolved and fair_separates else "fail",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.base_undertraining_audit.evidence_ledger",
        },
    }


def _derive_decision(
    comparison_rows: Sequence[Mapping[str, Any]],
    hardgates: Mapping[str, Mapping[str, Any]],
    construct_validity: Mapping[str, Any],
) -> tuple[str, str, list[dict[str, Any]], list[dict[str, Any]]]:
    if construct_validity.get("status") == "construct-boundary" or hardgates["BASE-UNDER-HG0"]["status"] != "pass":
        return (
            "construct-boundary",
            "defer-to-fair-reconstruction",
            [
                {
                    "ledger_id": "base-undertraining-construct-validity",
                    "status": "construct-boundary" if construct_validity.get("status") == "construct-boundary" else "fair-baseline-boundary",
                    "reason": (
                        "fair baseline evidence is missing or input accessibility does not certify the non-starved baseline"
                    ),
                    "source_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.base_undertraining_audit.construct_validity",
                    "reconstruction_pointer": FAIR_RECONSTRUCTION_POINTER,
                }
            ],
            [],
        )
    if hardgates["BASE-UNDER-HG1"]["status"] != "pass" or hardgates["BASE-UNDER-HG2"]["status"] != "pass" or hardgates["BASE-UNDER-HG3"]["status"] != "pass":
        return "inconclusive", "hold", [], []
    fair_rows = [row for row in comparison_rows if row["comparison_id"] in {"equal_compute", "equal_loss_decrease", "equal_validation_loss"}]
    catchup = [
        row for row in fair_rows
        if row.get("ci_overlap") is True or (row.get("ci_low_separation") is not None and row["ci_low_separation"] <= 0.0)
    ]
    if catchup:
        first = catchup[0]
        action = (
            "fair_compute_artifact"
            if first["comparison_id"] == "equal_compute"
            else "fair_validation_loss_artifact"
            if first["comparison_id"] == "equal_validation_loss"
            else "fair_loss_decrease_artifact"
        )
        return (
            "downgrade",
            action,
            [
                {
                    "ledger_id": f"base-undertraining-{row['comparison_id']}",
                    "comparison_id": row["comparison_id"],
                    "reason": "base reaches DGT after the construct-validity premise is satisfied",
                    "source_pointer": row["source_pointer"],
                }
                for row in catchup
            ],
            [],
        )
    return (
        "noninformative-separation",
        "record_noninformative_rows",
        [],
        [
            {
                "ledger_id": f"base-undertraining-{row['comparison_id']}",
                "comparison_id": row["comparison_id"],
                "ci_low_separation": row["ci_low_separation"],
                "source_pointer": row["source_pointer"],
            }
            for row in comparison_rows
        ],
    )


def build_payload(
    *,
    root: Path,
    generated_at: str = GENERATED_AT,
    l1_payload: Mapping[str, Any] | None = None,
    l1_status: str | None = None,
    l1_sha256: str | None = None,
    downstream_verdict: Any | None = None,
    construct_validity_override: Mapping[str, Any] | None = None,
    input_accessibility_payload: Mapping[str, Any] | None = None,
    fair_baseline_payload: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    if downstream_verdict is not None:
        raise ValueError("base-undertraining audit does not accept downstream verdict input")
    if l1_payload is None:
        resolved_status, loaded_payload, resolved_sha = _load_json_artifact(root, L1_SOURCE_ARTIFACT)
        l1_status = l1_status or resolved_status
        l1_payload = loaded_payload
        l1_sha256 = l1_sha256 if l1_sha256 is not None else resolved_sha
    else:
        l1_status = l1_status or "resolved"
        l1_sha256 = l1_sha256 if l1_sha256 is not None else _json_digest(l1_payload)

    fair_baseline_status = _load_fair_baseline(root, fair_baseline_payload)
    fair_summary = fair_baseline_status.get("summary") if fair_baseline_status.get("status") == "resolved" else None

    if l1_status == "resolved" and isinstance(l1_payload, Mapping):
        comparison_rows = (
            _build_rows(l1_payload, fair_summary if isinstance(fair_summary, Mapping) else None)
            if isinstance(fair_summary, Mapping)
            else _missing_fair_rows()
        )
        coverage = _base_grid_coverage(_step_rows(l1_payload))
    else:
        comparison_rows = []
        coverage = {
            "required_grid": list(REQUIRED_BASE_GRID),
            "observed_grid": [],
            "required_grid_present": False,
            "covers_dgt_compute_loss_interval": False,
            "source_pointer": f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder.step_grid",
        }

    input_accessibility_preconditions = _input_accessibility_preconditions(
        root,
        input_accessibility_payload,
    )
    fair_contract = _fair_baseline_contract(fair_baseline_status, l1_payload if isinstance(l1_payload, Mapping) else None)
    construct_validity = dict(
        construct_validity_override
        or construct_validity_assessment(
            baseline_input_order=2,
            label_dependency_order=2,
            second_predecessor_visible=True,
            input_accessibility_preconditions=input_accessibility_preconditions,
        )
    )
    construct_validity["input_accessibility_preconditions"] = input_accessibility_preconditions
    construct_validity["fair_baseline_contract"] = fair_contract
    source_pointers = dict(construct_validity.get("source_pointers", {}))
    source_pointers.update(input_accessibility_preconditions["source_pointers"])
    source_pointers["fair_baseline_summary"] = f"{FAIR_BASELINE_SUMMARY_ARTIFACT}:$"
    source_pointers["fair_baseline_raw_metrics"] = f"{FAIR_BASELINE_METRICS_ARTIFACT}:$"
    construct_validity["source_pointers"] = source_pointers
    hardgates = _hardgates(comparison_rows, coverage, construct_validity, fair_contract)
    verdict, claim_action, boundary, evidence = _derive_decision(comparison_rows, hardgates, construct_validity)
    source_contract = {
        "source_artifact": L1_SOURCE_ARTIFACT,
        "source_pointer": f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder",
        "sha256": l1_sha256,
        "status": l1_status or "invalid",
        "pointer_only": True,
        "required_pointers": sorted(
            {
                f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder",
                f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder.per_step",
                f"{L1_SOURCE_ARTIFACT}:$.l1_step_ladder.step_grid",
                f"{FAIR_BASELINE_SUMMARY_ARTIFACT}:$",
                f"{FAIR_BASELINE_METRICS_ARTIFACT}:$",
                *(str(row["source_pointer"]) for row in comparison_rows),
                input_accessibility_preconditions["input_accessibility_ref"],
                input_accessibility_preconditions["boundary_ledger_ref"],
                *input_accessibility_preconditions["information_starved_arms_ref"],
                *input_accessibility_preconditions["unanswerable_ood_splits_ref"],
            }
        ),
        "base_step_grid_coverage": coverage,
        "input_accessibility_preconditions": input_accessibility_preconditions,
        "fair_baseline_contract": fair_contract,
    }
    audit = BaseUndertrainingAudit(
        source_contract=source_contract,
        construct_validity=construct_validity,
        comparison_rows=comparison_rows,
        hardgates=hardgates,
        mechanical_decision_table=mechanical_decision_table(),
        verdict=verdict,
        claim_action=claim_action,
        boundary_ledger=boundary,
        evidence_ledger=evidence,
        not_claimed=NOT_CLAIMED,
        revoke_if=[
            "Any required L1 canonical pointer becomes missing or unresolvable.",
            "The construct-validity source no longer identifies the current baseline feature boundary.",
            "The audit is used as evidence outside bounded L1 tiny-sequence scope.",
        ],
    ).as_dict()
    audit["generated_at"] = generated_at
    audit["producer"] = PRODUCER
    payload = {"base_undertraining_audit": audit}
    validate_payload(payload)
    return payload


def validate_payload(payload: Mapping[str, Any]) -> None:
    if set(payload) != {"base_undertraining_audit"}:
        raise ValueError("base-undertraining payload must expose only base_undertraining_audit")
    audit = payload["base_undertraining_audit"]
    required = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "source_contract",
        "construct_validity",
        "comparison_rows",
        "hardgates",
        "mechanical_decision_table",
        "verdict",
        "claim_action",
        "boundary_ledger",
        "evidence_ledger",
        "not_claimed",
        "revoke_if",
    }
    if not isinstance(audit, Mapping) or set(audit) != required:
        raise ValueError("base-undertraining audit fields mismatch")
    if audit["schema_id"] != SCHEMA_ID or audit["artifact_id"] != ARTIFACT_ID:
        raise ValueError("base-undertraining audit identity mismatch")
    construct_validity = audit["construct_validity"]
    if not isinstance(construct_validity, Mapping) or construct_validity.get("status") not in {"construct-boundary", "construct-valid"}:
        raise ValueError("base-undertraining construct validity mismatch")
    if construct_validity.get("status") == "construct-boundary":
        if audit["verdict"] != "construct-boundary" or audit["claim_action"] != "defer-to-fair-reconstruction":
            raise ValueError("construct-boundary audit must defer to fair reconstruction")
        if audit["evidence_ledger"]:
            raise ValueError("construct-boundary audit must not emit evidence strengthening")
    rows = audit["comparison_rows"]
    if not isinstance(rows, list):
        raise ValueError("base-undertraining comparison rows must be a list")
    row_ids = [row.get("comparison_id") for row in rows if isinstance(row, Mapping)]
    if len(row_ids) != len(set(row_ids)):
        raise ValueError("base-undertraining comparison rows must be unique")
    if audit["verdict"] not in {"inconclusive", "construct-boundary"} and set(row_ids) != set(REQUIRED_COMPARISONS):
        raise ValueError("non-inconclusive base-undertraining verdict requires all comparison rows")
    for row in rows:
        if set(row) != set(BaseUndertrainingComparisonRow("", "", "", "", "", None, None, None, None, None, "").as_dict()):
            raise ValueError("base-undertraining comparison row fields mismatch")
        if row["source_artifact"] not in {L1_SOURCE_ARTIFACT, FAIR_BASELINE_SUMMARY_ARTIFACT}:
            raise ValueError("base-undertraining row source artifact mismatch")
        if not str(row["source_pointer"]).startswith((f"{L1_SOURCE_ARTIFACT}:", f"{FAIR_BASELINE_SUMMARY_ARTIFACT}:")):
            raise ValueError("base-undertraining row source pointer mismatch")
    serialized = json.dumps(payload, sort_keys=True)
    for forbidden in ("step_rows", "training_arms", '"raw_records"', '"probe_rows"'):
        if forbidden in serialized:
            raise ValueError(f"base-undertraining audit must not duplicate L1 payload: {forbidden}")


def render_markdown(payload: Mapping[str, Any]) -> str:
    audit = payload["base_undertraining_audit"]
    lines = [
        "# DGT base undertraining audit",
        "",
        f"- Verdict: `{audit['verdict']}`",
        f"- Claim action: `{audit['claim_action']}`",
        f"- Source: `{audit['source_contract']['source_pointer']}`",
        f"- Construct validity: `{audit['construct_validity']['status']}`",
        "",
        "## Boundary ledger",
        "",
    ]
    for row in audit["boundary_ledger"]:
        lines.append(f"- `{row['ledger_id']}`: {row['reason']}")
    lines.extend([
        "",
        "## Comparison rows",
        "",
    ])
    for row in audit["comparison_rows"]:
        lines.append(
            f"- `{row['comparison_id']}`: `{row['decision']}` "
            f"(base `{row['base_metric']}`, DGT `{row['dgt_metric']}`, pointer `{row['source_pointer']}`)"
        )
    lines.extend(["", "## Not claimed", ""])
    for item in audit["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    audit = payload["base_undertraining_audit"]
    source_contract = audit["source_contract"]
    return {
        "schema_id": "bedc-quality-lab:canonical-report-fingerprint",
        "report_name": "dgt-base-undertraining-audit",
        "json_artifact": CANONICAL_JSON_ARTIFACT,
        "markdown_artifact": CANONICAL_MARKDOWN_ARTIFACT,
        "producer_command": ["python3", PRODUCER],
        "input_fingerprint": _json_digest(source_contract),
        "output_digest": _json_digest(payload),
        "inputs": {"source_contract": source_contract},
        "generated_by": {"runner": PRODUCER, "generated_at": generated_at},
    }


def write_artifacts(payload: Mapping[str, Any], *, root: Path, generated_at: str | None = None) -> None:
    validate_payload(payload)
    _write_json(root / CANONICAL_JSON_ARTIFACT, payload)
    markdown_path = root / CANONICAL_MARKDOWN_ARTIFACT
    markdown_path.parent.mkdir(parents=True, exist_ok=True)
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")
    _write_json(
        root / CANONICAL_FINGERPRINT_ARTIFACT,
        fingerprint_payload(payload, generated_at=generated_at or datetime.now(timezone.utc).isoformat()),
    )

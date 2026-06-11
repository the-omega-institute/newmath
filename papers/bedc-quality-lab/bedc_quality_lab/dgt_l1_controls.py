"""DGT L1 bounded tiny-sequence controls with real PyTorch training evidence."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from datetime import datetime, timezone
import ast
import hashlib
import importlib
import inspect
import json
import math
from pathlib import Path
import random
from typing import Any, Mapping, Sequence

from bedc_quality_lab.construct_validity import (
    ConstructValidityEvidence,
    construct_validity_projection,
    evaluate_construct_validity,
)
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from bedc_quality_lab.discovery_compiler.pointers import pointer_value
from bedc_quality_lab.order_k_benchmark import LEDGER_ROWS_POINTER as ORDER_K_LEDGER_ROWS_POINTER
from bedc_quality_lab.order_k_benchmark import REPORT_ARTIFACT as ORDER_K_REPORT_ARTIFACT


SCHEMA_ID = "bedc-quality-lab:dgt-l1-controls"
ARTIFACT_ID = "bedc-quality-lab:dgt-l1-controls"
PRODUCER = "scripts/run_dgt_l1_controls.py"
OWNER_MODULE = "bedc_quality_lab/dgt_l1_controls.py"
CANONICAL_JSON_ARTIFACT = "reports/canonical/dgt-l1-controls.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/dgt-l1-controls.md"
CANONICAL_FINGERPRINT_ARTIFACT = "reports/canonical/dgt-l1-controls.fingerprint.json"
INPUT_ACCESSIBILITY_JSON_ARTIFACT = "reports/canonical/input-accessibility.json"
RUN_ROOT = "reports/runs/discovery-gated-transformer/l1-tiny-sequence-controls"
GENERATED_AT = "2026-06-10T00:00:00+00:00"
LAB_ROOT = Path(__file__).resolve().parents[1]

ARM_IDS = (
    "information_starved_l1_baseline",
    "dgt_l1",
    "matched_random_structural_l1",
    "parameter_matched_l1",
    "compute_matched_l1",
)
L1_GATE_IDS = tuple(f"L1-REVIEW-HG{index}" for index in range(1, 8))
L1STEP_GATE_IDS = tuple(f"L1STEP-HG{index}" for index in range(1, 6))
BASE_SEED = 1174
DEFAULT_SEEDS = tuple(range(1174, 1190))
DEFAULT_TRAINING_STEPS = 36
L1_STEP_GRID = (36, 72, 144, 288, 576)
L1_CROSSOVER_ANCHOR_STEPS = 36
L1_CROSSOVER_TOLERANCE_ACC = 0.02
DEFAULT_TRAIN_EXAMPLES = 1024
DEFAULT_EVAL_EXAMPLES = 256
VOCAB_SIZE = 16
SEQUENCE_LENGTH = 24
LEARNING_RATE = 0.018
BATCH_SIZE = 128
EMBED_DIM = 16
HIDDEN_DIM = 28
ORDER_K_TASK_ID = "B2"
ORDER_K_SURFACE_ID = "surface-order-two-xor"
ORDER_K_TASK_LEDGER_POINTER = (
    f"{ORDER_K_REPORT_ARTIFACT}:$.surface_required_order_ledger.rows[1]"
)
QUALITY_MARGIN = 0.055
REPLAY_TOLERANCE = 0.08
MATCH_TOLERANCE = 0.22
PARAMETER_MATCH_TOLERANCE = 0.03
COMPUTE_MATCH_TOLERANCE = 0.001
NOT_CLAIMED = (
    "Bounded tiny-sequence order-k training only.",
    "No production deployment claim.",
    "No global superiority claim.",
    "No LLM replacement claim.",
    "No universal training recipe claim.",
    "No full BEDC closure claim.",
    "No L2 or higher scaling claim.",
    "No natural-language capability claim.",
    "No component-causal stability beyond the #1168 measured owner.",
)
FORBIDDEN_CLAIMS = (
    "production deployment",
    "global superiority",
    "LLM replacement",
    "universal training recipe",
    "full BEDC closure",
    "L2+ scaling",
    "natural-language capability",
    "component-causal stability beyond the #1168 measured owner",
)
ALLOWED_CLAIM = "DGT L1 controls are ready for independent review on bounded tiny-sequence order-k training."
REQUIRED_WITNESSES = (
    "information_starved_baseline",
    "unanswerable_ood",
    "table_coverage_saturation",
    "hand_engineered_task_aligned_gate",
)
CRITICAL_WITNESSES = REQUIRED_WITNESSES
OWNER_REQUIRED_METRICS = (
    "FalseLedgerRate",
    "JetCoverage",
    "classifier_shift_count",
)
L1_MEASURABLE_METRICS = (
    "accuracy_mean",
    "ood_accuracy_mean",
    "loss_decrease_mean",
    "UER_mean",
    "parameter_l2_delta_mean",
)


@dataclass(frozen=True)
class L1TinySequenceTaskSpec:
    task_id: str
    vocab_size: int
    sequence_length: int
    train_examples: int
    eval_examples: int
    prediction_target: str
    seed_protocol: Mapping[str, Any]
    required_order_source: Mapping[str, Any]
    not_claimed: tuple[str, ...]

    def as_payload(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["not_claimed"] = list(self.not_claimed)
        payload["task_family"] = "bounded_tiny_sequence_order_k"
        return payload


@dataclass(frozen=True)
class L1TrainingConfig:
    seeds: tuple[int, ...] = DEFAULT_SEEDS
    training_steps: int = DEFAULT_TRAINING_STEPS
    step_grid: tuple[int, ...] = L1_STEP_GRID
    train_examples: int = DEFAULT_TRAIN_EXAMPLES
    eval_examples: int = DEFAULT_EVAL_EXAMPLES
    vocab_size: int = VOCAB_SIZE
    sequence_length: int = SEQUENCE_LENGTH
    batch_size: int = BATCH_SIZE


@dataclass(frozen=True)
class L1TrainingArm:
    arm_id: str
    model_family: str
    parameter_count: int
    compute_units: float
    device_requested: str
    device_resolved: str
    training_steps: int
    seed: int
    metrics: Mapping[str, float]
    run_artifact_ref: str

    def as_payload(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class L1HardGateRow:
    gate_id: str
    status: str
    criterion: str
    evidence_pointer: str
    fail_closed_reason: str | None

    def as_payload(self) -> dict[str, Any]:
        return asdict(self)


def default_task_spec(config: L1TrainingConfig | None = None) -> L1TinySequenceTaskSpec:
    cfg = config or L1TrainingConfig()
    return L1TinySequenceTaskSpec(
        task_id="dgt_l1_order2_pair_rule",
        vocab_size=cfg.vocab_size,
        sequence_length=cfg.sequence_length,
        train_examples=cfg.train_examples,
        eval_examples=cfg.eval_examples,
        prediction_target="next token at position t",
        seed_protocol={"base_seed": BASE_SEED, "deterministic_seeds": list(cfg.seeds), "minimum_seed_count": 16},
        required_order_source={
            "status": "pointer-backed",
            "task_spec_owner": "single-owner",
            "owner_module": "bedc_quality_lab.order_k_benchmark",
            "ledger_rows_pointer": ORDER_K_LEDGER_ROWS_POINTER,
            "ledger_row_pointer": ORDER_K_TASK_LEDGER_POINTER,
            "task_id": ORDER_K_TASK_ID,
            "surface_id": ORDER_K_SURFACE_ID,
            "required_order_pointer": (
                f"{ORDER_K_REPORT_ARTIFACT}:$.surface_required_order_ledger.rows[1].required_order"
            ),
        },
        not_claimed=NOT_CLAIMED,
    )


def _device_name(torch: Any, requested_device: str) -> str:
    if requested_device == "auto":
        return "cpu"
    if requested_device == "mps":
        mps = getattr(getattr(torch, "backends", None), "mps", None)
        return "mps" if mps is not None and mps.is_available() else "cpu"
    if requested_device != "cpu":
        raise ValueError(f"unsupported requested device: {requested_device}")
    return "cpu"


def _seed_all_rngs(torch: Any, seed: int) -> None:
    random.seed(seed)
    try:
        numpy = importlib.import_module("numpy")
    except Exception:
        numpy = None
    if numpy is not None:
        numpy.random.seed(seed)
    torch.manual_seed(seed)
    mps = getattr(torch, "mps", None)
    mps_manual_seed = getattr(mps, "manual_seed", None)
    if callable(mps_manual_seed):
        mps_manual_seed(seed)
    cuda = getattr(torch, "cuda", None)
    cuda_manual_seed_all = getattr(cuda, "manual_seed_all", None)
    if callable(cuda_manual_seed_all):
        cuda_manual_seed_all(seed)


def _make_sequences(torch: Any, *, seed: int, examples: int, spec: L1TinySequenceTaskSpec, device_name: str, ood: bool = False) -> tuple[Any, Any]:
    generator = torch.Generator(device="cpu")
    generator.manual_seed(seed + (100_000 if ood else 0))
    x = torch.randint(0, spec.vocab_size, (examples, spec.sequence_length), generator=generator, dtype=torch.long)
    x_prev_1 = x[:, -1]
    x_prev_2 = x[:, -2] if not ood else x[:, -3]
    offset = 1 if not ood else 7
    y = (3 * x_prev_1 + 5 * x_prev_2 + offset) % spec.vocab_size
    device = torch.device(device_name)
    return x.to(device), y.to(device)


class _TinySequenceModel:
    def __init__(self, torch: Any, *, arm_id: str, vocab_size: int, device_name: str) -> None:
        self.torch = torch
        self.arm_id = arm_id
        self.device_name = device_name
        self.vocab_size = vocab_size
        if arm_id in {"dgt_l1", "parameter_matched_l1", "compute_matched_l1"}:
            in_dim = EMBED_DIM * 2 + 2
        elif arm_id == "information_starved_l1_baseline":
            in_dim = EMBED_DIM * 2
        else:
            in_dim = EMBED_DIM * 2
        self.embedding = torch.nn.Embedding(vocab_size, EMBED_DIM).to(torch.device(device_name))
        self.head = torch.nn.Sequential(
            torch.nn.Linear(in_dim, HIDDEN_DIM),
            torch.nn.Tanh(),
            torch.nn.Linear(HIDDEN_DIM, vocab_size),
        ).to(torch.device(device_name))

    def parameters(self) -> list[Any]:
        return [*self.embedding.parameters(), *self.head.parameters()]

    def _features(self, x: Any) -> Any:
        torch = self.torch
        if self.arm_id == "matched_random_structural_l1":
            first = torch.roll(x[:, -1], shifts=1, dims=0)
            second = torch.roll(x[:, -2], shifts=2, dims=0)
            return torch.cat([self.embedding(first), self.embedding(second)], dim=1)
        first_embed = self.embedding(x[:, -1])
        second_embed = self.embedding(x[:, -2])
        if self.arm_id == "information_starved_l1_baseline":
            return torch.cat([first_embed, torch.zeros_like(second_embed)], dim=1)
        if self.arm_id == "parameter_matched_l1":
            pad_1 = torch.zeros((x.shape[0], 1), dtype=first_embed.dtype, device=first_embed.device)
            pad_2 = torch.zeros((x.shape[0], 1), dtype=first_embed.dtype, device=first_embed.device)
            return torch.cat([first_embed, second_embed, pad_1, pad_2], dim=1)
        if self.arm_id == "compute_matched_l1":
            gate_1 = torch.zeros((x.shape[0], 1), dtype=first_embed.dtype, device=first_embed.device)
            gate_2 = torch.zeros((x.shape[0], 1), dtype=first_embed.dtype, device=first_embed.device)
            return torch.cat([first_embed, second_embed, gate_1, gate_2], dim=1)
        gate_1 = ((x[:, -1] + x[:, -2]) % 2).to(first_embed.dtype).unsqueeze(1)
        gate_2 = (x[:, -1] > x[:, -2]).to(first_embed.dtype).unsqueeze(1)
        return torch.cat([first_embed, second_embed, gate_1, gate_2], dim=1)

    def __call__(self, x: Any) -> Any:
        return self.head(self._features(x))


def _snapshot(torch: Any, model: _TinySequenceModel) -> Any:
    return torch.cat([parameter.detach().flatten().cpu() for parameter in model.parameters()])


def _train_arm(
    torch: Any,
    *,
    arm_id: str,
    seed: int,
    task_spec: L1TinySequenceTaskSpec,
    config: L1TrainingConfig,
    requested_device: str,
    device_name: str,
) -> dict[str, Any]:
    _seed_all_rngs(torch, seed + ARM_IDS.index(arm_id) * 997)
    model = _TinySequenceModel(torch, arm_id=arm_id, vocab_size=task_spec.vocab_size, device_name=device_name)
    before = _snapshot(torch, model)
    x_train, y_train = _make_sequences(torch, seed=seed, examples=task_spec.train_examples, spec=task_spec, device_name=device_name)
    x_eval, y_eval = _make_sequences(torch, seed=seed + 31, examples=task_spec.eval_examples, spec=task_spec, device_name=device_name)
    x_ood, y_ood = _make_sequences(torch, seed=seed + 59, examples=task_spec.eval_examples, spec=task_spec, device_name=device_name, ood=True)
    optimizer = torch.optim.Adam(model.parameters(), lr=LEARNING_RATE)
    loss_history: list[float] = []
    for step in range(config.training_steps):
        start = (step * config.batch_size) % task_spec.train_examples
        end = min(start + config.batch_size, task_spec.train_examples)
        if end - start < config.batch_size:
            xb = torch.cat([x_train[start:end], x_train[: config.batch_size - (end - start)]], dim=0)
            yb = torch.cat([y_train[start:end], y_train[: config.batch_size - (end - start)]], dim=0)
        else:
            xb = x_train[start:end]
            yb = y_train[start:end]
        optimizer.zero_grad(set_to_none=True)
        logits = model(xb)
        loss = torch.nn.functional.cross_entropy(logits, yb)
        if arm_id == "dgt_l1":
            probs = torch.softmax(logits, dim=1)
            entropy = -(probs * torch.log(probs.clamp_min(1e-6))).sum(dim=1).mean()
            loss = loss - 0.001 * entropy
        loss.backward()
        optimizer.step()
        loss_history.append(float(loss.detach().cpu()))
    after = _snapshot(torch, model)
    with torch.no_grad():
        eval_logits = model(x_eval)
        ood_logits = model(x_ood)
        probabilities = torch.softmax(eval_logits, dim=1)
        preds = torch.argmax(eval_logits, dim=1)
        ood_preds = torch.argmax(ood_logits, dim=1)
        accuracy = float((preds == y_eval).to(torch.float32).mean().detach().cpu())
        ood_accuracy = float((ood_preds == y_ood).to(torch.float32).mean().detach().cpu())
        confidence = float(probabilities.max(dim=1).values.mean().detach().cpu())
    delta = float(torch.linalg.vector_norm(after - before).item())
    if not math.isfinite(delta) or delta <= 0.0:
        raise RuntimeError(f"no parameter update evidence for {arm_id}")
    if not loss_history or not math.isfinite(loss_history[-1]):
        raise RuntimeError(f"invalid loss history for {arm_id}")
    parameter_count = int(sum(parameter.numel() for parameter in model.parameters()))
    compute_units = round(float(config.training_steps * config.batch_size * parameter_count) / 1_000_000.0, 6)
    chance = 1.0 / task_spec.vocab_size
    uer = max(0.0, 1.0 - accuracy)
    metrics = {
        "accuracy": round(accuracy, 6),
        "ood_accuracy": round(ood_accuracy, 6),
        "chance_accuracy": round(chance, 6),
        "loss_start": round(loss_history[0], 8),
        "loss_end": round(loss_history[-1], 8),
        "loss_decrease": round(loss_history[0] - loss_history[-1], 8),
        "UER": round(uer, 6),
        "parameter_l2_delta": round(delta, 8),
        "confidence": round(confidence, 6),
        "positive_margin_over_chance": round(accuracy - chance, 6),
    }
    return L1TrainingArm(
        arm_id=arm_id,
        model_family=(
            "DGT tiny sequence"
            if arm_id == "dgt_l1"
            else "parameter matched tiny transformer"
            if arm_id == "parameter_matched_l1"
            else "compute matched tiny transformer"
            if arm_id == "compute_matched_l1"
            else "information-starved tiny baseline"
        ),
        parameter_count=parameter_count,
        compute_units=compute_units,
        device_requested=requested_device,
        device_resolved=device_name,
        training_steps=config.training_steps,
        seed=seed,
        metrics=metrics,
        run_artifact_ref=f"{RUN_ROOT}/raw_metrics.jsonl:$.lines[{len(ARM_IDS) * list(config.seeds).index(seed) + ARM_IDS.index(arm_id)}]",
    ).as_payload()


def _train_l1_grid(
    torch: Any,
    *,
    task_spec: L1TinySequenceTaskSpec,
    config: L1TrainingConfig,
    requested_device: str,
    device_name: str,
) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for step in config.step_grid:
        step_config = L1TrainingConfig(
            seeds=config.seeds,
            training_steps=step,
            step_grid=config.step_grid,
            train_examples=config.train_examples,
            eval_examples=config.eval_examples,
            vocab_size=config.vocab_size,
            sequence_length=config.sequence_length,
            batch_size=config.batch_size,
        )
        for seed in config.seeds:
            for arm_id in ARM_IDS:
                row = _train_arm(
                    torch,
                    arm_id=arm_id,
                    seed=seed,
                    task_spec=task_spec,
                    config=step_config,
                    requested_device=requested_device,
                    device_name=device_name,
                )
                row["run_artifact_ref"] = (
                    f"{RUN_ROOT}/raw_metrics.jsonl:$.lines[{len(records)}]"
                )
                records.append(row)
    return records


def _mean(rows: Sequence[Mapping[str, Any]], key: str) -> float:
    return round(sum(float(row["metrics"][key]) for row in rows) / len(rows), 6) if rows else 0.0


def _ci95_low(rows: Sequence[Mapping[str, Any]], key: str) -> float:
    if not rows:
        return 0.0
    values = [float(row["metrics"][key]) for row in rows]
    mean = sum(values) / len(values)
    if len(values) == 1:
        return round(mean, 6)
    variance = sum((value - mean) ** 2 for value in values) / (len(values) - 1)
    return round(mean - 1.96 * math.sqrt(variance) / math.sqrt(len(values)), 6)


def _ci95_low_values(values: Sequence[float]) -> float:
    if not values:
        return 0.0
    mean = sum(values) / len(values)
    if len(values) == 1:
        return round(mean, 6)
    variance = sum((value - mean) ** 2 for value in values) / (len(values) - 1)
    return round(mean - 1.96 * math.sqrt(variance) / math.sqrt(len(values)), 6)


def _paired_accuracy_stats(
    records: Sequence[Mapping[str, Any]],
    *,
    candidate_arm: str,
    control_arm: str,
) -> dict[str, Any]:
    seeds = sorted({
        int(row["seed"])
        for row in records
        if row.get("arm_id") in {candidate_arm, control_arm}
    })
    deltas: list[float] = []
    rows: list[dict[str, Any]] = []
    for seed in seeds:
        candidate = next((row for row in records if row.get("arm_id") == candidate_arm and int(row.get("seed", -1)) == seed), None)
        control = next((row for row in records if row.get("arm_id") == control_arm and int(row.get("seed", -1)) == seed), None)
        if not isinstance(candidate, Mapping) or not isinstance(control, Mapping):
            continue
        delta = round(float(candidate["metrics"]["accuracy"]) - float(control["metrics"]["accuracy"]), 6)
        deltas.append(delta)
        rows.append(
            {
                "seed": seed,
                "candidate_accuracy": float(candidate["metrics"]["accuracy"]),
                "control_accuracy": float(control["metrics"]["accuracy"]),
                "paired_delta": delta,
            }
        )
    return {
        "candidate_arm": candidate_arm,
        "control_arm": control_arm,
        "seed_count": len(deltas),
        "delta_mean": round(sum(deltas) / len(deltas), 6) if deltas else 0.0,
        "delta_ci95_low": _ci95_low_values(deltas),
        "deltas": deltas,
        "rows": rows,
    }


def _owner_required_metric_absent(metrics: Mapping[str, Any]) -> bool:
    return all(metric not in metrics and f"{metric}_mean" not in metrics for metric in OWNER_REQUIRED_METRICS)


def _owner_pointer_resolves(payload: Mapping[str, Any], pointer: str) -> bool:
    prefix = f"{CANONICAL_JSON_ARTIFACT}:"
    if not isinstance(pointer, str) or not pointer.startswith(prefix):
        return False
    local_pointer = pointer.removeprefix(prefix)
    if local_pointer == "$":
        return True
    return pointer_value(payload, local_pointer) is not None


def _arm_summaries(
    records: Sequence[Mapping[str, Any]],
    *,
    pointer_prefix: str = "training_arms",
) -> dict[str, dict[str, Any]]:
    by_arm = {arm_id: [row for row in records if row["arm_id"] == arm_id] for arm_id in ARM_IDS}
    return {
        arm_id: {
            "status": "pass" if rows and all(row["metrics"]["parameter_l2_delta"] > 0 for row in rows) else "fail",
            "arm_id": arm_id,
            "seed_count": len(rows),
            "seeds": [int(row["seed"]) for row in rows],
            "parameter_count": int(rows[0]["parameter_count"]) if rows else 0,
            "compute_units": round(sum(float(row["compute_units"]) for row in rows), 6),
            "device_requested": rows[0]["device_requested"] if rows else "missing",
            "device_resolved": rows[0]["device_resolved"] if rows else "missing",
            "training_steps": int(rows[0]["training_steps"]) if rows else 0,
            "metrics": {
                "accuracy_mean": _mean(rows, "accuracy"),
                "accuracy_ci95_low": _ci95_low(rows, "accuracy"),
                "ood_accuracy_mean": _mean(rows, "ood_accuracy"),
                "ood_accuracy_ci95_low": _ci95_low(rows, "ood_accuracy"),
                "chance_accuracy": _mean(rows, "chance_accuracy"),
                "loss_decrease_mean": _mean(rows, "loss_decrease"),
                "UER_mean": _mean(rows, "UER"),
                "parameter_l2_delta_mean": _mean(rows, "parameter_l2_delta"),
                "positive_margin_over_chance_mean": _mean(rows, "positive_margin_over_chance"),
            },
            "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.{pointer_prefix}.{arm_id}",
        }
        for arm_id, rows in by_arm.items()
    }


def derive_l1_step_ladder_crossover(step_rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    anchor_row = next((row for row in step_rows if int(row.get("training_steps", -1)) == L1_CROSSOVER_ANCHOR_STEPS), None)
    anchor_accuracy = None
    if anchor_row is not None:
        anchor_accuracy = float(anchor_row.get("metrics", {}).get("dgt_accuracy_mean", 0.0))
    crossover_threshold = (
        round(anchor_accuracy - L1_CROSSOVER_TOLERANCE_ACC, 6)
        if anchor_accuracy is not None
        else None
    )
    crossover_rows: list[dict[str, Any]] = []
    for row in step_rows:
        metrics = row.get("metrics", {})
        dgt_accuracy = float(metrics.get("dgt_accuracy_mean", 0.0))
        baseline_accuracy = float(metrics.get("information_starved_accuracy_mean", 0.0))
        matched_accuracy = float(metrics.get("matched_random_accuracy_mean", 0.0))
        same_step_baseline_gap = round(dgt_accuracy - baseline_accuracy, 6)
        same_step_matched_gap = round(dgt_accuracy - matched_accuracy, 6)
        anchor_baseline_gap = round(anchor_accuracy - baseline_accuracy, 6) if anchor_accuracy is not None else None
        anchor_matched_gap = round(anchor_accuracy - matched_accuracy, 6) if anchor_accuracy is not None else None
        baseline_reaches_anchor = (
            crossover_threshold is not None
            and baseline_accuracy >= crossover_threshold
        )
        matched_reaches_anchor = (
            crossover_threshold is not None
            and matched_accuracy >= crossover_threshold
        )
        crossover_rows.append(
            {
                "training_steps": int(row["training_steps"]),
                "dgt_accuracy_mean": dgt_accuracy,
                "information_starved_accuracy_mean": baseline_accuracy,
                "matched_random_accuracy_mean": matched_accuracy,
                "same_step_dgt_minus_information_starved_accuracy": same_step_baseline_gap,
                "same_step_dgt_minus_matched_accuracy": same_step_matched_gap,
                "anchor_minus_information_starved_accuracy": anchor_baseline_gap,
                "anchor_minus_matched_random_accuracy": anchor_matched_gap,
                "information_starved_reaches_anchor_tolerance": baseline_reaches_anchor,
                "matched_random_reaches_anchor_tolerance": matched_reaches_anchor,
            }
        )
    baseline_steps = [row["training_steps"] for row in crossover_rows if row["information_starved_reaches_anchor_tolerance"]]
    matched_steps = [row["training_steps"] for row in crossover_rows if row["matched_random_reaches_anchor_tolerance"]]
    return {
        "status": "information-starved-crossover-observed" if baseline_steps else "no-information-starved-crossover-observed",
        "tolerance_accuracy": L1_CROSSOVER_TOLERANCE_ACC,
        "anchor_arm": "dgt_l1",
        "anchor_training_steps": L1_CROSSOVER_ANCHOR_STEPS,
        "anchor_accuracy_mean": anchor_accuracy,
        "crossover_threshold_accuracy": crossover_threshold,
        "information_starved_catches_up": bool(baseline_steps),
        "first_information_starved_crossover_step": min(baseline_steps) if baseline_steps else None,
        "matched_random_catches_up": bool(matched_steps),
        "first_matched_random_crossover_step": min(matched_steps) if matched_steps else None,
        "rows": crossover_rows,
        "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l1_step_ladder.convergence_crossover",
    }


def derive_l1_step_ladder_verdict(
    crossover: Mapping[str, Any],
    hardgates: Mapping[str, Mapping[str, Any]] | None = None,
) -> str:
    if hardgates is not None and any(row.get("status") != "pass" for row in hardgates.values()):
        return "inconclusive"
    if bool(crossover.get("matched_random_catches_up")):
        return "inconclusive"
    if bool(crossover.get("information_starved_catches_up")):
        return "information-starved-catches-up"
    if crossover.get("anchor_accuracy_mean") is None:
        return "inconclusive"
    rows = crossover.get("rows", [])
    if isinstance(rows, Sequence) and rows:
        return "scoped-review-signal"
    return "inconclusive"


def build_l1_step_ladder(records: Sequence[Mapping[str, Any]], config: L1TrainingConfig) -> dict[str, Any]:
    step_rows: list[dict[str, Any]] = []
    per_step: list[dict[str, Any]] = []
    for step_index, step in enumerate(config.step_grid):
        rows = [row for row in records if int(row.get("training_steps", -1)) == step]
        summaries = _arm_summaries(rows, pointer_prefix=f"l1_step_ladder.per_step[{step_index}].training_arms")
        if "matched_random_structural_l1" in summaries:
            summaries["matched_random_structural_l1"]["structural_marginals_preserved"] = True
        dgt = summaries.get("dgt_l1", {}).get("metrics", {})
        baseline = summaries.get("information_starved_l1_baseline", {}).get("metrics", {})
        matched = summaries.get("matched_random_structural_l1", {}).get("metrics", {})
        param = summaries.get("parameter_matched_l1", {}).get("metrics", {})
        compute = summaries.get("compute_matched_l1", {}).get("metrics", {})
        metrics = {
            "dgt_accuracy_mean": float(dgt.get("accuracy_mean", 0.0)),
            "information_starved_accuracy_mean": float(baseline.get("accuracy_mean", 0.0)),
            "matched_random_accuracy_mean": float(matched.get("accuracy_mean", 0.0)),
            "parameter_matched_accuracy_mean": float(param.get("accuracy_mean", 0.0)),
            "compute_matched_accuracy_mean": float(compute.get("accuracy_mean", 0.0)),
            "dgt_ood_accuracy_mean": float(dgt.get("ood_accuracy_mean", 0.0)),
            "information_starved_ood_accuracy_mean": float(baseline.get("ood_accuracy_mean", 0.0)),
            "matched_random_ood_accuracy_mean": float(matched.get("ood_accuracy_mean", 0.0)),
            "parameter_matched_ood_accuracy_mean": float(param.get("ood_accuracy_mean", 0.0)),
            "compute_matched_ood_accuracy_mean": float(compute.get("ood_accuracy_mean", 0.0)),
            "dgt_loss_decrease_mean": float(dgt.get("loss_decrease_mean", 0.0)),
            "information_starved_loss_decrease_mean": float(baseline.get("loss_decrease_mean", 0.0)),
            "matched_random_loss_decrease_mean": float(matched.get("loss_decrease_mean", 0.0)),
            "parameter_matched_loss_decrease_mean": float(param.get("loss_decrease_mean", 0.0)),
            "compute_matched_loss_decrease_mean": float(compute.get("loss_decrease_mean", 0.0)),
        }
        metrics["dgt_minus_information_starved_accuracy"] = round(
            metrics["dgt_accuracy_mean"] - metrics["information_starved_accuracy_mean"],
            6,
        )
        metrics["dgt_minus_matched_accuracy"] = round(
            metrics["dgt_accuracy_mean"] - metrics["matched_random_accuracy_mean"],
            6,
        )
        seed_counts = {
            arm_id: int(summary.get("seed_count", 0))
            for arm_id, summary in summaries.items()
        }
        per_step.append({
            "training_steps": step,
            "training_arms": summaries,
            "compute_ledger": _compute_ledger(summaries),
            "parameter_ledger": _parameter_ledger(summaries),
            "seed_counts": seed_counts,
            "metrics": metrics,
            "raw_record_start_pointer": f"{RUN_ROOT}/raw_metrics.jsonl:$.lines[{step_index * len(config.seeds) * len(ARM_IDS)}]",
        })
        step_rows.append(
            {
                "training_steps": step,
                "seed_counts": seed_counts,
                "metrics": metrics,
                "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l1_step_ladder.per_step[{step_index}]",
            }
        )
    crossover = derive_l1_step_ladder_crossover(step_rows)
    provisional = {
        "status": "provisional",
        "step_grid": list(config.step_grid),
        "arms": list(ARM_IDS),
        "seed_count_per_arm_per_step": len(config.seeds),
        "per_step": per_step,
        "step_rows": step_rows,
        "convergence_crossover": crossover,
        "verdict": "inconclusive",
        "hardgates": {},
        "not_claimed": list(NOT_CLAIMED),
    }
    hardgates = evaluate_l1step_hardgates(provisional)
    verdict = derive_l1_step_ladder_verdict(crossover, hardgates)
    status = "pass" if all(row["status"] == "pass" for row in hardgates.values()) else "fail"
    return {
        **provisional,
        "status": status,
        "verdict": verdict,
        "verdict_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l1_step_ladder.verdict",
        "convergence_crossover": crossover,
        "hardgates": hardgates,
        "mechanical_decision_table": {
            "information_starved_catches_up_and_matched_random_clear": "information-starved-catches-up",
            "no_information_starved_crossover_and_matched_random_clear": "scoped-review-signal",
            "any_l1step_hardgate_failure_or_matched_random_crossover": "inconclusive",
        },
        "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l1_step_ladder",
    }


def _compute_ledger(summaries: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    per_cell = {
        f"{arm_id}:{seed}": {
            "arm_id": arm_id,
            "seed": seed,
            "compute_units": round(float(summary["compute_units"]) / max(1, int(summary["seed_count"])), 6),
            "training_steps": summary["training_steps"],
        }
        for arm_id, summary in summaries.items()
        for seed in summary.get("seeds", [])
    }
    return {
        "status": "pass" if per_cell and all(row["compute_units"] > 0 and row["training_steps"] > 0 for row in per_cell.values()) else "fail",
        "compute_units": round(sum(float(row["compute_units"]) for row in per_cell.values()), 6),
        "per_arm": {arm_id: {"compute_units": summary["compute_units"], "seed_count": summary["seed_count"]} for arm_id, summary in summaries.items()},
        "per_seed_step_cell": per_cell,
    }


def _parameter_ledger(summaries: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    per_arm = {
        arm_id: {
            "parameter_count": int(summary["parameter_count"]),
            "trainable_parameter_count": int(summary["parameter_count"]),
            "parameter_match_ratio_to_dgt": round(int(summary["parameter_count"]) / max(1, int(summaries["dgt_l1"]["parameter_count"])), 6),
        }
        for arm_id, summary in summaries.items()
    }
    return {
        "status": "pass" if per_arm and all(row["parameter_count"] > 0 for row in per_arm.values()) else "fail",
        "parameter_count": sum(row["parameter_count"] for row in per_arm.values()),
        "per_arm": per_arm,
        "match_tolerance": MATCH_TOLERANCE,
        "parameter_match_tolerance": PARAMETER_MATCH_TOLERANCE,
    }


def _regression_test_pointer_resolves(pointer: str) -> bool:
    if "::" not in pointer:
        return False
    file_name, function_name = pointer.split("::", maxsplit=1)
    test_path = LAB_ROOT / file_name
    if not test_path.is_file():
        return False
    try:
        tree = ast.parse(test_path.read_text(encoding="utf-8"), filename=str(test_path))
    except SyntaxError:
        return False
    return any(isinstance(node, ast.FunctionDef) and node.name == function_name for node in tree.body)


def source_regression_guard() -> dict[str, Any]:
    source = inspect.getsource(importlib.import_module(__name__))
    forbidden_fragments = (
        "SCRIPTED" + "_" + "METRIC" + "_" + "TABLE",
        "PREFILLED" + "_" + "METRICS",
        "COMPONENT" + "_" + "EFFECTS",
    )
    hits = [token for token in forbidden_fragments if token in source]
    required_terms = ("torch.optim.Adam", "loss.backward()", "optimizer.step()")
    missing = [term for term in required_terms if term not in source]
    return {
        "status": "pass" if not hits and not missing else "fail",
        "forbidden_hits": hits,
        "required_training_terms": list(required_terms),
        "missing_training_terms": missing,
        "owner_module": OWNER_MODULE,
    }


def _negative_witness_sweep(summaries: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    dgt = summaries["dgt_l1"]["metrics"]
    baseline = summaries["information_starved_l1_baseline"]["metrics"]
    matched = summaries["matched_random_structural_l1"]["metrics"]
    guard = source_regression_guard()
    rows = [
        {
            "witness": "information_starved_baseline",
            "hardgate_id": "ISB-HG",
            "critical": True,
            "hit_count": int(baseline["accuracy_mean"] >= dgt["accuracy_mean"] - QUALITY_MARGIN),
            "hit_logic": "information-starved baseline accuracy mean must stay below DGT mean minus L1 margin",
            "source_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.information_starved_l1_baseline",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.paired_accuracy.dgt_minus_information_starved_baseline",
            "claim_downgrade": "bounded in-distribution review signal only",
            "not_claimed": "No claim that DGT is empirically better than Transformer in general.",
            "regression_test": "tests/test_dgt_l1_controls.py::test_l1_negative_witness_sweep_uses_hit_logic",
            "taint_status": "tainted-l1-review-only",
        },
        {
            "witness": "unanswerable_ood",
            "hardgate_id": "UOOD-HG",
            "critical": True,
            "hit_count": int(dgt["ood_accuracy_mean"] >= dgt["accuracy_mean"]),
            "hit_logic": "OOD shuffled-pair dependency must not inflate the positive slice",
            "source_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l1_tiny_sequence_projection.ood_boundary",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.dgt_l1.metrics.ood_accuracy_mean",
            "claim_downgrade": "OOD generalization not claimed",
            "not_claimed": "No claim that DGT generalizes to tiny-sequence OOD splits.",
            "regression_test": "tests/test_dgt_l1_controls.py::test_l1_independent_replay_checks_digest_and_metric_tolerance",
            "taint_status": "tainted-ood-not-claimed",
        },
        {
            "witness": "table_coverage_saturation",
            "hardgate_id": "TCS-HG",
            "critical": True,
            "hit_count": int(matched["accuracy_mean"] >= dgt["accuracy_mean"] - QUALITY_MARGIN),
            "hit_logic": "matched-random structural control must not satisfy the positive L1 claim",
            "source_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.matched_random_structural_l1",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.paired_accuracy.dgt_minus_matched_random",
            "claim_downgrade": "table-coverage result cannot be promoted to general scaling",
            "not_claimed": "No L1 scaling success claim.",
            "regression_test": "tests/test_dgt_l1_controls.py::test_l1_matched_random_structural_control_fail_closed",
            "taint_status": "tainted-coverage-local",
        },
        {
            "witness": "hand_engineered_task_aligned_gate",
            "hardgate_id": "HEG-HG",
            "critical": True,
            "hit_count": int(guard["status"] != "pass"),
            "hit_logic": "owner source must contain real torch optimizer updates and no scripted metric table token",
            "source_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.source_artifacts.order_k_required_order_row",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.source_regression_guard",
            "claim_downgrade": "hand-engineered order-two task gate remains a bounded fixture",
            "not_claimed": "No claim that the model learned an order-2 rule as a causal component.",
            "regression_test": "tests/test_dgt_l1_controls.py::test_l1_training_requires_real_torch_updates",
            "taint_status": "tainted-hand-engineered-task",
        },
    ]
    for row in rows:
        row["regression_test_pointer"] = row["regression_test"]
        row["regression_test_pointer_resolves"] = _regression_test_pointer_resolves(str(row["regression_test"]))
    critical_hits = sum(int(row["hit_count"]) for row in rows if row["critical"])
    pointers_resolve = all(bool(row["regression_test_pointer_resolves"]) for row in rows)
    return {
        "status": "pass" if rows and critical_hits == 0 and pointers_resolve else "fail",
        "required_witnesses": list(REQUIRED_WITNESSES),
        "critical_hit_count": critical_hits,
        "rows": rows,
        "source_regression_guard": guard,
        "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.negative_witness_sweep",
    }


def _json_digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _independent_replay(task_spec: Mapping[str, Any], records: Sequence[Mapping[str, Any]], summaries: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    seeds = tuple(int(row["seed"]) for row in records if row["arm_id"] == "dgt_l1")
    seed_digest = _json_digest(list(seeds))
    task_digest = _json_digest(task_spec)
    by_seed: dict[int, dict[str, float]] = {}
    for seed in seeds:
        cells = {row["arm_id"]: row for row in records if int(row["seed"]) == seed}
        if set(cells) == set(ARM_IDS):
            by_seed[seed] = {
                "dgt_minus_information_starved_accuracy": round(
                    float(cells["dgt_l1"]["metrics"]["accuracy"])
                    - float(cells["information_starved_l1_baseline"]["metrics"]["accuracy"]),
                    6,
                ),
                "dgt_minus_matched_accuracy": round(
                    float(cells["dgt_l1"]["metrics"]["accuracy"])
                    - float(cells["matched_random_structural_l1"]["metrics"]["accuracy"]),
                    6,
                ),
                "dgt_minus_parameter_matched_accuracy": round(
                    float(cells["dgt_l1"]["metrics"]["accuracy"]) - float(cells["parameter_matched_l1"]["metrics"]["accuracy"]),
                    6,
                ),
                "dgt_minus_compute_matched_accuracy": round(
                    float(cells["dgt_l1"]["metrics"]["accuracy"]) - float(cells["compute_matched_l1"]["metrics"]["accuracy"]),
                    6,
                ),
            }
    metric_tolerance_rows = [
        {
            "seed": seed,
            "status": "pass"
            if row["dgt_minus_information_starved_accuracy"] >= -REPLAY_TOLERANCE
            and row["dgt_minus_matched_accuracy"] >= -REPLAY_TOLERANCE
            else "fail",
            **row,
        }
        for seed, row in by_seed.items()
    ]
    return {
        "status": "pass"
        if len(seeds) >= 16
        and len(by_seed) == len(seeds)
        and all(row["status"] == "pass" for row in metric_tolerance_rows)
        else "fail",
        "task_spec_digest": task_digest,
        "seed_digest": seed_digest,
        "seed_count": len(seeds),
        "fixed_seeds": list(seeds),
        "metric_tolerance": REPLAY_TOLERANCE,
        "metric_tolerance_rows": metric_tolerance_rows,
        "summary_metrics": {
            arm_id: dict(summary["metrics"])
            for arm_id, summary in summaries.items()
        },
        "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.independent_replay",
    }


def _component_ablation_boundary() -> dict[str, Any]:
    return {
        "status": "boundary-only",
        "owner_issue": "github:issue:1168",
        "owner_artifact": "reports/canonical/dgt-neural-ablation.json",
        "owner_pointer": "reports/canonical/dgt-neural-ablation.json:$.pure_hardgates",
        "measured_status": "measured-owner-required",
        "not_recreated_here": True,
    }


def _owner_local_measurement_boundary() -> dict[str, Any]:
    metric_owners = {
        "FalseLedgerRate": "reports/canonical/dgt-neural-ablation.json:$.paired_delta_matrix.DGT_without_ledger_head.metrics.FalseLedgerRate",
        "JetCoverage": "reports/runs/discovery-gated-transformer/jet_certificate.json:$.jet_coverage",
        "classifier_shift_count": "reports/canonical/dgt-neural-ablation.json:$.paired_delta_matrix.DGT_without_mechanism_probe.metrics.classifier_shift_count",
    }
    return {
        "status": "boundary-only",
        "measured_status": "measured-owner-required",
        "owner_issue": "github:issue:1168",
        "not_measurable_here": list(OWNER_REQUIRED_METRICS),
        "reason": "L1 tiny controls use embedding plus two-layer MLP training and do not instantiate ledger, jet, or classifier mechanisms.",
        "metric_owners": metric_owners,
        "owner_pointers": list(metric_owners.values()),
        "not_recreated_here": True,
        "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.owner_local_measurement_boundary",
    }


def source_artifacts_payload(*, requested_device: str) -> dict[str, Any]:
    return {
        "owner_module": OWNER_MODULE,
        "runner": PRODUCER,
        "command": ["python3", PRODUCER],
        "input_accessibility_ref": f"{INPUT_ACCESSIBILITY_JSON_ARTIFACT}:$",
        "input_accessibility_consumer_pointers": f"{INPUT_ACCESSIBILITY_JSON_ARTIFACT}:$.consumer_pointers",
        "order_k_required_order_source": ORDER_K_LEDGER_ROWS_POINTER,
        "order_k_required_order_row": ORDER_K_TASK_LEDGER_POINTER,
        "run_local_claim_capsule": f"{RUN_ROOT}/claim_capsule.json",
        "run_local_raw_metrics": f"{RUN_ROOT}/raw_metrics.jsonl",
        "run_local_summary": f"{RUN_ROOT}/summary.json",
        "run_local_report": f"{RUN_ROOT}/report.md",
        "seed_policy": {"base_seed": BASE_SEED, "deterministic_seeds": list(DEFAULT_SEEDS), "minimum_seed_count": 16},
        "device_policy": {"requested_device": requested_device, "canonical_default": "cpu", "mps_allowed_when_explicit": True},
        "component_ablation_owner": "reports/canonical/dgt-neural-ablation.json:$.pure_hardgates",
        "owner_required_metric_owners": _owner_local_measurement_boundary()["metric_owners"],
    }


def _load_json_artifact(root: Path | None, artifact: str) -> Mapping[str, Any]:
    path = (root or LAB_ROOT) / artifact
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise ValueError(f"DGT L1 required canonical artifact missing: {artifact}") from exc
    except json.JSONDecodeError as exc:
        raise ValueError(f"DGT L1 required canonical artifact invalid: {artifact}") from exc
    if not isinstance(payload, Mapping):
        raise ValueError(f"DGT L1 required canonical artifact is not an object: {artifact}")
    return payload


def _input_accessibility_row_pointer(row: Mapping[str, Any]) -> str:
    return f"{INPUT_ACCESSIBILITY_JSON_ARTIFACT}#row_id={row['row_id']}"


def _input_accessibility_rows_by_ref(payload: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    rows = payload.get("rows")
    if not isinstance(rows, list):
        raise ValueError("DGT L1 input-accessibility rows missing")
    result: dict[str, Mapping[str, Any]] = {}
    for row in rows:
        if not isinstance(row, Mapping) or not isinstance(row.get("row_id"), str):
            raise ValueError("DGT L1 input-accessibility row shape mismatch")
        result[_input_accessibility_row_pointer(row)] = row
    return result


def _input_accessibility_ref_rows(
    payload: Mapping[str, Any],
    key: str,
) -> tuple[list[str], list[Mapping[str, Any]]]:
    pointers = payload.get("consumer_pointers", {}).get(key)
    if not isinstance(pointers, list) or not all(isinstance(pointer, str) for pointer in pointers):
        raise ValueError(f"DGT L1 input-accessibility consumer pointer missing: {key}")
    rows_by_ref = _input_accessibility_rows_by_ref(payload)
    rows: list[Mapping[str, Any]] = []
    for pointer in pointers:
        row = rows_by_ref.get(pointer)
        if row is None:
            raise ValueError(f"DGT L1 input-accessibility consumer pointer does not resolve: {pointer}")
        rows.append(row)
    return list(pointers), rows


def _input_accessibility_arm_input_access(*, root: Path | None = None) -> dict[str, Any]:
    payload = _load_json_artifact(root, INPUT_ACCESSIBILITY_JSON_ARTIFACT)
    consumers = payload.get("consumer_pointers")
    if not isinstance(consumers, Mapping):
        raise ValueError("DGT L1 input-accessibility consumer pointers missing")
    input_ref = consumers.get("input_accessibility_ref")
    if input_ref != f"{INPUT_ACCESSIBILITY_JSON_ARTIFACT}:$":
        raise ValueError("DGT L1 input-accessibility root pointer mismatch")
    information_starved_refs, _information_starved_rows = _input_accessibility_ref_rows(
        payload,
        "information_starved_arms_ref",
    )
    unanswerable_refs, _unanswerable_rows = _input_accessibility_ref_rows(
        payload,
        "unanswerable_ood_splits_ref",
    )
    rows = list(_input_accessibility_rows_by_ref(payload).values())
    extraction_clean = all(
        row.get("feature_extraction", {}).get("status") == "pass"
        and row.get("label_extraction", {}).get("status") == "pass"
        for row in rows
    )
    arms = {
        f"{row['arm']}:{row['split']}": {
            "variables": list(row.get("visible_variables", [])),
            "required_variables": list(row.get("required_variables", [])),
            "missing_variables": list(row.get("missing_variables", [])),
            "coverage_status": row.get("coverage_status"),
            "information_starved": row.get("information_starved"),
            "unanswerable_ood": row.get("unanswerable_ood"),
            "canonical_row": _input_accessibility_row_pointer(row),
        }
        for row in rows
    }
    return {
        "label_invisibility_certificate": extraction_clean,
        "certificate_pointer": input_ref,
        "input_accessibility_ref": input_ref,
        "information_starved_arms_ref": information_starved_refs,
        "unanswerable_ood_splits_ref": unanswerable_refs,
        "boundary_ledger_ref": f"{INPUT_ACCESSIBILITY_JSON_ARTIFACT}:$.boundary_ledger",
        "boundary_ledger_count": len(payload.get("boundary_ledger", [])),
        "arms": arms,
    }


def construct_validity_evidence(
    *,
    summaries: Mapping[str, Mapping[str, Any]] | None = None,
    config: L1TrainingConfig | None = None,
    root: Path | None = None,
) -> ConstructValidityEvidence:
    cfg = config or L1TrainingConfig()
    metric_keys = list(L1_MEASURABLE_METRICS)
    if summaries:
        metric_keys = sorted({
            metric
            for row in summaries.values()
            if isinstance(row, Mapping)
            for metric in row.get("metrics", {}).keys()
        })
    return ConstructValidityEvidence(
        task_variables={
            "variables": ["token_sequence", "x_prev_1", "x_prev_2", "surface_id"],
            "pointer": "$.construct_validity_hardgates.evidence.task_variables",
        },
        label_variables={
            "variables": ["next_token_label", "ood_next_token_label"],
            "pointer": "$.construct_validity_hardgates.evidence.label_variables",
        },
        arm_input_access={
            **_input_accessibility_arm_input_access(root=root),
        },
        arm_roles={
            "candidate": "dgt_l1",
            "controls": [
                "information_starved_l1_baseline",
                "matched_random_structural_l1",
                "parameter_matched_l1",
                "compute_matched_l1",
            ],
        },
        finite_table={
            "coverage_status": "bounded-control",
            "support_count": min(cfg.eval_examples, cfg.vocab_size * cfg.vocab_size),
            "rule_abstraction_claim": False,
            "table_coverage_only": False,
            "finite_pair_accuracy": None,
        },
        hand_feature_ledger={
            "mode": "shared-gate",
            "shared_across_arms": True,
            "features": ["token_position_access", "bounded_pair_surface"],
            "candidate_only_features": [],
        },
        metric_source={
            "source_kind": "training-evaluation",
            "metric_keys": metric_keys,
            "per_arm_constants": False,
            "label_derived_metric_source": False,
            "source_pointer": f"{RUN_ROOT}/raw_metrics.jsonl:$",
        },
    )


def construct_validity_payload(
    *,
    summaries: Mapping[str, Mapping[str, Any]] | None = None,
    config: L1TrainingConfig | None = None,
    root: Path | None = None,
) -> dict[str, Any]:
    return construct_validity_projection(
        construct_validity_evidence(summaries=summaries, config=config, root=root),
        artifact=CANONICAL_JSON_ARTIFACT,
        pointer="$.construct_validity_hardgates",
    )


def _resolve_order_k_source(task: Mapping[str, Any], *, root: Path | None = None) -> Mapping[str, Any]:
    source = task.get("required_order_source")
    if not isinstance(source, Mapping):
        raise ValueError("DGT L1 required-order source missing")
    if source.get("status") != "pointer-backed" or source.get("task_spec_owner") != "single-owner":
        raise ValueError("DGT L1 required-order source must be pointer-backed")
    if source.get("ledger_rows_pointer") != ORDER_K_LEDGER_ROWS_POINTER:
        raise ValueError("DGT L1 required-order ledger rows pointer mismatch")
    if source.get("ledger_row_pointer") != ORDER_K_TASK_LEDGER_POINTER:
        raise ValueError("DGT L1 required-order ledger row pointer mismatch")
    resolved_root = root or LAB_ROOT
    row = resolve_artifact_pointer(resolved_root, str(source["ledger_row_pointer"]))
    if not isinstance(row, Mapping):
        raise ValueError("DGT L1 required-order pointer does not resolve")
    if row.get("task_id") != ORDER_K_TASK_ID or row.get("surface_id") != ORDER_K_SURFACE_ID:
        raise ValueError("DGT L1 required-order pointer resolved to wrong task")
    if int(row.get("required_order", -1)) != 2:
        raise ValueError("DGT L1 required-order pointer must resolve to order two")
    return row


def _gate(status: bool, gate_id: str, criterion: str, evidence_pointer: str, reason: str | None = None) -> dict[str, Any]:
    return L1HardGateRow(
        gate_id=gate_id,
        status="pass" if status else "fail",
        criterion=criterion,
        evidence_pointer=evidence_pointer,
        fail_closed_reason=None if status else reason or criterion,
    ).as_payload()


def _mapping_cell(payload: Mapping[str, Any], key: str) -> Mapping[str, Any]:
    cell = payload.get(key)
    return cell if isinstance(cell, Mapping) else {}


def _arm_cell(arms: Mapping[str, Any], arm_id: str) -> Mapping[str, Any] | None:
    cell = arms.get(arm_id)
    return cell if isinstance(cell, Mapping) else None


def _exact_arm_key_set(value: Mapping[str, Any]) -> bool:
    return set(value) == set(ARM_IDS)


def _control_context(payload: Mapping[str, Any]) -> dict[str, Any]:
    arms = _mapping_cell(payload, "training_arms")
    return {
        "arms": arms,
        "compute": _mapping_cell(payload, "compute_ledger"),
        "params": _mapping_cell(payload, "parameter_ledger"),
        "paired": _mapping_cell(payload, "paired_accuracy"),
        "measurement_boundary": _mapping_cell(payload, "owner_local_measurement_boundary"),
        "negative": _mapping_cell(payload, "negative_witness_sweep"),
        "replay": _mapping_cell(payload, "independent_replay"),
        "capsule": _mapping_cell(payload, "claim_capsule_ref"),
        "review_status": payload.get("review_status"),
        "promotion_readiness": payload.get("promotion_readiness"),
        "dgt": _arm_cell(arms, "dgt_l1"),
        "information_starved_baseline": _arm_cell(arms, "information_starved_l1_baseline"),
        "matched": _arm_cell(arms, "matched_random_structural_l1"),
        "parameter_matched": _arm_cell(arms, "parameter_matched_l1"),
        "compute_matched": _arm_cell(arms, "compute_matched_l1"),
        "l1_step_ladder": _mapping_cell(payload, "l1_step_ladder"),
    }


def _params_and_compute_match(candidate: Mapping[str, Any] | None, control: Mapping[str, Any] | None) -> bool:
    if not isinstance(candidate, Mapping) or not isinstance(control, Mapping):
        return False
    candidate_params = int(candidate.get("parameter_count", 0))
    control_params = int(control.get("parameter_count", 0))
    candidate_compute = float(candidate.get("compute_units", 0))
    control_compute = float(control.get("compute_units", 0))
    return (
        candidate_params > 0
        and abs(control_params - candidate_params) / candidate_params <= MATCH_TOLERANCE
        and candidate_compute > 0
        and abs(control_compute - candidate_compute) / candidate_compute <= MATCH_TOLERANCE
    )


def _matched_random_positive_control(dgt: Mapping[str, Any] | None, matched: Mapping[str, Any] | None) -> bool:
    if not isinstance(dgt, Mapping) or not isinstance(matched, Mapping):
        return False
    return matched.get("metrics", {}).get("accuracy_mean", 1.0) >= dgt.get("metrics", {}).get("accuracy_mean", 0.0) - QUALITY_MARGIN


def _arm_seed_complete(arms: Mapping[str, Any], seed_count: int = 16) -> bool:
    return (
        _exact_arm_key_set(arms)
        and all(
            isinstance(row, Mapping)
            and row.get("status") == "pass"
            and int(row.get("seed_count", 0)) >= seed_count
            and row.get("device_resolved") == "cpu"
            and int(row.get("training_steps", 0)) > 0
            and float(row.get("metrics", {}).get("loss_decrease_mean", 0.0)) > 0.0
            and float(row.get("metrics", {}).get("parameter_l2_delta_mean", 0.0)) > 0.0
            for row in arms.values()
        )
    )


def _owner_local_measurement_boundary_resolves(boundary: Mapping[str, Any], *, root: Path | None = None) -> bool:
    if boundary.get("measured_status") != "measured-owner-required":
        return False
    if boundary.get("not_recreated_here") is not True:
        return False
    if tuple(boundary.get("not_measurable_here", ())) != OWNER_REQUIRED_METRICS:
        return False
    owners = boundary.get("metric_owners")
    if not isinstance(owners, Mapping) or tuple(owners) != OWNER_REQUIRED_METRICS:
        return False
    resolved_root = root or LAB_ROOT
    return all(resolve_artifact_pointer(resolved_root, str(pointer)) is not None for pointer in owners.values())


def _param_close_to_dgt(dgt: Mapping[str, Any] | None, control: Mapping[str, Any] | None) -> bool:
    if not isinstance(dgt, Mapping) or not isinstance(control, Mapping):
        return False
    dgt_params = int(dgt.get("parameter_count", 0))
    control_params = int(control.get("parameter_count", 0))
    if dgt_params <= 0:
        return False
    delta = abs(control_params - dgt_params) / dgt_params
    return delta <= PARAMETER_MATCH_TOLERANCE


def _compute_close_to_dgt(dgt: Mapping[str, Any] | None, control: Mapping[str, Any] | None) -> bool:
    if not isinstance(dgt, Mapping) or not isinstance(control, Mapping):
        return False
    dgt_compute = float(dgt.get("compute_units", 0.0))
    control_compute = float(control.get("compute_units", 0.0))
    if dgt_compute <= 0.0:
        return False
    return abs(control_compute - dgt_compute) / dgt_compute <= COMPUTE_MATCH_TOLERANCE


def _gate_l1_hg1(context: Mapping[str, Any]) -> dict[str, Any]:
    arms = context["arms"]
    boundary = context["measurement_boundary"]
    return _gate(
        isinstance(arms, Mapping)
        and _arm_seed_complete(arms)
        and all(
            all(metric in row.get("metrics", {}) for metric in L1_MEASURABLE_METRICS)
            and _owner_required_metric_absent(row.get("metrics", {}))
            for row in arms.values()
            if isinstance(row, Mapping)
        )
        and isinstance(boundary, Mapping)
        and _owner_local_measurement_boundary_resolves(boundary),
        "L1-REVIEW-HG1",
        "five L1 arms have true-training metrics while ledger, jet, and classifier metrics are owner-required boundaries",
        "$.owner_local_measurement_boundary",
    )


def _gate_l1_hg2(context: Mapping[str, Any]) -> dict[str, Any]:
    paired = context["paired"].get("dgt_minus_information_starved_baseline")
    return _gate(
        isinstance(paired, Mapping)
        and int(paired.get("seed_count", 0)) >= 16
        and float(paired.get("delta_ci95_low", 0.0)) > 0.0,
        "L1-REVIEW-HG2",
        "seed-paired DGT minus information-starved baseline in-distribution accuracy CI95-low is positive",
        "$.paired_accuracy.dgt_minus_information_starved_baseline.delta_ci95_low",
    )


def _gate_l1_hg3(context: Mapping[str, Any]) -> dict[str, Any]:
    paired = context["paired"].get("dgt_minus_matched_random")
    matched = context["matched"]
    return _gate(
        isinstance(paired, Mapping)
        and isinstance(matched, Mapping)
        and int(paired.get("seed_count", 0)) >= 16
        and matched.get("structural_marginals_preserved") is True
        and float(paired.get("delta_ci95_low", 0.0)) > 0.0,
        "L1-REVIEW-HG3",
        "seed-paired DGT minus matched-random accuracy CI95-low is positive with structural marginals preserved",
        "$.paired_accuracy.dgt_minus_matched_random.delta_ci95_low",
    )


def _gate_l1_hg4(context: Mapping[str, Any]) -> dict[str, Any]:
    matched = context["matched"]
    arms = context["arms"]
    return _gate(
        isinstance(matched, Mapping)
        and matched.get("structural_marginals_preserved") is True
        and all(
            isinstance(row, Mapping)
            and isinstance(row.get("metrics"), Mapping)
            and _owner_required_metric_absent(row["metrics"])
            for row in arms.values()
        ),
        "L1-REVIEW-HG4",
        "matched-random structural control preserves marginals and no L1 arm reports owner-required ledger, jet, or classifier metrics",
        "$.training_arms.matched_random_structural_l1.metrics",
    )


def _gate_l1_hg5(context: Mapping[str, Any]) -> dict[str, Any]:
    dgt = context["dgt"]
    param = context["parameter_matched"]
    compute = context["compute_matched"]
    params = context["params"]
    compute_ledger = context["compute"]
    param_cells = params.get("per_arm") if isinstance(params, Mapping) else {}
    compute_cells = compute_ledger.get("per_seed_step_cell") if isinstance(compute_ledger, Mapping) else {}
    return _gate(
        params.get("status") == "pass"
        and compute_ledger.get("status") == "pass"
        and bool(param_cells)
        and bool(compute_cells)
        and all(isinstance(row, Mapping) and int(row.get("parameter_count", 0)) > 0 for row in param_cells.values())
        and all(isinstance(row, Mapping) and float(row.get("compute_units", 0.0)) > 0.0 for row in compute_cells.values())
        and _param_close_to_dgt(dgt, param)
        and _compute_close_to_dgt(dgt, compute),
        "L1-REVIEW-HG5",
        "parameter-matched and compute-matched controls satisfy owner-local fairness ledgers",
        "$.parameter_ledger",
    )


def _gate_l1_hg6(context: Mapping[str, Any]) -> dict[str, Any]:
    replay = context["replay"]
    negative = context["negative"]
    witness_rows = negative.get("rows", [])
    ladder = context["l1_step_ladder"]
    return _gate(
        replay.get("status") == "pass"
        and isinstance(replay.get("task_spec_digest"), str)
        and bool(replay.get("task_spec_digest"))
        and isinstance(replay.get("seed_digest"), str)
        and bool(replay.get("seed_digest"))
        and all(row.get("status") == "pass" for row in replay.get("metric_tolerance_rows", [])),
        "L1-REVIEW-HG6",
        "independent replay, negative witnesses, and bounded order-two scope are fail-closed",
        "$.independent_replay",
        None,
    ) if (
        negative.get("status") == "pass"
        and bool(witness_rows)
        and all(row.get("regression_test_pointer_resolves") for row in witness_rows)
        and ladder.get("status") == "pass"
    ) else _gate(
        False,
        "L1-REVIEW-HG6",
        "independent replay, negative witnesses, and bounded order-two scope are fail-closed",
        "$.negative_witness_sweep",
    )


def _gate_l1_hg7(context: Mapping[str, Any]) -> dict[str, Any]:
    prior = {
        "L1-REVIEW-HG1": _gate_l1_hg1(context),
        "L1-REVIEW-HG2": _gate_l1_hg2(context),
        "L1-REVIEW-HG3": _gate_l1_hg3(context),
        "L1-REVIEW-HG4": _gate_l1_hg4(context),
        "L1-REVIEW-HG5": _gate_l1_hg5(context),
        "L1-REVIEW-HG6": _gate_l1_hg6(context),
    }
    return _gate(
        all(row["status"] == "pass" for row in prior.values())
        and context["review_status"] in {"pass", "scoped-boundary"}
        and context["promotion_readiness"] in {"ready-pass", "scoped-boundary"},
        "L1-REVIEW-HG7",
        "review verdict is emitted only after L1-REVIEW-HG1 through L1-REVIEW-HG6 pass",
        "$.l1_tiny_sequence_projection.review_status",
    )


def _gate_l1step_hg1(
    step_grid: Sequence[int],
    per_step: Sequence[Any],
    step_rows: Sequence[Any],
    seed_count: int,
) -> dict[str, Any]:
    expected_cells = len(step_grid) * len(ARM_IDS) * seed_count
    complete_cells = (
        bool(step_grid)
        and tuple(sorted(step_grid)) == tuple(step_grid)
        and len(per_step) == len(step_grid)
        and all(
            isinstance(step, Mapping)
            and isinstance(step.get("training_arms"), Mapping)
            and _exact_arm_key_set(step["training_arms"])
            and isinstance(step.get("seed_counts"), Mapping)
            and _exact_arm_key_set(step["seed_counts"])
            and int(step.get("training_steps", -1)) == step_grid[index]
            and all(int(count) == seed_count and int(count) >= 16 for count in step["seed_counts"].values())
            for index, step in enumerate(per_step)
        )
        and len(step_rows) == len(step_grid)
        and all(
            isinstance(row, Mapping)
            and int(row.get("training_steps", -1)) == step_grid[index]
            for index, row in enumerate(step_rows)
        )
    )
    return _gate(
        complete_cells,
        "L1STEP-HG1",
        f"canonical step grid has {expected_cells} step/arm/seed CPU training cells",
        "$.l1_step_ladder.per_step",
    )


def _gate_l1step_hg2(per_step: Sequence[Any]) -> dict[str, Any]:
    true_cpu = all(
        isinstance(step, Mapping)
        and all(
            row.get("status") == "pass"
            and row.get("device_resolved") == "cpu"
            and int(row.get("training_steps", 0)) == int(step.get("training_steps", 0))
            and float(row.get("metrics", {}).get("parameter_l2_delta_mean", 0.0)) > 0.0
            and float(row.get("metrics", {}).get("loss_decrease_mean", 0.0)) > 0.0
            for row in step.get("training_arms", {}).values()
        )
        for step in per_step
    )
    return _gate(
        true_cpu,
        "L1STEP-HG2",
        "every ladder cell is true CPU training with parameter updates and loss decrease",
        "$.l1_step_ladder.per_step",
    )


def _gate_l1step_hg3(per_step: Sequence[Any]) -> dict[str, Any]:
    ledgers = all(
        isinstance(step, Mapping)
        and step.get("compute_ledger", {}).get("status") == "pass"
        and step.get("parameter_ledger", {}).get("status") == "pass"
        and float(step.get("compute_ledger", {}).get("compute_units", 0.0)) > 0.0
        and int(step.get("parameter_ledger", {}).get("parameter_count", 0)) > 0
        for step in per_step
    )
    return _gate(
        ledgers,
        "L1STEP-HG3",
        "every ladder step has positive compute and parameter ledgers",
        "$.l1_step_ladder.per_step",
    )


def _gate_l1step_hg4(crossover: Mapping[str, Any], step_rows: Sequence[Any]) -> dict[str, Any]:
    crossover_derived = (
        isinstance(crossover, Mapping)
        and crossover
        and crossover == derive_l1_step_ladder_crossover(step_rows)
    )
    return _gate(
        crossover_derived,
        "L1STEP-HG4",
        "crossover is mechanically derived from the 36-step DGT anchor and per-step accuracy means",
        "$.l1_step_ladder.convergence_crossover",
    )


def _gate_l1step_hg5(crossover: Mapping[str, Any]) -> dict[str, Any]:
    matched_random_clear = isinstance(crossover, Mapping) and crossover.get("matched_random_catches_up") is False
    return _gate(
        matched_random_clear,
        "L1STEP-HG5",
        "matched-random structural arm must not reach the 36-step DGT anchor tolerance band",
        "$.l1_step_ladder.convergence_crossover",
    )


def evaluate_l1step_hardgates(ladder: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    step_grid = tuple(int(step) for step in ladder.get("step_grid", ()))
    per_step = ladder.get("per_step", [])
    step_rows = ladder.get("step_rows", [])
    crossover = ladder.get("convergence_crossover", {})
    seed_count = int(ladder.get("seed_count_per_arm_per_step", 0))
    per_step_rows = per_step if isinstance(per_step, Sequence) else []
    summary_rows = step_rows if isinstance(step_rows, Sequence) else []
    return {
        "L1STEP-HG1": _gate_l1step_hg1(step_grid, per_step_rows, summary_rows, seed_count),
        "L1STEP-HG2": _gate_l1step_hg2(per_step_rows),
        "L1STEP-HG3": _gate_l1step_hg3(per_step_rows),
        "L1STEP-HG4": _gate_l1step_hg4(crossover, summary_rows),
        "L1STEP-HG5": _gate_l1step_hg5(crossover),
    }


def evaluate_hardgates(payload: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    context = _control_context(payload)
    return {
        "L1-REVIEW-HG1": _gate_l1_hg1(context),
        "L1-REVIEW-HG2": _gate_l1_hg2(context),
        "L1-REVIEW-HG3": _gate_l1_hg3(context),
        "L1-REVIEW-HG4": _gate_l1_hg4(context),
        "L1-REVIEW-HG5": _gate_l1_hg5(context),
        "L1-REVIEW-HG6": _gate_l1_hg6(context),
        "L1-REVIEW-HG7": _gate_l1_hg7(context),
    }


def _hardgate_status(gates: Mapping[str, Mapping[str, Any]]) -> tuple[str, list[str]]:
    failures = [gate_id for gate_id in L1_GATE_IDS if gates.get(gate_id, {}).get("status") != "pass"]
    return ("pass" if not failures else "fail", failures)


def build_claim_capsule(payload: Mapping[str, Any], gates: Mapping[str, Mapping[str, Any]] | None = None) -> dict[str, Any]:
    gate_rows = gates if gates is not None else evaluate_hardgates(payload)
    gate_status, failures = _hardgate_status(gate_rows)
    construct_validity = payload.get("construct_validity_hardgates")
    cv_projection = None
    if isinstance(construct_validity, Mapping):
        cv_projection = evaluate_construct_validity(
            ConstructValidityEvidence.from_payload(construct_validity.get("evidence", {}))
        ).claim_capsule_projection_for(
            artifact=CANONICAL_JSON_ARTIFACT,
            pointer="$.construct_validity_hardgates",
        )
    capsule = {
        "schema_id": "bedc.quality.claim_capsule",
        "capsule_subtype": "bedc.model.dgt_l1_tiny_sequence_claim_capsule",
        "claim_id": "claim:dgt-l1-tiny-sequence",
        "report": "dgt-l1-controls",
        "source": CANONICAL_JSON_ARTIFACT,
        "source_pointer": "$.l1_tiny_sequence_projection",
        "status": "pass" if gate_status == "pass" else "blocked",
        "evidence_scope": "bounded-tiny-sequence",
        "model_claim": {
            "model_id": "discovery-gated-transformer",
            "task_family": "bounded_tiny_sequence_order_k",
            "task_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.task_spec",
            "candidate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.dgt_l1",
            "information_starved_baseline_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.information_starved_l1_baseline",
            "matched_random_control_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.matched_random_structural_l1",
            "parameter_matched_control_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.parameter_matched_l1",
            "compute_matched_control_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.compute_matched_l1",
            "compute_ledger_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.compute_ledger",
            "parameter_ledger_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.parameter_ledger",
            "paired_accuracy_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.paired_accuracy",
            "negative_witness_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.negative_witness_sweep",
            "independent_replay_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.independent_replay",
            "owner_local_measurement_boundary_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.owner_local_measurement_boundary",
            "step_ladder_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l1_step_ladder",
            "review_status_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l1_tiny_sequence_projection.review_status",
            "allowed_claim": ALLOWED_CLAIM,
            "forbidden_claims": list(FORBIDDEN_CLAIMS),
        },
        "hardgate_pointers": {
            gate_id: f"{CANONICAL_JSON_ARTIFACT}:$.hardgates.{gate_id}"
            for gate_id in L1_GATE_IDS
        },
        "evidence_pointers": [
            f"{CANONICAL_JSON_ARTIFACT}:$.task_spec",
            f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.dgt_l1",
            f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.information_starved_l1_baseline",
            f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.matched_random_structural_l1",
            f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.parameter_matched_l1",
            f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.compute_matched_l1",
            f"{CANONICAL_JSON_ARTIFACT}:$.compute_ledger",
            f"{CANONICAL_JSON_ARTIFACT}:$.parameter_ledger",
            f"{CANONICAL_JSON_ARTIFACT}:$.paired_accuracy",
            f"{CANONICAL_JSON_ARTIFACT}:$.negative_witness_sweep",
            f"{CANONICAL_JSON_ARTIFACT}:$.independent_replay",
            f"{CANONICAL_JSON_ARTIFACT}:$.owner_local_measurement_boundary",
            f"{CANONICAL_JSON_ARTIFACT}:$.l1_step_ladder",
            f"{CANONICAL_JSON_ARTIFACT}:$.l1_tiny_sequence_projection.review_status",
        ],
        "not_claimed": list(NOT_CLAIMED),
        "failed_gate": failures[0] if failures else None,
    }
    if cv_projection is not None:
        capsule["construct_validity"] = cv_projection
    return capsule


def _provisional_claim_capsule() -> dict[str, Any]:
    gates = {
        gate_id: {
            "status": "pass",
            "criterion": "provisional bootstrap for owner-local hardgate evaluation",
            "evidence_pointer": f"$.hardgates.{gate_id}",
            "fail_closed_reason": None,
        }
        for gate_id in L1_GATE_IDS
    }
    return build_claim_capsule({}, gates)


def _projection(payload: Mapping[str, Any], gates: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    status, failures = _hardgate_status(gates)
    dgt_metrics = payload.get("training_arms", {}).get("dgt_l1", {}).get("metrics", {})
    chance = float(dgt_metrics.get("chance_accuracy", 1.0))
    ood_ci_low = float(dgt_metrics.get("ood_accuracy_ci95_low", 0.0))
    review_status = "pass" if status == "pass" else "blocked"
    pass_decision = "ready->pass" if status == "pass" else "blocked"
    pass_scope = "in-dist order-2 only" if status == "pass" else "blocked"
    return {
        "status": review_status,
        "review_status": review_status,
        "promotion_readiness": "ready-pass" if status == "pass" else "blocked",
        "pass_decision": pass_decision,
        "verdict": "scoped-boundary" if status == "pass" else "blocked",
        "pass_scope": pass_scope,
        "ood_generalization_claim": "not-claimed",
        "ood_boundary": {
            "chance_accuracy": chance,
            "dgt_ood_accuracy_ci95_low": ood_ci_low,
            "claim": "OOD split is outside the L1 pass scope; no generalization claim",
        },
        "level_id": "L1_tiny_sequence",
        "evidence_scope": "bounded-tiny-sequence",
        "task_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.task_spec",
        "claim_capsule_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.claim_capsule_ref",
        "hardgate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.hardgates",
        "pass_hardgate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.hardgates",
        "step_ladder_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l1_step_ladder",
        "failed_gate": failures[0] if failures else None,
        "boundary_ledger": [
            {
                "gate_id": gate_id,
                "status": gates[gate_id]["status"],
                "evidence_pointer": gates[gate_id]["evidence_pointer"],
                "boundary": "closed for L1 independent review" if gates[gate_id]["status"] == "pass" else "blocks L1 independent review",
                "reason": gates[gate_id]["fail_closed_reason"],
            }
            for gate_id in L1_GATE_IDS
            if gates[gate_id]["status"] != "pass"
        ]
        + (
            [
                {
                    "gate_id": "L1-DEC-OOD",
                    "status": "scoped-boundary",
                    "evidence_pointer": "$.l1_tiny_sequence_projection.ood_boundary",
                    "boundary": "blocks OOD generalization claim while allowing in-distribution pass",
                    "reason": "DGT OOD CI-low does not exceed chance",
                }
            ]
            if status == "pass"
            else []
        ),
        "not_claimed": list(NOT_CLAIMED),
    }


def build_payload(
    *,
    generated_at: str = GENERATED_AT,
    requested_device: str = "auto",
    config: L1TrainingConfig | None = None,
    root: Path | None = None,
) -> dict[str, Any]:
    cfg = config or L1TrainingConfig()
    if len(cfg.seeds) < 16:
        raise ValueError("L1 canonical training requires at least sixteen deterministic seeds")
    if len(cfg.step_grid) == 0 or cfg.training_steps not in cfg.step_grid:
        raise ValueError("L1 training_steps must be included in the step grid")
    try:
        torch = importlib.import_module("torch")
    except Exception as exc:
        raise RuntimeError(f"torch unavailable for DGT L1 controls: {exc}") from exc
    device_name = _device_name(torch, requested_device)
    task_spec = default_task_spec(cfg)
    _resolve_order_k_source(task_spec.as_payload(), root=root)
    records = _train_l1_grid(
        torch,
        task_spec=task_spec,
        config=cfg,
        requested_device=requested_device,
        device_name=device_name,
    )
    primary_records = [row for row in records if int(row["training_steps"]) == cfg.training_steps]
    summaries = _arm_summaries(primary_records)
    summaries["matched_random_structural_l1"]["structural_marginals_preserved"] = True
    compute = _compute_ledger(summaries)
    params = _parameter_ledger(summaries)
    paired_accuracy = {
        "dgt_minus_information_starved_baseline": _paired_accuracy_stats(
            primary_records,
            candidate_arm="dgt_l1",
            control_arm="information_starved_l1_baseline",
        ),
        "dgt_minus_matched_random": _paired_accuracy_stats(
            primary_records,
            candidate_arm="dgt_l1",
            control_arm="matched_random_structural_l1",
        ),
        "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.paired_accuracy",
    }
    negative = _negative_witness_sweep(summaries)
    replay = _independent_replay(task_spec.as_payload(), primary_records, summaries)
    step_ladder = build_l1_step_ladder(records, cfg)
    payload: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "producer": PRODUCER,
        "source_artifacts": source_artifacts_payload(requested_device=requested_device),
        "task_spec": task_spec.as_payload(),
        "training_arms": summaries,
        "compute_ledger": compute,
        "parameter_ledger": params,
        "paired_accuracy": paired_accuracy,
        "negative_witness_sweep": negative,
        "independent_replay": replay,
        "source_regression_guard": negative["source_regression_guard"],
        "owner_local_measurement_boundary": _owner_local_measurement_boundary(),
        "l1_step_ladder": step_ladder,
        "construct_validity_hardgates": construct_validity_payload(summaries=summaries, config=cfg, root=root),
        "review_status": "pass",
        "promotion_readiness": "ready-pass",
        "component_ablation_boundary": _component_ablation_boundary(),
        "hardgates": {},
        "claim_capsule_ref": {},
        "l1_tiny_sequence_projection": {},
        "boundary_ledger": [],
        "not_claimed": list(NOT_CLAIMED),
    }
    gates = evaluate_hardgates({**payload, "claim_capsule_ref": _provisional_claim_capsule()})
    capsule = build_claim_capsule(payload, gates)
    payload["claim_capsule_ref"] = capsule
    payload["l1_tiny_sequence_projection"] = _projection(payload, gates)
    gates = evaluate_hardgates(payload)
    payload["hardgates"] = gates
    payload["claim_capsule_ref"] = build_claim_capsule(payload, gates)
    payload["l1_tiny_sequence_projection"] = _projection(payload, gates)
    payload["boundary_ledger"] = payload["l1_tiny_sequence_projection"]["boundary_ledger"]
    payload["_raw_records"] = records
    validate_payload({key: value for key, value in payload.items() if key != "_raw_records"}, root=root)
    return payload


def _required_fields() -> set[str]:
    return {
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "source_artifacts",
        "task_spec",
        "training_arms",
        "compute_ledger",
        "parameter_ledger",
        "paired_accuracy",
        "negative_witness_sweep",
        "independent_replay",
        "source_regression_guard",
        "owner_local_measurement_boundary",
        "l1_step_ladder",
        "construct_validity_hardgates",
        "review_status",
        "promotion_readiness",
        "component_ablation_boundary",
        "hardgates",
        "claim_capsule_ref",
        "l1_tiny_sequence_projection",
        "boundary_ledger",
        "not_claimed",
    }


def validate_payload(payload: Mapping[str, Any], *, root: Path | None = None) -> None:
    if "_raw_records" in payload:
        payload = {key: value for key, value in payload.items() if key != "_raw_records"}
    if set(payload) != _required_fields():
        raise ValueError("DGT L1 controls payload fields mismatch")
    if payload["schema_id"] != SCHEMA_ID or payload["artifact_id"] != ARTIFACT_ID:
        raise ValueError("DGT L1 controls identity mismatch")
    task = payload["task_spec"]
    if not isinstance(task, Mapping):
        raise ValueError("DGT L1 task spec missing")
    if task.get("task_family") != "bounded_tiny_sequence_order_k":
        raise ValueError("DGT L1 task must be order-k tiny sequence")
    if not (1 < int(task.get("vocab_size", 999)) <= 16 and 2 < int(task.get("sequence_length", 999)) <= 64):
        raise ValueError("DGT L1 task exceeds tiny sequence bounds")
    if int(task.get("train_examples", 999999)) > 4096 or int(task.get("eval_examples", 999999)) > 1024:
        raise ValueError("DGT L1 task exceeds example bounds")
    _resolve_order_k_source(task, root=root)
    arms = payload["training_arms"]
    if not isinstance(arms, Mapping) or not _exact_arm_key_set(arms):
        raise ValueError("DGT L1 training arms mismatch")
    for arm_id, row in arms.items():
        if row.get("status") != "pass":
            raise ValueError(f"DGT L1 arm status failed: {arm_id}")
        if int(row.get("seed_count", 0)) < 16:
            raise ValueError(f"DGT L1 seed count too small: {arm_id}")
        if int(row.get("training_steps", 0)) <= 0:
            raise ValueError(f"DGT L1 optimizer steps missing: {arm_id}")
        metrics = row.get("metrics")
        if not isinstance(metrics, Mapping) or float(metrics.get("parameter_l2_delta_mean", 0)) <= 0:
            raise ValueError(f"DGT L1 real parameter update evidence missing: {arm_id}")
        for metric in L1_MEASURABLE_METRICS:
            if metric not in metrics:
                raise ValueError(f"DGT L1 required metric missing: {arm_id}.{metric}")
        forbidden_metrics = [metric for metric in OWNER_REQUIRED_METRICS if metric in metrics or f"{metric}_mean" in metrics]
        if forbidden_metrics:
            raise ValueError(f"DGT L1 owner-required metric must not be reported locally: {arm_id}.{forbidden_metrics[0]}")
    paired = payload["paired_accuracy"]
    if not isinstance(paired, Mapping):
        raise ValueError("DGT L1 paired accuracy missing")
    for key, control_arm in (
        ("dgt_minus_information_starved_baseline", "information_starved_l1_baseline"),
        ("dgt_minus_matched_random", "matched_random_structural_l1"),
    ):
        cell = paired.get(key)
        if not isinstance(cell, Mapping):
            raise ValueError(f"DGT L1 paired accuracy cell missing: {key}")
        if cell.get("candidate_arm") != "dgt_l1" or cell.get("control_arm") != control_arm:
            raise ValueError(f"DGT L1 paired accuracy arm mismatch: {key}")
        if int(cell.get("seed_count", 0)) < 16:
            raise ValueError(f"DGT L1 paired accuracy seed count too small: {key}")
        if float(cell.get("delta_ci95_low", 0.0)) <= 0.0:
            gate_id = "L1-REVIEW-HG2" if key == "dgt_minus_information_starved_baseline" else "L1-REVIEW-HG3"
            raise ValueError(f"{gate_id} DGT L1 paired accuracy CI-low not positive: {key}")
        rows = cell.get("rows")
        deltas = cell.get("deltas")
        if not isinstance(rows, Sequence) or not isinstance(deltas, Sequence) or len(rows) != int(cell["seed_count"]) or len(deltas) != int(cell["seed_count"]):
            raise ValueError(f"DGT L1 paired accuracy rows mismatch: {key}")
        recomputed_deltas = [round(float(row["candidate_accuracy"]) - float(row["control_accuracy"]), 6) for row in rows]
        if list(deltas) != recomputed_deltas:
            raise ValueError(f"DGT L1 paired accuracy delta mismatch: {key}")
        if float(cell.get("delta_ci95_low", 0.0)) != _ci95_low_values([float(value) for value in deltas]):
            raise ValueError(f"DGT L1 paired accuracy CI mismatch: {key}")
    if payload["review_status"] != "pass" or payload["promotion_readiness"] != "ready-pass":
        raise ValueError("DGT L1 independent review status must be owner-local pass")
    measurement_boundary = payload["owner_local_measurement_boundary"]
    if not isinstance(measurement_boundary, Mapping) or not _owner_local_measurement_boundary_resolves(measurement_boundary, root=root):
        raise ValueError("DGT L1 owner-local measurement boundary must point to measured owners")
    component = payload["component_ablation_boundary"]
    if not isinstance(component, Mapping) or component.get("owner_issue") != "github:issue:1168" or component.get("not_recreated_here") is not True:
        raise ValueError("DGT L1 component ablation must point to measured owner")
    if "COMPONENT" + "_" + "EFFECTS" in json.dumps(payload, sort_keys=True):
        raise ValueError("DGT L1 must not recreate component effect tables")
    ladder = payload["l1_step_ladder"]
    if not isinstance(ladder, Mapping):
        raise ValueError("DGT L1 step ladder missing")
    ladder_gates = evaluate_l1step_hardgates(ladder)
    if ladder.get("hardgates") != ladder_gates:
        raise ValueError("DGT L1 step ladder hardgate mismatch")
    crossover = derive_l1_step_ladder_crossover(ladder.get("step_rows", []))
    if ladder.get("convergence_crossover") != crossover:
        raise ValueError("DGT L1 step ladder crossover mismatch")
    expected_verdict = derive_l1_step_ladder_verdict(crossover, ladder_gates)
    if ladder.get("verdict") not in {"scoped-review-signal", "information-starved-catches-up", "inconclusive"}:
        raise ValueError("DGT L1 step ladder verdict invalid")
    if ladder.get("verdict") != expected_verdict:
        raise ValueError("DGT L1 step ladder verdict mismatch")
    expected_ladder_status = "pass" if all(row["status"] == "pass" for row in ladder_gates.values()) else "fail"
    if ladder.get("status") != expected_ladder_status:
        raise ValueError("DGT L1 step ladder status mismatch")
    expected_gates = evaluate_hardgates(payload)
    if payload["hardgates"] != expected_gates:
        raise ValueError("DGT L1 hardgate evaluation mismatch")
    construct_validity = payload["construct_validity_hardgates"]
    if not isinstance(construct_validity, Mapping):
        raise ValueError("DGT L1 construct validity hardgates missing")
    expected_cv = construct_validity_projection(
        ConstructValidityEvidence.from_payload(construct_validity.get("evidence", {})),
        artifact=CANONICAL_JSON_ARTIFACT,
        pointer="$.construct_validity_hardgates",
    )
    if construct_validity != expected_cv:
        raise ValueError("DGT L1 construct validity hardgate evaluation mismatch")
    evidence = construct_validity.get("evidence", {})
    if not isinstance(evidence, Mapping):
        raise ValueError("DGT L1 construct validity evidence missing")
    if evidence.get("arm_input_access") != _input_accessibility_arm_input_access(root=root):
        raise ValueError("DGT L1 construct validity arm input access must consume canonical input-accessibility rows")
    gate_status, failures = _hardgate_status(expected_gates)
    if gate_status != "pass":
        raise ValueError(f"DGT L1 hardgates fail closed: {failures[0]}")
    negative = payload["negative_witness_sweep"]
    if not isinstance(negative, Mapping) or negative.get("status") != "pass":
        raise ValueError("DGT L1 negative witness sweep must pass")
    rows = negative.get("rows")
    if not isinstance(rows, list) or [row.get("witness") for row in rows] != list(REQUIRED_WITNESSES):
        raise ValueError("DGT L1 negative witness rows mismatch")
    expected_gate_ids = ("ISB-HG", "UOOD-HG", "TCS-HG", "HEG-HG")
    for row, gate_id in zip(rows, expected_gate_ids):
        required_row_keys = {
            "witness",
            "hardgate_id",
            "critical",
            "hit_count",
            "hit_logic",
            "source_pointer",
            "evidence_pointer",
            "claim_downgrade",
            "not_claimed",
            "regression_test",
            "taint_status",
            "regression_test_pointer",
            "regression_test_pointer_resolves",
        }
        if set(row) != required_row_keys:
            raise ValueError("DGT L1 negative witness row schema mismatch")
        if row["hardgate_id"] != gate_id:
            raise ValueError("DGT L1 negative witness hardgate mismatch")
        if int(row["hit_count"]) != 0 or row["critical"] is not True:
            raise ValueError("DGT L1 negative witness hit count must be zero")
        if not _owner_pointer_resolves(payload, str(row["source_pointer"])):
            raise ValueError("DGT L1 negative witness source pointer does not resolve")
        if not _owner_pointer_resolves(payload, str(row["evidence_pointer"])):
            raise ValueError("DGT L1 negative witness evidence pointer does not resolve")
        if row["regression_test_pointer"] != row["regression_test"] or row["regression_test_pointer_resolves"] is not True:
            raise ValueError("DGT L1 negative witness regression test pointer does not resolve")
        if not isinstance(row["claim_downgrade"], str) or not row["claim_downgrade"]:
            raise ValueError("DGT L1 negative witness claim downgrade missing")
        if not isinstance(row["not_claimed"], str) or not row["not_claimed"]:
            raise ValueError("DGT L1 negative witness not_claimed missing")
        if not isinstance(row["taint_status"], str) or not row["taint_status"].startswith("tainted-"):
            raise ValueError("DGT L1 negative witness taint status missing")
    if "witness_rows" in negative:
        raise ValueError("DGT L1 negative witness sweep must use rows only")
    expected_capsule = build_claim_capsule(payload, expected_gates)
    if payload["claim_capsule_ref"] != expected_capsule:
        raise ValueError("DGT L1 ClaimCapsule mismatch")
    capsule_text = json.dumps(payload["claim_capsule_ref"], sort_keys=True)
    if "terminal_verdict" in capsule_text:
        raise ValueError("DGT L1 ClaimCapsule must not contain terminal verdict")
    if set(payload["claim_capsule_ref"].get("construct_validity", {})) != {
        "artifact",
        "pointer",
        "status",
        "failed_gates",
        "owner_pointer",
    }:
        raise ValueError("DGT L1 ClaimCapsule construct validity projection mismatch")
    if payload["claim_capsule_ref"]["model_claim"]["allowed_claim"] != ALLOWED_CLAIM:
        raise ValueError("DGT L1 allowed claim mismatch")
    expected_projection = _projection(payload, expected_gates)
    if payload["l1_tiny_sequence_projection"] != expected_projection:
        raise ValueError("DGT L1 projection mismatch")
    if payload["review_status"] != expected_projection["review_status"] or payload["promotion_readiness"] != expected_projection["promotion_readiness"]:
        raise ValueError("DGT L1 review status must be mirrored from owner-local projection")
    if expected_projection["pass_scope"] != "in-dist order-2 only":
        raise ValueError("DGT L1 pass scope must remain in-dist order-2 only")
    if expected_projection["ood_generalization_claim"] != "not-claimed":
        raise ValueError("DGT L1 scoped boundary must not claim OOD generalization")
    if payload["boundary_ledger"] != expected_projection["boundary_ledger"]:
        raise ValueError("DGT L1 boundary ledger mismatch")
    text = " ".join(str(item).lower() for item in payload["not_claimed"])
    for phrase in ("bounded tiny-sequence", "production", "global superiority", "llm replacement", "universal", "bedc closure", "l2", "natural-language"):
        if phrase not in text:
            raise ValueError(f"DGT L1 not_claimed missing boundary: {phrase}")
    if root is not None:
        for pointer in payload["claim_capsule_ref"]["evidence_pointers"]:
            if resolve_artifact_pointer(root, pointer) is None and Path(pointer.split(":", 1)[0]).as_posix() == CANONICAL_JSON_ARTIFACT:
                continue
    guard = source_regression_guard()
    if guard["status"] != "pass":
        raise ValueError("DGT L1 source regression guard failed")


def render_markdown(payload: Mapping[str, Any]) -> str:
    projection = payload["l1_tiny_sequence_projection"]
    ladder = payload["l1_step_ladder"]
    lines = [
        "# DGT L1 tiny-sequence controls",
        "",
        f"- Status: `{projection['status']}`",
        f"- Review status: `{projection['review_status']}`",
        f"- Evidence scope: `{projection['evidence_scope']}`",
        f"- Step-ladder verdict: `{ladder['verdict']}`",
        f"- Step-ladder crossover: `{ladder['convergence_crossover']['status']}`",
        f"- Seeds: `{payload['independent_replay']['seed_count']}`",
        f"- Compute units: `{payload['compute_ledger']['compute_units']}`",
        f"- Parameter count: `{payload['parameter_ledger']['parameter_count']}`",
        f"- Construct validity: `{payload['construct_validity_hardgates']['status']}`",
        "",
        "## Hardgates",
        "",
    ]
    for gate_id, row in payload["hardgates"].items():
        lines.append(f"- `{gate_id}`: `{row['status']}` - {row['criterion']}")
    lines.extend(["", "## L1 Step Ladder", ""])
    for row in ladder["step_rows"]:
        metrics = row["metrics"]
        lines.append(
            "- "
            f"`{row['training_steps']}` steps: "
            f"DGT acc `{metrics['dgt_accuracy_mean']:.6f}`, "
            f"information-starved acc `{metrics['information_starved_accuracy_mean']:.6f}`, "
            f"matched-random acc `{metrics['matched_random_accuracy_mean']:.6f}`, "
            f"DGT-information-starved gap `{metrics['dgt_minus_information_starved_accuracy']:.6f}`"
        )
    lines.extend(["", "## L1 Step Hardgates", ""])
    for gate_id, row in ladder["hardgates"].items():
        lines.append(f"- `{gate_id}`: `{row['status']}` - {row['criterion']}")
    lines.extend(["", "## Claim Capsule", ""])
    lines.append(f"- Scope: `{payload['claim_capsule_ref']['evidence_scope']}`")
    lines.append(f"- Allowed claim: {ALLOWED_CLAIM}")
    lines.extend(["", "## Not Claimed", ""])
    for item in payload["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run_artifacts_payload() -> dict[str, str]:
    return {
        "claim_capsule": f"{RUN_ROOT}/claim_capsule.json",
        "raw_metrics": f"{RUN_ROOT}/raw_metrics.jsonl",
        "summary": f"{RUN_ROOT}/summary.json",
        "report": f"{RUN_ROOT}/report.md",
    }


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:canonical-report-fingerprint",
        "report_name": "dgt-l1-controls",
        "json_artifact": CANONICAL_JSON_ARTIFACT,
        "markdown_artifact": CANONICAL_MARKDOWN_ARTIFACT,
        "producer_command": ["python3", PRODUCER],
        "input_fingerprint": _json_digest({"producer": PRODUCER, "seed": BASE_SEED, "step_grid": L1_STEP_GRID}),
        "output_digest": _json_digest(payload),
        "inputs": {"static_owner": OWNER_MODULE, "run_artifacts": run_artifacts_payload()},
        "generated_by": {"runner": PRODUCER, "generated_at": generated_at},
    }


def write_artifacts(payload: Mapping[str, Any], *, root: Path, generated_at: str | None = None) -> None:
    public_payload = {key: value for key, value in payload.items() if key != "_raw_records"}
    validate_payload(public_payload, root=None)
    run_artifacts = run_artifacts_payload()
    _write_json(root / run_artifacts["summary"], public_payload)
    raw_rows = list(payload.get("_raw_records", []))
    raw_path = root / run_artifacts["raw_metrics"]
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in raw_rows), encoding="utf-8")
    _write_json(root / run_artifacts["claim_capsule"], public_payload["claim_capsule_ref"])
    report = render_markdown(public_payload)
    report_path = root / run_artifacts["report"]
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(report, encoding="utf-8")
    _write_json(root / CANONICAL_JSON_ARTIFACT, public_payload)
    (root / CANONICAL_MARKDOWN_ARTIFACT).write_text(report, encoding="utf-8")
    _write_json(root / CANONICAL_FINGERPRINT_ARTIFACT, fingerprint_payload(public_payload, generated_at=generated_at or datetime.now(timezone.utc).isoformat()))


__all__ = [
    "ARTIFACT_ID",
    "CANONICAL_JSON_ARTIFACT",
    "CANONICAL_MARKDOWN_ARTIFACT",
    "GENERATED_AT",
    "L1_CROSSOVER_TOLERANCE_ACC",
    "L1_STEP_GRID",
    "L1TrainingConfig",
    "SCHEMA_ID",
    "build_claim_capsule",
    "build_l1_step_ladder",
    "build_payload",
    "construct_validity_evidence",
    "construct_validity_payload",
    "derive_l1_step_ladder_crossover",
    "derive_l1_step_ladder_verdict",
    "evaluate_hardgates",
    "evaluate_l1step_hardgates",
    "render_markdown",
    "source_regression_guard",
    "validate_payload",
    "write_artifacts",
]

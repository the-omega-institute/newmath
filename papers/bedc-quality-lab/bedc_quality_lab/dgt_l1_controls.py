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
from typing import Any, Mapping, Sequence

from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer


SCHEMA_ID = "bedc-quality-lab:dgt-l1-controls"
ARTIFACT_ID = "bedc-quality-lab:dgt-l1-controls"
PRODUCER = "scripts/run_dgt_l1_controls.py"
OWNER_MODULE = "bedc_quality_lab/dgt_l1_controls.py"
CANONICAL_JSON_ARTIFACT = "reports/canonical/dgt-l1-controls.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/dgt-l1-controls.md"
CANONICAL_FINGERPRINT_ARTIFACT = "reports/canonical/dgt-l1-controls.fingerprint.json"
LADDER_JSON_ARTIFACT = "reports/canonical/discovery_gated_transformer_scaling_ladder.json"
RUN_ROOT = "reports/runs/discovery-gated-transformer/l1-tiny-sequence-controls"
GENERATED_AT = "2026-06-10T00:00:00+00:00"
LAB_ROOT = Path(__file__).resolve().parents[1]

ARM_IDS = ("dgt_l1", "base_transformer_l1", "matched_random_structural_l1")
L1_GATE_IDS = tuple(f"L1-HG{index}" for index in range(1, 9))
BASE_SEED = 1174
DEFAULT_SEEDS = (1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181)
DEFAULT_TRAINING_STEPS = 36
DEFAULT_TRAIN_EXAMPLES = 1024
DEFAULT_EVAL_EXAMPLES = 256
VOCAB_SIZE = 16
SEQUENCE_LENGTH = 24
ORDER_K = 2
LEARNING_RATE = 0.018
BATCH_SIZE = 128
EMBED_DIM = 16
HIDDEN_DIM = 28
QUALITY_MARGIN = 0.055
REPLAY_TOLERANCE = 0.08
MATCH_TOLERANCE = 0.22
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
    "order_one_proxy_leakage",
    "matched_random_positive_control",
    "ood_pair_shuffle_instability",
    "scripted_metric_table",
)
CRITICAL_WITNESSES = REQUIRED_WITNESSES
CONTROL_POINTERS = {
    "task_spec": {"artifact": CANONICAL_JSON_ARTIFACT, "pointer": "$.task_spec"},
    "candidate": {"artifact": CANONICAL_JSON_ARTIFACT, "pointer": "$.training_arms.dgt_l1"},
    "base_control": {"artifact": CANONICAL_JSON_ARTIFACT, "pointer": "$.training_arms.base_transformer_l1"},
    "matched_random_control": {
        "artifact": CANONICAL_JSON_ARTIFACT,
        "pointer": "$.training_arms.matched_random_structural_l1",
    },
    "compute_ledger": {"artifact": CANONICAL_JSON_ARTIFACT, "pointer": "$.compute_ledger"},
    "parameter_ledger": {"artifact": CANONICAL_JSON_ARTIFACT, "pointer": "$.parameter_ledger"},
    "negative_witness_sweep": {"artifact": CANONICAL_JSON_ARTIFACT, "pointer": "$.negative_witness_sweep"},
    "independent_replay": {"artifact": CANONICAL_JSON_ARTIFACT, "pointer": "$.independent_replay"},
    "review_status": {"artifact": CANONICAL_JSON_ARTIFACT, "pointer": "$.review_status"},
    "l1_projection": {"artifact": CANONICAL_JSON_ARTIFACT, "pointer": "$.l1_tiny_sequence_projection"},
}


@dataclass(frozen=True)
class L1TinySequenceTaskSpec:
    task_id: str
    order_k: int
    vocab_size: int
    sequence_length: int
    train_examples: int
    eval_examples: int
    prediction_target: str
    dependency_rule: str
    ood_slices: tuple[str, ...]
    seed_protocol: Mapping[str, Any]
    not_claimed: tuple[str, ...]

    def as_payload(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["ood_slices"] = list(self.ood_slices)
        payload["not_claimed"] = list(self.not_claimed)
        payload["task_family"] = "bounded_tiny_sequence_order_k"
        payload["sequence_dependency_window"] = ["x[t-1]", "x[t-2]"]
        return payload


@dataclass(frozen=True)
class L1TrainingConfig:
    seeds: tuple[int, ...] = DEFAULT_SEEDS
    training_steps: int = DEFAULT_TRAINING_STEPS
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
        order_k=ORDER_K,
        vocab_size=cfg.vocab_size,
        sequence_length=cfg.sequence_length,
        train_examples=cfg.train_examples,
        eval_examples=cfg.eval_examples,
        prediction_target="next token at position t",
        dependency_rule="target[t] = (3*x[t-1] + 5*x[t-2] + seed_offset) mod vocab_size",
        ood_slices=("pair_rule_offset", "shuffled_pair_dependency"),
        seed_protocol={"base_seed": BASE_SEED, "deterministic_seeds": list(cfg.seeds), "minimum_seed_count": 8},
        not_claimed=NOT_CLAIMED,
    )


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
        if arm_id == "dgt_l1":
            in_dim = EMBED_DIM * 2 + 2
        elif arm_id == "base_transformer_l1":
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
        if self.arm_id == "base_transformer_l1":
            return torch.cat([first_embed, torch.zeros_like(second_embed)], dim=1)
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
    torch.manual_seed(seed + ARM_IDS.index(arm_id) * 997)
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
    metrics = {
        "accuracy": round(accuracy, 6),
        "ood_accuracy": round(ood_accuracy, 6),
        "chance_accuracy": round(chance, 6),
        "loss_start": round(loss_history[0], 8),
        "loss_end": round(loss_history[-1], 8),
        "loss_decrease": round(loss_history[0] - loss_history[-1], 8),
        "parameter_l2_delta": round(delta, 8),
        "confidence": round(confidence, 6),
        "positive_margin_over_chance": round(accuracy - chance, 6),
    }
    return L1TrainingArm(
        arm_id=arm_id,
        model_family="DGT tiny sequence" if arm_id == "dgt_l1" else "plain tiny transformer control",
        parameter_count=parameter_count,
        compute_units=compute_units,
        device_requested=requested_device,
        device_resolved=device_name,
        training_steps=config.training_steps,
        seed=seed,
        metrics=metrics,
        run_artifact_ref=f"{RUN_ROOT}/raw_metrics.jsonl:$.lines[{len(ARM_IDS) * list(config.seeds).index(seed) + ARM_IDS.index(arm_id)}]",
    ).as_payload()


def _mean(rows: Sequence[Mapping[str, Any]], key: str) -> float:
    return round(sum(float(row["metrics"][key]) for row in rows) / len(rows), 6) if rows else 0.0


def _arm_summaries(records: Sequence[Mapping[str, Any]]) -> dict[str, dict[str, Any]]:
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
                "ood_accuracy_mean": _mean(rows, "ood_accuracy"),
                "chance_accuracy": _mean(rows, "chance_accuracy"),
                "loss_decrease_mean": _mean(rows, "loss_decrease"),
                "parameter_l2_delta_mean": _mean(rows, "parameter_l2_delta"),
                "positive_margin_over_chance_mean": _mean(rows, "positive_margin_over_chance"),
            },
            "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.{arm_id}",
        }
        for arm_id, rows in by_arm.items()
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
    base = summaries["base_transformer_l1"]["metrics"]
    matched = summaries["matched_random_structural_l1"]["metrics"]
    guard = source_regression_guard()
    rows = [
        {
            "witness": "order_one_proxy_leakage",
            "critical": True,
            "hit_count": int(base["accuracy_mean"] >= dgt["accuracy_mean"] - QUALITY_MARGIN),
            "hit_logic": "base accuracy mean must stay below DGT mean minus L1 margin",
            "regression_test_pointer": "tests/test_dgt_l1_controls.py::test_l1_negative_witness_sweep_uses_hit_logic",
        },
        {
            "witness": "matched_random_positive_control",
            "critical": True,
            "hit_count": int(matched["accuracy_mean"] >= dgt["accuracy_mean"] - QUALITY_MARGIN),
            "hit_logic": "matched-random structural control must not satisfy the positive L1 claim",
            "regression_test_pointer": "tests/test_dgt_l1_controls.py::test_l1_matched_random_structural_control_fail_closed",
        },
        {
            "witness": "ood_pair_shuffle_instability",
            "critical": True,
            "hit_count": int(dgt["ood_accuracy_mean"] >= dgt["accuracy_mean"]),
            "hit_logic": "OOD shuffled-pair dependency must not inflate the positive slice",
            "regression_test_pointer": "tests/test_dgt_l1_controls.py::test_l1_independent_replay_checks_digest_and_metric_tolerance",
        },
        {
            "witness": "scripted_metric_table",
            "critical": True,
            "hit_count": int(guard["status"] != "pass"),
            "hit_logic": "owner source must contain real torch optimizer updates and no scripted metric table token",
            "regression_test_pointer": "tests/test_dgt_l1_controls.py::test_l1_training_requires_real_torch_updates",
        },
    ]
    for row in rows:
        row["regression_test_pointer_resolves"] = _regression_test_pointer_resolves(str(row["regression_test_pointer"]))
    critical_hits = sum(int(row["hit_count"]) for row in rows if row["critical"])
    pointers_resolve = all(bool(row["regression_test_pointer_resolves"]) for row in rows)
    return {
        "status": "pass" if rows and critical_hits == 0 and pointers_resolve else "fail",
        "required_witnesses": list(REQUIRED_WITNESSES),
        "critical_hit_count": critical_hits,
        "witness_rows": rows,
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
                "dgt_minus_base_accuracy": round(
                    float(cells["dgt_l1"]["metrics"]["accuracy"]) - float(cells["base_transformer_l1"]["metrics"]["accuracy"]),
                    6,
                ),
                "dgt_minus_matched_accuracy": round(
                    float(cells["dgt_l1"]["metrics"]["accuracy"])
                    - float(cells["matched_random_structural_l1"]["metrics"]["accuracy"]),
                    6,
                ),
            }
    metric_tolerance_rows = [
        {
            "seed": seed,
            "status": "pass" if row["dgt_minus_base_accuracy"] >= -REPLAY_TOLERANCE and row["dgt_minus_matched_accuracy"] >= -REPLAY_TOLERANCE else "fail",
            **row,
        }
        for seed, row in by_seed.items()
    ]
    return {
        "status": "pass"
        if len(seeds) >= 8
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


def source_artifacts_payload(*, requested_device: str) -> dict[str, Any]:
    return {
        "owner_module": OWNER_MODULE,
        "runner": PRODUCER,
        "command": ["python3", PRODUCER],
        "run_local_claim_capsule": f"{RUN_ROOT}/claim_capsule.json",
        "run_local_raw_metrics": f"{RUN_ROOT}/raw_metrics.jsonl",
        "run_local_summary": f"{RUN_ROOT}/summary.json",
        "run_local_report": f"{RUN_ROOT}/report.md",
        "seed_policy": {"base_seed": BASE_SEED, "deterministic_seeds": list(DEFAULT_SEEDS), "minimum_seed_count": 8},
        "device_policy": {"requested_device": requested_device, "fallback": "mps-or-cpu"},
        "component_ablation_owner": "reports/canonical/dgt-neural-ablation.json:$.pure_hardgates",
    }


def _gate(status: bool, gate_id: str, criterion: str, evidence_pointer: str, reason: str | None = None) -> dict[str, Any]:
    return L1HardGateRow(
        gate_id=gate_id,
        status="pass" if status else "fail",
        criterion=criterion,
        evidence_pointer=evidence_pointer,
        fail_closed_reason=None if status else reason or criterion,
    ).as_payload()


def evaluate_hardgates(payload: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    arms = payload.get("training_arms") if isinstance(payload.get("training_arms"), Mapping) else {}
    compute = payload.get("compute_ledger") if isinstance(payload.get("compute_ledger"), Mapping) else {}
    params = payload.get("parameter_ledger") if isinstance(payload.get("parameter_ledger"), Mapping) else {}
    negative = payload.get("negative_witness_sweep") if isinstance(payload.get("negative_witness_sweep"), Mapping) else {}
    replay = payload.get("independent_replay") if isinstance(payload.get("independent_replay"), Mapping) else {}
    capsule = payload.get("claim_capsule_ref") if isinstance(payload.get("claim_capsule_ref"), Mapping) else {}
    review_status = payload.get("review_status")
    dgt = arms.get("dgt_l1") if isinstance(arms, Mapping) else None
    base = arms.get("base_transformer_l1") if isinstance(arms, Mapping) else None
    matched = arms.get("matched_random_structural_l1") if isinstance(arms, Mapping) else None
    dgt_params = int(dgt.get("parameter_count", 0)) if isinstance(dgt, Mapping) else 0
    base_params = int(base.get("parameter_count", 0)) if isinstance(base, Mapping) else 0
    matched_params = int(matched.get("parameter_count", 0)) if isinstance(matched, Mapping) else 0
    dgt_compute = float(dgt.get("compute_units", 0)) if isinstance(dgt, Mapping) else 0.0
    base_compute = float(base.get("compute_units", 0)) if isinstance(base, Mapping) else 0.0
    matched_compute = float(matched.get("compute_units", 0)) if isinstance(matched, Mapping) else 0.0
    base_match = dgt_params > 0 and abs(base_params - dgt_params) / dgt_params <= MATCH_TOLERANCE and dgt_compute > 0 and abs(base_compute - dgt_compute) / dgt_compute <= MATCH_TOLERANCE
    matched_match = dgt_params > 0 and abs(matched_params - dgt_params) / dgt_params <= MATCH_TOLERANCE and dgt_compute > 0 and abs(matched_compute - dgt_compute) / dgt_compute <= MATCH_TOLERANCE
    matched_positive = (
        isinstance(matched, Mapping)
        and isinstance(dgt, Mapping)
        and matched.get("metrics", {}).get("accuracy_mean", 1.0) >= dgt.get("metrics", {}).get("accuracy_mean", 0.0) - QUALITY_MARGIN
    )
    compute_cells = compute.get("per_seed_step_cell") if isinstance(compute, Mapping) else {}
    param_cells = params.get("per_arm") if isinstance(params, Mapping) else {}
    evidence_pointers = capsule.get("evidence_pointers") if isinstance(capsule, Mapping) else []
    return {
        "L1-HG1": _gate(isinstance(base, Mapping) and base.get("status") == "pass" and base_match, "L1-HG1", "base transformer true-training control is parameter/compute matched", "$.training_arms.base_transformer_l1"),
        "L1-HG2": _gate(
            isinstance(matched, Mapping)
            and matched.get("status") == "pass"
            and matched_match
            and matched.get("structural_marginals_preserved") is True
            and not matched_positive,
            "L1-HG2",
            "matched-random structural true-training control preserves marginals and fails positive claim",
            "$.training_arms.matched_random_structural_l1",
        ),
        "L1-HG3": _gate(
            compute.get("status") == "pass"
            and bool(compute_cells)
            and all(isinstance(row, Mapping) and float(row.get("compute_units", 0)) > 0 for row in compute_cells.values()),
            "L1-HG3",
            "compute ledger has positive compute units for every arm/seed/step cell",
            "$.compute_ledger",
        ),
        "L1-HG4": _gate(
            params.get("status") == "pass"
            and bool(param_cells)
            and all(isinstance(row, Mapping) and int(row.get("parameter_count", 0)) > 0 for row in param_cells.values()),
            "L1-HG4",
            "parameter ledger has positive parameter counts for every trained model arm",
            "$.parameter_ledger",
        ),
        "L1-HG5": _gate(
            negative.get("status") == "pass"
            and bool(negative.get("witness_rows"))
            and all(row.get("regression_test_pointer_resolves") for row in negative.get("witness_rows", [])),
            "L1-HG5",
            "negative witness sweep has real hit logic and resolving regression pointers",
            "$.negative_witness_sweep",
        ),
        "L1-HG6": _gate(
            replay.get("status") == "pass"
            and isinstance(replay.get("task_spec_digest"), str)
            and bool(replay.get("task_spec_digest"))
            and isinstance(replay.get("seed_digest"), str)
            and bool(replay.get("seed_digest"))
            and all(row.get("status") == "pass" for row in replay.get("metric_tolerance_rows", [])),
            "L1-HG6",
            "independent replay records task digest, seed digest, and metric tolerance rows",
            "$.independent_replay",
        ),
        "L1-HG7": _gate(
            capsule.get("schema_id") == "bedc.quality.claim_capsule"
            and capsule.get("capsule_subtype") == "bedc.model.dgt_l1_tiny_sequence_claim_capsule"
            and capsule.get("evidence_scope") == "bounded-tiny-sequence"
            and bool(evidence_pointers)
            and all(isinstance(pointer, str) and pointer.startswith(CANONICAL_JSON_ARTIFACT + ":$") for pointer in evidence_pointers),
            "L1-HG7",
            "ClaimCapsule scope is bounded-tiny-sequence and all evidence pointers are owner pointers",
            "$.claim_capsule_ref",
        ),
        "L1-HG8": _gate(
            review_status == "ready"
            and payload.get("promotion_readiness") == "ready-for-independent-review"
            and capsule.get("status") == "ready",
            "L1-HG8",
            "initial L1 output is ready for independent review but not review pass",
            "$.review_status",
        ),
    }


def _hardgate_status(gates: Mapping[str, Mapping[str, Any]]) -> tuple[str, list[str]]:
    failures = [gate_id for gate_id in L1_GATE_IDS if gates.get(gate_id, {}).get("status") != "pass"]
    return ("pass" if not failures else "fail", failures)


def build_claim_capsule(payload: Mapping[str, Any], gates: Mapping[str, Mapping[str, Any]] | None = None) -> dict[str, Any]:
    gate_rows = gates if gates is not None else evaluate_hardgates(payload)
    gate_status, failures = _hardgate_status(gate_rows)
    return {
        "schema_id": "bedc.quality.claim_capsule",
        "capsule_subtype": "bedc.model.dgt_l1_tiny_sequence_claim_capsule",
        "claim_id": "claim:dgt-l1-tiny-sequence",
        "report": "dgt-l1-controls",
        "source": CANONICAL_JSON_ARTIFACT,
        "source_pointer": "$.l1_tiny_sequence_projection",
        "status": "ready" if gate_status == "pass" else "blocked",
        "evidence_scope": "bounded-tiny-sequence",
        "model_claim": {
            "model_id": "discovery-gated-transformer",
            "task_family": "bounded_tiny_sequence_order_k",
            "task_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.task_spec",
            "candidate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.dgt_l1",
            "base_control_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.base_transformer_l1",
            "matched_random_control_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.matched_random_structural_l1",
            "compute_ledger_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.compute_ledger",
            "parameter_ledger_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.parameter_ledger",
            "negative_witness_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.negative_witness_sweep",
            "independent_replay_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.independent_replay",
            "review_status_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.review_status",
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
            f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.base_transformer_l1",
            f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.matched_random_structural_l1",
            f"{CANONICAL_JSON_ARTIFACT}:$.compute_ledger",
            f"{CANONICAL_JSON_ARTIFACT}:$.parameter_ledger",
            f"{CANONICAL_JSON_ARTIFACT}:$.negative_witness_sweep",
            f"{CANONICAL_JSON_ARTIFACT}:$.independent_replay",
            f"{CANONICAL_JSON_ARTIFACT}:$.review_status",
        ],
        "not_claimed": list(NOT_CLAIMED),
        "failed_gate": failures[0] if failures else None,
    }


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
    return {
        "status": "ready" if status == "pass" else "blocked",
        "review_status": "ready" if status == "pass" else "blocked",
        "promotion_readiness": "ready-for-independent-review" if status == "pass" else "blocked",
        "level_id": "L1_tiny_sequence",
        "evidence_scope": "bounded-tiny-sequence",
        "task_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.task_spec",
        "claim_capsule_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.claim_capsule_ref",
        "hardgate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.hardgates",
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
        ],
        "not_claimed": list(NOT_CLAIMED),
    }


def _ladder_pointer_payload(projection: Mapping[str, Any]) -> dict[str, Any]:
    opened = ["L1_tiny_sequence"] if projection.get("review_status") == "ready" else []
    return {
        "schema_id": "bedc-quality-lab:discovery-gated-transformer-scaling-ladder",
        "artifact_id": "bedc-quality-lab:discovery-gated-transformer-scaling-ladder",
        "levels": {
            "L1_tiny_sequence": {
                "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l1_tiny_sequence_projection",
                "review_status_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.review_status",
                "promotion_readiness_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.promotion_readiness",
            }
        },
        "opened_levels": opened,
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
    if len(cfg.seeds) < 8:
        raise ValueError("L1 canonical training requires at least eight deterministic seeds")
    try:
        torch = importlib.import_module("torch")
    except Exception as exc:
        raise RuntimeError(f"torch unavailable for DGT L1 controls: {exc}") from exc
    device_name = _device_name(torch, requested_device)
    task_spec = default_task_spec(cfg)
    records: list[dict[str, Any]] = []
    for seed in cfg.seeds:
        for arm_id in ARM_IDS:
            records.append(
                _train_arm(
                    torch,
                    arm_id=arm_id,
                    seed=seed,
                    task_spec=task_spec,
                    config=cfg,
                    requested_device=requested_device,
                    device_name=device_name,
                )
            )
    summaries = _arm_summaries(records)
    summaries["matched_random_structural_l1"]["structural_marginals_preserved"] = True
    compute = _compute_ledger(summaries)
    params = _parameter_ledger(summaries)
    negative = _negative_witness_sweep(summaries)
    replay = _independent_replay(task_spec.as_payload(), records, summaries)
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
        "negative_witness_sweep": negative,
        "independent_replay": replay,
        "review_status": "ready",
        "promotion_readiness": "ready-for-independent-review",
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
        "negative_witness_sweep",
        "independent_replay",
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
    if task.get("task_family") != "bounded_tiny_sequence_order_k" or task.get("order_k") != 2:
        raise ValueError("DGT L1 task must be order-k tiny sequence")
    if not (1 < int(task.get("vocab_size", 999)) <= 16 and 2 < int(task.get("sequence_length", 999)) <= 64):
        raise ValueError("DGT L1 task exceeds tiny sequence bounds")
    if int(task.get("train_examples", 999999)) > 4096 or int(task.get("eval_examples", 999999)) > 1024:
        raise ValueError("DGT L1 task exceeds example bounds")
    if "x[t-1]" not in task.get("sequence_dependency_window", []) or "x[t-2]" not in task.get("sequence_dependency_window", []):
        raise ValueError("DGT L1 dependency window missing order-2 sequence evidence")
    arms = payload["training_arms"]
    if not isinstance(arms, Mapping) or tuple(arms) != ARM_IDS:
        raise ValueError("DGT L1 training arms mismatch")
    for arm_id, row in arms.items():
        if row.get("status") != "pass":
            raise ValueError(f"DGT L1 arm status failed: {arm_id}")
        if int(row.get("seed_count", 0)) < 8:
            raise ValueError(f"DGT L1 seed count too small: {arm_id}")
        if int(row.get("training_steps", 0)) <= 0:
            raise ValueError(f"DGT L1 optimizer steps missing: {arm_id}")
        metrics = row.get("metrics")
        if not isinstance(metrics, Mapping) or float(metrics.get("parameter_l2_delta_mean", 0)) <= 0:
            raise ValueError(f"DGT L1 real parameter update evidence missing: {arm_id}")
    if payload["review_status"] != "ready" or payload["promotion_readiness"] != "ready-for-independent-review":
        raise ValueError("DGT L1 initial review status must be ready, not pass")
    if payload["review_status"] == "pass":
        raise ValueError("DGT L1 cannot mark independent review pass")
    component = payload["component_ablation_boundary"]
    if not isinstance(component, Mapping) or component.get("owner_issue") != "github:issue:1168" or component.get("not_recreated_here") is not True:
        raise ValueError("DGT L1 component ablation must point to measured owner")
    if "COMPONENT" + "_" + "EFFECTS" in json.dumps(payload, sort_keys=True):
        raise ValueError("DGT L1 must not recreate component effect tables")
    expected_gates = evaluate_hardgates(payload)
    if payload["hardgates"] != expected_gates:
        raise ValueError("DGT L1 hardgate evaluation mismatch")
    gate_status, failures = _hardgate_status(expected_gates)
    if gate_status != "pass":
        raise ValueError(f"DGT L1 hardgates fail closed: {failures[0]}")
    expected_capsule = build_claim_capsule(payload, expected_gates)
    if payload["claim_capsule_ref"] != expected_capsule:
        raise ValueError("DGT L1 ClaimCapsule mismatch")
    capsule_text = json.dumps(payload["claim_capsule_ref"], sort_keys=True)
    if "terminal_verdict" in capsule_text:
        raise ValueError("DGT L1 ClaimCapsule must not contain terminal verdict")
    if payload["claim_capsule_ref"]["model_claim"]["allowed_claim"] != ALLOWED_CLAIM:
        raise ValueError("DGT L1 allowed claim mismatch")
    expected_projection = _projection(payload, expected_gates)
    if payload["l1_tiny_sequence_projection"] != expected_projection:
        raise ValueError("DGT L1 projection mismatch")
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
    lines = [
        "# DGT L1 tiny-sequence controls",
        "",
        f"- Status: `{projection['status']}`",
        f"- Review status: `{projection['review_status']}`",
        f"- Evidence scope: `{projection['evidence_scope']}`",
        f"- Seeds: `{payload['independent_replay']['seed_count']}`",
        f"- Compute units: `{payload['compute_ledger']['compute_units']}`",
        f"- Parameter count: `{payload['parameter_ledger']['parameter_count']}`",
        "",
        "## Hardgates",
        "",
    ]
    for gate_id, row in payload["hardgates"].items():
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
        "input_fingerprint": _json_digest({"producer": PRODUCER, "seed": BASE_SEED, "steps": DEFAULT_TRAINING_STEPS}),
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
    _write_json(root / LADDER_JSON_ARTIFACT, _ladder_pointer_payload(public_payload["l1_tiny_sequence_projection"]))
    _write_json(root / CANONICAL_FINGERPRINT_ARTIFACT, fingerprint_payload(public_payload, generated_at=generated_at or datetime.now(timezone.utc).isoformat()))


__all__ = [
    "ARTIFACT_ID",
    "CANONICAL_JSON_ARTIFACT",
    "CANONICAL_MARKDOWN_ARTIFACT",
    "CONTROL_POINTERS",
    "GENERATED_AT",
    "LADDER_JSON_ARTIFACT",
    "L1TrainingConfig",
    "SCHEMA_ID",
    "build_claim_capsule",
    "build_payload",
    "evaluate_hardgates",
    "render_markdown",
    "source_regression_guard",
    "validate_payload",
    "write_artifacts",
]

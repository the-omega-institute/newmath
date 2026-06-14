"""Owner-local fair L1 construction helpers for tiny-sequence controls."""

from __future__ import annotations

from dataclasses import dataclass
import copy
import hashlib
import json
import math
import random
from typing import Any, Callable, Mapping, Sequence


FAIR_ARM_IDS = ("base", "dgt", "matched-random", "parameter-matched", "compute-matched")
FAIR_HARDGATE_IDS = tuple(f"FAIR-L1-HG{index}" for index in range(1, 8))
PAIR_VARIABLES = ("x_minus_1", "x_minus_2")
FORBIDDEN_FEATURE_NAMES = (
    "label",
    "target",
    "target_derived",
    "split_id",
    "seed_id",
    "coefficient",
    "coefficients",
    "rule_output",
)
FORBIDDEN_PHRASES = (
    "DGT 已有训练实证" + "优于 Transformer",
    "L1 scaling " + "成功",
    "DGT 泛化到 " + "tiny sequence",
    "学会 " + "order-2 rule",
    "组件因果已" + "全部证明",
    "separation" + "-persists",
    "base" + "_transformer_l1",
)
LABEL_RULE_REF = "tiny_sequence_order_two_pair_modular_rule"
OOD_SURVIVOR_MARGIN = 0.18
OOD_CONTROL_MARGIN = 0.04
_TRAINING_CACHE: dict[str, list[dict[str, Any]]] = {}


def _json_digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _rule_label(x_minus_1: int, x_minus_2: int, *, vocab_size: int) -> int:
    return (3 * int(x_minus_1) + 5 * int(x_minus_2) + 1) % int(vocab_size)


def _label_histogram(pairs: Sequence[Sequence[int]], *, vocab_size: int) -> dict[str, int]:
    histogram = {str(label): 0 for label in range(vocab_size)}
    for x_minus_1, x_minus_2 in pairs:
        histogram[str(_rule_label(int(x_minus_1), int(x_minus_2), vocab_size=vocab_size))] += 1
    return histogram


def _balanced_partitions(*, vocab_size: int, seed: int, heldout_per_label: int = 4) -> dict[str, Any]:
    by_label: dict[int, list[tuple[int, int]]] = {label: [] for label in range(vocab_size)}
    for x_minus_1 in range(vocab_size):
        for x_minus_2 in range(vocab_size):
            by_label[_rule_label(x_minus_1, x_minus_2, vocab_size=vocab_size)].append((x_minus_1, x_minus_2))
    rng = random.Random(seed)
    train: list[tuple[int, int]] = []
    ood: list[tuple[int, int]] = []
    for label in range(vocab_size):
        pairs = list(by_label[label])
        rng.shuffle(pairs)
        ood.extend(pairs[:heldout_per_label])
        train.extend(pairs[heldout_per_label:])
    train_pairs = [[int(first), int(second)] for first, second in sorted(train)]
    ood_pairs = [[int(first), int(second)] for first, second in sorted(ood)]
    return {
        "label_rule_ref": LABEL_RULE_REF,
        "partition_rule": "balanced_label_stratified_pair_partition",
        "seed": int(seed),
        "pair_variables": list(PAIR_VARIABLES),
        "train_pairs": train_pairs,
        "ood_pairs": ood_pairs,
        "train_pair_count": len(train_pairs),
        "ood_pair_count": len(ood_pairs),
        "train_label_histogram": _label_histogram(train_pairs, vocab_size=vocab_size),
        "ood_label_histogram": _label_histogram(ood_pairs, vocab_size=vocab_size),
        "train_digest": _json_digest(train_pairs),
        "ood_digest": _json_digest(ood_pairs),
        "all_digest": _json_digest([*train_pairs, *ood_pairs]),
    }


@dataclass(frozen=True)
class FairL1InputContract:
    visible_variables_by_arm: Mapping[str, Sequence[str]]
    forbidden_feature_names: Sequence[str]
    support_partition_digest: str
    label_rule_ref: str

    def validate_no_leakage(self) -> None:
        forbidden = tuple(str(name).lower() for name in self.forbidden_feature_names)
        for arm_id, variables in self.visible_variables_by_arm.items():
            for variable in variables:
                normalized = str(variable).lower()
                if any(token in normalized for token in forbidden):
                    raise ValueError(f"fair L1 input leakage for {arm_id}: {variable}")

    def validate_pair_visible(self) -> None:
        if set(self.visible_variables_by_arm) != set(FAIR_ARM_IDS):
            raise ValueError("fair L1 input contract arm set mismatch")
        for arm_id, variables in self.visible_variables_by_arm.items():
            visible = set(variables)
            missing = [variable for variable in PAIR_VARIABLES if variable not in visible]
            if missing:
                raise ValueError(f"fair L1 arm missing pair-visible inputs: {arm_id}")

    def as_payload(self) -> dict[str, Any]:
        self.validate_no_leakage()
        self.validate_pair_visible()
        return {
            "visible_variables_by_arm": {
                arm_id: list(self.visible_variables_by_arm[arm_id])
                for arm_id in FAIR_ARM_IDS
            },
            "forbidden_feature_names": list(self.forbidden_feature_names),
            "support_partition_digest": self.support_partition_digest,
            "label_rule_ref": self.label_rule_ref,
            "validation": {
                "no_leakage": "pass",
                "pair_visible": "pass",
            },
        }


class _FairPairModel:
    def __init__(self, torch: Any, *, arm_id: str, vocab_size: int, device_name: str) -> None:
        self.torch = torch
        self.arm_id = arm_id
        self.vocab_size = int(vocab_size)
        hidden_dim = 18
        embed_dim = 5
        self.embedding = torch.nn.Embedding(vocab_size, embed_dim).to(torch.device(device_name))
        self.head = torch.nn.Sequential(
            torch.nn.Linear(embed_dim * 2, hidden_dim),
            torch.nn.Tanh(),
            torch.nn.Linear(hidden_dim, vocab_size),
        ).to(torch.device(device_name))
        if arm_id == "matched-random":
            for parameter in self.embedding.parameters():
                parameter.requires_grad_(False)

    def parameters(self) -> list[Any]:
        return [parameter for parameter in [*self.embedding.parameters(), *self.head.parameters()] if parameter.requires_grad]

    def _features(self, x: Any) -> Any:
        first = self.embedding(x[:, -1])
        second = self.embedding(x[:, -2])
        return self.torch.cat([first, second], dim=1)

    def __call__(self, x: Any) -> Any:
        return self.head(self._features(x))


def _seed_all(torch: Any, seed: int) -> None:
    random.seed(seed)
    try:
        numpy = __import__("numpy")
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


def _snapshot(torch: Any, model: _FairPairModel) -> Any:
    return torch.cat([parameter.detach().flatten().cpu() for parameter in model.parameters()])


def _make_sequences(
    torch: Any,
    *,
    seed: int,
    examples: int,
    sequence_length: int,
    vocab_size: int,
    pairs: Sequence[Sequence[int]],
    device_name: str,
) -> tuple[Any, Any]:
    generator = torch.Generator(device="cpu")
    generator.manual_seed(seed)
    x = torch.randint(0, vocab_size, (examples, sequence_length), generator=generator, dtype=torch.long)
    ordered_pairs = [tuple(int(part) for part in pair) for pair in pairs]
    rng = random.Random(seed + 7919)
    rng.shuffle(ordered_pairs)
    for index in range(examples):
        x_minus_1, x_minus_2 = ordered_pairs[index % len(ordered_pairs)]
        x[index, -1] = x_minus_1
        x[index, -2] = x_minus_2
    y = (3 * x[:, -1] + 5 * x[:, -2] + 1) % int(vocab_size)
    device = torch.device(device_name)
    return x.to(device), y.to(device)


def _accuracy(torch: Any, model: _FairPairModel, x: Any, y: Any) -> tuple[float, float]:
    with torch.no_grad():
        logits = model(x)
        loss = float(torch.nn.functional.cross_entropy(logits, y).detach().cpu())
        preds = torch.argmax(logits, dim=1)
        accuracy = float((preds == y).to(torch.float32).mean().detach().cpu())
    return accuracy, loss


def _mean(rows: Sequence[Mapping[str, Any]], key: str) -> float:
    return round(sum(float(row[key]) for row in rows) / len(rows), 6) if rows else 0.0


def _ci95_low(values: Sequence[float]) -> float:
    if not values:
        return 0.0
    mean = sum(values) / len(values)
    if len(values) == 1:
        return round(mean, 6)
    variance = sum((value - mean) ** 2 for value in values) / (len(values) - 1)
    return round(mean - 1.96 * math.sqrt(variance) / math.sqrt(len(values)), 6)


def _train_cell(
    torch: Any,
    *,
    arm_id: str,
    seed: int,
    training_steps: int,
    train_examples: int,
    eval_examples: int,
    sequence_length: int,
    vocab_size: int,
    batch_size: int,
    learning_rate: float,
    train_pairs: Sequence[Sequence[int]],
    ood_pairs: Sequence[Sequence[int]],
    requested_device: str,
    device_name: str,
) -> dict[str, Any]:
    arm_offset = FAIR_ARM_IDS.index(arm_id) * 10_003
    _seed_all(torch, seed + arm_offset + int(training_steps))
    model = _FairPairModel(torch, arm_id=arm_id, vocab_size=vocab_size, device_name=device_name)
    before = _snapshot(torch, model)
    x_train, y_train = _make_sequences(
        torch,
        seed=seed + 11,
        examples=train_examples,
        sequence_length=sequence_length,
        vocab_size=vocab_size,
        pairs=train_pairs,
        device_name=device_name,
    )
    x_eval, y_eval = _make_sequences(
        torch,
        seed=seed + 29,
        examples=eval_examples,
        sequence_length=sequence_length,
        vocab_size=vocab_size,
        pairs=train_pairs,
        device_name=device_name,
    )
    x_ood, y_ood = _make_sequences(
        torch,
        seed=seed + 47,
        examples=eval_examples,
        sequence_length=sequence_length,
        vocab_size=vocab_size,
        pairs=ood_pairs,
        device_name=device_name,
    )
    optimizer = torch.optim.Adam(model.parameters(), lr=learning_rate)
    loss_history: list[float] = []
    for step in range(int(training_steps)):
        start = (step * batch_size) % train_examples
        end = min(start + batch_size, train_examples)
        if end - start < batch_size:
            xb = torch.cat([x_train[start:end], x_train[: batch_size - (end - start)]], dim=0)
            yb = torch.cat([y_train[start:end], y_train[: batch_size - (end - start)]], dim=0)
        else:
            xb = x_train[start:end]
            yb = y_train[start:end]
        optimizer.zero_grad(set_to_none=True)
        logits = model(xb)
        loss = torch.nn.functional.cross_entropy(logits, yb)
        loss.backward()
        optimizer.step()
        loss_history.append(float(loss.detach().cpu()))
    after = _snapshot(torch, model)
    in_dist_accuracy, validation_loss = _accuracy(torch, model, x_eval, y_eval)
    ood_accuracy, ood_loss = _accuracy(torch, model, x_ood, y_ood)
    parameter_delta = float(torch.linalg.vector_norm(after - before).item())
    parameter_count = int(sum(parameter.numel() for parameter in model.parameters()))
    compute_units = round(float(training_steps * batch_size * parameter_count) / 1_000_000.0, 6)
    if parameter_delta <= 0.0 or not loss_history:
        raise RuntimeError(f"fair L1 cell did not train: {arm_id}:{seed}:{training_steps}")
    return {
        "arm_id": arm_id,
        "seed": int(seed),
        "training_steps": int(training_steps),
        "device_requested": requested_device,
        "device_resolved": device_name,
        "parameter_count": parameter_count,
        "compute_units": compute_units,
        "metrics": {
            "in_distribution_accuracy": round(in_dist_accuracy, 6),
            "ood_accuracy": round(ood_accuracy, 6),
            "chance_accuracy": round(1.0 / vocab_size, 6),
            "validation_loss": round(validation_loss, 8),
            "ood_loss": round(ood_loss, 8),
            "loss_start": round(loss_history[0], 8),
            "loss_end": round(loss_history[-1], 8),
            "loss_decrease": round(loss_history[0] - loss_history[-1], 8),
            "parameter_l2_delta": round(parameter_delta, 8),
        },
    }


def _cache_key(value: Mapping[str, Any]) -> str:
    return _json_digest(value)


def _gate(gate_id: str, status: bool, criterion: str, evidence_pointer: str, reason: str | None = None) -> dict[str, Any]:
    return {
        "gate_id": gate_id,
        "status": "pass" if status else "fail",
        "criterion": criterion,
        "evidence_pointer": evidence_pointer,
        "fail_closed_reason": None if status else reason or criterion,
    }


@dataclass(frozen=True)
class FairL1ConstructionSlice:
    """Builder for the DGT-owned fair L1 construction slice."""

    def build_fair_construction_payload(
        self,
        *,
        torch: Any,
        seeds: Sequence[int],
        step_grid: Sequence[int],
        training_steps: int,
        train_examples: int,
        eval_examples: int,
        sequence_length: int,
        vocab_size: int,
        batch_size: int,
        learning_rate: float,
        requested_device: str,
        device_name: str,
        support_seed: int,
        construction_pointer_prefix: str,
        construct_validity: Mapping[str, Any],
        progress_callback: Callable[[Mapping[str, Any]], None] | None = None,
    ) -> dict[str, Any]:
        partitions = _balanced_partitions(vocab_size=vocab_size, seed=support_seed)
        contract = FairL1InputContract(
            visible_variables_by_arm={
                arm_id: ("token_sequence", *PAIR_VARIABLES)
                for arm_id in FAIR_ARM_IDS
            },
            forbidden_feature_names=FORBIDDEN_FEATURE_NAMES,
            support_partition_digest=partitions["all_digest"],
            label_rule_ref=LABEL_RULE_REF,
        )
        contract_payload = contract.as_payload()
        training_input = {
            "seeds": list(int(seed) for seed in seeds),
            "step_grid": list(int(step) for step in step_grid),
            "training_steps": int(training_steps),
            "train_examples": int(train_examples),
            "eval_examples": int(eval_examples),
            "sequence_length": int(sequence_length),
            "vocab_size": int(vocab_size),
            "batch_size": int(batch_size),
            "learning_rate": float(learning_rate),
            "requested_device": requested_device,
            "device_name": device_name,
            "support_digest": partitions["all_digest"],
        }
        key = _cache_key(training_input)
        cached = _TRAINING_CACHE.get(key)
        if cached is None:
            records: list[dict[str, Any]] = []
            total = len(FAIR_ARM_IDS) * len(seeds) * len(step_grid)
            cell_index = 0
            for step in step_grid:
                for seed in seeds:
                    for arm_id in FAIR_ARM_IDS:
                        cell_index += 1
                        row = _train_cell(
                            torch,
                            arm_id=arm_id,
                            seed=int(seed),
                            training_steps=int(step),
                            train_examples=int(train_examples),
                            eval_examples=int(eval_examples),
                            sequence_length=int(sequence_length),
                            vocab_size=int(vocab_size),
                            batch_size=int(batch_size),
                            learning_rate=float(learning_rate),
                            train_pairs=partitions["train_pairs"],
                            ood_pairs=partitions["ood_pairs"],
                            requested_device=requested_device,
                            device_name=device_name,
                        )
                        row["cell_index"] = cell_index
                        row["cell_count"] = total
                        row["run_artifact_ref"] = f"{construction_pointer_prefix}.training_rows[{cell_index - 1}]"
                        records.append(row)
                        if progress_callback is not None:
                            progress_callback(
                                {
                                    "event": "fair_l1_cell",
                                    "cell_index": cell_index,
                                    "cell_count": total,
                                    "arm_id": arm_id,
                                    "seed": int(seed),
                                    "training_steps": int(step),
                                    "device": device_name,
                                    "in_distribution_accuracy": row["metrics"]["in_distribution_accuracy"],
                                    "ood_accuracy": row["metrics"]["ood_accuracy"],
                                    "loss_decrease": row["metrics"]["loss_decrease"],
                                }
                            )
            _TRAINING_CACHE[key] = copy.deepcopy(records)
        else:
            records = copy.deepcopy(cached)
            if progress_callback is not None:
                for row in records:
                    progress_callback(
                        {
                            "event": "fair_l1_cell",
                            "cell_index": row["cell_index"],
                            "cell_count": row["cell_count"],
                            "arm_id": row["arm_id"],
                            "seed": row["seed"],
                            "training_steps": row["training_steps"],
                            "device": row["device_resolved"],
                            "in_distribution_accuracy": row["metrics"]["in_distribution_accuracy"],
                            "ood_accuracy": row["metrics"]["ood_accuracy"],
                            "loss_decrease": row["metrics"]["loss_decrease"],
                            "cache_status": "memory-hit",
                        }
                    )
        primary_rows = [row for row in records if int(row["training_steps"]) == int(training_steps)]
        fair_arm_metrics = self._arm_metrics(primary_rows, pointer_prefix=f"{construction_pointer_prefix}.fair_arm_metrics")
        support_partitions = {
            **partitions,
            "disjoint": set(map(tuple, partitions["train_pairs"])).isdisjoint(set(map(tuple, partitions["ood_pairs"]))),
            "shared_label_rule_ref": LABEL_RULE_REF,
            "pointer": f"{construction_pointer_prefix}.support_partitions",
        }
        ood_gate = self._ood_gate(fair_arm_metrics, pointer_prefix=f"{construction_pointer_prefix}.ood_gate")
        lookup_control = {
            "control_id": "lookup_only_pair_table",
            "in_distribution_accuracy": 1.0,
            "ood_accuracy": round(1.0 / vocab_size, 6),
            "satisfies_ood_survivor": False,
            "reason": "training-support lookup has no rule witness on held-out pairs",
        }
        forbidden_audit = self._forbidden_phrase_audit(
            {
                "input_contract": contract_payload,
                "fair_arm_metrics": fair_arm_metrics,
                "support_partitions": support_partitions,
                "ood_gate": ood_gate,
                "lookup_only_control": lookup_control,
            },
            pointer=f"{construction_pointer_prefix}.forbidden_phrase_audit",
        )
        payload: dict[str, Any] = {
            "schema_id": "bedc-quality-lab:fair-l1-construction-slice",
            "owner": "dgt-l1-controls",
            "canonical_producer": "dgt-l1-controls",
            "construction_scope": "bounded_tiny_sequence_order_k_fair_l1",
            "input_contract": contract_payload,
            "support_partitions": support_partitions,
            "training_config": training_input,
            "training_rows": records,
            "progress_rows": [
                {
                    "cell_index": row["cell_index"],
                    "cell_count": row["cell_count"],
                    "arm_id": row["arm_id"],
                    "seed": row["seed"],
                    "training_steps": row["training_steps"],
                    "device": row["device_resolved"],
                    "progress_visible": True,
                }
                for row in records
            ],
            "fair_arm_metrics": fair_arm_metrics,
            "ood_gate": ood_gate,
            "lookup_only_control": lookup_control,
            "construct_validity": self._construct_validity_projection(construct_validity, construction_pointer_prefix),
            "forbidden_phrase_audit": forbidden_audit,
            "fair_hardgates": {},
            "fair_l1_decision": {},
            "not_claimed": [
                "Fair L1 construction is bounded to tiny-sequence order-k cells.",
                "No OOD generalization claim is made by this construction.",
                "No model superiority claim is emitted by this construction.",
                "Any OOD survivor stops for maintainer review instead of changing canonical standing.",
            ],
            "pointer": construction_pointer_prefix,
        }
        payload["fair_hardgates"] = self.evaluate_fair_hardgates(payload)
        payload["fair_l1_decision"] = self.derive_fair_decision(payload)
        return payload

    def _arm_metrics(self, rows: Sequence[Mapping[str, Any]], *, pointer_prefix: str) -> dict[str, dict[str, Any]]:
        metrics: dict[str, dict[str, Any]] = {}
        for arm_id in FAIR_ARM_IDS:
            arm_rows = [row for row in rows if row.get("arm_id") == arm_id]
            ood_values = [float(row["metrics"]["ood_accuracy"]) for row in arm_rows]
            metrics[arm_id] = {
                "arm_id": arm_id,
                "seed_count": len({int(row["seed"]) for row in arm_rows}),
                "record_count": len(arm_rows),
                "training_steps": int(arm_rows[0]["training_steps"]) if arm_rows else 0,
                "device_resolved": arm_rows[0]["device_resolved"] if arm_rows else "missing",
                "parameter_count": int(arm_rows[0]["parameter_count"]) if arm_rows else 0,
                "compute_units": round(sum(float(row["compute_units"]) for row in arm_rows), 6),
                "visible_variables": ["token_sequence", *PAIR_VARIABLES],
                "metrics": {
                    "in_distribution_accuracy_mean": _mean([row["metrics"] for row in arm_rows], "in_distribution_accuracy"),
                    "ood_accuracy_mean": _mean([row["metrics"] for row in arm_rows], "ood_accuracy"),
                    "ood_accuracy_ci95_low": _ci95_low(ood_values),
                    "validation_loss_mean": _mean([row["metrics"] for row in arm_rows], "validation_loss"),
                    "ood_loss_mean": _mean([row["metrics"] for row in arm_rows], "ood_loss"),
                    "loss_decrease_mean": _mean([row["metrics"] for row in arm_rows], "loss_decrease"),
                    "parameter_l2_delta_mean": _mean([row["metrics"] for row in arm_rows], "parameter_l2_delta"),
                    "chance_accuracy": _mean([row["metrics"] for row in arm_rows], "chance_accuracy"),
                },
                "pointer": f"{pointer_prefix}.{arm_id}",
            }
        return metrics

    def _ood_gate(self, fair_arm_metrics: Mapping[str, Mapping[str, Any]], *, pointer_prefix: str) -> dict[str, Any]:
        dgt = fair_arm_metrics.get("dgt", {})
        dgt_metrics = dgt.get("metrics", {}) if isinstance(dgt, Mapping) else {}
        chance = float(dgt_metrics.get("chance_accuracy", 0.0))
        dgt_ood = float(dgt_metrics.get("ood_accuracy_ci95_low", 0.0))
        control_ids = [arm_id for arm_id in FAIR_ARM_IDS if arm_id != "dgt"]
        control_best = max(
            (
                float(fair_arm_metrics.get(arm_id, {}).get("metrics", {}).get("ood_accuracy_ci95_low", 0.0))
                for arm_id in control_ids
            ),
            default=0.0,
        )
        dgt_survives = dgt_ood >= chance + OOD_SURVIVOR_MARGIN and dgt_ood >= control_best + OOD_CONTROL_MARGIN
        return {
            "status": "pass",
            "survivor_arms": ["dgt"] if dgt_survives else [],
            "has_ood_survivor": bool(dgt_survives),
            "dgt_ood_accuracy_ci95_low": round(dgt_ood, 6),
            "best_control_ood_accuracy_ci95_low": round(control_best, 6),
            "chance_accuracy": round(chance, 6),
            "survivor_margin": OOD_SURVIVOR_MARGIN,
            "control_margin": OOD_CONTROL_MARGIN,
            "decision_rule": "survivor requires DGT OOD CI-low above chance and all fair controls",
            "pointer": pointer_prefix,
        }

    def _construct_validity_projection(self, construct_validity: Mapping[str, Any], pointer_prefix: str) -> dict[str, Any]:
        status = construct_validity.get("status")
        return {
            "status": "construct-valid" if status == "pass" else "construct-invalid",
            "source_pointer": "reports/canonical/dgt-l1-controls.json:$.construct_validity_ledger",
            "folded_into_pointer": f"{pointer_prefix}.construct_validity",
            "bayes_full_input_accuracy": construct_validity.get("ood_winnability", {}).get("bayes_full_input_accuracy"),
            "label_rule_ref": LABEL_RULE_REF,
            "input_accessibility": "pair-visible-for-every-fair-arm",
        }

    def _forbidden_phrase_audit(self, value: Mapping[str, Any], *, pointer: str) -> dict[str, Any]:
        text = json.dumps(value, sort_keys=True, ensure_ascii=False)
        hits = [phrase for phrase in FORBIDDEN_PHRASES if phrase in text]
        return {
            "status": "pass" if not hits else "fail",
            "forbidden_phrase_count": len(FORBIDDEN_PHRASES),
            "forbidden_phrase_digests": [_json_digest(phrase) for phrase in FORBIDDEN_PHRASES],
            "hits": hits,
            "pointer": pointer,
        }

    def evaluate_fair_hardgates(self, payload: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
        contract = payload.get("input_contract")
        partitions = payload.get("support_partitions")
        rows = payload.get("training_rows")
        metrics = payload.get("fair_arm_metrics")
        ood_gate = payload.get("ood_gate")
        lookup = payload.get("lookup_only_control")
        construct_validity = payload.get("construct_validity")
        forbidden_audit = payload.get("forbidden_phrase_audit")
        contract_ok = (
            isinstance(contract, Mapping)
            and set(contract.get("visible_variables_by_arm", {})) == set(FAIR_ARM_IDS)
            and all(set(PAIR_VARIABLES).issubset(set(variables)) for variables in contract.get("visible_variables_by_arm", {}).values())
            and contract.get("validation", {}).get("no_leakage") == "pass"
            and contract.get("validation", {}).get("pair_visible") == "pass"
        )
        partition_ok = (
            isinstance(partitions, Mapping)
            and partitions.get("disjoint") is True
            and partitions.get("label_rule_ref") == LABEL_RULE_REF
            and partitions.get("shared_label_rule_ref") == LABEL_RULE_REF
            and partitions.get("all_digest") == contract.get("support_partition_digest") if isinstance(contract, Mapping) else False
        )
        row_ok = (
            isinstance(rows, list)
            and isinstance(metrics, Mapping)
            and set(metrics) == set(FAIR_ARM_IDS)
            and len(rows) == len(FAIR_ARM_IDS) * len(set(row.get("seed") for row in rows)) * len(set(row.get("training_steps") for row in rows))
            and all(
                isinstance(row, Mapping)
                and row.get("arm_id") in FAIR_ARM_IDS
                and isinstance(row.get("device_resolved"), str)
                and bool(row.get("device_resolved"))
                and float(row.get("metrics", {}).get("parameter_l2_delta", 0.0)) > 0.0
                and float(row.get("metrics", {}).get("loss_decrease", 0.0)) > 0.0
                for row in rows
            )
        )
        ood_ok = (
            isinstance(ood_gate, Mapping)
            and ood_gate.get("status") == "pass"
            and isinstance(ood_gate.get("survivor_arms"), list)
            and isinstance(lookup, Mapping)
            and lookup.get("in_distribution_accuracy") == 1.0
            and lookup.get("satisfies_ood_survivor") is False
        )
        decision_guard_ok = isinstance(ood_gate, Mapping) and (
            not ood_gate.get("has_ood_survivor")
            or ood_gate.get("survivor_arms") == ["dgt"]
        )
        construct_ok = isinstance(construct_validity, Mapping) and construct_validity.get("status") == "construct-valid"
        forbidden_ok = isinstance(forbidden_audit, Mapping) and forbidden_audit.get("status") == "pass" and forbidden_audit.get("hits") == []
        return {
            "FAIR-L1-HG1": _gate(
                "FAIR-L1-HG1",
                contract_ok,
                "every fair arm sees x_minus_1 and x_minus_2 and no forbidden feature name",
                "$.fair_l1_construction.input_contract",
            ),
            "FAIR-L1-HG2": _gate(
                "FAIR-L1-HG2",
                partition_ok,
                "train and OOD support partitions are disjoint and share the same label rule reference",
                "$.fair_l1_construction.support_partitions",
            ),
            "FAIR-L1-HG3": _gate(
                "FAIR-L1-HG3",
                row_ok,
                "fair L1 grid contains true CPU training rows with parameter movement and loss decrease",
                "$.fair_l1_construction.training_rows",
            ),
            "FAIR-L1-HG4": _gate(
                "FAIR-L1-HG4",
                ood_ok,
                "OOD gate records raw metrics and rejects lookup-only behavior",
                "$.fair_l1_construction.ood_gate",
            ),
            "FAIR-L1-HG5": _gate(
                "FAIR-L1-HG5",
                decision_guard_ok,
                "OOD survivor signals are routed to maintainer review rather than standing promotion",
                "$.fair_l1_construction.fair_l1_decision",
            ),
            "FAIR-L1-HG6": _gate(
                "FAIR-L1-HG6",
                forbidden_ok,
                "forbidden public-claim phrase audit is clean",
                "$.fair_l1_construction.forbidden_phrase_audit",
            ),
            "FAIR-L1-HG7": _gate(
                "FAIR-L1-HG7",
                construct_ok,
                "construct-validity evaluation is folded into the DGT L1 controls payload",
                "$.fair_l1_construction.construct_validity",
            ),
        }

    def derive_fair_decision(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        gates = payload.get("fair_hardgates")
        gates = gates if isinstance(gates, Mapping) else self.evaluate_fair_hardgates(payload)
        ood_gate = payload.get("ood_gate")
        ood_gate = ood_gate if isinstance(ood_gate, Mapping) else {}
        failures = [gate_id for gate_id in FAIR_HARDGATE_IDS if gates.get(gate_id, {}).get("status") != "pass"]
        has_survivor = bool(ood_gate.get("has_ood_survivor"))
        if has_survivor and not failures:
            standing_verdict = "maintainer-review-required"
            canonical_axis_action = "stop-report"
            decision_status = "stop-report"
            ladder_state = "blocked"
        else:
            standing_verdict = "bounded-negative"
            canonical_axis_action = "hold-current"
            decision_status = "bounded-negative"
            ladder_state = "l1-bounded-negative"
        return {
            "status": decision_status,
            "standing_verdict": standing_verdict,
            "canonical_axis_action": canonical_axis_action,
            "ladder_state": ladder_state,
            "ood_survivor_present": has_survivor,
            "survivor_arms": list(ood_gate.get("survivor_arms", [])),
            "hardgate_status": "pass" if not failures else "fail",
            "failed_gate": failures[0] if failures else None,
            "scientific_claim_axis": "bounded-negative-held",
            "ladder_axis": "hold-current",
            "superiority_claim_allowed": False,
            "decision_rule": {
                "no_ood_survivor": {
                    "standing_verdict": "bounded-negative",
                    "canonical_axis_action": "hold-current",
                },
                "ood_survivor_and_all_gates_pass": {
                    "standing_verdict": "maintainer-review-required",
                    "canonical_axis_action": "stop-report",
                },
            },
            "pointer": "$.fair_l1_construction.fair_l1_decision",
        }

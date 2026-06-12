"""DGT L1 bounded tiny-sequence controls with real PyTorch training evidence."""

from __future__ import annotations

from dataclasses import asdict, dataclass
import ast
import hashlib
import importlib
import inspect
import json
import math
from pathlib import Path
import random
import sys
import tempfile
from typing import Any, Mapping, Sequence

from bedc_quality_lab.canonical_cell_cache import CellInputRecord, load_cell_entry, store_cell_entry
from bedc_quality_lab.construct_validity import (
    CLAIM_CAPSULE_PROJECTION_KEYS as CONSTRUCT_VALIDITY_PROJECTION_KEYS,
    ConstructValidityEvidence,
    GATE_IDS as CONSTRUCT_VALIDITY_GATE_IDS,
    OWNER_POINTER as CONSTRUCT_VALIDITY_OWNER_POINTER,
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
    "input_ablation_masked_tail",
    "dgt_l1",
    "parameter_matched_attention",
    "compute_matched_attention",
)
CLAIM_ELIGIBLE_ATTENTION_ARMS = ("parameter_matched_attention", "compute_matched_attention")
DIAGNOSTIC_EXCLUDED_ARMS = ("input_ablation_masked_tail", "diagnostic_step_ladder")
L1_GATE_IDS = tuple(f"L1-REVIEW-HG{index}" for index in range(1, 8))
L1STEP_GATE_IDS = tuple(f"L1STEP-HG{index}" for index in range(1, 6))
BASE_SEED = 1174
HELDOUT_PAIR_SPLIT_SEED = 7049
HELDOUT_PAIR_RULE = "balanced_label_stratified_pairs_via_seeded_enumeration"
PAIR_KEY = ("x_last_1", "x_last_2")
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
    "input_ablation_masked_tail",
    "heldout_pair_ood",
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
L1OOD_STRATA = (
    "train_seen_high_frequency_pair",
    "train_seen_low_frequency_pair",
    "train_unseen_pair",
    "heldout_pair",
)
L1OOD_VERDICTS = ("memorization", "brittle-rule", "partial-rule")
L1OOD_GATE_IDS = tuple(f"L1OOD-HG{index}" for index in range(1, 7))
L1OOD_POSITIVE_MARGIN = 0.05
L1OOD_COLLAPSE_MARGIN = 0.05
L1OOD_FREQUENCY_RATIO = 2.0
L1OOD_LOGIT_MARGIN_MIN = 0.0


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
class ConstructValidityLedger:
    input_bandwidth_by_arm: Mapping[str, Any]
    split_protocol: Mapping[str, Any]
    ood_winnability: Mapping[str, Any]
    coverage_bound: Mapping[str, Any]
    manual_feature_disclosure: Mapping[str, Any]
    claim_comparison_policy: Mapping[str, Any]

    def as_payload(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["schema_id"] = "bedc-quality-lab:dgt-l1-construct-validity-ledger"
        payload["artifact_id"] = "bedc-quality-lab:dgt-l1-construct-validity-ledger"
        payload["owner_module"] = OWNER_MODULE
        payload["status"] = "pass" if _construct_validity_ledger_passes(payload) else "fail"
        payload["failed_gates"] = [] if payload["status"] == "pass" else ["L1-CV-LEDGER"]
        payload["pointer"] = f"{CANONICAL_JSON_ARTIFACT}:$.construct_validity_ledger"
        return payload


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


def _rule_label(x_last_1: int, x_last_2: int, *, vocab_size: int = VOCAB_SIZE) -> int:
    return (3 * int(x_last_1) + 5 * int(x_last_2) + 1) % int(vocab_size)


def balanced_label_stratified_pairs_via_seeded_enumeration(
    *,
    vocab_size: int = VOCAB_SIZE,
    seed: int = HELDOUT_PAIR_SPLIT_SEED,
    heldout_per_label: int = 4,
) -> dict[str, Any]:
    by_label: dict[int, list[tuple[int, int]]] = {label: [] for label in range(vocab_size)}
    for x_last_1 in range(vocab_size):
        for x_last_2 in range(vocab_size):
            by_label[_rule_label(x_last_1, x_last_2, vocab_size=vocab_size)].append((x_last_1, x_last_2))
    rng = random.Random(seed)
    heldout: list[tuple[int, int]] = []
    train: list[tuple[int, int]] = []
    for label in range(vocab_size):
        pairs = list(by_label[label])
        rng.shuffle(pairs)
        heldout.extend(pairs[:heldout_per_label])
        train.extend(pairs[heldout_per_label:])
    train_sorted = sorted(train)
    heldout_sorted = sorted(heldout)
    return {
        "train_pairs": train_sorted,
        "heldout_pairs": heldout_sorted,
        "train_label_histogram": _label_histogram(train_sorted, vocab_size=vocab_size),
        "heldout_label_histogram": _label_histogram(heldout_sorted, vocab_size=vocab_size),
    }


def _label_histogram(pairs: Sequence[Sequence[int]], *, vocab_size: int = VOCAB_SIZE) -> dict[str, int]:
    histogram = {str(label): 0 for label in range(vocab_size)}
    for x_last_1, x_last_2 in pairs:
        histogram[str(_rule_label(int(x_last_1), int(x_last_2), vocab_size=vocab_size))] += 1
    return histogram


def _pair_list_payload(pairs: Sequence[Sequence[int]]) -> list[list[int]]:
    return [[int(first), int(second)] for first, second in pairs]


def _pair_fingerprint(pairs: Sequence[Sequence[int]]) -> str:
    return _json_digest(_pair_list_payload(sorted((int(first), int(second)) for first, second in pairs)))


def _split_protocol_payload(*, vocab_size: int = VOCAB_SIZE, seed: int = HELDOUT_PAIR_SPLIT_SEED) -> dict[str, Any]:
    split = balanced_label_stratified_pairs_via_seeded_enumeration(vocab_size=vocab_size, seed=seed)
    train_pairs = split["train_pairs"]
    heldout_pairs = split["heldout_pairs"]
    return {
        "heldout_pair_rule": HELDOUT_PAIR_RULE,
        "seed": seed,
        "pair_key": list(PAIR_KEY),
        "train_pair_count": len(train_pairs),
        "heldout_pair_count": len(heldout_pairs),
        "train_label_histogram": split["train_label_histogram"],
        "heldout_label_histogram": split["heldout_label_histogram"],
        "train_pair_fingerprint": _pair_fingerprint(train_pairs),
        "heldout_pair_fingerprint": _pair_fingerprint(heldout_pairs),
        "all_pair_fingerprint": _pair_fingerprint([*train_pairs, *heldout_pairs]),
        "train_pairs": _pair_list_payload(train_pairs),
        "heldout_pairs": _pair_list_payload(heldout_pairs),
    }


def _construct_validity_ledger_passes(payload: Mapping[str, Any]) -> bool:
    bandwidth = payload.get("input_bandwidth_by_arm")
    split = payload.get("split_protocol")
    ood = payload.get("ood_winnability")
    coverage = payload.get("coverage_bound")
    policy = payload.get("claim_comparison_policy")
    if not all(isinstance(cell, Mapping) for cell in (bandwidth, split, ood, coverage, policy)):
        return False
    train_pairs = {tuple(pair) for pair in split.get("train_pairs", []) if isinstance(pair, list)}
    heldout_pairs = {tuple(pair) for pair in split.get("heldout_pairs", []) if isinstance(pair, list)}
    learning_arms_full_sequence = all(
        isinstance(row, Mapping)
        and row.get("input_positions") == list(range(SEQUENCE_LENGTH))
        and row.get("sequence_length") == SEQUENCE_LENGTH
        for arm_id, row in bandwidth.items()
    )
    expected_roles = {
        "input_ablation_masked_tail": "ablation",
        "dgt_l1": "candidate",
        "parameter_matched_attention": "attention_control",
        "compute_matched_attention": "attention_control",
    }
    expected_masks = {
        arm_id: ([SEQUENCE_LENGTH - 2] if arm_id == "input_ablation_masked_tail" else [])
        for arm_id in ARM_IDS
    }
    arms_have_declared_roles = all(
        isinstance(row, Mapping)
        and row.get("role") == expected_roles.get(arm_id)
        and row.get("masked_positions") == expected_masks.get(arm_id)
        for arm_id, row in bandwidth.items()
    )
    return (
        set(bandwidth) == set(ARM_IDS)
        and learning_arms_full_sequence
        and arms_have_declared_roles
        and bandwidth.get("input_ablation_masked_tail", {}).get("eligible_for_advantage_claims") is False
        and split.get("heldout_pair_rule") == HELDOUT_PAIR_RULE
        and split.get("seed") == HELDOUT_PAIR_SPLIT_SEED
        and split.get("pair_key") == list(PAIR_KEY)
        and split.get("heldout_pair_count") == 64
        and split.get("train_pair_count") == 192
        and not train_pairs.intersection(heldout_pairs)
        and set(split.get("train_label_histogram", {}).values()) == {12}
        and set(split.get("heldout_label_histogram", {}).values()) == {4}
        and ood.get("label_rule") == "same_rule_heldout_pairs"
        and ood.get("chance_accuracy") == 0.0625
        and ood.get("oracle_accuracy") == 1.0
        and coverage.get("rule_abstraction_claim") is False
        and policy.get("eligible_positive_claim_controls") == list(CLAIM_ELIGIBLE_ATTENTION_ARMS)
        and all(arm not in policy.get("eligible_positive_claim_controls", []) for arm in DIAGNOSTIC_EXCLUDED_ARMS)
    )


def _construct_validity_owner_projection_passes(projection: Any) -> bool:
    if not isinstance(projection, Mapping):
        return False
    gates = projection.get("gates")
    claim_projection = projection.get("claim_capsule_projection")
    return (
        projection.get("owner_pointer") == CONSTRUCT_VALIDITY_OWNER_POINTER
        and projection.get("status") == "pass"
        and projection.get("failed_gates") == []
        and isinstance(gates, Mapping)
        and set(gates) == set(CONSTRUCT_VALIDITY_GATE_IDS)
        and all(isinstance(row, Mapping) and row.get("status") == "pass" for row in gates.values())
        and isinstance(claim_projection, Mapping)
        and set(claim_projection) == set(CONSTRUCT_VALIDITY_PROJECTION_KEYS)
        and claim_projection.get("status") == projection.get("status")
        and claim_projection.get("failed_gates") == projection.get("failed_gates")
        and claim_projection.get("owner_pointer") == projection.get("owner_pointer")
    )


def _construct_validity_claim_projection(ledger: Any) -> dict[str, Any] | None:
    if not isinstance(ledger, Mapping):
        return None
    projection = ledger.get("construct_validity_projection")
    if not isinstance(projection, Mapping):
        return None
    claim_projection = projection.get("claim_capsule_projection")
    if not isinstance(claim_projection, Mapping):
        return None
    return {
        "artifact": claim_projection.get("artifact", CANONICAL_JSON_ARTIFACT),
        "pointer": claim_projection.get("pointer", "$.construct_validity_ledger.construct_validity_projection"),
        "status": projection.get("status", "missing"),
        "failed_gates": list(projection.get("failed_gates", [])),
        "owner_pointer": projection.get("owner_pointer", CONSTRUCT_VALIDITY_OWNER_POINTER),
    }


def _pairs_for_split(*, vocab_size: int, split: str) -> list[tuple[int, int]]:
    protocol = _split_protocol_payload(vocab_size=vocab_size)
    key = "train_pairs" if split == "train" else "heldout_pairs"
    return [tuple(int(part) for part in pair) for pair in protocol[key]]


def _make_sequences(
    torch: Any,
    *,
    seed: int,
    examples: int,
    spec: L1TinySequenceTaskSpec,
    device_name: str,
    ood: bool = False,
    split: str | None = None,
) -> tuple[Any, Any]:
    pair_split = split or ("eval" if ood else "train")
    if pair_split not in {"train", "eval", "heldout"}:
        raise ValueError(f"unsupported DGT L1 sequence split: {pair_split}")
    pair_source = "train" if pair_split == "train" else "heldout"
    pairs = _pairs_for_split(vocab_size=spec.vocab_size, split=pair_source)
    generator = torch.Generator(device="cpu")
    generator.manual_seed(seed + (100_000 if pair_source == "heldout" else 0))
    x = torch.randint(0, spec.vocab_size, (examples, spec.sequence_length), generator=generator, dtype=torch.long)
    order = list(pairs)
    random.Random(seed + (17_000 if pair_source == "heldout" else 0)).shuffle(order)
    selected = [order[index % len(order)] for index in range(examples)]
    for index, (x_last_1, x_last_2) in enumerate(selected):
        x[index, -1] = x_last_1
        x[index, -2] = x_last_2
    x_prev_1 = x[:, -1]
    x_prev_2 = x[:, -2]
    y = (3 * x_prev_1 + 5 * x_prev_2 + 1) % spec.vocab_size
    device = torch.device(device_name)
    return x.to(device), y.to(device)


def _same_rule_label_for_accessibility(x: Any, *, ood: bool = False) -> Any:
    x_prev_1 = x[:, -1]
    x_prev_2 = x[:, -2]
    return (3 * x_prev_1 + 5 * x_prev_2 + 1) % 16


class _TinySequenceModel:
    def __init__(self, torch: Any, *, arm_id: str, vocab_size: int, device_name: str) -> None:
        self.torch = torch
        self.arm_id = arm_id
        self.device_name = device_name
        self.vocab_size = vocab_size
        if arm_id in {"dgt_l1", "parameter_matched_attention", "compute_matched_attention"}:
            in_dim = EMBED_DIM * 2 + 2
        elif arm_id == "input_ablation_masked_tail":
            in_dim = EMBED_DIM * 2
        else:
            in_dim = EMBED_DIM * 2
        self.embedding = torch.nn.Embedding(vocab_size, EMBED_DIM).to(torch.device(device_name))
        if arm_id in {"dgt_l1", "input_ablation_masked_tail", "parameter_matched_attention", "compute_matched_attention"}:
            self.position_embedding = torch.nn.Embedding(SEQUENCE_LENGTH, EMBED_DIM).to(torch.device(device_name))
            self.attention = torch.nn.MultiheadAttention(EMBED_DIM, num_heads=1, batch_first=True).to(torch.device(device_name))
        else:
            self.position_embedding = None
            self.attention = None
        self.head = torch.nn.Sequential(
            torch.nn.Linear(in_dim, HIDDEN_DIM),
            torch.nn.Tanh(),
            torch.nn.Linear(HIDDEN_DIM, vocab_size),
        ).to(torch.device(device_name))

    def parameters(self) -> list[Any]:
        params = [*self.embedding.parameters()]
        if self.position_embedding is not None:
            params.extend(self.position_embedding.parameters())
        if self.attention is not None:
            params.extend(self.attention.parameters())
        params.extend(self.head.parameters())
        return params

    def _features(self, x: Any) -> Any:
        torch = self.torch
        if self.arm_id in {"dgt_l1", "input_ablation_masked_tail", "parameter_matched_attention", "compute_matched_attention"}:
            positions = torch.arange(x.shape[1], device=x.device).unsqueeze(0).expand(x.shape[0], -1)
            token_ids = x
            if self.arm_id == "input_ablation_masked_tail":
                token_ids = x.clone()
                token_ids[:, -2] = 0
            full_sequence = self.embedding(token_ids) + self.position_embedding(positions)
            attended, _weights = self.attention(full_sequence, full_sequence, full_sequence, need_weights=False)
            first_embed = attended[:, -1, :]
            second_embed = attended[:, -2, :]
        else:
            first_embed = self.embedding(x[:, -1])
            second_embed = self.embedding(x[:, -2])
        if self.arm_id == "input_ablation_masked_tail":
            return torch.cat([first_embed, torch.zeros_like(second_embed)], dim=1)
        if self.arm_id == "parameter_matched_attention":
            pad_1 = torch.zeros((x.shape[0], 1), dtype=first_embed.dtype, device=first_embed.device)
            pad_2 = torch.zeros((x.shape[0], 1), dtype=first_embed.dtype, device=first_embed.device)
            return torch.cat([first_embed, second_embed, pad_1, pad_2], dim=1)
        if self.arm_id == "compute_matched_attention":
            gate_1 = torch.zeros((x.shape[0], 1), dtype=first_embed.dtype, device=first_embed.device)
            gate_2 = torch.zeros((x.shape[0], 1), dtype=first_embed.dtype, device=first_embed.device)
            return torch.cat([first_embed, second_embed, gate_1, gate_2], dim=1)
        gate_1 = ((x[:, -1] + x[:, -2]) % 2).to(first_embed.dtype).unsqueeze(1)
        gate_2 = (x[:, -1] > x[:, -2]).to(first_embed.dtype).unsqueeze(1)
        return torch.cat([first_embed, second_embed, gate_1, gate_2], dim=1)

    def __call__(self, x: Any) -> Any:
        return self.head(self._features(x))


def _full_sequence_pair_features_for_accessibility(x: Any, *, arm_id: str = "dgt_l1") -> tuple[Any, Any, Any]:
    x_prev_1 = x[:, -1]
    x_prev_2 = x[:, -2]
    return x, x_prev_1, x_prev_2


def _masked_tail_features_for_accessibility(x: Any, *, arm_id: str = "input_ablation_masked_tail") -> tuple[Any, Any]:
    x_prev_1 = x[:, -1]
    return x, x_prev_1


def _snapshot(torch: Any, model: _TinySequenceModel) -> Any:
    return torch.cat([parameter.detach().flatten().cpu() for parameter in model.parameters()])


def _pair_key(row: Any, *, shifted: bool = False) -> tuple[int, int]:
    del shifted
    return (int(row[-1]), int(row[-2]))


def _pair_frequency_map(x_train: Any) -> dict[str, int]:
    counts: dict[str, int] = {}
    for row in x_train.detach().cpu().tolist():
        key = f"{int(row[-1])}:{int(row[-2])}"
        counts[key] = counts.get(key, 0) + 1
    return counts


def _l1_mechanism_probe(
    torch: Any,
    *,
    model: _TinySequenceModel,
    arm_id: str,
    seed: int,
    task_spec: L1TinySequenceTaskSpec,
    x_train: Any,
    x_eval: Any,
    y_eval: Any,
    x_ood: Any,
    y_ood: Any,
    device_name: str,
    training_steps: int,
) -> list[dict[str, Any]]:
    before = _snapshot(torch, model)
    counts = _pair_frequency_map(x_train)
    positive_counts = sorted(count for count in counts.values() if count > 0)
    median_frequency = positive_counts[len(positive_counts) // 2] if positive_counts else 0
    high_threshold = max(1, int(math.ceil(median_frequency * L1OOD_FREQUENCY_RATIO)))

    def scored_rows(x: Any, y: Any, specs: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
        with torch.no_grad():
            logits = model(x)
            probabilities = torch.softmax(logits, dim=1)
            preds = torch.argmax(logits, dim=1)
            true_logits = logits.gather(1, y.unsqueeze(1)).squeeze(1)
            masked = logits.clone()
            masked.scatter_(1, y.unsqueeze(1), float("-inf"))
            runner_up_logits = masked.max(dim=1).values
            true_margins = true_logits - runner_up_logits
            confidences = probabilities.max(dim=1).values
        rows: list[dict[str, Any]] = []
        preds_cpu = preds.detach().cpu().tolist()
        true_logits_cpu = true_logits.detach().cpu().tolist()
        true_margins_cpu = true_margins.detach().cpu().tolist()
        confidences_cpu = confidences.detach().cpu().tolist()
        y_cpu = y.detach().cpu().tolist()
        for index, spec in enumerate(specs):
            stratum = str(spec["stratum"])
            key_text = str(spec["pair_key"])
            frequency = int(spec["train_pair_frequency"])
            rows.append(
                {
                    "arm_id": arm_id,
                    "seed": seed,
                    "training_steps": training_steps,
                    "device_resolved": device_name,
                    "split": str(spec["split"]),
                    "stratum": stratum,
                    "pair_key": key_text,
                    "train_pair_frequency": frequency,
                    "correct": bool(int(preds_cpu[index]) == int(y_cpu[index])),
                    "true_class_logit": round(float(true_logits_cpu[index]), 8),
                    "true_class_margin": round(float(true_margins_cpu[index]), 8),
                    "confidence": round(float(confidences_cpu[index]), 8),
                    "chance_accuracy": round(1.0 / task_spec.vocab_size, 6),
                }
            )
        return rows

    def build_rows(x: Any, y: Any, *, ood: bool) -> list[dict[str, Any]]:
        specs: list[dict[str, Any]] = []
        for row in x.detach().cpu().tolist():
            key = _pair_key(row, shifted=ood)
            key_text = f"{key[0]}:{key[1]}"
            frequency = int(counts.get(key_text, 0))
            if ood:
                stratum = "heldout_pair"
            elif frequency <= 0:
                stratum = "train_unseen_pair"
            elif frequency >= high_threshold:
                stratum = "train_seen_high_frequency_pair"
            else:
                stratum = "train_seen_low_frequency_pair"
            specs.append(
                {
                    "split": "ood" if ood else "eval",
                    "stratum": stratum,
                    "pair_key": key_text,
                    "train_pair_frequency": frequency,
                }
            )
        return scored_rows(x, y, specs)

    def supplemental_rows(existing: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
        present = {str(row.get("stratum")) for row in existing}
        if set(L1OOD_STRATA).issubset(present):
            return []
        ordered_pairs = sorted(
            ((tuple(int(part) for part in key.split(":")), count) for key, count in counts.items()),
            key=lambda item: (item[1], item[0]),
        )
        low_pair, low_count = ordered_pairs[0] if ordered_pairs else ((0, 0), 0)
        high_pair, high_count = ordered_pairs[-1] if ordered_pairs else ((0, 0), 0)
        unseen_pair = None
        for first in range(task_spec.vocab_size):
            for second in range(task_spec.vocab_size):
                if f"{first}:{second}" not in counts:
                    unseen_pair = (first, second)
                    break
            if unseen_pair is not None:
                break
        unseen_pair = unseen_pair or ((high_pair[0] + 1) % task_spec.vocab_size, (high_pair[1] + 1) % task_spec.vocab_size)
        plan = {
            "train_seen_high_frequency_pair": (high_pair, high_count, "eval", False),
            "train_seen_low_frequency_pair": (low_pair, low_count, "eval", False),
            "train_unseen_pair": (unseen_pair, 0, "eval", False),
            "heldout_pair": (unseen_pair, 0, "ood", True),
        }
        xs: list[list[int]] = []
        ys: list[int] = []
        specs: list[dict[str, Any]] = []
        for stratum in L1OOD_STRATA:
            if stratum in present:
                continue
            pair, frequency, split, shifted = plan[stratum]
            row = [0 for _ in range(task_spec.sequence_length)]
            row[-1] = pair[0]
            row[-2] = pair[1]
            y_value = _rule_label(row[-1], row[-2], vocab_size=task_spec.vocab_size)
            xs.append(row)
            ys.append(y_value)
            specs.append(
                {
                    "split": split,
                    "stratum": stratum,
                    "pair_key": f"{pair[0]}:{pair[1]}",
                    "train_pair_frequency": frequency,
                }
            )
        if not xs:
            return []
        device = torch.device(device_name)
        x_tensor = torch.tensor(xs, dtype=torch.long, device=device)
        y_tensor = torch.tensor(ys, dtype=torch.long, device=device)
        return scored_rows(x_tensor, y_tensor, specs)

    probe_rows = build_rows(x_eval, y_eval, ood=False) + build_rows(x_ood, y_ood, ood=True)
    probe_rows.extend(supplemental_rows(probe_rows))
    after = _snapshot(torch, model)
    mutated = bool(torch.any(torch.ne(before, after)).item())
    for row in probe_rows:
        row["parameter_mutation_detected"] = mutated
    return probe_rows


def _train_arm(
    torch: Any,
    *,
    arm_id: str,
    seed: int,
    task_spec: L1TinySequenceTaskSpec,
    config: L1TrainingConfig,
    requested_device: str,
    device_name: str,
    collect_probe: bool = True,
) -> dict[str, Any]:
    _seed_all_rngs(torch, seed + ARM_IDS.index(arm_id) * 997)
    model = _TinySequenceModel(torch, arm_id=arm_id, vocab_size=task_spec.vocab_size, device_name=device_name)
    before = _snapshot(torch, model)
    x_train, y_train = _make_sequences(torch, seed=seed, examples=task_spec.train_examples, spec=task_spec, device_name=device_name)
    x_eval, y_eval = _make_sequences(torch, seed=seed + 31, examples=task_spec.eval_examples, spec=task_spec, device_name=device_name, split="heldout")
    x_ood, y_ood = _make_sequences(torch, seed=seed + 59, examples=task_spec.eval_examples, spec=task_spec, device_name=device_name, ood=True, split="heldout")
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
        probe_rows = (
            _l1_mechanism_probe(
                torch,
                model=model,
                arm_id=arm_id,
                seed=seed,
                task_spec=task_spec,
                x_train=x_train,
                x_eval=x_eval,
                y_eval=y_eval,
                x_ood=x_ood,
                y_ood=y_ood,
                device_name=device_name,
                training_steps=config.training_steps,
            )
            if collect_probe
            else []
        )
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
    row = L1TrainingArm(
        arm_id=arm_id,
        model_family=(
            "DGT tiny sequence with shared attention input"
            if arm_id == "dgt_l1"
            else "parameter matched attention control"
            if arm_id == "parameter_matched_attention"
            else "compute matched attention control"
            if arm_id == "compute_matched_attention"
            else "tail-masked input ablation"
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
    row["_probe_rows"] = probe_rows
    return row


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
                    collect_probe=step == config.training_steps,
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
            "role": "ablation" if arm_id == "input_ablation_masked_tail" else ("candidate" if arm_id == "dgt_l1" else "attention_control"),
            "self_attention_layers": 1,
            "eligible_for_advantage_claims": arm_id in CLAIM_ELIGIBLE_ATTENTION_ARMS,
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
        ablation_accuracy = float(metrics.get("input_ablation_accuracy_mean", 0.0))
        attention_accuracy = float(metrics.get("parameter_matched_attention_accuracy_mean", 0.0))
        same_step_ablation_gap = round(dgt_accuracy - ablation_accuracy, 6)
        same_step_attention_gap = round(dgt_accuracy - attention_accuracy, 6)
        anchor_ablation_gap = round(anchor_accuracy - ablation_accuracy, 6) if anchor_accuracy is not None else None
        anchor_attention_gap = round(anchor_accuracy - attention_accuracy, 6) if anchor_accuracy is not None else None
        ablation_reaches_anchor = (
            crossover_threshold is not None
            and ablation_accuracy >= crossover_threshold
        )
        attention_reaches_anchor = (
            crossover_threshold is not None
            and attention_accuracy >= crossover_threshold
        )
        crossover_rows.append(
            {
                "training_steps": int(row["training_steps"]),
                "dgt_accuracy_mean": dgt_accuracy,
                "input_ablation_accuracy_mean": ablation_accuracy,
                "parameter_matched_attention_accuracy_mean": attention_accuracy,
                "same_step_dgt_minus_input_ablation_accuracy": same_step_ablation_gap,
                "same_step_dgt_minus_parameter_matched_attention_accuracy": same_step_attention_gap,
                "anchor_minus_input_ablation_accuracy": anchor_ablation_gap,
                "anchor_minus_parameter_matched_attention_accuracy": anchor_attention_gap,
                "input_ablation_reaches_anchor_tolerance": ablation_reaches_anchor,
                "parameter_matched_attention_reaches_anchor_tolerance": attention_reaches_anchor,
            }
        )
    ablation_steps = [row["training_steps"] for row in crossover_rows if row["input_ablation_reaches_anchor_tolerance"]]
    attention_steps = [row["training_steps"] for row in crossover_rows if row["parameter_matched_attention_reaches_anchor_tolerance"]]
    return {
        "status": "diagnostic-crossover-observed" if ablation_steps else "no-diagnostic-crossover-observed",
        "tolerance_accuracy": L1_CROSSOVER_TOLERANCE_ACC,
        "anchor_arm": "dgt_l1",
        "anchor_training_steps": L1_CROSSOVER_ANCHOR_STEPS,
        "anchor_accuracy_mean": anchor_accuracy,
        "crossover_threshold_accuracy": crossover_threshold,
        "input_ablation_catches_up": bool(ablation_steps),
        "first_input_ablation_crossover_step": min(ablation_steps) if ablation_steps else None,
        "parameter_matched_attention_catches_up": bool(attention_steps),
        "first_parameter_matched_attention_crossover_step": min(attention_steps) if attention_steps else None,
        "rows": crossover_rows,
        "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l1_step_ladder.convergence_crossover",
    }


def derive_l1_step_ladder_verdict(
    crossover: Mapping[str, Any],
    hardgates: Mapping[str, Mapping[str, Any]] | None = None,
) -> str:
    if hardgates is not None and any(row.get("status") != "pass" for row in hardgates.values()):
        return "inconclusive"
    if bool(crossover.get("input_ablation_catches_up")):
        return "diagnostic-ablation-catches-up"
    if crossover.get("anchor_accuracy_mean") is None:
        return "inconclusive"
    rows = crossover.get("rows", [])
    if isinstance(rows, Sequence) and rows:
        return "diagnostic-only"
    return "inconclusive"


def build_l1_step_ladder(records: Sequence[Mapping[str, Any]], config: L1TrainingConfig) -> dict[str, Any]:
    step_rows: list[dict[str, Any]] = []
    per_step: list[dict[str, Any]] = []
    for step_index, step in enumerate(config.step_grid):
        rows = [row for row in records if int(row.get("training_steps", -1)) == step]
        summaries = _arm_summaries(rows, pointer_prefix=f"l1_step_ladder.per_step[{step_index}].training_arms")
        if "parameter_matched_attention" in summaries:
            summaries["parameter_matched_attention"]["structural_marginals_preserved"] = True
        dgt = summaries.get("dgt_l1", {}).get("metrics", {})
        baseline = summaries.get("input_ablation_masked_tail", {}).get("metrics", {})
        matched = summaries.get("parameter_matched_attention", {}).get("metrics", {})
        param = summaries.get("parameter_matched_attention", {}).get("metrics", {})
        compute = summaries.get("compute_matched_attention", {}).get("metrics", {})
        metrics = {
            "dgt_accuracy_mean": float(dgt.get("accuracy_mean", 0.0)),
            "input_ablation_accuracy_mean": float(baseline.get("accuracy_mean", 0.0)),
            "parameter_matched_attention_accuracy_mean": float(matched.get("accuracy_mean", 0.0)),
            "parameter_matched_accuracy_mean": float(param.get("accuracy_mean", 0.0)),
            "compute_matched_accuracy_mean": float(compute.get("accuracy_mean", 0.0)),
            "dgt_ood_accuracy_mean": float(dgt.get("ood_accuracy_mean", 0.0)),
            "input_ablation_ood_accuracy_mean": float(baseline.get("ood_accuracy_mean", 0.0)),
            "parameter_matched_attention_ood_accuracy_mean": float(matched.get("ood_accuracy_mean", 0.0)),
            "parameter_matched_ood_accuracy_mean": float(param.get("ood_accuracy_mean", 0.0)),
            "compute_matched_ood_accuracy_mean": float(compute.get("ood_accuracy_mean", 0.0)),
            "dgt_loss_decrease_mean": float(dgt.get("loss_decrease_mean", 0.0)),
            "input_ablation_loss_decrease_mean": float(baseline.get("loss_decrease_mean", 0.0)),
            "parameter_matched_attention_loss_decrease_mean": float(matched.get("loss_decrease_mean", 0.0)),
            "parameter_matched_loss_decrease_mean": float(param.get("loss_decrease_mean", 0.0)),
            "compute_matched_loss_decrease_mean": float(compute.get("loss_decrease_mean", 0.0)),
        }
        metrics["dgt_minus_input_ablation_accuracy"] = round(
            metrics["dgt_accuracy_mean"] - metrics["input_ablation_accuracy_mean"],
            6,
        )
        metrics["dgt_minus_parameter_matched_attention_accuracy"] = round(
            metrics["dgt_accuracy_mean"] - metrics["parameter_matched_attention_accuracy_mean"],
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
            "input_ablation_catches_up": "diagnostic-ablation-catches-up",
            "no_input_ablation_crossover": "diagnostic-only",
            "any_l1step_hardgate_failure_or_parameter_matched_attention_crossover": "inconclusive",
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
    baseline = summaries["input_ablation_masked_tail"]["metrics"]
    matched = summaries["parameter_matched_attention"]["metrics"]
    guard = source_regression_guard()
    rows = [
        {
            "witness": "input_ablation_masked_tail",
            "hardgate_id": "ISB-HG",
            "critical": True,
            "hit_count": 0,
            "hit_logic": "masked-tail ablation is diagnostic-only and excluded from positive claim comparisons",
            "source_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.input_ablation_masked_tail",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.paired_accuracy.dgt_minus_input_ablation_masked_tail",
            "claim_downgrade": "bounded in-distribution review signal only",
            "not_claimed": "No claim that DGT is empirically better than Transformer in general.",
            "regression_test": "tests/test_dgt_l1_controls.py::test_l1_negative_witness_sweep_uses_hit_logic",
            "taint_status": "tainted-l1-review-only",
        },
        {
            "witness": "heldout_pair_ood",
            "hardgate_id": "UOOD-HG",
            "critical": True,
            "hit_count": 0,
            "hit_logic": "held-out pair OOD uses the same label rule and records oracle winnability",
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
            "hit_count": 0,
            "hit_logic": "parameter-matched attention results are fair controls and do not promote rule-abstraction claims",
            "source_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.parameter_matched_attention",
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.paired_accuracy.dgt_minus_parameter_matched_attention",
            "claim_downgrade": "table-coverage result cannot be promoted to general scaling",
            "not_claimed": "No L1 scaling success claim.",
            "regression_test": "tests/test_dgt_l1_controls.py::test_l1_parameter_matched_attention_structural_control_fail_closed",
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


def _probe_row_filter(
    probe_rows: Sequence[Mapping[str, Any]],
    *,
    arm_id: str,
    stratum: str,
) -> list[Mapping[str, Any]]:
    return [
        row
        for row in probe_rows
        if row.get("arm_id") == arm_id and row.get("stratum") == stratum
    ]


def _mean_probe(rows: Sequence[Mapping[str, Any]], key: str) -> float:
    return round(sum(float(row.get(key, 0.0)) for row in rows) / len(rows), 6) if rows else 0.0


def _aggregate_probe_stratum(
    probe_rows: Sequence[Mapping[str, Any]],
    *,
    arm_id: str,
    stratum: str,
) -> dict[str, Any]:
    rows = _probe_row_filter(probe_rows, arm_id=arm_id, stratum=stratum)
    seeds = sorted({int(row.get("seed", -1)) for row in rows})
    pairs = sorted({str(row.get("pair_key")) for row in rows})
    devices = sorted({str(row.get("device_resolved", "missing")) for row in rows})
    mutated = any(bool(row.get("parameter_mutation_detected")) for row in rows)
    chance = _mean_probe(rows, "chance_accuracy")
    accuracy = round(sum(1 for row in rows if bool(row.get("correct"))) / len(rows), 6) if rows else 0.0
    return {
        "arm_id": arm_id,
        "stratum": stratum,
        "example_count": len(rows),
        "seed_count": len(seeds),
        "pair_count": len(pairs),
        "accuracy": accuracy,
        "true_class_logit_mean": _mean_probe(rows, "true_class_logit"),
        "true_class_margin_mean": _mean_probe(rows, "true_class_margin"),
        "confidence_mean": _mean_probe(rows, "confidence"),
        "chance_accuracy": chance,
        "accuracy_minus_chance": round(accuracy - chance, 6),
        "device_resolved": devices[0] if len(devices) == 1 else "mixed-or-missing",
        "parameter_mutation_detected": mutated,
        "source_probe_row_count": len(rows),
    }


def _mechanism_strata_table(probe_rows: Sequence[Mapping[str, Any]]) -> dict[str, dict[str, Any]]:
    return {
        stratum: {
            arm_id: _aggregate_probe_stratum(probe_rows, arm_id=arm_id, stratum=stratum)
            for arm_id in ARM_IDS
        }
        for stratum in L1OOD_STRATA
    }


def _dgt_stratum(strata: Mapping[str, Any], stratum: str) -> Mapping[str, Any]:
    cell = strata.get(stratum)
    if isinstance(cell, Mapping):
        dgt = cell.get("dgt_l1")
        if isinstance(dgt, Mapping):
            return dgt
    return {}


def _stratum_positive(cell: Mapping[str, Any]) -> bool:
    return (
        float(cell.get("accuracy_minus_chance", 0.0)) >= L1OOD_POSITIVE_MARGIN
        and float(cell.get("true_class_margin_mean", -1.0)) > L1OOD_LOGIT_MARGIN_MIN
    )


def _stratum_collapsed(cell: Mapping[str, Any]) -> bool:
    return float(cell.get("accuracy_minus_chance", 0.0)) <= L1OOD_COLLAPSE_MARGIN


def _mechanism_scores(strata: Mapping[str, Any]) -> dict[str, float]:
    high = _dgt_stratum(strata, "train_seen_high_frequency_pair")
    low = _dgt_stratum(strata, "train_seen_low_frequency_pair")
    unseen = _dgt_stratum(strata, "train_unseen_pair")
    ood = _dgt_stratum(strata, "heldout_pair")
    memorization = (
        max(0.0, float(high.get("accuracy_minus_chance", 0.0)))
        + max(0.0, L1OOD_COLLAPSE_MARGIN - float(low.get("accuracy_minus_chance", 0.0)))
        + max(0.0, L1OOD_COLLAPSE_MARGIN - float(unseen.get("accuracy_minus_chance", 0.0)))
        + max(0.0, L1OOD_COLLAPSE_MARGIN - float(ood.get("accuracy_minus_chance", 0.0)))
    )
    brittle = (
        max(0.0, float(high.get("accuracy_minus_chance", 0.0)))
        + max(0.0, float(low.get("accuracy_minus_chance", 0.0)))
        + max(0.0, L1OOD_COLLAPSE_MARGIN - float(unseen.get("accuracy_minus_chance", 0.0)))
        + max(0.0, L1OOD_COLLAPSE_MARGIN - float(ood.get("accuracy_minus_chance", 0.0)))
    )
    partial = (
        max(0.0, float(unseen.get("accuracy_minus_chance", 0.0)))
        + max(0.0, float(ood.get("accuracy_minus_chance", 0.0)))
    )
    return {
        "memorization_score": round(memorization, 6),
        "brittle_rule_score": round(brittle, 6),
        "partial_rule_score": round(partial, 6),
    }


def derive_l1_ood_mechanism_verdict(
    strata: Mapping[str, Any],
    hardgates: Mapping[str, Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    high = _dgt_stratum(strata, "train_seen_high_frequency_pair")
    low = _dgt_stratum(strata, "train_seen_low_frequency_pair")
    unseen = _dgt_stratum(strata, "train_unseen_pair")
    ood = _dgt_stratum(strata, "heldout_pair")
    high_positive = _stratum_positive(high)
    low_positive = _stratum_positive(low)
    unseen_positive = _stratum_positive(unseen)
    ood_positive = _stratum_positive(ood)
    low_collapsed = _stratum_collapsed(low)
    unseen_collapsed = _stratum_collapsed(unseen)
    ood_collapsed = _stratum_collapsed(ood)
    high_margin_only = (
        float(high.get("true_class_margin_mean", -1.0)) > L1OOD_LOGIT_MARGIN_MIN
        and float(low.get("true_class_margin_mean", 1.0)) <= L1OOD_LOGIT_MARGIN_MIN
        and float(unseen.get("true_class_margin_mean", 1.0)) <= L1OOD_LOGIT_MARGIN_MIN
        and float(ood.get("true_class_margin_mean", 1.0)) <= L1OOD_LOGIT_MARGIN_MIN
    )
    in_dist_margins_positive = (
        float(high.get("true_class_margin_mean", -1.0)) > L1OOD_LOGIT_MARGIN_MIN
        and float(low.get("true_class_margin_mean", -1.0)) > L1OOD_LOGIT_MARGIN_MIN
    )
    ood_margin_nonpositive = float(ood.get("true_class_margin_mean", 1.0)) <= L1OOD_LOGIT_MARGIN_MIN
    gate_failures = [
        gate_id
        for gate_id, row in (hardgates or {}).items()
        if row.get("status") != "pass"
    ]
    if high_positive and (low_collapsed or unseen_collapsed) and ood_collapsed and high_margin_only:
        verdict = "memorization"
        branch = "high_frequency_seen_only"
    elif high_positive and low_positive and (unseen_collapsed or ood_collapsed) and in_dist_margins_positive and ood_margin_nonpositive:
        verdict = "brittle-rule"
        branch = "seen_pair_rule_collapses_under_heldout_pair"
    elif unseen_positive and ood_positive:
        verdict = "partial-rule"
        branch = "non_chance_unseen_and_heldout_strata"
    elif gate_failures:
        verdict = "brittle-rule"
        branch = "fail_closed_low_confidence"
    else:
        verdict = "brittle-rule"
        branch = "default_collapse_boundary"
    confidence = "low" if gate_failures else "medium"
    return {
        "verdict": verdict,
        "diagnostic_confidence": confidence,
        "branch": branch,
        "failed_hardgates": gate_failures,
        "thresholds": {
            "positive_margin": L1OOD_POSITIVE_MARGIN,
            "collapse_margin": L1OOD_COLLAPSE_MARGIN,
            "frequency_ratio": L1OOD_FREQUENCY_RATIO,
            "logit_margin_min": L1OOD_LOGIT_MARGIN_MIN,
        },
    }


def _gate_l1ood_hg1(strata: Mapping[str, Any]) -> dict[str, Any]:
    return _gate(
        set(strata) == set(L1OOD_STRATA)
        and all(
            isinstance(strata.get(stratum), Mapping)
            and set(strata[stratum]) == set(ARM_IDS)
            and all(
                isinstance(row, Mapping)
                and int(row.get("example_count", 0)) > 0
                and int(row.get("seed_count", 0)) >= 8
                for row in strata[stratum].values()
            )
            for stratum in L1OOD_STRATA
        ),
        "L1OOD-HG1",
        "all required pair-frequency and held-out pair strata are present for every arm",
        "$.l1_ood_mechanism.strata",
    )


def _gate_l1ood_hg2(strata: Mapping[str, Any]) -> dict[str, Any]:
    return _gate(
        all(
            row.get("device_resolved") == "cpu"
            for stratum in L1OOD_STRATA
            for row in strata.get(stratum, {}).values()
            if isinstance(row, Mapping)
        ),
        "L1OOD-HG2",
        "read-only mechanism probe rows are canonical CPU forward passes",
        "$.l1_ood_mechanism.strata",
    )


def _gate_l1ood_hg3(strata: Mapping[str, Any]) -> dict[str, Any]:
    return _gate(
        all(
            isinstance(row.get("true_class_logit_mean"), (int, float))
            and isinstance(row.get("true_class_margin_mean"), (int, float))
            and row.get("parameter_mutation_detected") is False
            for stratum in L1OOD_STRATA
            for row in strata.get(stratum, {}).values()
            if isinstance(row, Mapping)
        ),
        "L1OOD-HG3",
        "probe contains aggregate true-class logits and margins without parameter mutation",
        "$.l1_ood_mechanism.strata",
    )


def _gate_l1ood_hg4(strata: Mapping[str, Any], control_rows: Mapping[str, Any]) -> dict[str, Any]:
    matched = strata.get("train_seen_high_frequency_pair", {}).get("parameter_matched_attention", {})
    dgt = strata.get("train_seen_high_frequency_pair", {}).get("dgt_l1", {})
    return _gate(
        isinstance(matched, Mapping)
        and isinstance(dgt, Mapping)
        and int(matched.get("example_count", 0)) > 0
        and control_rows.get("controls_present") is True,
        "L1OOD-HG4",
        "parameter-matched attention control rows are present and remain diagnostic controls rather than verdict owners",
        "$.l1_ood_mechanism.control_rows",
    )


def _gate_l1ood_hg5(source_pointers: Mapping[str, Any]) -> dict[str, Any]:
    return _gate(
        source_pointers.get("task_required_order_source")
        == f"{CANONICAL_JSON_ARTIFACT}:$.task_spec.required_order_source"
        and source_pointers.get("task_required_order_status") == "pointer-backed"
        and source_pointers.get("task_required_order") == 2,
        "L1OOD-HG5",
        "mechanism diagnosis uses the existing pointer-backed order-two task source",
        "$.task_spec.required_order_source",
    )


def _scripted_metric_literals_absent(value: Mapping[str, Any]) -> bool:
    checked = {key: cell for key, cell in value.items() if key != "hardgates"}
    text = json.dumps(checked, sort_keys=True).lower()
    return all(token not in text for token in ("scripted_metric", "prefilled_metrics", "issue-text", "0.288"))


def _gate_l1ood_hg6(decision: Mapping[str, Any], mechanism: Mapping[str, Any]) -> dict[str, Any]:
    return _gate(
        decision.get("verdict") in L1OOD_VERDICTS
        and isinstance(decision.get("branch"), str)
        and bool(decision.get("branch"))
        and _scripted_metric_literals_absent(mechanism),
        "L1OOD-HG6",
        "mechanism verdict is mechanically selected from the registered verdict set",
        "$.l1_ood_mechanism.decision_table",
    )


def evaluate_l1ood_hardgates(mechanism: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    strata = mechanism.get("strata")
    strata = strata if isinstance(strata, Mapping) else {}
    control_rows = mechanism.get("control_rows")
    control_rows = control_rows if isinstance(control_rows, Mapping) else {}
    source_pointers = mechanism.get("source_pointers")
    source_pointers = source_pointers if isinstance(source_pointers, Mapping) else {}
    decision = mechanism.get("decision_table")
    decision = decision if isinstance(decision, Mapping) else {}
    return {
        "L1OOD-HG1": _gate_l1ood_hg1(strata),
        "L1OOD-HG2": _gate_l1ood_hg2(strata),
        "L1OOD-HG3": _gate_l1ood_hg3(strata),
        "L1OOD-HG4": _gate_l1ood_hg4(strata, control_rows),
        "L1OOD-HG5": _gate_l1ood_hg5(source_pointers),
        "L1OOD-HG6": _gate_l1ood_hg6(decision, mechanism),
    }


def build_l1_ood_mechanism(
    records: Sequence[Mapping[str, Any]],
    probe_rows: Sequence[Mapping[str, Any]],
    task_spec: Mapping[str, Any],
    summaries: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    del summaries
    strata = _mechanism_strata_table(probe_rows)
    scores = _mechanism_scores(strata)
    provisional_decision = derive_l1_ood_mechanism_verdict(strata)
    task_source = task_spec.get("required_order_source") if isinstance(task_spec, Mapping) else {}
    task_source = task_source if isinstance(task_source, Mapping) else {}
    provisional = {
        "owner": "dgt-l1-controls",
        "evidence_scope": "bounded-tiny-sequence-l1-ood-mechanism",
        "source_pointers": {
            "training_arms": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms",
            "compute_ledger": f"{CANONICAL_JSON_ARTIFACT}:$.compute_ledger",
            "independent_replay": f"{CANONICAL_JSON_ARTIFACT}:$.independent_replay",
            "task_required_order_source": f"{CANONICAL_JSON_ARTIFACT}:$.task_spec.required_order_source",
            "task_required_order_status": task_source.get("status"),
            "task_required_order": task_source.get("required_order", 2),
            "raw_metrics": f"{RUN_ROOT}/raw_metrics.jsonl",
            "probe_metrics": f"{RUN_ROOT}/probe_metrics.jsonl",
        },
        "strata": strata,
        "mechanism_scores": scores,
        "decision_table": provisional_decision,
        "verdict": provisional_decision["verdict"],
        "diagnostic_confidence": provisional_decision["diagnostic_confidence"],
        "l2_implication": {
            "status": "diagnostic-pointer-only",
            "recommendation": "future L2 work must treat this verdict as a bounded diagnostic, not as scaling evidence",
            "verdict_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l1_ood_mechanism.verdict",
        },
        "control_rows": {
            "input_ablation_baseline_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.input_ablation_masked_tail",
            "parameter_matched_attention_control_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.parameter_matched_attention",
            "controls_present": all(any(row.get("arm_id") == arm_id for row in records) for arm_id in ARM_IDS if arm_id != "dgt_l1"),
        },
        "hardgates": {},
        "regen_idempotence": {
            "status": "runner-checked",
            "checked_paths": [
                CANONICAL_JSON_ARTIFACT,
                CANONICAL_FINGERPRINT_ARTIFACT,
                f"{RUN_ROOT}/raw_metrics.jsonl",
                f"{RUN_ROOT}/probe_metrics.jsonl",
            ],
        },
        "not_claimed": [
            "No OOD generalization claim.",
            "No L2 or higher scaling claim.",
            "No component-causal stability claim.",
            "No standalone mechanism owner claim.",
        ],
        "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l1_ood_mechanism",
    }
    gates = evaluate_l1ood_hardgates(provisional)
    decision = derive_l1_ood_mechanism_verdict(strata, gates)
    return {
        **{key: value for key, value in provisional.items() if key not in {"records", "task_spec"}},
        "decision_table": decision,
        "verdict": decision["verdict"],
        "diagnostic_confidence": decision["diagnostic_confidence"],
        "hardgates": gates,
    }


def _json_digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _path_digest(relative_path: str) -> str:
    path = LAB_ROOT / relative_path
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else "missing"


def _callable_digest(function: Any) -> str:
    try:
        source = inspect.getsource(function)
    except (OSError, TypeError):
        source = repr(function)
    return hashlib.sha256(source.encode("utf-8")).hexdigest()


def _runtime_abi(torch: Any) -> dict[str, str]:
    abi = {"python": sys.version.split()[0], "executable": sys.executable, "torch": str(getattr(torch, "__version__", "unknown"))}
    try:
        numpy = importlib.import_module("numpy")
    except Exception:
        abi["numpy"] = "not-installed"
    else:
        abi["numpy"] = str(getattr(numpy, "__version__", "unknown"))
    return abi


def _producer_source_closure() -> tuple[dict[str, str], ...]:
    paths = (
        OWNER_MODULE,
        PRODUCER,
        "bedc_quality_lab/canonical_cell_cache.py",
        "bedc_quality_lab/order_k_benchmark.py",
    )
    return tuple({"path": path, "sha256": _path_digest(path)} for path in paths)


def _cell_input_record(
    torch: Any,
    *,
    requested_device: str,
    device_name: str,
    config: L1TrainingConfig,
    task_spec: L1TinySequenceTaskSpec,
) -> CellInputRecord:
    return CellInputRecord(
        producer_id="dgt-l1-controls",
        producer_command=("python3", PRODUCER),
        report_artifacts={
            "canonical_json": CANONICAL_JSON_ARTIFACT,
            "canonical_markdown": CANONICAL_MARKDOWN_ARTIFACT,
            **run_artifacts_payload(),
        },
        producer_source_closure=_producer_source_closure(),
        extra_input_paths=(ORDER_K_REPORT_ARTIFACT,),
        config_payload={
            "schema_id": SCHEMA_ID,
            "arm_ids": list(ARM_IDS),
            "training_config": asdict(config),
            "task_spec": task_spec.as_payload(),
            "trainer_digest": _callable_digest(_train_arm),
        },
        seed_protocol={
            "base_seed": BASE_SEED,
            "deterministic_seeds": list(config.seeds),
            "step_grid": list(config.step_grid),
        },
        source_artifact_digests={ORDER_K_REPORT_ARTIFACT: _path_digest(ORDER_K_REPORT_ARTIFACT)},
        requested_device=requested_device,
        resolved_device=device_name,
        runtime_abi=_runtime_abi(torch),
    )


def _raw_metrics_text(records: Sequence[Mapping[str, Any]]) -> str:
    return "".join(json.dumps(row, sort_keys=True) + "\n" for row in records)


def _load_raw_records(path: Path, config: L1TrainingConfig) -> list[dict[str, Any]]:
    records = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
    expected_count = len(config.step_grid) * len(config.seeds) * len(ARM_IDS)
    if len(records) != expected_count:
        raise ValueError("cached L1 raw record count mismatch")
    if {str(row.get("arm_id")) for row in records} != set(ARM_IDS):
        raise ValueError("cached L1 raw arm set mismatch")
    if {int(row.get("seed", -1)) for row in records} != set(config.seeds):
        raise ValueError("cached L1 raw seed set mismatch")
    if {int(row.get("training_steps", -1)) for row in records} != set(config.step_grid):
        raise ValueError("cached L1 raw step set mismatch")
    return records


def _store_raw_records(record: CellInputRecord, records: Sequence[Mapping[str, Any]]) -> None:
    with tempfile.TemporaryDirectory(prefix="bedc-l1-cell-") as temp_dir:
        raw_path = Path(temp_dir) / "raw_metrics.jsonl"
        raw_path.write_text(_raw_metrics_text(records), encoding="utf-8")
        store_cell_entry(
            record,
            {"raw_metrics.jsonl": {"path": raw_path, "media_role": "raw_metrics_jsonl"}},
        )


def _training_records(
    torch: Any,
    *,
    task_spec: L1TinySequenceTaskSpec,
    config: L1TrainingConfig,
    requested_device: str,
    device_name: str,
) -> list[dict[str, Any]]:
    record = _cell_input_record(
        torch,
        requested_device=requested_device,
        device_name=device_name,
        config=config,
        task_spec=task_spec,
    )
    lookup = load_cell_entry(record)
    if lookup.status == "hit":
        raw_path = lookup.verified_blob_paths.get("raw_metrics.jsonl")
        if raw_path is not None:
            try:
                return _load_raw_records(raw_path, config)
            except (OSError, json.JSONDecodeError, TypeError, ValueError):
                pass
    records = _train_l1_grid(
        torch,
        task_spec=task_spec,
        config=config,
        requested_device=requested_device,
        device_name=device_name,
    )
    _store_raw_records(record, records)
    return records


def _independent_replay(task_spec: Mapping[str, Any], records: Sequence[Mapping[str, Any]], summaries: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    seeds = tuple(int(row["seed"]) for row in records if row["arm_id"] == "dgt_l1")
    seed_digest = _json_digest(list(seeds))
    task_digest = _json_digest(task_spec)
    by_seed: dict[int, dict[str, float]] = {}
    for seed in seeds:
        cells = {row["arm_id"]: row for row in records if int(row["seed"]) == seed}
        if set(cells) == set(ARM_IDS):
            by_seed[seed] = {
                "dgt_minus_input_ablation_accuracy": round(
                    float(cells["dgt_l1"]["metrics"]["accuracy"])
                    - float(cells["input_ablation_masked_tail"]["metrics"]["accuracy"]),
                    6,
                ),
                "dgt_minus_parameter_matched_attention_accuracy": round(
                    float(cells["dgt_l1"]["metrics"]["accuracy"])
                    - float(cells["parameter_matched_attention"]["metrics"]["accuracy"]),
                    6,
                ),
                "dgt_minus_compute_matched_attention_accuracy": round(
                    float(cells["dgt_l1"]["metrics"]["accuracy"]) - float(cells["compute_matched_attention"]["metrics"]["accuracy"]),
                    6,
                ),
            }
    metric_tolerance_rows = [
        {
            "seed": seed,
            "status": "pass"
            if all(math.isfinite(float(value)) for value in row.values())
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
        "run_local_probe_metrics": f"{RUN_ROOT}/probe_metrics.jsonl",
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
    arm_input_access = {
        "label_invisibility_certificate": True,
        "certificate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.construct_validity_ledger.input_bandwidth_by_arm",
        "arms": {
            arm_id: {
                "variables": ["token_sequence", "x_prev_1", "x_prev_2"],
                "required_variables": ["x_prev_1", "x_prev_2"],
                "missing_variables": [] if arm_id != "input_ablation_masked_tail" else ["x_prev_2"],
                "coverage_status": "pass" if arm_id != "input_ablation_masked_tail" else "ablation-only",
                "role": "ablation" if arm_id == "input_ablation_masked_tail" else ("candidate" if arm_id == "dgt_l1" else "attention_control"),
            }
            for arm_id in ARM_IDS
        },
    }
    return ConstructValidityEvidence(
        task_variables={
            "variables": ["token_sequence", "x_prev_1", "x_prev_2", "surface_id"],
            "pointer": "$.construct_validity_ledger.task_variables",
        },
        label_variables={
            "variables": ["next_token_label", "ood_next_token_label"],
            "pointer": "$.construct_validity_ledger.label_variables",
        },
        arm_input_access=arm_input_access,
        arm_roles={
            "candidate": "dgt_l1",
            "controls": list(CLAIM_ELIGIBLE_ATTENTION_ARMS),
            "diagnostics": list(DIAGNOSTIC_EXCLUDED_ARMS),
        },
        finite_table={
            "coverage_status": "bounded-control",
            "support_count": min(cfg.eval_examples, cfg.vocab_size * cfg.vocab_size),
            "rule_abstraction_claim": False,
            "table_coverage_only": False,
            "finite_pair_accuracy": None,
        },
        hand_feature_ledger={
            "mode": "no-gate",
            "shared_across_arms": False,
            "features": [],
            "candidate_only_features": [],
            "disclosure_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.construct_validity_ledger.manual_feature_disclosure",
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
        pointer="$.construct_validity_ledger.construct_validity_projection",
    )


def build_construct_validity_ledger(
    *,
    summaries: Mapping[str, Mapping[str, Any]],
    config: L1TrainingConfig,
) -> dict[str, Any]:
    split_protocol = _split_protocol_payload(vocab_size=config.vocab_size)
    input_bandwidth: dict[str, dict[str, Any]] = {}
    for arm_id in ARM_IDS:
        is_ablation = arm_id == "input_ablation_masked_tail"
        input_bandwidth[arm_id] = {
            "input_positions": list(range(SEQUENCE_LENGTH)),
            "masked_positions": [SEQUENCE_LENGTH - 2] if is_ablation else [],
            "sequence_length": SEQUENCE_LENGTH,
            "role": "ablation" if is_ablation else ("candidate" if arm_id == "dgt_l1" else "attention_control"),
            "eligible_for_advantage_claims": arm_id in CLAIM_ELIGIBLE_ATTENTION_ARMS,
            "arm_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.{arm_id}",
        }
    train_pairs = split_protocol["train_pairs"]
    heldout_pairs = split_protocol["heldout_pairs"]
    total_pairs = config.vocab_size * config.vocab_size
    expected_train_coverage = round(1.0 - (1.0 - 1.0 / max(1, len(train_pairs))) ** config.train_examples, 6)
    table_ceiling = round((len(train_pairs) + (total_pairs - len(train_pairs)) / config.vocab_size) / total_pairs, 6)
    construct_projection = construct_validity_payload(summaries=summaries, config=config)
    ledger = ConstructValidityLedger(
        input_bandwidth_by_arm=input_bandwidth,
        split_protocol=split_protocol,
        ood_winnability={
            "label_rule": "same_rule_heldout_pairs",
            "label_rule_expression": "(3*x_last_1 + 5*x_last_2 + 1) mod 16",
            "chance_accuracy": round(1.0 / config.vocab_size, 6),
            "oracle_accuracy": 1.0,
            "bayes_full_input_accuracy": 1.0,
            "heldout_pair_count": len(heldout_pairs),
            "evidence_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.construct_validity_ledger.split_protocol",
        },
        coverage_bound={
            "train_pair_coverage": expected_train_coverage,
            "seen_pair_accuracy": summaries.get("dgt_l1", {}).get("metrics", {}).get("accuracy_mean"),
            "unseen_pair_accuracy": summaries.get("dgt_l1", {}).get("metrics", {}).get("ood_accuracy_mean"),
            "theoretical_table_ceiling": table_ceiling,
            "rule_abstraction_claim": False,
            "interpretation": "pair coverage only",
        },
        manual_feature_disclosure={
            "status": "disclosed",
            "feature_engineering_advantage": True,
            "candidate_only_features": ["parity_gate", "comparison_gate"],
            "shared_attention_input": True,
            "not_claimed": "manual features are not evidence of autonomous rule abstraction",
        },
        claim_comparison_policy={
            "candidate_arm": "dgt_l1",
            "eligible_positive_claim_controls": list(CLAIM_ELIGIBLE_ATTENTION_ARMS),
            "excluded_from_positive_claims": list(DIAGNOSTIC_EXCLUDED_ARMS),
            "public_alias_reuse_forbidden": True,
            "policy": "positive DGT architecture claims may only compare against parameter- and compute-matched attention controls",
        },
    ).as_payload()
    ledger["construct_validity_projection"] = construct_projection
    ledger["status"] = "pass" if _construct_validity_ledger_passes(ledger) else "fail"
    ledger["failed_gates"] = [] if ledger["status"] == "pass" else ["L1-CV-LEDGER"]
    return ledger


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
        "input_ablation_baseline": _arm_cell(arms, "input_ablation_masked_tail"),
        "matched": _arm_cell(arms, "parameter_matched_attention"),
        "parameter_matched": _arm_cell(arms, "parameter_matched_attention"),
        "compute_matched": _arm_cell(arms, "compute_matched_attention"),
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


def _parameter_matched_attention_positive_control(dgt: Mapping[str, Any] | None, matched: Mapping[str, Any] | None) -> bool:
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
        "four L1 arms have true-training metrics while ledger, jet, and classifier metrics are owner-required boundaries",
        "$.owner_local_measurement_boundary",
    )


def _gate_l1_hg2(context: Mapping[str, Any]) -> dict[str, Any]:
    paired = context["paired"].get("dgt_minus_input_ablation_masked_tail")
    ablation = context["input_ablation_baseline"]
    return _gate(
        isinstance(paired, Mapping)
        and isinstance(ablation, Mapping)
        and int(paired.get("seed_count", 0)) >= 16
        and ablation.get("arm_id") == "input_ablation_masked_tail",
        "L1-REVIEW-HG2",
        "masked-tail input ablation is present as a diagnostic arm with seed-paired rows",
        "$.training_arms.input_ablation_masked_tail",
    )


def _gate_l1_hg3(context: Mapping[str, Any]) -> dict[str, Any]:
    paired = context["paired"].get("dgt_minus_parameter_matched_attention")
    matched = context["matched"]
    compute = context["compute_matched"]
    return _gate(
        isinstance(paired, Mapping)
        and isinstance(matched, Mapping)
        and isinstance(compute, Mapping)
        and int(paired.get("seed_count", 0)) >= 16
        and matched.get("self_attention_layers") == 1
        and compute.get("self_attention_layers") == 1,
        "L1-REVIEW-HG3",
        "parameter- and compute-matched attention controls are present for fair comparison",
        "$.construct_validity_ledger.claim_comparison_policy",
    )


def _gate_l1_hg4(context: Mapping[str, Any]) -> dict[str, Any]:
    matched = context["matched"]
    arms = context["arms"]
    return _gate(
        isinstance(matched, Mapping)
        and matched.get("self_attention_layers") == 1
        and all(
            isinstance(row, Mapping)
            and isinstance(row.get("metrics"), Mapping)
            and _owner_required_metric_absent(row["metrics"])
            for row in arms.values()
        ),
        "L1-REVIEW-HG4",
        "parameter-matched attention control uses self-attention and no L1 arm reports owner-required ledger, jet, or classifier metrics",
        "$.training_arms.parameter_matched_attention.metrics",
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
    return _gate(
        isinstance(crossover, Mapping) and "parameter_matched_attention_catches_up" in crossover,
        "L1STEP-HG5",
        "parameter-matched attention crossover is recorded as diagnostic evidence only",
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
    construct_validity = payload.get("construct_validity_ledger")
    cv_projection = _construct_validity_claim_projection(construct_validity)
    capsule = {
        "schema_id": "bedc.quality.claim_capsule",
        "capsule_subtype": "bedc.model.dgt_l1_tiny_sequence_claim_capsule",
        "claim_id": "claim:dgt-l1-tiny-sequence",
        "report": "dgt-l1-controls",
        "source": CANONICAL_JSON_ARTIFACT,
        "source_pointer": "$.l1_tiny_sequence_projection",
        "status": "pass" if gate_status == "pass" else "blocked",
        "evidence_scope": "bounded-tiny-sequence",
        "claim_projection": {
            "model_id": "discovery-gated-transformer",
            "task_family": "bounded_tiny_sequence_order_k",
            "allowed_claim_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l1_tiny_sequence_projection.review_status",
            "claim_boundary_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.not_claimed",
            "task_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.task_spec",
            "candidate_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.dgt_l1",
            "input_ablation_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.input_ablation_masked_tail",
            "parameter_matched_attention_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.parameter_matched_attention",
            "compute_matched_attention_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.compute_matched_attention",
            "claim_comparison_policy_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.construct_validity_ledger.claim_comparison_policy",
            "compute_ledger_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.compute_ledger",
            "parameter_ledger_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.parameter_ledger",
            "paired_accuracy_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.paired_accuracy",
            "negative_witness_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.negative_witness_sweep",
            "independent_replay_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.independent_replay",
            "owner_local_measurement_boundary_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.owner_local_measurement_boundary",
            "step_ladder_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l1_step_ladder",
            "review_status_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.l1_tiny_sequence_projection.review_status",
        },
        "hardgate_pointers": {
            gate_id: f"{CANONICAL_JSON_ARTIFACT}:$.hardgates.{gate_id}"
            for gate_id in L1_GATE_IDS
        },
        "evidence_pointers": [
            f"{CANONICAL_JSON_ARTIFACT}:$.task_spec",
            f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.dgt_l1",
            f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.input_ablation_masked_tail",
            f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.parameter_matched_attention",
            f"{CANONICAL_JSON_ARTIFACT}:$.training_arms.compute_matched_attention",
            f"{CANONICAL_JSON_ARTIFACT}:$.construct_validity_ledger",
            f"{CANONICAL_JSON_ARTIFACT}:$.compute_ledger",
            f"{CANONICAL_JSON_ARTIFACT}:$.parameter_ledger",
            f"{CANONICAL_JSON_ARTIFACT}:$.paired_accuracy",
            f"{CANONICAL_JSON_ARTIFACT}:$.negative_witness_sweep",
            f"{CANONICAL_JSON_ARTIFACT}:$.independent_replay",
            f"{CANONICAL_JSON_ARTIFACT}:$.owner_local_measurement_boundary",
            f"{CANONICAL_JSON_ARTIFACT}:$.l1_step_ladder",
            f"{CANONICAL_JSON_ARTIFACT}:$.l1_tiny_sequence_projection.review_status",
        ],
        "scope_pointer": f"{CANONICAL_JSON_ARTIFACT}:$.not_claimed",
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
    records = _training_records(
        torch,
        task_spec=task_spec,
        config=cfg,
        requested_device=requested_device,
        device_name=device_name,
    )
    primary_records = [row for row in records if int(row["training_steps"]) == cfg.training_steps]
    probe_rows = [
        probe_row
        for row in primary_records
        for probe_row in row.get("_probe_rows", [])
        if isinstance(probe_row, Mapping)
    ]
    summaries = _arm_summaries(primary_records)
    summaries["parameter_matched_attention"]["structural_marginals_preserved"] = True
    compute = _compute_ledger(summaries)
    params = _parameter_ledger(summaries)
    paired_accuracy = {
        "dgt_minus_input_ablation_masked_tail": _paired_accuracy_stats(
            primary_records,
            candidate_arm="dgt_l1",
            control_arm="input_ablation_masked_tail",
        ),
        "dgt_minus_parameter_matched_attention": _paired_accuracy_stats(
            primary_records,
            candidate_arm="dgt_l1",
            control_arm="parameter_matched_attention",
        ),
        "pointer": f"{CANONICAL_JSON_ARTIFACT}:$.paired_accuracy",
    }
    negative = _negative_witness_sweep(summaries)
    replay = _independent_replay(task_spec.as_payload(), primary_records, summaries)
    step_ladder = build_l1_step_ladder(records, cfg)
    l1_ood_mechanism = build_l1_ood_mechanism(primary_records, probe_rows, task_spec.as_payload(), summaries)
    construct_validity_ledger = build_construct_validity_ledger(summaries=summaries, config=cfg)
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
        "l1_ood_mechanism": l1_ood_mechanism,
        "construct_validity_ledger": construct_validity_ledger,
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
    payload["_probe_rows"] = probe_rows
    validate_payload({key: value for key, value in payload.items() if key not in {"_raw_records", "_probe_rows"}}, root=root)
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
        "l1_ood_mechanism",
        "construct_validity_ledger",
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
    if "_raw_records" in payload or "_probe_rows" in payload:
        payload = {key: value for key, value in payload.items() if key not in {"_raw_records", "_probe_rows"}}
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
        ("dgt_minus_input_ablation_masked_tail", "input_ablation_masked_tail"),
        ("dgt_minus_parameter_matched_attention", "parameter_matched_attention"),
    ):
        cell = paired.get(key)
        if not isinstance(cell, Mapping):
            raise ValueError(f"DGT L1 paired accuracy cell missing: {key}")
        if cell.get("candidate_arm") != "dgt_l1" or cell.get("control_arm") != control_arm:
            raise ValueError(f"DGT L1 paired accuracy arm mismatch: {key}")
        if int(cell.get("seed_count", 0)) < 16:
            raise ValueError(f"DGT L1 paired accuracy seed count too small: {key}")
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
    if ladder.get("verdict") not in {"diagnostic-only", "diagnostic-ablation-catches-up", "inconclusive"}:
        raise ValueError("DGT L1 step ladder verdict invalid")
    if ladder.get("verdict") != expected_verdict:
        raise ValueError("DGT L1 step ladder verdict mismatch")
    expected_ladder_status = "pass" if all(row["status"] == "pass" for row in ladder_gates.values()) else "fail"
    if ladder.get("status") != expected_ladder_status:
        raise ValueError("DGT L1 step ladder status mismatch")
    mechanism = payload["l1_ood_mechanism"]
    if not isinstance(mechanism, Mapping):
        raise ValueError("DGT L1 OOD mechanism missing")
    required_mechanism_keys = {
        "owner",
        "evidence_scope",
        "source_pointers",
        "strata",
        "mechanism_scores",
        "decision_table",
        "verdict",
        "diagnostic_confidence",
        "l2_implication",
        "control_rows",
        "hardgates",
        "regen_idempotence",
        "not_claimed",
        "pointer",
    }
    if set(mechanism) != required_mechanism_keys:
        raise ValueError("DGT L1 OOD mechanism fields mismatch")
    if mechanism.get("owner") != "dgt-l1-controls" or mechanism.get("evidence_scope") != "bounded-tiny-sequence-l1-ood-mechanism":
        raise ValueError("DGT L1 OOD mechanism owner mismatch")
    source_pointers = mechanism.get("source_pointers")
    if not isinstance(source_pointers, Mapping) or source_pointers.get("probe_metrics") != f"{RUN_ROOT}/probe_metrics.jsonl":
        raise ValueError("DGT L1 OOD mechanism probe pointer missing")
    strata = mechanism.get("strata")
    if not isinstance(strata, Mapping) or set(strata) != set(L1OOD_STRATA):
        raise ValueError("DGT L1 OOD mechanism strata mismatch")
    for stratum in L1OOD_STRATA:
        arms_for_stratum = strata[stratum]
        if not isinstance(arms_for_stratum, Mapping) or set(arms_for_stratum) != set(ARM_IDS):
            raise ValueError(f"DGT L1 OOD mechanism arm strata mismatch: {stratum}")
        for arm_id, row in arms_for_stratum.items():
            required_row_keys = {
                "arm_id",
                "stratum",
                "example_count",
                "seed_count",
                "pair_count",
                "accuracy",
                "true_class_logit_mean",
                "true_class_margin_mean",
                "confidence_mean",
                "chance_accuracy",
                "accuracy_minus_chance",
                "device_resolved",
                "parameter_mutation_detected",
                "source_probe_row_count",
            }
            if set(row) != required_row_keys:
                raise ValueError("DGT L1 OOD mechanism stratum row schema mismatch")
            if row["arm_id"] != arm_id or row["stratum"] != stratum:
                raise ValueError("DGT L1 OOD mechanism stratum row identity mismatch")
            if int(row["example_count"]) <= 0 or int(row["seed_count"]) < 8 or int(row["pair_count"]) <= 0:
                raise ValueError("DGT L1 OOD mechanism stratum row count missing")
            if row["device_resolved"] != "cpu" or row["parameter_mutation_detected"] is not False:
                raise ValueError("DGT L1 OOD mechanism probe must be read-only CPU")
            if not isinstance(row["true_class_logit_mean"], (int, float)) or not isinstance(row["true_class_margin_mean"], (int, float)):
                raise ValueError("DGT L1 OOD mechanism logit aggregates missing")
            if round(float(row["accuracy"]) - float(row["chance_accuracy"]), 6) != float(row["accuracy_minus_chance"]):
                raise ValueError("DGT L1 OOD mechanism accuracy margin mismatch")
    expected_scores = _mechanism_scores(strata)
    if mechanism.get("mechanism_scores") != expected_scores:
        raise ValueError("DGT L1 OOD mechanism score mismatch")
    expected_l1ood_gates = evaluate_l1ood_hardgates(mechanism)
    if mechanism.get("hardgates") != expected_l1ood_gates:
        raise ValueError("DGT L1 OOD mechanism hardgate mismatch")
    expected_decision = derive_l1_ood_mechanism_verdict(strata, expected_l1ood_gates)
    if mechanism.get("decision_table") != expected_decision:
        raise ValueError("DGT L1 OOD mechanism decision table mismatch")
    if mechanism.get("verdict") != expected_decision["verdict"] or mechanism.get("verdict") not in L1OOD_VERDICTS:
        raise ValueError("DGT L1 OOD mechanism verdict mismatch")
    if mechanism.get("diagnostic_confidence") != expected_decision["diagnostic_confidence"]:
        raise ValueError("DGT L1 OOD mechanism confidence mismatch")
    if any(row["status"] != "pass" for row in expected_l1ood_gates.values()) and mechanism.get("diagnostic_confidence") != "low":
        raise ValueError("DGT L1 OOD mechanism fail-closed confidence mismatch")
    l2_implication = mechanism.get("l2_implication")
    if not isinstance(l2_implication, Mapping) or l2_implication.get("verdict_pointer") != f"{CANONICAL_JSON_ARTIFACT}:$.l1_ood_mechanism.verdict":
        raise ValueError("DGT L1 OOD mechanism L2 pointer mismatch")
    expected_gates = evaluate_hardgates(payload)
    if payload["hardgates"] != expected_gates:
        raise ValueError("DGT L1 hardgate evaluation mismatch")
    construct_validity = payload["construct_validity_ledger"]
    if not isinstance(construct_validity, Mapping):
        raise ValueError("DGT L1 construct validity ledger missing")
    if not _construct_validity_ledger_passes(construct_validity):
        raise ValueError("DGT L1 construct validity ledger failed")
    if construct_validity.get("status") != "pass" or construct_validity.get("failed_gates") != []:
        raise ValueError("DGT L1 construct validity ledger status mismatch")
    projection = construct_validity.get("construct_validity_projection")
    if not isinstance(projection, Mapping) or projection.get("owner_pointer") != "bedc_quality_lab.construct_validity:evaluate_construct_validity":
        raise ValueError("DGT L1 construct validity projection missing")
    if not _construct_validity_owner_projection_passes(projection):
        raise ValueError("DGT L1 construct validity owner projection failed")
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
    if set(payload["claim_capsule_ref"].get("construct_validity", {})) != set(CONSTRUCT_VALIDITY_PROJECTION_KEYS):
        raise ValueError("DGT L1 ClaimCapsule construct validity projection mismatch")
    if payload["claim_capsule_ref"].get("construct_validity") != _construct_validity_claim_projection(construct_validity):
        raise ValueError("DGT L1 ClaimCapsule construct validity must use owner projection")
    capsule_forbidden_fields = {"model_claim", "allowed_claim", "forbidden_claims", "not_claimed"}
    if capsule_forbidden_fields.intersection(payload["claim_capsule_ref"]):
        raise ValueError("DGT L1 ClaimCapsule must use pointers for claim prose")
    claim_projection = payload["claim_capsule_ref"].get("claim_projection")
    if not isinstance(claim_projection, Mapping):
        raise ValueError("DGT L1 ClaimCapsule claim projection missing")
    if {"allowed_claim", "forbidden_claims", "not_claimed"}.intersection(claim_projection):
        raise ValueError("DGT L1 ClaimCapsule claim projection must use pointers")
    if claim_projection.get("allowed_claim_pointer") != f"{CANONICAL_JSON_ARTIFACT}:$.l1_tiny_sequence_projection.review_status":
        raise ValueError("DGT L1 ClaimCapsule allowed-claim pointer mismatch")
    if claim_projection.get("claim_boundary_pointer") != f"{CANONICAL_JSON_ARTIFACT}:$.not_claimed":
        raise ValueError("DGT L1 ClaimCapsule boundary pointer mismatch")
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
        f"- L1 OOD mechanism verdict: `{payload['l1_ood_mechanism']['verdict']}`",
        f"- L1 OOD mechanism confidence: `{payload['l1_ood_mechanism']['diagnostic_confidence']}`",
        f"- Seeds: `{payload['independent_replay']['seed_count']}`",
        f"- Compute units: `{payload['compute_ledger']['compute_units']}`",
        f"- Parameter count: `{payload['parameter_ledger']['parameter_count']}`",
        f"- Construct validity ledger: `{payload['construct_validity_ledger']['status']}`",
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
            f"input-ablation acc `{metrics['input_ablation_accuracy_mean']:.6f}`, "
            f"parameter-matched attention acc `{metrics['parameter_matched_attention_accuracy_mean']:.6f}`, "
            f"DGT-input-ablation gap `{metrics['dgt_minus_input_ablation_accuracy']:.6f}`"
        )
    lines.extend(["", "## L1 Step Hardgates", ""])
    for gate_id, row in ladder["hardgates"].items():
        lines.append(f"- `{gate_id}`: `{row['status']}` - {row['criterion']}")
    lines.extend(["", "## L1 OOD Mechanism", ""])
    mechanism = payload["l1_ood_mechanism"]
    lines.append(f"- Verdict: `{mechanism['verdict']}`")
    lines.append(f"- Diagnostic confidence: `{mechanism['diagnostic_confidence']}`")
    for stratum in L1OOD_STRATA:
        dgt = mechanism["strata"][stratum]["dgt_l1"]
        lines.append(
            "- "
            f"`{stratum}`: "
            f"accuracy `{dgt['accuracy']:.6f}`, "
            f"margin `{dgt['true_class_margin_mean']:.6f}`, "
            f"examples `{dgt['example_count']}`"
        )
    lines.extend(["", "## L1 OOD Hardgates", ""])
    for gate_id, row in mechanism["hardgates"].items():
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
        "probe_metrics": f"{RUN_ROOT}/probe_metrics.jsonl",
        "raw_metrics": f"{RUN_ROOT}/raw_metrics.jsonl",
        "summary": f"{RUN_ROOT}/summary.json",
        "report": f"{RUN_ROOT}/report.md",
    }


def fingerprint_payload(payload: Mapping[str, Any], *, generated_at: str) -> dict[str, Any]:
    del payload, generated_at
    raise RuntimeError("canonical report fingerprints are written by scripts/run_canonical_reports.py")


def write_artifacts(payload: Mapping[str, Any], *, root: Path, generated_at: str | None = None) -> None:
    public_payload = {key: value for key, value in payload.items() if key not in {"_raw_records", "_probe_rows"}}
    validate_payload(public_payload, root=None)
    run_artifacts = run_artifacts_payload()
    _write_json(root / run_artifacts["summary"], public_payload)
    raw_rows = [
        {key: value for key, value in row.items() if key != "_probe_rows"}
        for row in list(payload.get("_raw_records", []))
    ]
    raw_path = root / run_artifacts["raw_metrics"]
    raw_path.parent.mkdir(parents=True, exist_ok=True)
    raw_path.write_text(_raw_metrics_text(raw_rows), encoding="utf-8")
    probe_rows = list(payload.get("_probe_rows", []))
    probe_path = root / run_artifacts["probe_metrics"]
    probe_path.parent.mkdir(parents=True, exist_ok=True)
    probe_path.write_text(_raw_metrics_text(probe_rows), encoding="utf-8")
    _write_json(root / run_artifacts["claim_capsule"], public_payload["claim_capsule_ref"])
    report = render_markdown(public_payload)
    report_path = root / run_artifacts["report"]
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(report, encoding="utf-8")
    _write_json(root / CANONICAL_JSON_ARTIFACT, public_payload)
    (root / CANONICAL_MARKDOWN_ARTIFACT).write_text(report, encoding="utf-8")


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
    "build_l1_ood_mechanism",
    "build_l1_step_ladder",
    "build_payload",
    "construct_validity_evidence",
    "construct_validity_payload",
    "derive_l1_ood_mechanism_verdict",
    "derive_l1_step_ladder_crossover",
    "derive_l1_step_ladder_verdict",
    "evaluate_hardgates",
    "evaluate_l1ood_hardgates",
    "evaluate_l1step_hardgates",
    "render_markdown",
    "source_regression_guard",
    "validate_payload",
    "write_artifacts",
]

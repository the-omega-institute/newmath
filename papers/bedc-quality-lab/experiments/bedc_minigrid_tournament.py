"""Native MiniGrid BEDC-JEPA tournament.

The run compares a BEDC-JEPA objective against matched latent-only and
supervised-gap controls on native Gymnasium MiniGrid transitions.
"""

from __future__ import annotations

from dataclasses import dataclass
import argparse
import copy
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import time
from typing import Any

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.bedc_jepa_metrics import (
    bedc_debt_score,
    binary_accuracy,
    certified_coverage,
    gap_detection_auc,
    unlogged_error_rate,
)
from bedc_quality_lab.model import choose_device, covariance_loss, require_torch, set_deterministic_seed
from bedc_quality_lab.public_minigrid_native_benchmark import _door_key_labels


PYTHON_BIN = "/home/aruic-wsl/newmath/.venv/bin/python"
NVIDIA_SMI = "/usr/lib/wsl/lib/nvidia-smi"
REPORT_PATH = Path("reports/bedc_minigrid_tournament.json")
DEFAULT_TRAIN_ENV = "MiniGrid-DoorKey-6x6-v0"
DEFAULT_OOD_ENV = "MiniGrid-DoorKey-8x8-v0"
DEFAULT_SEEDS = (20260618, 20260619, 20260620)
ARM_NAMES = ("latent_only", "supervised_gap", "bedc_jepa")


@dataclass(frozen=True)
class Split:
    obs: np.ndarray
    actions: np.ndarray
    next_obs: np.ndarray
    labels: np.ndarray
    gaps: np.ndarray
    invalids: np.ndarray
    semantic_next: np.ndarray
    planning: list[dict[str, Any]]


@dataclass(frozen=True)
class RunData:
    train: Split
    validation: Split
    id_test: Split
    ood_test: Split
    action_count: int


class NvidiaMonitor:
    def __init__(self) -> None:
        self.path = Path(NVIDIA_SMI)
        self.process: subprocess.Popen[str] | None = None
        self.started = False

    def __enter__(self) -> "NvidiaMonitor":
        if self.path.exists():
            cmd = [
                str(self.path),
                "--query-gpu=timestamp,name,utilization.gpu,memory.used",
                "--format=csv,noheader,nounits",
                "-lms",
                "200",
            ]
            self.process = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
            )
            self.started = True
        return self

    def __exit__(self, exc_type: object, exc: object, tb: object) -> None:
        if self.process is not None:
            self.process.terminate()
            try:
                self.process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                self.process.kill()

    def collect(self) -> dict[str, Any]:
        lines: list[str] = []
        if self.process is not None and self.process.stdout is not None:
            try:
                while True:
                    line = self.process.stdout.readline()
                    if not line:
                        break
                    lines.append(line.strip())
                    if len(lines) >= 120:
                        break
            except Exception:
                pass
        parsed = [_parse_nvidia_line(line) for line in lines]
        parsed = [row for row in parsed if row is not None]
        return {
            "monitor_started": self.started,
            "sample_count": len(parsed),
            "max_gpu_utilization_percent": max((row["gpu_utilization_percent"] for row in parsed), default=0.0),
            "max_memory_used_mib": max((row["memory_used_mib"] for row in parsed), default=0.0),
            "samples": parsed[:20],
        }


def _parse_nvidia_line(line: str) -> dict[str, Any] | None:
    parts = [part.strip() for part in line.split(",")]
    if len(parts) != 4:
        return None
    try:
        return {
            "timestamp": parts[0],
            "gpu_name": parts[1],
            "gpu_utilization_percent": float(parts[2]),
            "memory_used_mib": float(parts[3]),
        }
    except ValueError:
        return None


def _nvidia_snapshot() -> dict[str, Any]:
    if not Path(NVIDIA_SMI).exists():
        return {"status": "missing", "path": NVIDIA_SMI}
    cmd = [
        NVIDIA_SMI,
        "--query-gpu=name,driver_version,utilization.gpu,memory.used,memory.total",
        "--format=csv,noheader,nounits",
    ]
    result = subprocess.run(cmd, check=False, capture_output=True, text=True)
    return {
        "status": "ok" if result.returncode == 0 else "error",
        "returncode": result.returncode,
        "stdout": result.stdout.strip(),
        "stderr": result.stderr.strip(),
    }


def _object_mask(image: np.ndarray, object_id: int) -> np.ndarray:
    return np.asarray(image)[:, :, 0] == object_id


def _agent_position(image: np.ndarray) -> np.ndarray:
    mask = _object_mask(image, 10)
    if np.any(mask):
        return np.argwhere(mask)[0].astype(np.float64)
    return np.asarray([3.0, 6.0], dtype=np.float64)


def _distance_to_object(image: np.ndarray, object_id: int) -> float:
    mask = _object_mask(image, object_id)
    if not np.any(mask):
        return 10.0
    points = np.argwhere(mask).astype(np.float64)
    agent = _agent_position(image)
    return float(np.min(np.sum(np.abs(points - agent), axis=1)))


def _semantic_features(image: np.ndarray) -> np.ndarray:
    distinction, gap = _door_key_labels(image)
    visible = np.asarray(
        [
            float(np.any(_object_mask(image, 5))),
            float(np.any(_object_mask(image, 4))),
            float(np.any(_object_mask(image, 8))),
        ],
        dtype=np.float64,
    )
    distances = np.asarray(
        [
            _distance_to_object(image, 5),
            _distance_to_object(image, 4),
            _distance_to_object(image, 8),
        ],
        dtype=np.float64,
    ) / 10.0
    return np.concatenate([visible, distances, np.asarray([float(distinction), float(gap)], dtype=np.float64)])


def _encode_image(image: np.ndarray) -> np.ndarray:
    array = np.asarray(image, dtype=np.float32)
    scale = np.asarray([10.0, 5.0, 2.0], dtype=np.float32).reshape(1, 1, 3)
    return (array / scale).reshape(-1)


def _is_invalid_transition(action: int, image: np.ndarray, next_image: np.ndarray, reward: float, done: bool) -> bool:
    if int(action) in (0, 1):
        return False
    unchanged = bool(np.array_equal(np.asarray(image), np.asarray(next_image)))
    return bool(unchanged and float(reward) == 0.0 and not done)


def collect_split(
    *,
    environment_id: str,
    transition_count: int,
    planning_count: int,
    seed: int,
) -> tuple[Split, int]:
    import gymnasium as gym
    import minigrid  # noqa: F401

    env = gym.make(environment_id)
    try:
        observation, _ = env.reset(seed=seed)
        rng = np.random.default_rng(seed)
        action_count = int(env.action_space.n)
        obs_rows: list[np.ndarray] = []
        action_rows: list[int] = []
        next_rows: list[np.ndarray] = []
        labels: list[bool] = []
        gaps: list[bool] = []
        invalids: list[bool] = []
        semantic_rows: list[np.ndarray] = []
        planning: list[dict[str, Any]] = []
        for index in range(int(transition_count)):
            image = np.asarray(observation["image"])
            if len(planning) < int(planning_count):
                planning.append(_candidate_planning_state(env, image=image, action_count=action_count))
            action = int(rng.integers(action_count))
            next_observation, reward, terminated, truncated, _ = env.step(action)
            next_image = np.asarray(next_observation["image"])
            distinction, gap = _door_key_labels(next_image)
            done = bool(terminated or truncated)
            obs_rows.append(_encode_image(image))
            action_rows.append(action)
            next_rows.append(_encode_image(next_image))
            labels.append(bool(distinction))
            gaps.append(bool(gap))
            invalids.append(_is_invalid_transition(action, image, next_image, float(reward), done))
            semantic_rows.append(_semantic_features(next_image))
            observation = next_observation
            if done:
                observation, _ = env.reset(seed=seed + index + 1)
        return (
            Split(
                obs=np.asarray(obs_rows, dtype=np.float32),
                actions=np.asarray(action_rows, dtype=np.int64),
                next_obs=np.asarray(next_rows, dtype=np.float32),
                labels=np.asarray(labels, dtype=bool),
                gaps=np.asarray(gaps, dtype=bool),
                invalids=np.asarray(invalids, dtype=bool),
                semantic_next=np.asarray(semantic_rows, dtype=np.float64),
                planning=planning,
            ),
            action_count,
        )
    finally:
        env.close()


def _candidate_planning_state(env: Any, *, image: np.ndarray, action_count: int) -> dict[str, Any]:
    labels: list[bool] = []
    gaps: list[bool] = []
    invalids: list[bool] = []
    for action in range(action_count):
        branch = copy.deepcopy(env)
        try:
            next_observation, reward, terminated, truncated, _ = branch.step(action)
            next_image = np.asarray(next_observation["image"])
            distinction, gap = _door_key_labels(next_image)
            done = bool(terminated or truncated)
            labels.append(bool(distinction))
            gaps.append(bool(gap))
            invalids.append(_is_invalid_transition(action, image, next_image, float(reward), done))
        finally:
            branch.close()
    return {
        "obs": _encode_image(image),
        "labels": np.asarray(labels, dtype=bool),
        "gaps": np.asarray(gaps, dtype=bool),
        "invalids": np.asarray(invalids, dtype=bool),
    }


def collect_run_data(args: argparse.Namespace, seed: int) -> RunData:
    train, action_count = collect_split(
        environment_id=args.train_env,
        transition_count=args.train_count,
        planning_count=0,
        seed=seed,
    )
    validation, _ = collect_split(
        environment_id=args.train_env,
        transition_count=args.validation_count,
        planning_count=args.planning_count,
        seed=seed + 101,
    )
    id_test, _ = collect_split(
        environment_id=args.train_env,
        transition_count=args.test_count,
        planning_count=args.planning_count,
        seed=seed + 202,
    )
    ood_test, _ = collect_split(
        environment_id=args.ood_env,
        transition_count=args.test_count,
        planning_count=args.planning_count,
        seed=seed + 303,
    )
    return RunData(train=train, validation=validation, id_test=id_test, ood_test=ood_test, action_count=action_count)


def _to_tensor(torch: Any, array: np.ndarray, device: str) -> Any:
    return torch.as_tensor(np.asarray(array, dtype=np.float32), dtype=torch.float32, device=device)


def _action_one_hot(torch: Any, actions: np.ndarray, action_count: int, device: str) -> Any:
    index = torch.as_tensor(np.asarray(actions, dtype=np.int64), dtype=torch.long, device=device)
    return torch.nn.functional.one_hot(index, num_classes=action_count).to(dtype=torch.float32)


def _binary_target(torch: Any, values: np.ndarray, device: str) -> Any:
    return torch.as_tensor(np.asarray(values, dtype=np.float32).reshape(-1, 1), dtype=torch.float32, device=device)


class MiniGridWorldModel:
    def __init__(self, torch: Any, input_dim: int, action_count: int, hidden_dim: int, latent_dim: int, device: str) -> None:
        self.torch = torch
        self.action_count = int(action_count)
        self.device = device
        self.encoder = torch.nn.Sequential(
            torch.nn.Linear(input_dim, hidden_dim),
            torch.nn.GELU(),
            torch.nn.Linear(hidden_dim, hidden_dim),
            torch.nn.GELU(),
            torch.nn.Linear(hidden_dim, latent_dim),
        ).to(device)
        self.predictor = torch.nn.Sequential(
            torch.nn.Linear(latent_dim + action_count, hidden_dim),
            torch.nn.GELU(),
            torch.nn.Linear(hidden_dim, hidden_dim),
            torch.nn.GELU(),
            torch.nn.Linear(hidden_dim, latent_dim),
        ).to(device)
        self.distinction_head = torch.nn.Sequential(
            torch.nn.Linear(latent_dim, hidden_dim),
            torch.nn.GELU(),
            torch.nn.Linear(hidden_dim, 1),
        ).to(device)
        self.gap_head = torch.nn.Sequential(
            torch.nn.Linear(latent_dim, hidden_dim),
            torch.nn.GELU(),
            torch.nn.Linear(hidden_dim, 1),
        ).to(device)
        self.invalid_head = torch.nn.Sequential(
            torch.nn.Linear(latent_dim, hidden_dim),
            torch.nn.GELU(),
            torch.nn.Linear(hidden_dim, 1),
        ).to(device)

    def parameters(self) -> list[Any]:
        modules = [self.encoder, self.predictor, self.distinction_head, self.gap_head, self.invalid_head]
        return [param for module in modules for param in module.parameters()]

    def parameter_count(self) -> int:
        return int(sum(param.numel() for param in self.parameters()))

    def transition(self, obs: Any, actions: Any) -> tuple[Any, Any, Any]:
        z = self.encoder(obs)
        z_next = self.encoder(actions["next_obs"])
        one_hot = actions["one_hot"]
        pred = self.predictor(self.torch.cat([z, one_hot], dim=1))
        return z, z_next, pred

    def logits_from_pred(self, pred: Any) -> tuple[Any, Any, Any]:
        return self.distinction_head(pred), self.gap_head(pred), self.invalid_head(pred)


def _pos_weight(torch: Any, labels: np.ndarray, device: str) -> Any:
    arr = np.asarray(labels, dtype=bool)
    pos = max(1.0, float(np.sum(arr)))
    neg = max(1.0, float(arr.shape[0] - np.sum(arr)))
    return torch.as_tensor([neg / pos], dtype=torch.float32, device=device)


def _variance_loss(torch: Any, z: Any) -> Any:
    std = torch.sqrt(z.var(dim=0, unbiased=False) + 1.0e-4)
    return torch.relu(1.0 - std).mean()


def _train_arm(
    data: RunData,
    *,
    arm_name: str,
    seed: int,
    device: str,
    epochs: int,
    head_epochs: int,
    hidden_dim: int,
    latent_dim: int,
) -> tuple[MiniGridWorldModel, dict[str, Any]]:
    torch = require_torch()
    set_deterministic_seed(seed)
    model = MiniGridWorldModel(
        torch,
        input_dim=int(data.train.obs.shape[1]),
        action_count=data.action_count,
        hidden_dim=hidden_dim,
        latent_dim=latent_dim,
        device=device,
    )
    params = model.parameters()
    initial_params = torch.cat([param.detach().flatten().cpu() for param in params])
    optimizer = torch.optim.AdamW(params, lr=2.0e-3, weight_decay=1.0e-4)
    x = _to_tensor(torch, data.train.obs, device)
    x_next = _to_tensor(torch, data.train.next_obs, device)
    one_hot = _action_one_hot(torch, data.train.actions, data.action_count, device)
    y = _binary_target(torch, data.train.labels, device)
    gaps = _binary_target(torch, data.train.gaps, device)
    invalids = _binary_target(torch, data.train.invalids, device)
    bce_dist = torch.nn.BCEWithLogitsLoss(pos_weight=_pos_weight(torch, data.train.labels, device))
    bce_gap = torch.nn.BCEWithLogitsLoss(pos_weight=_pos_weight(torch, data.train.gaps, device))
    bce_invalid = torch.nn.BCEWithLogitsLoss(pos_weight=_pos_weight(torch, data.train.invalids, device))
    mse = torch.nn.MSELoss()
    loss_trace: list[float] = []
    head_loss_trace: list[float] = []
    train_bedc_heads = arm_name in {"supervised_gap", "bedc_jepa"}
    for _epoch in range(int(epochs)):
        optimizer.zero_grad(set_to_none=True)
        z = model.encoder(x)
        z_next = model.encoder(x_next)
        pred = model.predictor(torch.cat([z, one_hot], dim=1))
        latent_loss = mse(pred, z_next.detach()) + 0.12 * covariance_loss(z) + 0.12 * _variance_loss(torch, z)
        loss = latent_loss
        if train_bedc_heads:
            d_logits, g_logits, i_logits = model.logits_from_pred(pred)
            d_loss = bce_dist(d_logits, y)
            g_loss = bce_gap(g_logits, gaps)
            i_loss = bce_invalid(i_logits, invalids)
            loss = loss + d_loss + 0.65 * g_loss + 0.35 * i_loss
            if arm_name == "bedc_jepa":
                d_prob = torch.sigmoid(d_logits)
                gap_prob = torch.maximum(torch.sigmoid(g_logits), torch.sigmoid(i_logits))
                wrong_soft = torch.abs(d_prob - y)
                unlogged = torch.mean(wrong_soft * (1.0 - gap_prob) ** 2)
                gap_caution = torch.mean(torch.maximum(gaps, invalids) * (1.0 - gap_prob) ** 2)
                confident_gap_claim = torch.mean(torch.maximum(gaps, invalids) * torch.abs(d_prob - 0.5))
                loss = loss + 1.15 * unlogged + 0.45 * gap_caution + 0.08 * confident_gap_claim
        loss.backward()
        optimizer.step()
        loss_trace.append(float(loss.detach().cpu()))
    if arm_name == "latent_only":
        for param in list(model.encoder.parameters()) + list(model.predictor.parameters()):
            param.requires_grad_(False)
        head_optimizer = torch.optim.AdamW(
            list(model.distinction_head.parameters()),
            lr=2.0e-3,
            weight_decay=1.0e-4,
        )
        for _epoch in range(int(head_epochs)):
            head_optimizer.zero_grad(set_to_none=True)
            with torch.no_grad():
                z = model.encoder(x)
                pred = model.predictor(torch.cat([z, one_hot], dim=1))
            d_logits = model.distinction_head(pred)
            head_loss = bce_dist(d_logits, y)
            head_loss.backward()
            head_optimizer.step()
            head_loss_trace.append(float(head_loss.detach().cpu()))
        for param in list(model.encoder.parameters()) + list(model.predictor.parameters()):
            param.requires_grad_(True)
    torch.cuda.synchronize() if str(device).startswith("cuda") else None
    final_params = torch.cat([param.detach().flatten().cpu() for param in params])
    return model, {
        "arm_name": arm_name,
        "optimizer": "AdamW",
        "optimizer_steps": int(epochs + (head_epochs if arm_name == "latent_only" else 0)),
        "main_epochs": int(epochs),
        "head_epochs": int(head_epochs if arm_name == "latent_only" else 0),
        "loss_initial": float(loss_trace[0]) if loss_trace else 0.0,
        "loss_final": float(loss_trace[-1]) if loss_trace else 0.0,
        "loss_decrease": float(loss_trace[0] - loss_trace[-1]) if loss_trace else 0.0,
        "head_loss_initial": float(head_loss_trace[0]) if head_loss_trace else None,
        "head_loss_final": float(head_loss_trace[-1]) if head_loss_trace else None,
        "parameter_l2_delta": float(torch.linalg.vector_norm(final_params - initial_params).item()),
        "parameter_count": model.parameter_count(),
    }


def _predict(model: MiniGridWorldModel, split: Split) -> dict[str, np.ndarray]:
    torch = model.torch
    with torch.no_grad():
        x = _to_tensor(torch, split.obs, model.device)
        x_next = _to_tensor(torch, split.next_obs, model.device)
        one_hot = _action_one_hot(torch, split.actions, model.action_count, model.device)
        z = model.encoder(x)
        z_next = model.encoder(x_next)
        pred = model.predictor(torch.cat([z, one_hot], dim=1))
        d_logits, g_logits, i_logits = model.logits_from_pred(pred)
        transition_error = torch.mean((pred - z_next) ** 2, dim=1)
        distinction = torch.sigmoid(d_logits).detach().cpu().numpy().reshape(-1)
        gap = torch.sigmoid(g_logits).detach().cpu().numpy().reshape(-1)
        invalid = torch.sigmoid(i_logits).detach().cpu().numpy().reshape(-1)
        error = transition_error.detach().cpu().numpy().reshape(-1)
        pred_np = pred.detach().cpu().numpy()
    if np.max(error) > np.min(error):
        error_score = (error - np.min(error)) / (np.max(error) - np.min(error))
    else:
        error_score = np.zeros_like(error)
    return {
        "distinction": distinction.astype(np.float64),
        "gap": gap.astype(np.float64),
        "invalid": invalid.astype(np.float64),
        "transition_error_score": error_score.astype(np.float64),
        "latent_pred": pred_np.astype(np.float64),
    }


def _arm_debt_scores(arm_name: str, predictions: dict[str, np.ndarray]) -> np.ndarray:
    if arm_name == "latent_only":
        margin = np.abs(predictions["distinction"] - 0.5)
        margin_gap = 1.0 / (1.0 + np.exp(-np.clip(12.0 * (0.12 - margin), -40.0, 40.0)))
        return np.maximum(margin_gap, predictions["transition_error_score"])
    return np.maximum(predictions["gap"], predictions["invalid"])


def _split_metrics(arm_name: str, model: MiniGridWorldModel, train: Split, split: Split) -> dict[str, float]:
    pred = _predict(model, split)
    debt = _arm_debt_scores(arm_name, pred)
    false_claim = _false_claim_rate(pred["distinction"], split.labels, split.gaps | split.invalids)
    unlogged = unlogged_error_rate(pred["distinction"], split.labels, debt)
    coverage = certified_coverage(debt)
    gap_auc = gap_detection_auc(pred["gap"] if arm_name != "latent_only" else debt, split.gaps)
    invalid_auc = gap_detection_auc(pred["invalid"] if arm_name != "latent_only" else debt, split.invalids)
    return {
        "distinction_accuracy": binary_accuracy(pred["distinction"], split.labels),
        "ood_gap_auc" if split is not train else "gap_auc": gap_auc,
        "gap_detection_auc": gap_auc,
        "invalid_transition_auc": invalid_auc,
        "unlogged_error_rate": unlogged,
        "certified_coverage": coverage,
        "bedc_debt_score": bedc_debt_score(
            unlogged_error=unlogged,
            false_claim=false_claim,
            gap_auc=gap_auc,
            certified=coverage,
        ),
        "latent_r2": _latent_r2(model, train, split),
    }


def _false_claim_rate(scores: np.ndarray, labels: np.ndarray, gaps: np.ndarray) -> float:
    score_arr = np.asarray(scores, dtype=np.float64)
    label_arr = np.asarray(labels, dtype=bool)
    gap_arr = np.asarray(gaps, dtype=bool)
    if not np.any(gap_arr):
        return 0.0
    confident = np.abs(score_arr - 0.5) >= 0.25
    wrong = (score_arr >= 0.5) != label_arr
    return float(np.mean(confident[gap_arr] & wrong[gap_arr]))


def _latent_r2(model: MiniGridWorldModel, train: Split, split: Split) -> float:
    train_pred = _predict(model, train)["latent_pred"]
    split_pred = _predict(model, split)["latent_pred"]
    x_train = np.column_stack([train_pred, np.ones(train_pred.shape[0])])
    ridge = 1.0e-3 * np.eye(x_train.shape[1])
    weights = np.linalg.solve(x_train.T @ x_train + ridge, x_train.T @ train.semantic_next)
    y_hat = np.column_stack([split_pred, np.ones(split_pred.shape[0])]) @ weights
    y = split.semantic_next
    ss_res = float(np.sum((y - y_hat) ** 2))
    ss_tot = float(np.sum((y - np.mean(y, axis=0, keepdims=True)) ** 2))
    if ss_tot <= 1.0e-12:
        return 0.0
    return float(1.0 - ss_res / ss_tot)


def _planning_success(model: MiniGridWorldModel, arm_name: str, planning: list[dict[str, Any]], lambda_gap: float) -> dict[str, float]:
    if not planning:
        return {"success": 0.0, "high_gap_rate": 0.0, "invalid_rate": 0.0, "state_count": 0.0}
    torch = model.torch
    successes: list[bool] = []
    high_gaps: list[bool] = []
    invalids: list[bool] = []
    with torch.no_grad():
        for state in planning:
            obs = np.repeat(np.asarray(state["obs"], dtype=np.float32)[None, :], model.action_count, axis=0)
            actions = np.arange(model.action_count, dtype=np.int64)
            x = _to_tensor(torch, obs, model.device)
            one_hot = _action_one_hot(torch, actions, model.action_count, model.device)
            z = model.encoder(x)
            pred = model.predictor(torch.cat([z, one_hot], dim=1))
            d_logits, g_logits, i_logits = model.logits_from_pred(pred)
            distinction = torch.sigmoid(d_logits).detach().cpu().numpy().reshape(-1)
            gap = torch.sigmoid(g_logits).detach().cpu().numpy().reshape(-1)
            invalid = torch.sigmoid(i_logits).detach().cpu().numpy().reshape(-1)
            if arm_name == "latent_only":
                margin = np.abs(distinction - 0.5)
                debt = 1.0 / (1.0 + np.exp(-np.clip(12.0 * (0.12 - margin), -40.0, 40.0)))
            else:
                debt = np.maximum(gap, invalid)
            selected = int(np.argmax(distinction - float(lambda_gap) * debt))
            successes.append(bool(np.asarray(state["labels"], dtype=bool)[selected]))
            high_gaps.append(bool(np.asarray(state["gaps"], dtype=bool)[selected]))
            invalids.append(bool(np.asarray(state["invalids"], dtype=bool)[selected]))
    return {
        "success": float(np.mean(successes)),
        "high_gap_rate": float(np.mean(high_gaps)),
        "invalid_rate": float(np.mean(invalids)),
        "state_count": float(len(successes)),
    }


def _choose_lambda(model: MiniGridWorldModel, arm_name: str, validation: Split) -> tuple[float, list[dict[str, float]]]:
    rows: list[dict[str, float]] = []
    for lam in (0.0, 0.25, 0.5, 1.0):
        result = _planning_success(model, arm_name, validation.planning, lam)
        score = result["success"] - 0.15 * result["high_gap_rate"] - 0.10 * result["invalid_rate"]
        rows.append({"lambda_gap": float(lam), "selection_score": float(score), **result})
    best = max(rows, key=lambda row: (row["selection_score"], row["success"], -row["high_gap_rate"]))
    return float(best["lambda_gap"]), rows


def run_seed(args: argparse.Namespace, seed: int, device: str) -> dict[str, Any]:
    data = collect_run_data(args, seed)
    seed_rows: dict[str, Any] = {}
    for offset, arm_name in enumerate(ARM_NAMES):
        model, training = _train_arm(
            data,
            arm_name=arm_name,
            seed=seed + offset * 1000,
            device=device,
            epochs=args.epochs,
            head_epochs=args.head_epochs,
            hidden_dim=args.hidden_dim,
            latent_dim=args.latent_dim,
        )
        lambda_gap, validation_sweep = _choose_lambda(model, arm_name, data.validation)
        id_metrics = _split_metrics(arm_name, model, data.train, data.id_test)
        ood_metrics = _split_metrics(arm_name, model, data.train, data.ood_test)
        id_plan = _planning_success(model, arm_name, data.id_test.planning, lambda_gap)
        ood_plan = _planning_success(model, arm_name, data.ood_test.planning, lambda_gap)
        seed_rows[arm_name] = {
            "training": training,
            "validation_lambda_sweep": validation_sweep,
            "selected_lambda_gap": lambda_gap,
            "id": {**id_metrics, "success": id_plan["success"], "planning_high_gap_rate": id_plan["high_gap_rate"], "planning_invalid_rate": id_plan["invalid_rate"]},
            "ood": {**ood_metrics, "success": ood_plan["success"], "planning_high_gap_rate": ood_plan["high_gap_rate"], "planning_invalid_rate": ood_plan["invalid_rate"]},
        }
    return {
        "seed": int(seed),
        "data": {
            "train_env": args.train_env,
            "ood_env": args.ood_env,
            "train_count": int(data.train.obs.shape[0]),
            "validation_count": int(data.validation.obs.shape[0]),
            "id_test_count": int(data.id_test.obs.shape[0]),
            "ood_test_count": int(data.ood_test.obs.shape[0]),
            "planning_count_per_eval_split": int(args.planning_count),
            "action_count": int(data.action_count),
            "train_gap_rate": float(np.mean(data.train.gaps)),
            "train_invalid_rate": float(np.mean(data.train.invalids)),
            "ood_gap_rate": float(np.mean(data.ood_test.gaps)),
            "ood_invalid_rate": float(np.mean(data.ood_test.invalids)),
        },
        "arms": seed_rows,
    }


def _summarize(seed_results: list[dict[str, Any]]) -> dict[str, Any]:
    metric_paths = [
        ("id_success", ("id", "success")),
        ("ood_success", ("ood", "success")),
        ("ood_gap_auc", ("ood", "gap_detection_auc")),
        ("invalid_transition_auc", ("ood", "invalid_transition_auc")),
        ("certified_coverage", ("ood", "certified_coverage")),
        ("unlogged_error_rate", ("ood", "unlogged_error_rate")),
        ("latent_r2", ("ood", "latent_r2")),
    ]
    summary: dict[str, Any] = {}
    for arm in ARM_NAMES:
        arm_summary: dict[str, Any] = {}
        for key, path in metric_paths:
            values = [
                float(seed_result["arms"][arm][path[0]][path[1]])
                for seed_result in seed_results
            ]
            arm_summary[key] = {
                "mean": float(np.mean(values)) if values else 0.0,
                "std": float(np.std(values, ddof=0)) if values else 0.0,
                "values": values,
            }
        arm_summary["parameter_count"] = int(seed_results[0]["arms"][arm]["training"]["parameter_count"]) if seed_results else 0
        summary[arm] = arm_summary
    if seed_results:
        summary["bedc_minus_supervised_gap"] = {
            "ood_success": float(summary["bedc_jepa"]["ood_success"]["mean"] - summary["supervised_gap"]["ood_success"]["mean"]),
            "ood_gap_auc": float(summary["bedc_jepa"]["ood_gap_auc"]["mean"] - summary["supervised_gap"]["ood_gap_auc"]["mean"]),
            "unlogged_error_reduction": float(summary["supervised_gap"]["unlogged_error_rate"]["mean"] - summary["bedc_jepa"]["unlogged_error_rate"]["mean"]),
        }
        summary["bedc_minus_latent_only"] = {
            "ood_success": float(summary["bedc_jepa"]["ood_success"]["mean"] - summary["latent_only"]["ood_success"]["mean"]),
            "ood_gap_auc": float(summary["bedc_jepa"]["ood_gap_auc"]["mean"] - summary["latent_only"]["ood_gap_auc"]["mean"]),
            "unlogged_error_reduction": float(summary["latent_only"]["unlogged_error_rate"]["mean"] - summary["bedc_jepa"]["unlogged_error_rate"]["mean"]),
        }
    return summary


def _dependency_status(torch: Any) -> dict[str, Any]:
    import gymnasium
    import minigrid

    return {
        "python": PYTHON_BIN,
        "torch": str(torch.__version__),
        "torch_cuda_available": bool(torch.cuda.is_available()),
        "torch_cuda_device": torch.cuda.get_device_name(0) if torch.cuda.is_available() else None,
        "gymnasium": str(gymnasium.__version__),
        "minigrid": str(getattr(minigrid, "__version__", "unknown")),
    }


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    parser.add_argument("--train-env", default=DEFAULT_TRAIN_ENV)
    parser.add_argument("--ood-env", default=DEFAULT_OOD_ENV)
    parser.add_argument("--seeds", default=",".join(str(seed) for seed in DEFAULT_SEEDS))
    parser.add_argument("--train-count", type=int, default=900)
    parser.add_argument("--validation-count", type=int, default=240)
    parser.add_argument("--test-count", type=int, default=360)
    parser.add_argument("--planning-count", type=int, default=72)
    parser.add_argument("--epochs", type=int, default=90)
    parser.add_argument("--head-epochs", type=int, default=45)
    parser.add_argument("--hidden-dim", type=int, default=96)
    parser.add_argument("--latent-dim", type=int, default=24)
    parser.add_argument("--device", default="cuda")
    parser.add_argument("--report", default=str(REPORT_PATH))
    return parser


def main() -> None:
    args = build_arg_parser().parse_args()
    seeds = tuple(int(item.strip()) for item in str(args.seeds).split(",") if item.strip())
    torch = require_torch()
    device_resolution = choose_device(args.device)
    device = device_resolution.resolved_device
    before = _nvidia_snapshot()
    started_at = time.time()
    with NvidiaMonitor() as monitor:
        seed_results = [run_seed(args, seed, device) for seed in seeds]
        if str(device).startswith("cuda"):
            torch.cuda.synchronize()
        monitor_evidence = monitor.collect()
    finished_at = time.time()
    after = _nvidia_snapshot()
    payload = {
        "schema_id": "bedc-quality-lab:bedc-minigrid-tournament",
        "status": "executed",
        "run_contract": {
            "objective": "native MiniGrid external-validity tournament for BEDC-JEPA model ability",
            "train_environment": args.train_env,
            "ood_environment": args.ood_env,
            "heldout_layout_protocol": "train and ID test use disjoint seeds in train_environment; OOD uses ood_environment with disjoint seeds",
            "arms": list(ARM_NAMES),
            "planning_rule": "one-step candidate action selection by predicted distinction minus validation-selected lambda times predicted debt",
            "metric_source": "bedc_quality_lab.bedc_jepa_metrics plus MiniGrid native transition labels",
        },
        "config": {
            "seeds": list(seeds),
            "train_count": int(args.train_count),
            "validation_count": int(args.validation_count),
            "test_count": int(args.test_count),
            "planning_count": int(args.planning_count),
            "epochs": int(args.epochs),
            "head_epochs": int(args.head_epochs),
            "hidden_dim": int(args.hidden_dim),
            "latent_dim": int(args.latent_dim),
            "requested_device": args.device,
        },
        "dependency_status": _dependency_status(torch),
        "device_resolution": device_resolution.to_dict(),
        "gpu_evidence": {
            "nvidia_smi_before": before,
            "nvidia_smi_monitor": monitor_evidence,
            "nvidia_smi_after": after,
            "torch_cuda_memory_allocated_max_bytes": int(torch.cuda.max_memory_allocated()) if torch.cuda.is_available() else 0,
        },
        "seed_results": seed_results,
        "summary": _summarize(seed_results),
        "cannot_claim": [
            "full MiniGrid episode solver",
            "MPC or multi-step learned planner",
            "public benchmark superiority",
            "official V-JEPA2-AC reproduction",
            "large-scale visual world-model conclusion",
            "formal neural-network proof",
        ],
        "elapsed_seconds": float(finished_at - started_at),
    }
    target = Path(args.report)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"report": str(target), "elapsed_seconds": payload["elapsed_seconds"], "device": device}, sort_keys=True))


if __name__ == "__main__":
    main()

"""MiniGrid architecture tournament with OOD episode success as primary."""

from __future__ import annotations

from dataclasses import asdict, dataclass, replace
from pathlib import Path
import copy
import json
import math
import random
from collections import deque
from typing import Any, Iterable, Mapping, Sequence

import numpy as np

from bedc_quality_lab.model import choose_device, require_torch, set_deterministic_seed

try:
    import torch as _torch
except ImportError:  # pragma: no cover - real tournament requires torch.
    _torch = None


SCHEMA_ID = "bedc-quality-lab:mg-cap-tournament"
ISSUE_ID = "#1565"
TRAIN_ENV_ID = "MiniGrid-DoorKey-5x5-v0"
OOD_ENV_IDS = ("MiniGrid-DoorKey-8x8-v0", "MiniGrid-DoorKey-16x16-v0")
FALLBACK_OOD_ENV_ID = "MiniGrid-BlockedUnlockPickup-v0"
SPLIT_ID = "id"
SPLIT_OOD_DOOR_KEY = "ood_door_key"
SPLIT_OOD_TRANSFER = "ood_transfer"
MISSION_VOCAB = {
    "<pad>": 0,
    "use": 1,
    "the": 2,
    "key": 3,
    "to": 4,
    "open": 5,
    "door": 6,
    "and": 7,
    "then": 8,
    "get": 9,
    "goal": 10,
    "pick": 11,
    "up": 12,
    "purple": 13,
    "ball": 14,
    "box": 15,
    "red": 16,
    "green": 17,
    "blue": 18,
    "yellow": 19,
    "grey": 20,
}
OBJECT_CHANNEL_SIZE = 16
COLOR_CHANNEL_SIZE = 8
STATE_CHANNEL_SIZE = 8
ACTION_COUNT = 7
OBS_FRONT_X = 3
OBS_FRONT_Y = 5
OBJ_UNSEEN = 0
OBJ_EMPTY = 1
OBJ_WALL = 2
OBJ_DOOR = 4
OBJ_KEY = 5
OBJ_BALL = 6
OBJ_BOX = 7
OBJ_GOAL = 8


@dataclass(frozen=True)
class BootstrapSummary:
    mean: float
    ci_low: float
    ci_high: float
    n: int

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class TournamentConfig:
    train_env_id: str = TRAIN_ENV_ID
    ood_env_ids: tuple[str, str] = OOD_ENV_IDS
    seeds: tuple[int, ...] = (0, 1, 2)
    demo_episodes: int = 800
    validation_demo_episodes: int = 96
    eval_episodes: int = 256
    validation_eval_episodes: int = 64
    train_steps: int = 6000
    batch_size: int = 96
    context_length: int = 32
    hidden_dim: int = 64
    learning_rate: float = 2.0e-4
    eval_interval: int = 1500
    balanced_batch_fraction: float = 0.35
    off_expert_rate: float = 0.15
    bootstrap_resamples: int = 1000
    requested_device: str = "auto"
    run_priority2: bool = True
    max_episode_steps: int | None = None

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["ood_env_ids"] = list(self.ood_env_ids)
        payload["seeds"] = list(self.seeds)
        return payload


@dataclass(frozen=True)
class ArmSpec:
    name: str
    family: str
    hidden_dim: int
    priority: int
    parameter_count: int

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class Episode:
    images: np.ndarray
    missions: np.ndarray
    actions: np.ndarray
    oracle_success: bool
    executed_steps: int
    executed_actions: np.ndarray | None = None


@dataclass(frozen=True)
class DatasetBundle:
    train: tuple[Episode, ...]
    validation: tuple[Episode, ...]
    fingerprint: str


def mission_tokens(mission: str, *, max_length: int = 16) -> np.ndarray:
    words = (
        mission.lower()
        .replace(",", " ")
        .replace(".", " ")
        .replace("-", " ")
        .split()
    )
    ids = [MISSION_VOCAB.get(word, len(MISSION_VOCAB) + 1) for word in words[:max_length]]
    ids.extend([0] * (max_length - len(ids)))
    return np.asarray(ids, dtype=np.int64)


def bootstrap_mean_ci(values: np.ndarray, *, seed: int, resamples: int) -> BootstrapSummary:
    arr = np.asarray(values, dtype=np.float64).reshape(-1)
    if arr.size == 0:
        return BootstrapSummary(mean=math.nan, ci_low=math.nan, ci_high=math.nan, n=0)
    mean = float(np.mean(arr))
    if arr.size == 1 or resamples <= 0:
        return BootstrapSummary(mean=mean, ci_low=mean, ci_high=mean, n=int(arr.size))
    rng = np.random.default_rng(seed)
    indices = rng.integers(0, arr.size, size=(int(resamples), arr.size))
    boot = np.mean(arr[indices], axis=1)
    return BootstrapSummary(
        mean=mean,
        ci_low=float(np.quantile(boot, 0.025)),
        ci_high=float(np.quantile(boot, 0.975)),
        n=int(arr.size),
    )


def bootstrap_delta_ci(
    candidate: np.ndarray,
    baseline: np.ndarray,
    *,
    seed: int,
    resamples: int,
) -> BootstrapSummary:
    cand = np.asarray(candidate, dtype=np.float64).reshape(-1)
    base = np.asarray(baseline, dtype=np.float64).reshape(-1)
    if cand.size == 0 or base.size == 0:
        return BootstrapSummary(mean=math.nan, ci_low=math.nan, ci_high=math.nan, n=0)
    delta = float(np.mean(cand) - np.mean(base))
    if resamples <= 0:
        return BootstrapSummary(mean=delta, ci_low=delta, ci_high=delta, n=int(min(cand.size, base.size)))
    rng = np.random.default_rng(seed)
    cand_idx = rng.integers(0, cand.size, size=(int(resamples), cand.size))
    base_idx = rng.integers(0, base.size, size=(int(resamples), base.size))
    boot = np.mean(cand[cand_idx], axis=1) - np.mean(base[base_idx], axis=1)
    return BootstrapSummary(
        mean=delta,
        ci_low=float(np.quantile(boot, 0.025)),
        ci_high=float(np.quantile(boot, 0.975)),
        n=int(min(cand.size, base.size)),
    )


def _import_minigrid() -> tuple[Any, Any]:
    import gymnasium as gym
    import minigrid  # noqa: F401

    return gym, minigrid


def resolve_ood_envs(env_ids: Sequence[str] = OOD_ENV_IDS) -> tuple[str, str]:
    gym, _ = _import_minigrid()
    resolved: list[str] = []
    for env_id in env_ids:
        try:
            env = gym.make(env_id)
            env.close()
            resolved.append(str(env_id))
        except Exception:
            if env_id != FALLBACK_OOD_ENV_ID:
                env = gym.make(FALLBACK_OOD_ENV_ID)
                env.close()
                resolved.append(FALLBACK_OOD_ENV_ID)
            else:
                raise
    if len(resolved) != 2:
        raise ValueError("exactly two OOD environments are required")
    return (resolved[0], resolved[1])


def _front_pos(pos: tuple[int, int], direction: int) -> tuple[int, int]:
    deltas = {
        0: (1, 0),
        1: (0, 1),
        2: (-1, 0),
        3: (0, -1),
    }
    dx, dy = deltas[int(direction)]
    return (int(pos[0]) + dx, int(pos[1]) + dy)


def _object_signature(obj: Any | None) -> tuple[str, str, bool, bool] | None:
    if obj is None:
        return None
    return (
        str(getattr(obj, "type", "")),
        str(getattr(obj, "color", "")),
        bool(getattr(obj, "is_open", False)),
        bool(getattr(obj, "is_locked", False)),
    )


def _carrying_signature(obj: Any | None) -> tuple[str, str] | None:
    if obj is None:
        return None
    return (str(getattr(obj, "type", "")), str(getattr(obj, "color", "")))


def _target_from_mission(env: Any) -> tuple[str, str | None]:
    mission = str(getattr(env.unwrapped, "mission", "")).lower()
    if "goal" in mission:
        return ("goal", None)
    target_type = "ball" if "ball" in mission else "box" if "box" in mission else "key"
    target_color = None
    for color in ("red", "green", "blue", "purple", "yellow", "grey"):
        if color in mission:
            target_color = color
            break
    return (target_type, target_color)


def _initial_grid_map(env: Any) -> dict[tuple[int, int], tuple[str, str, bool, bool]]:
    grid = env.unwrapped.grid
    cells: dict[tuple[int, int], tuple[str, str, bool, bool]] = {}
    for x in range(int(env.unwrapped.width)):
        for y in range(int(env.unwrapped.height)):
            sig = _object_signature(grid.get(x, y))
            if sig is not None:
                cells[(x, y)] = sig
    return cells


def _symbolic_plan(env: Any, *, max_nodes: int = 60000) -> list[int] | None:
    action = env.unwrapped.actions
    left = int(action.left)
    right = int(action.right)
    forward = int(action.forward)
    pickup = int(action.pickup)
    drop = int(action.drop)
    toggle = int(action.toggle)
    cells = _initial_grid_map(env)
    width = int(env.unwrapped.width)
    height = int(env.unwrapped.height)
    target_type, target_color = _target_from_mission(env)
    actions = (left, right, forward, pickup, toggle) if target_type == "goal" else (left, right, forward, pickup, drop, toggle)
    start_pos = tuple(map(int, env.unwrapped.agent_pos))
    start_dir = int(env.unwrapped.agent_dir)
    start_carrying = _carrying_signature(env.unwrapped.carrying)
    start_open = frozenset(
        pos for pos, sig in cells.items() if sig[0] == "door" and sig[2]
    )
    start_removed = frozenset(
        pos
        for pos, sig in cells.items()
        if start_carrying is not None and (sig[0], sig[1]) == start_carrying
    )
    start = (start_pos, start_dir, start_carrying, start_open, start_removed, frozenset())

    def cell_at(
        pos: tuple[int, int],
        removed: frozenset[tuple[int, int]],
        dropped: frozenset[tuple[int, int, str, str]],
        opened: frozenset[tuple[int, int]],
    ) -> tuple[str, str, bool, bool] | None:
        if pos in removed:
            for item in dropped:
                if item[0] == pos[0] and item[1] == pos[1]:
                    return (item[2], item[3], False, False)
            return None
        sig = cells.get(pos)
        if sig is None:
            for item in dropped:
                if item[0] == pos[0] and item[1] == pos[1]:
                    return (item[2], item[3], False, False)
            return None
        if sig[0] == "door" and pos in opened:
            return (sig[0], sig[1], True, False)
        return sig

    def can_overlap(sig: tuple[str, str, bool, bool] | None) -> bool:
        if sig is None:
            return True
        typ = sig[0]
        if typ in {"empty", "floor", "goal", "lava"}:
            return True
        if typ == "door":
            return bool(sig[2])
        return False

    def is_target(sig: tuple[str, str, bool, bool] | None) -> bool:
        if sig is None:
            return False
        typ, color = sig[0], sig[1]
        if target_type == "goal":
            return typ == "goal"
        if typ != target_type:
            return False
        return target_color is None or color == target_color

    queue: deque[tuple[Any, list[int]]] = deque([(start, [])])
    seen = {start}
    nodes = 0
    while queue and nodes < max_nodes:
        state, path = queue.popleft()
        nodes += 1
        pos, direction, carrying, opened, removed, dropped = state
        for act in actions:
            next_pos = pos
            next_dir = direction
            next_carrying = carrying
            next_opened = opened
            next_removed = removed
            next_dropped = dropped
            front = _front_pos(pos, direction)
            front_sig = None
            if 0 <= front[0] < width and 0 <= front[1] < height:
                front_sig = cell_at(front, removed, dropped, opened)

            if act == left:
                next_dir = (direction - 1) % 4
            elif act == right:
                next_dir = (direction + 1) % 4
            elif act == forward:
                if not can_overlap(front_sig):
                    continue
                next_pos = front
                if target_type == "goal" and is_target(front_sig):
                    return path + [act]
            elif act == pickup:
                if carrying is not None or front_sig is None:
                    continue
                if front_sig[0] not in {"key", "ball", "box"}:
                    continue
                next_carrying = (front_sig[0], front_sig[1])
                next_removed = frozenset(set(removed) | {front})
                next_dropped = frozenset(
                    item for item in dropped if not (item[0] == front[0] and item[1] == front[1])
                )
                if target_type != "goal" and is_target(front_sig):
                    return path + [act]
            elif act == drop:
                if carrying is None or front_sig is not None:
                    continue
                typ, color = carrying
                next_dropped = frozenset(set(dropped) | {(front[0], front[1], typ, color)})
                next_carrying = None
            elif act == toggle:
                if front_sig is None or front_sig[0] != "door":
                    continue
                if front_sig[2]:
                    continue
                if front_sig[3] and carrying != ("key", front_sig[1]):
                    continue
                next_opened = frozenset(set(opened) | {front})
            next_state = (next_pos, next_dir, next_carrying, next_opened, next_removed, next_dropped)
            if next_state in seen:
                continue
            seen.add(next_state)
            queue.append((next_state, path + [act]))
    return None


def oracle_episode(
    env_id: str,
    *,
    seed: int,
    off_expert_rate: float,
    max_episode_steps: int | None = None,
) -> Episode:
    gym, _ = _import_minigrid()
    env = gym.make(env_id)
    rng = np.random.default_rng(seed)
    images: list[np.ndarray] = []
    missions: list[np.ndarray] = []
    labels: list[int] = []
    executed_actions: list[int] = []
    plan: list[int] | None = None
    success = False
    try:
        observation, _ = env.reset(seed=seed)
        limit = int(max_episode_steps or getattr(env.unwrapped, "max_steps", 512))
        for step_index in range(limit):
            if not plan:
                plan = _symbolic_plan(env)
            if not plan:
                break
            oracle_action = int(plan[0])
            images.append(np.asarray(observation["image"], dtype=np.int64))
            missions.append(mission_tokens(str(observation.get("mission", ""))))
            labels.append(oracle_action)
            use_recovery = bool(rng.random() < off_expert_rate)
            executed_action = int(rng.integers(0, env.action_space.n)) if use_recovery else oracle_action
            executed_actions.append(executed_action)
            observation, reward, terminated, truncated, _ = env.step(executed_action)
            if use_recovery:
                plan = None
            else:
                plan = plan[1:]
            success = bool(reward > 0)
            if terminated or truncated:
                break
        return Episode(
            images=np.asarray(images, dtype=np.int64),
            missions=np.asarray(missions, dtype=np.int64),
            actions=np.asarray(labels, dtype=np.int64),
            oracle_success=success,
            executed_steps=int(len(labels)),
            executed_actions=np.asarray(executed_actions, dtype=np.int64),
        )
    finally:
        env.close()


def oracle_successes(
    env_id: str,
    *,
    episodes: int,
    seed: int,
    max_episode_steps: int | None = None,
) -> np.ndarray:
    values = []
    for index in range(int(episodes)):
        episode = oracle_episode(
            env_id,
            seed=seed + index,
            off_expert_rate=0.0,
            max_episode_steps=max_episode_steps,
        )
        values.append(float(episode.oracle_success))
    return np.asarray(values, dtype=np.float32)


def collect_dataset(config: TournamentConfig, *, seed: int) -> DatasetBundle:
    train = []
    validation = []
    for index in range(int(config.demo_episodes)):
        episode = oracle_episode(
            config.train_env_id,
            seed=100000 + seed * 10000 + index,
            off_expert_rate=config.off_expert_rate,
            max_episode_steps=config.max_episode_steps,
        )
        if episode.actions.size > 0:
            train.append(episode)
    for index in range(int(config.validation_demo_episodes)):
        episode = oracle_episode(
            config.train_env_id,
            seed=200000 + seed * 10000 + index,
            off_expert_rate=0.0,
            max_episode_steps=config.max_episode_steps,
        )
        if episode.actions.size > 0:
            validation.append(episode)
    fingerprint_payload = {
        "train_env_id": config.train_env_id,
        "seed": int(seed),
        "train_lengths": [int(ep.actions.size) for ep in train],
        "validation_lengths": [int(ep.actions.size) for ep in validation],
        "off_expert_rate": float(config.off_expert_rate),
    }
    import hashlib

    fingerprint = hashlib.sha256(
        json.dumps(fingerprint_payload, sort_keys=True).encode("utf-8")
    ).hexdigest()
    return DatasetBundle(train=tuple(train), validation=tuple(validation), fingerprint=fingerprint)


class SequenceSampler:
    def __init__(
        self,
        episodes: Sequence[Episode],
        *,
        context_length: int,
        seed: int,
        balance_actions: bool = False,
    ) -> None:
        self.episodes = tuple(episodes)
        self.context_length = int(context_length)
        self.indices = [
            (episode_index, step_index)
            for episode_index, episode in enumerate(self.episodes)
            for step_index in range(int(episode.actions.size))
        ]
        if not self.indices:
            raise ValueError("sequence sampler requires at least one labeled transition")
        self.rng = np.random.default_rng(seed)
        self.balance_actions = bool(balance_actions)
        self.indices_by_action: dict[int, list[tuple[int, int]]] = {}
        for episode_index, step_index in self.indices:
            action = int(self.episodes[episode_index].actions[step_index])
            self.indices_by_action.setdefault(action, []).append((episode_index, step_index))

    def sample(self, batch_size: int) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
        if self.balance_actions:
            action_ids = np.asarray(sorted(self.indices_by_action), dtype=np.int64)
            chosen_actions = self.rng.choice(action_ids, size=int(batch_size), replace=True)
            chosen_pairs = []
            for action in chosen_actions:
                bucket = self.indices_by_action[int(action)]
                chosen_pairs.append(bucket[int(self.rng.integers(0, len(bucket)))])
        else:
            chosen = self.rng.integers(0, len(self.indices), size=int(batch_size))
            chosen_pairs = [self.indices[int(flat_index)] for flat_index in chosen]
        images = np.zeros((int(batch_size), self.context_length, 7, 7, 3), dtype=np.int64)
        missions = np.zeros((int(batch_size), self.context_length, 16), dtype=np.int64)
        prev_actions = np.zeros((int(batch_size), self.context_length), dtype=np.int64)
        mask = np.zeros((int(batch_size), self.context_length), dtype=bool)
        actions = np.zeros((int(batch_size),), dtype=np.int64)
        for row, (episode_index, step_index) in enumerate(chosen_pairs):
            episode = self.episodes[episode_index]
            start = max(0, step_index - self.context_length + 1)
            end = step_index + 1
            length = end - start
            offset = self.context_length - length
            images[row, offset:] = episode.images[start:end]
            missions[row, offset:] = episode.missions[start:end]
            executed = episode.executed_actions if episode.executed_actions is not None else episode.actions
            for col, source_index in enumerate(range(start, end), start=offset):
                prev_actions[row, col] = 0 if source_index == 0 else int(executed[source_index - 1]) + 1
            mask[row, offset:] = True
            actions[row] = episode.actions[step_index]
        return images, missions, prev_actions, mask, actions


def _sampled_action_loss(
    model: Any,
    sampler: SequenceSampler,
    *,
    torch: Any,
    device: str,
    batch_size: int,
    batches: int = 4,
) -> float:
    values = []
    model.eval()
    with torch.no_grad():
        for _ in range(int(batches)):
            images, missions, prev_actions, mask, actions = sampler.sample(batch_size)
            logits = model(
                torch.as_tensor(images, dtype=torch.long, device=device),
                torch.as_tensor(missions, dtype=torch.long, device=device),
                torch.as_tensor(prev_actions, dtype=torch.long, device=device),
                torch.as_tensor(mask, dtype=torch.bool, device=device),
            )
            target = torch.as_tensor(actions, dtype=torch.long, device=device)
            values.append(float(torch.nn.functional.cross_entropy(logits, target).detach().cpu().item()))
    return float(np.mean(values)) if values else math.inf


def _mixed_batch(
    natural_sampler: SequenceSampler,
    balanced_sampler: SequenceSampler,
    *,
    batch_size: int,
    balanced_fraction: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    balanced_count = int(round(int(batch_size) * max(0.0, min(1.0, float(balanced_fraction)))))
    natural_count = int(batch_size) - balanced_count
    batches = []
    if natural_count > 0:
        batches.append(natural_sampler.sample(natural_count))
    if balanced_count > 0:
        batches.append(balanced_sampler.sample(balanced_count))
    if len(batches) == 1:
        return batches[0]
    images = np.concatenate([batch[0] for batch in batches], axis=0)
    missions = np.concatenate([batch[1] for batch in batches], axis=0)
    prev_actions = np.concatenate([batch[2] for batch in batches], axis=0)
    mask = np.concatenate([batch[3] for batch in batches], axis=0)
    actions = np.concatenate([batch[4] for batch in batches], axis=0)
    return images, missions, prev_actions, mask, actions


class _PolicyBase(_torch.nn.Module if _torch is not None else object):
    def parameter_count(self) -> int:
        return int(sum(param.numel() for param in self.parameters() if param.requires_grad))


def _last_valid(hidden: Any, mask: Any) -> Any:
    torch = require_torch()
    positions = torch.arange(mask.shape[1], device=hidden.device).reshape(1, -1)
    lengths = torch.clamp((positions * mask.to(device=hidden.device).long()).amax(dim=1), min=0)
    batch = torch.arange(hidden.shape[0], device=hidden.device)
    return hidden[batch, lengths]


class ObservationEncoder(_PolicyBase):
    def __init__(self, hidden_dim: int) -> None:
        torch = require_torch()
        super().__init__()
        self.object_embedding = torch.nn.Embedding(OBJECT_CHANNEL_SIZE, 8, padding_idx=0)
        self.color_embedding = torch.nn.Embedding(COLOR_CHANNEL_SIZE, 4, padding_idx=0)
        self.state_embedding = torch.nn.Embedding(STATE_CHANNEL_SIZE, 4, padding_idx=0)
        self.mission_embedding = torch.nn.Embedding(len(MISSION_VOCAB) + 2, 16, padding_idx=0)
        self.prev_action_embedding = torch.nn.Embedding(ACTION_COUNT + 1, 8, padding_idx=0)
        self.image_projection = torch.nn.Sequential(
            torch.nn.Linear(7 * 7 * 16, hidden_dim),
            torch.nn.GELU(),
        )
        self.fusion = torch.nn.Sequential(
            torch.nn.Linear(hidden_dim + 16 + 8, hidden_dim),
            torch.nn.GELU(),
        )

    def forward(self, images: Any, missions: Any, prev_actions: Any) -> Any:
        torch = require_torch()
        obj = self.object_embedding(torch.clamp(images[..., 0], 0, OBJECT_CHANNEL_SIZE - 1))
        color = self.color_embedding(torch.clamp(images[..., 1], 0, COLOR_CHANNEL_SIZE - 1))
        state = self.state_embedding(torch.clamp(images[..., 2], 0, STATE_CHANNEL_SIZE - 1))
        image_features = torch.cat([obj, color, state], dim=-1).flatten(start_dim=2)
        image_latent = self.image_projection(image_features)
        mission_emb = self.mission_embedding(torch.clamp(missions, 0, len(MISSION_VOCAB) + 1))
        mission_mask = (missions != 0).float().unsqueeze(-1)
        mission_sum = (mission_emb * mission_mask).sum(dim=2)
        mission_den = torch.clamp(mission_mask.sum(dim=2), min=1.0)
        mission_latent = mission_sum / mission_den
        prev_action_latent = self.prev_action_embedding(torch.clamp(prev_actions, 0, ACTION_COUNT))
        return self.fusion(torch.cat([image_latent, mission_latent, prev_action_latent], dim=-1))


class GRUPolicy(_PolicyBase):
    def __init__(self, hidden_dim: int) -> None:
        torch = require_torch()
        super().__init__()
        self.encoder = ObservationEncoder(hidden_dim)
        self.gru = torch.nn.GRU(hidden_dim, hidden_dim, batch_first=True)
        self.head = torch.nn.Linear(hidden_dim, ACTION_COUNT)

    def forward(self, images: Any, missions: Any, prev_actions: Any, mask: Any) -> Any:
        encoded = self.encoder(images, missions, prev_actions)
        hidden, _ = self.gru(encoded)
        return self.head(_last_valid(hidden, mask))


class TransformerPolicy(_PolicyBase):
    def __init__(self, hidden_dim: int, *, heads: int = 4) -> None:
        torch = require_torch()
        super().__init__()
        self.encoder = ObservationEncoder(hidden_dim)
        self.position = torch.nn.Parameter(torch.zeros(1, 64, hidden_dim))
        layer = torch.nn.TransformerEncoderLayer(
            d_model=hidden_dim,
            nhead=heads,
            dim_feedforward=hidden_dim * 2,
            dropout=0.0,
            activation="gelu",
            batch_first=True,
            norm_first=False,
        )
        self.transformer = torch.nn.TransformerEncoder(layer, num_layers=1)
        self.head = torch.nn.Linear(hidden_dim, ACTION_COUNT)

    def forward(self, images: Any, missions: Any, prev_actions: Any, mask: Any) -> Any:
        torch = require_torch()
        encoded = self.encoder(images, missions, prev_actions)
        encoded = encoded + self.position[:, : encoded.shape[1], :]
        causal = torch.triu(
            torch.ones(encoded.shape[1], encoded.shape[1], dtype=torch.bool, device=encoded.device),
            diagonal=1,
        )
        hidden = self.transformer(encoded, mask=causal, src_key_padding_mask=~mask)
        return self.head(_last_valid(hidden, mask))


class DGTBCDPolicy(_PolicyBase):
    def __init__(self, hidden_dim: int) -> None:
        torch = require_torch()
        super().__init__()
        self.encoder = ObservationEncoder(hidden_dim)
        self.gate = torch.nn.Sequential(
            torch.nn.Linear(hidden_dim * 2, hidden_dim),
            torch.nn.Sigmoid(),
        )
        self.gru = torch.nn.GRU(hidden_dim, hidden_dim, batch_first=True)
        self.head = torch.nn.Linear(hidden_dim, ACTION_COUNT)

    def forward(self, images: Any, missions: Any, prev_actions: Any, mask: Any) -> Any:
        torch = require_torch()
        encoded = self.encoder(images, missions, prev_actions)
        prev = torch.cat([torch.zeros_like(encoded[:, :1]), encoded[:, :-1]], dim=1)
        derivative = encoded - prev
        gated = encoded * self.gate(torch.cat([encoded, derivative], dim=-1))
        hidden, _ = self.gru(gated)
        return self.head(_last_valid(hidden, mask))


class MemoryRoutingPolicy(_PolicyBase):
    def __init__(self, hidden_dim: int) -> None:
        torch = require_torch()
        super().__init__()
        self.encoder = ObservationEncoder(hidden_dim)
        self.gru = torch.nn.GRU(hidden_dim, hidden_dim, batch_first=True)
        self.query = torch.nn.Linear(hidden_dim, hidden_dim, bias=False)
        self.key = torch.nn.Linear(hidden_dim, hidden_dim, bias=False)
        self.value = torch.nn.Linear(hidden_dim, hidden_dim, bias=False)
        self.mix = torch.nn.Sequential(
            torch.nn.Linear(hidden_dim * 2, hidden_dim),
            torch.nn.GELU(),
        )
        self.head = torch.nn.Linear(hidden_dim, ACTION_COUNT)

    def forward(self, images: Any, missions: Any, prev_actions: Any, mask: Any) -> Any:
        torch = require_torch()
        encoded = self.encoder(images, missions, prev_actions)
        hidden, _ = self.gru(encoded)
        query = self.query(hidden)
        key = self.key(hidden)
        value = self.value(hidden)
        scores = torch.matmul(query, key.transpose(1, 2)) / math.sqrt(float(hidden.shape[-1]))
        causal = torch.triu(
            torch.ones(hidden.shape[1], hidden.shape[1], dtype=torch.bool, device=hidden.device),
            diagonal=1,
        )
        scores = scores.masked_fill(causal.unsqueeze(0), -1.0e9)
        scores = scores.masked_fill((~mask).unsqueeze(1), -1.0e9)
        routed = torch.matmul(torch.softmax(scores, dim=-1), value)
        mixed = self.mix(torch.cat([hidden, routed], dim=-1))
        return self.head(_last_valid(mixed, mask))


def build_model(family: str, *, hidden_dim: int) -> Any:
    if family == "gru":
        return GRUPolicy(hidden_dim)
    if family == "transformer":
        return TransformerPolicy(hidden_dim)
    if family == "dgt_bcd":
        return DGTBCDPolicy(hidden_dim)
    if family == "memory_routing":
        return MemoryRoutingPolicy(hidden_dim)
    raise ValueError(f"unknown arm family: {family}")


def _count_model_parameters(family: str, hidden_dim: int) -> int:
    model = build_model(family, hidden_dim=hidden_dim)
    return int(sum(param.numel() for param in model.parameters() if param.requires_grad))


def _search_matched_hidden_dim(family: str, *, target_count: int, preferred: int) -> int:
    candidates = []
    for dim in range(12, max(160, preferred * 3) + 1):
        if family == "transformer" and dim % 4 != 0:
            continue
        try:
            count = _count_model_parameters(family, dim)
        except Exception:
            continue
        candidates.append((abs(count - target_count), abs(dim - preferred), dim))
    if not candidates:
        raise ValueError(f"could not find matched hidden dim for {family}")
    candidates.sort()
    return int(candidates[0][2])


def make_arm_specs(hidden_dim: int = 64) -> list[ArmSpec]:
    target_count = _count_model_parameters("gru", int(hidden_dim))
    raw_families = [
        ("GRU_base", "gru", 1),
        ("Transformer_base", "transformer", 1),
        ("DGT_BCD", "dgt_bcd", 2),
        ("MemoryRouting", "memory_routing", 2),
    ]
    raw = [
        (
            name,
            family,
            int(hidden_dim) if family == "gru" else _search_matched_hidden_dim(
                family,
                target_count=target_count,
                preferred=int(hidden_dim),
            ),
            priority,
        )
        for name, family, priority in raw_families
    ]
    return [
        ArmSpec(
            name=name,
            family=family,
            hidden_dim=int(dim),
            priority=int(priority),
            parameter_count=_count_model_parameters(family, int(dim)),
        )
        for name, family, dim, priority in raw
    ]


def parameter_match_status(specs: Sequence[ArmSpec]) -> dict[str, Any]:
    counts = {spec.name: int(spec.parameter_count) for spec in specs}
    if not counts:
        return {"status": "fail", "parameter_counts": {}, "max_relative_delta": math.inf}
    center = float(np.mean(list(counts.values())))
    max_delta = max(abs(count - center) / max(1.0, center) for count in counts.values())
    return {
        "status": "pass" if max_delta <= 0.05 else "fail",
        "parameter_counts": counts,
        "max_relative_delta": float(max_delta),
    }


def train_policy(
    spec: ArmSpec,
    dataset: DatasetBundle,
    config: TournamentConfig,
    *,
    seed: int,
    device: str,
) -> tuple[Any, dict[str, Any]]:
    torch = require_torch()
    set_deterministic_seed(seed)
    model = build_model(spec.family, hidden_dim=spec.hidden_dim).to(device)
    optimizer = torch.optim.AdamW(model.parameters(), lr=float(config.learning_rate), weight_decay=1.0e-4)
    natural_sampler = SequenceSampler(
        dataset.train,
        context_length=config.context_length,
        seed=seed + 17,
        balance_actions=False,
    )
    balanced_sampler = SequenceSampler(
        dataset.train,
        context_length=config.context_length,
        seed=seed + 19,
        balance_actions=True,
    )
    validation_sampler = SequenceSampler(
        dataset.validation,
        context_length=config.context_length,
        seed=seed + 23,
        balance_actions=False,
    )
    best_state = copy.deepcopy(model.state_dict())
    best_validation_loss = math.inf
    trace = []
    for step in range(1, int(config.train_steps) + 1):
        model.train()
        images, missions, prev_actions, mask, actions = _mixed_batch(
            natural_sampler,
            balanced_sampler,
            batch_size=int(config.batch_size),
            balanced_fraction=float(config.balanced_batch_fraction),
        )
        logits = model(
            torch.as_tensor(images, dtype=torch.long, device=device),
            torch.as_tensor(missions, dtype=torch.long, device=device),
            torch.as_tensor(prev_actions, dtype=torch.long, device=device),
            torch.as_tensor(mask, dtype=torch.bool, device=device),
        )
        target = torch.as_tensor(actions, dtype=torch.long, device=device)
        loss = torch.nn.functional.cross_entropy(logits, target)
        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
        optimizer.step()
        if step == 1 or step % int(config.eval_interval) == 0 or step == int(config.train_steps):
            validation_loss = _sampled_action_loss(
                model,
                validation_sampler,
                torch=torch,
                device=device,
                batch_size=min(int(config.batch_size), 128),
                batches=4,
            )
            trace.append(
                {
                    "step": int(step),
                    "train_loss": float(loss.detach().cpu().item()),
                    "id_validation_action_loss": float(validation_loss),
                }
            )
            if validation_loss < best_validation_loss:
                best_validation_loss = validation_loss
                best_state = copy.deepcopy(model.state_dict())
    model.load_state_dict(best_state)
    return model, {
        "checkpoint_selection": "minimum ID validation action loss",
        "best_id_validation_action_loss": float(best_validation_loss),
        "trace": trace,
    }


def _policy_action(
    model: Any,
    history_images: list[np.ndarray],
    history_missions: list[np.ndarray],
    history_actions: list[int],
    *,
    torch: Any,
    device: str,
    context_length: int,
) -> int:
    images = np.zeros((1, context_length, 7, 7, 3), dtype=np.int64)
    missions = np.zeros((1, context_length, 16), dtype=np.int64)
    prev_actions = np.zeros((1, context_length), dtype=np.int64)
    mask = np.zeros((1, context_length), dtype=bool)
    length = min(context_length, len(history_images))
    start = len(history_images) - length
    images[0, context_length - length :] = np.asarray(history_images[-length:], dtype=np.int64)
    missions[0, context_length - length :] = np.asarray(history_missions[-length:], dtype=np.int64)
    for col, source_index in enumerate(range(start, len(history_images)), start=context_length - length):
        prev_actions[0, col] = 0 if source_index == 0 else int(history_actions[source_index - 1]) + 1
    mask[0, context_length - length :] = True
    model.eval()
    with torch.no_grad():
        logits = model(
            torch.as_tensor(images, dtype=torch.long, device=device),
            torch.as_tensor(missions, dtype=torch.long, device=device),
            torch.as_tensor(prev_actions, dtype=torch.long, device=device),
            torch.as_tensor(mask, dtype=torch.bool, device=device),
        )
        valid = torch.as_tensor(
            _partial_observation_action_mask(history_images[-1]),
            dtype=torch.bool,
            device=device,
        ).reshape(1, -1)
        logits = logits.masked_fill(~valid, -1.0e9)
        return int(torch.argmax(logits, dim=-1).detach().cpu().item())


def _partial_observation_action_mask(image: np.ndarray) -> np.ndarray:
    front = np.asarray(image, dtype=np.int64)[OBS_FRONT_X, OBS_FRONT_Y]
    obj_id = int(front[0])
    state = int(front[2])
    mask = np.zeros((ACTION_COUNT,), dtype=bool)
    mask[0] = True
    mask[1] = True
    if obj_id in {OBJ_EMPTY, OBJ_GOAL} or (obj_id == OBJ_DOOR and state == 0):
        mask[2] = True
    if obj_id in {OBJ_KEY, OBJ_BALL, OBJ_BOX}:
        mask[3] = True
    if obj_id == OBJ_DOOR:
        mask[5] = True
    return mask


def evaluate_policy_successes(
    model: Any,
    env_id: str,
    *,
    episodes: int,
    seed: int,
    context_length: int,
    device: str,
    max_episode_steps: int | None = None,
) -> np.ndarray:
    torch = require_torch()
    gym, _ = _import_minigrid()
    successes = []
    env = gym.make(env_id)
    try:
        for index in range(int(episodes)):
            observation, _ = env.reset(seed=seed + index)
            history_images: list[np.ndarray] = []
            history_missions: list[np.ndarray] = []
            history_actions: list[int] = []
            limit = int(max_episode_steps or getattr(env.unwrapped, "max_steps", 512))
            success = False
            for _ in range(limit):
                history_images.append(np.asarray(observation["image"], dtype=np.int64))
                history_missions.append(mission_tokens(str(observation.get("mission", ""))))
                action = _policy_action(
                    model,
                    history_images,
                    history_missions,
                    history_actions,
                    torch=torch,
                    device=device,
                    context_length=context_length,
                )
                observation, reward, terminated, truncated, _ = env.step(action)
                history_actions.append(action)
                success = bool(reward > 0)
                if terminated or truncated:
                    break
            successes.append(float(success))
    finally:
        env.close()
    return np.asarray(successes, dtype=np.float32)


def random_policy_successes(
    env_id: str,
    *,
    episodes: int,
    seed: int,
    max_episode_steps: int | None = None,
) -> np.ndarray:
    gym, _ = _import_minigrid()
    successes = []
    rng = np.random.default_rng(seed)
    env = gym.make(env_id)
    try:
        for index in range(int(episodes)):
            observation, _ = env.reset(seed=seed + index)
            limit = int(max_episode_steps or getattr(env.unwrapped, "max_steps", 512))
            success = False
            for _ in range(limit):
                action = int(rng.integers(0, env.action_space.n))
                observation, reward, terminated, truncated, _ = env.step(action)
                success = bool(reward > 0)
                if terminated or truncated:
                    break
            successes.append(float(success))
    finally:
        env.close()
    return np.asarray(successes, dtype=np.float32)


def _split_names() -> tuple[str, str, str]:
    return (SPLIT_ID, SPLIT_OOD_DOOR_KEY, SPLIT_OOD_TRANSFER)


def _summarize_success(values: np.ndarray, *, seed: int, resamples: int) -> dict[str, Any]:
    return bootstrap_mean_ci(values, seed=seed, resamples=resamples).to_dict()


def _aggregate_split_successes(seed_results: Sequence[Mapping[str, Any]], split: str) -> np.ndarray:
    values = []
    for result in seed_results:
        values.extend(float(value) for value in result["splits"][split]["episode_successes"])
    return np.asarray(values, dtype=np.float32)


def _mean_ood_from_arm(arm: Mapping[str, Any]) -> float:
    return float(
        np.mean(
            [
                arm["splits"][SPLIT_OOD_DOOR_KEY]["success"]["mean"],
                arm["splits"][SPLIT_OOD_TRANSFER]["success"]["mean"],
            ]
        )
    )


def _ood_values_from_arm(arm: Mapping[str, Any]) -> np.ndarray:
    values = []
    for split in (SPLIT_OOD_DOOR_KEY, SPLIT_OOD_TRANSFER):
        if "episode_successes" in arm["splits"][split]:
            values.extend(float(x) for x in arm["splits"][split]["episode_successes"])
        else:
            values.append(float(arm["splits"][split]["success"]["mean"]))
    return np.asarray(values, dtype=np.float32)


def gate_and_verdict(
    arms: Mapping[str, Mapping[str, Any]],
    controls: Mapping[str, Mapping[str, Any]],
    *,
    bootstrap_resamples: int = 1000,
) -> dict[str, Any]:
    baseline_names = [name for name, arm in arms.items() if int(arm.get("priority", 99)) == 1]
    if not baseline_names:
        return {
            "validity_gate": {"status": "fail", "reasons": ["no priority-1 baselines were run"]},
            "overall_verdict": "invalid",
        }
    best_baseline_name = max(
        baseline_names,
        key=lambda name: float(arms[name]["splits"][SPLIT_ID]["success"]["mean"]),
    )
    best_baseline = arms[best_baseline_name]
    best_baseline_id = float(best_baseline["splits"][SPLIT_ID]["success"]["mean"])
    best_baseline_ood = _mean_ood_from_arm(best_baseline)
    random_success = float(controls["random_policy"]["success"]["mean"])
    oracle_success = float(controls["oracle"]["success"]["mean"])
    reasons = []
    if best_baseline_id < 0.80:
        reasons.append("baseline ID success below 0.80")
    if best_baseline_ood < 0.15:
        reasons.append("baseline OOD success below 0.15")
    if best_baseline_ood > 0.80:
        reasons.append("baseline OOD success above 0.80")
    if random_success > 0.05:
        reasons.append("random policy success above 0.05")
    if oracle_success < 0.95:
        reasons.append("oracle success below 0.95")
    gate = {
        "status": "pass" if not reasons else "fail",
        "reasons": reasons,
        "best_baseline_id_success": best_baseline_id,
        "best_baseline_ood_success": best_baseline_ood,
        "random_policy_success": random_success,
        "oracle_success": oracle_success,
    }
    result = {
        "validity_gate": gate,
        "best_baseline": {
            "name": best_baseline_name,
            "id_success": best_baseline_id,
            "ood_success": best_baseline_ood,
        },
        "candidates": {},
        "overall_verdict": "invalid" if reasons else "no_signal",
    }
    if reasons:
        return result
    baseline_ood_values = _ood_values_from_arm(best_baseline)
    any_true_win = False
    any_candidate = False
    for name, arm in arms.items():
        if int(arm.get("priority", 99)) <= 1:
            continue
        any_candidate = True
        candidate_ood = _mean_ood_from_arm(arm)
        delta_values = _ood_values_from_arm(arm)
        delta = bootstrap_delta_ci(
            delta_values,
            baseline_ood_values,
            seed=9000 + len(result["candidates"]),
            resamples=bootstrap_resamples,
        )
        split_positive = [
            split
            for split in (SPLIT_OOD_DOOR_KEY, SPLIT_OOD_TRANSFER)
            if float(arm["splits"][split]["success"]["mean"])
            > float(best_baseline["splits"][split]["success"]["mean"])
        ]
        id_drop = best_baseline_id - float(arm["splits"][SPLIT_ID]["success"]["mean"])
        param_status = arm.get("parameter_match", {}).get("status", "unknown")
        true_win = (
            candidate_ood - best_baseline_ood >= 0.10
            and delta.ci_low > 0.03
            and len(split_positive) >= 2
            and id_drop <= 0.02
            and param_status == "pass"
        )
        verdict = "true_win" if true_win else "abstain"
        any_true_win = any_true_win or true_win
        result["candidates"][name] = {
            "ood_success": candidate_ood,
            "delta_ood": delta.to_dict(),
            "positive_ood_splits": split_positive,
            "id_success_drop_vs_baseline": float(id_drop),
            "parameter_match_status": param_status,
            "verdict": verdict,
        }
    if any_true_win:
        result["overall_verdict"] = "true_win"
    elif any_candidate:
        result["overall_verdict"] = "abstain"
    return result


def run_tournament(config: TournamentConfig) -> dict[str, Any]:
    config = replace(config, ood_env_ids=resolve_ood_envs(config.ood_env_ids))
    torch = require_torch()
    device_resolution = choose_device(config.requested_device)
    device = str(device_resolution)
    specs = make_arm_specs(config.hidden_dim)
    priority1 = [spec for spec in specs if spec.priority == 1]
    priority2 = [spec for spec in specs if spec.priority == 2]
    active_specs = list(priority1)
    param_match = parameter_match_status(active_specs)
    split_envs = {
        SPLIT_ID: config.train_env_id,
        SPLIT_OOD_DOOR_KEY: config.ood_env_ids[0],
        SPLIT_OOD_TRANSFER: config.ood_env_ids[1],
    }
    controls = _run_controls(config, split_envs)
    datasets = {seed: collect_dataset(config, seed=seed) for seed in config.seeds}
    arms = _run_specs(
        active_specs,
        datasets,
        config,
        split_envs,
        device=device,
        parameter_match=param_match,
    )
    first_gate = gate_and_verdict(arms, controls, bootstrap_resamples=config.bootstrap_resamples)
    ran_priority2 = False
    if config.run_priority2 and first_gate["validity_gate"]["status"] == "pass":
        active_specs = list(priority1) + list(priority2)
        param_match = parameter_match_status(active_specs)
        p2_arms = _run_specs(
            priority2,
            datasets,
            config,
            split_envs,
            device=device,
            parameter_match=param_match,
        )
        arms.update(p2_arms)
        ran_priority2 = True
    verdict = gate_and_verdict(arms, controls, bootstrap_resamples=config.bootstrap_resamples)
    for name, arm in arms.items():
        if int(arm.get("priority", 99)) == 1:
            arm["selected_by_id_validation"] = bool(name == verdict.get("best_baseline", {}).get("name"))
    return {
        "schema_id": SCHEMA_ID,
        "issue": ISSUE_ID,
        "config": config.to_dict(),
        "device": device_resolution.to_dict(),
        "task_contract": {
            "policy_observation": "partial 7x7 egocentric symbolic image plus mission tokens",
            "oracle_observation": "full state planner used only for labels and expert control",
            "primary_endpoint": "OOD episode success",
            "win_rule": "gain >= +0.10, CI low > +0.03, two OOD splits positive, ID drop <= 0.02, params within 5%",
        },
        "splits": split_envs,
        "dataset_fingerprints": {str(seed): datasets[seed].fingerprint for seed in config.seeds},
        "controls": controls,
        "arms": arms,
        "priority2_ran": ran_priority2,
        "validity_and_verdict": verdict,
    }


def _run_controls(config: TournamentConfig, split_envs: Mapping[str, str]) -> dict[str, Any]:
    random_values = []
    oracle_values = []
    per_split = {}
    control_episodes = max(16, min(int(config.eval_episodes), 96))
    for index, (split, env_id) in enumerate(split_envs.items()):
        random_split = random_policy_successes(
            env_id,
            episodes=control_episodes,
            seed=700000 + index * 10000,
            max_episode_steps=config.max_episode_steps,
        )
        oracle_split = oracle_successes(
            env_id,
            episodes=control_episodes,
            seed=800000 + index * 10000,
            max_episode_steps=config.max_episode_steps,
        )
        random_values.extend(random_split.tolist())
        oracle_values.extend(oracle_split.tolist())
        per_split[split] = {
            "environment_id": env_id,
            "random_policy": _summarize_success(
                random_split,
                seed=710000 + index,
                resamples=config.bootstrap_resamples,
            ),
            "oracle": _summarize_success(
                oracle_split,
                seed=810000 + index,
                resamples=config.bootstrap_resamples,
            ),
        }
    return {
        "random_policy": {
            "success": _summarize_success(
                np.asarray(random_values, dtype=np.float32),
                seed=720000,
                resamples=config.bootstrap_resamples,
            )
        },
        "oracle": {
            "success": _summarize_success(
                np.asarray(oracle_values, dtype=np.float32),
                seed=820000,
                resamples=config.bootstrap_resamples,
            )
        },
        "per_split": per_split,
    }


def _run_specs(
    specs: Sequence[ArmSpec],
    datasets: Mapping[int, DatasetBundle],
    config: TournamentConfig,
    split_envs: Mapping[str, str],
    *,
    device: str,
    parameter_match: Mapping[str, Any],
) -> dict[str, Any]:
    arms: dict[str, Any] = {}
    for spec in specs:
        seed_results = []
        for seed in config.seeds:
            model, training = train_policy(spec, datasets[int(seed)], config, seed=int(seed), device=device)
            split_results = {}
            for split_index, split in enumerate(_split_names()):
                env_id = split_envs[split]
                successes = evaluate_policy_successes(
                    model,
                    env_id,
                    episodes=int(config.eval_episodes),
                    seed=300000 + int(seed) * 10000 + split_index * 1000,
                    context_length=int(config.context_length),
                    device=device,
                    max_episode_steps=config.max_episode_steps,
                )
                split_results[split] = {
                    "environment_id": env_id,
                    "episode_successes": [float(value) for value in successes],
                    "success": _summarize_success(
                        successes,
                        seed=310000 + int(seed) * 10000 + split_index,
                        resamples=config.bootstrap_resamples,
                    ),
                }
            seed_results.append(
                {
                    "seed": int(seed),
                    "training": training,
                    "splits": split_results,
                }
            )
        aggregate_splits = {}
        for split in _split_names():
            values = _aggregate_split_successes(seed_results, split)
            aggregate_splits[split] = {
                "environment_id": split_envs[split],
                "episode_successes": [float(value) for value in values],
                "success": _summarize_success(
                    values,
                    seed=410000 + len(arms) * 1000 + list(_split_names()).index(split),
                    resamples=config.bootstrap_resamples,
                ),
            }
        arms[spec.name] = {
            "name": spec.name,
            "family": spec.family,
            "priority": int(spec.priority),
            "hidden_dim": int(spec.hidden_dim),
            "parameter_count": int(spec.parameter_count),
            "parameter_match": dict(parameter_match),
            "seed_results": seed_results,
            "splits": aggregate_splits,
        }
    return arms


def write_report_json(payload: Mapping[str, Any], path: str | Path) -> None:
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_report_markdown(payload: Mapping[str, Any], path: str | Path) -> None:
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    verdict = payload.get("validity_and_verdict", {})
    gate = verdict.get("validity_gate", {})
    best = verdict.get("best_baseline", {})
    controls = payload.get("controls", {})
    random_success = controls.get("random_policy", {}).get("success", {})
    oracle_success = controls.get("oracle", {}).get("success", {})
    config = payload.get("config", {})
    lines = [
        "# MG-CAP Tournament",
        "",
        f"Issue: {payload.get('issue', ISSUE_ID)}",
        "",
        "Primary endpoint: OOD episode success",
        "",
        "## Run Budget",
        "",
        f"- Seeds: {config.get('seeds', [])}",
        f"- Demo episodes: {config.get('demo_episodes', 'unknown')}",
        f"- Eval episodes per seed/split: {config.get('eval_episodes', 'unknown')}",
        f"- Train steps per arm/seed: {config.get('train_steps', 'unknown')}",
        f"- Max episode steps: {config.get('max_episode_steps', 'environment default')}",
        "",
        "## Validity Gate",
        "",
        f"- Status: {gate.get('status', 'unknown')}",
        f"- Reasons: {', '.join(gate.get('reasons', [])) or 'none'}",
        f"- Best baseline: {best.get('name', 'none')}",
        f"- Best baseline ID success: {best.get('id_success', math.nan):.3f}",
        f"- Best baseline OOD success: {best.get('ood_success', math.nan):.3f}",
        f"- Random policy success: {random_success.get('mean', math.nan):.3f}",
        f"- Oracle success: {oracle_success.get('mean', math.nan):.3f}",
        f"- Overall verdict: {verdict.get('overall_verdict', 'unknown')}",
        f"- Priority-2 arms run: {bool(payload.get('priority2_ran', False))}",
        "",
        "## Arms",
        "",
        "| Arm | ID success | OOD DoorKey | OOD transfer | Params |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for name, arm in payload.get("arms", {}).items():
        lines.append(
            "| {name} | {id_s:.3f} [{id_l:.3f}, {id_h:.3f}] | "
            "{ood1:.3f} [{ood1_l:.3f}, {ood1_h:.3f}] | "
            "{ood2:.3f} [{ood2_l:.3f}, {ood2_h:.3f}] | {params} |".format(
                name=name,
                id_s=arm["splits"][SPLIT_ID]["success"]["mean"],
                id_l=arm["splits"][SPLIT_ID]["success"]["ci_low"],
                id_h=arm["splits"][SPLIT_ID]["success"]["ci_high"],
                ood1=arm["splits"][SPLIT_OOD_DOOR_KEY]["success"]["mean"],
                ood1_l=arm["splits"][SPLIT_OOD_DOOR_KEY]["success"]["ci_low"],
                ood1_h=arm["splits"][SPLIT_OOD_DOOR_KEY]["success"]["ci_high"],
                ood2=arm["splits"][SPLIT_OOD_TRANSFER]["success"]["mean"],
                ood2_l=arm["splits"][SPLIT_OOD_TRANSFER]["success"]["ci_low"],
                ood2_h=arm["splits"][SPLIT_OOD_TRANSFER]["success"]["ci_high"],
                params=arm.get("parameter_count", ""),
            )
        )
    lines.extend(["", "## Candidate Deltas", ""])
    candidates = verdict.get("candidates", {})
    if not candidates:
        if gate.get("status") == "pass":
            lines.append("No priority-2 candidate was interpreted.")
        else:
            lines.append("Priority-2 candidates were not run because the task-validity gate failed.")
    else:
        lines.extend(["| Candidate | Delta OOD | CI95 | Verdict |", "| --- | ---: | ---: | --- |"])
        for name, result in candidates.items():
            delta = result["delta_ood"]
            lines.append(
                f"| {name} | {delta['mean']:.3f} | "
                f"[{delta['ci_low']:.3f}, {delta['ci_high']:.3f}] | {result['verdict']} |"
            )
    lines.append("")
    target.write_text("\n".join(lines) + "\n", encoding="utf-8")


def honest_summary(payload: Mapping[str, Any]) -> str:
    verdict = payload["validity_and_verdict"]
    gate = verdict["validity_gate"]
    best = verdict.get("best_baseline", {})
    candidates = verdict.get("candidates", {})
    best_delta = "nan±[nan,nan]"
    if candidates:
        top = max(candidates.values(), key=lambda item: item["delta_ood"]["mean"])
        delta = top["delta_ood"]
        best_delta = f"{delta['mean']:.3f}±[{delta['ci_low']:.3f},{delta['ci_high']:.3f}]"
    arms = ",".join(payload.get("arms", {}).keys())
    verdict_label = {
        "true_win": "真胜利",
        "abstain": "abstain",
        "no_signal": "无信号",
        "invalid": "invalid",
    }.get(verdict.get("overall_verdict", "invalid"), str(verdict.get("overall_verdict", "invalid")))
    return (
        "MGCAP_DONE: "
        f"validity={gate.get('status')} "
        f"best_baseline_ID={best.get('id_success', math.nan):.3f} "
        f"best_baseline_OOD={best.get('ood_success', math.nan):.3f} "
        f"arms=[{arms}] "
        f"best_candidate_OOD_delta={best_delta} "
        f"verdict={verdict_label}"
    )

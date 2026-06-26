"""Latent-claim certificates over fixed V-JEPA2-AC carrier features."""

from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import traceback
from typing import Any

import numpy as np

os.environ.setdefault("CUBLAS_WORKSPACE_CONFIG", ":4096:8")

from bedc_quality_lab.latent_claim_certificate import (
    ALPHAS,
    PRIMARY_ALPHA,
    LatentCarrierSplit,
    certify_latent_claim,
    source_gap_claim,
)
from bedc_quality_lab.public_jepa_baselines import (
    PUBLIC_VJEPA2_AC_GIANT_CHECKPOINT_URL,
    _load_vjepa2_ac_giant_modules,
)
from bedc_quality_lab.public_minigrid_native_benchmark import (
    DEFAULT_ENVIRONMENT_ID,
    _agent_position,
    _distance_to_object,
    _door_key_labels,
    _object_mask,
)


REPORTS = Path(__file__).resolve().parents[1] / "reports"


def _dependency_status() -> dict[str, str]:
    return {
        name: "installed" if importlib.util.find_spec(name) is not None else "missing"
        for name in ("gymnasium", "minigrid", "torch", "timm", "einops")
    }


def _image_to_rgb(image: Any, *, size: int = 256) -> np.ndarray:
    symbolic = np.asarray(image, dtype=np.int64)
    object_ids = symbolic[:, :, 0]
    color_table = np.asarray(
        [
            [0.02, 0.02, 0.02],
            [0.15, 0.15, 0.15],
            [0.50, 0.50, 0.50],
            [0.20, 0.60, 0.90],
            [0.75, 0.45, 0.15],
            [0.90, 0.85, 0.20],
            [0.65, 0.40, 0.90],
            [0.20, 0.80, 0.40],
            [0.10, 0.80, 0.15],
            [0.85, 0.20, 0.25],
            [0.95, 0.95, 0.95],
            [0.40, 0.70, 0.95],
        ],
        dtype=np.float32,
    )
    rgb = color_table[np.clip(object_ids, 0, color_table.shape[0] - 1)]
    scale = int(np.ceil(size / rgb.shape[0]))
    expanded = np.repeat(np.repeat(rgb, scale, axis=0), scale, axis=1)
    return expanded[:size, :size, :]


def _state_contract(image: Any, action_count: int) -> np.ndarray:
    agent = _agent_position(image) / 7.0
    visible = np.asarray(
        [
            float(np.any(_object_mask(image, 5))),
            float(np.any(_object_mask(image, 4))),
            float(np.any(_object_mask(image, 8))),
        ],
        dtype=np.float32,
    )
    nearest = min(_distance_to_object(image, 5), _distance_to_object(image, 4), _distance_to_object(image, 8)) / 10.0
    return np.asarray(
        [
            float(agent[0]),
            float(agent[1]),
            float(visible[0]),
            float(visible[1]),
            float(visible[2]),
            float(nearest),
            float(action_count) / 10.0,
        ],
        dtype=np.float32,
    )


def _action_contract(action: int, action_count: int) -> np.ndarray:
    vector = np.zeros(7, dtype=np.float32)
    vector[int(action)] = 1.0
    if action_count < 7:
        vector[-1] = float(action_count) / 10.0
    return vector


def _collect_minigrid_transitions(
    *,
    environment_id: str,
    sample_count: int,
    seed: int,
) -> dict[str, np.ndarray]:
    import gymnasium as gym
    import minigrid  # noqa: F401

    env = gym.make(environment_id)
    try:
        observation, _ = env.reset(seed=seed)
        action_count = int(env.action_space.n)
        rng = np.random.default_rng(seed)
        videos = []
        actions = []
        states = []
        labels = []
        gaps = []
        for index in range(sample_count):
            action = int(rng.integers(action_count))
            image = observation["image"]
            next_observation, _, terminated, truncated, _ = env.step(action)
            next_image = next_observation["image"]
            label, gap = _door_key_labels(next_image)
            video = np.stack([_image_to_rgb(image), _image_to_rgb(next_image)], axis=0)
            videos.append(video)
            actions.append(_action_contract(action, action_count))
            states.append(_state_contract(image, action_count))
            labels.append(label)
            gaps.append(gap)
            observation = next_observation
            if terminated or truncated:
                observation, _ = env.reset(seed=seed + index + 1)
        video_array = np.asarray(videos, dtype=np.float32)
        video_array = np.transpose(video_array, (0, 4, 1, 2, 3))
        return {
            "videos": video_array,
            "actions": np.asarray(actions, dtype=np.float32)[:, None, :],
            "states": np.asarray(states, dtype=np.float32)[:, None, :],
            "door_key_context_visible": np.asarray(labels, dtype=bool),
            "unsafe_transition": np.asarray(gaps, dtype=bool),
        }
    finally:
        env.close()


def _extract_features(
    carrier: dict[str, np.ndarray],
    *,
    batch_size: int,
    device: str,
    use_amp: bool,
) -> np.ndarray:
    encoder, predictor, _ = _load_vjepa2_ac_giant_modules(num_frames=2)
    encoder.eval().to(device)
    predictor.eval().to(device)
    return _extract_features_with_modules(
        carrier,
        encoder=encoder,
        predictor=predictor,
        batch_size=batch_size,
        device=device,
        use_amp=use_amp,
    )


def _extract_features_with_modules(
    carrier: dict[str, np.ndarray],
    *,
    encoder: Any,
    predictor: Any,
    batch_size: int,
    device: str,
    use_amp: bool,
) -> np.ndarray:
    import torch

    features: list[np.ndarray] = []
    videos = torch.from_numpy(carrier["videos"])
    actions_np = carrier["actions"]
    states_np = carrier["states"]
    amp_enabled = bool(use_amp and device == "cuda")
    with torch.inference_mode():
        for start in range(0, videos.shape[0], batch_size):
            stop = min(start + batch_size, videos.shape[0])
            video = videos[start:stop].to(device, non_blocking=True)
            actions = torch.from_numpy(actions_np[start:stop]).to(device, non_blocking=True)
            states = torch.from_numpy(states_np[start:stop]).to(device, non_blocking=True)
            with torch.cuda.amp.autocast(enabled=amp_enabled):
                tokens = encoder(video)
                predicted = predictor(tokens, actions, states)
                pooled = predicted.mean(dim=1)
            features.append(pooled.detach().float().cpu().numpy())
            del video, actions, states, tokens, predicted, pooled
            if device == "cuda":
                torch.cuda.empty_cache()
    return np.concatenate(features, axis=0)


def build_vjepa2_ac_claim_certificate_packet(
    *,
    features_train: np.ndarray,
    labels_train: np.ndarray,
    gaps_train: np.ndarray,
    features_calibration: np.ndarray,
    labels_calibration: np.ndarray,
    gaps_calibration: np.ndarray,
    features_test: np.ndarray,
    labels_test: np.ndarray,
    gaps_test: np.ndarray,
    environment_id: str = DEFAULT_ENVIRONMENT_ID,
    carrier_id: str = "vjepa2-ac-giant-fixed-minigrid-carrier",
    torch_environment: dict[str, Any] | None = None,
    execution_contract: dict[str, Any] | None = None,
    checkpoint_contract: dict[str, Any] | None = None,
    feature_contract: dict[str, Any] | None = None,
) -> dict[str, Any]:
    claims = [
        certify_latent_claim(
            LatentCarrierSplit(
                carrier_id=carrier_id,
                source="fixed V-JEPA2-AC Giant checkpoint features over the public MiniGrid image/action stream",
                features_train=features_train,
                labels_train=labels_train,
                features_calibration=features_calibration,
                labels_calibration=labels_calibration,
                features_test=features_test,
                labels_test=labels_test,
                predicate="door_key_context_visible",
                test_surface="action-conditioned MiniGrid transition with visible key, door, or goal context",
                stability_condition="disjoint train/calibration/test seeds over the same public MiniGrid environment",
                gap_policy="split conformal singleton claims; non-singleton sets are ledgered as coverage debt",
            )
        ),
        certify_latent_claim(
            LatentCarrierSplit(
                carrier_id=carrier_id,
                source="fixed V-JEPA2-AC Giant checkpoint features over the public MiniGrid image/action stream",
                features_train=features_train,
                labels_train=gaps_train,
                features_calibration=features_calibration,
                labels_calibration=gaps_calibration,
                features_test=features_test,
                labels_test=gaps_test,
                predicate="unsafe_transition",
                test_surface="boundary-like DoorKey transition context used as the public MiniGrid gap surface",
                stability_condition="disjoint train/calibration/test seeds over the same public MiniGrid environment",
                gap_policy="split conformal singleton claims; non-singleton sets are ledgered as coverage debt",
            )
        ),
        source_gap_claim(
            carrier_id=carrier_id,
            source=environment_id,
            predicate="has_key",
            test_surface="pickup intervention changes carried-key state",
            stability_condition="inventory-state source split",
            reason="the fixed-carrier packet uses image/action observations and does not expose a carried-key source trace",
        ),
        source_gap_claim(
            carrier_id=carrier_id,
            source=environment_id,
            predicate="door_open_or_unlocked",
            test_surface="toggle intervention changes door transition state",
            stability_condition="door-state source split",
            reason="the fixed-carrier packet does not preserve a separate door-state label split",
        ),
        source_gap_claim(
            carrier_id=carrier_id,
            source=environment_id,
            predicate="goal_reachable_with_current_state",
            test_surface="planner feasibility under current known state",
            stability_condition="environment-graph source split",
            reason="the fixed-carrier packet does not expose a graph-level reachability source split",
        ),
    ]
    return {
        "schema_id": "bedc-vjepa2-ac-minigrid-claim-certificate",
        "status": "executed",
        "protocol": "Latent Claim Certificate Protocol",
        "environment_id": environment_id,
        "carrier_id": carrier_id,
        "risk_level": PRIMARY_ALPHA,
        "alphas": [float(alpha) for alpha in ALPHAS],
        "torch_environment": torch_environment or {},
        "execution_contract": execution_contract
        or {
            "run_command": "python scripts/run_vjepa2_ac_minigrid_claim_certificate.py",
            "environment_id": environment_id,
            "train_count": float(features_train.shape[0]),
            "calibration_count": float(features_calibration.shape[0]),
            "test_count": float(features_test.shape[0]),
            "split_rule": "disjoint train, calibration, and test transition streams are used for LCCP readback",
        },
        "checkpoint_contract": checkpoint_contract
        or {
            "repository_url": "https://github.com/facebookresearch/vjepa2",
            "hub_entry": "vjepa2_ac_vit_giant",
            "checkpoint_url": PUBLIC_VJEPA2_AC_GIANT_CHECKPOINT_URL,
            "candidate_id": "vjepa2-ac-vit-giant",
            "loaded_components": ["encoder", "predictor"],
            "checkpoint_loading": "torch hub model structure with explicit public checkpoint state dictionaries for encoder and predictor",
            "official_benchmark_boundary": "this packet certifies fixed-carrier readback on a MiniGrid stream and does not reproduce the official V-JEPA2-AC benchmark protocol",
        },
        "feature_contract": feature_contract
        or {
            "carrier_features": "action-conditioned predictor pooled token features over two-frame MiniGrid transition videos",
            "video_contract": "two 256x256 RGB frames rendered from MiniGrid symbolic observations before and after the sampled action",
            "action_contract": "one-hot MiniGrid action vector with an auxiliary action-count coordinate",
            "state_contract": "agent position, visible key/door/goal indicators, nearest-object distance, and action-count coordinate",
            "certificate_protocol": "split conformal singleton claims over linear readout scores; non-singleton sets are ledgered as coverage debt",
        },
        "claims": claims,
        "accepted_claim_count": float(sum(1 for claim in claims if claim["claim_status"] == "certified")),
        "gap_claim_count": float(sum(1 for claim in claims if claim["claim_status"] != "certified")),
        "cannot_claim": [
            "public benchmark superiority",
            "native V-JEPA2-AC rollout reproduction",
            "natural-language semantic grounding",
            "global latent interpretability",
        ],
    }


def run_vjepa2_ac_minigrid_claim_certificate(
    *,
    environment_id: str = DEFAULT_ENVIRONMENT_ID,
    train_count: int = 16,
    calibration_count: int = 16,
    test_count: int = 16,
    seed: int = 20260608,
    batch_size: int = 1,
    device: str = "cuda",
    use_amp: bool = True,
) -> dict[str, Any]:
    deps = _dependency_status()
    try:
        import torch

        cuda_available = bool(torch.cuda.is_available())
        torch_environment = {
            "torch_version": str(torch.__version__),
            "cuda_available": cuda_available,
            "cuda_device_name": str(torch.cuda.get_device_name(0)) if cuda_available else "",
            "device": device,
        }
        if device == "cuda" and not cuda_available:
            raise RuntimeError("CUDA requested but torch.cuda.is_available() is false")
        train = _collect_minigrid_transitions(environment_id=environment_id, sample_count=train_count, seed=seed)
        calibration = _collect_minigrid_transitions(
            environment_id=environment_id,
            sample_count=calibration_count,
            seed=seed + 1,
        )
        test = _collect_minigrid_transitions(environment_id=environment_id, sample_count=test_count, seed=seed + 2)
        encoder, predictor, _ = _load_vjepa2_ac_giant_modules(num_frames=2)
        encoder.eval().to(device)
        predictor.eval().to(device)
        features_train = _extract_features_with_modules(
            train,
            encoder=encoder,
            predictor=predictor,
            batch_size=batch_size,
            device=device,
            use_amp=use_amp,
        )
        features_calibration = _extract_features_with_modules(
            calibration,
            encoder=encoder,
            predictor=predictor,
            batch_size=batch_size,
            device=device,
            use_amp=use_amp,
        )
        features_test = _extract_features_with_modules(
            test,
            encoder=encoder,
            predictor=predictor,
            batch_size=batch_size,
            device=device,
            use_amp=use_amp,
        )
        packet = build_vjepa2_ac_claim_certificate_packet(
            features_train=features_train,
            labels_train=train["door_key_context_visible"],
            gaps_train=train["unsafe_transition"],
            features_calibration=features_calibration,
            labels_calibration=calibration["door_key_context_visible"],
            gaps_calibration=calibration["unsafe_transition"],
            features_test=features_test,
            labels_test=test["door_key_context_visible"],
            gaps_test=test["unsafe_transition"],
            environment_id=environment_id,
            torch_environment=torch_environment,
            execution_contract={
                "run_command": "python scripts/run_vjepa2_ac_minigrid_claim_certificate.py",
                "environment_id": environment_id,
                "seed": float(seed),
                "train_seed": float(seed),
                "calibration_seed": float(seed + 1),
                "test_seed": float(seed + 2),
                "train_count": float(train_count),
                "calibration_count": float(calibration_count),
                "test_count": float(test_count),
                "batch_size": float(batch_size),
                "device": device,
                "use_amp": bool(use_amp),
                "split_rule": "disjoint seeded transition streams; train fits readouts, calibration sets conformal thresholds, test reports claims and gaps",
            },
            checkpoint_contract={
                "repository_url": "https://github.com/facebookresearch/vjepa2",
                "hub_entry": "vjepa2_ac_vit_giant",
                "checkpoint_url": PUBLIC_VJEPA2_AC_GIANT_CHECKPOINT_URL,
                "candidate_id": "vjepa2-ac-vit-giant",
                "loaded_components": ["encoder", "predictor"],
                "checkpoint_loading": "torch hub model structure with explicit public checkpoint state dictionaries for encoder and predictor",
                "official_benchmark_boundary": "this packet certifies fixed-carrier readback on a MiniGrid stream and does not reproduce the official V-JEPA2-AC benchmark protocol",
            },
            feature_contract={
                "carrier_features": "action-conditioned predictor pooled token features over two-frame MiniGrid transition videos",
                "video_contract": "two 256x256 RGB frames rendered from MiniGrid symbolic observations before and after the sampled action",
                "action_contract": "one-hot MiniGrid action vector with an auxiliary action-count coordinate",
                "state_contract": "agent position, visible key/door/goal indicators, nearest-object distance, and action-count coordinate",
                "certificate_protocol": "split conformal singleton claims over linear readout scores; non-singleton sets are ledgered as coverage debt",
            },
        )
        packet["dependency_status"] = deps
        packet["sample_counts"] = {
            "train": float(train_count),
            "calibration": float(calibration_count),
            "test": float(test_count),
        }
        return packet
    except Exception as exc:  # pragma: no cover - environment-dependent carrier boundary
        return {
            "schema_id": "bedc-vjepa2-ac-minigrid-claim-certificate",
            "status": "source_gap",
            "protocol": "Latent Claim Certificate Protocol",
            "environment_id": environment_id,
            "carrier_id": "vjepa2-ac-giant-fixed-minigrid-carrier",
            "dependency_status": deps,
            "exception_type": type(exc).__name__,
            "message": str(exc),
            "trace_tail": traceback.format_exc().splitlines()[-8:],
            "claims": [
                source_gap_claim(
                    carrier_id="vjepa2-ac-giant-fixed-minigrid-carrier",
                    source=environment_id,
                    predicate="door_key_context_visible",
                    test_surface="action-conditioned MiniGrid transition",
                    stability_condition="disjoint train/calibration/test seeds",
                    reason="fixed V-JEPA2-AC MiniGrid carrier features could not be extracted",
                )
            ],
            "cannot_claim": [
                "certified V-JEPA2-AC MiniGrid latent claim",
                "public benchmark superiority",
                "native V-JEPA2-AC rollout reproduction",
            ],
        }


def write_vjepa2_ac_minigrid_claim_certificate(path: str | Path) -> dict[str, Any]:
    packet = run_vjepa2_ac_minigrid_claim_certificate()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet

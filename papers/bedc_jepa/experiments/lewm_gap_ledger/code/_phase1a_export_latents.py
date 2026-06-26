from __future__ import annotations

import argparse
import json
from pathlib import Path

import h5py
import hdf5plugin  # noqa: F401 - registers blosc HDF5 filter
import numpy as np
import torch
import torch.nn.functional as F
from huggingface_hub import hf_hub_download

from lewm_latent_probe import build_model, load_checkpoint


MODEL_REPO = "quentinll/lewm-tworooms"
FRAMESKIP = 5
HISTORY_SIZE = 3
IMAGENET_MEAN = np.array([0.485, 0.456, 0.406], dtype=np.float32)
IMAGENET_STD = np.array([0.229, 0.224, 0.225], dtype=np.float32)


def to_model_pixels(frames: np.ndarray, image_size: int, device: torch.device) -> torch.Tensor:
    x = torch.from_numpy(frames).to(device=device, dtype=torch.float32)
    x = x.permute(0, 3, 1, 2).div_(255.0)
    mean = torch.tensor(IMAGENET_MEAN, device=device).view(1, 3, 1, 1)
    std = torch.tensor(IMAGENET_STD, device=device).view(1, 3, 1, 1)
    x = (x - mean) / std
    if x.shape[-2:] != (image_size, image_size):
        x = F.interpolate(x, size=(image_size, image_size), mode="bilinear", align_corners=False)
    return x


def action_blocks_for_episode(action: np.ndarray, offset: int, ep_len: int, frameskip: int) -> tuple[np.ndarray, np.ndarray]:
    frame_rel = np.arange(0, ep_len, frameskip, dtype=np.int64)
    blocks = np.zeros((len(frame_rel), frameskip * action.shape[1]), dtype=np.float32)
    for i, rel in enumerate(frame_rel):
        raw = action[offset + rel : offset + min(rel + frameskip, ep_len)]
        if len(raw) < frameskip:
            padded = np.zeros((frameskip, action.shape[1]), dtype=np.float32)
            padded[: len(raw)] = raw
            raw = padded
        blocks[i] = raw.reshape(-1)
    return frame_rel, blocks


def fit_action_block_stats(h5: h5py.File, episode_count: int, frameskip: int) -> tuple[np.ndarray, np.ndarray, int]:
    action = h5["action"]
    ep_len = h5["ep_len"][:episode_count]
    ep_offset = h5["ep_offset"][:episode_count]
    blocks: list[np.ndarray] = []
    for length, offset in zip(ep_len, ep_offset):
        if length <= frameskip:
            continue
        _, ep_blocks = action_blocks_for_episode(action, int(offset), int(length), frameskip)
        blocks.append(ep_blocks[:-1])
    data = np.concatenate(blocks, axis=0)
    mean = data.mean(axis=0).astype(np.float32)
    std = data.std(axis=0, ddof=1).astype(np.float32)
    std[std == 0] = 1.0
    return mean, std, int(data.shape[0])


def choose_episodes(ep_len: np.ndarray, min_transitions: int, max_transitions: int) -> tuple[np.ndarray, int]:
    chosen: list[int] = []
    total = 0
    for ep_i, length in enumerate(ep_len):
        transitions = int((int(length) - 1) // FRAMESKIP)
        if transitions <= 0:
            continue
        if total >= min_transitions and total + transitions > max_transitions:
            break
        chosen.append(ep_i)
        total += transitions
        if total >= max_transitions:
            break
    return np.array(chosen, dtype=np.int32), total


def percentile_stats(x: np.ndarray) -> tuple[list[str], np.ndarray]:
    x = x[np.isfinite(x)]
    names = ["mean", "std", "min", "p05", "p25", "p50", "p75", "p95", "max"]
    vals = np.array(
        [
            x.mean(),
            x.std(),
            x.min(),
            np.percentile(x, 5),
            np.percentile(x, 25),
            np.percentile(x, 50),
            np.percentile(x, 75),
            np.percentile(x, 95),
            x.max(),
        ],
        dtype=np.float64,
    )
    return names, vals


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--h5", default="_tworoom_prefix.h5")
    parser.add_argument("--out", default="tworooms_latent.npz")
    parser.add_argument("--device", default="cuda" if torch.cuda.is_available() else "cpu")
    parser.add_argument("--min-transitions", type=int, default=300)
    parser.add_argument("--max-transitions", type=int, default=650)
    parser.add_argument("--stats-episodes", type=int, default=1024)
    parser.add_argument("--predict-batch", type=int, default=512)
    args = parser.parse_args()

    device = torch.device(args.device)
    checkpoint_path = hf_hub_download(MODEL_REPO, "weights.pt", repo_type="model")
    config_path = hf_hub_download(MODEL_REPO, "config.json", repo_type="model")
    with open(config_path, "r", encoding="utf-8") as f:
        config = json.load(f)
    image_size = int(config["encoder"]["image_size"])
    action_dim = int(config["action_encoder"]["input_dim"])
    if action_dim != 10:
        raise RuntimeError(f"expected action_dim=10 for tworooms checkpoint, got {action_dim}")

    print(f"loading model on {device}", flush=True)
    model = build_model(config)
    load_checkpoint(model, checkpoint_path)
    model.to(device).eval().requires_grad_(False)

    h5_path = Path(args.h5)
    with h5py.File(h5_path, "r") as h5:
        print("fitting local action-block normalizer", flush=True)
        action_mean, action_std, stats_blocks = fit_action_block_stats(
            h5, episode_count=args.stats_episodes, frameskip=FRAMESKIP
        )

        ep_len_all = h5["ep_len"][: args.stats_episodes]
        chosen, total_transitions = choose_episodes(ep_len_all, args.min_transitions, args.max_transitions)
        ep_lens = h5["ep_len"][chosen]
        ep_offsets = h5["ep_offset"][chosen]
        max_t = int(max((int(length) - 1) // FRAMESKIP + 1 for length in ep_lens))
        n_ep = len(chosen)
        print(f"selected_episodes={n_ep} transitions={total_transitions} max_t={max_t}", flush=True)

        emb = np.full((n_ep, max_t, 192), np.nan, dtype=np.float32)
        action_block_raw = np.full((n_ep, max_t, 10), np.nan, dtype=np.float32)
        action_block_norm = np.full((n_ep, max_t, 10), np.nan, dtype=np.float32)
        raw_frame_idx = np.full((n_ep, max_t), -1, dtype=np.int64)
        valid_mask = np.zeros((n_ep, max_t), dtype=bool)

        frame_fields = {
            "ep_idx": np.full((n_ep, max_t), -1, dtype=np.int32),
            "step_idx": np.full((n_ep, max_t), -1, dtype=np.int64),
            "id": np.full((n_ep, max_t), -1, dtype=np.int64),
            "observation": np.full((n_ep, max_t, 10), np.nan, dtype=np.float64),
            "pos_agent": np.full((n_ep, max_t, 2), np.nan, dtype=np.float32),
            "pos_target": np.full((n_ep, max_t, 2), np.nan, dtype=np.float32),
            "proprio": np.full((n_ep, max_t, 2), np.nan, dtype=np.float32),
            "distance_to_target": np.full((n_ep, max_t), np.nan, dtype=np.float64),
            "reward": np.full((n_ep, max_t), np.nan, dtype=np.float64),
            "render_time": np.full((n_ep, max_t), np.nan, dtype=np.float64),
            "terminated": np.zeros((n_ep, max_t), dtype=bool),
            "truncated": np.zeros((n_ep, max_t), dtype=bool),
        }

        for out_i, (ep_i, offset, length) in enumerate(zip(chosen, ep_offsets, ep_lens)):
            offset = int(offset)
            length = int(length)
            frame_rel, blocks = action_blocks_for_episode(h5["action"], offset, length, FRAMESKIP)
            idx = offset + frame_rel
            t = len(idx)
            frames = h5["pixels"][idx]
            pixels = to_model_pixels(frames, image_size=image_size, device=device)
            with torch.inference_mode():
                ep_emb = model.encode({"pixels": pixels.unsqueeze(0)})["emb"][0].detach().cpu().numpy()

            emb[out_i, :t] = ep_emb
            action_block_raw[out_i, :t] = blocks
            action_block_norm[out_i, :t] = (blocks - action_mean) / action_std
            raw_frame_idx[out_i, :t] = idx
            valid_mask[out_i, :t] = True

            for name, arr in frame_fields.items():
                arr[out_i, :t] = h5[name][idx]
            print(f"encoded episode {out_i + 1}/{n_ep}: ep_idx={ep_i} T={t}", flush=True)

    pred = np.full((n_ep, max_t - 1, 192), np.nan, dtype=np.float32)
    transition_mask = valid_mask[:, 1:]

    windows_emb: list[np.ndarray] = []
    windows_act: list[np.ndarray] = []
    windows_meta: list[tuple[int, int, int]] = []
    for ep_i in range(n_ep):
        t_ep = int(valid_mask[ep_i].sum())
        if t_ep < HISTORY_SIZE + 1:
            continue
        for transition_t in range(t_ep - 1):
            start = 0 if transition_t < HISTORY_SIZE else transition_t - HISTORY_SIZE + 1
            pos = transition_t - start
            windows_emb.append(emb[ep_i, start : start + HISTORY_SIZE])
            windows_act.append(action_block_norm[ep_i, start : start + HISTORY_SIZE])
            windows_meta.append((ep_i, transition_t, pos))

    print(f"predict_windows={len(windows_meta)}", flush=True)
    with torch.inference_mode():
        for lo in range(0, len(windows_meta), args.predict_batch):
            hi = min(lo + args.predict_batch, len(windows_meta))
            batch_emb = torch.from_numpy(np.stack(windows_emb[lo:hi])).to(device=device, dtype=torch.float32)
            batch_act = torch.from_numpy(np.stack(windows_act[lo:hi])).to(device=device, dtype=torch.float32)
            batch_pred = model.predict(batch_emb, model.action_encoder(batch_act)).detach().cpu().numpy()
            for row, (ep_i, transition_t, pos) in enumerate(windows_meta[lo:hi]):
                pred[ep_i, transition_t] = batch_pred[row, pos]

    target = emb[:, 1:, :]
    sq = (pred - target) ** 2
    mse = np.full(pred.shape[:2], np.nan, dtype=np.float32)
    l2 = np.full(pred.shape[:2], np.nan, dtype=np.float32)
    mse[transition_mask] = sq[transition_mask].mean(axis=-1).astype(np.float32)
    l2[transition_mask] = np.sqrt(sq[transition_mask].sum(axis=-1)).astype(np.float32)
    stat_names, mse_stats = percentile_stats(mse)
    _, l2_stats = percentile_stats(l2)

    agent_room_lr = (frame_fields["pos_agent"][..., 0] >= 112.0).astype(np.int8)
    target_room_lr = (frame_fields["pos_target"][..., 0] >= 112.0).astype(np.int8)
    same_room_lr = (agent_room_lr == target_room_lr) & valid_mask
    crosses_room_midline = agent_room_lr[:, 1:] != agent_room_lr[:, :-1]
    crosses_room_midline[~transition_mask] = False

    out_path = Path(args.out)
    np.savez_compressed(
        out_path,
        emb=emb,
        pred=pred,
        transition_target_emb=target,
        prediction_mse=mse,
        prediction_l2=l2,
        valid_mask=valid_mask,
        transition_mask=transition_mask,
        action=action_block_norm,
        action_raw_block=action_block_raw,
        action_block_mean=action_mean,
        action_block_std=action_std,
        action_stats_blocks=np.array(stats_blocks, dtype=np.int64),
        raw_frame_idx=raw_frame_idx,
        selected_ep_idx=chosen,
        selected_ep_len=ep_lens,
        selected_ep_offset=ep_offsets,
        agent_room_lr=agent_room_lr,
        target_room_lr=target_room_lr,
        same_room_lr=same_room_lr,
        crosses_room_midline=crosses_room_midline,
        frameskip=np.array(FRAMESKIP, dtype=np.int64),
        history_size=np.array(HISTORY_SIZE, dtype=np.int64),
        image_mean=IMAGENET_MEAN,
        image_std=IMAGENET_STD,
        stat_names=np.array(stat_names),
        mse_stats=mse_stats,
        l2_stats=l2_stats,
        **frame_fields,
    )
    print(f"saved={out_path.resolve()}", flush=True)
    print(f"emb_shape={emb.shape} pred_shape={pred.shape}", flush=True)
    print(f"valid_transitions={int(transition_mask.sum())}", flush=True)
    print("mse_stats", dict(zip(stat_names, mse_stats)), flush=True)
    print("l2_stats", dict(zip(stat_names, l2_stats)), flush=True)


if __name__ == "__main__":
    main()

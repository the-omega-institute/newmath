from __future__ import annotations

import argparse
import io
import json
import math
import shutil
import subprocess
import threading
import time
from pathlib import Path
from typing import Any

import h5py
import hdf5plugin  # noqa: F401
import numpy as np
import torch
import torch.nn.functional as F
from huggingface_hub import HfApi, HfFileSystem, hf_hub_download

from lewm_latent_probe import build_model, load_checkpoint


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT / "reports"
FRAMESKIP = 5
HISTORY_SIZE = 3
IMAGENET_MEAN = np.array([0.485, 0.456, 0.406], dtype=np.float32)
IMAGENET_STD = np.array([0.229, 0.224, 0.225], dtype=np.float32)
TARGETS = {
    "pusht": {
        "model_repo": "quentinll/lewm-pusht",
        "dataset_repo": "quentinll/lewm-pusht",
        "dataset_file": "pusht_expert_train.h5.zst",
        "format": "raw_h5_zst",
    },
    "reacher": {
        "model_repo": "quentinll/lewm-reacher",
        "dataset_repo": "quentinll/lewm-reacher",
        "dataset_file": "reacher.tar.zst",
        "format": "tar_zst_h5",
    },
    "cube": {
        "model_repo": "quentinll/lewm-cube",
        "dataset_repo": "quentinll/lewm-cube",
        "dataset_file": "cube_single_expert.tar.zst",
        "format": "tar_zst_h5",
    },
}


class PrefixFile(io.RawIOBase):
    def __init__(self, data: bytearray | bytes, logical_size: int):
        self.data = bytes(data)
        self.logical_size = int(logical_size)
        self.pos = 0

    def readable(self) -> bool:
        return True

    def seekable(self) -> bool:
        return True

    def readinto(self, out) -> int:
        if self.pos >= self.logical_size:
            return 0
        n = min(len(out), self.logical_size - self.pos)
        end = self.pos + n
        if self.pos < len(self.data):
            k = min(n, len(self.data) - self.pos)
            out[:k] = self.data[self.pos : self.pos + k]
            if k < n:
                out[k:n] = b"\0" * (n - k)
        else:
            out[:n] = b"\0" * n
        self.pos = end
        return n

    def seek(self, offset: int, whence: int = 0) -> int:
        if whence == 0:
            self.pos = int(offset)
        elif whence == 1:
            self.pos += int(offset)
        elif whence == 2:
            self.pos = self.logical_size + int(offset)
        else:
            raise ValueError(f"bad whence {whence}")
        return self.pos

    def tell(self) -> int:
        return self.pos


def write_fail(env: str, reason: str, detail: str, extra: dict[str, Any] | None = None) -> None:
    REPORT_DIR.mkdir(exist_ok=True)
    report = {
        "env": env,
        "status": "fail_closed",
        "reason": reason,
        "detail": detail,
        "sample_counts": {"episodes": 0, "valid_transitions": 0},
        "conclusion": {"claim": "data_unavailable"},
    }
    if extra:
        report.update(extra)
    path = REPORT_DIR / f"lewm_{env}_gap_ledger.json"
    path.write_text(json.dumps(report, indent=2), encoding="utf-8")
    md = REPORT_DIR / f"lewm_{env}_gap_ledger.md"
    md.write_text(
        f"# LeWM {env} Cross-Env Gap Ledger\n\n"
        f"- status: fail_closed\n"
        f"- reason: {reason}\n"
        f"- detail: {detail}\n",
        encoding="utf-8",
    )


def bsdtar_path() -> str | None:
    p = Path("tar")
    return str(p) if p.exists() else shutil.which("tar")


def tar_member_info(remote_path: str, timeout_s: int = 30) -> tuple[str, int]:
    tar = bsdtar_path()
    if tar is None:
        raise RuntimeError("no tar executable available")
    p = subprocess.Popen([tar, "-tvf", "-"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def feed() -> None:
        try:
            fs = HfFileSystem()
            with fs.open(remote_path, "rb") as src:
                for _ in range(128):
                    chunk = src.read(65536)
                    if not chunk:
                        break
                    try:
                        assert p.stdin is not None
                        p.stdin.write(chunk)
                        p.stdin.flush()
                    except BrokenPipeError:
                        break
        finally:
            try:
                assert p.stdin is not None
                p.stdin.close()
            except Exception:
                pass

    threading.Thread(target=feed, daemon=True).start()
    start = time.time()
    out = b""
    while time.time() - start < timeout_s:
        if p.stdout is None:
            break
        b = p.stdout.readline()
        if b:
            out += b
            break
        if p.poll() is not None:
            break
        time.sleep(0.1)
    if p.poll() is None:
        p.kill()
    line = out.decode("utf-8", "replace").strip()
    parts = line.split()
    if len(parts) < 6:
        raise RuntimeError(f"could not parse tar member listing: {line!r}")
    size = int(parts[4])
    name = parts[-1]
    return name, size


def read_tar_h5_prefix(remote_path: str, want_bytes: int, progress_label: str) -> bytearray:
    tar = bsdtar_path()
    if tar is None:
        raise RuntimeError("no tar executable available")
    p = subprocess.Popen([tar, "-xOf", "-"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    feed_error: list[str] = []

    def feed() -> None:
        try:
            fs = HfFileSystem()
            with fs.open(remote_path, "rb") as src:
                while True:
                    chunk = src.read(262144)
                    if not chunk:
                        break
                    try:
                        assert p.stdin is not None
                        p.stdin.write(chunk)
                        p.stdin.flush()
                    except BrokenPipeError:
                        break
        except Exception as exc:
            feed_error.append(repr(exc))
        finally:
            try:
                assert p.stdin is not None
                p.stdin.close()
            except Exception:
                pass

    threading.Thread(target=feed, daemon=True).start()
    buf = bytearray()
    last = 0
    t0 = time.time()
    while len(buf) < want_bytes:
        assert p.stdout is not None
        chunk = p.stdout.read(min(1024 * 1024, want_bytes - len(buf)))
        if not chunk:
            if p.poll() is not None:
                err = b""
                if p.stderr is not None:
                    err = p.stderr.read(4096)
                raise RuntimeError(
                    f"tar stream ended at {len(buf)} bytes before requested {want_bytes}; "
                    f"rc={p.returncode}; stderr={err.decode('utf-8', 'replace')}; feed_error={feed_error}"
                )
            time.sleep(0.1)
            continue
        buf.extend(chunk)
        mib = len(buf) // (64 * 1024 * 1024)
        if mib > last:
            last = mib
            print(
                f"{progress_label}: h5_prefix_mib={len(buf)/(1024*1024):.1f} "
                f"elapsed_s={time.time()-t0:.1f}",
                flush=True,
            )
    if p.poll() is None:
        p.kill()
    return buf


def to_model_pixels(frames: np.ndarray, image_size: int, device: torch.device) -> torch.Tensor:
    x = torch.from_numpy(frames).to(device=device, dtype=torch.float32)
    x = x.permute(0, 3, 1, 2).div_(255.0)
    mean = torch.tensor(IMAGENET_MEAN, device=device).view(1, 3, 1, 1)
    std = torch.tensor(IMAGENET_STD, device=device).view(1, 3, 1, 1)
    x = (x - mean) / std
    if x.shape[-2:] != (image_size, image_size):
        x = F.interpolate(x, size=(image_size, image_size), mode="bilinear", align_corners=False)
    return x


def action_blocks_for_episode(action: h5py.Dataset, offset: int, ep_len: int, frameskip: int) -> tuple[np.ndarray, np.ndarray]:
    frame_rel = np.arange(0, ep_len, frameskip, dtype=np.int64)
    raw_dim = int(action.shape[1])
    blocks = np.zeros((len(frame_rel), frameskip * raw_dim), dtype=np.float32)
    for i, rel in enumerate(frame_rel):
        raw = np.asarray(action[offset + rel : offset + min(rel + frameskip, ep_len)], dtype=np.float32)
        if len(raw) < frameskip:
            padded = np.zeros((frameskip, raw_dim), dtype=np.float32)
            padded[: len(raw)] = raw
            raw = padded
        blocks[i] = raw.reshape(-1)
    return frame_rel, blocks


def choose_episodes(ep_len: np.ndarray, episode_limit: int) -> tuple[np.ndarray, int]:
    chosen: list[int] = []
    transitions = 0
    for i, length in enumerate(ep_len):
        t = int((int(length) - 1) // FRAMESKIP)
        if t <= 0:
            continue
        chosen.append(i)
        transitions += t
        if len(chosen) >= episode_limit:
            break
    return np.asarray(chosen, dtype=np.int32), int(transitions)


def chunk_end(ds: h5py.Dataset, coord: tuple[int, ...]) -> int:
    info = ds.id.get_chunk_info_by_coord(coord)
    return int(info.byte_offset + info.size)


def required_h5_prefix_bytes(h5: h5py.File, chosen: np.ndarray) -> int:
    ep_len = h5["ep_len"][chosen]
    ep_offset = h5["ep_offset"][chosen]
    max_raw = 0
    for off, length in zip(ep_offset, ep_len):
        max_raw = max(max_raw, int(off) + int(length) - 1)
    max_bytes = 0
    for name in h5.keys():
        ds = h5[name]
        if not isinstance(ds, h5py.Dataset) or ds.chunks is None:
            continue
        row = min(max_raw, ds.shape[0] - 1) if ds.shape and ds.shape[0] > 1 else 0
        coord = (row,) + tuple(0 for _ in ds.shape[1:])
        try:
            max_bytes = max(max_bytes, chunk_end(ds, coord))
        except Exception:
            pass
    return int(max_bytes + 16 * 1024 * 1024)


def fit_action_stats(h5: h5py.File, episode_count: int, frameskip: int) -> tuple[np.ndarray, np.ndarray, int]:
    ep_len = h5["ep_len"][:episode_count]
    ep_offset = h5["ep_offset"][:episode_count]
    blocks = []
    for off, length in zip(ep_offset, ep_len):
        if int(length) <= frameskip:
            continue
        _, b = action_blocks_for_episode(h5["action"], int(off), int(length), frameskip)
        blocks.append(b[:-1])
    data = np.concatenate(blocks, axis=0)
    mean = data.mean(axis=0).astype(np.float32)
    std = data.std(axis=0, ddof=1).astype(np.float32)
    std[std < 1e-8] = 1.0
    return mean, std, int(data.shape[0])


def optional_frame_fields(h5: h5py.File, n_ep: int, max_t: int) -> dict[str, np.ndarray]:
    specs = {}
    for name in h5.keys():
        if name in {"pixels", "action", "ep_len", "ep_offset"}:
            continue
        ds = h5[name]
        if not isinstance(ds, h5py.Dataset) or not ds.shape or ds.shape[0] != h5["action"].shape[0]:
            continue
        shape = ds.shape[1:]
        dtype = ds.dtype
        fill: float | int | bool
        if dtype.kind == "b":
            fill = False
        elif dtype.kind in {"i", "u"}:
            fill = -1
        else:
            fill = np.nan
        specs[name] = np.full((n_ep, max_t) + shape, fill, dtype=dtype)
    return specs


def export_env(env: str, episode_limit: int, device_name: str) -> dict[str, Any]:
    cfg = TARGETS[env]
    out_path = ROOT / f"{env}_latent_large.npz"
    if out_path.exists():
        return {"status": "cached", "latent_path": str(out_path), "env": env}
    if cfg["format"] != "tar_zst_h5":
        write_fail(
            env,
            "missing_zstandard_raw_h5",
            "dataset is a raw .h5.zst stream; this Python lacks zstandard and bsdtar can only extract archive streams",
            {"asset": cfg},
        )
        return {"status": "fail_closed", "env": env, "reason": "missing_zstandard_raw_h5"}

    remote = f"datasets/{cfg['dataset_repo']}/{cfg['dataset_file']}"
    member_name, logical_size = tar_member_info(remote)
    print(f"{env}: tar member {member_name} logical_size={logical_size}", flush=True)

    small = read_tar_h5_prefix(remote, 32 * 1024 * 1024, env)
    with h5py.File(PrefixFile(small, logical_size), "r") as h5:
        ep_len_all = h5["ep_len"][: min(max(episode_limit, 1024), h5["ep_len"].shape[0])]
        chosen, total_transitions = choose_episodes(ep_len_all, episode_limit)
        if len(chosen) == 0:
            raise RuntimeError("no valid episodes found")
        required = required_h5_prefix_bytes(h5, chosen)
        fields = {name: {"shape": h5[name].shape, "dtype": str(h5[name].dtype)} for name in h5.keys()}
    print(f"{env}: episodes={len(chosen)} transitions={total_transitions} required_prefix_mib={required/(1024*1024):.1f}", flush=True)

    prefix = small if len(small) >= required else read_tar_h5_prefix(remote, required, env)

    checkpoint_path = hf_hub_download(cfg["model_repo"], "weights.pt", repo_type="model")
    config_path = hf_hub_download(cfg["model_repo"], "config.json", repo_type="model")
    model_cfg = json.loads(Path(config_path).read_text(encoding="utf-8"))
    image_size = int(model_cfg["encoder"]["image_size"])
    action_dim = int(model_cfg["action_encoder"]["input_dim"])
    latent_dim = int(model_cfg["predictor"]["input_dim"])

    device = torch.device(device_name)
    model = build_model(model_cfg)
    load_checkpoint(model, checkpoint_path)
    model.to(device).eval().requires_grad_(False)

    with h5py.File(PrefixFile(prefix, logical_size), "r") as h5:
        action_raw_dim = int(h5["action"].shape[1])
        if action_dim != FRAMESKIP * action_raw_dim:
            raise RuntimeError(f"action_dim mismatch: checkpoint={action_dim} dataset raw={action_raw_dim} frameskip={FRAMESKIP}")
        stats_eps = min(1024, int(h5["ep_len"].shape[0]))
        action_mean, action_std, stats_blocks = fit_action_stats(h5, stats_eps, FRAMESKIP)

        ep_lens = h5["ep_len"][chosen]
        ep_offsets = h5["ep_offset"][chosen]
        max_t = int(max((int(length) - 1) // FRAMESKIP + 1 for length in ep_lens))
        n_ep = len(chosen)
        emb = np.full((n_ep, max_t, latent_dim), np.nan, dtype=np.float32)
        action_block_raw = np.full((n_ep, max_t, action_dim), np.nan, dtype=np.float32)
        action_block_norm = np.full((n_ep, max_t, action_dim), np.nan, dtype=np.float32)
        raw_frame_idx = np.full((n_ep, max_t), -1, dtype=np.int64)
        valid_mask = np.zeros((n_ep, max_t), dtype=bool)
        frame_fields = optional_frame_fields(h5, n_ep, max_t)

        for out_i, (ep_i, offset, length) in enumerate(zip(chosen, ep_offsets, ep_lens)):
            frame_rel, blocks = action_blocks_for_episode(h5["action"], int(offset), int(length), FRAMESKIP)
            idx = int(offset) + frame_rel
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
            print(f"{env}: encoded {out_i + 1}/{n_ep} ep_idx={int(ep_i)} T={t}", flush=True)

    pred = np.full((n_ep, max_t - 1, latent_dim), np.nan, dtype=np.float32)
    transition_mask = valid_mask[:, 1:]
    windows_emb: list[np.ndarray] = []
    windows_act: list[np.ndarray] = []
    windows_meta: list[tuple[int, int, int]] = []
    for ep_i in range(n_ep):
        t_ep = int(valid_mask[ep_i].sum())
        for transition_t in range(max(0, t_ep - 1)):
            start = 0 if transition_t < HISTORY_SIZE else transition_t - HISTORY_SIZE + 1
            pos = transition_t - start
            windows_emb.append(emb[ep_i, start : start + HISTORY_SIZE])
            windows_act.append(action_block_norm[ep_i, start : start + HISTORY_SIZE])
            windows_meta.append((ep_i, transition_t, pos))
    with torch.inference_mode():
        for lo in range(0, len(windows_meta), 512):
            hi = min(lo + 512, len(windows_meta))
            be = torch.from_numpy(np.stack(windows_emb[lo:hi])).to(device=device, dtype=torch.float32)
            ba = torch.from_numpy(np.stack(windows_act[lo:hi])).to(device=device, dtype=torch.float32)
            bp = model.predict(be, model.action_encoder(ba)).detach().cpu().numpy()
            for row, (ep_i, transition_t, pos) in enumerate(windows_meta[lo:hi]):
                pred[ep_i, transition_t] = bp[row, pos]

    target = emb[:, 1:, :]
    sq = (pred - target) ** 2
    mse = np.full(pred.shape[:2], np.nan, dtype=np.float32)
    mse[transition_mask] = sq[transition_mask].mean(axis=-1).astype(np.float32)
    max_abs_identity = float(np.nanmax(np.abs(mse[transition_mask] - sq[transition_mask].mean(axis=-1))))
    if not (max_abs_identity < 1e-5):
        raise RuntimeError(f"prediction_mse identity failed: max_abs={max_abs_identity}")
    l2 = np.full(pred.shape[:2], np.nan, dtype=np.float32)
    l2[transition_mask] = np.sqrt(sq[transition_mask].sum(axis=-1)).astype(np.float32)

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
        action_stats_blocks=np.asarray(stats_blocks, dtype=np.int64),
        raw_frame_idx=raw_frame_idx,
        selected_ep_idx=chosen,
        selected_ep_len=ep_lens,
        selected_ep_offset=ep_offsets,
        frameskip=np.asarray(FRAMESKIP, dtype=np.int64),
        history_size=np.asarray(HISTORY_SIZE, dtype=np.int64),
        image_mean=IMAGENET_MEAN,
        image_std=IMAGENET_STD,
        env=np.asarray(env),
        model_repo=np.asarray(cfg["model_repo"]),
        dataset_repo=np.asarray(cfg["dataset_repo"]),
        dataset_file=np.asarray(cfg["dataset_file"]),
        tar_member=np.asarray(member_name),
        h5_logical_size=np.asarray(logical_size, dtype=np.int64),
        h5_required_prefix_bytes=np.asarray(required, dtype=np.int64),
        prediction_mse_identity_max_abs=np.asarray(max_abs_identity, dtype=np.float64),
        h5_fields_json=np.asarray(json.dumps(fields)),
        **frame_fields,
    )
    return {
        "status": "exported",
        "env": env,
        "latent_path": str(out_path),
        "episodes": int(n_ep),
        "valid_transitions": int(transition_mask.sum()),
        "prediction_mse_identity_max_abs": max_abs_identity,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--env", choices=sorted(TARGETS), required=True)
    parser.add_argument("--episodes", type=int, default=150)
    parser.add_argument("--device", default="cuda" if torch.cuda.is_available() else "cpu")
    args = parser.parse_args()

    REPORT_DIR.mkdir(exist_ok=True)
    try:
        result = export_env(args.env, args.episodes, args.device)
        print(json.dumps(result, indent=2))
    except Exception as exc:
        write_fail(args.env, "latent_export_failed", repr(exc), {"exception_type": type(exc).__name__})
        raise


if __name__ == "__main__":
    main()

from __future__ import annotations

import argparse
import io
import json
from pathlib import Path
from typing import Any

import h5py
import numpy as np
import torch

from _crossenv_export_latents import (
    FRAMESKIP,
    HISTORY_SIZE,
    IMAGENET_MEAN,
    IMAGENET_STD,
    PrefixFile,
    TARGETS,
    action_blocks_for_episode,
    fit_action_stats,
    optional_frame_fields,
    read_tar_h5_prefix,
    required_h5_prefix_bytes,
    tar_member_info,
    to_model_pixels,
    write_fail,
)
from lewm_latent_probe import build_model, load_checkpoint
from huggingface_hub import hf_hub_download


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT / "reports"
CACHE_ROOT = REPORT_DIR / "crossenv_latent_cache"
CHUNK_EPISODES = 10
MAX_PREFIX_BYTES = 96 * 1024 * 1024 * 1024


class DiskPrefixFile(io.RawIOBase):
    def __init__(self, path: Path, logical_size: int):
        self.path = path
        self.file = path.open("rb")
        self.file_size = path.stat().st_size
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
        if self.pos < self.file_size:
            self.file.seek(self.pos)
            chunk = self.file.read(min(n, self.file_size - self.pos))
            k = len(chunk)
            out[:k] = chunk
            if k < n:
                out[k:n] = b"\0" * (n - k)
        else:
            out[:n] = b"\0" * n
        self.pos += n
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

    def close(self) -> None:
        self.file.close()
        super().close()


def _json_array(v: np.ndarray) -> list[int]:
    return [int(x) for x in np.asarray(v).reshape(-1)]


def _is_complete_episode(path: Path, latent_dim: int, action_dim: int) -> bool:
    try:
        with np.load(path, allow_pickle=False) as d:
            if "emb" not in d or "action" not in d or "valid_mask" not in d:
                return False
            emb = d["emb"]
            action = d["action"]
            valid = d["valid_mask"]
            return emb.ndim == 2 and emb.shape[1] == latent_dim and action.shape == (emb.shape[0], action_dim) and valid.shape == (emb.shape[0],)
    except Exception:
        return False


def _save_episode(
    path: Path,
    *,
    ep_i: int,
    selected_ep_idx: int,
    offset: int,
    length: int,
    emb: np.ndarray,
    action_raw: np.ndarray,
    action_norm: np.ndarray,
    raw_frame_idx: np.ndarray,
    frame_fields: dict[str, np.ndarray],
) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    np.savez_compressed(
        tmp,
        ep_i=np.asarray(ep_i, dtype=np.int64),
        selected_ep_idx=np.asarray(selected_ep_idx, dtype=np.int64),
        selected_ep_offset=np.asarray(offset, dtype=np.int64),
        selected_ep_len=np.asarray(length, dtype=np.int64),
        emb=emb.astype(np.float32),
        action_raw_block=action_raw.astype(np.float32),
        action=action_norm.astype(np.float32),
        raw_frame_idx=raw_frame_idx.astype(np.int64),
        valid_mask=np.ones(emb.shape[0], dtype=bool),
        **frame_fields,
    )
    if tmp.exists():
        tmp.replace(path)
    else:
        alt = Path(str(tmp) + ".npz")
        alt.replace(path)


def _cache_manifest_path(env: str) -> Path:
    return CACHE_ROOT / env / "manifest.json"


def _write_manifest(env: str, manifest: dict[str, Any]) -> None:
    cache_dir = CACHE_ROOT / env
    cache_dir.mkdir(parents=True, exist_ok=True)
    _cache_manifest_path(env).write_text(json.dumps(manifest, indent=2), encoding="utf-8")


def open_prefix(prefix: bytearray | bytes | Path, logical_size: int):
    if isinstance(prefix, Path):
        return DiskPrefixFile(prefix, logical_size)
    return PrefixFile(prefix, logical_size)


def _download_tar_h5_prefix_to_disk(remote_path: str, target_path: Path, want_bytes: int, progress_label: str) -> Path:
    target_path.parent.mkdir(parents=True, exist_ok=True)
    if target_path.exists() and target_path.stat().st_size >= want_bytes:
        return target_path
    tmp = target_path.with_suffix(target_path.suffix + ".tmp")
    import subprocess
    import threading
    import time
    from _crossenv_export_latents import bsdtar_path
    from huggingface_hub import HfFileSystem

    tar = bsdtar_path()
    if tar is None:
        raise RuntimeError("no tar executable available")
    start_at = tmp.stat().st_size if tmp.exists() else 0
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
    got = start_at
    last = got // (64 * 1024 * 1024)
    t0 = time.time()
    with tmp.open("ab") as out:
        skipped = 0
        while skipped < start_at:
            assert p.stdout is not None
            chunk = p.stdout.read(min(4 * 1024 * 1024, start_at - skipped))
            if not chunk:
                if p.poll() is not None:
                    err = b""
                    if p.stderr is not None:
                        err = p.stderr.read(4096)
                    raise RuntimeError(
                        f"tar stream ended while skipping cached prefix at {skipped} of {start_at}; "
                        f"rc={p.returncode}; stderr={err.decode('utf-8', 'replace')}; feed_error={feed_error}"
                    )
                time.sleep(0.1)
                continue
            skipped += len(chunk)
            mib = skipped // (1024 * 1024 * 1024)
            if mib and skipped % (1024 * 1024 * 1024) < len(chunk):
                print(
                    f"{progress_label}: skipped_cached_prefix_gib={skipped/(1024*1024*1024):.1f} "
                    f"of {start_at/(1024*1024*1024):.1f}",
                    flush=True,
                )
        while got < want_bytes:
            assert p.stdout is not None
            chunk = p.stdout.read(min(1024 * 1024, want_bytes - got))
            if not chunk:
                if p.poll() is not None:
                    err = b""
                    if p.stderr is not None:
                        err = p.stderr.read(4096)
                    raise RuntimeError(
                        f"tar stream ended at {got} bytes before requested {want_bytes}; "
                        f"rc={p.returncode}; stderr={err.decode('utf-8', 'replace')}; feed_error={feed_error}"
                    )
                time.sleep(0.1)
                continue
            out.write(chunk)
            got += len(chunk)
            mib = got // (64 * 1024 * 1024)
            if mib > last:
                last = mib
                print(
                    f"{progress_label}: disk_h5_prefix_mib={got/(1024*1024):.1f} "
                    f"elapsed_s={time.time()-t0:.1f}",
                    flush=True,
                )
    if p.poll() is None:
        p.kill()
    tmp.replace(target_path)
    return target_path


def _extract_local_tar_h5_prefix_to_disk(archive_path: Path, target_path: Path, want_bytes: int, progress_label: str) -> Path:
    target_path.parent.mkdir(parents=True, exist_ok=True)
    if target_path.exists() and target_path.stat().st_size >= want_bytes:
        return target_path
    tmp = target_path.with_suffix(target_path.suffix + ".tmp")
    tmp.unlink(missing_ok=True)
    import subprocess
    import time
    from _crossenv_export_latents import bsdtar_path

    tar = bsdtar_path()
    if tar is None:
        raise RuntimeError("no tar executable available")
    p = subprocess.Popen([tar, "-xOf", str(archive_path)], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    got = 0
    last = 0
    t0 = time.time()
    with tmp.open("wb") as out:
        while got < want_bytes:
            assert p.stdout is not None
            chunk = p.stdout.read(min(4 * 1024 * 1024, want_bytes - got))
            if not chunk:
                if p.poll() is not None:
                    err = b""
                    if p.stderr is not None:
                        err = p.stderr.read(4096)
                    raise RuntimeError(
                        f"local tar stream ended at {got} bytes before requested {want_bytes}; "
                        f"rc={p.returncode}; stderr={err.decode('utf-8', 'replace')}"
                    )
                time.sleep(0.1)
                continue
            out.write(chunk)
            got += len(chunk)
            mib = got // (64 * 1024 * 1024)
            if mib > last:
                last = mib
                print(
                    f"{progress_label}: local_h5_prefix_mib={got/(1024*1024):.1f} "
                    f"elapsed_s={time.time()-t0:.1f}",
                    flush=True,
                )
    if p.poll() is None:
        p.kill()
    tmp.replace(target_path)
    return target_path


def _raw_zst_logical_size(remote_path: str) -> int:
    try:
        import zstandard as zstd
        from huggingface_hub import HfFileSystem
    except Exception as exc:
        raise RuntimeError(f"zstandard raw h5 support unavailable: {exc!r}") from exc

    fs = HfFileSystem()
    with fs.open(remote_path, "rb") as src:
        head = src.read(256 * 1024)
    logical_size = int(zstd.frame_content_size(head))
    unknown = int(getattr(zstd, "CONTENTSIZE_UNKNOWN", 2**64 - 1))
    error = int(getattr(zstd, "CONTENTSIZE_ERROR", 2**64 - 2))
    if logical_size in {unknown, error} or logical_size <= 0:
        raise RuntimeError(f"raw zstd frame did not expose HDF5 content size: {logical_size}")
    return logical_size


def _download_raw_h5_zst_prefix_to_disk(remote_path: str, target_path: Path, want_bytes: int, progress_label: str) -> Path:
    target_path.parent.mkdir(parents=True, exist_ok=True)
    if target_path.exists() and target_path.stat().st_size >= want_bytes:
        return target_path

    try:
        import zstandard as zstd
        from huggingface_hub import HfFileSystem
    except Exception as exc:
        raise RuntimeError(f"zstandard raw h5 support unavailable: {exc!r}") from exc

    import time

    start_at = target_path.stat().st_size if target_path.exists() else 0
    got = start_at
    last = got // (64 * 1024 * 1024)
    t0 = time.time()
    skipped = 0
    fs = HfFileSystem()
    with fs.open(remote_path, "rb") as src:
        with zstd.ZstdDecompressor().stream_reader(src) as reader:
            while skipped < start_at:
                chunk = reader.read(min(4 * 1024 * 1024, start_at - skipped))
                if not chunk:
                    raise RuntimeError(f"raw zstd stream ended while skipping cached prefix at {skipped} of {start_at}")
                skipped += len(chunk)
                gib = skipped // (1024 * 1024 * 1024)
                if gib and skipped % (1024 * 1024 * 1024) < len(chunk):
                    print(
                        f"{progress_label}: skipped_cached_raw_prefix_gib={skipped/(1024*1024*1024):.1f} "
                        f"of {start_at/(1024*1024*1024):.1f}",
                        flush=True,
                    )

            with target_path.open("ab") as out:
                while got < want_bytes:
                    chunk = reader.read(min(4 * 1024 * 1024, want_bytes - got))
                    if not chunk:
                        raise RuntimeError(f"raw zstd stream ended at {got} bytes before requested {want_bytes}")
                    out.write(chunk)
                    got += len(chunk)
                    mib = got // (64 * 1024 * 1024)
                    if mib > last:
                        last = mib
                        print(
                            f"{progress_label}: raw_h5_prefix_mib={got/(1024*1024):.1f} "
                            f"elapsed_s={time.time()-t0:.1f}",
                            flush=True,
                        )
    return target_path


def episode_required_prefix_bytes(h5: h5py.File, ep_idx: int) -> int:
    return required_h5_prefix_bytes(h5, np.asarray([ep_idx], dtype=np.int32))


def choose_low_prefix_episodes(h5: h5py.File, episode_limit: int) -> tuple[np.ndarray, int, int]:
    n_probe = min(max(episode_limit * 8, 1024), int(h5["ep_len"].shape[0]))
    candidates: list[tuple[int, int, int]] = []
    ep_len = h5["ep_len"][:n_probe]
    for i, length in enumerate(ep_len):
        transitions = int((int(length) - 1) // FRAMESKIP)
        if transitions <= 0:
            continue
        try:
            req = episode_required_prefix_bytes(h5, i)
        except Exception:
            continue
        candidates.append((req, i, transitions))
    if not candidates:
        raise RuntimeError("no valid episodes found")
    candidates.sort(key=lambda x: (x[0], x[1]))
    chosen: list[int] = []
    transitions = 0
    required = 0
    for req, i, t in candidates:
        if req > MAX_PREFIX_BYTES and len(chosen) == 0:
            continue
        if len(chosen) >= episode_limit:
            break
        chosen.append(i)
        transitions += t
        required = max(required, req)
    chosen_arr = np.asarray(sorted(chosen), dtype=np.int32)
    required = required_h5_prefix_bytes(h5, chosen_arr)
    transitions = int(sum(int((int(h5["ep_len"][i]) - 1) // FRAMESKIP) for i in chosen_arr))
    return chosen_arr, transitions, required


def _prepare(env: str, episode_limit: int) -> dict[str, Any]:
    cfg = TARGETS[env]
    if cfg["format"] == "raw_h5_zst":
        remote = f"datasets/{cfg['dataset_repo']}/{cfg['dataset_file']}"
        member_name = f"raw_h5_zst:{cfg['dataset_file']}"
        try:
            logical_size = _raw_zst_logical_size(remote)
        except Exception as exc:
            write_fail(
                env,
                "missing_zstandard_raw_h5",
                f"dataset is a raw .h5.zst stream but raw zstd setup failed: {exc!r}",
                {"asset": cfg, "exception_type": type(exc).__name__},
            )
            return {"status": "fail_closed", "env": env, "reason": "missing_zstandard_raw_h5"}
        print(f"{env}: raw h5.zst logical_size={logical_size}", flush=True)

        prefix_path = _download_raw_h5_zst_prefix_to_disk(
            remote,
            CACHE_ROOT / env / "h5_prefix.bin",
            32 * 1024 * 1024,
            env,
        )
        with h5py.File(open_prefix(prefix_path, logical_size), "r") as h5:
            chosen, total_transitions, required = choose_low_prefix_episodes(h5, episode_limit)
            fields = {name: {"shape": h5[name].shape, "dtype": str(h5[name].dtype)} for name in h5.keys()}
        print(
            f"{env}: episodes={len(chosen)} transitions={total_transitions} "
            f"required_prefix_mib={required/(1024*1024):.1f}",
            flush=True,
        )

        if required > MAX_PREFIX_BYTES:
            write_fail(
                env,
                "data_unavailable",
                f"required HDF5 prefix for selected episodes is {required} bytes, above cap {MAX_PREFIX_BYTES}",
                {"asset": cfg, "episodes_selected": int(len(chosen)), "required_prefix_bytes": int(required)},
            )
            return {"status": "fail_closed", "env": env, "reason": "data_unavailable"}
        prefix = _download_raw_h5_zst_prefix_to_disk(remote, prefix_path, required, env)
        return {
            "status": "prepared",
            "cfg": cfg,
            "remote": remote,
            "member_name": member_name,
            "logical_size": logical_size,
            "prefix": prefix,
            "chosen": chosen,
            "total_transitions": total_transitions,
            "required": required,
            "fields": fields,
        }

    if cfg["format"] != "tar_zst_h5":
        write_fail(
            env,
            "unsupported_dataset_format",
            f"unsupported dataset format {cfg['format']!r}",
            {"asset": cfg},
        )
        return {"status": "fail_closed", "env": env, "reason": "unsupported_dataset_format"}

    remote = f"datasets/{cfg['dataset_repo']}/{cfg['dataset_file']}"
    member_name, logical_size = tar_member_info(remote)
    print(f"{env}: tar member {member_name} logical_size={logical_size}", flush=True)

    small = read_tar_h5_prefix(remote, 32 * 1024 * 1024, env)
    with h5py.File(PrefixFile(small, logical_size), "r") as h5:
        chosen, total_transitions, required = choose_low_prefix_episodes(h5, episode_limit)
        fields = {name: {"shape": h5[name].shape, "dtype": str(h5[name].dtype)} for name in h5.keys()}
    print(f"{env}: episodes={len(chosen)} transitions={total_transitions} required_prefix_mib={required/(1024*1024):.1f}", flush=True)

    if required <= len(small):
        prefix: bytearray | bytes | Path = small
    elif required <= MAX_PREFIX_BYTES:
        archive_path = Path(
            hf_hub_download(
                repo_id=cfg["dataset_repo"],
                filename=cfg["dataset_file"],
                repo_type="dataset",
            )
        )
        prefix = _extract_local_tar_h5_prefix_to_disk(archive_path, CACHE_ROOT / env / "h5_prefix.bin", required, env)
    else:
        write_fail(
            env,
            "data_unavailable",
            f"required HDF5 prefix for selected episodes is {required} bytes, above cap {MAX_PREFIX_BYTES}",
            {"asset": cfg, "episodes_selected": int(len(chosen)), "required_prefix_bytes": int(required)},
        )
        return {"status": "fail_closed", "env": env, "reason": "data_unavailable"}
    return {
        "status": "prepared",
        "cfg": cfg,
        "remote": remote,
        "member_name": member_name,
        "logical_size": logical_size,
        "prefix": prefix,
        "chosen": chosen,
        "total_transitions": total_transitions,
        "required": required,
        "fields": fields,
    }


def export_env_resumable(env: str, episode_limit: int, device_name: str, force_rebuild_final: bool = False) -> dict[str, Any]:
    out_path = ROOT / f"{env}_latent_large.npz"
    if out_path.exists() and not force_rebuild_final:
        try:
            with np.load(out_path, allow_pickle=False) as d:
                required = {"emb", "pred", "prediction_mse", "transition_mask", "action", "valid_mask"}
                if required.issubset(set(d.files)):
                    sq = (d["pred"] - d["emb"][:, 1:, :]) ** 2
                    tm = d["transition_mask"].astype(bool)
                    max_abs = float(np.nanmax(np.abs(d["prediction_mse"][tm] - sq[tm].mean(axis=-1)))) if np.any(tm) else 0.0
                    if max_abs < 1e-5:
                        return {"status": "cached", "latent_path": str(out_path), "env": env, "prediction_mse_identity_max_abs": max_abs}
        except Exception:
            out_path.unlink(missing_ok=True)

    prepared = _prepare(env, episode_limit)
    if prepared.get("status") != "prepared":
        return prepared

    cfg = prepared["cfg"]
    cache_dir = CACHE_ROOT / env
    cache_dir.mkdir(parents=True, exist_ok=True)

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

    chosen = prepared["chosen"]
    prefix = prepared["prefix"]
    logical_size = int(prepared["logical_size"])

    with h5py.File(open_prefix(prefix, logical_size), "r") as h5:
        action_raw_dim = int(h5["action"].shape[1])
        if action_dim != FRAMESKIP * action_raw_dim:
            raise RuntimeError(f"action_dim mismatch: checkpoint={action_dim} dataset raw={action_raw_dim} frameskip={FRAMESKIP}")
        stats_eps = min(1024, int(h5["ep_len"].shape[0]))
        action_mean, action_std, stats_blocks = fit_action_stats(h5, stats_eps, FRAMESKIP)
        ep_lens = h5["ep_len"][chosen]
        ep_offsets = h5["ep_offset"][chosen]

        manifest = {
            "env": env,
            "episodes": int(len(chosen)),
            "selected_ep_idx": _json_array(chosen),
            "selected_ep_len": _json_array(ep_lens),
            "selected_ep_offset": _json_array(ep_offsets),
            "latent_dim": latent_dim,
            "action_dim": action_dim,
            "image_size": image_size,
            "frameskip": FRAMESKIP,
            "history_size": HISTORY_SIZE,
            "model_repo": cfg["model_repo"],
            "dataset_repo": cfg["dataset_repo"],
            "dataset_file": cfg["dataset_file"],
            "tar_member": prepared["member_name"],
            "h5_logical_size": logical_size,
            "h5_required_prefix_bytes": int(prepared["required"]),
            "h5_fields": prepared["fields"],
            "action_stats_blocks": int(stats_blocks),
        }
        _write_manifest(env, manifest)

        for out_i, (ep_i, offset, length) in enumerate(zip(chosen, ep_offsets, ep_lens)):
            ep_path = cache_dir / f"episode_{out_i:04d}.npz"
            if _is_complete_episode(ep_path, latent_dim, action_dim):
                print(f"{env}: cached episode {out_i + 1}/{len(chosen)} ep_idx={int(ep_i)}", flush=True)
                continue
            ep_path.unlink(missing_ok=True)

            frame_rel, blocks = action_blocks_for_episode(h5["action"], int(offset), int(length), FRAMESKIP)
            idx = int(offset) + frame_rel
            frames = h5["pixels"][idx]
            pixels = to_model_pixels(frames, image_size=image_size, device=device)
            with torch.inference_mode():
                ep_emb = model.encode({"pixels": pixels.unsqueeze(0)})["emb"][0].detach().cpu().numpy()
            frame_fields = {}
            for name, ds in h5.items():
                if name in {"pixels", "action", "ep_len", "ep_offset"}:
                    continue
                if isinstance(ds, h5py.Dataset) and ds.shape and ds.shape[0] == h5["action"].shape[0]:
                    if ds.dtype.kind == "O":
                        continue
                    frame_fields[name] = ds[idx]
            _save_episode(
                ep_path,
                ep_i=out_i,
                selected_ep_idx=int(ep_i),
                offset=int(offset),
                length=int(length),
                emb=ep_emb,
                action_raw=blocks,
                action_norm=(blocks - action_mean) / action_std,
                raw_frame_idx=idx,
                frame_fields=frame_fields,
            )
            if (out_i + 1) % CHUNK_EPISODES == 0 or out_i + 1 == len(chosen):
                print(f"{env}: checkpointed {out_i + 1}/{len(chosen)} episodes", flush=True)

    return assemble_final(env, action_mean, action_std, prepared, latent_dim, action_dim, stats_blocks)


def assemble_final(
    env: str,
    action_mean: np.ndarray | None = None,
    action_std: np.ndarray | None = None,
    prepared: dict[str, Any] | None = None,
    latent_dim: int | None = None,
    action_dim: int | None = None,
    stats_blocks: int | None = None,
) -> dict[str, Any]:
    manifest_path = _cache_manifest_path(env)
    if not manifest_path.exists():
        raise RuntimeError(f"missing cache manifest for {env}")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    cache_dir = manifest_path.parent
    n_ep = int(manifest["episodes"])
    latent_dim = int(latent_dim or manifest["latent_dim"])
    action_dim = int(action_dim or manifest["action_dim"])

    episodes = []
    for i in range(n_ep):
        path = cache_dir / f"episode_{i:04d}.npz"
        if not _is_complete_episode(path, latent_dim, action_dim):
            raise RuntimeError(f"missing or incomplete episode cache: {path}")
        try:
            episodes.append(dict(np.load(path, allow_pickle=False)))
        except ValueError:
            raw = dict(np.load(path, allow_pickle=True))
            episodes.append({k: v for k, v in raw.items() if getattr(v, "dtype", None) is None or v.dtype.kind != "O"})

    max_t = max(int(ep["emb"].shape[0]) for ep in episodes)
    emb = np.full((n_ep, max_t, latent_dim), np.nan, dtype=np.float32)
    action = np.full((n_ep, max_t, action_dim), np.nan, dtype=np.float32)
    action_raw = np.full((n_ep, max_t, action_dim), np.nan, dtype=np.float32)
    raw_frame_idx = np.full((n_ep, max_t), -1, dtype=np.int64)
    valid_mask = np.zeros((n_ep, max_t), dtype=bool)

    optional_names = sorted(set().union(*(set(ep.keys()) for ep in episodes)) - {
        "ep_i",
        "selected_ep_idx",
        "selected_ep_offset",
        "selected_ep_len",
        "emb",
        "action",
        "action_raw_block",
        "raw_frame_idx",
        "valid_mask",
    })
    frame_fields: dict[str, np.ndarray] = {}
    for name in optional_names:
        sample = next((ep[name] for ep in episodes if name in ep), None)
        if sample is None:
            continue
        dtype = sample.dtype
        fill: float | int | bool
        if dtype.kind == "b":
            fill = False
        elif dtype.kind in {"i", "u"}:
            fill = -1
        else:
            fill = np.nan
        frame_fields[name] = np.full((n_ep, max_t) + sample.shape[1:], fill, dtype=dtype)

    for i, ep in enumerate(episodes):
        t = int(ep["emb"].shape[0])
        emb[i, :t] = ep["emb"]
        action[i, :t] = ep["action"]
        action_raw[i, :t] = ep["action_raw_block"]
        raw_frame_idx[i, :t] = ep["raw_frame_idx"]
        valid_mask[i, :t] = True
        for name in frame_fields:
            if name in ep:
                frame_fields[name][i, :t] = ep[name]

    cfg = TARGETS[env]
    checkpoint_path = hf_hub_download(cfg["model_repo"], "weights.pt", repo_type="model")
    config_path = hf_hub_download(cfg["model_repo"], "config.json", repo_type="model")
    model_cfg = json.loads(Path(config_path).read_text(encoding="utf-8"))
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    model = build_model(model_cfg)
    load_checkpoint(model, checkpoint_path)
    model.to(device).eval().requires_grad_(False)

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
            we = emb[ep_i, start : start + HISTORY_SIZE]
            wa = action[ep_i, start : start + HISTORY_SIZE]
            if we.shape[0] < HISTORY_SIZE:
                pe = np.zeros((HISTORY_SIZE, latent_dim), dtype=np.float32)
                pa = np.zeros((HISTORY_SIZE, action_dim), dtype=np.float32)
                pe[: we.shape[0]] = we
                pa[: wa.shape[0]] = wa
                we = pe
                wa = pa
            windows_emb.append(we)
            windows_act.append(wa)
            windows_meta.append((ep_i, transition_t, pos))

    with torch.inference_mode():
        for lo in range(0, len(windows_meta), 512):
            hi = min(lo + 512, len(windows_meta))
            be = torch.from_numpy(np.stack(windows_emb[lo:hi])).to(device=device, dtype=torch.float32)
            ba = torch.from_numpy(np.stack(windows_act[lo:hi])).to(device=device, dtype=torch.float32)
            bp = model.predict(be, model.action_encoder(ba)).detach().cpu().numpy()
            for row, (ep_i, transition_t, pos) in enumerate(windows_meta[lo:hi]):
                pred[ep_i, transition_t] = bp[row, pos]
            print(f"{env}: predicted transitions {hi}/{len(windows_meta)}", flush=True)

    target = emb[:, 1:, :]
    sq = (pred - target) ** 2
    mse = np.full(pred.shape[:2], np.nan, dtype=np.float32)
    mse[transition_mask] = sq[transition_mask].mean(axis=-1).astype(np.float32)
    max_abs_identity = float(np.nanmax(np.abs(mse[transition_mask] - sq[transition_mask].mean(axis=-1)))) if np.any(transition_mask) else 0.0
    if not (max_abs_identity < 1e-5):
        raise RuntimeError(f"prediction_mse identity failed: max_abs={max_abs_identity}")
    l2 = np.full(pred.shape[:2], np.nan, dtype=np.float32)
    l2[transition_mask] = np.sqrt(sq[transition_mask].sum(axis=-1)).astype(np.float32)

    if action_mean is None or action_std is None or stats_blocks is None:
        action_mean = np.full(action_dim, np.nan, dtype=np.float32)
        action_std = np.full(action_dim, np.nan, dtype=np.float32)
        stats_blocks = int(manifest.get("action_stats_blocks", -1))

    selected_ep_idx = np.asarray(manifest["selected_ep_idx"], dtype=np.int32)
    selected_ep_len = np.asarray(manifest["selected_ep_len"], dtype=np.int64)
    selected_ep_offset = np.asarray(manifest["selected_ep_offset"], dtype=np.int64)
    out_path = ROOT / f"{env}_latent_large.npz"
    tmp = out_path.with_suffix(out_path.suffix + ".tmp")
    np.savez_compressed(
        tmp,
        emb=emb,
        pred=pred,
        transition_target_emb=target,
        prediction_mse=mse,
        prediction_l2=l2,
        valid_mask=valid_mask,
        transition_mask=transition_mask,
        action=action,
        action_raw_block=action_raw,
        action_block_mean=action_mean,
        action_block_std=action_std,
        action_stats_blocks=np.asarray(stats_blocks, dtype=np.int64),
        raw_frame_idx=raw_frame_idx,
        selected_ep_idx=selected_ep_idx,
        selected_ep_len=selected_ep_len,
        selected_ep_offset=selected_ep_offset,
        frameskip=np.asarray(FRAMESKIP, dtype=np.int64),
        history_size=np.asarray(HISTORY_SIZE, dtype=np.int64),
        image_mean=IMAGENET_MEAN,
        image_std=IMAGENET_STD,
        env=np.asarray(env),
        model_repo=np.asarray(manifest["model_repo"]),
        dataset_repo=np.asarray(manifest["dataset_repo"]),
        dataset_file=np.asarray(manifest["dataset_file"]),
        tar_member=np.asarray(manifest["tar_member"]),
        h5_logical_size=np.asarray(manifest["h5_logical_size"], dtype=np.int64),
        h5_required_prefix_bytes=np.asarray(manifest["h5_required_prefix_bytes"], dtype=np.int64),
        prediction_mse_identity_max_abs=np.asarray(max_abs_identity, dtype=np.float64),
        h5_fields_json=np.asarray(json.dumps(manifest["h5_fields"])),
        **frame_fields,
    )
    if tmp.exists():
        tmp.replace(out_path)
    else:
        Path(str(tmp) + ".npz").replace(out_path)
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
    parser.add_argument("--force-rebuild-final", action="store_true")
    args = parser.parse_args()

    REPORT_DIR.mkdir(exist_ok=True)
    try:
        result = export_env_resumable(args.env, args.episodes, args.device, args.force_rebuild_final)
        print(json.dumps(result, indent=2))
    except Exception as exc:
        write_fail(args.env, "latent_export_failed", repr(exc), {"exception_type": type(exc).__name__})
        raise


if __name__ == "__main__":
    main()

"""Reader-capacity frontier for clean retention vs OOD awareness.

Protocol frozen by the prompt:
- input is flattened WINDOW=6 windows of (emb, action), 6 * (192 + 10) = 1212
- failure truth is LeWM prediction_mse > clean train p75
- split/seed matches the LAT port: SPLIT_SEED=1701, torch/np seed=20260611
- readers are pure discriminators trained with AdamW/BCE for 30 epochs
- arms are clean_trained and ood_aware (clean train + all perturbed train slices)
"""

from __future__ import annotations

import json
import math
import time
from pathlib import Path
from typing import Any

import h5py
import hdf5plugin  # noqa: F401 - registers blosc HDF5 filter
import numpy as np
import torch
import torch.nn as nn
from huggingface_hub import hf_hub_download

from lewm_latent_probe import build_model, load_checkpoint
from _phase1c_gap_ledger import flatten_transition_rows
from _phase2a_brittleness_gap import H5_PATH, MODEL_REPO, perturbation_grid, predict_eval_rows
from _phase2c_ood_aware_gap import encode_split_episodes_batched
from _lat_lewm_ood import EMB_CACHE, build_perturbed_windows, load_emb_cache, save_emb_cache, strength_token
from _lat_lewm_ood_aware import mse_cache_path, split_emb_cache_path
from _lat_lewm_port import (
    BATCH,
    BOOTSTRAP_SEED,
    BOOTSTRAPS,
    EPOCHS,
    LR,
    NPZ_PATH,
    PYTHON_SEED,
    REPORT_DIR,
    SPLIT_SEED,
    WINDOW,
    LedgerAwareTransformer,
    auroc_rank,
    build_windows,
    split_episodes,
)

JSON_PATH = REPORT_DIR / "lewm_reader_capacity_frontier.json"
MD_PATH = REPORT_DIR / "lewm_reader_capacity_frontier.md"
PORT_JSON = REPORT_DIR / "lewm_ledger_aware_transformer.json"

READERS = ("linear", "mlp1", "mlp2", "tfm")
ARMS = ("clean_trained", "ood_aware")


def clean_json(v: Any) -> Any:
    if isinstance(v, dict):
        return {str(k): clean_json(val) for k, val in v.items()}
    if isinstance(v, (list, tuple)):
        return [clean_json(val) for val in v]
    if isinstance(v, np.ndarray):
        return clean_json(v.tolist())
    if isinstance(v, (np.integer,)):
        return int(v)
    if isinstance(v, (np.floating,)):
        v = float(v)
    if isinstance(v, float) and not math.isfinite(v):
        return None
    return v


def fmt_ci(m: dict[str, float]) -> str:
    return f"{m['observed']:.3f} [{m['ci95_low']:.3f}, {m['ci95_high']:.3f}]"


def flatten_windows(win_emb: np.ndarray, win_act: np.ndarray) -> np.ndarray:
    x = np.concatenate([win_emb, win_act], axis=-1)
    return x.reshape(x.shape[0], -1).astype(np.float32)


def bootstrap_auroc_by_episode(
    y: np.ndarray,
    score: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
    n_boot: int,
) -> dict[str, float]:
    observed = auroc_rank(y, score)
    rng = np.random.default_rng(seed)
    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    vals: list[float] = []
    for _ in range(n_boot):
        sampled = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[i] for i in sampled])
        vals.append(auroc_rank(y[idx], score[idx]))
    arr = np.asarray(vals, dtype=np.float64)
    return {
        "observed": float(observed),
        "bootstrap_mean": float(np.nanmean(arr)),
        "ci95_low": float(np.nanpercentile(arr, 2.5)),
        "ci95_high": float(np.nanpercentile(arr, 97.5)),
    }


def eval_metrics(y: np.ndarray, score: np.ndarray, episode: np.ndarray, *, seed: int) -> dict[str, Any]:
    return {
        "failure_detection_auroc": bootstrap_auroc_by_episode(
            y.astype(np.int8),
            score.astype(np.float64),
            episode.astype(np.int64),
            seed=seed,
            n_boot=BOOTSTRAPS,
        ),
        "sample_count": int(len(y)),
        "episode_count": int(len(np.unique(episode))),
        "positive_count": int(np.sum(y)),
        "negative_count": int(len(y) - np.sum(y)),
        "single_class_truth": bool(np.unique(y).size < 2),
    }


class FlatReader(nn.Module):
    def __init__(self, kind: str, input_dim: int) -> None:
        super().__init__()
        if kind == "linear":
            self.net = nn.Linear(input_dim, 1)
        elif kind == "mlp1":
            self.net = nn.Sequential(nn.Linear(input_dim, 64), nn.ReLU(), nn.Linear(64, 1))
        elif kind == "mlp2":
            self.net = nn.Sequential(
                nn.Linear(input_dim, 64),
                nn.ReLU(),
                nn.Linear(64, 64),
                nn.ReLU(),
                nn.Linear(64, 1),
            )
        else:
            raise ValueError(f"unknown flat reader kind: {kind}")

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x).squeeze(-1)


class TfmDiscriminator(nn.Module):
    def __init__(self, emb_dim: int, act_dim: int) -> None:
        super().__init__()
        self.model = LedgerAwareTransformer(emb_dim, act_dim)

    def forward(self, win_emb: torch.Tensor, win_act: torch.Tensor) -> torch.Tensor:
        logit, _ = self.model(win_emb, win_act)
        return logit


def normalize_flat_fit(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    mean = x.mean(axis=0)
    std = x.std(axis=0) + 1e-6
    return mean.astype(np.float32), std.astype(np.float32)


def normalize_emb_fit(win_emb: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    flat = win_emb.reshape(-1, win_emb.shape[-1])
    mean = flat.mean(axis=0)
    std = flat.std(axis=0) + 1e-6
    return mean.astype(np.float32), std.astype(np.float32)


def train_flat_reader(x: np.ndarray, y: np.ndarray, kind: str, *, seed: int) -> tuple[nn.Module, tuple[np.ndarray, np.ndarray], dict[str, Any]]:
    torch.manual_seed(seed)
    mean, std = normalize_flat_fit(x)
    x_t = torch.from_numpy(((x - mean) / std).astype(np.float32))
    y_t = torch.from_numpy(y.astype(np.float32))
    model = FlatReader(kind, x.shape[1])
    opt = torch.optim.AdamW(model.parameters(), lr=LR)
    bce = nn.BCEWithLogitsLoss()
    g = torch.Generator().manual_seed(seed)
    n = len(y)
    steps = 0
    t0 = time.perf_counter()
    model.train()
    for _ in range(EPOCHS):
        order = torch.randperm(n, generator=g)
        for start in range(0, n, BATCH):
            sel = order[start : start + BATCH]
            logit = model(x_t[sel])
            loss = bce(logit, y_t[sel])
            if not torch.isfinite(loss):
                raise SystemExit(f"non-finite loss while training {kind}")
            opt.zero_grad()
            loss.backward()
            opt.step()
            steps += 1
    info = {
        "status": "trained",
        "reader": kind,
        "parameter_count": int(sum(p.numel() for p in model.parameters())),
        "train_rows": int(n),
        "train_failure_rate": float(np.mean(y)),
        "optimizer_steps": int(steps),
        "epochs": EPOCHS,
        "lr": LR,
        "batch": BATCH,
        "wall_time_seconds": round(time.perf_counter() - t0, 2),
        "torch_seed": seed,
        "device": "cpu",
    }
    return model, (mean, std), info


def score_flat_reader(model: nn.Module, norm: tuple[np.ndarray, np.ndarray], x: np.ndarray) -> np.ndarray:
    mean, std = norm
    out = np.empty(len(x), dtype=np.float64)
    model.eval()
    with torch.no_grad():
        for start in range(0, len(x), 1024):
            sl = slice(start, min(start + 1024, len(x)))
            xx = torch.from_numpy(((x[sl] - mean) / std).astype(np.float32))
            out[sl] = torch.sigmoid(model(xx)).numpy()
    return out


def train_tfm_reader(
    win_emb: np.ndarray,
    win_act: np.ndarray,
    y: np.ndarray,
    *,
    seed: int,
) -> tuple[nn.Module, tuple[np.ndarray, np.ndarray], dict[str, Any]]:
    torch.manual_seed(seed)
    emb_mean, emb_std = normalize_emb_fit(win_emb)
    x_emb = torch.from_numpy(((win_emb - emb_mean) / emb_std).astype(np.float32))
    x_act = torch.from_numpy(win_act.astype(np.float32))
    y_t = torch.from_numpy(y.astype(np.float32))
    model = TfmDiscriminator(win_emb.shape[-1], win_act.shape[-1])
    opt = torch.optim.AdamW(model.parameters(), lr=LR)
    bce = nn.BCEWithLogitsLoss()
    g = torch.Generator().manual_seed(seed)
    n = len(y)
    steps = 0
    t0 = time.perf_counter()
    model.train()
    for _ in range(EPOCHS):
        order = torch.randperm(n, generator=g)
        for start in range(0, n, BATCH):
            sel = order[start : start + BATCH]
            logit = model(x_emb[sel], x_act[sel])
            loss = bce(logit, y_t[sel])
            if not torch.isfinite(loss):
                raise SystemExit("non-finite loss while training tfm")
            opt.zero_grad()
            loss.backward()
            opt.step()
            steps += 1
    info = {
        "status": "trained",
        "reader": "tfm",
        "parameter_count": int(sum(p.numel() for p in model.parameters())),
        "train_rows": int(n),
        "train_failure_rate": float(np.mean(y)),
        "optimizer_steps": int(steps),
        "epochs": EPOCHS,
        "lr": LR,
        "batch": BATCH,
        "dynamics_weight": 0.0,
        "wall_time_seconds": round(time.perf_counter() - t0, 2),
        "torch_seed": seed,
        "device": "cpu",
    }
    return model, (emb_mean, emb_std), info


def score_tfm_reader(
    model: nn.Module,
    norm: tuple[np.ndarray, np.ndarray],
    win_emb: np.ndarray,
    win_act: np.ndarray,
) -> np.ndarray:
    emb_mean, emb_std = norm
    out = np.empty(len(win_emb), dtype=np.float64)
    model.eval()
    with torch.no_grad():
        for start in range(0, len(win_emb), 1024):
            sl = slice(start, min(start + 1024, len(win_emb)))
            x_emb = torch.from_numpy(((win_emb[sl] - emb_mean) / emb_std).astype(np.float32))
            x_act = torch.from_numpy(win_act[sl].astype(np.float32))
            out[sl] = torch.sigmoid(model(x_emb, x_act)).numpy()
    return out


def train_reader(part: dict[str, np.ndarray], kind: str, *, seed: int) -> tuple[Any, tuple[np.ndarray, np.ndarray], dict[str, Any]]:
    if kind == "tfm":
        return train_tfm_reader(part["win_emb"], part["win_act"], part["y"], seed=seed)
    return train_flat_reader(flatten_windows(part["win_emb"], part["win_act"]), part["y"], kind, seed=seed)


def score_reader(model: Any, norm: tuple[np.ndarray, np.ndarray], part: dict[str, np.ndarray], kind: str) -> np.ndarray:
    if kind == "tfm":
        return score_tfm_reader(model, norm, part["win_emb"], part["win_act"])
    return score_flat_reader(model, norm, flatten_windows(part["win_emb"], part["win_act"]))


def concat_train_parts(parts: list[dict[str, np.ndarray]]) -> dict[str, np.ndarray]:
    return {
        "win_emb": np.concatenate([p["win_emb"] for p in parts], axis=0).astype(np.float32),
        "win_act": np.concatenate([p["win_act"] for p in parts], axis=0).astype(np.float32),
        "y": np.concatenate([p["y"] for p in parts], axis=0).astype(np.int8),
        "episode": np.concatenate([p["episode"] for p in parts], axis=0).astype(np.int64),
    }


def materialize_slices(
    data: dict[str, np.ndarray],
    splits: dict[str, np.ndarray],
    tau: float,
) -> tuple[dict[tuple[str, float, str], dict[str, np.ndarray]], dict[str, list[float]]]:
    rows1c = flatten_transition_rows(data)
    split_rows_idx = {
        name: np.where(np.isin(rows1c["episode"], splits[name]))[0] for name in ("train", "eval")
    }
    grids = perturbation_grid()
    slices: dict[tuple[str, float, str], dict[str, np.ndarray]] = {}

    device = torch.device("cpu")
    checkpoint_path = hf_hub_download(MODEL_REPO, "weights.pt", repo_type="model")
    config_path = hf_hub_download(MODEL_REPO, "config.json", repo_type="model")
    with open(config_path, "r", encoding="utf-8") as f:
        config = json.load(f)
    lewm = build_model(config)
    load_checkpoint(lewm, checkpoint_path)
    lewm.to(device).eval().requires_grad_(False)

    with h5py.File(H5_PATH, "r") as h5:
        for family, strengths in grids.items():
            for strength_raw in strengths:
                strength = float(strength_raw)
                if strength == 0.0:
                    continue
                for split_name in ("train", "eval"):
                    emb_path = split_emb_cache_path(split_name, family, strength)
                    pert_emb_by_ep = load_emb_cache(emb_path)
                    if pert_emb_by_ep is None:
                        print(f"[encode] {split_name} {family} strength={strength:g}", flush=True)
                        pert_emb_by_ep = encode_split_episodes_batched(
                            h5,
                            lewm,
                            config,
                            data,
                            splits[split_name],
                            family,
                            strength,
                            device,
                            encode_batch_size=64,
                        )
                        save_emb_cache(emb_path, pert_emb_by_ep)

                    m_path = mse_cache_path(split_name, family, strength)
                    if m_path.exists():
                        raw = np.load(m_path)
                        valid_idx = raw["row_idx"].astype(np.int64)
                        mse = raw["mse"].astype(np.float64)
                    else:
                        print(f"[mse] {split_name} {family} strength={strength:g}", flush=True)
                        valid_idx, mse = predict_eval_rows(
                            lewm,
                            data,
                            rows1c,
                            split_rows_idx[split_name],
                            pert_emb_by_ep,
                            device,
                            batch_size=512,
                        )
                        tmp = m_path.with_name("tmp_" + m_path.name)
                        np.savez_compressed(tmp, row_idx=valid_idx, mse=mse)
                        tmp.replace(m_path)

                    episodes = rows1c["episode"][valid_idx].astype(np.int64)
                    ts = rows1c["t"][valid_idx].astype(np.int64)
                    win_emb, win_act = build_perturbed_windows(
                        pert_emb_by_ep,
                        data["action"].astype(np.float32),
                        episodes,
                        ts,
                    )
                    finite = np.isfinite(win_emb).all(axis=(1, 2)) & np.isfinite(win_act).all(axis=(1, 2)) & np.isfinite(mse)
                    slices[(family, strength, split_name)] = {
                        "family": np.asarray([family] * int(finite.sum()), dtype=object),
                        "strength": np.full(int(finite.sum()), strength, dtype=np.float64),
                        "win_emb": win_emb[finite].astype(np.float32),
                        "win_act": win_act[finite].astype(np.float32),
                        "y": (mse[finite] > tau).astype(np.int8),
                        "episode": episodes[finite].astype(np.int64),
                        "mse": mse[finite].astype(np.float64),
                    }
    return slices, {k: [float(s) for s in v if float(s) != 0.0] for k, v in grids.items()}


def main() -> None:
    np.random.seed(PYTHON_SEED)
    torch.manual_seed(PYTHON_SEED)
    REPORT_DIR.mkdir(exist_ok=True)

    data = dict(np.load(NPZ_PATH))
    rows = build_windows(data)
    n_ep = data["emb"].shape[0]
    splits = split_episodes(n_ep)
    masks = {name: np.isin(rows["episode"], eps) for name, eps in splits.items()}
    train_mask, eval_mask = masks["train"], masks["eval"]
    tau = float(np.percentile(rows["mse"][train_mask], 75))
    y_clean_all = (rows["mse"] > tau).astype(np.int8)

    clean_train = {
        "win_emb": rows["win_emb"][train_mask].astype(np.float32),
        "win_act": rows["win_act"][train_mask].astype(np.float32),
        "y": y_clean_all[train_mask].astype(np.int8),
        "episode": rows["episode"][train_mask].astype(np.int64),
    }
    clean_eval = {
        "win_emb": rows["win_emb"][eval_mask].astype(np.float32),
        "win_act": rows["win_act"][eval_mask].astype(np.float32),
        "y": y_clean_all[eval_mask].astype(np.int8),
        "episode": rows["episode"][eval_mask].astype(np.int64),
    }

    slices, grids = materialize_slices(data, splits, tau)
    ood_train = concat_train_parts(
        [clean_train]
        + [
            slices[(family, strength, "train")]
            for family in grids
            for strength in grids[family]
        ]
    )

    eval_slices = {
        "clean": clean_eval,
        **{
            f"{family}@{strength_token(strength)}": slices[(family, strength, "eval")]
            for family in grids
            for strength in grids[family]
        },
    }
    final_strengths = {family: strengths[-1] for family, strengths in grids.items()}
    final_slice_keys = {family: f"{family}@{strength_token(strength)}" for family, strength in final_strengths.items()}
    bg_key = final_slice_keys["background_tint"]

    arms: dict[str, Any] = {}
    table_rows: list[dict[str, Any]] = []
    frontier: dict[str, Any] = {}

    for reader_i, reader in enumerate(READERS):
        reader_results: dict[str, Any] = {}
        trained: dict[str, tuple[Any, tuple[np.ndarray, np.ndarray]]] = {}
        for arm_i, arm in enumerate(ARMS):
            train_part = clean_train if arm == "clean_trained" else ood_train
            print(f"[train] {reader}/{arm} rows={len(train_part['y'])}", flush=True)
            model, norm, info = train_reader(train_part, reader, seed=PYTHON_SEED)
            trained[arm] = (model, norm)
            arm_report: dict[str, Any] = {"info": info, "eval": {}}
            for slice_i, (slice_key, part) in enumerate(eval_slices.items()):
                score = score_reader(model, norm, part, reader)
                seed = BOOTSTRAP_SEED + 100000 * reader_i + 10000 * arm_i + slice_i
                arm_report["eval"][slice_key] = {
                    **eval_metrics(part["y"], score, part["episode"], seed=seed),
                    "failure_rate": float(np.mean(part["y"])),
                    "mean_score": float(np.mean(score)),
                    "declared_gap_rate": float(np.mean(score >= 0.5)),
                }
            reader_results[arm] = arm_report
            clean_m = arm_report["eval"]["clean"]["failure_detection_auroc"]
            bg_m = arm_report["eval"][bg_key]["failure_detection_auroc"]
            table_rows.append(
                {
                    "reader": reader,
                    "arm": arm,
                    "train_rows": info["train_rows"],
                    "train_failure_rate": info["train_failure_rate"],
                    "clean_eval_auroc": clean_m,
                    "background_tint_0p6_auroc": bg_m,
                    "declared_gap_rate_clean": arm_report["eval"]["clean"]["declared_gap_rate"],
                    "declared_gap_rate_background_tint_0p6": arm_report["eval"][bg_key]["declared_gap_rate"],
                    "final_strength_auroc": {
                        family: arm_report["eval"][key]["failure_detection_auroc"]
                        for family, key in final_slice_keys.items()
                    },
                }
            )

        clean_clean = reader_results["clean_trained"]["eval"]["clean"]["failure_detection_auroc"]
        clean_ood = reader_results["ood_aware"]["eval"]["clean"]["failure_detection_auroc"]
        bg_ood = reader_results["ood_aware"]["eval"][bg_key]["failure_detection_auroc"]
        frontier[reader] = {
            "delta_clean": float(clean_ood["observed"] - clean_clean["observed"]),
            "clean_trained_clean_eval_auroc": clean_clean,
            "ood_aware_clean_eval_auroc": clean_ood,
            "ood_aware_background_tint_0p6_auroc": bg_ood,
            "ood_aware_final_strength_auroc": {
                family: reader_results["ood_aware"]["eval"][key]["failure_detection_auroc"]
                for family, key in final_slice_keys.items()
            },
        }
        arms[reader] = reader_results

    deltas = [frontier[r]["delta_clean"] for r in READERS]
    monotonic_non_decreasing = bool(all(a <= b + 1e-12 for a, b in zip(deltas, deltas[1:])))
    tfm_anchor = frontier["tfm"]["clean_trained_clean_eval_auroc"]["observed"]
    lat_without_dynamics_reference = None
    tfm_anchor_delta = None
    if PORT_JSON.exists():
        port = json.loads(PORT_JSON.read_text(encoding="utf-8"))
        lat_without_dynamics_reference = float(
            port["arms"]["lat_without_dynamics"]["metrics_eval_episode_bootstrap"]["failure_detection_auroc"]["observed"]
        )
        tfm_anchor_delta = float(tfm_anchor - lat_without_dynamics_reference)

    conclusion = {
        "delta_clean_order": {reader: frontier[reader]["delta_clean"] for reader in READERS},
        "delta_clean_monotonic_non_decreasing": monotonic_non_decreasing,
        "sentence": (
            "capacity frontier is monotonic non-decreasing over this grid"
            if monotonic_non_decreasing
            else "capacity frontier is not monotonic over this grid"
        ),
        "tfm_clean_anchor": {
            "observed": tfm_anchor,
            "published_lat_without_dynamics_reference": lat_without_dynamics_reference,
            "difference": tfm_anchor_delta,
            "within_0p02": None if tfm_anchor_delta is None else bool(abs(tfm_anchor_delta) <= 0.02),
        },
    }

    report = {
        "schema_id": "lewm.reader_capacity_frontier",
        "protocol": {
            "input": "flattened WINDOW=6 windows of (emb, action)",
            "input_dim": int(WINDOW * (rows["win_emb"].shape[-1] + rows["win_act"].shape[-1])),
            "window": WINDOW,
            "failure_truth": "prediction_mse > clean train p75",
            "tau_err_train_p75": tau,
            "split_seed": SPLIT_SEED,
            "numpy_torch_seed": PYTHON_SEED,
            "bootstrap_seed": BOOTSTRAP_SEED,
            "bootstraps": BOOTSTRAPS,
            "bootstrap_unit": "episode",
            "optimizer": "AdamW",
            "lr": LR,
            "loss": "BCEWithLogitsLoss",
            "epochs": EPOCHS,
            "batch": BATCH,
            "dynamics_loss": "not used for any reader in this experiment",
            "perturbation_grid": grids,
            "emb_cache_dir": str(EMB_CACHE),
        },
        "sample_counts": {
            "valid_clean_windows": int(len(rows["episode"])),
            "clean_train_windows": int(len(clean_train["y"])),
            "clean_eval_windows": int(len(clean_eval["y"])),
            "ood_aware_train_windows": int(len(ood_train["y"])),
            "episodes": int(n_ep),
            "train_episodes": int(len(splits["train"])),
            "eval_episodes": int(len(splits["eval"])),
        },
        "frontier": frontier,
        "table_rows": table_rows,
        "arms": arms,
        "conclusion": conclusion,
        "not_claimed": [
            "architecture optimality",
            "claims beyond this four-reader capacity grid",
            "claims beyond the tworooms checkpoint or this perturbation grid",
        ],
    }
    JSON_PATH.write_text(json.dumps(clean_json(report), indent=2), encoding="utf-8")

    lines = [
        "# LeWM Reader Capacity Frontier",
        "",
        "Pure-discriminator readers over flattened `(emb, action)` windows. OOD-aware arms train on clean train windows plus all 20 perturbed train slices.",
        "",
        f"- tau: {tau:.12f} (clean train p75 prediction_mse)",
        f"- input dim: {report['protocol']['input_dim']} = 6 x 202",
        f"- Delta clean monotonic non-decreasing: {monotonic_non_decreasing}",
        "",
        "## 4x2 Frontier Table",
        "",
        "| reader | arm | train rows | train fail rate | clean eval AUROC | bg_tint@0.6 AUROC | final color_shift | final occlusion | final brightness | final gaussian_noise |",
        "| --- | --- | ---: | ---: | --- | --- | --- | --- | --- | --- |",
    ]
    for row in table_rows:
        final = row["final_strength_auroc"]
        lines.append(
            f"| `{row['reader']}` | `{row['arm']}` | {row['train_rows']} | {row['train_failure_rate']:.3f} "
            f"| {fmt_ci(row['clean_eval_auroc'])} | {fmt_ci(row['background_tint_0p6_auroc'])} "
            f"| {fmt_ci(final['color_shift'])} | {fmt_ci(final['occlusion'])} "
            f"| {fmt_ci(final['brightness'])} | {fmt_ci(final['gaussian_noise'])} |"
        )

    lines += [
        "",
        "## Delta Clean Frontier",
        "",
        "| reader | Delta clean | ood-aware bg_tint@0.6 AUROC |",
        "| --- | ---: | --- |",
    ]
    for reader in READERS:
        f = frontier[reader]
        lines.append(
            f"| `{reader}` | {f['delta_clean']:+.4f} | {fmt_ci(f['ood_aware_background_tint_0p6_auroc'])} |"
        )

    lines += [
        "",
        "## Conclusion",
        "",
        conclusion["sentence"] + ".",
        "",
        "## not_claimed",
        "",
        "- architecture optimality",
        "- claims beyond this four-reader capacity grid",
        "- claims beyond the tworooms checkpoint or this perturbation grid",
    ]
    if tfm_anchor_delta is not None and abs(tfm_anchor_delta) > 0.02:
        lines += [
            "",
            "## Anchor Check",
            "",
            f"- tfm clean_trained clean AUROC differs from published lat_without_dynamics by {tfm_anchor_delta:+.4f}; this run uses the frozen pure-discriminator recipe.",
        ]
    MD_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(json.dumps(clean_json(conclusion), indent=2))
    print(JSON_PATH)
    print(MD_PATH)


if __name__ == "__main__":
    main()

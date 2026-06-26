#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import os
import random
import sys
from pathlib import Path
from typing import Any

os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"

import numpy as np

try:
    import torch
except ModuleNotFoundError:  # pragma: no cover
    torch = None  # type: ignore[assignment]


SCRIPT_PATH = Path(__file__).resolve()
SURVEY_DIR = SCRIPT_PATH.parents[2]
if str(SURVEY_DIR) not in sys.path:
    sys.path.insert(0, str(SURVEY_DIR))

from _phase1c_gap_ledger import (  # noqa: E402
    auroc_rank,
    basic_metrics,
    fit_logistic_head,
    predict_logistic_head,
    split_episodes,
)


HYPOTHESIS_ID = "fi-002.pusht-independent-export"
METRIC = "uer_delta"
ROOT_NPZ_PATH = SURVEY_DIR / "pusht_latent_large.npz"
C3B_DIR = Path(r"artifacts/pusht_indep_export\C3b_stratified_random_seed2718")
C3B_NPZ_PATH = C3B_DIR / "pusht_latent_large.npz"
C3B_LABELS_PATH = C3B_DIR / "crossenv_horizon_labels_pusht_C3b_stratified_random_seed2718.npz"
BOOTSTRAPS = 500
H1 = 1
Q75 = 75


def set_determinism(seed: int) -> None:
    os.environ["PYTHONHASHSEED"] = str(seed)
    os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"
    random.seed(seed)
    np.random.seed(seed)
    if torch is None:
        return
    torch.manual_seed(seed)
    if torch.cuda.is_available():
        torch.cuda.manual_seed_all(seed)
    torch.use_deterministic_algorithms(True)
    if hasattr(torch.backends, "cudnn"):
        torch.backends.cudnn.benchmark = False
        torch.backends.cudnn.deterministic = True
    try:
        torch.set_num_threads(1)
        torch.set_num_interop_threads(1)
    except RuntimeError:
        pass


def clean_float(value: float) -> float:
    value = float(value)
    if value == 0.0:
        return 0.0
    if not math.isfinite(value):
        raise ValueError(f"non-finite float in payload: {value!r}")
    return value


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
    if isinstance(v, float):
        return clean_float(v)
    return v


def load_npz_dict(path: Path) -> dict[str, np.ndarray]:
    if not path.exists():
        raise FileNotFoundError(path)
    with np.load(path, allow_pickle=False) as raw:
        return {key: raw[key] for key in raw.files}


def choose_export() -> tuple[Path, Path | None, str]:
    if C3B_NPZ_PATH.exists() and C3B_LABELS_PATH.exists():
        return C3B_NPZ_PATH, C3B_LABELS_PATH, "A"
    return ROOT_NPZ_PATH, None, "B"


def prediction_mse_identity_max_abs(data: dict[str, np.ndarray]) -> float:
    if "prediction_mse_identity_max_abs" in data:
        return clean_float(float(np.asarray(data["prediction_mse_identity_max_abs"]).item()))
    tm = data["transition_mask"].astype(bool)
    if not np.any(tm):
        return 0.0
    pred = data["pred"].astype(np.float64)
    target = data["transition_target_emb"].astype(np.float64)
    direct = np.mean((pred - target) ** 2, axis=-1)
    stored = data["prediction_mse"].astype(np.float64)
    delta = np.abs(direct[tm] - stored[tm])
    return clean_float(float(delta.max()) if delta.size else 0.0)


def flatten_rows(data: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    tm = data["transition_mask"].astype(bool)
    ep, t = np.where(tm)
    rows = {
        "episode": ep.astype(np.int64),
        "t": t.astype(np.int64),
        "emb": data["emb"][ep, t].astype(np.float64),
        "pred": data["pred"][ep, t].astype(np.float64),
        "mse": data["prediction_mse"][ep, t].astype(np.float64),
    }
    finite = (
        np.isfinite(rows["emb"]).all(axis=1)
        & np.isfinite(rows["pred"]).all(axis=1)
        & np.isfinite(rows["mse"])
    )
    return {key: val[finite] for key, val in rows.items()}


def uer_delta_metrics(
    y_err: np.ndarray,
    vanilla_score: np.ndarray,
    learned_score: np.ndarray,
) -> dict[str, float]:
    vanilla = basic_metrics(y_err, vanilla_score, vanilla_score)["unlogged_error_rate"]
    learned = basic_metrics(y_err, learned_score, learned_score)["unlogged_error_rate"]
    return {
        "uer": clean_float(float(learned)),
        "uer_baseline": clean_float(float(vanilla)),
        "uer_delta": clean_float(float(learned - vanilla)),
    }


def bootstrap_uer_delta_by_episode(
    y_err: np.ndarray,
    vanilla_score: np.ndarray,
    learned_score: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
    n_boot: int,
) -> tuple[dict[str, float], tuple[float, float]]:
    observed = uer_delta_metrics(y_err, vanilla_score, learned_score)
    unique_ep = np.unique(episode)
    if unique_ep.size == 0:
        raise RuntimeError("eval split has zero episodes")
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    rng = np.random.default_rng(seed)
    values = np.empty(n_boot, dtype=np.float64)
    for i in range(n_boot):
        sampled = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[j] for j in sampled])
        values[i] = uer_delta_metrics(
            y_err[idx],
            vanilla_score[idx],
            learned_score[idx],
        )["uer_delta"]
    low = clean_float(float(np.nanpercentile(values, 2.5)))
    high = clean_float(float(np.nanpercentile(values, 97.5)))
    return observed, (low, high)


def h1_q75_posthoc_auroc(
    data: dict[str, np.ndarray],
    labels: dict[str, np.ndarray],
) -> float:
    horizons = [int(x) for x in labels["horizons"].reshape(-1)]
    quantiles = [int(x) for x in labels["quantiles"].reshape(-1)]
    h_idx = horizons.index(H1)
    q_idx = quantiles.index(Q75)

    train_valid = labels["train_valid"][:, h_idx].astype(bool)
    eval_valid = labels["eval_valid"][:, h_idx].astype(bool)
    train_y = labels["train_y"][train_valid, h_idx, q_idx].astype(np.int8)
    eval_y = labels["eval_y"][eval_valid, h_idx, q_idx].astype(np.int8)
    train_anchors = labels["train_anchor_ep_t0"][train_valid].astype(np.int64)
    eval_anchors = labels["eval_anchor_ep_t0"][eval_valid].astype(np.int64)

    if train_anchors.size == 0 or eval_anchors.size == 0:
        raise RuntimeError("h1 q75 labels have zero train or eval anchors")

    x_train = np.asarray(
        [data["emb"][int(ep), int(t)] for ep, t in train_anchors],
        dtype=np.float64,
    )
    x_eval = np.asarray(
        [data["emb"][int(ep), int(t)] for ep, t in eval_anchors],
        dtype=np.float64,
    )

    if np.unique(train_y).size < 2 or np.unique(eval_y).size < 2:
        return 0.5
    head, _info = fit_logistic_head(x_train, train_y, steps=2500, lr=0.05, l2=1e-4)
    score, _logit = predict_logistic_head(head, x_eval)
    return clean_float(auroc_rank(eval_y, score))


def compute_uer_payload(seed: int, data: dict[str, np.ndarray], scope_mode: str) -> tuple[dict[str, Any], bool]:
    rows = flatten_rows(data)
    splits = split_episodes(int(data["emb"].shape[0]))
    masks = {name: np.isin(rows["episode"], eps) for name, eps in splits.items()}
    train_mask = masks["train"]
    eval_mask = masks["eval"]

    if int(train_mask.sum()) == 0 or int(eval_mask.sum()) == 0:
        claim = (
            "A: 独立 stratified C3b 导出上 train/eval transition 为空，UER delta 不可识别。"
            if scope_mode == "A"
            else "B: 仅当前 root pusht_latent_large.npz 上 train/eval transition 为空，非独立 stratified replication，UER delta 不可识别。"
        )
        return (
            {
                "metric_value": 0.0,
                "ci": {"low": 0.0, "high": 0.0},
                "status": "fail-closed",
                "measured_scope": ["uer_delta", "uer"],
                "reported_claim": claim,
            },
            True,
        )

    tau = float(np.percentile(rows["mse"][train_mask], 75))
    y = (rows["mse"] > tau).astype(np.int8)
    y_train = y[train_mask]
    y_eval = y[eval_mask]
    train_rate = float(y_train.mean()) if len(y_train) else 0.5
    vanilla = np.full(len(y), train_rate, dtype=np.float64)

    single_class = bool(np.unique(y_train).size < 2 or np.unique(y_eval).size < 2)
    if single_class:
        claim = (
            "A: 独立 stratified C3b 导出上 train/eval prediction-error 标签单类，UER delta 不可识别。"
            if scope_mode == "A"
            else "B: 仅当前 root pusht_latent_large.npz 上 prediction-error 标签单类，非独立 stratified replication，UER delta 不可识别。"
        )
        return (
            {
                "metric_value": 0.0,
                "ci": {"low": 0.0, "high": 0.0},
                "status": "fail-closed",
                "measured_scope": ["uer_delta", "uer"],
                "reported_claim": claim,
            },
            True,
        )

    head, _info = fit_logistic_head(
        rows["emb"][train_mask],
        y_train,
        steps=2500,
        lr=0.05,
        l2=1e-4,
    )
    learned, _logit = predict_logistic_head(head, rows["emb"])
    observed, ci = bootstrap_uer_delta_by_episode(
        y_eval,
        vanilla[eval_mask],
        learned[eval_mask],
        rows["episode"][eval_mask],
        seed=seed,
        n_boot=BOOTSTRAPS,
    )

    return (
        {
            "metric_value": clean_float(observed["uer_delta"]),
            "ci": {"low": ci[0], "high": ci[1]},
            "measured_scope": ["uer_delta", "uer"],
            "reported_claim": (
                f"A: 独立 stratified C3b 导出上 learned-vs-vanilla UER delta={observed['uer_delta']:.12g} "
                f"(CI [{ci[0]:.12g},{ci[1]:.12g}])。"
                if scope_mode == "A"
                else (
                    f"B: 仅当前 root pusht_latent_large.npz 上测 learned-vs-vanilla UER drop，"
                    f"非独立 stratified replication；UER delta={observed['uer_delta']:.12g} "
                    f"(CI [{ci[0]:.12g},{ci[1]:.12g}])。"
                )
            ),
        },
        False,
    )


def measure(seed: int) -> dict[str, Any]:
    set_determinism(seed)
    npz_path, labels_path, scope_mode = choose_export()
    data = load_npz_dict(npz_path)
    anchor = prediction_mse_identity_max_abs(data)
    uer_part, fail_closed = compute_uer_payload(seed, data, scope_mode)

    measured_scope = list(uer_part["measured_scope"])
    reported_claim = str(uer_part["reported_claim"])
    if scope_mode == "A":
        assert labels_path is not None
        labels = load_npz_dict(labels_path)
        auroc = h1_q75_posthoc_auroc(data, labels)
        measured_scope.append("auroc")
        reported_claim = (
            f"A: 独立 stratified C3b 导出上 learned-vs-vanilla UER delta={uer_part['metric_value']:.12g} "
            f"(CI [{uer_part['ci']['low']:.12g},{uer_part['ci']['high']:.12g}])；"
            f"posthoc h1/q75 AUROC={auroc:.12g}。"
        )

    payload: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": anchor},
        "metric": METRIC,
        "metric_value": uer_part["metric_value"],
        "ci": uer_part["ci"],
        "measured_scope": measured_scope,
        "reported_claim": reported_claim,
    }
    if fail_closed:
        payload["status"] = "fail-closed"
    return clean_json(payload)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True, help="Path to write the frozen verdict payload JSON.")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    payload = measure(args.seed)
    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    if torch is not None and torch.cuda.is_available():
        torch.cuda.empty_cache()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
import os
import random
import sys
import types
from pathlib import Path
from typing import Any, Callable

os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"

import numpy as np


SCRIPT_PATH = Path(__file__).resolve()
ROOT = SCRIPT_PATH.parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from _phase1c_gap_ledger import fit_logistic_head, predict_logistic_head  # noqa: E402


HYPOTHESIS_ID = "fi-005.conformal-selective-risk-holds"
NPZ_PATH = ROOT / "pusht_latent_large.npz"
ALPHA = 0.10
TARGET_H = 5
PRIMARY_Q = 75.0
HISTORY = 6
SPLIT_SEED = 1701
BOOTSTRAPS = 500
BOOTSTRAP_SEED_OFFSET = 314159
ANCHOR_TOL = 1e-12


def set_determinism(seed: int) -> None:
    os.environ["PYTHONHASHSEED"] = str(seed)
    os.environ["CUBLAS_WORKSPACE_CONFIG"] = ":4096:8"
    random.seed(seed)
    np.random.seed(seed)
    try:
        import torch
    except ModuleNotFoundError:
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


def install_conformal_import_stubs() -> None:
    """Allow importing _conformal_calibration without executing heavy report deps."""
    stubs: dict[str, dict[str, Any]] = {
        "_phase2a_brittleness_gap": {
            "NPZ_PATH": NPZ_PATH,
            "fit_clean_protocol": lambda *args, **kwargs: None,
            "perturbation_grid": lambda: {},
        },
        "_phase2c_ood_aware_gap": {
            "cache_path": lambda *args, **kwargs: ROOT / "missing.npz",
            "fit_gap_head_for_parts": lambda *args, **kwargs: None,
            "load_part_cache": lambda *args, **kwargs: None,
            "materialize_clean_split": lambda *args, **kwargs: None,
        },
        "_lat_lewm_ood": {
            "build_perturbed_windows": lambda *args, **kwargs: None,
            "load_emb_cache": lambda *args, **kwargs: None,
            "strength_token": lambda strength: str(strength).replace(".", "p"),
        },
        "_lat_lewm_ood_aware": {
            "mse_cache_path": lambda *args, **kwargs: ROOT / "missing.npz",
            "score_lat": lambda *args, **kwargs: None,
            "split_emb_cache_path": lambda *args, **kwargs: ROOT / "missing.npz",
            "train_lat": lambda *args, **kwargs: None,
        },
        "_lat_lewm_port": {
            "DYNAMICS_WEIGHT": 0.0,
            "NPZ_PATH": NPZ_PATH,
            "PYTHON_SEED": 0,
            "REPORT_DIR": ROOT / "reports",
            "build_windows": lambda *args, **kwargs: None,
            "split_episodes": lambda *args, **kwargs: None,
            "train_arm": lambda *args, **kwargs: None,
        },
    }
    for name, attrs in stubs.items():
        module = types.ModuleType(name)
        for key, value in attrs.items():
            setattr(module, key, value)
        sys.modules[name] = module


def load_conformal_functions() -> tuple[Callable[..., dict[str, Any]], Callable[..., dict[str, Any]]]:
    install_conformal_import_stubs()
    import _conformal_calibration as conformal

    return conformal.calibrate_threshold, conformal.evaluate_selective


def clean_float(value: float) -> float:
    value = float(value)
    if value == 0.0:
        return 0.0
    if not math.isfinite(value):
        raise ValueError(f"non-finite float in payload: {value!r}")
    return value


def clean_json(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): clean_json(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [clean_json(v) for v in value]
    if isinstance(value, np.ndarray):
        return clean_json(value.tolist())
    if isinstance(value, np.integer):
        return int(value)
    if isinstance(value, np.floating):
        value = float(value)
    if isinstance(value, float):
        return clean_float(value)
    return value


def load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as raw:
        return {key: raw[key] for key in raw.files}


def identity_anchor(data: dict[str, np.ndarray]) -> float:
    if "prediction_mse_identity_max_abs" in data:
        return clean_float(float(np.asarray(data["prediction_mse_identity_max_abs"]).item()))
    tm = data["transition_mask"].astype(bool)
    if not np.any(tm):
        return 0.0
    pred = data["pred"].astype(np.float64)
    target = data["transition_target_emb"].astype(np.float64)
    direct = np.mean((pred - target) ** 2, axis=-1)
    stored = data["prediction_mse"].astype(np.float64)
    return clean_float(float(np.max(np.abs(direct[tm] - stored[tm]))))


def split_episodes(n_ep: int, seed: int) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(seed)
    perm = rng.permutation(n_ep)
    n_train = int(round(0.60 * n_ep))
    n_cal = int(round(0.20 * n_ep))
    return {
        "train": np.sort(perm[:n_train]),
        "calibration": np.sort(perm[n_train : n_train + n_cal]),
        "eval": np.sort(perm[n_train + n_cal :]),
    }


def build_rows(data: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    emb = data["emb"].astype(np.float64)
    action = data["action"].astype(np.float64)
    mse = data["prediction_mse"].astype(np.float64)
    tm = data["transition_mask"].astype(bool)

    episodes: list[int] = []
    steps: list[int] = []
    features: list[np.ndarray] = []
    target_err: list[float] = []

    max_transitions = tm.shape[1]
    for ep in range(tm.shape[0]):
        valid_count = int(tm[ep].sum())
        for t_raw in np.where(tm[ep])[0]:
            t = int(t_raw)
            if t < 1 or t + TARGET_H > max_transitions:
                continue
            if t + TARGET_H > valid_count or not bool(np.all(tm[ep, t : t + TARGET_H])):
                continue

            future_err = float(np.mean(mse[ep, t : t + TARGET_H]))
            if not math.isfinite(future_err):
                continue

            chunks: list[np.ndarray] = []
            for offset in range(HISTORY):
                src = max(0, t - HISTORY + 1 + offset)
                chunks.append(emb[ep, src])
                chunks.append(action[ep, src])

            past_gap_values = np.zeros(HISTORY, dtype=np.float64)
            for offset in range(HISTORY):
                src = t - HISTORY + offset
                if 0 <= src < t and src < mse.shape[1] and tm[ep, src]:
                    past_gap_values[offset] = mse[ep, src]
            past_gap_summary = np.asarray(
                [
                    float(np.mean(past_gap_values)),
                    float(np.max(past_gap_values)),
                    float(np.std(past_gap_values)),
                    float(t) / float(max(1, valid_count - 1)),
                    float(valid_count) / float(max(1, max_transitions)),
                ],
                dtype=np.float64,
            )
            chunks.append(past_gap_values)
            chunks.append(past_gap_summary)
            x = np.concatenate(chunks).astype(np.float64)

            if not np.all(np.isfinite(x)):
                continue
            episodes.append(ep)
            steps.append(t)
            features.append(x)
            target_err.append(future_err)

    if not features:
        raise RuntimeError("no non-leaking target-horizon rows were constructed")
    return {
        "episode": np.asarray(episodes, dtype=np.int64),
        "t": np.asarray(steps, dtype=np.int64),
        "x": np.stack(features).astype(np.float64),
        "target_err": np.asarray(target_err, dtype=np.float64),
    }


def margin_from_selective_eval(result: dict[str, Any], alpha: float) -> float:
    risk = result.get("realized_p_fail_given_ok")
    if risk is None:
        return -float(alpha)
    return clean_float(float(alpha) - float(risk))


def bootstrap_margin_ci(
    score: np.ndarray,
    y: np.ndarray,
    episode: np.ndarray,
    tau: float | None,
    alpha: float,
    evaluate_selective: Callable[..., dict[str, Any]],
    seed: int,
) -> tuple[float, float]:
    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    rng = np.random.default_rng(seed)
    values = np.empty(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        sampled = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[j] for j in sampled])
        ev = evaluate_selective(score[idx], y[idx], tau, alpha)
        values[i] = margin_from_selective_eval(ev, alpha)
    return (
        clean_float(float(np.percentile(values, 2.5))),
        clean_float(float(np.percentile(values, 97.5))),
    )


def final_status(ci_low: float, ci_high: float, single_class: bool) -> str:
    if single_class:
        return "fail-closed"
    if ci_low > 0.0:
        return "positive"
    if ci_high <= 0.0:
        return "negative"
    return "fail-closed"


def make_claim(realized_risk: float | None, margin: float, ci_low: float, ci_high: float, status: str) -> str:
    risk_text = "NA" if realized_risk is None else f"{realized_risk:.12g}"
    if status == "positive":
        verdict = "CI low>0，选择性保证成立"
    elif status == "negative":
        verdict = "CI high<=0，held-out eval 上违约"
    else:
        verdict = "CI 跨 0 或单类/空 admitted，不可识别并 fail-closed"
    return (
        f"α=0.10 下 admitted realized risk={risk_text}, "
        f"risk_margin={margin:.12g}, CI=[{ci_low:.12g},{ci_high:.12g}]；{verdict}。"
    )


def fail_closed_payload(anchor_value: float, reason: str) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": clean_float(anchor_value)},
        "metric": "risk_margin",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["risk_margin", "uer"],
        "reported_claim": f"α=0.10 下 realized risk 与 risk_margin 不可识别；{reason}。",
    }


def measure(seed: int) -> dict[str, Any]:
    set_determinism(seed)
    calibrate_threshold, evaluate_selective = load_conformal_functions()
    data = load_npz(NPZ_PATH)
    anchor_value = identity_anchor(data)
    if abs(anchor_value) > ANCHOR_TOL:
        return fail_closed_payload(anchor_value, "identity anchor 未通过")

    rows = build_rows(data)
    splits = split_episodes(int(data["emb"].shape[0]), SPLIT_SEED + seed)
    masks = {name: np.isin(rows["episode"], eps) for name, eps in splits.items()}
    train_mask = masks["train"]
    cal_mask = masks["calibration"]
    eval_mask = masks["eval"]
    if int(train_mask.sum()) == 0 or int(cal_mask.sum()) == 0 or int(eval_mask.sum()) == 0:
        return fail_closed_payload(anchor_value, "train/calibration/eval split 至少一个为空")

    tau_err = float(np.percentile(rows["target_err"][train_mask], PRIMARY_Q))
    y = (rows["target_err"] > tau_err).astype(np.int8)
    y_train = y[train_mask]
    y_cal = y[cal_mask]
    y_eval = y[eval_mask]
    single_class = bool(
        np.unique(y_train).size < 2
        or np.unique(y_cal).size < 2
        or np.unique(y_eval).size < 2
    )

    head, _info = fit_logistic_head(
        rows["x"][train_mask],
        y_train,
        steps=2500,
        lr=0.05,
        l2=1e-4,
    )
    score_all, _logit = predict_logistic_head(head, rows["x"])
    calibration = calibrate_threshold(score_all[cal_mask], y_cal, ALPHA)
    tau = calibration["threshold"] if calibration.get("status") == "ok" else None
    eval_result = evaluate_selective(score_all[eval_mask], y_eval, tau, ALPHA)
    margin = margin_from_selective_eval(eval_result, ALPHA)
    ci_low, ci_high = bootstrap_margin_ci(
        score_all[eval_mask],
        y_eval,
        rows["episode"][eval_mask],
        tau,
        ALPHA,
        evaluate_selective,
        seed + BOOTSTRAP_SEED_OFFSET,
    )
    status = final_status(ci_low, ci_high, single_class or tau is None or eval_result.get("realized_p_fail_given_ok") is None)
    realized_risk = eval_result.get("realized_p_fail_given_ok")

    payload: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": clean_float(anchor_value)},
        "metric": "risk_margin",
        "metric_value": clean_float(margin),
        "ci": {"low": ci_low, "high": ci_high},
    }
    if status == "fail-closed":
        payload["status"] = "fail-closed"
    payload["measured_scope"] = ["risk_margin", "uer"]
    payload["reported_claim"] = make_claim(realized_risk, margin, ci_low, ci_high, status)
    return clean_json(payload)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    payload = measure(args.seed)
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

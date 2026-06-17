from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np

import _compute_value_structured_assignment as structured


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_JSON = REPORT_DIR / "compute_value_survival_matrix.json"
DEFAULT_MD = REPORT_DIR / "compute_value_survival_matrix.md"
ARTIFACTS = {
    "pusht": REPORT_DIR / "compute_value_independent_full_feature_predictions.npz",
    "reacher": REPORT_DIR / "compute_value_independent_full_feature_reacher_predictions.npz",
    "cube": REPORT_DIR / "compute_value_independent_full_feature_cube_predictions.npz",
}


def clean_float(value: float) -> float:
    out = float(value)
    if out == 0.0:
        return 0.0
    if not math.isfinite(out):
        raise ValueError(f"non-finite value: {out!r}")
    return out


def clean_json(value: Any) -> Any:
    if isinstance(value, dict):
        return {str(k): clean_json(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [clean_json(v) for v in value]
    if isinstance(value, np.ndarray):
        return clean_json(value.tolist())
    if isinstance(value, (np.integer,)):
        return int(value)
    if isinstance(value, (np.floating,)):
        return clean_float(float(value))
    if isinstance(value, float):
        return clean_float(value)
    return value


def load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {key: data[key] for key in data.files}


def ridge_fit(x: np.ndarray, y: np.ndarray, alpha: float) -> tuple[np.ndarray, np.ndarray]:
    x = np.asarray(x, dtype=np.float64)
    y = np.asarray(y, dtype=np.float64)
    x_aug = np.concatenate([x, np.ones((len(x), 1), dtype=np.float64)], axis=1)
    eye = np.eye(x_aug.shape[1], dtype=np.float64)
    eye[-1, -1] = 0.0
    w = np.linalg.solve(x_aug.T @ x_aug + alpha * eye, x_aug.T @ y)
    return w[:-1], w[-1]


def ridge_predict(x: np.ndarray, w: np.ndarray, b: np.ndarray) -> np.ndarray:
    return np.asarray(x, dtype=np.float64) @ w + b


def mse(y: np.ndarray, pred: np.ndarray) -> float:
    return clean_float(float(np.mean((np.asarray(y, dtype=np.float64) - np.asarray(pred, dtype=np.float64)) ** 2)))


def train_eval_split(n: int, seed: int) -> tuple[np.ndarray, np.ndarray]:
    rng = np.random.default_rng(seed)
    order = rng.permutation(n)
    cut = max(1, int(round(0.6 * n)))
    train = np.sort(order[:cut])
    eval_idx = np.sort(order[cut:])
    if len(eval_idx) == 0:
        eval_idx = train
    return train, eval_idx


def base_controls(arrays: dict[str, np.ndarray]) -> np.ndarray:
    depths = arrays["option_depths"].reshape(-1).astype(np.float64)
    option_error = arrays["option_error"].astype(np.float64)
    anchors = np.arange(option_error.shape[0], dtype=np.float64)
    t0 = arrays.get("t0", anchors).reshape(-1).astype(np.float64)
    if np.std(t0) > 1.0e-9:
        t0 = (t0 - float(np.mean(t0))) / float(np.std(t0))
    depth_centered = (depths - float(np.mean(depths))) / max(1.0e-9, float(np.std(depths)))
    rows = np.repeat(t0[:, None], len(depths), axis=0)
    depth_rows = np.tile(depth_centered[:, None], (option_error.shape[0], 1))
    bias_context = np.ones_like(rows)
    return np.concatenate([bias_context, rows, depth_rows], axis=1).astype(np.float64)


def episode_mean_score(arrays: dict[str, np.ndarray]) -> np.ndarray:
    episode = arrays["episode"].astype(np.int64)
    option_error = arrays["option_error"].astype(np.float64)
    score = np.zeros_like(option_error, dtype=np.float64)
    for ep in np.unique(episode):
        idx = np.where(episode == ep)[0]
        score[idx] = np.mean(option_error[idx], axis=0, keepdims=True)
    return score


def candidate_features(arrays: dict[str, np.ndarray], seed: int) -> dict[str, np.ndarray]:
    score = arrays["predicted_option_score"].astype(np.float64)
    true_mv = arrays.get("true_mv", np.zeros_like(score)).astype(np.float64)
    depths = arrays["option_depths"].reshape(-1).astype(np.float64)
    depth_only = np.repeat(depths[None, :], score.shape[0], axis=0)
    rng = np.random.default_rng(seed)
    shuffled = score.reshape(-1).copy()
    rng.shuffle(shuffled)
    return {
        "learned_option_score": score.reshape(-1, 1),
        "true_marginal_value": true_mv.reshape(-1, 1),
        "depth_only": depth_only.reshape(-1, 1),
        "episode_mean_oracle": episode_mean_score(arrays).reshape(-1, 1),
        "shuffled_learned_score": shuffled.reshape(-1, 1),
    }


def payload_from_arrays(arrays: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    return {
        "episode": arrays["episode"].astype(np.int64),
        "t0": arrays.get("t0", np.arange(len(arrays["episode"]))).astype(np.int64),
        "anchor_ep_t0": arrays.get("anchor_ep_t0", np.zeros((len(arrays["episode"]), 2), dtype=np.int64)).astype(np.int64),
        "option_error": arrays["option_error"].astype(np.float64),
        "uniform_error": arrays["uniform_error"].astype(np.float64),
        "true_mv": arrays.get("true_mv", np.zeros_like(arrays["option_error"], dtype=np.float64)).astype(np.float64),
    }


def allocation_delta(arrays: dict[str, np.ndarray], candidate: np.ndarray, *, seed: int) -> dict[str, Any]:
    payload = payload_from_arrays(arrays)
    score = np.asarray(candidate, dtype=np.float64).reshape(arrays["option_error"].shape)
    return structured.evaluate_scores(payload, score, seed=seed)["allocation_delta"]


def row(env: str, path: Path, *, seed: int) -> dict[str, Any]:
    if not path.exists():
        return {"status": "missing", "artifact": str(path)}
    arrays = load_npz(path)
    y = arrays["option_error"].astype(np.float64).reshape(-1, 1)
    x0 = base_controls(arrays)
    train, eval_idx = train_eval_split(len(y), seed)
    w0, b0 = ridge_fit(x0[train], y[train], alpha=1.0e-3)
    pred0 = ridge_predict(x0[eval_idx], w0, b0)
    base_loss = mse(y[eval_idx], pred0)
    candidates = candidate_features(arrays, seed + 17)
    survival: dict[str, Any] = {}
    for name, q in candidates.items():
        xq = np.concatenate([x0, q.astype(np.float64)], axis=1)
        wq, bq = ridge_fit(xq[train], y[train], alpha=1.0e-3)
        predq = ridge_predict(xq[eval_idx], wq, bq)
        q_loss = mse(y[eval_idx], predq)
        s = clean_float(base_loss - q_loss)
        alloc = allocation_delta(arrays, q.reshape(arrays["option_error"].shape), seed=seed + 31)
        survival[name] = {
            "option_error_base_mse": base_loss,
            "option_error_with_q_mse": q_loss,
            "option_error_survival": s,
            "option_error_relative_survival": clean_float(s / max(base_loss, 1.0e-12)),
            "allocation_delta": alloc,
            "allocation_closed": bool(float(alloc["high"]) < 0.0),
        }
    return {
        "status": "ok",
        "artifact": str(path),
        "anchors": int(arrays["option_error"].shape[0]),
        "episodes": int(len(np.unique(arrays["episode"]))),
        "base_controls": ["constant", "anchor_t0", "candidate_depth"],
        "readouts": ["option_error_mse", "exact_budget_allocation_delta"],
        "survival": survival,
    }


def summarize(rows: dict[str, Any]) -> dict[str, Any]:
    closed: dict[str, list[str]] = {}
    positive_survival: dict[str, list[str]] = {}
    for env, item in rows.items():
        if item.get("status") != "ok":
            continue
        for name, vals in item["survival"].items():
            if float(vals["option_error_survival"]) > 0.0:
                positive_survival.setdefault(name, []).append(env)
            if vals["allocation_closed"]:
                closed.setdefault(name, []).append(env)
    return {
        "positive_option_error_survival": positive_survival,
        "closed_allocation_delta": closed,
        "interpretation": (
            "A candidate survives a readout when it reduces held-out option-error MSE "
            "beyond base controls; allocation closure is reported separately because "
            "readability and budget-feasible intervention value can diverge."
        ),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# Compute-Value Survival Matrix",
        "",
        "Survival is held-out option-error MSE reduction after base controls.",
        "",
        "| env | candidate | survival | relative | allocation delta |",
        "|---|---|---:|---:|---:|",
    ]
    for env, item in report["rows"].items():
        if item.get("status") != "ok":
            lines.append(f"| `{env}` | missing | | | |")
            continue
        for name, vals in item["survival"].items():
            d = vals["allocation_delta"]
            lines.append(
                f"| `{env}` | `{name}` | {vals['option_error_survival']:.9g} "
                f"| {vals['option_error_relative_survival']:.9g} "
                f"| {d['observed']:.9g} [{d['low']:.9g}, {d['high']:.9g}] |"
            )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Compute a BEDC world-state survival matrix over compute-value artifacts")
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--seed", type=int, default=67)
    args = parser.parse_args()
    rows = {env: row(env, path, seed=int(args.seed) + i * 100) for i, (env, path) in enumerate(ARTIFACTS.items())}
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_survival_matrix",
        "definition": "S_q(r|Z)=J_0(r|Z)-J_q(r|Z,q), instantiated with held-out option-error MSE after base controls",
        "rows": rows,
        "summary": summarize(rows),
        "not_claimed": "This matrix audits candidate distinctions on existing artifacts; it is not a survival-regularized training result or a prediction-parity claim.",
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report["summary"]), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

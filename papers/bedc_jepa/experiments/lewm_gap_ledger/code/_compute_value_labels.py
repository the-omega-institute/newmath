from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_G2N_LABELS = REPORT_DIR / "g2n_labels_clean.npz"
ALT_G2N_LABELS = Path("C:/OMEGA/le-wm-survey/reports/g2n_labels_clean.npz")
DEFAULT_OUT = REPORT_DIR / "compute_value_labels.npz"
DEFAULT_JSON = REPORT_DIR / "compute_value_labels.json"
DEFAULT_MD = REPORT_DIR / "compute_value_labels.md"

LOW_H = 5
MID_H = 3
HIGH_H = 1
OPTION_DEPTHS = np.asarray([HIGH_H, MID_H, LOW_H], dtype=np.int64)
BOOTSTRAPS = 1000


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


def resolve_g2n_labels(path: Path) -> Path | None:
    candidates = [path, DEFAULT_G2N_LABELS, ALT_G2N_LABELS]
    for candidate in candidates:
        if candidate.exists():
            return candidate
    return None


def horizon_index(labels: dict[str, np.ndarray], h: int) -> int:
    horizons = [int(item) for item in labels["horizons"].reshape(-1)]
    if h not in horizons:
        raise RuntimeError(f"missing horizon {h} in {labels['horizons']}")
    return horizons.index(h)


def rankdata(values: np.ndarray) -> np.ndarray:
    order = np.argsort(values, kind="mergesort")
    ranks = np.empty(len(values), dtype=np.float64)
    sorted_values = values[order]
    i = 0
    while i < len(values):
        j = i + 1
        while j < len(values) and sorted_values[j] == sorted_values[i]:
            j += 1
        ranks[order[i:j]] = 0.5 * (i + j - 1)
        i = j
    return ranks


def spearman(x: np.ndarray, y: np.ndarray) -> float:
    if len(x) < 2:
        return 0.0
    rx = rankdata(np.asarray(x, dtype=np.float64))
    ry = rankdata(np.asarray(y, dtype=np.float64))
    rx = rx - float(rx.mean())
    ry = ry - float(ry.mean())
    denom = math.sqrt(float(np.dot(rx, rx)) * float(np.dot(ry, ry)))
    if denom <= 0:
        return 0.0
    return clean_float(float(np.dot(rx, ry) / denom))


def episode_groups(episode: np.ndarray) -> list[np.ndarray]:
    return [np.where(episode == ep)[0] for ep in np.unique(episode)]


def balanced_choice(episode: np.ndarray, score: np.ndarray) -> np.ndarray:
    chosen = np.full(len(episode), MID_H, dtype=np.int64)
    for idxs in episode_groups(episode):
        ordered = sorted((int(i) for i in idxs), key=lambda i: (float(score[i]), int(i)))
        n = len(ordered)
        half = n // 2
        chosen[np.asarray(ordered[:half], dtype=np.int64)] = HIGH_H
        chosen[np.asarray(ordered[n - half :], dtype=np.int64)] = LOW_H
        if n % 2:
            chosen[ordered[half]] = MID_H
        if int(chosen[np.asarray(ordered, dtype=np.int64)].sum()) != MID_H * n:
            raise RuntimeError("balanced choice budget mismatch")
    return chosen


def per_step_delta(
    episode: np.ndarray,
    option_error_by_depth: dict[int, np.ndarray],
    chosen_depth: np.ndarray,
    uniform_error: np.ndarray,
    *,
    seed: int,
) -> dict[str, float]:
    chosen_error = np.asarray(
        [option_error_by_depth[int(h)][i] for i, h in enumerate(chosen_depth)],
        dtype=np.float64,
    )
    chosen_steps = chosen_depth.astype(np.float64)
    uniform_steps = np.full(len(episode), MID_H, dtype=np.float64)
    groups = episode_groups(episode)
    selected_ep_error = np.asarray([float(np.sum(chosen_error[idx])) for idx in groups], dtype=np.float64)
    selected_ep_steps = np.asarray([float(np.sum(chosen_steps[idx])) for idx in groups], dtype=np.float64)
    uniform_ep_error = np.asarray([float(np.sum(uniform_error[idx])) for idx in groups], dtype=np.float64)
    uniform_ep_steps = np.asarray([float(np.sum(uniform_steps[idx])) for idx in groups], dtype=np.float64)
    observed = clean_float(float(selected_ep_error.sum() / selected_ep_steps.sum() - uniform_ep_error.sum() / uniform_ep_steps.sum()))
    rng = np.random.default_rng(seed)
    samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    for i in range(BOOTSTRAPS):
        pick = rng.integers(0, len(groups), size=len(groups))
        samples[i] = float(
            selected_ep_error[pick].sum() / selected_ep_steps[pick].sum()
            - uniform_ep_error[pick].sum() / uniform_ep_steps[pick].sum()
        )
    return {
        "observed": observed,
        "low": clean_float(float(np.percentile(samples, 2.5))),
        "high": clean_float(float(np.percentile(samples, 97.5))),
    }


def build_payload(labels: dict[str, np.ndarray], *, seed: int) -> tuple[dict[str, np.ndarray], dict[str, Any]]:
    h5_idx = horizon_index(labels, LOW_H)
    valid = labels["eval_valid"][:, h5_idx].astype(bool)
    anchors = labels["eval_anchor_ep_t0"][valid].astype(np.int64)
    err_at_h = labels["eval_err_at_h"][valid].astype(np.float64)
    if len(anchors) == 0:
        raise RuntimeError("no h=5-valid eval anchors")
    if len(np.unique(anchors[:, 0])) < 2:
        raise RuntimeError("episode bootstrap requires at least two eval episodes")

    option_error = np.zeros((len(anchors), len(OPTION_DEPTHS)), dtype=np.float64)
    option_error_by_depth: dict[int, np.ndarray] = {}
    for col, h in enumerate(OPTION_DEPTHS):
        err = np.sum(err_at_h[:, : int(h)], axis=1)
        option_error[:, col] = err
        option_error_by_depth[int(h)] = err

    uniform_error = option_error[:, int(np.where(OPTION_DEPTHS == MID_H)[0][0])].copy()
    true_mv = uniform_error[:, None] / float(MID_H) - option_error / OPTION_DEPTHS[None, :]
    low_col = int(np.where(OPTION_DEPTHS == HIGH_H)[0][0])
    high_col = int(np.where(OPTION_DEPTHS == LOW_H)[0][0])
    oracle_score = true_mv[:, high_col] - true_mv[:, low_col]
    oracle_depth = balanced_choice(anchors[:, 0].astype(np.int64), oracle_score)
    oracle_delta = per_step_delta(
        anchors[:, 0].astype(np.int64),
        option_error_by_depth,
        oracle_depth,
        uniform_error,
        seed=seed,
    )
    oracle_rho = spearman(oracle_score, true_mv[:, high_col] - true_mv[:, low_col])

    arrays = {
        "episode": anchors[:, 0].astype(np.int64),
        "t0": anchors[:, 1].astype(np.int64),
        "anchor_ep_t0": anchors.astype(np.int64),
        "option_depths": OPTION_DEPTHS.astype(np.int64),
        "option_steps": OPTION_DEPTHS.astype(np.float64),
        "uniform_steps": np.full(len(anchors), MID_H, dtype=np.float64),
        "option_error": option_error.astype(np.float64),
        "uniform_error": uniform_error.astype(np.float64),
        "true_mv": true_mv.astype(np.float64),
        "predicted_mv": true_mv.astype(np.float64),
        "oracle_depth": oracle_depth.astype(np.int64),
    }
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_labels",
        "source": "g2n_labels_clean.npz eval split",
        "label_semantics": {
            "option_b": "rollout depth in {1,3,5}",
            "option_error": "sum of per-step rollout latent MSE up to depth b",
            "uniform_error": "sum of per-step rollout latent MSE up to depth 3",
            "MV(t,b)": "uniform per-step error(t)-option per-step error(t,b)",
            "predicted_mv": "oracle readback placeholder derived from true per-step MV; training runs must replace it with model predictions",
        },
        "counts": {
            "anchors": int(len(anchors)),
            "episodes": int(len(np.unique(anchors[:, 0]))),
            "options": int(len(OPTION_DEPTHS)),
        },
        "option_depths": OPTION_DEPTHS.tolist(),
        "uniform_depth": MID_H,
        "oracle_readback": {
            "allocation_delta": oracle_delta,
            "mv_spearman": oracle_rho,
            "note": "upper-bound readback using true per-step MV as predicted_mv; not a model claim",
        },
        "cannot_claim": [
            "trained compute-value model",
            "planning benefit",
            "control benefit",
            "independent export generality",
        ],
    }
    return arrays, report


def fail_closed_report(reason: str, *, labels: Path, out: Path) -> dict[str, Any]:
    return {
        "status": "fail-closed",
        "reason": reason,
        "expected_input": str(labels),
        "fallback_inputs": [str(DEFAULT_G2N_LABELS), str(ALT_G2N_LABELS)],
        "expected_output": str(out),
        "required_generation_step": "run code/_g2n_horizon_labels.py to create g2n_labels_clean.npz, then rerun this script",
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    if report.get("status") != "ok":
        path.write_text(
            "# Compute-Value Labels\n\n"
            f"- status: `{report.get('status')}`\n"
            f"- reason: `{report.get('reason')}`\n"
            f"- expected input: `{report.get('expected_input')}`\n",
            encoding="utf-8",
        )
        return
    oracle = report["oracle_readback"]["allocation_delta"]
    path.write_text(
        "# Compute-Value Labels\n\n"
        f"- status: `{report['status']}`\n"
        f"- anchors: `{report['counts']['anchors']}`\n"
        f"- episodes: `{report['counts']['episodes']}`\n"
        f"- option depths: `{report['option_depths']}`\n"
        f"- uniform depth: `{report['uniform_depth']}`\n"
        f"- oracle readback allocation delta: `{oracle['observed']:.9g}` "
        f"`[{oracle['low']:.9g}, {oracle['high']:.9g}]`\n"
        f"- oracle readback MV Spearman: `{report['oracle_readback']['mv_spearman']:.9g}`\n\n"
        "The `predicted_mv` array is an oracle readback placeholder equal to true per-step MV. "
        "A trained compute-value model must replace it before any model claim is made.\n",
        encoding="utf-8",
    )


def main() -> int:
    parser = argparse.ArgumentParser(description="Build BEDC-JEPA compute-value label artifact")
    parser.add_argument("--g2n-labels", default=str(DEFAULT_G2N_LABELS))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    labels_path = Path(args.g2n_labels)
    out_path = Path(args.out)
    json_path = Path(args.json)
    md_path = Path(args.md)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    md_path.parent.mkdir(parents=True, exist_ok=True)

    resolved_labels = resolve_g2n_labels(labels_path)
    if resolved_labels is None:
        report = fail_closed_report("missing g2n horizon label artifact", labels=labels_path, out=out_path)
        json_path.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
        write_markdown(md_path, report)
        print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
        return 0

    arrays, report = build_payload(load_npz(resolved_labels), seed=int(args.seed))
    report["input"] = str(resolved_labels)
    np.savez_compressed(out_path, **arrays)
    report["outputs"] = {"npz": str(out_path), "json": str(json_path), "md": str(md_path)}
    json_path.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(md_path, report)
    print(json.dumps(clean_json(report["oracle_readback"]), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

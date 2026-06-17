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
DEFAULT_JSON = REPORT_DIR / "compute_value_independent_audit.json"
DEFAULT_MD = REPORT_DIR / "compute_value_independent_audit.md"
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


def payload_from_arrays(arrays: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    return {
        "episode": arrays["episode"].astype(np.int64),
        "t0": arrays.get("t0", np.arange(len(arrays["episode"]))).astype(np.int64),
        "anchor_ep_t0": arrays.get("anchor_ep_t0", np.zeros((len(arrays["episode"]), 2), dtype=np.int64)).astype(np.int64),
        "option_error": arrays["option_error"].astype(np.float64),
        "uniform_error": arrays["uniform_error"].astype(np.float64),
        "true_mv": arrays.get("true_mv", np.zeros_like(arrays["option_error"], dtype=np.float64)).astype(np.float64),
    }


def evaluate_named(payload: dict[str, np.ndarray], score: np.ndarray, *, seed: int) -> dict[str, Any]:
    return structured.evaluate_scores(payload, score.astype(np.float64), seed=seed)


def episode_mean_score(payload: dict[str, np.ndarray]) -> np.ndarray:
    score = np.zeros_like(payload["option_error"], dtype=np.float64)
    for ep in np.unique(payload["episode"]):
        idx = np.where(payload["episode"] == ep)[0]
        score[idx] = np.mean(payload["option_error"][idx], axis=0, keepdims=True)
    return score


def shuffled_score(score: np.ndarray, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    flat = score.reshape(-1).copy()
    rng.shuffle(flat)
    return flat.reshape(score.shape)


def row(name: str, path: Path, *, seed: int) -> dict[str, Any]:
    if not path.exists():
        return {"status": "missing", "artifact": str(path)}
    arrays = load_npz(path)
    payload = payload_from_arrays(arrays)
    learned = arrays["predicted_option_score"].astype(np.float64)
    depths = arrays["option_depths"].reshape(-1).astype(np.float64)
    depth_only = np.repeat(depths[None, :], len(payload["episode"]), axis=0)
    evals = {
        "learned": evaluate_named(payload, learned, seed=seed + 1),
        "exact_budget_oracle": structured.exact_oracle(payload, seed=seed + 2),
        "depth_only": evaluate_named(payload, depth_only, seed=seed + 3),
        "episode_mean_oracle": evaluate_named(payload, episode_mean_score(payload), seed=seed + 4),
        "shuffled_learned": evaluate_named(payload, shuffled_score(learned, seed + 5), seed=seed + 6),
    }
    return {
        "status": "ok",
        "artifact": str(path),
        "anchors": int(len(payload["episode"])),
        "episodes": int(len(np.unique(payload["episode"]))),
        "eval": evals,
    }


def verdict(rows: dict[str, Any]) -> dict[str, Any]:
    issues: list[str] = []
    pusht = rows.get("pusht", {})
    if pusht.get("status") == "ok":
        learned = pusht["eval"]["learned"]["allocation_delta"]
        depth = pusht["eval"]["depth_only"]["allocation_delta"]
        shuffled = pusht["eval"]["shuffled_learned"]["allocation_delta"]
        if float(depth["high"]) < 0.0:
            issues.append("pusht depth-only control is positive")
        if float(shuffled["high"]) < 0.0:
            issues.append("pusht shuffled-score control is positive")
        if not float(learned["high"]) < 0.0:
            issues.append("pusht learned row is not closed")
    closed_envs = []
    for env, item in rows.items():
        if item.get("status") != "ok":
            continue
        d = item["eval"]["learned"]["allocation_delta"]
        if float(d["high"]) < 0.0:
            closed_envs.append(env)
    return {
        "status": "needs-more" if issues else "sound-but-scoped",
        "issues": issues,
        "closed_environments": closed_envs,
        "scope": (
            "controls audit shortcut baselines for independent full-feature compute-value artifacts; "
            "it does not establish population-level control or selective-risk coverage"
        ),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# Compute-Value Independent Audit",
        "",
        f"- verdict: `{report['verdict']['status']}`",
        f"- closed environments: `{','.join(report['verdict']['closed_environments'])}`",
        "",
        "| environment | learned delta | depth-only delta | shuffled delta |",
        "|---|---:|---:|---:|",
    ]
    for env, item in report["rows"].items():
        if item.get("status") != "ok":
            lines.append(f"| `{env}` | missing | missing | missing |")
            continue
        learned = item["eval"]["learned"]["allocation_delta"]
        depth = item["eval"]["depth_only"]["allocation_delta"]
        shuffled = item["eval"]["shuffled_learned"]["allocation_delta"]
        lines.append(
            f"| `{env}` | {learned['observed']:.9g} [{learned['low']:.9g}, {learned['high']:.9g}] "
            f"| {depth['observed']:.9g} [{depth['low']:.9g}, {depth['high']:.9g}] "
            f"| {shuffled['observed']:.9g} [{shuffled['low']:.9g}, {shuffled['high']:.9g}] |"
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit independent full-feature compute-value shortcut controls")
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--seed", type=int, default=51)
    args = parser.parse_args()
    rows = {env: row(env, path, seed=int(args.seed) + i * 100) for i, (env, path) in enumerate(ARTIFACTS.items())}
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.compute_value_independent_audit",
        "rows": rows,
        "verdict": verdict(rows),
    }
    Path(args.json).parent.mkdir(parents=True, exist_ok=True)
    Path(args.json).write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report["verdict"]), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

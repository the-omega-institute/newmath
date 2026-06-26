from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
BASE_SCRIPT = ROOT / "_state_generation_episode_allocation.py"
DEFAULT_JSON = REPORT_DIR / "state_generation_episode_allocation_seeds.json"
DEFAULT_MD = REPORT_DIR / "state_generation_episode_allocation_seeds.md"


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


def run_seed(seed: int, args: argparse.Namespace) -> dict[str, Any]:
    stem = f"state_generation_episode_allocation_seed_{seed}"
    report_path = REPORT_DIR / f"{stem}.json"
    md_path = REPORT_DIR / f"{stem}.md"
    pred_path = REPORT_DIR / f"{stem}_predictions.npz"
    cmd = [
        sys.executable,
        str(BASE_SCRIPT),
        "--json",
        str(report_path),
        "--md",
        str(md_path),
        "--out",
        str(pred_path),
        "--seed",
        str(seed),
        "--epochs",
        str(args.epochs),
        "--hidden",
        str(args.hidden),
        "--depth",
        str(args.depth),
        "--batch",
        str(args.batch),
        "--lr",
        str(args.lr),
    ]
    subprocess.run(cmd, cwd=str(ROOT), check=True)
    report = json.loads(report_path.read_text(encoding="utf-8"))
    episode = report["eval"]["episode_allocation"]
    baseline = report["eval"]["allocation_native"]
    oracle = report["eval"]["oracle_true_error"]
    return {
        "seed": seed,
        "selected_epoch": int(report["selection"]["best"]["epoch"]),
        "episode": episode,
        "allocation_native": baseline,
        "oracle_true_error": oracle,
        "diagnosis": report["diagnosis"],
        "artifacts": {
            "json": str(report_path.relative_to(REPORT_DIR.parent)),
            "md": str(md_path.relative_to(REPORT_DIR.parent)),
            "predictions": str(pred_path.relative_to(REPORT_DIR.parent)),
        },
    }


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    ep_obs = np.array([row["episode"]["allocation_delta"]["observed"] for row in rows], dtype=np.float64)
    ep_high = np.array([row["episode"]["allocation_delta"]["high"] for row in rows], dtype=np.float64)
    base_obs = np.array([row["allocation_native"]["allocation_delta"]["observed"] for row in rows], dtype=np.float64)
    base_high = np.array([row["allocation_native"]["allocation_delta"]["high"] for row in rows], dtype=np.float64)
    oracle_high = np.array([row["oracle_true_error"]["allocation_delta"]["high"] for row in rows], dtype=np.float64)
    observed_beats = ep_obs < base_obs
    high_beats = ep_high < base_high
    closed = ep_high < 0.0
    oracle_closed = oracle_high < 0.0
    return {
        "seed_count": int(len(rows)),
        "episode_delta_observed_median": clean_float(float(np.median(ep_obs))),
        "episode_delta_observed_min": clean_float(float(np.min(ep_obs))),
        "episode_delta_observed_max": clean_float(float(np.max(ep_obs))),
        "episode_delta_high_median": clean_float(float(np.median(ep_high))),
        "baseline_delta_observed_median": clean_float(float(np.median(base_obs))),
        "baseline_delta_high_median": clean_float(float(np.median(base_high))),
        "observed_beats_baseline_count": int(np.sum(observed_beats)),
        "ci_high_beats_baseline_count": int(np.sum(high_beats)),
        "allocation_closed_count": int(np.sum(closed)),
        "oracle_closed_count": int(np.sum(oracle_closed)),
        "stable_movement": bool(
            float(np.median(ep_obs)) < 0.0
            and float(np.median(ep_high)) < float(np.median(base_high))
            and int(np.sum(observed_beats)) >= max(1, (len(rows) + 1) // 2)
            and int(np.sum(high_beats)) >= max(1, (len(rows) + 1) // 2)
            and int(np.sum(oracle_closed)) == len(rows)
        ),
        "allocation_closed": bool(int(np.sum(closed)) == len(rows)),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Episode Allocation Seeds",
        "",
        f"- seeds: `{report['config']['seeds']}`",
        f"- stable movement: `{report['summary']['stable_movement']}`",
        f"- allocation closed across seeds: `{report['summary']['allocation_closed']}`",
        "",
        "| seed | selected epoch | episode delta | baseline delta | oracle delta |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in report["seeds"]:
        ep = row["episode"]["allocation_delta"]
        base = row["allocation_native"]["allocation_delta"]
        oracle = row["oracle_true_error"]["allocation_delta"]
        lines.append(
            f"| {row['seed']} | {row['selected_epoch']} | "
            f"{ep['observed']:.6g} [{ep['low']:.6g}, {ep['high']:.6g}] | "
            f"{base['observed']:.6g} [{base['low']:.6g}, {base['high']:.6g}] | "
            f"{oracle['observed']:.6g} [{oracle['low']:.6g}, {oracle['high']:.6g}] |"
        )
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Replicate episode-level allocation objective across seeds")
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--seeds", nargs="+", type=int, default=[431, 509, 617])
    parser.add_argument("--epochs", type=int, default=180)
    parser.add_argument("--hidden", type=int, default=256)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--batch", type=int, default=128)
    parser.add_argument("--lr", type=float, default=4.0e-4)
    args = parser.parse_args()
    rows = [run_seed(int(seed), args) for seed in args.seeds]
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_episode_allocation_seeds",
        "config": {
            "seeds": [int(seed) for seed in args.seeds],
            "epochs": int(args.epochs),
            "hidden": int(args.hidden),
            "depth": int(args.depth),
            "batch": int(args.batch),
            "lr": float(args.lr),
        },
        "summary": summarize(rows),
        "seeds": rows,
        "leakage_attestation": {
            "features": "aligned export x only",
            "selection": "per-seed calibration exact-budget allocation_delta CI high, then observed delta",
            "slurm_or_ssh": "not used",
            "targets": "train option_error is converted to exact-budget oracle choices; eval option_error is used only after score generation for metrics",
        },
        "not_claimed": ["allocation closure", "deployable policy", "complete BEDC-native world model"],
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

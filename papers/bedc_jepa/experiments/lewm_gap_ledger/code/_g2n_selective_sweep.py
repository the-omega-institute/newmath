#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import numpy as np


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT.parent / "reports"
DEFAULT_SCORE_DUMP = REPORT_DIR / "g2n_integrated_a100_scores.npz"
DEFAULT_OUT = REPORT_DIR / "g2n_integrated_a100_selective_sweep.json"
TARGET_H = 5
TARGET_Q = 75
ALPHAS = (0.05, 0.10, 0.15, 0.20)


def clean_float(value: float) -> float:
    out = float(value)
    if out == 0.0:
        return 0.0
    if not math.isfinite(out):
        raise ValueError(f"non-finite JSON float: {out!r}")
    return out


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
        return clean_float(float(value))
    if isinstance(value, float):
        return clean_float(value)
    return value


def load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as raw:
        return {key: raw[key] for key in raw.files}


def conformal_threshold(score: np.ndarray, y: np.ndarray, alpha: float) -> float | None:
    finite = np.isfinite(score) & np.isfinite(y)
    score = score[finite].astype(np.float64)
    y = y[finite].astype(np.float64)
    if len(score) == 0:
        return None
    order = np.argsort(score, kind="mergesort")
    s_sorted = score[order]
    y_sorted = y[order]
    cum_fail = np.cumsum(y_sorted)
    n = np.arange(1, len(y_sorted) + 1, dtype=np.float64)
    conservative_risk = (1.0 + cum_fail) / (1.0 + n)
    ok = np.where(conservative_risk <= alpha)[0]
    if len(ok) == 0:
        return None
    return float(s_sorted[int(ok[-1])])


def selective_eval(score: np.ndarray, y: np.ndarray, threshold: float | None, alpha: float) -> dict[str, Any]:
    if threshold is None:
        return {
            "alpha": float(alpha),
            "tau": None,
            "risk": None,
            "coverage": 0.0,
            "risk_le_alpha": False,
            "admitted": 0,
            "n": int(len(score)),
        }
    keep = score <= threshold
    coverage = float(np.mean(keep)) if len(score) else 0.0
    risk = float(np.mean(y[keep])) if bool(keep.any()) else None
    return {
        "alpha": float(alpha),
        "tau": float(threshold),
        "risk": risk,
        "coverage": coverage,
        "risk_le_alpha": bool(risk is not None and risk <= alpha),
        "admitted": int(keep.sum()),
        "n": int(len(score)),
    }


def build_payload(args: argparse.Namespace) -> dict[str, Any]:
    score_path = Path(args.score_dump)
    if not score_path.exists():
        return {
            "status": "fail-closed",
            "reported_claim": f"fail-closed: missing G2N score dump: {score_path}; no selective calibration result is admitted.",
        }
    dump = load_npz(score_path)
    target_horizons = [int(x) for x in dump["target_horizons"].reshape(-1)]
    quantiles = [int(x) for x in dump["quantiles"].reshape(-1)]
    h_pos = target_horizons.index(int(args.horizon))
    q_pos = quantiles.index(int(args.quantile))

    cal_valid = dump["calibration_valid_target"][:, h_pos].astype(bool)
    eval_valid = dump["eval_valid_target"][:, h_pos].astype(bool)
    cal_score = dump["calibration_admission"][cal_valid].astype(np.float64)
    eval_score = dump["eval_admission"][eval_valid].astype(np.float64)
    cal_y = dump["calibration_y_target"][cal_valid, h_pos, q_pos].astype(np.float64)
    eval_y = dump["eval_y_target"][eval_valid, h_pos, q_pos].astype(np.float64)
    eval_ood = dump["eval_ood_distance"][eval_valid].astype(np.float64)
    ood_threshold = float(dump["ood_distance_threshold"].reshape(-1)[0])

    rows = []
    for alpha in ALPHAS:
        tau = conformal_threshold(cal_score, cal_y, float(alpha))
        row = selective_eval(eval_score, eval_y, tau, float(alpha))
        if tau is not None:
            keep = eval_score <= tau
            severe = eval_ood > ood_threshold
            row["ood_ok_rate"] = float(np.mean(keep[severe])) if bool(severe.any()) else None
            row["ood_n"] = int(severe.sum())
        else:
            row["ood_ok_rate"] = 0.0
            row["ood_n"] = int(np.sum(eval_ood > ood_threshold))
        rows.append(row)

    passing = [r for r in rows if bool(r.get("risk_le_alpha", False))]
    if passing:
        best = max(passing, key=lambda r: float(r.get("coverage", 0.0)))
        status = "positive"
        claim = (
            f"selective calibration admits a risk-controlled row for h{int(args.horizon)} q{int(args.quantile)}: "
            f"alpha={float(best['alpha']):.2f}, risk={float(best['risk']):.9g}, "
            f"coverage={float(best['coverage']):.9g}, admitted={int(best['admitted'])}/{int(best['n'])}."
        )
    else:
        status = "fail-closed"
        claim = (
            f"selective calibration sweep for h{int(args.horizon)} q{int(args.quantile)} has no row with eval risk <= alpha; "
            "the claim gate remains bounded under this score dump."
        )
    return {
        "status": status,
        "target": {"horizon": int(args.horizon), "quantile": int(args.quantile)},
        "rows": rows,
        "reported_claim": claim,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--score-dump", default=str(DEFAULT_SCORE_DUMP))
    parser.add_argument("--out", default=str(DEFAULT_OUT))
    parser.add_argument("--horizon", type=int, default=TARGET_H)
    parser.add_argument("--quantile", type=int, default=TARGET_Q)
    args = parser.parse_args()
    payload = clean_json(build_payload(args))
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, ensure_ascii=False, sort_keys=False, separators=(",", ":")) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

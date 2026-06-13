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
os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")

import numpy as np


SCRIPT_PATH = Path(__file__).resolve()
ROOT = SCRIPT_PATH.parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from _phase1c_gap_ledger import auroc_rank  # noqa: E402

native_phase2a_stub = types.ModuleType("_phase2a_brittleness_gap")
native_phase2a_stub.BOOTSTRAPS = 500
native_phase2a_stub.clean_json = lambda value: value
native_phase2a_stub.fit_clean_protocol = lambda *args, **kwargs: None
native_phase2a_stub.perturbation_grid = lambda: {}
sys.modules.setdefault("_phase2a_brittleness_gap", native_phase2a_stub)

native_phase2c_stub = types.ModuleType("_phase2c_ood_aware_gap")
native_phase2c_stub.cache_path = lambda *args, **kwargs: ROOT / "missing.npz"
native_phase2c_stub.fit_gap_head_for_parts = lambda *args, **kwargs: None
native_phase2c_stub.load_part_cache = lambda *args, **kwargs: None
native_phase2c_stub.materialize_clean_split = lambda *args, **kwargs: None
sys.modules.setdefault("_phase2c_ood_aware_gap", native_phase2c_stub)

native_label_stub = types.ModuleType("_g2n_horizon_labels")
native_label_stub.load_perturbed_emb = lambda *args, **kwargs: None
sys.modules.setdefault("_g2n_horizon_labels", native_label_stub)

rollout_stub = types.ModuleType("_ledger_gated_rollout")
rollout_stub.HIGH_H = 5
rollout_stub.LOW_H = 1
rollout_stub.MID_H = 3
rollout_stub.ROLLOUT_BOOTSTRAP_SEED = 0
rollout_stub.UNIFORM_H = 3
rollout_stub.allocation_by_score = lambda *args, **kwargs: {}
rollout_stub.allocation_uniform = lambda *args, **kwargs: {}
rollout_stub.paired_bootstrap_delta = lambda *args, **kwargs: {}
rollout_stub.summarize_allocation = lambda *args, **kwargs: {}
sys.modules.setdefault("_ledger_gated_rollout", rollout_stub)

from _g2n_native_ledger import (  # noqa: E402
    HORIZONS,
    Q_TO_IDX,
    build_clean_examples,
    output_col,
    predict_logits,
    sigmoid_np,
    train_arm,
)


HYPOTHESIS_ID = "fi-015.native-selective-risk-control"
NPZ_PATH = ROOT / "tworooms_latent_large.npz"
CLEAN_LABELS = ROOT / "reports" / "g2n_labels_clean.npz"
HORIZON_LABEL_REPORT = ROOT / "reports" / "g2n_horizon_labels.json"
ALPHA = 0.10
CALIBRATION_ALPHA = 0.07
CALIBRATION_COVERAGE_CAP = 60
TARGET_H = 5
PRIMARY_Q = 75
SPLIT_SEED = 1701
BOOTSTRAPS = 500
BOOTSTRAP_SEED_OFFSET = 314159
ANCHOR_TOL = 1e-4


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
    """Import the conformal helpers without importing unrelated report builders."""
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
    if HORIZON_LABEL_REPORT.exists():
        report = json.loads(HORIZON_LABEL_REPORT.read_text(encoding="utf-8"))
        checks = report.get("anchor_checks", {})
        tolerance = float(checks.get("tolerance", ANCHOR_TOL))
        delta = float(checks.get("clean_h1_prediction_mse_max_abs_delta", float("inf")))
        if report.get("status") == "ok" and math.isfinite(delta) and delta < tolerance:
            return 0.0
    tm = data["transition_mask"].astype(bool)
    if not np.any(tm):
        return 0.0
    pred = data["pred"].astype(np.float64)
    target = data["transition_target_emb"].astype(np.float64)
    direct = np.mean((pred - target) ** 2, axis=-1)
    stored = data["prediction_mse"].astype(np.float64)
    return clean_float(float(np.max(np.abs(direct[tm] - stored[tm]))))


def validate_label_splits(data: dict[str, np.ndarray], clean: np.lib.npyio.NpzFile) -> bool:
    rng = np.random.default_rng(SPLIT_SEED)
    perm = rng.permutation(int(data["emb"].shape[0]))
    n_train = int(round(0.60 * len(perm)))
    n_cal = int(round(0.20 * len(perm)))
    expected = {
        "train": set(int(v) for v in perm[:n_train]),
        "calibration": set(int(v) for v in perm[n_train : n_train + n_cal]),
        "eval": set(int(v) for v in perm[n_train + n_cal :]),
    }
    observed = {
        split: set(int(v) for v in clean[f"{split}_anchor_ep_t0"][:, 0])
        for split in ("train", "calibration", "eval")
    }
    return all(observed[k].issubset(expected[k]) for k in expected) and not (
        observed["train"] & observed["calibration"]
        or observed["train"] & observed["eval"]
        or observed["calibration"] & observed["eval"]
    )


def slice_hq(ex: dict[str, np.ndarray], prob: np.ndarray) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    h_i = HORIZONS.index(TARGET_H)
    q_i = Q_TO_IDX[PRIMARY_Q]
    mask = ex["valid"][:, h_i, q_i].astype(bool)
    score = prob[mask, output_col(TARGET_H, PRIMARY_Q)].astype(np.float64)
    y = ex["y"][mask, h_i, q_i].astype(np.int8)
    episode = ex["episode"][mask].astype(np.int64)
    return score, y, episode, mask


def margin_from_selective_eval(result: dict[str, Any], alpha: float) -> float:
    risk = result.get("realized_p_fail_given_ok")
    if risk is None:
        return -float(alpha)
    return clean_float(float(alpha) - float(risk))


def conservative_capped_calibration(
    score: np.ndarray,
    y: np.ndarray,
    alpha: float,
    coverage_cap: int,
    calibrate_threshold: Callable[..., dict[str, Any]],
) -> dict[str, Any]:
    base = calibrate_threshold(score, y, alpha)
    if base.get("status") != "ok":
        return base

    score = np.asarray(score, dtype=np.float64)
    y = np.asarray(y, dtype=np.int8)
    order = np.argsort(score, kind="mergesort")
    s_sorted = score[order]
    y_sorted = y[order]
    cum_fail = np.cumsum(y_sorted, dtype=np.int64)
    n = np.arange(1, len(y_sorted) + 1, dtype=np.int64)
    conservative_risk = (1.0 + cum_fail) / (1.0 + n)
    feasible = (s_sorted <= float(base["threshold"])) & (n <= int(coverage_cap)) & (conservative_risk <= alpha)
    if not np.any(feasible):
        return base
    idx = int(np.flatnonzero(feasible)[-1])
    out = dict(base)
    out.update(
        {
            "threshold": float(s_sorted[idx]),
            "covered_calibration_rows": int(n[idx]),
            "calibration_failures_covered": int(cum_fail[idx]),
            "conservative_calibration_risk": float(conservative_risk[idx]),
            "base_threshold": float(base["threshold"]),
            "base_covered_calibration_rows": int(base["covered_calibration_rows"]),
            "coverage_cap": int(coverage_cap),
            "shrink_rule": "largest calibration prefix within base conformal threshold, coverage cap, and conservative risk alpha",
        }
    )
    return out


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


def uer(score: np.ndarray, y: np.ndarray) -> float:
    return clean_float(float(np.mean((y > 0) & (score < 0.5)))) if len(y) else 0.0


def final_status(ci_low: float, ci_high: float, fail_closed: bool) -> str | None:
    if fail_closed:
        return "fail-closed"
    if ci_low > 0.0:
        return None
    if ci_high <= 0.0:
        return None
    return "fail-closed"


def make_claim(
    realized_risk: float | None,
    margin: float,
    ci_low: float,
    ci_high: float,
    coverage: float | None,
    auroc: float,
    uer_value: float,
    calibration: dict[str, Any],
    status: str | None,
) -> str:
    risk_text = "NA" if realized_risk is None else f"{realized_risk:.12g}"
    cov_text = "NA" if coverage is None else f"{coverage:.12g}"
    tau_text = "NA" if calibration.get("threshold") is None else f"{float(calibration['threshold']):.12g}"
    if status == "fail-closed":
        verdict = "CI跨0或无admitted，未稳健拿下selective tier"
    elif ci_low > 0.0:
        verdict = "CI low>0，held-out eval稳健低于alpha=0.10"
    else:
        verdict = "held-out eval未给出严格正margin"
    return (
        f"native horizon-ledger arm F h5_q75 score，split-conformal用alpha'=0.07且cal cap=60校准tau={tau_text}；"
        f"eval realized risk={risk_text}, risk_margin={margin:.12g}, "
        f"episode-bootstrap CI=[{ci_low:.12g},{ci_high:.12g}], coverage={cov_text}, "
        f"auroc={auroc:.12g}, uer={uer_value:.12g}；{verdict}。"
        f"vs fi-005边际结果(0.092 risk且CI跨0)，本次按CI low>0判定。"
    )


def fail_closed_payload(anchor_value: float, reason: str) -> dict[str, Any]:
    return {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": clean_float(anchor_value)},
        "metric": "risk_margin",
        "metric_value": 0.0,
        "ci": {"low": 0.0, "high": 0.0},
        "status": "fail-closed",
        "measured_scope": ["risk_margin", "uer", "auroc"],
        "reported_claim": f"alpha=0.10下 realized risk 与 risk_margin 不可识别；{reason}。",
    }


def measure(seed: int) -> dict[str, Any]:
    set_determinism(seed)
    calibrate_threshold, evaluate_selective = load_conformal_functions()
    data = load_npz(NPZ_PATH)
    anchor_value = identity_anchor(data)
    if abs(anchor_value) > ANCHOR_TOL:
        return fail_closed_payload(anchor_value, "identity anchor未通过")
    if not CLEAN_LABELS.exists():
        return fail_closed_payload(anchor_value, f"missing clean label cache: {CLEAN_LABELS}")

    with np.load(CLEAN_LABELS, allow_pickle=False) as clean:
        if not validate_label_splits(data, clean):
            return fail_closed_payload(anchor_value, "cached train/calibration/eval episode split不互斥或不匹配")
        train_ex = build_clean_examples(data, clean, "train", None)
        cal_ex = build_clean_examples(data, clean, "calibration", None)
        eval_ex = build_clean_examples(data, clean, "eval", None)

    model, _info, norm = train_arm(
        "F",
        train_ex,
        include_future=True,
        action_only=False,
        use_teacher=True,
        use_unlogged=True,
        use_budget=True,
        label_permutation_seed=None,
    )
    cal_score, y_cal, _ep_cal, _m_cal = slice_hq(cal_ex, sigmoid_np(predict_logits(model, cal_ex, norm)))
    eval_score, y_eval, ep_eval, _m_eval = slice_hq(eval_ex, sigmoid_np(predict_logits(model, eval_ex, norm)))

    single_class = bool(np.unique(y_cal).size < 2 or np.unique(y_eval).size < 2)
    calibration = conservative_capped_calibration(
        cal_score,
        y_cal,
        CALIBRATION_ALPHA,
        CALIBRATION_COVERAGE_CAP,
        calibrate_threshold,
    )
    tau = calibration["threshold"] if calibration.get("status") == "ok" else None
    eval_result = evaluate_selective(eval_score, y_eval, tau, ALPHA)
    margin = margin_from_selective_eval(eval_result, ALPHA)
    ci_low, ci_high = bootstrap_margin_ci(
        eval_score,
        y_eval,
        ep_eval,
        tau,
        ALPHA,
        evaluate_selective,
        seed + BOOTSTRAP_SEED_OFFSET,
    )
    fail_closed = bool(single_class or tau is None or eval_result.get("realized_p_fail_given_ok") is None)
    status = final_status(ci_low, ci_high, fail_closed)
    realized_risk = eval_result.get("realized_p_fail_given_ok")
    coverage = eval_result.get("ok_rate")
    auroc = clean_float(float(auroc_rank(y_eval, eval_score)))
    uer_value = uer(eval_score, y_eval)

    payload: dict[str, Any] = {
        "hypothesis_id": HYPOTHESIS_ID,
        "anchor": {"field": "anchor.identity_max_abs", "value": clean_float(anchor_value)},
        "metric": "risk_margin",
        "metric_value": clean_float(margin),
        "ci": {"low": ci_low, "high": ci_high},
    }
    if status == "fail-closed":
        payload["status"] = "fail-closed"
    payload["measured_scope"] = ["risk_margin", "uer", "auroc"]
    payload["reported_claim"] = make_claim(
        None if realized_risk is None else float(realized_risk),
        margin,
        ci_low,
        ci_high,
        None if coverage is None else float(coverage),
        auroc,
        uer_value,
        calibration,
        status,
    )
    claim = payload["reported_claim"]
    if "real_robot_transfer" in claim or "paper_claim_strength" in claim:
        raise RuntimeError("reported_claim contains forbidden literal")
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

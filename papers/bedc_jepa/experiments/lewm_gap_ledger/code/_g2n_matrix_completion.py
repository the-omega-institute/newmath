from __future__ import annotations

import json
import os
from collections import defaultdict
from pathlib import Path
from typing import Any

import numpy as np
import torch

import _g2n_addendum as addendum
import _g2n_horizon_labels as horizon
import _g2n_native_ledger as native
from _lat_lewm_port import NPZ_PATH, REPORT_DIR, split_episodes
from _phase1c_gap_ledger import auroc_rank, flatten_transition_rows, fit_logistic_head, predict_logistic_head
from _phase2a_brittleness_gap import clean_json, fit_clean_protocol
from _phase2c_ood_aware_gap import fit_gap_head_for_parts, materialize_clean_split


ROOT = Path(__file__).resolve().parent
JSON_PATH = REPORT_DIR / "g2n_matrix_completion.json"
MD_PATH = REPORT_DIR / "g2n_matrix_completion.md"
PERT_TRAIN_LABELS = REPORT_DIR / "g2n_labels_perturbed_train.npz"
PERT_PREDZ = REPORT_DIR / "g2n_labels_perturbed_predz.npz"
OOD_EMB_CACHE_DIR = REPORT_DIR / "lat_ood_emb_cache"

EXPECTED_E_H1_AUROC = 0.7385152058598745
ANCHOR_TOL_STRICT = 1e-9
PERT_TRAIN_H1_TOL = 1e-6
POSTHOC_STEPS = 500
POSTHOC_LR = 0.14
POSTHOC_L2 = 1e-4
H_RANK_PERMUTATION_SEED = 90210


def require_inputs() -> None:
    required = [
        REPORT_DIR / "g2n_labels_clean.npz",
        REPORT_DIR / "g2n_labels_perturbed.npz",
        PERT_PREDZ,
        REPORT_DIR / "g2n_native_ledger.json",
        REPORT_DIR / "g2n_addendum.json",
        ROOT / "_g2n_native_ledger.py",
        ROOT / "_g2n_addendum.py",
        OOD_EMB_CACHE_DIR,
    ]
    missing = [p for p in required if not p.exists()]
    if missing:
        raise SystemExit("missing required precursor(s): " + ", ".join(str(p) for p in missing))
    train = sorted(OOD_EMB_CACHE_DIR.glob("train_*.npz"))
    mse_train = sorted(OOD_EMB_CACHE_DIR.glob("mse_train_*.npz"))
    if len(train) != 20 or len(mse_train) != 20:
        raise SystemExit(
            f"expected 20 train_*.npz and 20 mse_train_*.npz under {OOD_EMB_CACHE_DIR}; "
            f"got {len(train)} and {len(mse_train)}"
        )


def load_data() -> dict[str, np.ndarray]:
    raw = np.load(NPZ_PATH)
    return {k: raw[k] for k in raw.files}


def metric_observed(y: np.ndarray, prob: np.ndarray) -> dict[str, float]:
    return {
        "failure_detection_auroc": float(auroc_rank(y.astype(np.int8), prob.astype(np.float64))),
        "unlogged_error_rate": float(np.mean((y > 0) & (prob < 0.5))) if len(y) else float("nan"),
        "declared_gap_rate": float(np.mean(prob >= 0.5)) if len(y) else float("nan"),
        "failure_rate": float(np.mean(y)) if len(y) else float("nan"),
        "positive_count": int(np.sum(y > 0)),
        "negative_count": int(np.sum(y <= 0)),
    }


def bootstrap_binary_metrics(
    y: np.ndarray,
    prob: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
    n_boot: int = native.BOOTSTRAPS,
) -> dict[str, dict[str, float]]:
    observed = metric_observed(y, prob)
    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    rng = np.random.default_rng(seed)
    values: dict[str, list[float]] = {k: [] for k in observed}
    for _ in range(n_boot):
        sampled = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[i] for i in sampled])
        m = metric_observed(y[idx], prob[idx])
        for k, v in m.items():
            values[k].append(v)
    out: dict[str, dict[str, float]] = {}
    for k, obs in observed.items():
        arr = np.asarray(values[k], dtype=np.float64)
        out[k] = {
            "observed": float(obs),
            "bootstrap_mean": float(np.nanmean(arr)),
            "ci95_low": float(np.nanpercentile(arr, 2.5)),
            "ci95_high": float(np.nanpercentile(arr, 97.5)),
        }
    return out


def row_x_by_anchor(
    part: dict[str, Any],
    clean: np.lib.npyio.NpzFile,
    rows: dict[str, np.ndarray],
    split: str,
    h: int,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    row_to_x = {int(row_idx): part["x"][i] for i, row_idx in enumerate(part["row_idx"])}
    pair_row = native.pair_to_row_index(rows)
    anchors = clean[f"{split}_anchor_ep_t0"].astype(np.int64)
    h_idx = native.H_TO_LABEL_IDX[h]
    q_idx = native.Q_TO_IDX[75]
    valid = clean[f"{split}_valid"][:, h_idx].astype(bool)
    xs: list[np.ndarray] = []
    ys: list[int] = []
    eps: list[int] = []
    for i, (ep_raw, t_raw) in enumerate(anchors):
        if not valid[i]:
            continue
        row_idx = pair_row[(int(ep_raw), int(t_raw))]
        if row_idx not in row_to_x:
            raise RuntimeError(f"phase2c clean feature row missing for split={split}, row_idx={row_idx}")
        xs.append(row_to_x[row_idx])
        ys.append(int(clean[f"{split}_y"][i, h_idx, q_idx]))
        eps.append(int(ep_raw))
    return np.asarray(xs, dtype=np.float64), np.asarray(ys, dtype=np.int8), np.asarray(eps, dtype=np.int64)


def run_b_posthoc_horizon(
    data: dict[str, np.ndarray],
    rows: dict[str, np.ndarray],
    clean: np.lib.npyio.NpzFile,
    phase2c_report: dict[str, Any],
) -> dict[str, Any]:
    print("[B] rebuilding phase2c clean-only T1 anchor", flush=True)
    protocol = fit_clean_protocol(data, rows)
    train_clean = materialize_clean_split(protocol, rows, "train")
    eval_clean = materialize_clean_split(protocol, rows, "eval")
    clean_head, clean_fit = fit_gap_head_for_parts([train_clean])
    p_eval, _ = predict_logistic_head(clean_head, eval_clean["x"])
    observed = float(auroc_rank(eval_clean["y"], p_eval))
    target = float(phase2c_report["arms"]["clean_only"]["clean_eval"]["observed"]["failure_detection_auroc"])
    delta = abs(observed - target)
    if delta > ANCHOR_TOL_STRICT:
        raise SystemExit(f"B T1 anchor failed: observed={observed:.17g}, target={target:.17g}")

    by_h: dict[str, Any] = {}
    for h in native.HORIZONS:
        print(f"[B] posthoc horizon h={h}", flush=True)
        x_train, y_train, ep_train = row_x_by_anchor(train_clean, clean, rows, "train", h)
        x_eval, y_eval, ep_eval = row_x_by_anchor(eval_clean, clean, rows, "eval", h)
        head, fit_info = fit_logistic_head(x_train, y_train, steps=POSTHOC_STEPS, lr=POSTHOC_LR, l2=POSTHOC_L2)
        prob, _ = predict_logistic_head(head, x_eval)
        metrics = bootstrap_binary_metrics(
            y_eval,
            prob,
            ep_eval,
            seed=native.BOOTSTRAP_SEED + 1000 + h,
            n_boot=native.BOOTSTRAPS,
        )
        by_h[f"h{h}_q75"] = {
            "train_rows": int(len(y_train)),
            "train_episodes": int(len(np.unique(ep_train))),
            "eval_rows": int(len(y_eval)),
            "eval_episodes": int(len(np.unique(ep_eval))),
            "fit": fit_info,
            "metrics_eval_episode_bootstrap": metrics,
        }

    return {
        "status": "ok",
        "protocol": {
            "feature_source": "_phase2c_ood_aware_gap.materialize_clean_split x",
            "labels": "reports/g2n_labels_clean.npz h in {1,3,5,10}, q=75, aligned by (ep,t0), t0>=2 anchors",
            "head": f"_phase1c_gap_ledger.fit_logistic_head steps={POSTHOC_STEPS}, lr={POSTHOC_LR}, l2={POSTHOC_L2}",
        },
        "anchors": {
            "phase2c_clean_only_t1_auroc": {
                "observed": observed,
                "target": target,
                "abs_delta": delta,
                "tolerance": ANCHOR_TOL_STRICT,
                "fit": clean_fit,
            }
        },
        "horizons": by_h,
        "not_claimed": ["information-only post-hoc cell; no positive/negative criterion was predeclared"],
    }


def budget_allocation_from_logits(
    clean: np.lib.npyio.NpzFile,
    clean_eval_ex: dict[str, np.ndarray],
    logits: np.ndarray,
    name: str,
) -> dict[str, Any]:
    anchors, errors_h5 = native.build_budget_anchors(clean_eval_ex, clean)
    anchors_by_ep: dict[int, list[int]] = defaultdict(list)
    for i, anchor in enumerate(anchors):
        anchors_by_ep[int(anchor["episode"])].append(i)
    uniform_h = native.allocation_uniform(anchors_by_ep)
    uniform_alloc = native.summarize_allocation("uniform", uniform_h, errors_h5, anchors)
    valid_h5 = clean["eval_valid"][:, native.H_TO_LABEL_IDX[5]].astype(bool)
    score = logits[valid_h5, native.output_col(5, 75)]
    alloc = native.budget_eval_for_score(name, score, anchors, anchors_by_ep, errors_h5, uniform_alloc)
    oracle_score = np.mean(errors_h5, axis=1)
    oracle_alloc = native.budget_eval_for_score("oracle", oracle_score, anchors, anchors_by_ep, errors_h5, uniform_alloc)
    return {
        "uniform": {"allocation": uniform_alloc},
        name: alloc,
        "oracle": oracle_alloc,
        "oracle_minus_uniform_per_step_mse": float(
            oracle_alloc["allocation"]["per_emitted_step_mse"] - uniform_alloc["per_emitted_step_mse"]
        ),
    }


def run_e_rank(
    clean: np.lib.npyio.NpzFile,
    context: dict[str, Any],
    main_report: dict[str, Any],
) -> dict[str, Any]:
    print("[E_rank] reproducing pure E anchor", flush=True)
    e_cfg = dict(
        include_future=True,
        action_only=False,
        use_teacher=False,
        use_unlogged=False,
        use_budget=False,
        label_permutation_seed=None,
    )
    e_model, e_info, e_norm = native.train_arm("E", context["clean_train_ex"], **e_cfg)
    e_logits = native.predict_logits(e_model, context["clean_eval_ex"], e_norm)
    e_clean = native.evaluate_clean(e_logits, context["clean_eval_ex"])
    e_observed = float(e_clean["h1_q75"]["failure_detection_auroc"]["observed"])
    e_main = float(main_report["arms"]["E"]["clean_eval"]["h1_q75"]["failure_detection_auroc"]["observed"])
    e_delta_expected = abs(e_observed - EXPECTED_E_H1_AUROC)
    e_delta_main = abs(e_observed - e_main)
    if e_delta_expected > ANCHOR_TOL_STRICT or e_delta_main > ANCHOR_TOL_STRICT:
        raise SystemExit(
            "E anchor failed: "
            f"observed={e_observed:.17g}, expected={EXPECTED_E_H1_AUROC:.17g}, main={e_main:.17g}"
        )

    rank_cfg = dict(e_cfg)
    rank_cfg["use_budget"] = True
    print("[E_rank] training E + budget rank", flush=True)
    er_model, er_info, er_norm = native.train_arm("E_rank", context["clean_train_ex"], **rank_cfg)
    er_logits = native.predict_logits(er_model, context["clean_eval_ex"], er_norm)
    er_clean = native.evaluate_clean(er_logits, context["clean_eval_ex"])
    er_budget = budget_allocation_from_logits(clean, context["clean_eval_ex"], er_logits, "E_rank")
    er_delta = er_budget["E_rank"]["delta_vs_uniform"]
    er_verdict = "positive" if er_delta["ci95_high"] < 0.0 else "negative"

    h_cfg = dict(rank_cfg)
    h_cfg["label_permutation_seed"] = H_RANK_PERMUTATION_SEED
    print("[E_rank] training H_rank permutation control", flush=True)
    hr_model, hr_info, hr_norm = native.train_arm("H_rank", context["clean_train_ex"], **h_cfg)
    hr_logits = native.predict_logits(hr_model, context["clean_eval_ex"], hr_norm)
    hr_clean = native.evaluate_clean(hr_logits, context["clean_eval_ex"])
    hr_budget = budget_allocation_from_logits(clean, context["clean_eval_ex"], hr_logits, "H_rank")

    return {
        "status": "ok",
        "protocol": {
            "base_arm": "E: include_future=True, action_only=False, no teacher, no unlogged, clean train only",
            "rank_loss": "L_budget lambda=0.5, in-batch same-episode pairwise logistic ranking on h=5,q=75 logit with target mean_err_to_h[:,5]",
            "allocation": "same as _ledger_gated_rollout: clean eval h=5 anchors, per-episode 5/1 split, h=3 uniform, same budget",
            "positive_rule": "positive iff paired episode-bootstrap CI for delta=E_rank-uniform is entirely < 0",
        },
        "anchors": {
            "pure_E_h1_q75_auroc": {
                "observed": e_observed,
                "expected": EXPECTED_E_H1_AUROC,
                "main_report_observed": e_main,
                "abs_delta_vs_expected": e_delta_expected,
                "abs_delta_vs_main_report": e_delta_main,
                "tolerance": ANCHOR_TOL_STRICT,
            }
        },
        "pure_E": {"info": e_info, "clean_eval": e_clean},
        "E_rank": {
            "info": er_info,
            "clean_eval": er_clean,
            "budget_allocation": er_budget,
            "delta_E_rank_minus_uniform": er_delta,
            "verdict": er_verdict,
        },
        "H_rank": {
            "info": hr_info,
            "clean_eval": hr_clean,
            "budget_allocation": hr_budget,
            "delta_H_rank_minus_uniform": hr_budget["H_rank"]["delta_vs_uniform"],
        },
        "oracle_ceiling": {
            "source": "same allocation protocol recomputed in this script",
            "oracle_minus_uniform_per_step_mse": er_budget["oracle_minus_uniform_per_step_mse"],
            "native_report_oracle_minus_uniform_per_step_mse": float(
                main_report["budget_allocation"]["oracle"]["delta_vs_uniform"]["observed"]
            ),
        },
        "not_claimed": ["budget allocation is prediction budget only; no planning/control benefit is claimed"],
    }


def discover_train_slices() -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for path in sorted(OOD_EMB_CACHE_DIR.glob("train_*.npz")):
        key = path.stem[len("train_") :]
        family, token = key.rsplit("_", 1)
        mse_path = OOD_EMB_CACHE_DIR / f"mse_train_{key}.npz"
        if not mse_path.exists():
            raise RuntimeError(f"missing train h=1 mse cache for {path.name}: {mse_path.name}")
        out.append(
            {
                "key": key,
                "family": family,
                "strength_token": token,
                "strength": horizon.strength_from_token(token),
                "emb_path": path,
                "mse_path": mse_path,
            }
        )
    if len(out) != 20:
        raise RuntimeError(f"expected 20 train perturb slices, got {len(out)}")
    return out


def generate_perturbed_train_labels(
    data: dict[str, np.ndarray],
    rows: dict[str, np.ndarray],
    clean: np.lib.npyio.NpzFile,
) -> dict[str, Any]:
    print("[G_oodh] generating perturbed train horizon labels", flush=True)
    device = torch.device("cpu")
    model, config, checkpoint_path, config_path, loader_source = horizon.load_predictor(device)
    train_anchors = clean["train_anchor_ep_t0"].astype(np.int64)
    pair_row = native.pair_to_row_index(rows)
    specs = discover_train_slices()
    tau = clean["tau"][: horizon.MAX_PERT_H].astype(np.float64)
    npz: dict[str, np.ndarray] = {
        "horizons": np.arange(1, horizon.MAX_PERT_H + 1, dtype=np.int64),
        "quantiles": horizon.QUANTILES.copy(),
        "tau_h1_to_h5": tau,
        "slice_keys": np.asarray([s["key"] for s in specs]),
        "families": np.asarray([s["family"] for s in specs]),
        "strength_tokens": np.asarray([s["strength_token"] for s in specs]),
        "strengths": np.asarray([s["strength"] for s in specs], dtype=np.float64),
    }
    rows_report: list[dict[str, Any]] = []
    deltas: list[float] = []
    for spec in specs:
        key = str(spec["key"])
        print(f"[G_oodh] train slice={key} anchors={len(train_anchors)}", flush=True)
        pert_emb_by_ep = horizon.load_perturbed_emb(Path(spec["emb_path"]))
        part = horizon.rollout_predictions(
            model,
            data,
            train_anchors,
            device=device,
            max_h=horizon.MAX_PERT_H,
            pert_emb_by_ep=pert_emb_by_ep,
        )
        y = horizon.compute_labels(part["err_at_h"], part["valid"], tau, horizon.MAX_PERT_H)
        mse_cache = np.load(spec["mse_path"])
        mse_by_row = {int(r): float(m) for r, m in zip(mse_cache["row_idx"], mse_cache["mse"])}
        ref = []
        got = []
        for i, (ep_raw, t0_raw) in enumerate(train_anchors):
            row_idx = pair_row[(int(ep_raw), int(t0_raw))]
            if row_idx not in mse_by_row:
                raise RuntimeError(f"{spec['mse_path'].name} missing row_idx={row_idx}")
            ref.append(mse_by_row[row_idx])
            got.append(float(part["err_at_h"][i, 0]))
        h1_delta = float(np.max(np.abs(np.asarray(got, dtype=np.float64) - np.asarray(ref, dtype=np.float64))))
        deltas.append(h1_delta)
        if not np.isfinite(h1_delta) or h1_delta >= PERT_TRAIN_H1_TOL:
            raise SystemExit(f"perturbed train h=1 anchor failed for {key}: max_delta={h1_delta:.9g}")
        npz[f"{key}_anchor_ep_t0"] = train_anchors.astype(np.int64)
        npz[f"{key}_valid"] = part["valid"].astype(bool)
        npz[f"{key}_pred_z"] = part["pred_z"].astype(np.float32)
        npz[f"{key}_err_at_h"] = part["err_at_h"].astype(np.float64)
        npz[f"{key}_mean_err_to_h"] = part["mean_err_to_h"].astype(np.float64)
        npz[f"{key}_y"] = y.astype(np.int8)
        npz[f"{key}_h1_mse_cache_max_abs_delta"] = np.asarray(h1_delta, dtype=np.float64)
        rows_report.append(
            {
                "key": key,
                "family": spec["family"],
                "strength": spec["strength"],
                "anchors": int(len(train_anchors)),
                "valid_h1": int(part["valid"][:, 0].sum()),
                "valid_h3": int(part["valid"][:, 2].sum()),
                "valid_h5": int(part["valid"][:, 4].sum()),
                "h1_mse_cache_max_abs_delta": h1_delta,
            }
        )
    np.savez_compressed(PERT_TRAIN_LABELS, **npz)
    return {
        "status": "ok",
        "path": str(PERT_TRAIN_LABELS),
        "loader_source": loader_source,
        "checkpoint_path": checkpoint_path,
        "config_path": config_path,
        "config_history_size": int(config["predictor"]["num_frames"]),
        "max_h": horizon.MAX_PERT_H,
        "anchor_tolerance": PERT_TRAIN_H1_TOL,
        "h1_mse_cache_max_abs_delta": float(max(deltas)),
        "slices": rows_report,
    }


def build_oodh_train_examples(
    data: dict[str, np.ndarray],
    labels: np.lib.npyio.NpzFile,
    keys: list[str],
) -> dict[str, np.ndarray]:
    emb_dim = data["emb"].shape[-1]
    act_dim = data["action"].shape[-1]
    clean_emb = data["emb"].astype(np.float32)
    act_np = data["action"].astype(np.float32)
    chunks: list[dict[str, np.ndarray]] = []
    for key in keys:
        emb_by_ep = horizon.load_perturbed_emb(OOD_EMB_CACHE_DIR / f"train_{key}.npz")
        anchors = labels[f"{key}_anchor_ep_t0"].astype(np.int64)
        n = len(anchors)
        past_z = np.zeros((n, native.WINDOW, emb_dim), dtype=np.float32)
        past_a = np.zeros((n, native.WINDOW, act_dim), dtype=np.float32)
        future_z = np.zeros((n, native.MAX_FUTURE_TOKENS, emb_dim), dtype=np.float32)
        future_delta = np.zeros((n, native.MAX_FUTURE_TOKENS, emb_dim), dtype=np.float32)
        future_avail = labels[f"{key}_valid"][:, : native.MAX_FUTURE_TOKENS].astype(bool)
        pred_z = labels[f"{key}_pred_z"][:, : native.MAX_FUTURE_TOKENS].astype(np.float32)
        t_scalar = np.zeros(n, dtype=np.float32)
        y = np.zeros((n, len(native.HORIZONS), len(native.QUANTILES)), dtype=np.float32)
        valid = np.zeros_like(y, dtype=bool)
        raw_y = labels[f"{key}_y"].astype(np.int8)
        raw_valid = labels[f"{key}_valid"].astype(bool)
        for i, (ep_raw, t_raw) in enumerate(anchors):
            ep = int(ep_raw)
            t0 = int(t_raw)
            vt = native.valid_transition_count(data, ep)
            t_scalar[i] = 0.0 if vt <= 1 else float(t0 / max(1, vt - 1))
            seq = emb_by_ep[ep]
            for w in range(native.WINDOW):
                src = max(0, t0 - native.WINDOW + 1 + w)
                past_z[i, w] = seq[src]
                past_a[i, w] = act_np[ep, src]
            previous = clean_emb[ep, t0]
            for k in range(native.MAX_FUTURE_TOKENS):
                if future_avail[i, k] and np.isfinite(pred_z[i, k]).all():
                    future_z[i, k] = pred_z[i, k]
                    future_delta[i, k] = pred_z[i, k] - previous
                    previous = pred_z[i, k]
                else:
                    future_avail[i, k] = False
            for h in (1, 3, 5):
                h_i = native.HORIZONS.index(h)
                src_i = native.PERT_H_TO_LABEL_IDX[h]
                if raw_valid[i, src_i]:
                    y[i, h_i] = raw_y[i, src_i]
                    valid[i, h_i] = True
        chunks.append(
            {
                "kind": np.full(n, 1, dtype=np.int8),
                "past_z": past_z,
                "past_a": past_a,
                "future_z": future_z,
                "future_delta": future_delta,
                "future_avail": future_avail,
                "t_scalar": t_scalar,
                "episode": anchors[:, 0].astype(np.int64),
                "anchor_ep_t0": anchors,
                "y": y,
                "valid": valid,
                "teacher": np.full(n, np.nan, dtype=np.float32),
                "teacher_valid": np.zeros(n, dtype=bool),
                "budget_err": np.full(n, np.nan, dtype=np.float64),
                "budget_valid": np.zeros(n, dtype=bool),
                "slice_key": np.asarray([key] * n),
            }
        )
    return native.concat_examples(chunks)


def ci_overlap(a: dict[str, float], b: dict[str, float]) -> bool:
    return bool(a["ci95_high"] >= b["ci95_low"] and b["ci95_high"] >= a["ci95_low"])


def run_g_oodh(
    data: dict[str, np.ndarray],
    rows: dict[str, np.ndarray],
    clean: np.lib.npyio.NpzFile,
    pert_eval: np.lib.npyio.NpzFile,
    predz: np.lib.npyio.NpzFile,
    context: dict[str, Any],
    main_report: dict[str, Any],
    addendum_report: dict[str, Any],
) -> dict[str, Any]:
    label_meta = generate_perturbed_train_labels(data, rows, clean)
    train_labels = np.load(PERT_TRAIN_LABELS)
    keys = [str(k) for k in train_labels["slice_keys"].tolist()]
    print("[G_oodh] building train examples", flush=True)
    pert_train_oodh = build_oodh_train_examples(data, train_labels, keys)
    train_ex = native.concat_examples([context["clean_train_ex"], pert_train_oodh])
    cfg = dict(
        include_future=True,
        action_only=False,
        use_teacher=False,
        use_unlogged=False,
        use_budget=False,
        label_permutation_seed=None,
    )
    print(f"[G_oodh] training rows={len(train_ex['episode'])}", flush=True)
    model, info, norm = native.train_arm("G_oodh", train_ex, **cfg)
    clean_logits = native.predict_logits(model, context["clean_eval_ex"], norm)
    clean_eval = native.evaluate_clean(clean_logits, context["clean_eval_ex"])
    e_ref = main_report["arms"]["E"]["clean_eval"]["h1_q75"]["failure_detection_auroc"]
    g_h1 = clean_eval["h1_q75"]["failure_detection_auroc"]
    retained = ci_overlap(g_h1, e_ref)
    ood_keys = [str(k) for k in pert_eval["slice_keys"].tolist()]
    corrected = addendum.evaluate_ood_corrected(model, norm, data, pert_eval, predz, ood_keys)
    e_corrected = addendum_report["corrected_ood"]["corrected"]["E"]
    representative = addendum.representative_slices(ood_keys)
    return {
        "status": "ok",
        "protocol": {
            "base_arm": "E + perturbed train horizon labels and true perturbed rollout future tokens",
            "clean_rows": int(np.sum(train_ex["kind"] == 0)),
            "perturbed_rows": int(np.sum(train_ex["kind"] == 1)),
            "perturbed_train_outputs": "h=1,3,5 labels active; h=10 loss only on clean rows",
            "corrected_ood_eval": "reports/g2n_labels_perturbed_predz.npz true future tokens; single-class AUROC fail-closed",
        },
        "perturbed_train_labels": label_meta,
        "info": info,
        "clean_eval": clean_eval,
        "clean_retention": {
            "reference": "main report arm E clean h=1,q75 AUROC",
            "E_h1_q75_auroc": e_ref,
            "G_oodh_h1_q75_auroc": g_h1,
            "ci_overlap": retained,
            "verdict": "retained" if retained else "degraded",
        },
        "corrected_ood": {
            "G_oodh": corrected,
            "E_reference_from_addendum": e_corrected,
            "representative_slices": representative,
        },
        "not_claimed": [
            "single checkpoint, single export",
            "clean retention uses CI overlap against E, not a superiority claim",
            "corrected OOD is detection on perturbed latent labels, not planning/control",
        ],
    }


def fmt_metric(m: dict[str, Any], key: str = "failure_detection_auroc") -> str:
    d = m[key]
    if d["observed"] is None:
        return "fail-closed"
    return f"{d['observed']:.6f} [{d['ci95_low']:.6f}, {d['ci95_high']:.6f}]"


def write_markdown(report: dict[str, Any]) -> None:
    lines = [
        "# G2N Matrix Completion",
        "",
        f"- status: `{report['status']}`",
        f"- E_rank allocation verdict: **{report['cells']['E_rank']['E_rank']['verdict']}**",
        "- seeds/hyperparameters follow `_g2n_native_ledger.py`: np/torch 20260611, split 1701, bootstrap 500/314159, epochs 30, batch 256, lr 1e-3, lambda_budget 0.5.",
        "",
        "## B_posthoc_horizon",
        "",
        "| h | AUROC | UER | eval rows |",
        "|---:|---:|---:|---:|",
    ]
    for h in native.HORIZONS:
        item = report["cells"]["B_posthoc_horizon"]["horizons"][f"h{h}_q75"]
        m = item["metrics_eval_episode_bootstrap"]
        lines.append(
            f"| {h} | {fmt_metric(m, 'failure_detection_auroc')} | "
            f"{fmt_metric(m, 'unlogged_error_rate')} | {item['eval_rows']} |"
        )
    e_rank = report["cells"]["E_rank"]
    d = e_rank["E_rank"]["delta_E_rank_minus_uniform"]
    dh = e_rank["H_rank"]["delta_H_rank_minus_uniform"]
    lines.extend(
        [
            "",
            "## E_rank",
            "",
            f"- pure E h=1 anchor: `{e_rank['anchors']['pure_E_h1_q75_auroc']['observed']:.15f}`",
            f"- E_rank delta ledger-uniform: `{d['observed']:.9f}`; 95% CI `[{d['ci95_low']:.9f}, {d['ci95_high']:.9f}]`; verdict **{e_rank['E_rank']['verdict']}**",
            f"- H_rank permutation-control delta: `{dh['observed']:.9f}`; 95% CI `[{dh['ci95_low']:.9f}, {dh['ci95_high']:.9f}]`",
            f"- oracle ceiling oracle-uniform: `{e_rank['oracle_ceiling']['oracle_minus_uniform_per_step_mse']:.9f}`",
            "",
            "| arm | h=1 AUROC | h=5 AUROC |",
            "|---|---:|---:|",
        ]
    )
    for arm in ("pure_E", "E_rank", "H_rank"):
        ce = e_rank[arm]["clean_eval"]
        lines.append(
            f"| `{arm}` | {fmt_metric(ce['h1_q75'], 'failure_detection_auroc')} | "
            f"{fmt_metric(ce['h5_q75'], 'failure_detection_auroc')} |"
        )
    g = report["cells"]["G_oodh"]
    lines.extend(
        [
            "",
            "## G_oodh",
            "",
            f"- perturbed train label h=1 max |delta| vs `mse_train_*`: `{g['perturbed_train_labels']['h1_mse_cache_max_abs_delta']:.9g}`",
            f"- clean h=1 retention verdict: **{g['clean_retention']['verdict']}**",
            "",
            "| h | clean AUROC | clean UER |",
            "|---:|---:|---:|",
        ]
    )
    for h in native.HORIZONS:
        m = g["clean_eval"][f"h{h}_q75"]
        lines.append(
            f"| {h} | {fmt_metric(m, 'failure_detection_auroc')} | {fmt_metric(m, 'unlogged_error_rate')} |"
        )
    lines.extend(
        [
            "",
            "## Corrected OOD Representative Slices",
            "",
            "| slice | h | E corrected AUROC | G_oodh corrected AUROC |",
            "|---|---:|---:|---:|",
        ]
    )
    reps = g["corrected_ood"]["representative_slices"]
    for key in reps:
        for h in (1, 3, 5):
            e_m = g["corrected_ood"]["E_reference_from_addendum"][key][f"h{h}_q75"]
            g_m = g["corrected_ood"]["G_oodh"][key][f"h{h}_q75"]
            lines.append(
                f"| `{key}` | {h} | {fmt_metric(e_m, 'failure_detection_auroc')} | "
                f"{fmt_metric(g_m, 'failure_detection_auroc')} |"
            )
    lines.extend(["", "## Not Claimed", ""])
    for item in report["not_claimed"]:
        lines.append(f"- {item}")
    MD_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    require_inputs()
    np.random.seed(native.PYTHON_SEED)
    torch.manual_seed(native.TORCH_SEED)
    torch.set_num_threads(int(os.environ.get("G2N_TORCH_THREADS", "4")))
    REPORT_DIR.mkdir(exist_ok=True)

    data = load_data()
    rows = flatten_transition_rows(data)
    splits = split_episodes(data["emb"].shape[0])
    if native.SPLIT_SEED != 1701 or int(len(splits["eval"])) <= 0:
        raise SystemExit("split sanity failed")

    clean = np.load(REPORT_DIR / "g2n_labels_clean.npz")
    pert = np.load(REPORT_DIR / "g2n_labels_perturbed.npz")
    predz = np.load(PERT_PREDZ)
    main_report = json.loads((REPORT_DIR / "g2n_native_ledger.json").read_text(encoding="utf-8"))
    addendum_report = json.loads((REPORT_DIR / "g2n_addendum.json").read_text(encoding="utf-8"))
    phase2c_report = json.loads((REPORT_DIR / "lewm_ood_aware_gap.json").read_text(encoding="utf-8"))

    context = addendum.build_train_eval_context(data, clean)

    b_cell = run_b_posthoc_horizon(data, rows, clean, phase2c_report)
    e_cell = run_e_rank(clean, context, main_report)
    g_cell = run_g_oodh(data, rows, clean, pert, predz, context, main_report, addendum_report)

    report = {
        "status": "ok",
        "schema_id": "g2n.matrix_completion",
        "protocol": {
            "deterministic": True,
            "seeds": {"numpy": native.PYTHON_SEED, "torch": native.TORCH_SEED, "split": native.SPLIT_SEED, "bootstrap": native.BOOTSTRAP_SEED},
            "bootstrap_resamples": native.BOOTSTRAPS,
            "primary_quantile": 75,
            "epochs": native.EPOCHS,
            "batch": native.BATCH,
            "lr": native.LR,
            "lambda_budget": native.LAMBDA_BUDGET,
        },
        "precursors": {
            "clean_labels": str(REPORT_DIR / "g2n_labels_clean.npz"),
            "perturbed_eval_labels": str(REPORT_DIR / "g2n_labels_perturbed.npz"),
            "perturbed_eval_predz": str(PERT_PREDZ),
            "native_ledger": str(REPORT_DIR / "g2n_native_ledger.json"),
            "addendum": str(REPORT_DIR / "g2n_addendum.json"),
            "lat_ood_emb_cache": str(OOD_EMB_CACHE_DIR),
        },
        "cells": {
            "B_posthoc_horizon": b_cell,
            "E_rank": e_cell,
            "G_oodh": g_cell,
        },
        "not_claimed": [
            "No planning or control benefit is claimed.",
            "All allocation results are prediction-budget allocation only.",
            "No lambda or hyperparameter scan was performed.",
            "Single checkpoint/single latent export; episode bootstrap does not replace independent world seeds.",
            "B_posthoc_horizon is information-only.",
        ],
        "outputs": {
            "json": str(JSON_PATH),
            "md": str(MD_PATH),
            "perturbed_train_labels": str(PERT_TRAIN_LABELS),
        },
    }
    serializable = clean_json(report)
    JSON_PATH.write_text(json.dumps(serializable, indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(serializable)
    print(json.dumps(serializable["cells"]["E_rank"]["E_rank"]["delta_E_rank_minus_uniform"], indent=2), flush=True)
    print(f"wrote {JSON_PATH}", flush=True)
    print(f"wrote {MD_PATH}", flush=True)
    print(f"wrote {PERT_TRAIN_LABELS}", flush=True)


if __name__ == "__main__":
    main()

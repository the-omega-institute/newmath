from __future__ import annotations

import json
import math
import os
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch

import _g2n_matrix_completion as mc
import _g2n_native_ledger as g2n
import _native_residual_detection as nrd
from _lat_lewm_port import NPZ_PATH, REPORT_DIR, split_episodes
from _phase1c_gap_ledger import auroc_rank, flatten_transition_rows, predict_logistic_head
from _phase2a_brittleness_gap import clean_json, fit_clean_protocol
from _phase2c_ood_aware_gap import fit_gap_head_for_parts, materialize_clean_split


ROOT = Path(__file__).resolve().parent
CLEAN_LABELS = REPORT_DIR / "g2n_labels_clean.npz"
LATENT_NPZ = NPZ_PATH
SOURCE_JSON = REPORT_DIR / "lewm_native_residual_detection.json"
MATRIX_COMPLETION_JSON = REPORT_DIR / "g2n_matrix_completion.json"
PHASE2C_JSON = REPORT_DIR / "lewm_ood_aware_gap.json"
JSON_PATH = REPORT_DIR / "lewm_native_vs_posthoc_paired.json"
MD_PATH = REPORT_DIR / "lewm_native_vs_posthoc_paired.md"

PYTHON_SEED = 20260611
TORCH_SEED = 20260611
SPLIT_SEED = 1701
BOOTSTRAP_SEED = 314159
BOOTSTRAPS = 500
PRIMARY_Q = 75
TARGET_HORIZONS = (1, 5)
EXPECTED_E_H1_AUROC = 0.7385152058598745
EXPECTED_R_RANK_H1_AUROC = 0.7876022489084622
E_ANCHOR_TOL = 1e-9
R_RANK_ANCHOR_TOL = 1e-6
POSTHOC_ANCHOR_TOL = 1e-12


def require_inputs() -> None:
    required = [
        CLEAN_LABELS,
        LATENT_NPZ,
        ROOT / "_native_residual_detection.py",
        ROOT / "_g2n_native_ledger.py",
        ROOT / "_allocation_bridge.py",
        SOURCE_JSON,
        MATRIX_COMPLETION_JSON,
        PHASE2C_JSON,
    ]
    missing = [p for p in required if not p.exists()]
    if missing:
        raise SystemExit("missing required precursor(s): " + ", ".join(str(p) for p in missing))


def metric_stat(observed: float, samples: np.ndarray) -> dict[str, float]:
    arr = np.asarray(samples, dtype=np.float64)
    finite = arr[np.isfinite(arr)]
    if len(finite) != len(arr):
        raise RuntimeError("non-finite bootstrap sample in paired AUROC delta")
    return {
        "observed": float(observed),
        "bootstrap_mean": float(np.mean(finite)),
        "ci95_low": float(np.percentile(finite, 2.5)),
        "ci95_high": float(np.percentile(finite, 97.5)),
    }


def target_arrays(clean: np.lib.npyio.NpzFile, split: str, h: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    h_idx = g2n.H_TO_LABEL_IDX[h]
    q_idx = g2n.Q_TO_IDX[PRIMARY_Q]
    valid = clean[f"{split}_valid"][:, h_idx].astype(bool)
    y = clean[f"{split}_y"][:, h_idx, q_idx].astype(np.int8)
    anchors = clean[f"{split}_anchor_ep_t0"].astype(np.int64)
    return y[valid], anchors[valid, 0].astype(np.int64), valid


def observed_auroc(y: np.ndarray, score: np.ndarray) -> float:
    return float(auroc_rank(y.astype(np.int8), score.astype(np.float64)))


def paired_bootstrap_delta(
    y: np.ndarray,
    native_score: np.ndarray,
    posthoc_score: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int = BOOTSTRAP_SEED,
    n_boot: int = BOOTSTRAPS,
) -> dict[str, Any]:
    y = y.astype(np.int8)
    native_score = native_score.astype(np.float64)
    posthoc_score = posthoc_score.astype(np.float64)
    episode = episode.astype(np.int64)
    if not (len(y) == len(native_score) == len(posthoc_score) == len(episode)):
        raise RuntimeError("paired arrays have inconsistent lengths")
    if np.unique(y).size < 2:
        raise RuntimeError("observed paired AUROC is undefined for a single-class truth vector")

    native_obs = observed_auroc(y, native_score)
    posthoc_obs = observed_auroc(y, posthoc_score)
    delta_obs = native_obs - posthoc_obs

    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    rng = np.random.default_rng(seed)
    deltas: list[float] = []
    native_samples: list[float] = []
    posthoc_samples: list[float] = []
    skipped_single_class = 0
    for _ in range(n_boot):
        sampled = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[i] for i in sampled])
        if np.unique(y[idx]).size < 2:
            skipped_single_class += 1
            continue
        n_auc = observed_auroc(y[idx], native_score[idx])
        p_auc = observed_auroc(y[idx], posthoc_score[idx])
        native_samples.append(n_auc)
        posthoc_samples.append(p_auc)
        deltas.append(n_auc - p_auc)

    if skipped_single_class:
        raise RuntimeError(f"single-class paired bootstrap resamples encountered: {skipped_single_class}")

    delta_arr = np.asarray(deltas, dtype=np.float64)
    native_arr = np.asarray(native_samples, dtype=np.float64)
    posthoc_arr = np.asarray(posthoc_samples, dtype=np.float64)
    return {
        "delta_native_minus_posthoc": metric_stat(delta_obs, delta_arr),
        "native_auroc": metric_stat(native_obs, native_arr),
        "posthoc_auroc": metric_stat(posthoc_obs, posthoc_arr),
        "bootstrap_seed": int(seed),
        "bootstrap_resamples": int(n_boot),
        "eval_rows": int(len(y)),
        "eval_episodes": int(len(unique_ep)),
        "positive_count": int(np.sum(y > 0)),
        "negative_count": int(np.sum(y <= 0)),
    }


def build_posthoc_scores(
    data: dict[str, np.ndarray],
    clean: np.lib.npyio.NpzFile,
    rows: dict[str, np.ndarray],
) -> tuple[dict[int, dict[str, Any]], dict[str, Any]]:
    phase2c_report = json.loads(PHASE2C_JSON.read_text(encoding="utf-8"))
    matrix_report = json.loads(MATRIX_COMPLETION_JSON.read_text(encoding="utf-8"))

    print("[posthoc] rebuilding phase2c clean-only T1 anchor", flush=True)
    protocol = fit_clean_protocol(data, rows)
    train_clean = materialize_clean_split(protocol, rows, "train")
    eval_clean = materialize_clean_split(protocol, rows, "eval")
    clean_head, clean_fit = fit_gap_head_for_parts([train_clean])
    p_eval, _ = predict_logistic_head(clean_head, eval_clean["x"])
    phase2c_obs = float(auroc_rank(eval_clean["y"], p_eval))
    phase2c_target = float(phase2c_report["arms"]["clean_only"]["clean_eval"]["observed"]["failure_detection_auroc"])
    phase2c_delta = abs(phase2c_obs - phase2c_target)
    if phase2c_delta > mc.ANCHOR_TOL_STRICT:
        raise SystemExit(
            f"posthoc T1 anchor failed: observed={phase2c_obs:.17g}, target={phase2c_target:.17g}"
        )

    out: dict[int, dict[str, Any]] = {}
    for h in TARGET_HORIZONS:
        print(f"[posthoc] horizon h={h}", flush=True)
        x_train, y_train, ep_train = mc.row_x_by_anchor(train_clean, clean, rows, "train", h)
        x_eval, y_eval, ep_eval = mc.row_x_by_anchor(eval_clean, clean, rows, "eval", h)
        head, fit_info = mc.fit_logistic_head(x_train, y_train, steps=mc.POSTHOC_STEPS, lr=mc.POSTHOC_LR, l2=mc.POSTHOC_L2)
        prob, _ = predict_logistic_head(head, x_eval)
        obs = observed_auroc(y_eval, prob)
        frozen = matrix_report["cells"]["B_posthoc_horizon"]["horizons"][f"h{h}_q75"]["metrics_eval_episode_bootstrap"][
            "failure_detection_auroc"
        ]
        delta = abs(obs - float(frozen["observed"]))
        if delta > POSTHOC_ANCHOR_TOL:
            raise SystemExit(
                f"posthoc h={h} observed anchor failed: observed={obs:.17g}, frozen={float(frozen['observed']):.17g}"
            )
        out[h] = {
            "score": prob.astype(np.float64),
            "y": y_eval.astype(np.int8),
            "episode": ep_eval.astype(np.int64),
            "fit": fit_info,
            "train_rows": int(len(y_train)),
            "train_episodes": int(len(np.unique(ep_train))),
            "observed_auroc": obs,
            "frozen_independent_ci": frozen,
        }

    anchor = {
        "phase2c_clean_only_t1_auroc": {
            "observed": phase2c_obs,
            "target": phase2c_target,
            "abs_delta": phase2c_delta,
            "tolerance": mc.ANCHOR_TOL_STRICT,
            "fit": clean_fit,
        }
    }
    return out, anchor


def write_markdown(report: dict[str, Any]) -> None:
    lines = [
        "# Native vs Post-Hoc Paired AUROC",
        "",
        f"- status: `{report['status']}`",
        f"- B verdict: `{report['decision']['verdict']}`",
        f"- rule: {report['decision']['rule']}",
        f"- E skeleton anchor h=1: `{report['anchors']['skeleton_E_h1_q75_auroc']['observed']:.15f}`",
        f"- R-rank anchor h=1: `{report['anchors']['R-rank_h1_q75_auroc']['observed']:.15f}`",
        "",
        "## Paired Delta AUROC",
        "",
        "| arm | h | native AUROC | post-hoc AUROC | delta native-posthoc [95% CI] | decision |",
        "|---|---:|---:|---:|---:|---|",
    ]
    for arm, item in report["arms"].items():
        for h in TARGET_HORIZONS:
            paired = item["paired"][f"h{h}_q75"]
            n = paired["native_auroc"]
            p = paired["posthoc_auroc"]
            d = paired["delta_native_minus_posthoc"]
            lines.append(
                f"| {arm} | {h} | `{n['observed']:.6f}` | `{p['observed']:.6f}` | "
                f"`{d['observed']:.6f}` [`{d['ci95_low']:.6f}`, `{d['ci95_high']:.6f}`] | "
                f"`{paired['decision']}` |"
            )

    lines.extend(
        [
            "",
            "## Prior Independent CI",
            "",
            "Round2-B independent-CI results are retained as prior context; this report adds the paired comparison on the same eval episodes.",
            "",
            "| arm | h | native AUROC [CI] | post-hoc AUROC [CI] | independent CI separates |",
            "|---|---:|---:|---:|---|",
        ]
    )
    for arm, item in report["arms"].items():
        for h in TARGET_HORIZONS:
            prior = item["prior_independent_ci"][f"h{h}_q75"]
            n = prior["native_failure_detection_auroc"]
            p = prior["posthoc_failure_detection_auroc"]
            lines.append(
                f"| {arm} | {h} | `{n['observed']:.6f}` [`{n['ci95_low']:.6f}`, `{n['ci95_high']:.6f}`] | "
                f"`{p['observed']:.6f}` [`{p['ci95_low']:.6f}`, `{p['ci95_high']:.6f}`] | "
                f"`{prior['ci_separates_posthoc']}` |"
            )

    lines.extend(
        [
            "",
            "## Not Claimed",
        ]
    )
    lines.extend(f"- {x}" for x in report["not_claimed"])
    MD_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    require_inputs()
    if (PYTHON_SEED, TORCH_SEED, SPLIT_SEED, BOOTSTRAP_SEED, BOOTSTRAPS) != (
        g2n.PYTHON_SEED,
        g2n.TORCH_SEED,
        g2n.SPLIT_SEED,
        g2n.BOOTSTRAP_SEED,
        g2n.BOOTSTRAPS,
    ):
        raise SystemExit("seed/hyperparameter sanity failed")
    if (PYTHON_SEED, TORCH_SEED, SPLIT_SEED, BOOTSTRAP_SEED, BOOTSTRAPS) != (
        nrd.PYTHON_SEED,
        nrd.TORCH_SEED,
        nrd.SPLIT_SEED,
        nrd.BOOTSTRAP_SEED,
        nrd.BOOTSTRAPS,
    ):
        raise SystemExit("_native_residual_detection seed/hyperparameter sanity failed")

    np.random.seed(PYTHON_SEED)
    torch.manual_seed(TORCH_SEED)
    torch.set_num_threads(int(os.environ.get("G2N_TORCH_THREADS", "4")))

    data = dict(np.load(LATENT_NPZ, allow_pickle=True))
    splits = split_episodes(data["emb"].shape[0])
    if SPLIT_SEED != 1701 or int(len(splits["eval"])) <= 0:
        raise SystemExit("split sanity failed")
    clean = np.load(CLEAN_LABELS)
    source_report = json.loads(SOURCE_JSON.read_text(encoding="utf-8"))
    matrix_report = json.loads(MATRIX_COMPLETION_JSON.read_text(encoding="utf-8"))

    clean_train_ex = g2n.build_clean_examples(data, clean, "train", None)
    clean_eval_ex = g2n.build_clean_examples(data, clean, "eval", None)

    print("[anchor] retraining native E skeleton", flush=True)
    e_model, e_info, e_norm = g2n.train_arm(
        "E",
        clean_train_ex,
        include_future=True,
        action_only=False,
        use_teacher=False,
        use_unlogged=False,
        use_budget=False,
        label_permutation_seed=None,
    )
    e_logits = g2n.predict_logits(e_model, clean_eval_ex, e_norm)
    e_eval = g2n.evaluate_clean(e_logits, clean_eval_ex)
    e_obs = float(e_eval["h1_q75"]["failure_detection_auroc"]["observed"])
    e_delta = abs(e_obs - EXPECTED_E_H1_AUROC)
    if e_delta > E_ANCHOR_TOL:
        raise SystemExit(f"E skeleton anchor failed: observed={e_obs:.17g}, expected={EXPECTED_E_H1_AUROC:.17g}")

    rows = flatten_transition_rows(data)
    posthoc_scores, posthoc_anchor = build_posthoc_scores(data, clean, rows)

    train_ex = nrd.attach_targets(clean_train_ex, clean, "train")
    eval_ex = nrd.attach_targets(clean_eval_ex, clean, "eval")
    arm_specs = [
        ("R-reg", "regression", None, "Huber(log mean_err_to_h[h]) dual-head"),
        ("R-rank", "rank", None, "within-episode pairwise logistic ranking over mean_err_to_h[h] dual-head"),
        ("R-multitask-lambda0p25", "multitask", 0.25, "BCE horizon + 0.25*Huber(log mean_err) + pairwise rank"),
        ("R-multitask-lambda1p0", "multitask", 1.0, "BCE horizon + 1.0*Huber(log mean_err) + pairwise rank"),
    ]

    arms: dict[str, Any] = {}
    r_rank_anchor: dict[str, Any] | None = None
    for arm, objective, lambda_reg, label in arm_specs:
        print(f"[train] {arm}", flush=True)
        t0 = time.perf_counter()
        model, info, norm = nrd.train_residual_arm(arm, train_ex, objective=objective, lambda_reg=lambda_reg)
        score = nrd.predict_residual(model, eval_ex, norm)
        train_seconds = round(time.perf_counter() - t0, 2)
        info["objective_label"] = label
        info["paired_script_wall_time_seconds"] = train_seconds

        paired_by_h: dict[str, Any] = {}
        prior_by_h: dict[str, Any] = {}
        for j, h in enumerate(TARGET_HORIZONS):
            y, episode, valid = target_arrays(clean, "eval", h)
            native_score = score[valid, j].astype(np.float64)
            post = posthoc_scores[h]
            if not np.array_equal(y, post["y"]) or not np.array_equal(episode, post["episode"]):
                raise SystemExit(f"posthoc/native eval alignment failed for arm={arm}, h={h}")
            paired = paired_bootstrap_delta(y, native_score, post["score"], episode)
            paired["decision"] = "positive" if paired["delta_native_minus_posthoc"]["ci95_low"] > 0.0 else "not_separated"
            paired_by_h[f"h{h}_q75"] = paired

            prior = source_report["arms"][arm]["clean_eval"][f"h{h}_q75"]
            prior_by_h[f"h{h}_q75"] = {
                "native_failure_detection_auroc": prior["native"]["failure_detection_auroc"],
                "posthoc_failure_detection_auroc": prior["posthoc_frozen_B"],
                "ci_separates_posthoc": prior["ci_separates_posthoc"],
                "point_beats_posthoc": prior["point_beats_posthoc"],
            }
            native_source_obs = float(prior["native"]["failure_detection_auroc"]["observed"])
            if abs(native_source_obs - paired["native_auroc"]["observed"]) > (R_RANK_ANCHOR_TOL if arm == "R-rank" else 1e-12):
                raise SystemExit(
                    f"native source observed mismatch for {arm} h={h}: "
                    f"rebuilt={paired['native_auroc']['observed']:.17g}, source={native_source_obs:.17g}"
                )
            frozen_obs = float(matrix_report["cells"]["B_posthoc_horizon"]["horizons"][f"h{h}_q75"][
                "metrics_eval_episode_bootstrap"
            ]["failure_detection_auroc"]["observed"])
            if abs(frozen_obs - paired["posthoc_auroc"]["observed"]) > POSTHOC_ANCHOR_TOL:
                raise SystemExit(
                    f"paired posthoc observed mismatch for h={h}: "
                    f"rebuilt={paired['posthoc_auroc']['observed']:.17g}, frozen={frozen_obs:.17g}"
                )

        if arm == "R-rank":
            h1 = paired_by_h["h1_q75"]["native_auroc"]["observed"]
            delta = abs(float(h1) - EXPECTED_R_RANK_H1_AUROC)
            if delta > R_RANK_ANCHOR_TOL:
                raise SystemExit(
                    f"R-rank h=1 anchor failed: observed={float(h1):.17g}, "
                    f"expected={EXPECTED_R_RANK_H1_AUROC:.17g}, abs_delta={delta:.9g}"
                )
            r_rank_anchor = {
                "observed": float(h1),
                "expected": EXPECTED_R_RANK_H1_AUROC,
                "abs_delta": float(delta),
                "tolerance": R_RANK_ANCHOR_TOL,
            }

        arms[arm] = {
            "info": info,
            "paired": paired_by_h,
            "prior_independent_ci": prior_by_h,
        }

    if r_rank_anchor is None:
        raise RuntimeError("R-rank anchor was not produced")

    r_rank_h1_delta = arms["R-rank"]["paired"]["h1_q75"]["delta_native_minus_posthoc"]
    b_positive = bool(float(r_rank_h1_delta["ci95_low"]) > 0.0)
    decision = {
        "verdict": "B_positive" if b_positive else "B_parity_bound",
        "positive": b_positive,
        "primary_arm": "R-rank",
        "primary_horizon": 1,
        "primary_delta_native_minus_posthoc": r_rank_h1_delta,
        "rule": "B positive iff R-rank paired delta AUROC(h=1) CI95_low > 0; otherwise B parity-bound.",
    }

    report = {
        "status": "ok",
        "schema_id": "lewm.native_vs_posthoc_paired",
        "protocol": {
            "comparison": "paired episode bootstrap over identical clean eval episodes and anchors",
            "delta": "AUROC(native scalar ledger score) - AUROC(post-hoc horizon reader score)",
            "bootstrap_resamples": BOOTSTRAPS,
            "bootstrap_seed": BOOTSTRAP_SEED,
            "seeds": {"numpy": PYTHON_SEED, "torch": TORCH_SEED, "split": SPLIT_SEED},
            "primary_quantile": PRIMARY_Q,
            "target_horizons": list(TARGET_HORIZONS),
            "native_source": "_native_residual_detection.py residual arms, same seed and hyperparameters",
            "posthoc_source": "_g2n_matrix_completion.py B_posthoc_horizon reader rebuilt for per-anchor scores",
            "posthoc_head": f"_phase1c_gap_ledger.fit_logistic_head steps={mc.POSTHOC_STEPS}, lr={mc.POSTHOC_LR}, l2={mc.POSTHOC_L2}",
        },
        "precursors": {
            "clean_npz": str(CLEAN_LABELS),
            "latent_npz": str(LATENT_NPZ),
            "native_residual_detection_json": str(SOURCE_JSON),
            "matrix_completion_json": str(MATRIX_COMPLETION_JSON),
        },
        "anchors": {
            "skeleton_E_h1_q75_auroc": {
                "observed": e_obs,
                "expected": EXPECTED_E_H1_AUROC,
                "abs_delta": e_delta,
                "tolerance": E_ANCHOR_TOL,
                "train_info": e_info,
                "h1_q75": e_eval["h1_q75"]["failure_detection_auroc"],
                "h5_q75": e_eval["h5_q75"]["failure_detection_auroc"],
            },
            "R-rank_h1_q75_auroc": r_rank_anchor,
            "posthoc": posthoc_anchor,
        },
        "arms": arms,
        "decision": decision,
        "not_claimed": [
            "Round2-B independent-CI not_positive result is retained and cited as prior context.",
            "This report only changes the comparison statistic to the paired AUROC delta on the same eval episodes.",
            "single checkpoint and single latent export; no world-seed replication is claimed.",
            "R-rank was reproduced from the Round2-B seed and hyperparameters, not retrained to a better seed.",
            "post-hoc horizon reader uses the same split and frozen protocol; it is rebuilt only to expose per-anchor scores.",
            "No planning or control benefit is claimed.",
        ],
        "outputs": {"json": str(JSON_PATH), "md": str(MD_PATH)},
    }

    cleaned = clean_json(report)
    JSON_PATH.write_text(json.dumps(cleaned, indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(cleaned)
    print(f"[done] wrote {JSON_PATH} and {MD_PATH}", flush=True)


if __name__ == "__main__":
    main()

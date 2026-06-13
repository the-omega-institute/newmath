import json
from pathlib import Path

import numpy as np

from _lat_lewm_port import split_episodes
from _phase1c_gap_ledger import auroc_rank, flatten_transition_rows


NP_SEED = 20260611
BOOTSTRAP_SEED = 314159
N_BOOT = 500
K_NEIGHBORS = 20
LATENT_PATH = Path("tworooms_latent_large.npz")
REPORT_DIR = Path("reports")
JSON_PATH = REPORT_DIR / "lewm_identifiability_link.json"
MD_PATH = REPORT_DIR / "lewm_identifiability_link.md"
FULL_GAP_HEAD_AUROC_REFERENCE = 0.731


def rank_average(x: np.ndarray) -> np.ndarray:
    x = np.asarray(x)
    order = np.argsort(x, kind="mergesort")
    sorted_x = x[order]
    ranks = np.empty(len(x), dtype=np.float64)
    i = 0
    while i < len(x):
        j = i + 1
        while j < len(x) and sorted_x[j] == sorted_x[i]:
            j += 1
        avg_rank = (i + 1 + j) / 2.0
        ranks[order[i:j]] = avg_rank
        i = j
    return ranks


def spearman_rank_corr(a: np.ndarray, b: np.ndarray) -> float:
    ar = rank_average(np.asarray(a, dtype=np.float64))
    br = rank_average(np.asarray(b, dtype=np.float64))
    if ar.size < 2 or float(np.std(ar)) == 0.0 or float(np.std(br)) == 0.0:
        return float("nan")
    return float(np.corrcoef(ar, br)[0, 1])


def summarize_bootstrap(values: list[float], observed: float) -> dict[str, float]:
    arr = np.asarray(values, dtype=np.float64)
    return {
        "observed": float(observed),
        "bootstrap_mean": float(np.nanmean(arr)),
        "ci95_low": float(np.nanpercentile(arr, 2.5)),
        "ci95_high": float(np.nanpercentile(arr, 97.5)),
    }


def bootstrap_metric_by_episode(
    y: np.ndarray,
    mse: np.ndarray,
    score: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
    n_boot: int,
) -> dict[str, dict[str, float]]:
    observed_auroc = auroc_rank(y, score)
    observed_spearman = spearman_rank_corr(score, mse)

    rng = np.random.default_rng(seed)
    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    n_ep = len(by_ep)

    aurocs: list[float] = []
    spearmans: list[float] = []
    for _ in range(n_boot):
        sampled = rng.integers(0, n_ep, size=n_ep)
        idx = np.concatenate([by_ep[i] for i in sampled])
        aurocs.append(auroc_rank(y[idx], score[idx]))
        spearmans.append(spearman_rank_corr(score[idx], mse[idx]))

    return {
        "auroc_failure_truth": summarize_bootstrap(aurocs, observed_auroc),
        "spearman_with_mse": summarize_bootstrap(spearmans, observed_spearman),
    }


def mask_for_episodes(episode: np.ndarray, split_ep: np.ndarray) -> np.ndarray:
    return np.isin(episode, split_ep)


def fit_global_linear_residual(
    emb_train: np.ndarray,
    state_train: np.ndarray,
    emb_eval: np.ndarray,
    state_eval: np.ndarray,
) -> tuple[np.ndarray, dict[str, object]]:
    x_train = np.concatenate(
        [emb_train.astype(np.float64), np.ones((emb_train.shape[0], 1), dtype=np.float64)],
        axis=1,
    )
    coef, residuals, rank, singular_values = np.linalg.lstsq(x_train, state_train, rcond=None)
    x_eval = np.concatenate(
        [emb_eval.astype(np.float64), np.ones((emb_eval.shape[0], 1), dtype=np.float64)],
        axis=1,
    )
    pred_eval = x_eval @ coef
    residual = np.mean((pred_eval - state_eval) ** 2, axis=1)
    info = {
        "fit": "np.linalg.lstsq",
        "includes_intercept": True,
        "design_shape": [int(x_train.shape[0]), int(x_train.shape[1])],
        "target_shape": [int(state_train.shape[0]), int(state_train.shape[1])],
        "rank": int(rank),
        "residuals_sum_by_target": residuals.astype(float).tolist(),
        "singular_values_min": float(np.min(singular_values)),
        "singular_values_max": float(np.max(singular_values)),
    }
    return residual, info


def local_knn_mean_residual(
    emb_train: np.ndarray,
    state_train: np.ndarray,
    emb_eval: np.ndarray,
    state_eval: np.ndarray,
    *,
    k: int,
) -> tuple[np.ndarray, dict[str, object]]:
    diff = emb_eval[:, None, :].astype(np.float64) - emb_train[None, :, :].astype(np.float64)
    dist2 = np.sum(diff * diff, axis=2)
    nn_idx = np.argpartition(dist2, kth=k - 1, axis=1)[:, :k]
    pred_eval = np.mean(state_train[nn_idx], axis=1)
    residual = np.mean((pred_eval - state_eval) ** 2, axis=1)
    info = {
        "k": int(k),
        "distance": "euclidean_in_emb_space",
        "implementation": "numpy_argpartition_on_full_eval_by_train_squared_distance_matrix",
        "distance_matrix_shape": [int(dist2.shape[0]), int(dist2.shape[1])],
    }
    return residual, info


def fmt_ci(metric: dict[str, float], digits: int = 4) -> str:
    return (
        f"{metric['observed']:.{digits}f} "
        f"[{metric['ci95_low']:.{digits}f}, {metric['ci95_high']:.{digits}f}]"
    )


def render_markdown(report: dict[str, object]) -> str:
    metrics = report["metrics_eval_episode_bootstrap"]
    split = report["split"]
    failure = report["failure_truth"]
    conclusion = report["conclusion"]
    rows = [
        "# LeWM tworooms identifiability-failure link",
        "",
        f"- scientific question: {report['scientific_question']}",
        f"- conclusion: **{conclusion['label']}**",
        f"- positive criterion: {conclusion['positive_criterion']}",
        f"- criterion passed by: {', '.join(conclusion['passed_by']) if conclusion['passed_by'] else 'none'}",
        f"- latent: `{report['data']['latent_path']}`; rows: {report['data']['valid_transition_rows']}; episodes: {report['data']['episodes']}",
        f"- fixed seeds: numpy={report['seeds']['numpy']}, split={report['seeds']['split']}, bootstrap={report['seeds']['bootstrap']}",
        f"- failure truth: `mse > train p75`; tau={failure['tau_train_p75']:.12f}; eval failure rate={failure['rates']['eval']:.6f}",
        f"- context only, not recomputed: full gap head AUROC {report['context_not_recomputed']['full_gap_head_auroc']:.3f}",
        "",
        "## Split",
        "",
        "| split | episodes | rows | failure rate |",
        "|---|---:|---:|---:|",
    ]
    for name in ("train", "calibration", "eval"):
        rows.append(
            f"| {name} | {split[name]['episodes']} | {split[name]['rows']} | "
            f"{failure['rates'][name]:.6f} |"
        )
    rows.extend(
        [
            "",
            "## Residual Link Tests",
            "",
            "| residual | AUROC(y, residual) | Spearman(residual, mse) | mean residual | median residual |",
            "|---|---:|---:|---:|---:|",
        ]
    )
    for key, label in (("global_linear", "global linear"), ("local_knn_mean", "local k=20 mean")):
        m = metrics[key]
        residual_summary = report["residual_summaries_eval"][key]
        rows.append(
            f"| {label} | {fmt_ci(m['auroc_failure_truth'])} | "
            f"{fmt_ci(m['spearman_with_mse'])} | "
            f"{residual_summary['mean']:.6f} | {residual_summary['median']:.6f} |"
        )
    rows.extend(
        [
            "",
            "## Protocol",
            "",
            "- rows: `_phase1c_gap_ledger.flatten_transition_rows` using `emb`, `mse`, `pos_agent`, `pos_target`, `episode`, `t`.",
            "- split: `_lat_lewm_port.split_episodes`, SPLIT_SEED 1701, 60/20/20.",
            "- state vector: `concat(pos_agent, pos_target)` with 4 dimensions.",
            "- global residual: least-squares `emb(192) -> state(4)` on train split, including intercept.",
            "- local residual: eval rows predicted from the mean state of k=20 nearest train embeddings.",
            "- CI: eval episode bootstrap, 500 resamples, BOOTSTRAP_SEED 314159.",
            "",
            "## Not Claimed",
            "",
        ]
    )
    rows.extend([f"- {item}" for item in report["not_claimed"]])
    rows.append("")
    return "\n".join(rows)


def residual_summary(x: np.ndarray) -> dict[str, float]:
    return {
        "mean": float(np.mean(x)),
        "median": float(np.median(x)),
        "std": float(np.std(x)),
        "min": float(np.min(x)),
        "p25": float(np.percentile(x, 25.0)),
        "p75": float(np.percentile(x, 75.0)),
        "max": float(np.max(x)),
    }


def main() -> None:
    np.random.seed(NP_SEED)

    data_npz = np.load(LATENT_PATH)
    data = {k: data_npz[k] for k in data_npz.files}
    rows = flatten_transition_rows(data)
    n_ep = int(data["emb"].shape[0])
    splits = split_episodes(n_ep)

    train_mask = mask_for_episodes(rows["episode"], splits["train"])
    cal_mask = mask_for_episodes(rows["episode"], splits["calibration"])
    eval_mask = mask_for_episodes(rows["episode"], splits["eval"])

    emb = rows["emb"].astype(np.float64)
    mse = rows["mse"].astype(np.float64)
    state = np.concatenate(
        [rows["pos_agent"].astype(np.float64), rows["pos_target"].astype(np.float64)],
        axis=1,
    )

    tau = float(np.percentile(mse[train_mask], 75.0))
    y = mse > tau

    emb_train = emb[train_mask]
    state_train = state[train_mask]
    emb_eval = emb[eval_mask]
    state_eval = state[eval_mask]
    y_eval = y[eval_mask]
    mse_eval = mse[eval_mask]
    episode_eval = rows["episode"][eval_mask]

    r_global, global_info = fit_global_linear_residual(
        emb_train, state_train, emb_eval, state_eval
    )
    r_local, local_info = local_knn_mean_residual(
        emb_train, state_train, emb_eval, state_eval, k=K_NEIGHBORS
    )

    metrics = {
        "global_linear": bootstrap_metric_by_episode(
            y_eval,
            mse_eval,
            r_global,
            episode_eval,
            seed=BOOTSTRAP_SEED,
            n_boot=N_BOOT,
        ),
        "local_knn_mean": bootstrap_metric_by_episode(
            y_eval,
            mse_eval,
            r_local,
            episode_eval,
            seed=BOOTSTRAP_SEED,
            n_boot=N_BOOT,
        ),
    }

    passed_by = [
        name
        for name, m in metrics.items()
        if m["auroc_failure_truth"]["ci95_low"] > 0.5
    ]
    conclusion_label = "positive" if passed_by else "negative_or_inconclusive"

    split_report = {}
    failure_rates = {}
    for name, mask in (("train", train_mask), ("calibration", cal_mask), ("eval", eval_mask)):
        split_report[name] = {
            "episodes": int(len(splits[name])),
            "rows": int(np.sum(mask)),
        }
        failure_rates[name] = float(np.mean(y[mask]))

    report = {
        "scientific_question": "世界模型在其 latent 局部无法线性恢复环境状态的地方失败",
        "protocol_status": "frozen_predeclared",
        "data": {
            "latent_path": str(LATENT_PATH),
            "row_builder": "_phase1c_gap_ledger.flatten_transition_rows",
            "valid_transition_rows": int(len(mse)),
            "episodes": n_ep,
            "embedding_dim": int(emb.shape[1]),
            "state_vector": "concat(pos_agent, pos_target)",
            "state_dim": int(state.shape[1]),
        },
        "seeds": {
            "numpy": NP_SEED,
            "split": 1701,
            "bootstrap": BOOTSTRAP_SEED,
        },
        "split": split_report,
        "failure_truth": {
            "definition": "mse > train split p75",
            "tau_train_p75": tau,
            "rates": failure_rates,
            "counts": {
                "train_positive": int(np.sum(y[train_mask])),
                "train_negative": int(np.sum(~y[train_mask])),
                "calibration_positive": int(np.sum(y[cal_mask])),
                "calibration_negative": int(np.sum(~y[cal_mask])),
                "eval_positive": int(np.sum(y_eval)),
                "eval_negative": int(np.sum(~y_eval)),
            },
        },
        "residual_definitions": {
            "global_linear": global_info,
            "local_knn_mean": local_info,
        },
        "metrics_eval_episode_bootstrap": metrics,
        "residual_summaries_eval": {
            "global_linear": residual_summary(r_global),
            "local_knn_mean": residual_summary(r_local),
        },
        "bootstrap": {
            "unit": "eval_episode",
            "n_boot": N_BOOT,
            "seed": BOOTSTRAP_SEED,
            "eval_episodes": int(len(np.unique(episode_eval))),
        },
        "context_not_recomputed": {
            "full_gap_head_auroc": FULL_GAP_HEAD_AUROC_REFERENCE,
            "source_note": "Quoted control context from prior published report; not recomputed here.",
        },
        "conclusion": {
            "label": conclusion_label,
            "positive_criterion": "positive iff any residual AUROC ci95_low > 0.5",
            "passed_by": passed_by,
        },
        "not_claimed": [
            "不声称因果关系。",
            "不声称全局可辨识性定理被检验。",
            "仅为 tworooms 单导出上的操作化关联检验。",
            "不声称结果可外推到其他环境、checkpoint、world seeds 或数据导出。",
            "不重算完整 gap head；AUROC 0.731 仅作对照语境引用。",
        ],
    }

    REPORT_DIR.mkdir(exist_ok=True)
    JSON_PATH.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    MD_PATH.write_text(render_markdown(report) + "\n", encoding="utf-8")

    print(f"tau_train_p75={tau:.12f}")
    print(json.dumps(report["conclusion"], indent=2, ensure_ascii=False))
    print(f"wrote {JSON_PATH}")
    print(f"wrote {MD_PATH}")


if __name__ == "__main__":
    main()

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
DEFAULT_EXPORT = REPORT_DIR / "aligned_state_generation_export.npz"
DEFAULT_JSON = REPORT_DIR / "state_generation_hard_cluster_coverage.json"
DEFAULT_MD = REPORT_DIR / "state_generation_hard_cluster_coverage.md"
HARD_DIAGNOSTIC_JSON = REPORT_DIR / "state_generation_hard_episode_diagnostic.json"
BOOTSTRAPS = 5000


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


def episode_groups(episode: np.ndarray) -> list[np.ndarray]:
    return [np.where(episode == ep)[0].astype(np.int64) for ep in np.unique(episode.astype(np.int64))]


def read_hard_episodes(path: Path) -> list[int]:
    report = json.loads(path.read_text(encoding="utf-8"))
    episodes = report.get("hard_episode_union", [])
    if not isinstance(episodes, list) or not episodes:
        raise RuntimeError("missing hard episode union")
    return [int(item) for item in episodes]


def fit_anchor_standardizer(train_x: np.ndarray, cal_x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    x = np.concatenate([train_x.astype(np.float64), cal_x.astype(np.float64)], axis=0)
    mean = np.mean(x, axis=0).astype(np.float32)
    scale = np.std(x, axis=0).astype(np.float32)
    scale[scale < 1.0e-6] = 1.0
    return mean, scale


def standardize_x(x: np.ndarray, mean: np.ndarray, scale: np.ndarray) -> np.ndarray:
    return ((x.astype(np.float32) - mean) / scale).astype(np.float32)


def episode_summary(x: np.ndarray, episode: np.ndarray, t0: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    rows = []
    eps = []
    for idxs in episode_groups(episode):
        ep = int(episode[idxs[0]])
        local_x = x[idxs].astype(np.float64)
        local_t = t0[idxs].astype(np.float64)
        mean = np.mean(local_x, axis=0)
        std = np.std(local_x, axis=0)
        scalar = np.asarray(
            [
                float(len(idxs)),
                float(np.mean(local_t)),
                float(np.std(local_t)),
                float(np.min(local_t)),
                float(np.max(local_t)),
            ],
            dtype=np.float64,
        )
        rows.append(np.concatenate([mean, std, scalar], axis=0))
        eps.append(ep)
    return np.asarray(eps, dtype=np.int64), np.vstack(rows).astype(np.float64)


def fit_episode_embedding(train_summary: np.ndarray, cal_summary: np.ndarray, *, dim: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    base = np.concatenate([train_summary, cal_summary], axis=0).astype(np.float64)
    mean = np.mean(base, axis=0)
    scale = np.std(base, axis=0)
    scale[scale < 1.0e-6] = 1.0
    z = (base - mean) / scale
    _, _, vt = np.linalg.svd(z, full_matrices=False)
    basis = vt[: min(dim, vt.shape[0])].T.astype(np.float64)
    return mean.astype(np.float64), scale.astype(np.float64), basis


def apply_episode_embedding(summary: np.ndarray, mean: np.ndarray, scale: np.ndarray, basis: np.ndarray) -> np.ndarray:
    return ((summary.astype(np.float64) - mean) / scale) @ basis


def fit_kmeans(x: np.ndarray, *, k: int, seed: int, iterations: int = 80) -> np.ndarray:
    rng = np.random.default_rng(seed)
    centers = np.zeros((k, x.shape[1]), dtype=np.float64)
    first = int(rng.integers(0, len(x)))
    centers[0] = x[first]
    min_dist = np.sum((x - centers[0]) ** 2, axis=1)
    for c in range(1, k):
        total = float(np.sum(min_dist))
        if total <= 0.0:
            centers[c] = x[int(rng.integers(0, len(x)))]
            continue
        probs = min_dist / total
        idx = int(rng.choice(len(x), p=probs))
        centers[c] = x[idx]
        min_dist = np.minimum(min_dist, np.sum((x - centers[c]) ** 2, axis=1))
    for _ in range(iterations):
        labels = assign_clusters(x, centers)
        new_centers = centers.copy()
        for c in range(k):
            mask = labels == c
            if np.any(mask):
                new_centers[c] = np.mean(x[mask], axis=0)
        if float(np.max(np.abs(new_centers - centers))) < 1.0e-7:
            centers = new_centers
            break
        centers = new_centers
    return centers


def assign_clusters(x: np.ndarray, centers: np.ndarray) -> np.ndarray:
    dist = np.sum((x[:, None, :] - centers[None, :, :]) ** 2, axis=2)
    return np.argmin(dist, axis=1).astype(np.int64)


def row_episode_delta(base: dict[str, np.ndarray], score: np.ndarray) -> dict[int, float]:
    episode = base["episode"].astype(np.int64)
    depths = base["option_depths"].astype(np.int64)
    option_error = base["option_error"].astype(np.float64)
    mid = int(np.where(depths == 3)[0][0])
    chosen = structured.exact_budget_choice(episode, score.astype(np.float64), structured.DEPTHS).astype(np.int64)
    selected_error = option_error[np.arange(len(chosen)), chosen]
    uniform_error = option_error[:, mid]
    selected_steps = depths[chosen].astype(np.float64)
    out: dict[int, float] = {}
    for idxs in episode_groups(episode):
        ep = int(episode[idxs[0]])
        delta = float(np.sum(selected_error[idxs]) / np.sum(selected_steps[idxs]) - np.sum(uniform_error[idxs]) / (3.0 * len(idxs)))
        out[ep] = clean_float(delta)
    return out


def load_score_rows() -> tuple[dict[str, np.ndarray], dict[str, np.ndarray]]:
    best_seed = load_npz(REPORT_DIR / "state_generation_episode_allocation_seed_617_predictions.npz")
    rows: dict[str, np.ndarray] = {
        "episode_best_seed": best_seed["episode_allocation_score"].astype(np.float64),
        "episode_objective": load_npz(REPORT_DIR / "state_generation_episode_allocation_predictions.npz")[
            "episode_allocation_score"
        ].astype(np.float64),
        "seed_mean": load_npz(REPORT_DIR / "state_generation_episode_seed_ensemble_predictions.npz")[
            "mean_score"
        ].astype(np.float64),
        "episode_balanced": load_npz(REPORT_DIR / "state_generation_episode_balanced_predictions.npz")[
            "episode_balanced_score"
        ].astype(np.float64),
        "episode_regret": load_npz(REPORT_DIR / "state_generation_episode_regret_predictions.npz")[
            "episode_regret_score"
        ].astype(np.float64),
        "episode_dual_price": load_npz(REPORT_DIR / "state_generation_episode_dual_price_predictions.npz")[
            "dual_price_score"
        ].astype(np.float64),
    }
    return best_seed, rows


def percentile_rank(values: np.ndarray, observed: float, *, lower_is_more_extreme: bool) -> float:
    if lower_is_more_extreme:
        return clean_float(float((np.sum(values <= observed) + 1.0) / (len(values) + 1.0)))
    return clean_float(float((np.sum(values >= observed) + 1.0) / (len(values) + 1.0)))


def permutation_diagnostics(
    eval_eps: np.ndarray,
    eval_labels: np.ndarray,
    traincal_counts: dict[int, int],
    hard_episodes: list[int],
    *,
    seed: int,
) -> dict[str, Any]:
    hard = np.asarray([ep in set(hard_episodes) for ep in eval_eps], dtype=bool)
    hard_clusters = eval_labels[hard]
    non_hard_clusters = eval_labels[~hard]
    hard_coverage = np.asarray([traincal_counts[int(c)] for c in hard_clusters], dtype=np.float64)
    non_hard_coverage = np.asarray([traincal_counts[int(c)] for c in non_hard_clusters], dtype=np.float64)
    observed_mean_coverage_gap = clean_float(float(np.mean(hard_coverage) - np.mean(non_hard_coverage)))
    observed_unique_clusters = int(len(set(int(c) for c in hard_clusters)))
    observed_max_cluster_hard = int(max(np.sum(hard_clusters == c) for c in set(int(x) for x in eval_labels)))
    rng = np.random.default_rng(seed)
    n_hard = int(np.sum(hard))
    mean_gap_samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    unique_samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    max_cluster_samples = np.zeros(BOOTSTRAPS, dtype=np.float64)
    all_idx = np.arange(len(eval_eps))
    cluster_counts = {int(c): int(np.sum(eval_labels == c)) for c in set(int(x) for x in eval_labels)}
    for i in range(BOOTSTRAPS):
        pick = rng.choice(all_idx, size=n_hard, replace=False)
        mask = np.zeros(len(eval_eps), dtype=bool)
        mask[pick] = True
        pick_clusters = eval_labels[mask]
        rest_clusters = eval_labels[~mask]
        pick_cov = np.asarray([traincal_counts[int(c)] for c in pick_clusters], dtype=np.float64)
        rest_cov = np.asarray([traincal_counts[int(c)] for c in rest_clusters], dtype=np.float64)
        mean_gap_samples[i] = float(np.mean(pick_cov) - np.mean(rest_cov))
        unique_samples[i] = float(len(set(int(c) for c in pick_clusters)))
        max_cluster_samples[i] = float(max(np.sum(pick_clusters == c) for c in cluster_counts))
    return {
        "hard_mean_traincal_cluster_count": clean_float(float(np.mean(hard_coverage))),
        "non_hard_mean_traincal_cluster_count": clean_float(float(np.mean(non_hard_coverage))),
        "hard_minus_non_hard_traincal_count": observed_mean_coverage_gap,
        "coverage_gap_permutation_p_low": percentile_rank(
            mean_gap_samples, observed_mean_coverage_gap, lower_is_more_extreme=True
        ),
        "hard_unique_cluster_count": observed_unique_clusters,
        "unique_cluster_permutation_p_low": percentile_rank(
            unique_samples, float(observed_unique_clusters), lower_is_more_extreme=True
        ),
        "hard_max_cluster_count": observed_max_cluster_hard,
        "max_cluster_permutation_p_high": percentile_rank(
            max_cluster_samples, float(observed_max_cluster_hard), lower_is_more_extreme=False
        ),
    }


def write_markdown(path: Path, report: dict[str, Any]) -> None:
    lines = [
        "# State-Generation Hard-Cluster Coverage",
        "",
        f"- hard episodes: `{report['hard_episode_union']}`",
        f"- cluster count: `{report['cluster_count']}`",
        f"- coverage gap: `{report['permutation']['hard_minus_non_hard_traincal_count']:.6g}`",
        f"- compactness unique clusters: `{report['permutation']['hard_unique_cluster_count']}`",
        "",
        "| cluster | train+cal episodes | eval episodes | hard eval episodes | mean best-seed delta |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in report["clusters"]:
        lines.append(
            f"| {row['cluster']} | {row['traincal_episode_count']} | {row['eval_episode_count']} | "
            f"{row['hard_eval_episode_count']} | {row['mean_episode_best_seed_delta']:.6g} |"
        )
    lines.extend(["", "## Verdict", "", report["verdict"]])
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Diagnose whether hard eval episodes occupy feature-space coverage regimes")
    parser.add_argument("--export", default=str(DEFAULT_EXPORT))
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--md", default=str(DEFAULT_MD))
    parser.add_argument("--hard-diagnostic", default=str(HARD_DIAGNOSTIC_JSON))
    parser.add_argument("--clusters", type=int, default=12)
    parser.add_argument("--embed-dim", type=int, default=24)
    parser.add_argument("--seed", type=int, default=9059)
    args = parser.parse_args()

    data = load_npz(Path(args.export))
    hard_episodes = read_hard_episodes(Path(args.hard_diagnostic))
    mean, scale = fit_anchor_standardizer(data["train_x"], data["calibration_x"])
    split_summaries: dict[str, tuple[np.ndarray, np.ndarray]] = {}
    for split in ["train", "calibration", "eval"]:
        x = standardize_x(data[f"{split}_x"], mean, scale)
        eps, summary = episode_summary(x, data[f"{split}_episode"], data[f"{split}_t0"])
        split_summaries[split] = (eps, summary)
    emb_mean, emb_scale, basis = fit_episode_embedding(
        split_summaries["train"][1], split_summaries["calibration"][1], dim=args.embed_dim
    )
    train_emb = apply_episode_embedding(split_summaries["train"][1], emb_mean, emb_scale, basis)
    cal_emb = apply_episode_embedding(split_summaries["calibration"][1], emb_mean, emb_scale, basis)
    eval_emb = apply_episode_embedding(split_summaries["eval"][1], emb_mean, emb_scale, basis)
    traincal_emb = np.concatenate([train_emb, cal_emb], axis=0)
    centers = fit_kmeans(traincal_emb, k=args.clusters, seed=args.seed)
    train_labels = assign_clusters(train_emb, centers)
    cal_labels = assign_clusters(cal_emb, centers)
    eval_labels = assign_clusters(eval_emb, centers)
    eval_eps = split_summaries["eval"][0]
    traincal_labels = np.concatenate([train_labels, cal_labels], axis=0)
    traincal_counts = {cluster: int(np.sum(traincal_labels == cluster)) for cluster in range(args.clusters)}

    base, score_rows = load_score_rows()
    deltas_by_row = {name: row_episode_delta(base, score) for name, score in score_rows.items()}
    clusters = []
    hard_set = set(hard_episodes)
    for cluster in range(args.clusters):
        eval_mask = eval_labels == cluster
        cluster_eps = [int(ep) for ep in eval_eps[eval_mask]]
        hard_cluster_eps = [ep for ep in cluster_eps if ep in hard_set]
        best_seed_deltas = [deltas_by_row["episode_best_seed"][ep] for ep in cluster_eps]
        row_damage = {
            name: clean_float(float(np.mean([episode_delta[ep] for ep in cluster_eps]))) if cluster_eps else 0.0
            for name, episode_delta in deltas_by_row.items()
        }
        clusters.append(
            {
                "cluster": int(cluster),
                "train_episode_count": int(np.sum(train_labels == cluster)),
                "calibration_episode_count": int(np.sum(cal_labels == cluster)),
                "traincal_episode_count": int(traincal_counts[cluster]),
                "eval_episode_count": int(np.sum(eval_mask)),
                "hard_eval_episode_count": int(len(hard_cluster_eps)),
                "eval_episodes": cluster_eps,
                "hard_eval_episodes": hard_cluster_eps,
                "mean_episode_best_seed_delta": clean_float(float(np.mean(best_seed_deltas))) if best_seed_deltas else 0.0,
                "row_mean_episode_delta": row_damage,
            }
        )
    perm = permutation_diagnostics(eval_eps, eval_labels, traincal_counts, hard_episodes, seed=args.seed + 33)
    hard_clusters = sorted(set(int(eval_labels[np.where(eval_eps == ep)[0][0]]) for ep in hard_episodes))
    hard_cluster_rows = [row for row in clusters if int(row["cluster"]) in hard_clusters]
    concentrated = int(perm["hard_unique_cluster_count"]) <= max(3, len(hard_episodes) // 2)
    undercovered = float(perm["hard_minus_non_hard_traincal_count"]) < 0.0
    verdict = (
        "Pre-label episode summaries make the hard episodes partially visible as a cluster-transfer issue: "
        "the hard set occupies fewer clusters than a typical size-matched eval subset and has lower train/cal "
        "cluster coverage on average.  This supports hard-cluster objectives without using eval labels for training."
        if concentrated and undercovered
        else "Pre-label episode summaries do not by themselves cleanly expose the hard set as an under-covered compact cluster; "
        "the next objective must use richer invariant episode descriptors or causal perturbation features."
    )
    report = {
        "status": "ok",
        "schema_id": "bedc_jepa.state_generation_hard_cluster_coverage",
        "cluster_count": int(args.clusters),
        "embedding_dim": int(basis.shape[1]),
        "hard_episode_union": hard_episodes,
        "hard_cluster_count": int(len(hard_clusters)),
        "hard_clusters": hard_clusters,
        "clusters": clusters,
        "hard_cluster_rows": hard_cluster_rows,
        "permutation": perm,
        "verdict": verdict,
        "leakage_attestation": {
            "cluster_features": "train/cal/eval episode summaries of x and t0 only; x is pre-label carrier context plus predicted rollout-internal features",
            "cluster_fit": "k-means centers are fit only on train+cal episode summaries",
            "diagnostic_labels": "eval hard episode ids and option_error are used only after fixed cluster assignment for diagnostic accounting",
            "targets_not_used_for_cluster": ["option_error", "true_mv", "horizon_y", "next_target", "lewm_h1_mse"],
        },
        "not_claimed": ["allocation closure", "deployable hard-cluster policy", "eval-label-free training result"],
    }
    Path(args.json).write_text(json.dumps(clean_json(report), ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(Path(args.md), report)
    print(json.dumps(clean_json(report), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

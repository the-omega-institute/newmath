from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import numpy as np

from _phase1c_gap_ledger import (
    BOOTSTRAP_SEED,
    BOOTSTRAPS,
    MATCHED_RANDOM_SEED,
    PYTHON_SEED,
    auroc_rank,
    bootstrap_metrics_by_episode,
    fit_logistic_head,
    predict_logistic_head,
    split_episodes,
)


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT / "reports"


def fmt_ci(m: dict[str, float]) -> str:
    return f"{m['observed']:.4f} [{m['ci95_low']:.4f}, {m['ci95_high']:.4f}]"


def load_rows(npz_path: Path) -> tuple[dict[str, np.ndarray], dict[str, Any]]:
    data = dict(np.load(npz_path, allow_pickle=False))
    tm = data["transition_mask"].astype(bool)
    ep, t = np.where(tm)
    rows = {
        "episode": ep.astype(np.int64),
        "t": t.astype(np.int64),
        "emb": data["emb"][ep, t].astype(np.float64),
        "pred": data["pred"][ep, t].astype(np.float64),
        "mse": data["prediction_mse"][ep, t].astype(np.float64),
    }
    finite = np.isfinite(rows["emb"]).all(axis=1) & np.isfinite(rows["pred"]).all(axis=1) & np.isfinite(rows["mse"])
    rows = {k: v[finite] for k, v in rows.items()}
    meta = {
        "episodes": int(data["emb"].shape[0]),
        "valid_transitions": int(len(rows["episode"])),
        "latent_dim": int(data["emb"].shape[-1]),
    }
    for k in ("model_repo", "dataset_repo", "dataset_file", "prediction_mse_identity_max_abs"):
        if k in data:
            v = np.asarray(data[k])
            meta[k] = v.item() if v.shape == () else str(v)
    return rows, meta


def evaluate_env(env: str, run_lat: bool = False) -> dict[str, Any]:
    fail_report = REPORT_DIR / f"lewm_{env}_gap_ledger.json"
    npz_path = ROOT / f"{env}_latent_large.npz"
    if not npz_path.exists():
        if fail_report.exists():
            return json.loads(fail_report.read_text(encoding="utf-8"))
        report = {
            "env": env,
            "status": "fail_closed",
            "reason": "latent_missing",
            "sample_counts": {"episodes": 0, "valid_transitions": 0},
            "conclusion": {"claim": "data_unavailable"},
        }
        return report

    rows, meta = load_rows(npz_path)
    splits = split_episodes(meta["episodes"])
    masks = {name: np.isin(rows["episode"], eps) for name, eps in splits.items()}
    train_mask = masks["train"]
    eval_mask = masks["eval"]
    tau = float(np.percentile(rows["mse"][train_mask], 75))
    y = (rows["mse"] > tau).astype(np.int8)
    y_eval = y[eval_mask]
    eval_episode = rows["episode"][eval_mask]

    arms: dict[str, dict[str, Any]] = {}
    train_rate = float(y[train_mask].mean()) if int(train_mask.sum()) else 0.5
    vanilla = np.full(len(y), train_rate, dtype=np.float64)
    arms["vanilla"] = {
        "info": {"status": "constant", "train_base_rate": train_rate},
        "metrics_eval_episode_bootstrap": bootstrap_metrics_by_episode(
            y_eval, vanilla[eval_mask], vanilla[eval_mask], eval_episode, seed=BOOTSTRAP_SEED, n_boot=BOOTSTRAPS
        ),
    }

    head, info = fit_logistic_head(rows["emb"][train_mask], y[train_mask], steps=2500, lr=0.05, l2=1e-4)
    scores, _ = predict_logistic_head(head, rows["emb"])
    arms["learned_logistic_emb"] = {
        "info": info,
        "metrics_eval_episode_bootstrap": bootstrap_metrics_by_episode(
            y_eval, scores[eval_mask], scores[eval_mask], eval_episode, seed=BOOTSTRAP_SEED, n_boot=BOOTSTRAPS
        ),
    }

    rng = np.random.default_rng(MATCHED_RANDOM_SEED)
    y_perm = y.copy()
    train_idx = np.where(train_mask)[0]
    y_perm[train_idx] = y_perm[train_idx][rng.permutation(len(train_idx))]
    rhead, rinfo = fit_logistic_head(rows["emb"][train_mask], y_perm[train_mask], steps=2500, lr=0.05, l2=1e-4)
    rscores, _ = predict_logistic_head(rhead, rows["emb"])
    arms["matched_random_logistic_emb"] = {
        "info": rinfo | {"label_permutation_seed": MATCHED_RANDOM_SEED},
        "metrics_eval_episode_bootstrap": bootstrap_metrics_by_episode(
            y_eval, rscores[eval_mask], rscores[eval_mask], eval_episode, seed=BOOTSTRAP_SEED, n_boot=BOOTSTRAPS
        ),
    }

    fail_notes = []
    if len(y_eval) == 0:
        fail_notes.append("eval split has zero transitions")
    elif np.unique(y_eval).size < 2:
        fail_notes.append("eval split is single-class; AUROC is unidentifiable and reported by convention")

    learned_m = arms["learned_logistic_emb"]["metrics_eval_episode_bootstrap"]
    random_m = arms["matched_random_logistic_emb"]["metrics_eval_episode_bootstrap"]
    vanilla_m = arms["vanilla"]["metrics_eval_episode_bootstrap"]
    auroc_sep = learned_m["failure_detection_auroc"]["ci95_low"] > random_m["failure_detection_auroc"]["ci95_high"]
    uer_sep = learned_m["unlogged_error_rate"]["ci95_high"] < vanilla_m["unlogged_error_rate"]["ci95_low"]
    claim = "positive" if (auroc_sep and uer_sep and not fail_notes) else "negative_or_inconclusive"

    lat_result: dict[str, Any] = {"status": "not_run", "reason": "optional_time_budget"}
    if run_lat:
        try:
            from _lat_lewm_port import build_windows, train_arm
            from _lat_lewm_port import bootstrap_metrics_by_episode as lat_bootstrap

            data = dict(np.load(npz_path))
            lat_rows = build_windows(data)
            lat_masks = {name: np.isin(lat_rows["episode"], eps) for name, eps in splits.items()}
            lat_train = lat_masks["train"]
            lat_eval = lat_masks["eval"]
            lat_tau = float(np.percentile(lat_rows["mse"][lat_train], 75))
            lat_y = (lat_rows["mse"] > lat_tau).astype(np.int8)
            lat_train_rate = float(lat_y[lat_train].mean())
            lat_v = np.full(len(lat_y), lat_train_rate, dtype=np.float64)
            lat_l, lat_linfo = train_arm(
                lat_rows, lat_train, lat_y, seed=PYTHON_SEED, dynamics_weight=1.0, label_permutation_seed=None
            )
            lat_r, lat_rinfo = train_arm(
                lat_rows,
                lat_train,
                lat_y,
                seed=PYTHON_SEED,
                dynamics_weight=1.0,
                label_permutation_seed=MATCHED_RANDOM_SEED,
            )
            ye = lat_y[lat_eval]
            ee = lat_rows["episode"][lat_eval]
            vm = lat_bootstrap(ye, lat_v[lat_eval], ee, seed=BOOTSTRAP_SEED, n_boot=BOOTSTRAPS)
            lm = lat_bootstrap(ye, lat_l[lat_eval], ee, seed=BOOTSTRAP_SEED, n_boot=BOOTSTRAPS)
            rm = lat_bootstrap(ye, lat_r[lat_eval], ee, seed=BOOTSTRAP_SEED, n_boot=BOOTSTRAPS)
            lat_auroc = lm["failure_detection_auroc"]["ci95_low"] > rm["failure_detection_auroc"]["ci95_high"]
            lat_uer = lm["unlogged_error_rate"]["ci95_high"] < vm["unlogged_error_rate"]["ci95_low"]
            lat_result = {
                "status": "run",
                "tau_err_train_p75": lat_tau,
                "arms": {
                    "vanilla": {"metrics_eval_episode_bootstrap": vm},
                    "lat_learned": {"info": lat_linfo, "metrics_eval_episode_bootstrap": lm},
                    "lat_matched_random": {"info": lat_rinfo, "metrics_eval_episode_bootstrap": rm},
                },
                "conclusion": {
                    "claim": "positive" if lat_auroc and lat_uer else "negative_or_inconclusive",
                    "auroc_ci_separated_from_matched_random": bool(lat_auroc),
                    "uer_ci_separated_from_vanilla": bool(lat_uer),
                },
            }
        except Exception as exc:
            lat_result = {"status": "fail_closed", "reason": repr(exc), "exception_type": type(exc).__name__}

    report = {
        "env": env,
        "status": "evaluated",
        "protocol": {
            "split_seed": 1701,
            "tau": "train prediction_mse p75",
            "bootstrap_seed": BOOTSTRAP_SEED,
            "bootstraps": BOOTSTRAPS,
            "bootstrap_unit": "eval episodes",
            "features": "emb only",
            "matched_random": "same logistic head with train labels permuted",
            "vanilla": "constant train base rate",
            "claim_criteria": [
                "learned AUROC ci95_low > matched-random AUROC ci95_high",
                "learned UER ci95_high < vanilla UER ci95_low",
            ],
        },
        "sample_counts": meta,
        "splits": {name: {"episodes": int(len(eps)), "transitions": int(masks[name].sum())} for name, eps in splits.items()},
        "failure_truth": {
            "definition": "prediction_mse > train_split_p75",
            "tau_err_train_p75": tau,
            "train_failure_rate": float(y[train_mask].mean()),
            "eval_failure_rate": float(y_eval.mean()) if len(y_eval) else float("nan"),
        },
        "arms": arms,
        "lat_port_optional": lat_result,
        "conclusion": {
            "claim": claim,
            "learned_auroc_ci_low_gt_matched_ci_high": bool(auroc_sep),
            "learned_uer_ci_high_lt_vanilla_ci_low": bool(uer_sep),
            "fail_closed_notes": fail_notes,
        },
    }
    return report


def write_report(env: str, report: dict[str, Any]) -> None:
    REPORT_DIR.mkdir(exist_ok=True)
    (REPORT_DIR / f"lewm_{env}_gap_ledger.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    sc = report.get("sample_counts", {})
    arms = report.get("arms", {})
    learned = arms.get("learned_logistic_emb", {}).get("metrics_eval_episode_bootstrap", {})
    random = arms.get("matched_random_logistic_emb", {}).get("metrics_eval_episode_bootstrap", {})
    vanilla = arms.get("vanilla", {}).get("metrics_eval_episode_bootstrap", {})
    lines = [f"# LeWM {env} Cross-Env Gap Ledger", ""]
    lines.append(f"- status: {report.get('status')}")
    lines.append(f"- claim: {report.get('conclusion', {}).get('claim')}")
    lines.append(f"- episodes: {sc.get('episodes', 0)}; transitions: {sc.get('valid_transitions', 0)}")
    if report.get("status") == "evaluated":
        lines.append(f"- tau: {report['failure_truth']['tau_err_train_p75']:.8f}")
        lines.append("")
        lines.append("| arm | AUROC [CI] | UER [CI] |")
        lines.append("|---|---:|---:|")
        lines.append(
            f"| learned_logistic_emb | {fmt_ci(learned['failure_detection_auroc'])} | "
            f"{fmt_ci(learned['unlogged_error_rate'])} |"
        )
        lines.append(
            f"| matched_random_logistic_emb | {fmt_ci(random['failure_detection_auroc'])} | "
            f"{fmt_ci(random['unlogged_error_rate'])} |"
        )
        lines.append(
            f"| vanilla | {fmt_ci(vanilla['failure_detection_auroc'])} | "
            f"{fmt_ci(vanilla['unlogged_error_rate'])} |"
        )
    else:
        lines.append(f"- reason: {report.get('reason')}")
        lines.append(f"- detail: {report.get('detail', '')}")
    (REPORT_DIR / f"lewm_{env}_gap_ledger.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def summarize(envs: list[str]) -> dict[str, Any]:
    rows = []
    for env in envs:
        p = REPORT_DIR / f"lewm_{env}_gap_ledger.json"
        if not p.exists():
            rows.append({"env": env, "status": "missing_report", "claim": "data_unavailable"})
            continue
        r = json.loads(p.read_text(encoding="utf-8"))
        row: dict[str, Any] = {
            "env": env,
            "status": r.get("status"),
            "episodes": r.get("sample_counts", {}).get("episodes", 0),
            "transitions": r.get("sample_counts", {}).get("valid_transitions", 0),
            "claim": r.get("conclusion", {}).get("claim"),
        }
        if r.get("status") == "evaluated":
            arms = r["arms"]
            for key, arm in [
                ("learned", arms["learned_logistic_emb"]),
                ("matched", arms["matched_random_logistic_emb"]),
                ("vanilla", arms["vanilla"]),
            ]:
                m = arm["metrics_eval_episode_bootstrap"]
                row[f"{key}_auroc"] = m["failure_detection_auroc"]
                row[f"{key}_uer"] = m["unlogged_error_rate"]
            row["tau"] = r["failure_truth"]["tau_err_train_p75"]
        else:
            row["reason"] = r.get("reason")
            row["detail"] = r.get("detail")
        rows.append(row)
    summary = {"envs": rows}
    (REPORT_DIR / "lewm_cross_env_replication.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")

    lines = ["# LeWM Cross-Env Replication", "", "| env | episodes | transitions | learned AUROC [CI] | matched [CI] | UER before -> after | claim |"]
    lines.append("|---|---:|---:|---:|---:|---:|---|")
    for row in rows:
        if "learned_auroc" in row:
            u0 = row["vanilla_uer"]
            u1 = row["learned_uer"]
            lines.append(
                f"| {row['env']} | {row['episodes']} | {row['transitions']} | "
                f"{fmt_ci(row['learned_auroc'])} | {fmt_ci(row['matched_auroc'])} | "
                f"{fmt_ci(u0)} -> {fmt_ci(u1)} | {row['claim']} |"
            )
        else:
            lines.append(
                f"| {row['env']} | {row.get('episodes', 0)} | {row.get('transitions', 0)} | n/a | n/a | n/a | "
                f"{row.get('claim', 'data_unavailable')} ({row.get('reason', row.get('status'))}) |"
            )
    (REPORT_DIR / "lewm_cross_env_replication.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--env", choices=["pusht", "reacher", "cube", "all"], default="all")
    parser.add_argument("--run-lat", action="store_true")
    args = parser.parse_args()
    envs = ["pusht", "reacher", "cube"] if args.env == "all" else [args.env]
    for env in envs:
        report = evaluate_env(env, run_lat=args.run_lat)
        write_report(env, report)
    print(json.dumps(summarize(["pusht", "reacher", "cube"]), indent=2))


if __name__ == "__main__":
    main()

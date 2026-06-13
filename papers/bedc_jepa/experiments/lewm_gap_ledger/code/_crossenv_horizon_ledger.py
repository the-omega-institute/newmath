from __future__ import annotations

import json
import math
import os
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch
from huggingface_hub import hf_hub_download

from lewm_latent_probe import build_model, load_checkpoint
from _g2n_horizon_labels import (
    ANCHOR_TOL,
    HISTORY_SIZE,
    MAX_CLEAN_H,
    QUANTILES,
    ROLL_BATCH,
    build_split_anchors,
    clean_h1_anchor_delta,
    compute_labels,
    compute_tau,
    rollout_predictions,
)
from _g2n_native_ledger import (
    BATCH,
    BOOTSTRAP_SEED,
    BOOTSTRAPS,
    D_MODEL,
    EPOCHS,
    FFN_DIM,
    HORIZONS,
    LR,
    MAX_FUTURE_TOKENS,
    N_HEADS,
    N_LAYERS,
    PYTHON_SEED,
    TORCH_SEED,
    WINDOW,
    build_clean_examples,
    evaluate_clean,
    predict_logits,
    train_arm,
)
from _phase1c_gap_ledger import split_episodes


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT / "reports"
JSON_PATH = REPORT_DIR / "lewm_crossenv_horizon_ledger.json"
MD_PATH = REPORT_DIR / "lewm_crossenv_horizon_ledger.md"

ENVS = ("reacher", "cube", "pusht")
MODEL_REPOS = {
    "reacher": "quentinll/lewm-reacher",
    "cube": "quentinll/lewm-cube",
    "pusht": "quentinll/lewm-pusht",
}
TEACHER_REFERENCE_H1_AUROC = {
    "reacher": 0.662,
    "cube": 0.610,
    "pusht": 1.000,
}
PRIMARY_Q = 75


def clean_json(v: Any) -> Any:
    if isinstance(v, dict):
        return {str(k): clean_json(val) for k, val in v.items()}
    if isinstance(v, (list, tuple)):
        return [clean_json(val) for val in v]
    if isinstance(v, np.ndarray):
        return clean_json(v.tolist())
    if isinstance(v, (np.integer,)):
        return int(v)
    if isinstance(v, (np.floating,)):
        v = float(v)
    if isinstance(v, float) and not math.isfinite(v):
        return None
    return v


def require_inputs() -> None:
    required = [
        ROOT / "reacher_latent_large.npz",
        ROOT / "cube_latent_large.npz",
        ROOT / "pusht_latent_large.npz",
        ROOT / "_g2n_horizon_labels.py",
        ROOT / "_g2n_native_ledger.py",
        REPORT_DIR / "lewm_cross_env_replication.json",
    ]
    missing = [str(p) for p in required if not p.exists()]
    if missing:
        raise SystemExit("missing required precursor(s): " + ", ".join(missing))


def load_npz_dict(path: Path) -> dict[str, np.ndarray]:
    raw = np.load(path, allow_pickle=False)
    return {k: raw[k] for k in raw.files}


def load_predictor(env: str, device: torch.device) -> tuple[Any, dict[str, Any], str, str]:
    repo = MODEL_REPOS[env]
    checkpoint_path = hf_hub_download(repo, "weights.pt", repo_type="model")
    config_path = hf_hub_download(repo, "config.json", repo_type="model")
    with open(config_path, "r", encoding="utf-8") as f:
        config = json.load(f)
    model = build_model(config)
    load_checkpoint(model, checkpoint_path)
    model.to(device).eval().requires_grad_(False)
    return model, config, checkpoint_path, config_path


def split_base_rates(parts: dict[str, dict[str, np.ndarray]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    q_to_idx = {int(q): i for i, q in enumerate(QUANTILES)}
    for h in HORIZONS:
        h_idx = int(h) - 1
        q_idx = q_to_idx[PRIMARY_Q]
        row: dict[str, Any] = {"h": int(h), "q": PRIMARY_Q}
        for split in ("train", "calibration", "eval"):
            valid = parts[split]["valid"][:, h_idx]
            y = parts[split]["y"][:, h_idx, q_idx].astype(bool)
            row[f"{split}_failure_base_rate"] = float(y[valid].mean()) if np.any(valid) else float("nan")
            row[f"{split}_valid_n"] = int(valid.sum())
        rows.append(row)
    return rows


def tau_table(tau: np.ndarray) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for h_idx in range(tau.shape[0]):
        out.append(
            {
                "h": h_idx + 1,
                "q50": float(tau[h_idx, 0]),
                "q75": float(tau[h_idx, 1]),
                "q90": float(tau[h_idx, 2]),
            }
        )
    return out


def anchor_counts(splits: dict[str, np.ndarray], parts: dict[str, dict[str, np.ndarray]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for split, part in parts.items():
        row: dict[str, Any] = {
            "episodes": int(len(splits[split])),
            "anchors": int(len(part["anchors"])),
        }
        for h in HORIZONS:
            row[f"valid_h{h}"] = int(part["valid"][:, int(h) - 1].sum())
        out[split] = row
    return out


def write_label_npz(env: str, data: dict[str, np.ndarray], model: Any, device: torch.device) -> dict[str, Any]:
    history_size = int(np.asarray(data["history_size"]).item())
    if history_size != HISTORY_SIZE:
        raise RuntimeError(f"{env}: expected history_size={HISTORY_SIZE}, got {history_size}")

    splits = split_episodes(data["emb"].shape[0])
    clean_parts: dict[str, dict[str, np.ndarray]] = {}
    h1_delta_by_split: dict[str, float] = {}
    npz_out: dict[str, np.ndarray] = {
        "horizons": np.arange(1, MAX_CLEAN_H + 1, dtype=np.int64),
        "quantiles": QUANTILES.copy(),
        "env": np.asarray(env),
    }

    for split in ("train", "calibration", "eval"):
        anchors = build_split_anchors(data, splits[split])
        print(f"[labels] env={env} split={split} anchors={len(anchors)}", flush=True)
        part = rollout_predictions(model, data, anchors, device=device, max_h=MAX_CLEAN_H, batch_size=ROLL_BATCH)
        h1_delta = clean_h1_anchor_delta(data, anchors, part["err_at_h"][:, 0])
        h1_delta_by_split[split] = h1_delta
        if not np.isfinite(h1_delta) or h1_delta >= ANCHOR_TOL:
            raise RuntimeError(
                f"{env}: h=1 anchor failed for split={split}; "
                f"max_abs_delta={h1_delta:.9g}, tolerance={ANCHOR_TOL:.9g}"
            )
        clean_parts[split] = {"anchors": anchors, **part}

    tau = compute_tau(clean_parts["train"]["err_at_h"], clean_parts["train"]["valid"], MAX_CLEAN_H)
    for split, part in clean_parts.items():
        part["y"] = compute_labels(part["err_at_h"], part["valid"], tau, MAX_CLEAN_H)
        npz_out[f"{split}_anchor_ep_t0"] = part["anchors"].astype(np.int64)
        npz_out[f"{split}_valid"] = part["valid"].astype(bool)
        npz_out[f"{split}_err_at_h"] = part["err_at_h"].astype(np.float64)
        npz_out[f"{split}_mean_err_to_h"] = part["mean_err_to_h"].astype(np.float64)
        npz_out[f"{split}_pred_z"] = part["pred_z"].astype(np.float32)
        npz_out[f"{split}_y"] = part["y"].astype(np.int8)
    npz_out["tau"] = tau.astype(np.float64)

    path = REPORT_DIR / f"crossenv_horizon_labels_{env}.npz"
    np.savez_compressed(path, **npz_out)

    return {
        "path": str(path),
        "splits": splits,
        "parts": clean_parts,
        "tau": tau,
        "anchor_check": {
            "tolerance": ANCHOR_TOL,
            "clean_h1_prediction_mse_max_abs_delta": float(max(h1_delta_by_split.values())),
            "clean_h1_prediction_mse_by_split": h1_delta_by_split,
        },
        "tau_table": tau_table(tau),
        "failure_base_rates_q75": split_base_rates(clean_parts),
        "anchor_counts": anchor_counts(splits, clean_parts),
    }


def ci_overlap(a: dict[str, float], b: dict[str, float] | None) -> bool | None:
    if b is None:
        return None
    return not (float(a["ci95_high"]) < float(b["ci95_low"]) or float(b["ci95_high"]) < float(a["ci95_low"]))


def get_reference_probe_rows(replication: dict[str, Any]) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for row in replication.get("envs", []):
        env = str(row.get("env"))
        if env in ENVS:
            out[env] = {
                "source": "reports/lewm_cross_env_replication.json learned_logistic_emb h=1 q75 row",
                "failure_detection_auroc": row.get("learned_auroc"),
                "unlogged_error_rate": row.get("learned_uer"),
                "rounded_reference_auroc_declared_in_prompt": TEACHER_REFERENCE_H1_AUROC[env],
            }
    return out


def run_native(env: str, data: dict[str, np.ndarray], labels_path: str) -> dict[str, Any]:
    labels = np.load(labels_path, allow_pickle=False)
    train_ex = build_clean_examples(data, labels, "train", None)
    eval_ex = build_clean_examples(data, labels, "eval", None)

    print(f"[train] env={env} arm=E rows={len(train_ex['episode'])}", flush=True)
    model, info, norm = train_arm(
        "E",
        train_ex,
        include_future=True,
        action_only=False,
        use_teacher=False,
        use_unlogged=False,
        use_budget=False,
        label_permutation_seed=None,
    )
    logits = predict_logits(model, eval_ex, norm)
    return {
        "info": info,
        "clean_eval_q75_by_h": evaluate_clean(logits, eval_ex),
    }


def summarize_native_by_h(native_eval: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for h in HORIZONS:
        key = f"h{h}_q{PRIMARY_Q}"
        m = native_eval[key]
        auroc = m["failure_detection_auroc"]
        uer = m["unlogged_error_rate"]
        rows.append(
            {
                "h": int(h),
                "q": PRIMARY_Q,
                "auroc": auroc,
                "uer": uer,
                "detectable": bool(float(auroc["ci95_low"]) > 0.5),
            }
        )
    return rows


def env_conclusion(rows: list[dict[str, Any]]) -> str:
    detected = [f"h={r['h']}" for r in rows if r["detectable"]]
    if not detected:
        return "native horizon ledger was not detectable at q=75 under the preregistered CI rule"
    if len(detected) == len(rows):
        return "native horizon ledger was detectable for all preregistered horizons at q=75"
    return "native horizon ledger was detectable at " + ", ".join(detected) + " at q=75"


def fmt_metric(m: dict[str, float]) -> str:
    return f"{m['observed']:.3f} [{m['ci95_low']:.3f}, {m['ci95_high']:.3f}]"


def write_markdown(report: dict[str, Any]) -> None:
    lines = [
        "# Cross-Env Native Horizon Ledger",
        "",
        f"- status: {report['status']}",
        "- no OOD arm claimed: three-environment pipeline has no perturbation/OOD evaluation path in this protocol",
        f"- seeds: numpy={PYTHON_SEED}, torch={TORCH_SEED}, split=1701, bootstrap={BOOTSTRAP_SEED}",
        f"- arm: E only; epochs={EPOCHS}, batch={BATCH}, lr={LR}, d_model={D_MODEL}",
        "",
        "| env | h=1 AUROC | h=3 AUROC | h=5 AUROC | h=10 AUROC | h=1 probe AUROC | conclusion |",
        "|---|---:|---:|---:|---:|---:|---|",
    ]
    for env_row in report["envs"]:
        by_h = {int(r["h"]): r for r in env_row["native_horizon_q75"]}
        ref = env_row["teacher_reference_h1"]
        probe = ref.get("failure_detection_auroc")
        probe_s = fmt_metric(probe) if isinstance(probe, dict) else f"{ref['rounded_reference_auroc_declared_in_prompt']:.3f}"
        lines.append(
            f"| {env_row['env']} | "
            f"{fmt_metric(by_h[1]['auroc'])} | {fmt_metric(by_h[3]['auroc'])} | "
            f"{fmt_metric(by_h[5]['auroc'])} | {fmt_metric(by_h[10]['auroc'])} | "
            f"{probe_s} | {env_row['conclusion']} |"
        )
    lines.append("")

    for env_row in report["envs"]:
        lines.extend(
            [
                f"## {env_row['env']}",
                "",
                f"- label file: `{env_row['labels']['path']}`",
                f"- h=1 anchor max |delta|: `{env_row['labels']['anchor_check']['clean_h1_prediction_mse_max_abs_delta']:.9g}`",
                f"- train/eval anchors: `{env_row['labels']['anchor_counts']['train']['anchors']}` / `{env_row['labels']['anchor_counts']['eval']['anchors']}`",
                "",
                "| h | tau q50 | tau q75 | tau q90 | eval base rate q75 | detectable |",
                "|---:|---:|---:|---:|---:|---|",
            ]
        )
        tau_by_h = {int(r["h"]): r for r in env_row["labels"]["tau_table"]}
        base_by_h = {int(r["h"]): r for r in env_row["labels"]["failure_base_rates_q75"]}
        native_by_h = {int(r["h"]): r for r in env_row["native_horizon_q75"]}
        for h in HORIZONS:
            tt = tau_by_h[int(h)]
            br = base_by_h[int(h)]
            nr = native_by_h[int(h)]
            lines.append(
                f"| {h} | {tt['q50']:.8g} | {tt['q75']:.8g} | {tt['q90']:.8g} | "
                f"{br['eval_failure_base_rate']:.3f} | {str(nr['detectable']).lower()} |"
            )
        lines.append("")
    MD_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    require_inputs()
    np.random.seed(PYTHON_SEED)
    torch.manual_seed(TORCH_SEED)
    torch.set_num_threads(int(os.environ.get("G2N_TORCH_THREADS", "4")))
    REPORT_DIR.mkdir(exist_ok=True)

    replication = json.loads((REPORT_DIR / "lewm_cross_env_replication.json").read_text(encoding="utf-8"))
    refs = get_reference_probe_rows(replication)
    device = torch.device("cpu")

    env_reports: list[dict[str, Any]] = []
    started = time.perf_counter()
    for env in ENVS:
        print(f"[env] {env}", flush=True)
        data = load_npz_dict(ROOT / f"{env}_latent_large.npz")
        model, config, checkpoint_path, config_path = load_predictor(env, device)
        label_info = write_label_npz(env, data, model, device)
        del model

        native = run_native(env, data, label_info["path"])
        native_rows = summarize_native_by_h(native["clean_eval_q75_by_h"])
        teacher_ref = refs.get(
            env,
            {
                "source": "prompt frozen reference only",
                "failure_detection_auroc": None,
                "unlogged_error_rate": None,
                "rounded_reference_auroc_declared_in_prompt": TEACHER_REFERENCE_H1_AUROC[env],
            },
        )
        h1_native = native_rows[0]["auroc"]
        h1_probe = teacher_ref.get("failure_detection_auroc")
        comparison = {
            "native_h1_auroc": h1_native,
            "teacher_probe_h1_auroc": h1_probe,
            "teacher_probe_prompt_reference": TEACHER_REFERENCE_H1_AUROC[env],
            "ci_overlap": ci_overlap(h1_native, h1_probe if isinstance(h1_probe, dict) else None),
        }
        env_reports.append(
            {
                "env": env,
                "status": "evaluated",
                "model": {
                    "repo": MODEL_REPOS[env],
                    "checkpoint_path": checkpoint_path,
                    "config_path": config_path,
                    "config_history_size": int(config["predictor"]["num_frames"]),
                    "npz_history_size": int(np.asarray(data["history_size"]).item()),
                },
                "sample_counts": {
                    "episodes": int(data["emb"].shape[0]),
                    "valid_transitions": int(data["transition_mask"].astype(bool).sum()),
                    "latent_dim": int(data["emb"].shape[-1]),
                    "action_dim": int(data["action"].shape[-1]),
                },
                "labels": {k: v for k, v in label_info.items() if k not in ("splits", "parts", "tau")},
                "native_arm_E": native["info"],
                "native_horizon_q75": native_rows,
                "teacher_reference_h1": teacher_ref,
                "h1_native_vs_teacher_probe": comparison,
                "conclusion": env_conclusion(native_rows),
                "not_claimed": [
                    "No OOD arm is claimed: reacher/cube/pusht have no perturbation pipeline in this protocol.",
                    "Only single-export episode bootstrap is reported.",
                    "Teacher probe row is a frozen reference/subject selector, not a distillation target.",
                ],
            }
        )

    report = {
        "status": "ok",
        "schema_id": "crossenv.native_horizon_ledger",
        "protocol": {
            "scientific_question": (
                "Whether horizon-conditioned native ledger supervision transfers across reacher/cube/pusht "
                "after the tworooms result."
            ),
            "seeds": {"numpy": PYTHON_SEED, "torch": TORCH_SEED, "split": 1701, "bootstrap": BOOTSTRAP_SEED},
            "bootstrap_resamples": BOOTSTRAPS,
            "bootstrap_unit": "eval episodes",
            "primary_quantile": PRIMARY_Q,
            "horizons": list(HORIZONS),
            "quantiles": [int(q) for q in QUANTILES.tolist()],
            "arm": "E",
            "native_supervision": "pure horizon labels; no distillation; no rank/budget/unlogged losses",
            "architecture": {
                "past_tokens": WINDOW,
                "max_future_tokens": MAX_FUTURE_TOKENS,
                "d_model": D_MODEL,
                "heads": N_HEADS,
                "layers": N_LAYERS,
                "ffn_dim": FFN_DIM,
                "outputs": [f"h{h}_q{q}" for h in HORIZONS for q in QUANTILES],
            },
            "optimization": {"epochs": EPOCHS, "batch": BATCH, "lr": LR, "optimizer": "AdamW"},
            "detectable_rule": "per horizon, q=75 AUROC ci95_low > 0.5",
            "anchor_rule": f"h=1 generated rollout MSE must match npz prediction_mse with max |delta| < {ANCHOR_TOL}",
        },
        "precursors": {
            "replication_json": str(REPORT_DIR / "lewm_cross_env_replication.json"),
            "label_script_reused": str(ROOT / "_g2n_horizon_labels.py"),
            "native_script_reused": str(ROOT / "_g2n_native_ledger.py"),
        },
        "envs": env_reports,
        "outputs": {
            "json": str(JSON_PATH),
            "md": str(MD_PATH),
            "label_npz": {env: str(REPORT_DIR / f"crossenv_horizon_labels_{env}.npz") for env in ENVS},
        },
        "wall_time_seconds": round(time.perf_counter() - started, 2),
        "not_claimed": [
            "No OOD arm is claimed: this three-environment pipeline has no perturbation/OOD evaluation path.",
            "No hyperparameter tuning was performed.",
        ],
    }
    JSON_PATH.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(report)
    print(f"wrote {JSON_PATH}", flush=True)
    print(f"wrote {MD_PATH}", flush=True)


if __name__ == "__main__":
    main()

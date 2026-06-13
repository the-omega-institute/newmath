from __future__ import annotations

import json
import os
import time
from collections import defaultdict
from pathlib import Path
from typing import Any

import numpy as np
import torch
import torch.nn as nn

import _g2n_native_ledger as g2n
from _allocation_bridge import (
    ANCHOR_TOL,
    BOOTSTRAPS,
    BOOTSTRAP_SEED,
    E_H1_AUROC_TARGET,
    PYTHON_SEED,
    SPLIT_SEED,
    TARGET_H,
    TARGET_H_INDEX,
    TORCH_SEED,
    budget_eval_for_score,
    pairwise_logistic_loss,
    within_episode_spearman,
)
from _lat_lewm_port import NPZ_PATH, REPORT_DIR
from _ledger_gated_rollout import (
    HIGH_H,
    LOW_H,
    MID_H,
    UNIFORM_H,
    allocation_uniform,
    summarize_allocation,
)
from _phase2a_brittleness_gap import clean_json


ROOT = Path(__file__).resolve().parent
CLEAN_LABELS = REPORT_DIR / "g2n_labels_clean.npz"
ALLOCATION_BRIDGE = ROOT / "_allocation_bridge.py"
ALLOCATION_RHO_THRESHOLD = ROOT / "_allocation_rho_threshold.py"
NATIVE_LEDGER = ROOT / "_g2n_native_ledger.py"
JSON_PATH = REPORT_DIR / "lewm_alloc_rich_input.json"
MD_PATH = REPORT_DIR / "lewm_alloc_rich_input.md"

ORACLE_DELTA_TARGET = -0.015867561326231905
R1_FAILURE_BASELINE_RHO = 0.51
RHO_POSITIVE_THRESHOLD = 0.58
RICH_H = 5


class RichRanker(nn.Module):
    def __init__(self, in_dim: int) -> None:
        super().__init__()
        self.net = nn.Sequential(
            nn.Linear(in_dim, 128),
            nn.ReLU(),
            nn.Linear(128, 64),
            nn.ReLU(),
            nn.Linear(64, 1),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x).squeeze(-1)


def require_inputs() -> None:
    missing = [
        p
        for p in (CLEAN_LABELS, ALLOCATION_BRIDGE, ALLOCATION_RHO_THRESHOLD, NATIVE_LEDGER)
        if not p.exists()
    ]
    if missing:
        raise SystemExit("missing required precursor(s): " + ", ".join(str(p) for p in missing))


def write_stopped_report(status: str, reason: str, extra: dict[str, Any]) -> None:
    report = {
        "status": status,
        "reason": reason,
        "extra": extra,
        "not_claimed": [
            "stopped before testing rich-input allocation arms",
            "no positive or negative scientific claim is made from a failed anchor run",
        ],
    }
    JSON_PATH.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    lines = [
        "# LEWM Allocation Rich Input",
        "",
        f"- status: `{status}`",
        f"- stopped reason: {reason}",
    ]
    for k, v in extra.items():
        lines.append(f"- {k}: `{v}`")
    lines.extend(["", "## Not Claimed", ""])
    for item in report["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    MD_PATH.write_text("\n".join(lines), encoding="utf-8")


def build_base_examples(data: dict[str, np.ndarray], clean: np.lib.npyio.NpzFile, split: str) -> dict[str, np.ndarray]:
    return g2n.build_clean_examples(data, clean, split, None)


def fit_feature_norm(features: np.ndarray) -> dict[str, np.ndarray]:
    mean = features.mean(axis=0).astype(np.float32)
    std = (features.std(axis=0) + 1e-6).astype(np.float32)
    return {"mean": mean, "std": std}


def apply_feature_norm(features: np.ndarray, norm: dict[str, np.ndarray]) -> np.ndarray:
    return ((features - norm["mean"]) / norm["std"]).astype(np.float32)


def rich_feature_blocks(
    ex: dict[str, np.ndarray],
    ledger_logits: np.ndarray | None,
) -> dict[str, np.ndarray]:
    past = np.concatenate(
        [
            ex["past_z"].reshape(len(ex["episode"]), -1),
            ex["past_a"].reshape(len(ex["episode"]), -1),
        ],
        axis=1,
    ).astype(np.float32)
    pred = ex["future_z"][:, :RICH_H, :].reshape(len(ex["episode"]), -1).astype(np.float32)
    delta = (ex["future_z"][:, 1:RICH_H, :] - ex["future_z"][:, : RICH_H - 1, :]).reshape(
        len(ex["episode"]),
        -1,
    ).astype(np.float32)
    drift = np.linalg.norm(
        ex["future_z"][:, 1:RICH_H, :] - ex["future_z"][:, : RICH_H - 1, :],
        axis=2,
    ).astype(np.float32)
    blocks = {
        "past": past,
        "pred_z_trajectory": pred,
        "pred_z_step_deltas": delta,
        "drift_norms": drift,
    }
    if ledger_logits is not None:
        blocks["ledger_logits"] = ledger_logits.astype(np.float32)
    return blocks


def compose_features(blocks: dict[str, np.ndarray], arm: str) -> np.ndarray:
    if arm == "A1":
        keys = ("past", "pred_z_trajectory", "pred_z_step_deltas")
    elif arm == "A2":
        keys = ("past", "pred_z_trajectory", "pred_z_step_deltas", "ledger_logits")
    elif arm == "A3":
        keys = ("past", "pred_z_trajectory", "pred_z_step_deltas", "ledger_logits", "drift_norms")
    else:
        raise ValueError(f"unknown arm {arm}")
    return np.concatenate([blocks[k] for k in keys], axis=1).astype(np.float32)


def train_rich_ranker(
    name: str,
    x_all: np.ndarray,
    clean: np.lib.npyio.NpzFile,
) -> tuple[RichRanker, dict[str, Any], dict[str, np.ndarray]]:
    torch.manual_seed(TORCH_SEED)
    np.random.seed(PYTHON_SEED)

    valid = clean["train_valid"][:, TARGET_H_INDEX].astype(bool)
    x = x_all[valid].astype(np.float32)
    y = clean["train_mean_err_to_h"][valid, TARGET_H_INDEX].astype(np.float32)
    episode = clean["train_anchor_ep_t0"][valid, 0].astype(np.int64)
    norm = fit_feature_norm(x)
    xn = apply_feature_norm(x, norm)

    x_t = torch.from_numpy(xn)
    y_t = torch.from_numpy(y)
    ep_t = torch.from_numpy(episode)
    model = RichRanker(xn.shape[1])
    opt = torch.optim.AdamW(model.parameters(), lr=g2n.LR)
    generator = torch.Generator().manual_seed(TORCH_SEED)
    steps = 0
    t0 = time.perf_counter()
    model.train()
    for epoch in range(1, g2n.EPOCHS + 1):
        order = torch.randperm(len(y), generator=generator)
        for start in range(0, len(y), g2n.BATCH):
            idx = order[start : start + g2n.BATCH]
            score = model(x_t[idx])
            maybe_loss = pairwise_logistic_loss(score, y_t[idx], ep_t[idx])
            if maybe_loss is None:
                continue
            loss = maybe_loss
            if not torch.isfinite(loss):
                raise RuntimeError(f"non-finite loss in {name}")
            opt.zero_grad()
            loss.backward()
            opt.step()
            steps += 1
        if epoch == 1 or epoch % 5 == 0 or epoch == g2n.EPOCHS:
            print(f"[train] {name} epoch={epoch}/{g2n.EPOCHS} steps={steps}", flush=True)
    info = {
        "status": "trained",
        "objective": "within_episode_pairwise_logistic_ranking",
        "target": f"clean train mean_err_to_h[:, {TARGET_H_INDEX}] for h={TARGET_H}",
        "mlp": "Linear(input,128), ReLU, Linear(128,64), ReLU, Linear(64,1)",
        "epochs": g2n.EPOCHS,
        "batch": g2n.BATCH,
        "optimizer": "AdamW",
        "lr": g2n.LR,
        "optimizer_steps": int(steps),
        "wall_time_seconds": round(time.perf_counter() - t0, 2),
        "parameter_count": int(sum(p.numel() for p in model.parameters())),
        "train_rows": int(len(y)),
        "input_dim": int(xn.shape[1]),
    }
    return model.eval(), info, norm


def predict_rich_ranker(
    model: RichRanker,
    x_all: np.ndarray,
    norm: dict[str, np.ndarray],
    *,
    batch: int = 4096,
) -> np.ndarray:
    x = apply_feature_norm(x_all.astype(np.float32), norm)
    out = np.zeros(len(x), dtype=np.float64)
    with torch.no_grad():
        for lo in range(0, len(out), batch):
            hi = min(lo + batch, len(out))
            score = model(torch.from_numpy(x[lo:hi].astype(np.float32)))
            out[lo:hi] = score.detach().cpu().numpy().astype(np.float64)
    return out


def build_eval_budget(
    clean_eval_ex: dict[str, np.ndarray],
    clean: np.lib.npyio.NpzFile,
) -> tuple[list[dict[str, Any]], dict[int, list[int]], np.ndarray, np.ndarray, np.ndarray, dict[str, Any]]:
    valid_h5 = clean["eval_valid"][:, TARGET_H_INDEX].astype(bool)
    errors_h5 = clean["eval_err_at_h"][valid_h5, :TARGET_H].astype(np.float64)
    true_mean_h5 = clean["eval_mean_err_to_h"][valid_h5, TARGET_H_INDEX].astype(np.float64)
    anchors_arr = clean_eval_ex["anchor_ep_t0"][valid_h5]
    anchors = [
        {"episode": int(ep), "t0": int(t), "row_idx": int(i), "gap_score": 0.0}
        for i, (ep, t) in enumerate(anchors_arr)
    ]
    anchors_by_ep: dict[int, list[int]] = defaultdict(list)
    for i, anchor in enumerate(anchors):
        anchors_by_ep[int(anchor["episode"])].append(i)
    uniform_h = allocation_uniform(anchors_by_ep)
    uniform_alloc = summarize_allocation("uniform", uniform_h, errors_h5, anchors)
    return anchors, anchors_by_ep, errors_h5, true_mean_h5, valid_h5, uniform_alloc


def write_markdown(report: dict[str, Any]) -> None:
    lines = [
        "# LEWM Allocation Rich Input",
        "",
        f"- status: `{report['status']}`",
        f"- positive rule: {report['decision_rule']}",
        f"- E clean h=1 AUROC: `{report['anchors']['e_clean_h1_auroc']['observed']:.15f}` "
        f"(target `{report['anchors']['e_clean_h1_auroc']['target']:.15f}`)",
        f"- oracle delta: `{report['anchors']['oracle_delta']['observed']:.9f}` "
        f"(target `{report['anchors']['oracle_delta']['target']:.9f}`)",
        "",
        "## Three Arms",
        "",
        "| arm | input | rho | rho>=0.58 | delta vs uniform | 95% CI | oracle gap | verdict | rho > 0.51 baseline |",
        "|---|---|---:|---|---:|---:|---:|---|---|",
    ]
    for name in ("A1", "A2", "A3"):
        row = report["arms"][name]
        d = row["delta_vs_uniform"]
        lines.append(
            f"| `{name}` | {row['input_summary']} | {row['spearman']['episode_mean']:.6f} | "
            f"{'yes' if row['rho_pass'] else 'no'} | {d['observed']:.9f} | "
            f"[{d['ci95_low']:.9f}, {d['ci95_high']:.9f}] | {row['oracle_gap']:.9f} | "
            f"{row['verdict']} | {'yes' if row['beats_0p51_baseline'] else 'no'} |"
        )
    lines.extend(
        [
            "",
            "## Controls",
            "",
            "| control | rho | delta vs uniform | 95% CI |",
            "|---|---:|---:|---:|",
        ]
    )
    oracle = report["controls"]["oracle"]
    od = oracle["delta_vs_uniform"]
    lines.append(
        f"| `oracle` | {oracle['spearman']['episode_mean']:.6f} | {od['observed']:.9f} | "
        f"[{od['ci95_low']:.9f}, {od['ci95_high']:.9f}] |"
    )
    lines.extend(["", "## Interpretation", ""])
    for item in report["interpretation"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Not Claimed", ""])
    for item in report["not_claimed"]:
        lines.append(f"- {item}")
    lines.append("")
    MD_PATH.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    require_inputs()
    np.random.seed(PYTHON_SEED)
    torch.manual_seed(TORCH_SEED)
    torch.set_num_threads(int(os.environ.get("G2N_TORCH_THREADS", "4")))
    REPORT_DIR.mkdir(exist_ok=True)

    raw = np.load(NPZ_PATH)
    data = {k: raw[k] for k in raw.files}
    splits = g2n.split_episodes(data["emb"].shape[0])
    if SPLIT_SEED != 1701 or int(len(splits["eval"])) <= 0:
        raise SystemExit("split sanity failed")

    clean = np.load(CLEAN_LABELS)
    clean_train_ex = build_base_examples(data, clean, "train")
    clean_eval_ex = build_base_examples(data, clean, "eval")

    print("[anchor] train frozen G2N arm E", flush=True)
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
    e_train_logits = g2n.predict_logits(e_model, clean_train_ex, e_norm)
    e_eval_logits = g2n.predict_logits(e_model, clean_eval_ex, e_norm)
    e_eval = g2n.evaluate_clean(e_eval_logits, clean_eval_ex)
    e_h1 = float(e_eval["h1_q75"]["failure_detection_auroc"]["observed"])
    e_delta = abs(e_h1 - E_H1_AUROC_TARGET)
    if e_delta > ANCHOR_TOL:
        extra = {
            "observed_h1_auroc": e_h1,
            "target_h1_auroc": E_H1_AUROC_TARGET,
            "abs_delta": e_delta,
            "tolerance": ANCHOR_TOL,
        }
        write_stopped_report("stopped_e_anchor_failed", "E clean h=1 AUROC anchor failed", extra)
        raise SystemExit(f"E anchor failed: observed={e_h1:.17g}, target={E_H1_AUROC_TARGET:.17g}")

    anchors, anchors_by_ep, errors_h5, true_mean_h5, valid_h5, uniform_alloc = build_eval_budget(
        clean_eval_ex,
        clean,
    )
    oracle_score = true_mean_h5.copy()
    oracle = budget_eval_for_score("oracle", oracle_score, anchors, anchors_by_ep, errors_h5, uniform_alloc)
    oracle_delta = float(oracle["delta_vs_uniform"]["observed"])
    oracle_abs_delta = abs(oracle_delta - ORACLE_DELTA_TARGET)
    if oracle_abs_delta > ANCHOR_TOL:
        extra = {
            "observed_oracle_delta": oracle_delta,
            "target_oracle_delta": ORACLE_DELTA_TARGET,
            "abs_delta": oracle_abs_delta,
            "tolerance": ANCHOR_TOL,
        }
        write_stopped_report("stopped_oracle_anchor_failed", "allocation oracle delta anchor failed", extra)
        raise SystemExit(
            f"oracle anchor failed: observed={oracle_delta:.17g}, target={ORACLE_DELTA_TARGET:.17g}"
        )

    train_blocks = rich_feature_blocks(clean_train_ex, e_train_logits)
    eval_blocks = rich_feature_blocks(clean_eval_ex, e_eval_logits)
    input_summaries = {
        "A1": "past(z,a)+pred_z[1:5]+delta_pred_z[2:5]",
        "A2": "A1+12 frozen E logits",
        "A3": "A2+4 pred_z drift norms",
    }
    feature_dims = {arm: int(compose_features(train_blocks, arm).shape[1]) for arm in ("A1", "A2", "A3")}

    arms: dict[str, Any] = {}
    for arm in ("A1", "A2", "A3"):
        print(f"[train] {arm} rich-input ranker", flush=True)
        train_x = compose_features(train_blocks, arm)
        eval_x = compose_features(eval_blocks, arm)
        model, info, norm = train_rich_ranker(arm, train_x, clean)
        score_all = predict_rich_ranker(model, eval_x, norm)
        score = score_all[valid_h5]
        budget = budget_eval_for_score(arm, score, anchors, anchors_by_ep, errors_h5, uniform_alloc)
        sp = within_episode_spearman(score, true_mean_h5, anchors)
        d = budget["delta_vs_uniform"]
        rho = float(sp["episode_mean"])
        rho_pass = bool(rho >= RHO_POSITIVE_THRESHOLD)
        ci_pass = bool(float(d["ci95_high"]) < 0.0)
        arms[arm] = {
            "info": info,
            "input_summary": input_summaries[arm],
            "feature_dim": feature_dims[arm],
            "allocation": budget["allocation"],
            "delta_vs_uniform": d,
            "spearman": sp,
            "oracle_gap": float(d["observed"] - oracle_delta),
            "rho_pass": rho_pass,
            "ci_pass": ci_pass,
            "verdict": "positive" if rho_pass and ci_pass else "not_positive",
            "beats_0p51_baseline": bool(rho > R1_FAILURE_BASELINE_RHO),
            "rho_minus_0p51_baseline": float(rho - R1_FAILURE_BASELINE_RHO),
        }

    any_positive = any(row["verdict"] == "positive" for row in arms.values())
    any_rho_over_baseline = any(row["beats_0p51_baseline"] for row in arms.values())
    max_rho_arm = max(arms, key=lambda name: float(arms[name]["spearman"]["episode_mean"]))
    max_rho = float(arms[max_rho_arm]["spearman"]["episode_mean"])
    interpretation = [
        f"best rich-input rho is {max_rho:.6f} from {max_rho_arm}; baseline comparison is rho~{R1_FAILURE_BASELINE_RHO:.2f}",
        "rich input pushed rho over the 0.51 failed-ranker baseline"
        if any_rho_over_baseline
        else "rich input did not push rho over the 0.51 failed-ranker baseline",
        "at least one arm satisfies the predeclared positive rule"
        if any_positive
        else "no arm satisfies the predeclared positive rule rho>=0.58 and CI95_high<0",
    ]
    if not any_positive:
        interpretation.append(
            "negative result strengthens the information-limit diagnosis under this frozen protocol"
        )

    report = {
        "status": "ok",
        "schema_id": "lewm.alloc_rich_input",
        "scientific_question": (
            "Can richer predictor-internal trajectory signals push allocation ranking quality past rho>=0.58?"
        ),
        "protocol": {
            "reused_from": "_allocation_bridge for seeds, split, allocation rule, oracle, and paired bootstrap",
            "seeds": {
                "numpy": PYTHON_SEED,
                "torch": TORCH_SEED,
                "split": SPLIT_SEED,
                "bootstrap": BOOTSTRAP_SEED,
            },
            "bootstrap_resamples": BOOTSTRAPS,
            "target": {
                "description": "h=5 mean rollout error",
                "npz_field": "mean_err_to_h",
                "column_index": TARGET_H_INDEX,
                "horizon": TARGET_H,
            },
            "input_blocks": {
                "past": f"WINDOW={g2n.WINDOW} z/action window",
                "pred_z_trajectory": "complete pred_z[:, :5, :] flattened",
                "pred_z_step_deltas": "pred_z[k] - pred_z[k-1] for k=1..4",
                "ledger_logits": "frozen G2N E logits for h in {1,3,5,10}, q in {50,75,90}",
                "drift_norms": "||pred_z[k] - pred_z[k-1]|| for k=1..4",
            },
            "training": {
                "objective": "within_episode_pairwise_logistic_ranking",
                "epochs": g2n.EPOCHS,
                "batch": g2n.BATCH,
                "optimizer": "AdamW",
                "lr": g2n.LR,
                "no_hyperparameter_scan": True,
            },
            "allocation_rule": {
                "uniform": f"h={UNIFORM_H} for every anchor",
                "score_sorted": f"within episode low score half h={LOW_H}, high score half h={HIGH_H}, odd median h={MID_H}",
                "oracle": "same rule, sorted by true h=5 mean error",
            },
            "eval": {
                "anchors": int(len(anchors)),
                "episodes": int(len(anchors_by_ep)),
                "episode_split": "eval",
                "budget_errors": "eval_err_at_h first five steps",
            },
        },
        "precursors": {
            "clean_npz": str(CLEAN_LABELS),
            "allocation_bridge_script": str(ALLOCATION_BRIDGE),
            "allocation_rho_threshold_script": str(ALLOCATION_RHO_THRESHOLD),
            "native_ledger_script": str(NATIVE_LEDGER),
        },
        "anchors": {
            "e_clean_h1_auroc": {
                "status": "passed",
                "observed": e_h1,
                "target": E_H1_AUROC_TARGET,
                "abs_delta": e_delta,
                "tolerance": ANCHOR_TOL,
                "info": e_info,
            },
            "oracle_delta": {
                "status": "passed",
                "observed": oracle_delta,
                "target": ORACLE_DELTA_TARGET,
                "abs_delta": oracle_abs_delta,
                "tolerance": ANCHOR_TOL,
            },
        },
        "arms": arms,
        "controls": {
            "uniform": {"allocation": uniform_alloc},
            "oracle": {
                "allocation": oracle["allocation"],
                "delta_vs_uniform": oracle["delta_vs_uniform"],
                "spearman": within_episode_spearman(oracle_score, true_mean_h5, anchors),
                "oracle_gap": 0.0,
            },
            "r1_failed_ranker_baseline": {
                "rho_reference": R1_FAILURE_BASELINE_RHO,
                "source": "Round1 failed ranker band, summarized as rho top around 0.51",
            },
        },
        "decision_rule": "positive iff rho >= 0.58 and allocation delta CI95_high < 0",
        "summary": {
            "any_positive": bool(any_positive),
            "any_rho_over_0p51_baseline": bool(any_rho_over_baseline),
            "best_rho_arm": max_rho_arm,
            "best_rho": max_rho,
        },
        "interpretation": interpretation,
        "not_claimed": [
            "single checkpoint single export",
            "prediction budget allocation rather than planning or control",
            "no hyperparameter scan",
            "no selection of only the best arm",
            "negative arms are reported as negative without post hoc threshold changes",
        ],
    }
    clean_report = clean_json(report)
    JSON_PATH.write_text(json.dumps(clean_report, indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(clean_report)
    print(json.dumps(clean_json({"summary": report["summary"], "arms": arms}), indent=2, ensure_ascii=False), flush=True)
    print(f"wrote {JSON_PATH}", flush=True)
    print(f"wrote {MD_PATH}", flush=True)


if __name__ == "__main__":
    main()

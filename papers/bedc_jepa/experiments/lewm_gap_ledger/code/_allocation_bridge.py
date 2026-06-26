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
from _lat_lewm_port import NPZ_PATH, REPORT_DIR
from _ledger_gated_rollout import (
    LOW_H,
    MID_H,
    HIGH_H,
    UNIFORM_H,
    allocation_by_score,
    allocation_uniform,
    paired_bootstrap_delta,
    summarize_allocation,
)
from _phase1c_gap_ledger import auroc_rank, flatten_transition_rows
from _phase2a_brittleness_gap import clean_json


ROOT = Path(__file__).resolve().parent
CLEAN_LABELS = REPORT_DIR / "g2n_labels_clean.npz"
NATIVE_LEDGER = ROOT / "_g2n_native_ledger.py"
ROLLOUT_LEDGER = ROOT / "_ledger_gated_rollout.py"
NATIVE_LEDGER_JSON = REPORT_DIR / "g2n_native_ledger.json"
JSON_PATH = REPORT_DIR / "lewm_allocation_bridge.json"
MD_PATH = REPORT_DIR / "lewm_allocation_bridge.md"

PYTHON_SEED = 20260611
TORCH_SEED = 20260611
SPLIT_SEED = 1701
PERMUTATION_SEED = 90210
BOOTSTRAP_SEED = 314159
BOOTSTRAPS = 500

TARGET_H = 5
TARGET_H_INDEX = g2n.H_TO_LABEL_IDX[TARGET_H]
E_H1_AUROC_TARGET = 0.7385152058598745
ANCHOR_TOL = 1e-9


def require_inputs() -> None:
    missing = [
        p
        for p in (CLEAN_LABELS, NATIVE_LEDGER, ROLLOUT_LEDGER, NATIVE_LEDGER_JSON)
        if not p.exists()
    ]
    if missing:
        raise SystemExit("missing required precursor(s): " + ", ".join(str(p) for p in missing))


class ScalarLedgerTransformer(nn.Module):
    def __init__(self, emb_dim: int, act_dim: int) -> None:
        super().__init__()
        self.emb_dim = emb_dim
        self.act_dim = act_dim
        token_dim = emb_dim * 2 + act_dim + 1
        self.token_proj = nn.Linear(token_dim, g2n.D_MODEL)
        self.pos = nn.Parameter(torch.zeros(g2n.WINDOW + g2n.MAX_FUTURE_TOKENS + 1, g2n.D_MODEL))
        self.type_emb = nn.Embedding(3, g2n.D_MODEL)
        layer = nn.TransformerEncoderLayer(
            d_model=g2n.D_MODEL,
            nhead=g2n.N_HEADS,
            dim_feedforward=g2n.FFN_DIM,
            dropout=0.0,
            batch_first=True,
            norm_first=True,
        )
        self.encoder = nn.TransformerEncoder(layer, num_layers=g2n.N_LAYERS)
        self.head = nn.Linear(g2n.D_MODEL, 1)

    def forward(
        self,
        past_z: torch.Tensor,
        past_a: torch.Tensor,
        future_z: torch.Tensor,
        future_delta: torch.Tensor,
        future_avail: torch.Tensor,
        t_scalar: torch.Tensor,
    ) -> torch.Tensor:
        b = past_z.shape[0]
        t_past = t_scalar[:, None, None].expand(b, g2n.WINDOW, 1)
        past = torch.cat(
            [
                past_z,
                torch.zeros(b, g2n.WINDOW, self.emb_dim, device=past_z.device, dtype=past_z.dtype),
                past_a,
                t_past,
            ],
            dim=-1,
        )
        t_future = t_scalar[:, None, None].expand(b, g2n.MAX_FUTURE_TOKENS, 1)
        fut = torch.cat(
            [
                future_z,
                future_delta,
                torch.zeros(
                    b,
                    g2n.MAX_FUTURE_TOKENS,
                    self.act_dim,
                    device=past_z.device,
                    dtype=past_z.dtype,
                ),
                t_future,
            ],
            dim=-1,
        )
        query = torch.zeros(
            b,
            1,
            self.emb_dim * 2 + self.act_dim + 1,
            device=past_z.device,
            dtype=past_z.dtype,
        )
        x = torch.cat([past, fut, query], dim=1)
        tid = torch.cat(
            [
                torch.zeros(b, g2n.WINDOW, device=past_z.device, dtype=torch.long),
                torch.ones(b, g2n.MAX_FUTURE_TOKENS, device=past_z.device, dtype=torch.long),
                torch.full((b, 1), 2, device=past_z.device, dtype=torch.long),
            ],
            dim=1,
        )
        pad = torch.cat(
            [
                torch.zeros(b, g2n.WINDOW, device=past_z.device, dtype=torch.bool),
                ~future_avail.bool(),
                torch.zeros(b, 1, device=past_z.device, dtype=torch.bool),
            ],
            dim=1,
        )
        h = self.token_proj(x) + self.type_emb(tid) + self.pos[: x.shape[1]].unsqueeze(0)
        h = self.encoder(h, src_key_padding_mask=pad)
        return self.head(h[:, -1]).squeeze(-1)


class LogitRanker(nn.Module):
    def __init__(self, in_dim: int) -> None:
        super().__init__()
        self.net = nn.Sequential(nn.Linear(in_dim, 64), nn.ReLU(), nn.Linear(64, 1))

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.net(x).squeeze(-1)


def target_mean_err(clean: np.lib.npyio.NpzFile, split: str) -> tuple[np.ndarray, np.ndarray]:
    valid = clean[f"{split}_valid"][:, TARGET_H_INDEX].astype(bool)
    y = clean[f"{split}_mean_err_to_h"][:, TARGET_H_INDEX].astype(np.float64)
    return y, valid


def tensorize_examples(exn: dict[str, np.ndarray]) -> dict[str, torch.Tensor]:
    return {
        "past_z": torch.from_numpy(exn["past_z"].astype(np.float32)),
        "past_a": torch.from_numpy(exn["past_a"].astype(np.float32)),
        "future_z": torch.from_numpy(exn["future_z"].astype(np.float32)),
        "future_delta": torch.from_numpy(exn["future_delta"].astype(np.float32)),
        "future_avail": torch.from_numpy(exn["future_avail"].astype(bool)),
        "t_scalar": torch.from_numpy(exn["t_scalar"].astype(np.float32)),
    }


def pairwise_logistic_loss(score: torch.Tensor, target: torch.Tensor, episode: torch.Tensor) -> torch.Tensor | None:
    same = episode[:, None] == episode[None, :]
    upper = torch.triu(torch.ones_like(same, dtype=torch.bool), diagonal=1)
    target_diff = target[:, None] - target[None, :]
    sign = torch.sign(target_diff)
    pair = same & upper & (sign != 0)
    if not bool(pair.any()):
        return None
    score_diff = score[:, None] - score[None, :]
    return nn.functional.softplus(-(score_diff[pair] * sign[pair])).mean()


def train_scalar_bridge(
    name: str,
    train_ex: dict[str, np.ndarray],
    clean: np.lib.npyio.NpzFile,
    *,
    regression: bool,
    permutation_seed: int | None,
) -> tuple[ScalarLedgerTransformer, dict[str, Any], dict[str, np.ndarray]]:
    torch.manual_seed(TORCH_SEED)
    np.random.seed(PYTHON_SEED)
    y_all, valid_all = target_mean_err(clean, "train")
    keep = valid_all
    ex = {k: (v[keep] if isinstance(v, np.ndarray) and len(v) == len(keep) else v) for k, v in train_ex.items()}
    target = y_all[keep].astype(np.float32)
    if permutation_seed is not None:
        rng = np.random.default_rng(permutation_seed)
        target = target[rng.permutation(len(target))]

    norm = g2n.compute_norm(ex)
    exn = g2n.normalize_examples(ex, norm)
    tensors = tensorize_examples(exn)
    target_t = torch.from_numpy(target)
    episode_t = torch.from_numpy(exn["episode"].astype(np.int64))
    model = ScalarLedgerTransformer(exn["past_z"].shape[-1], exn["past_a"].shape[-1])
    opt = torch.optim.AdamW(model.parameters(), lr=g2n.LR)
    generator = torch.Generator().manual_seed(TORCH_SEED)
    steps = 0
    t0 = time.perf_counter()
    model.train()
    for epoch in range(1, g2n.EPOCHS + 1):
        order = torch.randperm(len(target), generator=generator)
        for start in range(0, len(target), g2n.BATCH):
            idx = order[start : start + g2n.BATCH]
            score = model(
                tensors["past_z"][idx],
                tensors["past_a"][idx],
                tensors["future_z"][idx],
                tensors["future_delta"][idx],
                tensors["future_avail"][idx],
                tensors["t_scalar"][idx],
            )
            if regression:
                loss = nn.functional.mse_loss(score, torch.log(target_t[idx] + 1e-8))
            else:
                maybe_loss = pairwise_logistic_loss(score, target_t[idx], episode_t[idx])
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
        "objective": "log_h5_mean_error_mse" if regression else "within_episode_pairwise_logistic_ranking",
        "target": f"clean train mean_err_to_h[:, {TARGET_H_INDEX}] for h={TARGET_H}",
        "epochs": g2n.EPOCHS,
        "batch": g2n.BATCH,
        "optimizer": "AdamW",
        "lr": g2n.LR,
        "optimizer_steps": int(steps),
        "wall_time_seconds": round(time.perf_counter() - t0, 2),
        "parameter_count": int(sum(p.numel() for p in model.parameters())),
        "train_rows": int(len(target)),
        "label_permutation_seed": permutation_seed,
    }
    return model.eval(), info, norm


def predict_scalar(
    model: ScalarLedgerTransformer,
    ex: dict[str, np.ndarray],
    norm: dict[str, np.ndarray],
    *,
    batch: int = 1024,
) -> np.ndarray:
    exn = g2n.normalize_examples(ex, norm)
    out = np.zeros(len(exn["episode"]), dtype=np.float64)
    with torch.no_grad():
        for lo in range(0, len(out), batch):
            hi = min(lo + batch, len(out))
            score = model(
                torch.from_numpy(exn["past_z"][lo:hi].astype(np.float32)),
                torch.from_numpy(exn["past_a"][lo:hi].astype(np.float32)),
                torch.from_numpy(exn["future_z"][lo:hi].astype(np.float32)),
                torch.from_numpy(exn["future_delta"][lo:hi].astype(np.float32)),
                torch.from_numpy(exn["future_avail"][lo:hi].astype(bool)),
                torch.from_numpy(exn["t_scalar"][lo:hi].astype(np.float32)),
            )
            out[lo:hi] = score.detach().cpu().numpy().astype(np.float64)
    return out


def train_logit_ranker(train_logits: np.ndarray, clean: np.lib.npyio.NpzFile) -> tuple[LogitRanker, dict[str, Any]]:
    torch.manual_seed(TORCH_SEED)
    np.random.seed(PYTHON_SEED)
    y_all, valid_all = target_mean_err(clean, "train")
    x = train_logits[valid_all].astype(np.float32)
    y = y_all[valid_all].astype(np.float32)
    episode = clean["train_anchor_ep_t0"][valid_all, 0].astype(np.int64)
    x_t = torch.from_numpy(x)
    y_t = torch.from_numpy(y)
    ep_t = torch.from_numpy(episode)
    model = LogitRanker(x.shape[1])
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
                raise RuntimeError("non-finite loss in R3")
            opt.zero_grad()
            loss.backward()
            opt.step()
            steps += 1
        if epoch == 1 or epoch % 5 == 0 or epoch == g2n.EPOCHS:
            print(f"[train] R3 ranker epoch={epoch}/{g2n.EPOCHS} steps={steps}", flush=True)
    info = {
        "status": "trained",
        "objective": "within_episode_pairwise_logistic_ranking",
        "features": "frozen G2N arm E 12 clean logits",
        "mlp": "Linear(12,64), ReLU, Linear(64,1)",
        "target": f"clean train mean_err_to_h[:, {TARGET_H_INDEX}] for h={TARGET_H}",
        "epochs": g2n.EPOCHS,
        "batch": g2n.BATCH,
        "optimizer": "AdamW",
        "lr": g2n.LR,
        "optimizer_steps": int(steps),
        "wall_time_seconds": round(time.perf_counter() - t0, 2),
        "parameter_count": int(sum(p.numel() for p in model.parameters())),
        "train_rows": int(len(y)),
    }
    return model.eval(), info


def predict_ranker(model: LogitRanker, logits: np.ndarray, *, batch: int = 4096) -> np.ndarray:
    out = np.zeros(len(logits), dtype=np.float64)
    with torch.no_grad():
        for lo in range(0, len(out), batch):
            hi = min(lo + batch, len(out))
            score = model(torch.from_numpy(logits[lo:hi].astype(np.float32)))
            out[lo:hi] = score.detach().cpu().numpy().astype(np.float64)
    return out


def rank_average(x: np.ndarray) -> np.ndarray:
    order = np.argsort(x, kind="mergesort")
    ranks = np.empty(len(x), dtype=np.float64)
    i = 0
    while i < len(x):
        j = i + 1
        while j < len(x) and x[order[j]] == x[order[i]]:
            j += 1
        ranks[order[i:j]] = (i + j - 1) / 2.0
        i = j
    return ranks


def spearman_one(x: np.ndarray, y: np.ndarray) -> float:
    if len(x) < 2:
        return float("nan")
    rx = rank_average(x.astype(np.float64))
    ry = rank_average(y.astype(np.float64))
    if float(np.std(rx)) == 0.0 or float(np.std(ry)) == 0.0:
        return float("nan")
    return float(np.corrcoef(rx, ry)[0, 1])


def within_episode_spearman(score: np.ndarray, truth: np.ndarray, anchors: list[dict[str, Any]]) -> dict[str, Any]:
    by_ep: dict[int, list[int]] = defaultdict(list)
    for i, anchor in enumerate(anchors):
        by_ep[int(anchor["episode"])].append(i)
    values: list[float] = []
    weighted_num = 0.0
    weighted_den = 0
    for idxs in by_ep.values():
        idx = np.asarray(idxs, dtype=np.int64)
        rho = spearman_one(score[idx], truth[idx])
        if np.isfinite(rho):
            values.append(float(rho))
            weighted_num += float(rho) * len(idx)
            weighted_den += len(idx)
    return {
        "episode_mean": float(np.mean(values)) if values else float("nan"),
        "anchor_weighted_mean": float(weighted_num / weighted_den) if weighted_den else float("nan"),
        "episodes_used": int(len(values)),
        "episodes_total": int(len(by_ep)),
        "definition": "Spearman(score, true h=5 mean error), computed within episode then averaged",
    }


def budget_eval_for_score(
    name: str,
    score: np.ndarray,
    anchors: list[dict[str, Any]],
    anchors_by_ep: dict[int, list[int]],
    errors_h5: np.ndarray,
    uniform_alloc: dict[str, Any],
) -> dict[str, Any]:
    h = allocation_by_score(anchors, anchors_by_ep, score)
    alloc = summarize_allocation(name, h, errors_h5, anchors)
    delta = paired_bootstrap_delta(
        alloc["episode_total_error"],
        uniform_alloc["episode_total_error"],
        alloc["episode_emitted_steps"],
        uniform_alloc["episode_emitted_steps"],
    )
    return {"allocation": alloc, "delta_vs_uniform": delta}


def write_markdown(report: dict[str, Any]) -> None:
    lines = [
        "# LEWM Allocation Bridge",
        "",
        f"- status: `{report['status']}`",
        f"- positive rule: {report['decision_rule']}",
        f"- oracle delta: `{report['controls']['oracle']['delta_vs_uniform']['observed']:.9f}` "
        f"[`{report['controls']['oracle']['delta_vs_uniform']['ci95_low']:.9f}`, "
        f"`{report['controls']['oracle']['delta_vs_uniform']['ci95_high']:.9f}`]",
        "",
        "## Allocation Results",
        "",
        "| arm | delta vs uniform | 95% CI | Spearman episode mean | oracle gap | verdict |",
        "|---|---:|---:|---:|---:|---|",
    ]
    for name in ("R1", "R2", "R3"):
        row = report["arms"][name]
        d = row["delta_vs_uniform"]
        lines.append(
            f"| `{name}` | {d['observed']:.9f} | [{d['ci95_low']:.9f}, {d['ci95_high']:.9f}] | "
            f"{row['spearman']['episode_mean']:.6f} | {row['oracle_gap']:.9f} | {row['verdict']} |"
        )
    lines.extend(
        [
            "",
            "## Controls",
            "",
            "| control | delta vs uniform | 95% CI | Spearman episode mean | oracle gap |",
            "|---|---:|---:|---:|---:|",
        ]
    )
    for name in ("R1_permuted", "oracle"):
        row = report["controls"][name]
        d = row["delta_vs_uniform"]
        sp = row.get("spearman", {}).get("episode_mean", float("nan"))
        lines.append(
            f"| `{name}` | {d['observed']:.9f} | [{d['ci95_low']:.9f}, {d['ci95_high']:.9f}] | "
            f"{sp:.6f} | {row['oracle_gap']:.9f} |"
        )
    lines.extend(["", "## R3 Anchor", ""])
    r3 = report["r3_e_anchor"]
    lines.append(
        f"- E clean h=1 AUROC: `{r3['observed_h1_auroc']:.15f}`; target "
        f"`{r3['target_h1_auroc']:.15f}`; abs delta `{r3['abs_delta']:.3g}`."
    )
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
    rows = flatten_transition_rows(data)
    splits = g2n.split_episodes(data["emb"].shape[0])
    if SPLIT_SEED != 1701 or int(len(splits["eval"])) <= 0:
        raise SystemExit("split sanity failed")

    clean = np.load(CLEAN_LABELS)
    clean_train_ex = g2n.build_clean_examples(data, clean, "train", None)
    clean_eval_ex = g2n.build_clean_examples(data, clean, "eval", None)

    print("[train] R1 regression bridge", flush=True)
    r1_model, r1_info, r1_norm = train_scalar_bridge(
        "R1",
        clean_train_ex,
        clean,
        regression=True,
        permutation_seed=None,
    )
    print("[train] R1 permuted control", flush=True)
    rp_model, rp_info, rp_norm = train_scalar_bridge(
        "R1_permuted",
        clean_train_ex,
        clean,
        regression=True,
        permutation_seed=PERMUTATION_SEED,
    )
    print("[train] R2 ranking bridge", flush=True)
    r2_model, r2_info, r2_norm = train_scalar_bridge(
        "R2",
        clean_train_ex,
        clean,
        regression=False,
        permutation_seed=None,
    )

    print("[train] R3 frozen E anchor", flush=True)
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
        report = {
            "status": "stopped_r3_e_anchor_failed",
            "reason": "R3 frozen E reconstruction clean h=1 AUROC anchor failed",
            "observed_h1_auroc": e_h1,
            "target_h1_auroc": E_H1_AUROC_TARGET,
            "abs_delta": e_delta,
            "tolerance": ANCHOR_TOL,
        }
        JSON_PATH.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
        MD_PATH.write_text(
            "# LEWM Allocation Bridge\n\n"
            f"Stopped: R3 E anchor failed. observed `{e_h1:.17g}`, "
            f"target `{E_H1_AUROC_TARGET:.17g}`, abs delta `{e_delta:.9g}`.\n",
            encoding="utf-8",
        )
        raise SystemExit(
            f"R3 E anchor failed: observed={e_h1:.17g}, target={E_H1_AUROC_TARGET:.17g}"
        )

    print("[train] R3 logit ranker", flush=True)
    r3_model, r3_info = train_logit_ranker(e_train_logits, clean)

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

    r1_score_all = predict_scalar(r1_model, clean_eval_ex, r1_norm)
    rp_score_all = predict_scalar(rp_model, clean_eval_ex, rp_norm)
    r2_score_all = predict_scalar(r2_model, clean_eval_ex, r2_norm)
    r3_score_all = predict_ranker(r3_model, e_eval_logits)
    scores = {
        "R1": r1_score_all[valid_h5],
        "R2": r2_score_all[valid_h5],
        "R3": r3_score_all[valid_h5],
        "R1_permuted": rp_score_all[valid_h5],
    }
    oracle_score = true_mean_h5.copy()
    oracle = budget_eval_for_score("oracle", oracle_score, anchors, anchors_by_ep, errors_h5, uniform_alloc)
    oracle_delta = float(oracle["delta_vs_uniform"]["observed"])

    arm_infos = {"R1": r1_info, "R2": r2_info, "R3": r3_info}
    out_arms: dict[str, Any] = {}
    for name in ("R1", "R2", "R3"):
        budget = budget_eval_for_score(name, scores[name], anchors, anchors_by_ep, errors_h5, uniform_alloc)
        delta = budget["delta_vs_uniform"]
        out_arms[name] = {
            "info": arm_infos[name],
            "allocation": budget["allocation"],
            "delta_vs_uniform": delta,
            "spearman": within_episode_spearman(scores[name], true_mean_h5, anchors),
            "oracle_gap": float(delta["observed"] - oracle_delta),
            "verdict": "positive" if float(delta["ci95_high"]) < 0.0 else "not_positive",
        }

    perm_budget = budget_eval_for_score(
        "R1_permuted",
        scores["R1_permuted"],
        anchors,
        anchors_by_ep,
        errors_h5,
        uniform_alloc,
    )
    controls = {
        "uniform": {"allocation": uniform_alloc},
        "R1_permuted": {
            "info": rp_info,
            "allocation": perm_budget["allocation"],
            "delta_vs_uniform": perm_budget["delta_vs_uniform"],
            "spearman": within_episode_spearman(scores["R1_permuted"], true_mean_h5, anchors),
            "oracle_gap": float(perm_budget["delta_vs_uniform"]["observed"] - oracle_delta),
        },
        "oracle": {
            "allocation": oracle["allocation"],
            "delta_vs_uniform": oracle["delta_vs_uniform"],
            "spearman": within_episode_spearman(oracle_score, true_mean_h5, anchors),
            "oracle_gap": 0.0,
        },
    }

    report = {
        "status": "ok",
        "schema_id": "lewm.allocation_bridge",
        "protocol": {
            "seeds": {
                "numpy": PYTHON_SEED,
                "torch": TORCH_SEED,
                "split": SPLIT_SEED,
                "bootstrap": BOOTSTRAP_SEED,
                "permutation_control": PERMUTATION_SEED,
            },
            "bootstrap_resamples": BOOTSTRAPS,
            "target": {
                "description": "h=5 mean rollout error",
                "npz_field": "mean_err_to_h",
                "column_index": TARGET_H_INDEX,
                "horizon": TARGET_H,
            },
            "architecture": {
                "base": "G2N native ledger arm E transformer, output changed to one scalar for R1/R2",
                "past_tokens": g2n.WINDOW,
                "max_future_tokens": g2n.MAX_FUTURE_TOKENS,
                "d_model": g2n.D_MODEL,
                "heads": g2n.N_HEADS,
                "layers": g2n.N_LAYERS,
                "r3_ranker": "MLP(12 -> 64 -> 1) with ReLU",
            },
            "training": {
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
            "native_ledger_script": str(NATIVE_LEDGER),
            "rollout_allocation_script": str(ROLLOUT_LEDGER),
            "native_ledger_json": str(NATIVE_LEDGER_JSON),
        },
        "r3_e_anchor": {
            "status": "passed",
            "observed_h1_auroc": e_h1,
            "target_h1_auroc": E_H1_AUROC_TARGET,
            "abs_delta": e_delta,
            "tolerance": ANCHOR_TOL,
            "info": e_info,
        },
        "arms": out_arms,
        "controls": controls,
        "decision_rule": "per arm positive iff paired episode-bootstrap CI for allocation minus uniform is entirely < 0",
        "not_claimed": [
            "single checkpoint single export",
            "prediction budget allocation rather than planning or control",
            "no hyperparameter scan",
            "no selection of only the best arm",
        ],
    }
    JSON_PATH.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(clean_json(report))
    print(json.dumps(clean_json({"arms": out_arms, "controls": controls}), indent=2, ensure_ascii=False), flush=True)
    print(f"wrote {JSON_PATH}", flush=True)
    print(f"wrote {MD_PATH}", flush=True)


if __name__ == "__main__":
    main()

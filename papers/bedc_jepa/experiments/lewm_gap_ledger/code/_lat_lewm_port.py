"""LAT-style ledger-aware transformer ported to real LeWM latents.

Ports the *architecture idea* of the BEDC-native ledger-aware-transformer
(quality-lab `bedc_quality_lab/ledger_aware_transformer.py`: a sequence model
whose ledger head declares its own uncertainty, trained jointly with the task)
onto the real LeWM tworooms latent export, under the exact phase1c protocol:

- failure truth: LeWM predictor's own rollout error (prediction_mse) > train p75
- episode split (SPLIT_SEED 1701, 60/20/20), eval episode-level bootstrap (500)
- arms: vanilla (constant train base rate), lat_learned, lat_matched_random
  (same architecture/training, ledger labels permuted within train split),
  lat_without_dynamics (component ablation: no joint next-latent loss)
- positive claim iff BOTH: learned AUROC ci95_low > matched-random ci95_high
  AND learned UER ci95_high < vanilla UER ci95_low. Otherwise fail-closed.

Ledger-head inference inputs are strictly (emb, action) windows — no mse, no
ground-truth state/observation/position columns.
"""

from __future__ import annotations

import json
import math
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch
import torch.nn as nn

ROOT = Path(__file__).resolve().parent
NPZ_PATH = ROOT / "tworooms_latent_large.npz"
REPORT_DIR = ROOT / "reports"
JSON_PATH = REPORT_DIR / "lewm_ledger_aware_transformer.json"
MD_PATH = REPORT_DIR / "lewm_ledger_aware_transformer.md"
PHASE1C_JSON = REPORT_DIR / "lewm_gap_ledger_head_large.json"

PYTHON_SEED = 20260611
SPLIT_SEED = 1701
MATCHED_RANDOM_SEED = 90210
BOOTSTRAP_SEED = 314159
BOOTSTRAPS = 500

WINDOW = 6
D_MODEL = 64
N_HEADS = 4
N_LAYERS = 2
FFN_DIM = 128
EPOCHS = 30
BATCH = 256
LR = 1e-3
DYNAMICS_WEIGHT = 1.0

FORBIDDEN_INFERENCE_COLUMNS = (
    "prediction_mse",
    "observation",
    "pos_agent",
    "pos_target",
    "distance_to_target",
    "agent_room_lr",
    "target_room_lr",
    "same_room_lr",
)


def auroc_rank(y_true: np.ndarray, score: np.ndarray) -> float:
    y = y_true.astype(bool)
    n_pos = int(y.sum())
    n_neg = int((~y).sum())
    if n_pos == 0 or n_neg == 0:
        return 0.5
    order = np.argsort(score, kind="mergesort")
    sorted_score = score[order]
    ranks = np.empty(len(score), dtype=np.float64)
    i = 0
    while i < len(score):
        j = i + 1
        while j < len(score) and sorted_score[j] == sorted_score[i]:
            j += 1
        avg_rank = (i + 1 + j) / 2.0
        ranks[order[i:j]] = avg_rank
        i = j
    return float((ranks[y].sum() - n_pos * (n_pos + 1) / 2.0) / (n_pos * n_neg))


def ece_10bin(y_true: np.ndarray, prob: np.ndarray) -> float:
    y = y_true.astype(np.float64)
    if len(y) == 0:
        return float("nan")
    edges = np.linspace(0.0, 1.0, 11)
    out = 0.0
    for lo, hi in zip(edges[:-1], edges[1:]):
        if hi == 1.0:
            m = (prob >= lo) & (prob <= hi)
        else:
            m = (prob >= lo) & (prob < hi)
        if not np.any(m):
            continue
        out += float(m.mean()) * abs(float(prob[m].mean()) - float(y[m].mean()))
    return float(out)


def basic_metrics(y_err: np.ndarray, gap_score: np.ndarray) -> dict[str, float]:
    return {
        "failure_detection_auroc": auroc_rank(y_err, gap_score),
        "ece": ece_10bin(y_err, gap_score),
        "unlogged_error_rate": float(np.mean((y_err > 0) & (gap_score < 0.5))),
        "declared_gap_rate": float(np.mean(gap_score >= 0.5)),
        "false_alarm_rate": float(np.mean((y_err == 0) & (gap_score >= 0.5))),
    }


def bootstrap_metrics_by_episode(
    y_err: np.ndarray,
    gap_score: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
    n_boot: int,
) -> dict[str, dict[str, float]]:
    observed = basic_metrics(y_err, gap_score)
    rng = np.random.default_rng(seed)
    values: dict[str, list[float]] = {k: [] for k in observed}
    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    n_ep = len(by_ep)
    for _ in range(n_boot):
        sampled = rng.integers(0, n_ep, size=n_ep)
        idx = np.concatenate([by_ep[i] for i in sampled])
        m = basic_metrics(y_err[idx], gap_score[idx])
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


def split_episodes(n_ep: int) -> dict[str, np.ndarray]:
    rng = np.random.default_rng(SPLIT_SEED)
    perm = rng.permutation(n_ep)
    n_train = int(round(0.60 * n_ep))
    n_cal = int(round(0.20 * n_ep))
    train = np.sort(perm[:n_train])
    cal = np.sort(perm[n_train : n_train + n_cal])
    eval_ep = np.sort(perm[n_train + n_cal :])
    return {"train": train, "calibration": cal, "eval": eval_ep}


def build_windows(data: dict[str, np.ndarray]) -> dict[str, np.ndarray]:
    """One row per valid transition (ep, t): window of (emb, action) tokens
    at positions [t-WINDOW+1 .. t] (left-padded by repeating the episode's
    first frame), failure truth from the LeWM predictor's own rollout error."""
    tm = data["transition_mask"].astype(bool)
    ep_idx, t_idx = np.where(tm)
    emb = data["emb"].astype(np.float32)
    act = data["action"].astype(np.float32)
    mse = data["prediction_mse"].astype(np.float64)
    n = len(ep_idx)
    win_emb = np.empty((n, WINDOW, emb.shape[2]), dtype=np.float32)
    win_act = np.empty((n, WINDOW, act.shape[2]), dtype=np.float32)
    for i, (ep, t) in enumerate(zip(ep_idx, t_idx)):
        for w in range(WINDOW):
            src = max(0, t - WINDOW + 1 + w)
            win_emb[i, w] = emb[ep, src]
            win_act[i, w] = act[ep, src]
    rows = {
        "episode": ep_idx.astype(np.int64),
        "t": t_idx.astype(np.int64),
        "win_emb": win_emb,
        "win_act": win_act,
        "next_emb": emb[ep_idx, t_idx + 1].astype(np.float32),
        "mse": mse[ep_idx, t_idx],
    }
    finite = (
        np.isfinite(rows["win_emb"]).all(axis=(1, 2))
        & np.isfinite(rows["win_act"]).all(axis=(1, 2))
        & np.isfinite(rows["next_emb"]).all(axis=1)
        & np.isfinite(rows["mse"])
    )
    if not np.all(finite):
        rows = {k: v[finite] for k, v in rows.items()}
    return rows


class LedgerAwareTransformer(nn.Module):
    """Small causal transformer over (emb, action) tokens with two heads:
    a next-latent prediction head (joint dynamics task) and a ledger head
    declaring 'the world model's next prediction will fail'."""

    def __init__(self, emb_dim: int, act_dim: int) -> None:
        super().__init__()
        self.token_proj = nn.Linear(emb_dim + act_dim, D_MODEL)
        self.pos = nn.Parameter(torch.zeros(WINDOW, D_MODEL))
        layer = nn.TransformerEncoderLayer(
            d_model=D_MODEL,
            nhead=N_HEADS,
            dim_feedforward=FFN_DIM,
            dropout=0.0,
            batch_first=True,
            norm_first=True,
        )
        self.encoder = nn.TransformerEncoder(layer, num_layers=N_LAYERS)
        self.ledger_head = nn.Linear(D_MODEL, 1)
        self.dynamics_head = nn.Linear(D_MODEL, emb_dim)
        mask = torch.triu(torch.full((WINDOW, WINDOW), float("-inf")), diagonal=1)
        self.register_buffer("causal_mask", mask)

    def forward(self, win_emb: torch.Tensor, win_act: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
        x = torch.cat([win_emb, win_act], dim=-1)
        h = self.token_proj(x) + self.pos
        h = self.encoder(h, mask=self.causal_mask)
        last = h[:, -1]
        return self.ledger_head(last).squeeze(-1), self.dynamics_head(last)


def train_arm(
    rows: dict[str, np.ndarray],
    train_mask: np.ndarray,
    y: np.ndarray,
    *,
    seed: int,
    dynamics_weight: float,
    label_permutation_seed: int | None,
    return_artifacts: bool = False,
) -> tuple[np.ndarray, dict[str, Any]] | tuple[np.ndarray, dict[str, Any], "LedgerAwareTransformer", tuple[np.ndarray, np.ndarray]]:
    torch.manual_seed(seed)
    emb_dim = rows["win_emb"].shape[2]
    act_dim = rows["win_act"].shape[2]

    train_idx = np.where(train_mask)[0]
    emb_flat = rows["win_emb"][train_idx].reshape(-1, emb_dim)
    emb_mean = emb_flat.mean(axis=0)
    emb_std = emb_flat.std(axis=0) + 1e-6

    def norm_emb(a: np.ndarray) -> np.ndarray:
        return (a - emb_mean) / emb_std

    y_train = y[train_idx].astype(np.float32)
    if label_permutation_seed is not None:
        perm = np.random.default_rng(label_permutation_seed).permutation(len(y_train))
        y_train = y_train[perm]

    model = LedgerAwareTransformer(emb_dim, act_dim)
    param_count = sum(p.numel() for p in model.parameters())
    opt = torch.optim.AdamW(model.parameters(), lr=LR)
    bce = nn.BCEWithLogitsLoss()

    x_emb_t = torch.from_numpy(norm_emb(rows["win_emb"][train_idx]).astype(np.float32))
    x_act_t = torch.from_numpy(rows["win_act"][train_idx])
    y_t = torch.from_numpy(y_train)
    target_t = torch.from_numpy(norm_emb(rows["next_emb"][train_idx]).astype(np.float32))

    g = torch.Generator().manual_seed(seed)
    n_train = len(train_idx)
    steps = 0
    t0 = time.perf_counter()
    model.train()
    for _ in range(EPOCHS):
        order = torch.randperm(n_train, generator=g)
        for start in range(0, n_train, BATCH):
            sel = order[start : start + BATCH]
            logit, dyn = model(x_emb_t[sel], x_act_t[sel])
            loss = bce(logit, y_t[sel])
            if dynamics_weight > 0.0:
                loss = loss + dynamics_weight * nn.functional.mse_loss(dyn, target_t[sel])
            if not torch.isfinite(loss):
                bad = np.full(len(y), np.nan), {"status": "fail-closed", "reason": "non-finite loss"}
                return (*bad, None, (emb_mean, emb_std)) if return_artifacts else bad
            opt.zero_grad()
            loss.backward()
            opt.step()
            steps += 1
    wall = time.perf_counter() - t0

    model.eval()
    scores = np.empty(len(y), dtype=np.float64)
    with torch.no_grad():
        for start in range(0, len(y), 1024):
            sl = slice(start, min(start + 1024, len(y)))
            logit, _ = model(
                torch.from_numpy(norm_emb(rows["win_emb"][sl]).astype(np.float32)),
                torch.from_numpy(rows["win_act"][sl]),
            )
            scores[sl] = torch.sigmoid(logit).numpy()
    info = {
        "status": "trained",
        "parameter_count": int(param_count),
        "train_rows": int(n_train),
        "optimizer_steps": int(steps),
        "epochs": EPOCHS,
        "wall_time_seconds": round(wall, 2),
        "dynamics_weight": dynamics_weight,
        "label_permutation_seed": label_permutation_seed,
        "device": "cpu",
        "torch_seed": seed,
    }
    if return_artifacts:
        return scores, info, model, (emb_mean, emb_std)
    return scores, info


def ci_sep_gt(a: dict[str, dict[str, float]], b: dict[str, dict[str, float]], metric: str) -> bool:
    return a[metric]["ci95_low"] > b[metric]["ci95_high"]


def fmt_ci(m: dict[str, float]) -> str:
    return f"{m['observed']:.3f} [{m['ci95_low']:.3f}, {m['ci95_high']:.3f}]"


def main() -> None:
    np.random.seed(PYTHON_SEED)
    data = dict(np.load(NPZ_PATH))
    rows = build_windows(data)
    n_rows = len(rows["episode"])
    n_ep = data["emb"].shape[0]

    splits = split_episodes(n_ep)
    masks = {name: np.isin(rows["episode"], eps) for name, eps in splits.items()}
    train_mask, eval_mask = masks["train"], masks["eval"]

    tau_err = float(np.percentile(rows["mse"][train_mask], 75))
    y_err = (rows["mse"] > tau_err).astype(np.int8)

    arms: dict[str, Any] = {}

    train_rate = float(y_err[train_mask].mean())
    vanilla_scores = np.full(n_rows, train_rate, dtype=np.float64)
    arms["vanilla"] = {"scores": vanilla_scores, "info": {"status": "constant", "train_base_rate": train_rate}}

    learned_scores, learned_info = train_arm(
        rows, train_mask, y_err, seed=PYTHON_SEED, dynamics_weight=DYNAMICS_WEIGHT, label_permutation_seed=None
    )
    arms["lat_learned"] = {"scores": learned_scores, "info": learned_info}

    random_scores, random_info = train_arm(
        rows, train_mask, y_err, seed=PYTHON_SEED, dynamics_weight=DYNAMICS_WEIGHT,
        label_permutation_seed=MATCHED_RANDOM_SEED,
    )
    arms["lat_matched_random"] = {"scores": random_scores, "info": random_info}

    nodyn_scores, nodyn_info = train_arm(
        rows, train_mask, y_err, seed=PYTHON_SEED, dynamics_weight=0.0, label_permutation_seed=None
    )
    arms["lat_without_dynamics"] = {"scores": nodyn_scores, "info": nodyn_info}

    eval_episode = rows["episode"][eval_mask]
    y_eval = y_err[eval_mask]
    fail_closed_notes: list[str] = []
    if y_eval.min() == y_eval.max():
        fail_closed_notes.append("eval slice is single-class; AUROC unidentifiable")
    for name, pack in arms.items():
        if pack["info"].get("status") == "fail-closed":
            fail_closed_notes.append(f"arm {name} fail-closed: {pack['info'].get('reason')}")
        pack["metrics_eval_episode_bootstrap"] = bootstrap_metrics_by_episode(
            y_eval, pack["scores"][eval_mask], eval_episode, seed=BOOTSTRAP_SEED, n_boot=BOOTSTRAPS
        )

    vanilla_m = arms["vanilla"]["metrics_eval_episode_bootstrap"]
    learned_m = arms["lat_learned"]["metrics_eval_episode_bootstrap"]
    random_m = arms["lat_matched_random"]["metrics_eval_episode_bootstrap"]
    nodyn_m = arms["lat_without_dynamics"]["metrics_eval_episode_bootstrap"]

    auroc_sep = ci_sep_gt(learned_m, random_m, "failure_detection_auroc")
    uer_sep = learned_m["unlogged_error_rate"]["ci95_high"] < vanilla_m["unlogged_error_rate"]["ci95_low"]
    claim = "positive" if (auroc_sep and uer_sep and not fail_closed_notes) else "negative_or_inconclusive"

    phase1c_ref: dict[str, Any] = {}
    if PHASE1C_JSON.exists():
        p1c = json.loads(PHASE1C_JSON.read_text(encoding="utf-8"))
        for arm in (
            "learned_gap_head_A_all_probe_features",
            "learned_gap_head_B_denoised_agent_room_only",
        ):
            m = p1c.get("arms", {}).get(arm, {}).get("metrics_eval_episode_bootstrap", {})
            if m:
                phase1c_ref[arm] = {
                    "failure_detection_auroc": m.get("failure_detection_auroc"),
                    "unlogged_error_rate": m.get("unlogged_error_rate"),
                }

    report = {
        "schema_id": "lewm.ledger_aware_transformer_port",
        "source_architecture": "paper-bedc-quality-lab:papers/bedc-quality-lab/bedc_quality_lab/ledger_aware_transformer.py (architecture idea: joint task + ledger head; reimplemented in torch, not imported)",
        "carrier": "quentinll/lewm-tworooms public checkpoint latents (tworooms_latent_large.npz)",
        "sample_counts": {"valid_transitions": int(n_rows), "episodes": int(n_ep)},
        "splits": {name: int(m.sum()) for name, m in masks.items()},
        "failure_truth": {
            "definition": "prediction_mse > train_split_p75 (LeWM predictor's own rollout error)",
            "tau_err_train_p75": tau_err,
            "eval_failure_rate": float(y_eval.mean()),
        },
        "architecture": {
            "window": WINDOW,
            "d_model": D_MODEL,
            "n_heads": N_HEADS,
            "n_layers": N_LAYERS,
            "ffn_dim": FFN_DIM,
            "heads": ["ledger (declare failure)", "dynamics (next-latent prediction, joint loss)"],
            "inference_inputs": "windows of (emb, action) only",
            "forbidden_inference_columns": list(FORBIDDEN_INFERENCE_COLUMNS),
        },
        "protocol": {
            "split_seed": SPLIT_SEED,
            "matched_random_seed": MATCHED_RANDOM_SEED,
            "bootstrap_seed": BOOTSTRAP_SEED,
            "bootstraps": BOOTSTRAPS,
            "bootstrap_unit": "eval episodes",
            "eval_episode_count": int(len(np.unique(eval_episode))),
            "claim_criteria": [
                "lat_learned AUROC ci95_low > lat_matched_random AUROC ci95_high",
                "lat_learned UER ci95_high < vanilla UER ci95_low",
            ],
        },
        "arms": {
            name: {"info": pack["info"], "metrics_eval_episode_bootstrap": pack["metrics_eval_episode_bootstrap"]}
            for name, pack in arms.items()
        },
        "conclusion": {
            "claim": claim,
            "auroc_ci_separated_from_matched_random": bool(auroc_sep),
            "uer_ci_separated_from_vanilla": bool(uer_sep),
            "fail_closed_notes": fail_closed_notes,
        },
        "component_ablation": {
            "without_dynamics_loss": {
                "auroc": nodyn_m["failure_detection_auroc"],
                "uer": nodyn_m["unlogged_error_rate"],
                "note": "same arm minus the joint next-latent loss; measures whether joint task training matters",
            }
        },
        "phase1c_logistic_reference": phase1c_ref,
        "not_claimed": [
            "full model training",
            "global architecture superiority",
            "replacement of the phase1c logistic gap head",
            "benchmark reproduction or public-benchmark superiority",
            "transfer beyond the tworooms checkpoint",
        ],
    }
    REPORT_DIR.mkdir(exist_ok=True)
    JSON_PATH.write_text(json.dumps(report, indent=2), encoding="utf-8")

    lines = [
        "# LAT-style ledger-aware transformer on real LeWM latents",
        "",
        f"- claim: **{claim}** (auroc_sep={auroc_sep}, uer_sep={uer_sep})",
        f"- failure truth: prediction_mse > {tau_err:.6f} (train p75); eval failure rate {float(y_eval.mean()):.3f}",
        f"- transitions: {n_rows}; episodes: {n_ep}; eval episodes: {len(np.unique(eval_episode))}",
        f"- model: {arms['lat_learned']['info'].get('parameter_count', 'n/a')} params, "
        f"{arms['lat_learned']['info'].get('optimizer_steps', 'n/a')} steps, "
        f"{arms['lat_learned']['info'].get('wall_time_seconds', 'n/a')}s CPU",
        "",
        "| arm | AUROC | UER | declared gap rate | false alarm |",
        "| --- | --- | --- | --- | --- |",
    ]
    for name in ("vanilla", "lat_learned", "lat_matched_random", "lat_without_dynamics"):
        m = arms[name]["metrics_eval_episode_bootstrap"]
        lines.append(
            f"| `{name}` | {fmt_ci(m['failure_detection_auroc'])} | {fmt_ci(m['unlogged_error_rate'])} "
            f"| {fmt_ci(m['declared_gap_rate'])} | {fmt_ci(m['false_alarm_rate'])} |"
        )
    if phase1c_ref:
        lines += ["", "Phase1c logistic gap head reference (same protocol):", ""]
        for arm, m in phase1c_ref.items():
            lines.append(
                f"- `{arm}`: AUROC {fmt_ci(m['failure_detection_auroc'])}, UER {fmt_ci(m['unlogged_error_rate'])}"
            )
    if fail_closed_notes:
        lines += ["", "Fail-closed notes:", ""] + [f"- {n}" for n in fail_closed_notes]
    MD_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(json.dumps(report["conclusion"], indent=2))
    print(MD_PATH)


if __name__ == "__main__":
    main()

from __future__ import annotations

import json
import os
import time
from pathlib import Path
from typing import Any

import numpy as np
import torch
import torch.nn as nn

import _g2n_native_ledger as g2n
from _allocation_bridge import pairwise_logistic_loss
from _lat_lewm_port import NPZ_PATH, REPORT_DIR, split_episodes
from _phase1c_gap_ledger import auroc_rank
from _phase2a_brittleness_gap import clean_json


ROOT = Path(__file__).resolve().parent
CLEAN_LABELS = REPORT_DIR / "g2n_labels_clean.npz"
LATENT_NPZ = NPZ_PATH
NATIVE_LEDGER = ROOT / "_g2n_native_ledger.py"
ALLOCATION_BRIDGE = ROOT / "_allocation_bridge.py"
MATRIX_COMPLETION = ROOT / "_g2n_matrix_completion.py"
MATRIX_COMPLETION_JSON = REPORT_DIR / "g2n_matrix_completion.json"
JSON_PATH = REPORT_DIR / "lewm_native_residual_detection.json"
MD_PATH = REPORT_DIR / "lewm_native_residual_detection.md"

PYTHON_SEED = 20260611
TORCH_SEED = 20260611
SPLIT_SEED = 1701
BOOTSTRAP_SEED = 314159
BOOTSTRAPS = 500
PRIMARY_Q = 75
TARGET_HORIZONS = (1, 5)
H_TO_LABEL_IDX = {1: 0, 5: 4}
EXPECTED_E_H1_AUROC = 0.7385152058598745
ANCHOR_TOL = 1e-9
POSTHOC = {
    1: {"observed": 0.7374860956618465, "ci95_low": 0.6988114860644067, "ci95_high": 0.7746852460814778},
    5: {"observed": 0.7103642959329655, "ci95_low": 0.666394843186451, "ci95_high": 0.7502714813500182},
}
E_CURRENT_CI_LOW = {1: 0.6962381170315705, 5: 0.6573334955821668}


def require_inputs() -> None:
    missing = [
        p
        for p in (CLEAN_LABELS, LATENT_NPZ, NATIVE_LEDGER, ALLOCATION_BRIDGE, MATRIX_COMPLETION, MATRIX_COMPLETION_JSON)
        if not p.exists()
    ]
    if missing:
        raise SystemExit("missing required precursor(s): " + ", ".join(str(p) for p in missing))


def metric_stat(observed: float, samples: np.ndarray) -> dict[str, float]:
    arr = np.asarray(samples, dtype=np.float64)
    return {
        "observed": float(observed),
        "bootstrap_mean": float(np.nanmean(arr)),
        "ci95_low": float(np.nanpercentile(arr, 2.5)),
        "ci95_high": float(np.nanpercentile(arr, 97.5)),
    }


def binary_observed(y: np.ndarray, score: np.ndarray) -> dict[str, float]:
    return {
        "failure_detection_auroc": float(auroc_rank(y.astype(np.int8), score.astype(np.float64))),
        "failure_rate": float(np.mean(y)) if len(y) else float("nan"),
        "positive_count": int(np.sum(y > 0)),
        "negative_count": int(np.sum(y <= 0)),
    }


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


def spearman_observed(score: np.ndarray, truth: np.ndarray) -> dict[str, float]:
    return {"spearman_score_mean_err": spearman_one(score, truth)}


def bootstrap_detection_and_spearman(
    y: np.ndarray,
    score: np.ndarray,
    mean_err: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int = BOOTSTRAP_SEED,
    n_boot: int = BOOTSTRAPS,
) -> dict[str, dict[str, float]]:
    observed_bin = binary_observed(y, score)
    observed_spear = spearman_observed(score, mean_err)
    observed = {**observed_bin, **observed_spear}

    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    rng = np.random.default_rng(seed)
    values: dict[str, list[float]] = {k: [] for k in observed}
    for _ in range(n_boot):
        sampled = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[i] for i in sampled])
        m = {**binary_observed(y[idx], score[idx]), **spearman_observed(score[idx], mean_err[idx])}
        for k, v in m.items():
            values[k].append(v)

    return {k: metric_stat(v, np.asarray(values[k], dtype=np.float64)) for k, v in observed.items()}


def filter_examples_for_h(ex: dict[str, np.ndarray], clean: np.lib.npyio.NpzFile, split: str, h: int) -> dict[str, np.ndarray]:
    valid = clean[f"{split}_valid"][:, H_TO_LABEL_IDX[h]].astype(bool)
    out: dict[str, np.ndarray] = {}
    for k, v in ex.items():
        if isinstance(v, np.ndarray) and len(v) == len(valid):
            out[k] = v[valid]
        else:
            out[k] = v
    return out


def targets_for_split(clean: np.lib.npyio.NpzFile, split: str, h: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    idx = H_TO_LABEL_IDX[h]
    valid = clean[f"{split}_valid"][:, idx].astype(bool)
    y = clean[f"{split}_y"][:, idx, g2n.Q_TO_IDX[PRIMARY_Q]].astype(np.int8)
    mean_err = clean[f"{split}_mean_err_to_h"][:, idx].astype(np.float64)
    return y[valid], mean_err[valid], valid


class ResidualLedgerTransformer(nn.Module):
    def __init__(self, emb_dim: int, act_dim: int, *, binary_outputs: bool) -> None:
        super().__init__()
        self.emb_dim = emb_dim
        self.act_dim = act_dim
        self.binary_outputs = binary_outputs
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
        self.scalar_head = nn.Linear(g2n.D_MODEL, len(TARGET_HORIZONS))
        self.binary_head = nn.Linear(g2n.D_MODEL, len(g2n.HORIZONS) * len(g2n.QUANTILES)) if binary_outputs else None

    def forward(
        self,
        past_z: torch.Tensor,
        past_a: torch.Tensor,
        future_z: torch.Tensor,
        future_delta: torch.Tensor,
        future_avail: torch.Tensor,
        t_scalar: torch.Tensor,
    ) -> tuple[torch.Tensor, torch.Tensor | None]:
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
                torch.zeros(b, g2n.MAX_FUTURE_TOKENS, self.act_dim, device=past_z.device, dtype=past_z.dtype),
                t_future,
            ],
            dim=-1,
        )
        query = torch.zeros(b, 1, self.emb_dim * 2 + self.act_dim + 1, device=past_z.device, dtype=past_z.dtype)
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
        enc = self.encoder(h, src_key_padding_mask=pad)[:, -1]
        scalar = self.scalar_head(enc)
        binary = self.binary_head(enc) if self.binary_head is not None else None
        return scalar, binary


def tensorize(exn: dict[str, np.ndarray]) -> dict[str, torch.Tensor]:
    return {
        "past_z": torch.from_numpy(exn["past_z"].astype(np.float32)),
        "past_a": torch.from_numpy(exn["past_a"].astype(np.float32)),
        "future_z": torch.from_numpy(exn["future_z"].astype(np.float32)),
        "future_delta": torch.from_numpy(exn["future_delta"].astype(np.float32)),
        "future_avail": torch.from_numpy(exn["future_avail"].astype(bool)),
        "t_scalar": torch.from_numpy(exn["t_scalar"].astype(np.float32)),
        "episode": torch.from_numpy(exn["episode"].astype(np.int64)),
        "y_binary": torch.from_numpy(exn["y"].reshape(len(exn["y"]), -1).astype(np.float32)),
        "valid_binary": torch.from_numpy(exn["valid"].reshape(len(exn["valid"]), -1).astype(bool)),
        "mean_err": torch.from_numpy(exn["mean_err_targets"].astype(np.float32)),
        "mean_err_valid": torch.from_numpy(exn["mean_err_valid"].astype(bool)),
        "log_mean_err": torch.from_numpy(np.log(exn["mean_err_targets"].astype(np.float32) + 1e-8)),
    }


def attach_targets(ex: dict[str, np.ndarray], clean: np.lib.npyio.NpzFile, split: str) -> dict[str, np.ndarray]:
    out = {k: (v.copy() if isinstance(v, np.ndarray) else v) for k, v in ex.items()}
    target = np.zeros((len(out["episode"]), len(TARGET_HORIZONS)), dtype=np.float32)
    valid = np.zeros_like(target, dtype=bool)
    for j, h in enumerate(TARGET_HORIZONS):
        idx = H_TO_LABEL_IDX[h]
        v = clean[f"{split}_valid"][:, idx].astype(bool)
        target[v, j] = clean[f"{split}_mean_err_to_h"][v, idx].astype(np.float32)
        valid[:, j] = v
    out["mean_err_targets"] = target
    out["mean_err_valid"] = valid
    return out


def train_residual_arm(
    name: str,
    train_ex: dict[str, np.ndarray],
    *,
    objective: str,
    lambda_reg: float | None = None,
) -> tuple[ResidualLedgerTransformer, dict[str, Any], dict[str, np.ndarray]]:
    torch.manual_seed(TORCH_SEED)
    np.random.seed(PYTHON_SEED)
    norm = g2n.compute_norm(train_ex)
    exn = g2n.normalize_examples(train_ex, norm)
    tensors = tensorize(exn)
    model = ResidualLedgerTransformer(
        exn["past_z"].shape[-1],
        exn["past_a"].shape[-1],
        binary_outputs=(objective == "multitask"),
    )
    opt = torch.optim.AdamW(model.parameters(), lr=g2n.LR)
    generator = torch.Generator().manual_seed(TORCH_SEED)
    n = len(exn["episode"])
    steps = 0
    skipped_rank_batches = 0
    t0 = time.perf_counter()
    model.train()
    for epoch in range(1, g2n.EPOCHS + 1):
        order = torch.randperm(n, generator=generator)
        for start in range(0, n, g2n.BATCH):
            idx = order[start : start + g2n.BATCH]
            scalar, binary = model(
                tensors["past_z"][idx],
                tensors["past_a"][idx],
                tensors["future_z"][idx],
                tensors["future_delta"][idx],
                tensors["future_avail"][idx],
                tensors["t_scalar"][idx],
            )
            losses: list[torch.Tensor] = []
            if objective == "regression":
                mask = tensors["mean_err_valid"][idx]
                losses.append(nn.functional.huber_loss(scalar[mask], tensors["log_mean_err"][idx][mask]))
            elif objective == "rank":
                rank_losses: list[torch.Tensor] = []
                for j in range(len(TARGET_HORIZONS)):
                    mask = tensors["mean_err_valid"][idx, j]
                    if bool(mask.sum() >= 2):
                        maybe = pairwise_logistic_loss(
                            scalar[:, j][mask],
                            tensors["mean_err"][idx, j][mask],
                            tensors["episode"][idx][mask],
                        )
                        if maybe is not None:
                            rank_losses.append(maybe)
                if rank_losses:
                    losses.append(torch.stack(rank_losses).mean())
                else:
                    skipped_rank_batches += 1
                    continue
            elif objective == "multitask":
                assert binary is not None
                valid = tensors["valid_binary"][idx]
                bce = nn.functional.binary_cross_entropy_with_logits(binary, tensors["y_binary"][idx], reduction="none")
                losses.append(bce[valid].sum() / torch.clamp(valid.sum().float(), min=1.0))

                mask = tensors["mean_err_valid"][idx]
                losses.append(float(lambda_reg) * nn.functional.huber_loss(scalar[mask], tensors["log_mean_err"][idx][mask]))

                rank_losses = []
                for j in range(len(TARGET_HORIZONS)):
                    mask_h = tensors["mean_err_valid"][idx, j]
                    if bool(mask_h.sum() >= 2):
                        maybe = pairwise_logistic_loss(
                            scalar[:, j][mask_h],
                            tensors["mean_err"][idx, j][mask_h],
                            tensors["episode"][idx][mask_h],
                        )
                        if maybe is not None:
                            rank_losses.append(maybe)
                if rank_losses:
                    losses.append(torch.stack(rank_losses).mean())
            else:
                raise ValueError(f"unknown objective: {objective}")

            loss = torch.stack(losses).sum()
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
        "objective": objective,
        "targets": "dual scalar heads for log(mean_err_to_h[h]+1e-8) or within-episode rank over mean_err_to_h[h], h in {1,5}",
        "epochs": g2n.EPOCHS,
        "batch": g2n.BATCH,
        "optimizer": "AdamW",
        "lr": g2n.LR,
        "optimizer_steps": int(steps),
        "skipped_rank_batches": int(skipped_rank_batches),
        "wall_time_seconds": round(time.perf_counter() - t0, 2),
        "parameter_count": int(sum(p.numel() for p in model.parameters())),
        "train_rows": int(n),
        "lambda_reg": None if lambda_reg is None else float(lambda_reg),
        "architecture": {
            "past_tokens": g2n.WINDOW,
            "max_future_tokens": g2n.MAX_FUTURE_TOKENS,
            "d_model": g2n.D_MODEL,
            "heads": g2n.N_HEADS,
            "layers": g2n.N_LAYERS,
        },
    }
    return model.eval(), info, norm


def predict_residual(
    model: ResidualLedgerTransformer,
    ex: dict[str, np.ndarray],
    norm: dict[str, np.ndarray],
    *,
    batch: int = 1024,
) -> np.ndarray:
    exn = g2n.normalize_examples(ex, norm)
    out = np.zeros((len(exn["episode"]), len(TARGET_HORIZONS)), dtype=np.float64)
    with torch.no_grad():
        for lo in range(0, len(out), batch):
            hi = min(lo + batch, len(out))
            score, _ = model(
                torch.from_numpy(exn["past_z"][lo:hi].astype(np.float32)),
                torch.from_numpy(exn["past_a"][lo:hi].astype(np.float32)),
                torch.from_numpy(exn["future_z"][lo:hi].astype(np.float32)),
                torch.from_numpy(exn["future_delta"][lo:hi].astype(np.float32)),
                torch.from_numpy(exn["future_avail"][lo:hi].astype(bool)),
                torch.from_numpy(exn["t_scalar"][lo:hi].astype(np.float32)),
            )
            out[lo:hi] = score.detach().cpu().numpy().astype(np.float64)
    return out


def evaluate_scores(score: np.ndarray, eval_ex: dict[str, np.ndarray], clean: np.lib.npyio.NpzFile) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for j, h in enumerate(TARGET_HORIZONS):
        y, mean_err, valid = targets_for_split(clean, "eval", h)
        metrics = bootstrap_detection_and_spearman(y, score[valid, j], mean_err, eval_ex["episode"][valid])
        auroc = metrics["failure_detection_auroc"]
        posthoc = POSTHOC[h]
        out[f"h{h}_q75"] = {
            "eval_rows": int(len(y)),
            "eval_episodes": int(len(np.unique(eval_ex["episode"][valid]))),
            "native_scalar_score_direction": "higher means predicted larger residual/error",
            "native": metrics,
            "posthoc_frozen_B": posthoc,
            "ci_separates_posthoc": bool(auroc["ci95_low"] > posthoc["ci95_high"]),
            "point_beats_posthoc": bool(auroc["observed"] > posthoc["observed"]),
        }
    return out


def load_posthoc_anchor() -> dict[str, Any]:
    report = json.loads(MATRIX_COMPLETION_JSON.read_text(encoding="utf-8"))
    out: dict[str, Any] = {}
    for h in TARGET_HORIZONS:
        metric = report["cells"]["B_posthoc_horizon"]["horizons"][f"h{h}_q75"]["metrics_eval_episode_bootstrap"][
            "failure_detection_auroc"
        ]
        expected = POSTHOC[h]
        deltas = {k: abs(float(metric[k]) - float(expected[k])) for k in expected}
        if any(v > 1e-12 for v in deltas.values()):
            raise SystemExit(f"posthoc frozen value mismatch for h={h}: {deltas}")
        out[f"h{h}_q75"] = metric
    return out


def write_markdown(report: dict[str, Any]) -> None:
    lines = [
        "# Native Residual Detection",
        "",
        f"- status: `{report['status']}`",
        f"- decision: `{report['decision']['verdict']}`",
        f"- skeleton anchor E h=1 q75 AUROC: `{report['skeleton_anchor']['observed']:.12f}` "
        f"(expected `{report['skeleton_anchor']['expected']:.12f}`, abs delta `{report['skeleton_anchor']['abs_delta']:.3g}`)",
        "",
        "## AUROC vs Post-Hoc",
        "",
        "| arm | objective | h=1 native AUROC [95% CI] | h=1 post-hoc AUROC [95% CI] | h=5 native AUROC [95% CI] | h=5 post-hoc AUROC [95% CI] |",
        "|---|---|---:|---:|---:|---:|",
    ]
    for arm, item in report["arms"].items():
        row = [arm, item["info"]["objective_label"]]
        for h in TARGET_HORIZONS:
            native = item["clean_eval"][f"h{h}_q75"]["native"]["failure_detection_auroc"]
            post = item["clean_eval"][f"h{h}_q75"]["posthoc_frozen_B"]
            row.append(f"`{native['observed']:.6f}` [`{native['ci95_low']:.6f}`, `{native['ci95_high']:.6f}`]")
            row.append(f"`{post['observed']:.6f}` [`{post['ci95_low']:.6f}`, `{post['ci95_high']:.6f}`]")
        lines.append("| " + " | ".join(row) + " |")

    lines.extend(
        [
            "",
            "## Spearman Attachment",
            "",
            "| arm | h=1 Spearman(score, mean_err) | h=5 Spearman(score, mean_err) |",
            "|---|---:|---:|",
        ]
    )
    for arm, item in report["arms"].items():
        h1 = item["clean_eval"]["h1_q75"]["native"]["spearman_score_mean_err"]
        h5 = item["clean_eval"]["h5_q75"]["native"]["spearman_score_mean_err"]
        lines.append(
            f"| {arm} | `{h1['observed']:.6f}` [`{h1['ci95_low']:.6f}`, `{h1['ci95_high']:.6f}`] "
            f"| `{h5['observed']:.6f}` [`{h5['ci95_low']:.6f}`, `{h5['ci95_high']:.6f}`] |"
        )

    lines.extend(
        [
            "",
            "## Decision",
            "",
            f"- positive(B breakthrough): `{report['decision']['positive']}`",
            f"- best native arm: `{report['decision']['best_arm']}` h=`{report['decision']['best_horizon']}` AUROC=`{report['decision']['best_auroc']:.6f}`",
            f"- reason: {report['decision']['reason']}",
            "",
            "## Not Claimed",
        ]
    )
    lines.extend(f"- {x}" for x in report["not_claimed"])
    MD_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")


def decide(arms: dict[str, Any]) -> dict[str, Any]:
    positive_hits: list[tuple[str, int, float]] = []
    best_arm = ""
    best_h = 0
    best_auc = -1.0
    any_best_le_posthoc = False
    any_ci_overlap_for_best = False

    for arm, item in arms.items():
        for h in TARGET_HORIZONS:
            auc = item["clean_eval"][f"h{h}_q75"]["native"]["failure_detection_auroc"]
            obs = float(auc["observed"])
            if obs > best_auc:
                best_auc = obs
                best_arm = arm
                best_h = h
            if auc["ci95_low"] > POSTHOC[h]["ci95_high"]:
                other_h = 5 if h == 1 else 1
                other_auc = item["clean_eval"][f"h{other_h}_q75"]["native"]["failure_detection_auroc"]
                if other_auc["ci95_low"] >= E_CURRENT_CI_LOW[other_h]:
                    positive_hits.append((arm, h, obs))

    best_posthoc = POSTHOC[best_h]["observed"] if best_h else float("nan")
    if best_auc <= best_posthoc:
        any_best_le_posthoc = True
    if best_h:
        best_ci = arms[best_arm]["clean_eval"][f"h{best_h}_q75"]["native"]["failure_detection_auroc"]
        any_ci_overlap_for_best = bool(best_ci["ci95_low"] <= POSTHOC[best_h]["ci95_high"])

    if positive_hits:
        arm, h, obs = max(positive_hits, key=lambda x: x[2])
        return {
            "positive": True,
            "verdict": "positive_B_breakthrough",
            "best_arm": best_arm,
            "best_horizon": int(best_h),
            "best_auroc": float(best_auc),
            "positive_hits": [{"arm": a, "horizon": int(hh), "auroc": float(o)} for a, hh, o in positive_hits],
            "winning_hit": {"arm": arm, "horizon": int(h), "auroc": float(obs)},
            "reason": "at least one native residual arm has AUROC CI95_low above the corresponding post-hoc CI95_high and the other horizon is not below E current CI-low",
        }

    if any_best_le_posthoc:
        reason = "best native residual point estimate is not above the corresponding post-hoc point estimate"
    elif any_ci_overlap_for_best:
        reason = "best native residual arm improves only by point estimate or not at all; its CI overlaps the corresponding post-hoc CI"
    else:
        reason = "no arm satisfies the predeclared separation plus other-horizon guard"
    return {
        "positive": False,
        "verdict": "failed_parity_is_upper_bound",
        "best_arm": best_arm,
        "best_horizon": int(best_h),
        "best_auroc": float(best_auc),
        "positive_hits": [],
        "reason": reason,
    }


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

    np.random.seed(PYTHON_SEED)
    torch.manual_seed(TORCH_SEED)
    torch.set_num_threads(int(os.environ.get("G2N_TORCH_THREADS", "4")))
    data = dict(np.load(LATENT_NPZ, allow_pickle=True))
    splits = split_episodes(data["emb"].shape[0])
    if SPLIT_SEED != 1701 or int(len(splits["eval"])) <= 0:
        raise SystemExit("split sanity failed")
    clean = np.load(CLEAN_LABELS)
    posthoc_from_report = load_posthoc_anchor()

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
    if e_delta > ANCHOR_TOL:
        raise SystemExit(f"E skeleton anchor failed: observed={e_obs:.17g}, expected={EXPECTED_E_H1_AUROC:.17g}")

    train_ex = attach_targets(clean_train_ex, clean, "train")
    eval_ex = attach_targets(clean_eval_ex, clean, "eval")
    arm_specs = [
        ("R-reg", "regression", None, "Huber(log mean_err_to_h[h]) dual-head"),
        ("R-rank", "rank", None, "within-episode pairwise logistic ranking over mean_err_to_h[h] dual-head"),
        ("R-multitask-lambda0p25", "multitask", 0.25, "BCE horizon + 0.25*Huber(log mean_err) + pairwise rank"),
        ("R-multitask-lambda1p0", "multitask", 1.0, "BCE horizon + 1.0*Huber(log mean_err) + pairwise rank"),
    ]

    arms: dict[str, Any] = {}
    for arm, objective, lambda_reg, label in arm_specs:
        print(f"[train] {arm}", flush=True)
        model, info, norm = train_residual_arm(arm, train_ex, objective=objective, lambda_reg=lambda_reg)
        score = predict_residual(model, eval_ex, norm)
        info["objective_label"] = label
        arms[arm] = {
            "info": info,
            "clean_eval": evaluate_scores(score, eval_ex, clean),
        }

    decision = decide(arms)
    report = {
        "status": "ok",
        "schema_id": "lewm.native_residual_detection",
        "protocol": {
            "seeds": {"numpy": PYTHON_SEED, "torch": TORCH_SEED, "split": SPLIT_SEED, "bootstrap": BOOTSTRAP_SEED},
            "bootstrap_resamples": BOOTSTRAPS,
            "primary_quantile": PRIMARY_Q,
            "target_horizons": list(TARGET_HORIZONS),
            "hyperparameters_source": "_g2n_native_ledger.py arm E",
            "epochs": g2n.EPOCHS,
            "batch": g2n.BATCH,
            "optimizer": "AdamW",
            "lr": g2n.LR,
            "architecture": {
                "past_tokens": g2n.WINDOW,
                "max_future_tokens": g2n.MAX_FUTURE_TOKENS,
                "d_model": g2n.D_MODEL,
                "heads": g2n.N_HEADS,
                "layers": g2n.N_LAYERS,
                "input": "past (z,a) window + pred_z[:5] + future_delta, same as native arm E",
            },
            "decision_rule": (
                "positive iff h=1 or h=5 native scalar/multitask AUROC CI95_low > corresponding post-hoc "
                "AUROC CI95_high, and the other horizon is not below native E current CI95_low"
            ),
        },
        "precursors": {
            "clean_npz": str(CLEAN_LABELS),
            "latent_npz": str(LATENT_NPZ),
            "native_ledger_py": str(NATIVE_LEDGER),
            "allocation_bridge_py": str(ALLOCATION_BRIDGE),
            "matrix_completion_py": str(MATRIX_COMPLETION),
        },
        "skeleton_anchor": {
            "arm": "E",
            "metric": "clean eval h=1 q75 failure_detection_auroc",
            "observed": e_obs,
            "expected": EXPECTED_E_H1_AUROC,
            "abs_delta": e_delta,
            "tolerance": ANCHOR_TOL,
            "train_info": e_info,
            "h1_q75": e_eval["h1_q75"]["failure_detection_auroc"],
            "h5_q75": e_eval["h5_q75"]["failure_detection_auroc"],
        },
        "posthoc_control": {
            "source": "reports/g2n_matrix_completion.json cells.B_posthoc_horizon frozen values",
            "horizons": posthoc_from_report,
        },
        "native_E_current_ci_low_guard": E_CURRENT_CI_LOW,
        "arms": arms,
        "decision": decision,
        "not_claimed": [
            "Spearman is reported only as an attachment and is not used for the B breakthrough decision",
            "single latent export and single checkpoint; episode bootstrap is not independent world-seed replication",
            "post-hoc control is the frozen B_posthoc_horizon value from g2n_matrix_completion, not retuned here",
            "lambda is limited to the predeclared {0.25, 1.0}; no hyperparameter tuning or model selection beyond reporting best observed arm",
            "no planning/control benefit is claimed",
        ],
    }

    cleaned = clean_json(report)
    JSON_PATH.write_text(json.dumps(cleaned, indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(cleaned)
    print(f"[done] wrote {JSON_PATH} and {MD_PATH}", flush=True)


if __name__ == "__main__":
    main()

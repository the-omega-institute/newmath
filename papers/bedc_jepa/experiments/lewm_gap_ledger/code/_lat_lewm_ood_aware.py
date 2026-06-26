"""OOD-aware training for the LAT port, mirroring the phase2c protocol.

Arms (all share the port's architecture, seeds, and hyperparameters):
- lat_clean_only: trained on clean train windows only (identical call to the
  committed port run; must reproduce its eval AUROC bit-for-bit).
- lat_ood_aware: trained on clean train windows plus perturbed train windows
  from every (family, strength) slice of the phase2a perturbation grid.
- leave-one-out (one per family): trained on clean plus the other four
  families' perturbed train windows; the held-out family is evaluation-only.

Protocol mirrored from phase2c:
- failure truth y = perturbed prediction_mse > clean train p75 (same tau as
  the port); perturbed latents come from re-encoding perturbed frames through
  the LeWM encoder (cached under reports/lat_ood_emb_cache, train and eval);
- per (family, strength) evaluation with episode bootstrap (300) reporting
  failure_detection_auroc / bedc UER / vanilla UER / declared-gap CIs;
- point claim is positive iff AUROC ci95_low > 0.5 AND bedc UER ci95_high <
  vanilla UER ci95_low; per family both the final-strength claim and the
  nonzero-pooled claim are recorded; single-class slices are flagged
  fail-closed (AUROC unidentifiable, reported 0.5);
- leave-one-out headline is the held-out family's nonzero-pooled claim.
"""

from __future__ import annotations

import json
import time
from typing import Any

import h5py
import hdf5plugin  # noqa: F401 - registers blosc HDF5 filter
import numpy as np
import torch
from huggingface_hub import hf_hub_download

from lewm_latent_probe import build_model, load_checkpoint
from _phase2a_brittleness_gap import (
    H5_PATH,
    MODEL_REPO,
    perturbation_grid,
    predict_eval_rows,
)
from _phase2c_ood_aware_gap import encode_split_episodes_batched
from _phase1c_gap_ledger import auroc_rank, flatten_transition_rows
from _lat_lewm_port import (
    BATCH,
    BOOTSTRAP_SEED,
    DYNAMICS_WEIGHT,
    EPOCHS,
    LR,
    NPZ_PATH,
    PYTHON_SEED,
    REPORT_DIR,
    LedgerAwareTransformer,
    build_windows,
    split_episodes,
    train_arm,
)
from _lat_lewm_ood import (
    EMB_CACHE,
    build_perturbed_windows,
    load_emb_cache,
    save_emb_cache,
    strength_token,
)

JSON_PATH = REPORT_DIR / "lewm_ledger_aware_transformer_ood_aware.json"
MD_PATH = REPORT_DIR / "lewm_ledger_aware_transformer_ood_aware.md"
PORT_JSON = REPORT_DIR / "lewm_ledger_aware_transformer.json"
OOD_BOOTSTRAPS = 300


def split_emb_cache_path(split_name: str, family: str, strength: float):
    return EMB_CACHE / f"{split_name}_{family}_{strength_token(strength)}.npz"


def mse_cache_path(split_name: str, family: str, strength: float):
    return EMB_CACHE / f"mse_{split_name}_{family}_{strength_token(strength)}.npz"


def slice_metrics(
    y: np.ndarray,
    score: np.ndarray,
    episode: np.ndarray,
    *,
    seed: int,
    n_boot: int = OOD_BOOTSTRAPS,
) -> dict[str, Any]:
    def basic(yy: np.ndarray, ss: np.ndarray) -> dict[str, float]:
        return {
            "failure_detection_auroc": auroc_rank(yy, ss),
            "bedc_gap_head_uer": float(np.mean((yy > 0) & (ss < 0.5))),
            "vanilla_uer": float(np.mean(yy)),
            "declared_gap_rate": float(np.mean(ss >= 0.5)),
        }

    observed = basic(y, score)
    rng = np.random.default_rng(seed)
    unique_ep = np.unique(episode)
    by_ep = [np.where(episode == ep)[0] for ep in unique_ep]
    values: dict[str, list[float]] = {k: [] for k in observed}
    for _ in range(n_boot):
        sampled = rng.integers(0, len(by_ep), size=len(by_ep))
        idx = np.concatenate([by_ep[i] for i in sampled])
        m = basic(y[idx], score[idx])
        for k, v in m.items():
            values[k].append(v)
    out: dict[str, Any] = {}
    for k, obs in observed.items():
        arr = np.asarray(values[k], dtype=np.float64)
        out[k] = {
            "observed": float(obs),
            "ci95_low": float(np.nanpercentile(arr, 2.5)),
            "ci95_high": float(np.nanpercentile(arr, 97.5)),
        }
    return out


def point_claim(metrics: dict[str, Any], single_class: bool) -> dict[str, Any]:
    auroc_pos = bool(metrics["failure_detection_auroc"]["ci95_low"] > 0.5)
    uer_pos = bool(
        metrics["bedc_gap_head_uer"]["ci95_high"] < metrics["vanilla_uer"]["ci95_low"]
    )
    return {
        "auroc_ci_low_gt_0_5": auroc_pos,
        "bedc_uer_ci_high_lt_vanilla_ci_low": uer_pos,
        "claim": "positive" if auroc_pos and uer_pos else "negative_or_inconclusive",
        "single_class_truth": single_class,
    }


def train_lat(
    win_emb: np.ndarray,
    win_act: np.ndarray,
    y: np.ndarray,
    dyn_target_emb: np.ndarray,
    *,
    seed: int,
) -> tuple[Any, tuple[np.ndarray, np.ndarray], dict[str, Any]]:
    """Generalized LAT trainer over an explicit window dataset (same
    architecture, epochs, batch, lr, and joint dynamics loss as the port)."""
    torch.manual_seed(seed)
    emb_dim = win_emb.shape[2]
    act_dim = win_act.shape[2]
    flat = win_emb.reshape(-1, emb_dim)
    emb_mean = flat.mean(axis=0)
    emb_std = flat.std(axis=0) + 1e-6

    model = LedgerAwareTransformer(emb_dim, act_dim)
    opt = torch.optim.AdamW(model.parameters(), lr=LR)
    bce = torch.nn.BCEWithLogitsLoss()

    x_emb = torch.from_numpy(((win_emb - emb_mean) / emb_std).astype(np.float32))
    x_act = torch.from_numpy(win_act.astype(np.float32))
    y_t = torch.from_numpy(y.astype(np.float32))
    target = torch.from_numpy(((dyn_target_emb - emb_mean) / emb_std).astype(np.float32))

    g = torch.Generator().manual_seed(seed)
    n = len(y)
    steps = 0
    t0 = time.perf_counter()
    model.train()
    for _ in range(EPOCHS):
        order = torch.randperm(n, generator=g)
        for start in range(0, n, BATCH):
            sel = order[start : start + BATCH]
            logit, dyn = model(x_emb[sel], x_act[sel])
            loss = bce(logit, y_t[sel])
            if DYNAMICS_WEIGHT > 0.0:
                loss = loss + DYNAMICS_WEIGHT * torch.nn.functional.mse_loss(dyn, target[sel])
            if not torch.isfinite(loss):
                raise SystemExit("fail-closed: non-finite loss in ood-aware training")
            opt.zero_grad()
            loss.backward()
            opt.step()
            steps += 1
    info = {
        "train_rows": int(n),
        "train_failure_rate": float(np.mean(y)),
        "optimizer_steps": int(steps),
        "epochs": EPOCHS,
        "wall_time_seconds": round(time.perf_counter() - t0, 2),
        "torch_seed": seed,
        "device": "cpu",
    }
    return model, (emb_mean, emb_std), info


def score_lat(
    model: Any,
    norm: tuple[np.ndarray, np.ndarray],
    win_emb: np.ndarray,
    win_act: np.ndarray,
) -> np.ndarray:
    emb_mean, emb_std = norm
    scores = np.empty(len(win_emb), dtype=np.float64)
    model.eval()
    with torch.no_grad():
        for start in range(0, len(win_emb), 1024):
            sl = slice(start, min(start + 1024, len(win_emb)))
            normed = ((win_emb[sl] - emb_mean) / emb_std).astype(np.float32)
            logit, _ = model(torch.from_numpy(normed), torch.from_numpy(win_act[sl].astype(np.float32)))
            scores[sl] = torch.sigmoid(logit).numpy()
    return scores


def main() -> None:
    np.random.seed(PYTHON_SEED)
    data = dict(np.load(NPZ_PATH))
    win_rows = build_windows(data)
    n_ep = data["emb"].shape[0]
    splits = split_episodes(n_ep)
    masks = {name: np.isin(win_rows["episode"], eps) for name, eps in splits.items()}
    train_mask, eval_mask = masks["train"], masks["eval"]

    tau = float(np.percentile(win_rows["mse"][train_mask], 75))
    y_clean = (win_rows["mse"] > tau).astype(np.int8)

    clean_scores, clean_info, clean_model, clean_norm = train_arm(
        win_rows, train_mask, y_clean, seed=PYTHON_SEED, dynamics_weight=DYNAMICS_WEIGHT,
        label_permutation_seed=None, return_artifacts=True,
    )
    port = json.loads(PORT_JSON.read_text(encoding="utf-8"))
    committed = port["arms"]["lat_learned"]["metrics_eval_episode_bootstrap"]["failure_detection_auroc"]["observed"]
    got = auroc_rank(y_clean[eval_mask], clean_scores[eval_mask])
    if abs(got - committed) > 1e-9:
        raise SystemExit(f"clean anchor mismatch: {got} != {committed}")
    print(f"[anchor] clean LAT reproduces committed port AUROC {got:.6f}", flush=True)

    rows1c = flatten_transition_rows(data)
    split_rows_idx = {
        name: np.where(np.isin(rows1c["episode"], splits[name]))[0] for name in ("train", "eval")
    }

    device = torch.device("cpu")
    checkpoint_path = hf_hub_download(MODEL_REPO, "weights.pt", repo_type="model")
    config_path = hf_hub_download(MODEL_REPO, "config.json", repo_type="model")
    with open(config_path, "r", encoding="utf-8") as f:
        config = json.load(f)
    lewm = build_model(config)
    load_checkpoint(lewm, checkpoint_path)
    lewm.to(device).eval().requires_grad_(False)

    grids = perturbation_grid()
    families = list(grids)

    # Materialize perturbed window datasets per (family, strength, split).
    slices: dict[tuple[str, float, str], dict[str, Any]] = {}
    with h5py.File(H5_PATH, "r") as h5:
        for family in families:
            for strength in grids[family]:
                if float(strength) == 0.0:
                    continue
                for split_name in ("train", "eval"):
                    key = (family, float(strength), split_name)
                    emb_path = split_emb_cache_path(split_name, family, float(strength))
                    pert_emb_by_ep = load_emb_cache(emb_path)
                    if pert_emb_by_ep is None:
                        print(f"[encode] {split_name} {family} strength={strength}", flush=True)
                        pert_emb_by_ep = encode_split_episodes_batched(
                            h5, lewm, config, data, splits[split_name], family, float(strength),
                            device, encode_batch_size=64,
                        )
                        save_emb_cache(emb_path, pert_emb_by_ep)
                    mse_path = mse_cache_path(split_name, family, float(strength))
                    if mse_path.exists():
                        raw = np.load(mse_path)
                        valid_idx, mse = raw["row_idx"].astype(np.int64), raw["mse"].astype(np.float64)
                    else:
                        valid_idx, mse = predict_eval_rows(
                            lewm, data, rows1c, split_rows_idx[split_name], pert_emb_by_ep,
                            device, batch_size=512,
                        )
                        np.savez_compressed(mse_path, row_idx=valid_idx, mse=mse)
                    episodes = rows1c["episode"][valid_idx]
                    ts = rows1c["t"][valid_idx]
                    win_emb, win_act = build_perturbed_windows(
                        pert_emb_by_ep, data["action"].astype(np.float32), episodes, ts
                    )
                    dyn_target = np.stack(
                        [pert_emb_by_ep[int(ep)][int(t) + 1] for ep, t in zip(episodes, ts)]
                    ).astype(np.float32)
                    slices[key] = {
                        "family": family,
                        "strength": float(strength),
                        "split": split_name,
                        "win_emb": win_emb,
                        "win_act": win_act,
                        "y": (np.asarray(mse, dtype=np.float64) > tau).astype(np.int8),
                        "episode": episodes.astype(np.int64),
                        "dyn_target": dyn_target,
                    }

    clean_train = {
        "win_emb": win_rows["win_emb"][train_mask],
        "win_act": win_rows["win_act"][train_mask],
        "y": y_clean[train_mask],
        "episode": win_rows["episode"][train_mask],
        "dyn_target": win_rows["next_emb"][train_mask],
    }
    clean_eval = {
        "win_emb": win_rows["win_emb"][eval_mask],
        "win_act": win_rows["win_act"][eval_mask],
        "y": y_clean[eval_mask],
        "episode": win_rows["episode"][eval_mask],
    }

    def assemble(train_families: list[str]) -> dict[str, np.ndarray]:
        parts = [clean_train] + [
            slices[(f, float(s), "train")]
            for f in train_families
            for s in grids[f]
            if float(s) != 0.0
        ]
        return {
            "win_emb": np.concatenate([p["win_emb"] for p in parts], axis=0),
            "win_act": np.concatenate([p["win_act"] for p in parts], axis=0),
            "y": np.concatenate([p["y"] for p in parts], axis=0),
            "dyn_target": np.concatenate([p["dyn_target"] for p in parts], axis=0),
        }

    def evaluate(model: Any, norm: tuple[np.ndarray, np.ndarray], *, seed_offset: int) -> dict[str, Any]:
        clean_score = score_lat(model, norm, clean_eval["win_emb"], clean_eval["win_act"])
        out: dict[str, Any] = {
            "clean_eval": {
                "metrics": slice_metrics(
                    clean_eval["y"], clean_score, clean_eval["episode"], seed=BOOTSTRAP_SEED + seed_offset
                ),
            }
        }
        fam_reports: dict[str, Any] = {}
        for family_i, family in enumerate(families):
            points = []
            pooled_y, pooled_s, pooled_ep = [], [], []
            for strength_i, strength in enumerate([s for s in grids[family] if float(s) != 0.0], start=1):
                sl = slices[(family, float(strength), "eval")]
                score = score_lat(model, norm, sl["win_emb"], sl["win_act"])
                single = bool(sl["y"].min() == sl["y"].max())
                m = slice_metrics(
                    sl["y"], score, sl["episode"],
                    seed=BOOTSTRAP_SEED + seed_offset + 1000 * family_i + strength_i,
                )
                points.append(
                    {
                        "strength": float(strength),
                        "sample_count": int(len(sl["y"])),
                        "single_class_truth": single,
                        "metrics": m,
                        "claim": point_claim(m, single),
                    }
                )
                pooled_y.append(sl["y"])
                pooled_s.append(score)
                pooled_ep.append(sl["episode"])
            yy = np.concatenate(pooled_y)
            ss = np.concatenate(pooled_s)
            ee = np.concatenate(pooled_ep)
            pooled_m = slice_metrics(
                yy, ss, ee, seed=BOOTSTRAP_SEED + seed_offset + 1000 * family_i + 101
            )
            pooled_single = bool(yy.min() == yy.max())
            fam_reports[family] = {
                "points": points,
                "nonzero_pooled": {
                    "metrics": pooled_m,
                    "single_class_truth": pooled_single,
                    "claim": point_claim(pooled_m, pooled_single),
                },
                "final_claim": points[-1]["claim"],
            }
        out["families"] = fam_reports
        return out

    print("[train] lat_ood_aware (clean + all perturbed train slices)", flush=True)
    ood_set = assemble(families)
    ood_model, ood_norm, ood_info = train_lat(
        ood_set["win_emb"], ood_set["win_act"], ood_set["y"], ood_set["dyn_target"],
        seed=PYTHON_SEED,
    )

    arms: dict[str, Any] = {
        "lat_clean_only": {
            "info": clean_info,
            **evaluate(clean_model, clean_norm, seed_offset=0),
        },
        "lat_ood_aware": {
            "info": ood_info,
            **evaluate(ood_model, ood_norm, seed_offset=20000),
        },
    }

    leave_one_out: dict[str, Any] = {}
    for family_i, heldout in enumerate(families):
        print(f"[train] leave-one-out heldout={heldout}", flush=True)
        loo_set = assemble([f for f in families if f != heldout])
        loo_model, loo_norm, loo_info = train_lat(
            loo_set["win_emb"], loo_set["win_act"], loo_set["y"], loo_set["dyn_target"],
            seed=PYTHON_SEED,
        )
        full = evaluate(loo_model, loo_norm, seed_offset=30000 + 1000 * family_i)
        leave_one_out[heldout] = {
            "info": loo_info,
            "heldout_family": full["families"][heldout],
            "clean_eval": full["clean_eval"],
        }

    strict_pos = [
        f for f in families
        if arms["lat_ood_aware"]["families"][f]["final_claim"]["claim"] == "positive"
    ]
    loo_pos = [
        f for f in families
        if leave_one_out[f]["heldout_family"]["nonzero_pooled"]["claim"]["claim"] == "positive"
    ]
    conclusion = {
        "strict_final_positive_families": strict_pos,
        "strict_final_negative_or_inconclusive_families": [f for f in families if f not in strict_pos],
        "leave_one_out_positive_families": loo_pos,
        "leave_one_out_negative_or_inconclusive_families": [f for f in families if f not in loo_pos],
    }

    report = {
        "schema_id": "lewm.ledger_aware_transformer_port.ood_aware_training",
        "protocol": {
            "mirrors": "phase2c ood-aware protocol at the LAT level",
            "tau_err_train_p75": tau,
            "training_mix": "clean train windows + perturbed train windows (all strengths of the listed families)",
            "perturbation_grid": {k: [s for s in v if float(s) != 0.0] for k, v in grids.items()},
            "bootstraps": OOD_BOOTSTRAPS,
            "bootstrap_unit": "eval episodes",
            "claim_criteria": [
                "AUROC ci95_low > 0.5",
                "bedc UER ci95_high < vanilla UER ci95_low",
            ],
            "single_class_policy": "AUROC unidentifiable; slice flagged fail-closed",
            "clean_anchor_reproduces_port": True,
        },
        "arms": arms,
        "leave_one_out": leave_one_out,
        "conclusion": conclusion,
        "not_claimed": [
            "global architecture superiority",
            "replacement of the phase2c logistic ood-aware head",
            "benchmark reproduction or public-benchmark superiority",
            "transfer beyond the tworooms checkpoint or this perturbation grid",
        ],
    }
    JSON_PATH.write_text(json.dumps(report, indent=2), encoding="utf-8")

    def fmt(m: dict[str, Any]) -> str:
        return f"{m['observed']:.3f} [{m['ci95_low']:.3f}, {m['ci95_high']:.3f}]"

    lines = [
        "# OOD-aware training for the LAT port (phase2c protocol at the LAT level)",
        "",
        f"- clean anchor reproduces committed port AUROC {committed:.6f}",
        f"- ood_aware training rows: {ood_info['train_rows']} (failure rate {ood_info['train_failure_rate']:.3f})",
        f"- strict final-strength positive families: {conclusion['strict_final_positive_families'] or 'none'}",
        f"- leave-one-out positive families (nonzero pooled): {conclusion['leave_one_out_positive_families'] or 'none'}",
        "",
        "## lat_ood_aware per-slice (eval)",
        "",
        "| family | strength | vanilla UER | AUROC | UER | declared | claim |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for family in families:
        for p in arms["lat_ood_aware"]["families"][family]["points"]:
            m = p["metrics"]
            flag = " (single-class)" if p["single_class_truth"] else ""
            lines.append(
                f"| `{family}` | {p['strength']:g} | {m['vanilla_uer']['observed']:.3f} "
                f"| {fmt(m['failure_detection_auroc'])}{flag} | {fmt(m['bedc_gap_head_uer'])} "
                f"| {fmt(m['declared_gap_rate'])} | {p['claim']['claim']} |"
            )
    lines += ["", "## leave-one-out (held-out family, nonzero pooled)", "",
              "| held-out | AUROC | UER | vanilla UER | declared | claim |",
              "| --- | --- | --- | --- | --- | --- |"]
    for family in families:
        hf = leave_one_out[family]["heldout_family"]["nonzero_pooled"]
        m = hf["metrics"]
        lines.append(
            f"| `{family}` | {fmt(m['failure_detection_auroc'])} | {fmt(m['bedc_gap_head_uer'])} "
            f"| {fmt(m['vanilla_uer'])} | {fmt(m['declared_gap_rate'])} | {hf['claim']['claim']} |"
        )
    lines += ["", "## clean eval per arm (does OOD-aware training cost clean performance?)", ""]
    for arm_name in ("lat_clean_only", "lat_ood_aware"):
        m = arms[arm_name]["clean_eval"]["metrics"]
        lines.append(
            f"- `{arm_name}`: AUROC {fmt(m['failure_detection_auroc'])}, UER {fmt(m['bedc_gap_head_uer'])}, "
            f"declared {fmt(m['declared_gap_rate'])}"
        )
    MD_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(json.dumps(conclusion, indent=2))
    print(MD_PATH)


if __name__ == "__main__":
    main()

"""OOD arm for the LAT port: the clean-trained ledger-aware transformer
evaluated under the phase2a perturbation grid on real LeWM latents.

Question (descriptive, no new positive claim): does the clean-trained LAT-style
ledger head keep detecting the LeWM predictor's failures when eval frames are
visually perturbed, or does it collapse like the clean-only logistic gap head
did in phase2a?

Protocol:
- identical clean training to `_lat_lewm_port.py` (same seeds; the rebuilt
  model must reproduce the committed port report's eval AUROC bit-for-bit,
  asserted at startup);
- perturbed eval latents: eval-split frames re-encoded through the LeWM
  encoder after `perturb_frames` (same families/strengths as phase2a's
  `perturbation_grid`), predictor errors via `predict_eval_rows`;
- failure truth y = perturbed prediction_mse > the SAME clean train p75 tau;
- per (family, strength): episode-level bootstrap (300, matching the phase2a
  brittleness protocol); single-class slices are recorded fail-closed;
- vanilla row per slice = failure rate (a no-ledger model declares nothing);
- phase2a clean-only logistic head numbers quoted per slice for comparison.

Perturbed eval emb sequences are cached under reports/lat_ood_emb_cache/ so
reruns and future OOD-aware extensions skip the encoder pass.
"""

from __future__ import annotations

import json
from pathlib import Path
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
from _phase2c_ood_aware_gap import cache_path as phase2c_cache_path
from _phase1c_gap_ledger import flatten_transition_rows
from _lat_lewm_port import (
    BOOTSTRAP_SEED,
    DYNAMICS_WEIGHT,
    NPZ_PATH,
    PYTHON_SEED,
    REPORT_DIR,
    WINDOW,
    basic_metrics,
    bootstrap_metrics_by_episode,
    build_windows,
    fmt_ci,
    split_episodes,
    train_arm,
)

JSON_PATH = REPORT_DIR / "lewm_ledger_aware_transformer_ood.json"
MD_PATH = REPORT_DIR / "lewm_ledger_aware_transformer_ood.md"
PORT_JSON = REPORT_DIR / "lewm_ledger_aware_transformer.json"
PHASE2A_JSON = REPORT_DIR / "lewm_brittleness_gap.json"
EMB_CACHE = REPORT_DIR / "lat_ood_emb_cache"
OOD_BOOTSTRAPS = 300


def strength_token(strength: float) -> str:
    return f"{strength:g}".replace(".", "p").replace("-", "m")


def emb_cache_path(family: str, strength: float) -> Path:
    return EMB_CACHE / f"eval_{family}_{strength_token(strength)}.npz"


def load_emb_cache(path: Path) -> dict[int, np.ndarray] | None:
    if not path.exists():
        return None
    raw = np.load(path)
    return {int(k): raw[k] for k in raw.files}


def save_emb_cache(path: Path, pert_emb_by_ep: dict[int, np.ndarray]) -> None:
    path.parent.mkdir(exist_ok=True)
    tmp = path.with_name("tmp_" + path.name)
    np.savez_compressed(tmp, **{str(ep): arr.astype(np.float32) for ep, arr in pert_emb_by_ep.items()})
    tmp.replace(path)


def score_windows(
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
            logit, _ = model(torch.from_numpy(normed), torch.from_numpy(win_act[sl]))
            scores[sl] = torch.sigmoid(logit).numpy()
    return scores


def build_perturbed_windows(
    pert_emb_by_ep: dict[int, np.ndarray],
    action: np.ndarray,
    episodes: np.ndarray,
    ts: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    emb_dim = next(iter(pert_emb_by_ep.values())).shape[-1]
    act_dim = action.shape[-1]
    n = len(episodes)
    win_emb = np.empty((n, WINDOW, emb_dim), dtype=np.float32)
    win_act = np.empty((n, WINDOW, act_dim), dtype=np.float32)
    for i, (ep, t) in enumerate(zip(episodes, ts)):
        seq = pert_emb_by_ep[int(ep)]
        for w in range(WINDOW):
            src = max(0, int(t) - WINDOW + 1 + w)
            win_emb[i, w] = seq[src]
            win_act[i, w] = action[int(ep), src]
    return win_emb, win_act


def phase2a_reference() -> dict[str, dict[str, Any]]:
    if not PHASE2A_JSON.exists():
        return {}
    p = json.loads(PHASE2A_JSON.read_text(encoding="utf-8"))
    out: dict[str, dict[str, Any]] = {}
    for family, pack in p.get("families", {}).items():
        for point in pack.get("points", []):
            key = f"{family}@{float(point.get('strength')):g}"
            m = point.get("metrics_episode_bootstrap", {})
            out[key] = {
                "failure_detection_auroc": m.get("failure_detection_auroc"),
                "unlogged_error_rate": m.get("unlogged_error_rate"),
                "observed": point.get("observed"),
            }
    return out


def main() -> None:
    np.random.seed(PYTHON_SEED)
    data = dict(np.load(NPZ_PATH))
    win_rows = build_windows(data)
    n_ep = data["emb"].shape[0]
    splits = split_episodes(n_ep)
    masks = {name: np.isin(win_rows["episode"], eps) for name, eps in splits.items()}
    train_mask, eval_mask = masks["train"], masks["eval"]

    tau_err = float(np.percentile(win_rows["mse"][train_mask], 75))
    y_err = (win_rows["mse"] > tau_err).astype(np.int8)

    scores, info, model, norm = train_arm(
        win_rows, train_mask, y_err, seed=PYTHON_SEED, dynamics_weight=DYNAMICS_WEIGHT,
        label_permutation_seed=None, return_artifacts=True,
    )
    if info.get("status") != "trained":
        raise SystemExit(f"clean LAT retrain fail-closed: {info}")

    clean_eval = basic_metrics(y_err[eval_mask], scores[eval_mask])
    port = json.loads(PORT_JSON.read_text(encoding="utf-8"))
    committed = port["arms"]["lat_learned"]["metrics_eval_episode_bootstrap"]["failure_detection_auroc"]["observed"]
    if abs(clean_eval["failure_detection_auroc"] - committed) > 1e-9:
        raise SystemExit(
            f"retrained clean LAT does not reproduce the committed port report: "
            f"{clean_eval['failure_detection_auroc']} != {committed}"
        )

    rows1c = flatten_transition_rows(data)
    eval_rows_idx = np.where(np.isin(rows1c["episode"], splits["eval"]))[0]

    device = torch.device("cpu")
    checkpoint_path = hf_hub_download(MODEL_REPO, "weights.pt", repo_type="model")
    config_path = hf_hub_download(MODEL_REPO, "config.json", repo_type="model")
    with open(config_path, "r", encoding="utf-8") as f:
        config = json.load(f)
    lewm = build_model(config)
    load_checkpoint(lewm, checkpoint_path)
    lewm.to(device).eval().requires_grad_(False)

    ref = phase2a_reference()
    grids = perturbation_grid()
    families: dict[str, Any] = {}
    fail_closed_slices: list[str] = []

    with h5py.File(H5_PATH, "r") as h5:
        for family, strengths in grids.items():
            points: list[dict[str, Any]] = []
            for strength in strengths:
                if strength == 0.0:
                    continue
                print(f"[lat-ood] {family} strength={strength}", flush=True)
                cache = emb_cache_path(family, strength)
                pert_emb_by_ep = load_emb_cache(cache)
                if pert_emb_by_ep is None:
                    pert_emb_by_ep = encode_split_episodes_batched(
                        h5, lewm, config, data, splits["eval"], family, float(strength), device,
                        encode_batch_size=64,
                    )
                    save_emb_cache(cache, pert_emb_by_ep)
                valid_idx, mse_pert = predict_eval_rows(
                    lewm, data, rows1c, eval_rows_idx, pert_emb_by_ep, device, batch_size=512,
                )
                episodes = rows1c["episode"][valid_idx]
                ts = rows1c["t"][valid_idx]
                win_emb, win_act = build_perturbed_windows(pert_emb_by_ep, data["action"].astype(np.float32), episodes, ts)
                lat_scores = score_windows(model, norm, win_emb, win_act)
                y_pert = (np.asarray(mse_pert, dtype=np.float64) > tau_err).astype(np.int8)
                single_class = bool(y_pert.min() == y_pert.max())
                slice_key = f"{family}@{strength:g}"
                if single_class:
                    fail_closed_slices.append(slice_key)
                point = {
                    "family": family,
                    "strength": float(strength),
                    "sample_count": int(len(y_pert)),
                    "episode_count": int(len(np.unique(episodes))),
                    "failure_rate_vanilla_uer": float(y_pert.mean()),
                    "mean_prediction_mse": float(np.asarray(mse_pert).mean()),
                    "single_class_fail_closed": single_class,
                    "lat_clean_trained": bootstrap_metrics_by_episode(
                        y_pert, lat_scores, episodes, seed=BOOTSTRAP_SEED, n_boot=OOD_BOOTSTRAPS,
                    ),
                    "phase2a_logistic_clean_only_reference": ref.get(slice_key),
                }
                points.append(point)
            detectable = [
                p["strength"] for p in points
                if not p["single_class_fail_closed"]
                and p["lat_clean_trained"]["failure_detection_auroc"]["ci95_low"] > 0.5
            ]
            families[family] = {
                "points": points,
                "summary": {
                    "strengths_with_auroc_ci_above_0p5": detectable,
                    "strengths_single_class_fail_closed": [
                        p["strength"] for p in points if p["single_class_fail_closed"]
                    ],
                },
            }

    report = {
        "schema_id": "lewm.ledger_aware_transformer_port.ood_arm",
        "question": "does the clean-trained LAT port keep detecting LeWM predictor failures under visual perturbation (phase2a setting)?",
        "claim_kind": "descriptive boundary mapping; no new positive claim",
        "clean_anchor": {
            "tau_err_train_p75": tau_err,
            "eval_auroc_observed": clean_eval["failure_detection_auroc"],
            "reproduces_committed_port_report": True,
        },
        "protocol": {
            "perturbation_grid": {k: [s for s in v if s != 0.0] for k, v in grids.items()},
            "failure_truth": "perturbed prediction_mse > clean train p75 (same tau as the port)",
            "bootstraps": OOD_BOOTSTRAPS,
            "bootstrap_unit": "eval episodes",
            "single_class_policy": "AUROC unidentifiable; slice recorded fail-closed (auroc_rank returns 0.5)",
            "emb_cache_dir": str(EMB_CACHE.name),
        },
        "families": families,
        "fail_closed_slices": fail_closed_slices,
        "not_claimed": [
            "OOD robustness of the clean-trained LAT (this arm MEASURES its boundary)",
            "OOD-aware LAT training (not run; would need perturbed train-split latents)",
            "any claim beyond the tworooms checkpoint and this perturbation grid",
        ],
    }
    JSON_PATH.write_text(json.dumps(report, indent=2), encoding="utf-8")

    lines = [
        "# LAT port OOD arm: clean-trained ledger head under perturbation",
        "",
        f"- clean anchor: eval AUROC {clean_eval['failure_detection_auroc']:.3f} (reproduces the committed port report)",
        f"- failure truth: perturbed prediction_mse > {tau_err:.6f} (clean train p75)",
        f"- fail-closed single-class slices: {', '.join(fail_closed_slices) if fail_closed_slices else 'none'}",
        "",
        "| family | strength | vanilla UER (=failure rate) | LAT AUROC | LAT UER | declared gap rate | phase2a logistic AUROC |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for family, pack in families.items():
        for p in pack["points"]:
            m = p["lat_clean_trained"]
            ref_m = p.get("phase2a_logistic_clean_only_reference") or {}
            ref_auroc = ref_m.get("failure_detection_auroc") or {}
            ref_str = (
                f"{ref_auroc.get('observed'):.3f}" if isinstance(ref_auroc.get("observed"), float) else "n/a"
            )
            flag = " (single-class)" if p["single_class_fail_closed"] else ""
            lines.append(
                f"| `{family}` | {p['strength']:g} | {p['failure_rate_vanilla_uer']:.3f} "
                f"| {fmt_ci(m['failure_detection_auroc'])}{flag} | {fmt_ci(m['unlogged_error_rate'])} "
                f"| {fmt_ci(m['declared_gap_rate'])} | {ref_str} |"
            )
    lines += [
        "",
        "Summary per family (strengths with AUROC ci95_low > 0.5 / single-class fail-closed):",
        "",
    ]
    for family, pack in families.items():
        s = pack["summary"]
        lines.append(
            f"- `{family}`: detectable at {s['strengths_with_auroc_ci_above_0p5'] or 'none'}; "
            f"single-class at {s['strengths_single_class_fail_closed'] or 'none'}"
        )
    MD_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(json.dumps({"fail_closed_slices": fail_closed_slices}, indent=2))
    print(MD_PATH)


if __name__ == "__main__":
    main()

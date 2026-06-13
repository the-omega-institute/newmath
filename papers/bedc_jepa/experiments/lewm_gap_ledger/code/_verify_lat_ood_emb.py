"""Independent verification of the LAT OOD arm's perturbed-emb data path.

For each (family, strength) eval slice: load the emb sequences the OOD run
actually used (reports/lat_ood_emb_cache), recompute predictor rollout mse via
predict_eval_rows, and compare row-by-row against the mse recorded in the
phase2c materialized cache (produced by the original full-perturbed-encode
pipeline). Reports per-slice max |dmse|, mismatch fraction, and failure-label
(y, at the clean train p75 tau) disagreement counts.
"""

from __future__ import annotations

import json

import h5py  # noqa: F401
import hdf5plugin  # noqa: F401
import numpy as np
import torch
from huggingface_hub import hf_hub_download

from lewm_latent_probe import build_model, load_checkpoint
from _phase2a_brittleness_gap import MODEL_REPO, perturbation_grid, predict_eval_rows
from _phase1c_gap_ledger import flatten_transition_rows
from _lat_lewm_port import NPZ_PATH, REPORT_DIR, split_episodes, build_windows
from _lat_lewm_ood import emb_cache_path, load_emb_cache, phase2c_cache_path

import _lat_lewm_port as port


def main() -> None:
    data = dict(np.load(NPZ_PATH))
    rows = flatten_transition_rows(data)
    splits = split_episodes(data["emb"].shape[0])
    eval_rows_idx = np.where(np.isin(rows["episode"], splits["eval"]))[0]

    win_rows = build_windows(data)
    train_mask = np.isin(win_rows["episode"], splits["train"])
    tau = float(np.percentile(win_rows["mse"][train_mask], 75))

    device = torch.device("cpu")
    checkpoint_path = hf_hub_download(MODEL_REPO, "weights.pt", repo_type="model")
    config_path = hf_hub_download(MODEL_REPO, "config.json", repo_type="model")
    with open(config_path, "r", encoding="utf-8") as f:
        config = json.load(f)
    lewm = build_model(config)
    load_checkpoint(lewm, checkpoint_path)
    lewm.to(device).eval().requires_grad_(False)

    summary = []
    for family, strengths in perturbation_grid().items():
        for strength in strengths:
            if strength == 0.0:
                continue
            used = load_emb_cache(emb_cache_path(family, strength))
            if used is None:
                summary.append((family, strength, "NO lat_ood_emb_cache"))
                continue
            p2c = np.load(phase2c_cache_path(family, float(strength), "eval"))
            valid_idx, mse_new = predict_eval_rows(
                lewm, data, rows, eval_rows_idx, used, device, batch_size=512
            )
            new_by_row = {int(i): float(m) for i, m in zip(valid_idx, mse_new)}
            old_rows = p2c["row_idx"].astype(np.int64)
            old_mse = p2c["mse"].astype(np.float64)
            both = [(int(i), float(m)) for i, m in zip(old_rows, old_mse) if int(i) in new_by_row]
            d = np.array([abs(new_by_row[i] - m) for i, m in both])
            y_old = np.array([m > tau for _, m in both])
            y_new = np.array([new_by_row[i] > tau for i, _ in both])
            summary.append(
                (
                    family,
                    strength,
                    f"rows={len(both)}/{len(old_rows)} max|dmse|={d.max():.6f} "
                    f"frac>1e-6={float((d > 1e-6).mean()):.4f} y_disagree={int((y_old != y_new).sum())}",
                )
            )
            print(summary[-1], flush=True)

    print("\n=== summary ===")
    for s in summary:
        print(s)


if __name__ == "__main__":
    main()

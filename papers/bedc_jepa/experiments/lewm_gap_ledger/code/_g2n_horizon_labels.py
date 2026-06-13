from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

import numpy as np
import torch
from huggingface_hub import hf_hub_download

from lewm_latent_probe import build_model, load_checkpoint
from _lat_lewm_port import NPZ_PATH, REPORT_DIR, SPLIT_SEED, split_episodes
from _phase1c_gap_ledger import flatten_transition_rows


ROOT = Path(__file__).resolve().parent
CLEAN_NPZ_PATH = REPORT_DIR / "g2n_labels_clean.npz"
PERT_NPZ_PATH = REPORT_DIR / "g2n_labels_perturbed.npz"
JSON_PATH = REPORT_DIR / "g2n_horizon_labels.json"
MD_PATH = REPORT_DIR / "g2n_horizon_labels.md"
OOD_CACHE_DIR = REPORT_DIR / "lat_ood_emb_cache"

MODEL_REPO = "quentinll/lewm-tworooms"
HISTORY_SIZE = 3
MAX_CLEAN_H = 10
MAX_PERT_H = 5
QUANTILES = np.asarray([50, 75, 90], dtype=np.int64)
ANCHOR_TOL = 1e-4
ROLL_BATCH = 512


try:
    from _ledger_gated_rollout import (  # type: ignore
        load_predictor as ledger_load_predictor,
        rollout_errors_for_horizon as ledger_rollout_errors_for_horizon,
    )

    LEDGER_ROLLOUT_IMPORT_ERROR = ""
except Exception as exc:  # pragma: no cover - exercised only when optional imports fail.
    ledger_load_predictor = None
    ledger_rollout_errors_for_horizon = None
    LEDGER_ROLLOUT_IMPORT_ERROR = repr(exc)


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


def load_data() -> dict[str, np.ndarray]:
    raw = np.load(NPZ_PATH)
    return {k: raw[k] for k in raw.files}


def load_predictor(device: torch.device) -> tuple[Any, dict[str, Any], str, str, str]:
    if ledger_load_predictor is not None:
        model, config, checkpoint_path, config_path = ledger_load_predictor(device)
        return model, config, checkpoint_path, config_path, "imported:_ledger_gated_rollout.load_predictor"

    checkpoint_path = hf_hub_download(MODEL_REPO, "weights.pt", repo_type="model")
    config_path = hf_hub_download(MODEL_REPO, "config.json", repo_type="model")
    with open(config_path, "r", encoding="utf-8") as f:
        config = json.load(f)
    model = build_model(config)
    load_checkpoint(model, checkpoint_path)
    model.to(device).eval().requires_grad_(False)
    return model, config, checkpoint_path, config_path, "fallback:lewm_latent_probe"


def valid_transition_count(data: dict[str, np.ndarray], ep: int) -> int:
    return int(data["transition_mask"][ep].astype(bool).sum())


def build_split_anchors(data: dict[str, np.ndarray], split_eps: np.ndarray) -> np.ndarray:
    anchors: list[tuple[int, int]] = []
    tm = data["transition_mask"].astype(bool)
    for ep_raw in split_eps:
        ep = int(ep_raw)
        for t0 in np.where(tm[ep])[0]:
            t = int(t0)
            if t >= HISTORY_SIZE - 1:
                anchors.append((ep, t))
    return np.asarray(anchors, dtype=np.int64)


def anchor_dicts(anchors: np.ndarray) -> list[dict[str, int]]:
    return [{"episode": int(ep), "t0": int(t0)} for ep, t0 in anchors]


def load_perturbed_emb(path: Path) -> dict[int, np.ndarray]:
    raw = np.load(path)
    return {int(k): raw[k].astype(np.float32) for k in raw.files}


def episode_sequence(
    clean_emb: np.ndarray,
    pert_emb_by_ep: dict[int, np.ndarray] | None,
    ep: int,
) -> np.ndarray:
    if pert_emb_by_ep is None:
        return clean_emb[ep]
    if ep not in pert_emb_by_ep:
        raise RuntimeError(f"perturbed cache is missing eval episode {ep}")
    return pert_emb_by_ep[ep]


def rollout_predictions(
    model: Any,
    data: dict[str, np.ndarray],
    anchors: np.ndarray,
    *,
    device: torch.device,
    max_h: int,
    pert_emb_by_ep: dict[int, np.ndarray] | None = None,
    batch_size: int = ROLL_BATCH,
) -> dict[str, np.ndarray]:
    clean_emb = data["emb"].astype(np.float32)
    action_np = data["action"].astype(np.float32)
    emb_dim = clean_emb.shape[-1]

    valid = np.zeros((len(anchors), max_h), dtype=bool)
    pred_z = np.full((len(anchors), max_h, emb_dim), np.nan, dtype=np.float32)
    err = np.full((len(anchors), max_h), np.nan, dtype=np.float64)
    mean_err = np.full((len(anchors), max_h), np.nan, dtype=np.float64)

    with torch.inference_mode():
        for lo in range(0, len(anchors), batch_size):
            hi = min(lo + batch_size, len(anchors))
            b = hi - lo
            ctx_emb = np.zeros((b, HISTORY_SIZE, emb_dim), dtype=np.float32)
            ctx_action = np.zeros((b, HISTORY_SIZE, action_np.shape[-1]), dtype=np.float32)
            future_action = np.zeros((b, max_h, action_np.shape[-1]), dtype=np.float32)
            true_future = np.full((b, max_h, emb_dim), np.nan, dtype=np.float32)

            for j, (ep_raw, t0_raw) in enumerate(anchors[lo:hi]):
                ep = int(ep_raw)
                t0 = int(t0_raw)
                seq = episode_sequence(clean_emb, pert_emb_by_ep, ep)
                reachable = min(max_h, valid_transition_count(data, ep) - t0, seq.shape[0] - 1 - t0)
                if reachable < 1:
                    continue
                start = t0 - HISTORY_SIZE + 1
                ctx_emb[j] = seq[start : t0 + 1]
                ctx_action[j] = action_np[ep, start : t0 + 1]
                true_future[j, :reachable] = seq[t0 + 1 : t0 + reachable + 1]
                future_action[j, :reachable] = action_np[ep, t0 + 1 : t0 + reachable + 1]
                valid[lo + j, :reachable] = True

            emb = torch.from_numpy(ctx_emb).to(device=device, dtype=torch.float32)
            act = torch.from_numpy(ctx_action).to(device=device, dtype=torch.float32)
            future_act = torch.from_numpy(future_action).to(device=device, dtype=torch.float32)
            preds: list[torch.Tensor] = []

            for step in range(max_h):
                act_emb = model.action_encoder(act[:, -HISTORY_SIZE:])
                pred = model.predict(emb[:, -HISTORY_SIZE:], act_emb)[:, -1]
                preds.append(pred)
                emb = torch.cat([emb, pred[:, None, :]], dim=1)
                act = torch.cat([act, future_act[:, step : step + 1]], dim=1)

            pred_stack = torch.stack(preds, dim=1).detach().cpu().numpy().astype(np.float32)
            pred_z[lo:hi] = pred_stack
            batch_valid = valid[lo:hi]
            sq = (pred_stack - true_future) ** 2
            batch_err = np.mean(sq, axis=-1, dtype=np.float64)
            batch_err[~batch_valid] = np.nan
            err[lo:hi] = batch_err

            csum = np.nancumsum(np.where(batch_valid, batch_err, 0.0), axis=1)
            counts = np.cumsum(batch_valid.astype(np.int64), axis=1)
            with np.errstate(invalid="ignore", divide="ignore"):
                m = csum / counts
            m[~batch_valid] = np.nan
            mean_err[lo:hi] = m

    pred_z[~valid] = np.nan
    return {"valid": valid, "pred_z": pred_z, "err_at_h": err, "mean_err_to_h": mean_err}


def compute_tau(train_err: np.ndarray, train_valid: np.ndarray, max_h: int) -> np.ndarray:
    tau = np.full((max_h, len(QUANTILES)), np.nan, dtype=np.float64)
    for h_idx in range(max_h):
        vals = train_err[train_valid[:, h_idx], h_idx]
        if len(vals) == 0:
            raise RuntimeError(f"no valid train anchors for h={h_idx + 1}")
        tau[h_idx] = np.percentile(vals, QUANTILES)
    return tau


def compute_labels(err: np.ndarray, valid: np.ndarray, tau: np.ndarray, max_h: int) -> np.ndarray:
    y = np.zeros((err.shape[0], max_h, len(QUANTILES)), dtype=np.int8)
    for h_idx in range(max_h):
        for q_idx in range(len(QUANTILES)):
            y[:, h_idx, q_idx] = ((err[:, h_idx] > tau[h_idx, q_idx]) & valid[:, h_idx]).astype(np.int8)
    return y


def split_base_rates(clean_parts: dict[str, dict[str, np.ndarray]], tau: np.ndarray) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for h_idx in range(tau.shape[0]):
        row: dict[str, Any] = {"h": h_idx + 1}
        for q_idx, q in enumerate(QUANTILES):
            for split in ("train", "eval"):
                valid = clean_parts[split]["valid"][:, h_idx]
                y = clean_parts[split]["y"][:, h_idx, q_idx].astype(bool)
                row[f"{split}_q{int(q)}"] = float(y[valid].mean()) if np.any(valid) else float("nan")
                row[f"{split}_q{int(q)}_n"] = int(valid.sum())
        rows.append(row)
    return rows


def pair_to_row_index(rows: dict[str, np.ndarray]) -> dict[tuple[int, int], int]:
    return {(int(ep), int(t)): i for i, (ep, t) in enumerate(zip(rows["episode"], rows["t"]))}


def clean_h1_anchor_delta(data: dict[str, np.ndarray], anchors: np.ndarray, h1_err: np.ndarray) -> float:
    ref = np.asarray([data["prediction_mse"][int(ep), int(t0)] for ep, t0 in anchors], dtype=np.float64)
    return float(np.max(np.abs(h1_err - ref))) if len(ref) else float("nan")


def imported_rollout_h1_delta(
    model: Any,
    data: dict[str, np.ndarray],
    anchors: np.ndarray,
    generated_h1: np.ndarray,
    device: torch.device,
) -> float | None:
    if ledger_rollout_errors_for_horizon is None:
        return None
    imported = ledger_rollout_errors_for_horizon(
        model,
        data,
        anchor_dicts(anchors),
        device=device,
        history_size=HISTORY_SIZE,
        horizon=1,
        batch_size=ROLL_BATCH,
    )[:, 0]
    return float(np.max(np.abs(imported.astype(np.float64) - generated_h1.astype(np.float64))))


def stop_anchor_failed(report: dict[str, Any]) -> None:
    REPORT_DIR.mkdir(exist_ok=True)
    JSON_PATH.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    MD_PATH.write_text(
        "# G2N Horizon Labels\n\n"
        f"Stopped: `{report['reason']}`.\n\n"
        f"- max |delta|: `{report['max_abs_delta']:.9g}`\n"
        f"- tolerance: `{report['tolerance']:.9g}`\n",
        encoding="utf-8",
    )
    raise SystemExit(f"{report['reason']}: max_delta={report['max_abs_delta']:.9g}")


def strength_from_token(token: str) -> float:
    return float(token.replace("p", ".").replace("m", "-"))


def discover_eval_ood_slices() -> list[dict[str, Any]]:
    out = []
    for path in sorted(OOD_CACHE_DIR.glob("eval_*.npz")):
        stem = path.stem[len("eval_") :]
        family, strength_token = stem.rsplit("_", 1)
        mse_path = OOD_CACHE_DIR / f"mse_eval_{family}_{strength_token}.npz"
        if not mse_path.exists():
            raise RuntimeError(f"missing perturbed h=1 mse cache for {path.name}: {mse_path.name}")
        out.append(
            {
                "key": f"{family}_{strength_token}",
                "family": family,
                "strength_token": strength_token,
                "strength": strength_from_token(strength_token),
                "emb_path": path,
                "mse_path": mse_path,
            }
        )
    if not out:
        raise RuntimeError(f"no eval perturbed emb caches found under {OOD_CACHE_DIR}")
    return out


def write_markdown(report: dict[str, Any]) -> None:
    lines = [
        "# G2N Horizon Labels",
        "",
        f"- status: `{report['status']}`",
        f"- latent: `tworooms_latent_large.npz`; model: `{MODEL_REPO}`",
        f"- split seed: `{SPLIT_SEED}`; history size: `{HISTORY_SIZE}`",
        f"- clean h=1 max |delta| vs `prediction_mse`: `{report['anchor_checks']['clean_h1_prediction_mse_max_abs_delta']:.9g}`",
        f"- perturbed h=1 max |delta| vs `mse_eval_*`: `{report['anchor_checks']['perturbed_h1_mse_cache_max_abs_delta']:.9g}`",
        "",
        "## Anchor Counts",
        "",
        "| split | anchors | h1 | h3 | h5 | h10 |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for split in ("train", "calibration", "eval"):
        c = report["anchors"]["clean"][split]
        lines.append(f"| `{split}` | {c['anchors']} | {c['valid_h1']} | {c['valid_h3']} | {c['valid_h5']} | {c['valid_h10']} |")

    lines.extend(["", "## Tau Table", "", "| h | q50 | q75 | q90 |", "|---:|---:|---:|---:|"])
    for row in report["tau_table"]:
        lines.append(f"| {row['h']} | {row['q50']:.9f} | {row['q75']:.9f} | {row['q90']:.9f} |")

    lines.extend(["", "## Failure Base Rates", "", "| h | train q50 | train q75 | train q90 | eval q50 | eval q75 | eval q90 |", "|---:|---:|---:|---:|---:|---:|---:|"])
    for row in report["failure_base_rates"]:
        lines.append(
            f"| {row['h']} | {row['train_q50']:.6f} | {row['train_q75']:.6f} | {row['train_q90']:.6f} | "
            f"{row['eval_q50']:.6f} | {row['eval_q75']:.6f} | {row['eval_q90']:.6f} |"
        )

    lines.extend(["", "## Perturbed Slices", "", "| slice | anchors | h1 | h3 | h5 | h1 max |delta| |", "|---|---:|---:|---:|---:|---:|"])
    for row in report["anchors"]["perturbed"]:
        lines.append(
            f"| `{row['key']}` | {row['anchors']} | {row['valid_h1']} | {row['valid_h3']} | {row['valid_h5']} | "
            f"{row['h1_mse_cache_max_abs_delta']:.9g} |"
        )
    MD_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    REPORT_DIR.mkdir(exist_ok=True)
    data = load_data()
    history_size = int(np.asarray(data["history_size"]).item())
    if history_size != HISTORY_SIZE:
        raise SystemExit(f"expected history_size={HISTORY_SIZE}, got {history_size}")

    device = torch.device("cpu")
    model, config, checkpoint_path, config_path, loader_source = load_predictor(device)
    splits = split_episodes(data["emb"].shape[0])
    rows = flatten_transition_rows(data)
    pair_row = pair_to_row_index(rows)

    clean_parts: dict[str, dict[str, np.ndarray]] = {}
    clean_npz: dict[str, np.ndarray] = {
        "horizons": np.arange(1, MAX_CLEAN_H + 1, dtype=np.int64),
        "quantiles": QUANTILES.copy(),
    }
    clean_anchor_delta_by_split: dict[str, float] = {}
    imported_delta_by_split: dict[str, float | None] = {}

    for split in ("train", "calibration", "eval"):
        anchors = build_split_anchors(data, splits[split])
        print(f"[clean] split={split} anchors={len(anchors)}", flush=True)
        part = rollout_predictions(model, data, anchors, device=device, max_h=MAX_CLEAN_H)
        h1_delta = clean_h1_anchor_delta(data, anchors, part["err_at_h"][:, 0])
        imported_delta = imported_rollout_h1_delta(model, data, anchors, part["err_at_h"][:, 0], device)
        clean_anchor_delta_by_split[split] = h1_delta
        imported_delta_by_split[split] = imported_delta
        if not np.isfinite(h1_delta) or h1_delta >= ANCHOR_TOL:
            stop_anchor_failed(
                {
                    "status": "stopped_anchor_failed",
                    "reason": f"clean h=1 anchor failed for split={split}",
                    "max_abs_delta": h1_delta,
                    "tolerance": ANCHOR_TOL,
                    "split": split,
                    "anchors_checked": int(len(anchors)),
                }
            )
        clean_parts[split] = {"anchors": anchors, **part}

    tau = compute_tau(clean_parts["train"]["err_at_h"], clean_parts["train"]["valid"], MAX_CLEAN_H)
    for split, part in clean_parts.items():
        part["y"] = compute_labels(part["err_at_h"], part["valid"], tau, MAX_CLEAN_H)
        clean_npz[f"{split}_anchor_ep_t0"] = part["anchors"].astype(np.int64)
        clean_npz[f"{split}_valid"] = part["valid"].astype(bool)
        clean_npz[f"{split}_err_at_h"] = part["err_at_h"].astype(np.float64)
        clean_npz[f"{split}_mean_err_to_h"] = part["mean_err_to_h"].astype(np.float64)
        clean_npz[f"{split}_pred_z"] = part["pred_z"].astype(np.float32)
        clean_npz[f"{split}_y"] = part["y"].astype(np.int8)
    clean_npz["tau"] = tau.astype(np.float64)

    pert_slices = discover_eval_ood_slices()
    pert_npz: dict[str, np.ndarray] = {
        "horizons": np.arange(1, MAX_PERT_H + 1, dtype=np.int64),
        "quantiles": QUANTILES.copy(),
        "tau_h1_to_h5": tau[:MAX_PERT_H].astype(np.float64),
        "slice_keys": np.asarray([s["key"] for s in pert_slices]),
        "families": np.asarray([s["family"] for s in pert_slices]),
        "strength_tokens": np.asarray([s["strength_token"] for s in pert_slices]),
        "strengths": np.asarray([s["strength"] for s in pert_slices], dtype=np.float64),
    }
    perturbed_anchor_rows: list[dict[str, Any]] = []
    pert_h1_deltas: list[float] = []
    eval_anchors = clean_parts["eval"]["anchors"]

    for spec in pert_slices:
        key = str(spec["key"])
        print(f"[perturbed] slice={key} anchors={len(eval_anchors)}", flush=True)
        pert_emb_by_ep = load_perturbed_emb(Path(spec["emb_path"]))
        part = rollout_predictions(
            model,
            data,
            eval_anchors,
            device=device,
            max_h=MAX_PERT_H,
            pert_emb_by_ep=pert_emb_by_ep,
        )
        y = compute_labels(part["err_at_h"], part["valid"], tau[:MAX_PERT_H], MAX_PERT_H)

        mse_cache = np.load(spec["mse_path"])
        mse_by_row = {int(r): float(m) for r, m in zip(mse_cache["row_idx"], mse_cache["mse"])}
        ref = []
        got = []
        for i, (ep_raw, t0_raw) in enumerate(eval_anchors):
            ep = int(ep_raw)
            t0 = int(t0_raw)
            row_idx = pair_row[(ep, t0)]
            if row_idx not in mse_by_row:
                raise RuntimeError(f"{spec['mse_path'].name} missing row_idx={row_idx} for ep={ep}, t0={t0}")
            ref.append(mse_by_row[row_idx])
            got.append(float(part["err_at_h"][i, 0]))
        h1_delta = float(np.max(np.abs(np.asarray(got, dtype=np.float64) - np.asarray(ref, dtype=np.float64))))
        pert_h1_deltas.append(h1_delta)
        if not np.isfinite(h1_delta) or h1_delta >= ANCHOR_TOL:
            stop_anchor_failed(
                {
                    "status": "stopped_anchor_failed",
                    "reason": f"perturbed h=1 anchor failed for slice={key}",
                    "max_abs_delta": h1_delta,
                    "tolerance": ANCHOR_TOL,
                    "slice": key,
                    "anchors_checked": int(len(eval_anchors)),
                }
            )

        pert_npz[f"{key}_anchor_ep_t0"] = eval_anchors.astype(np.int64)
        pert_npz[f"{key}_valid"] = part["valid"].astype(bool)
        pert_npz[f"{key}_err_at_h"] = part["err_at_h"].astype(np.float64)
        pert_npz[f"{key}_mean_err_to_h"] = part["mean_err_to_h"].astype(np.float64)
        pert_npz[f"{key}_y"] = y.astype(np.int8)
        pert_npz[f"{key}_h1_mse_cache_max_abs_delta"] = np.asarray(h1_delta, dtype=np.float64)

        perturbed_anchor_rows.append(
            {
                "key": key,
                "family": spec["family"],
                "strength": spec["strength"],
                "anchors": int(len(eval_anchors)),
                "valid_h1": int(part["valid"][:, 0].sum()),
                "valid_h3": int(part["valid"][:, 2].sum()),
                "valid_h5": int(part["valid"][:, 4].sum()),
                "h1_mse_cache_max_abs_delta": h1_delta,
            }
        )

    tau_table = [
        {"h": h_idx + 1, "q50": float(tau[h_idx, 0]), "q75": float(tau[h_idx, 1]), "q90": float(tau[h_idx, 2])}
        for h_idx in range(MAX_CLEAN_H)
    ]
    base_rates = split_base_rates(clean_parts, tau)
    anchor_counts = {
        split: {
            "episodes": int(len(splits[split])),
            "anchors": int(len(part["anchors"])),
            "valid_h1": int(part["valid"][:, 0].sum()),
            "valid_h3": int(part["valid"][:, 2].sum()),
            "valid_h5": int(part["valid"][:, 4].sum()),
            "valid_h10": int(part["valid"][:, 9].sum()),
        }
        for split, part in clean_parts.items()
    }

    report = {
        "status": "ok",
        "protocol": {
            "task": "G2N horizon rollout failure labels and prediction trajectory cache",
            "anchor_definition": "per split episodes, all valid transition positions (ep,t0) with t0 >= 2",
            "valid_horizon_definition": "h valid iff t0 + h <= episode valid transition count",
            "clean_horizons": list(range(1, MAX_CLEAN_H + 1)),
            "perturbed_horizons": list(range(1, MAX_PERT_H + 1)),
            "quantiles": QUANTILES.tolist(),
            "threshold_source": "train split err_at_h only, per horizon",
        },
        "model": {
            "repo": MODEL_REPO,
            "checkpoint_path": checkpoint_path,
            "config_path": config_path,
            "loader_source": loader_source,
            "ledger_rollout_imported": bool(ledger_rollout_errors_for_horizon is not None),
            "ledger_rollout_import_error": LEDGER_ROLLOUT_IMPORT_ERROR,
            "config_history_size": int(config["predictor"]["num_frames"]),
            "npz_history_size": history_size,
        },
        "split": {
            "seed": SPLIT_SEED,
            "episode_counts": {name: int(len(eps)) for name, eps in splits.items()},
        },
        "anchors": {
            "clean": anchor_counts,
            "perturbed": perturbed_anchor_rows,
        },
        "anchor_checks": {
            "tolerance": ANCHOR_TOL,
            "clean_h1_prediction_mse_max_abs_delta": float(max(clean_anchor_delta_by_split.values())),
            "clean_h1_prediction_mse_by_split": clean_anchor_delta_by_split,
            "generated_vs_imported_ledger_h1_max_abs_delta_by_split": imported_delta_by_split,
            "perturbed_h1_mse_cache_max_abs_delta": float(max(pert_h1_deltas)),
        },
        "tau_table": tau_table,
        "failure_base_rates": base_rates,
        "outputs": {
            "clean_npz": str(CLEAN_NPZ_PATH),
            "perturbed_npz": str(PERT_NPZ_PATH),
            "json": str(JSON_PATH),
            "md": str(MD_PATH),
        },
    }

    np.savez_compressed(CLEAN_NPZ_PATH, **clean_npz)
    np.savez_compressed(PERT_NPZ_PATH, **pert_npz)
    JSON_PATH.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")
    write_markdown(report)
    print(json.dumps(clean_json(report["anchor_checks"]), indent=2, ensure_ascii=False), flush=True)
    print(f"wrote {CLEAN_NPZ_PATH}", flush=True)
    print(f"wrote {PERT_NPZ_PATH}", flush=True)
    print(f"wrote {JSON_PATH}", flush=True)
    print(f"wrote {MD_PATH}", flush=True)


if __name__ == "__main__":
    main()

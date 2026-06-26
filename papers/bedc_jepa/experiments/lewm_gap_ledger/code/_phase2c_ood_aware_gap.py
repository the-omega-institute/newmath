from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import h5py
import hdf5plugin  # noqa: F401 - registers blosc HDF5 filter
import numpy as np
import torch
from huggingface_hub import hf_hub_download

from lewm_latent_probe import build_model, load_checkpoint
from _phase1c_gap_ledger import (
    BOOTSTRAP_SEED,
    DISTINCTIONS,
    FEATURE_VARIANTS,
    LogisticHead,
    auroc_rank,
    basic_metrics,
    build_gap_features,
    fit_logistic_head,
    flatten_transition_rows,
    fmt_ci,
    predict_logistic_head,
)
from _phase2a_brittleness_gap import (
    BOOTSTRAPS,
    H5_PATH,
    IMAGENET_MEAN,
    IMAGENET_STD,
    MODEL_REPO,
    NPZ_PATH,
    PRIMARY_VARIANT,
    clean_json,
    fit_clean_protocol,
    perturb_metrics,
    perturb_frames,
    perturbation_grid,
    predict_eval_rows,
)


ROOT = Path(__file__).resolve().parent
REPORT_DIR = ROOT / "reports"
JSON_PATH = REPORT_DIR / "lewm_ood_aware_gap.json"
MD_PATH = REPORT_DIR / "lewm_ood_aware_gap.md"
FINDINGS_PATH = ROOT / "PHASE2C_FINDINGS.md"
CACHE_DIR = REPORT_DIR / "phase2c_materialized_cache"

PRIMARY_PROBE_INDICES = FEATURE_VARIANTS[PRIMARY_VARIANT]
STRONG_FAMILIES = ("color_shift", "gaussian_noise", "occlusion", "brightness")
DEFAULT_FAMILIES = ("color_shift", "occlusion", "brightness", "background_tint", "gaussian_noise")


def to_model_pixels_batched(frames: np.ndarray, image_size: int, device: torch.device) -> torch.Tensor:
    x = torch.from_numpy(frames).to(device=device, dtype=torch.float32)
    x = x.permute(0, 3, 1, 2).div_(255.0)
    mean = torch.tensor(IMAGENET_MEAN, device=device).view(1, 3, 1, 1)
    std = torch.tensor(IMAGENET_STD, device=device).view(1, 3, 1, 1)
    x = (x - mean) / std
    if x.shape[-2:] != (image_size, image_size):
        x = torch.nn.functional.interpolate(x, size=(image_size, image_size), mode="bilinear", align_corners=False)
    return x


def encode_split_episodes_batched(
    h5: h5py.File,
    model: Any,
    config: dict[str, Any],
    data: dict[str, np.ndarray],
    split_eps: np.ndarray,
    family: str,
    strength: float,
    device: torch.device,
    *,
    encode_batch_size: int,
) -> dict[int, np.ndarray]:
    image_size = int(config["encoder"]["image_size"])
    ep_slices: dict[int, tuple[int, int]] = {}
    frame_batches = []
    cursor = 0
    for ep_raw in split_eps:
        ep = int(ep_raw)
        valid_t = int(data["valid_mask"][ep].sum())
        idx = data["raw_frame_idx"][ep, :valid_t].astype(np.int64)
        frames = h5["pixels"][idx]
        frames = perturb_frames(frames, family, strength)
        frame_batches.append(frames)
        ep_slices[ep] = (cursor, cursor + valid_t)
        cursor += valid_t

    all_frames = np.concatenate(frame_batches, axis=0)
    all_emb = np.zeros((len(all_frames), data["emb"].shape[-1]), dtype=np.float32)
    with torch.inference_mode():
        for lo in range(0, len(all_frames), encode_batch_size):
            hi = min(lo + encode_batch_size, len(all_frames))
            pixels = to_model_pixels_batched(all_frames[lo:hi], image_size=image_size, device=device)
            emb = model.encode({"pixels": pixels.unsqueeze(1)})["emb"][:, 0].detach().cpu().numpy()
            all_emb[lo:hi] = emb.astype(np.float32)

    return {ep: all_emb[lo:hi] for ep, (lo, hi) in ep_slices.items()}


def cache_path(family: str, strength: float, split_name: str) -> Path:
    strength_token = f"{strength:g}".replace(".", "p").replace("-", "m")
    return CACHE_DIR / f"{split_name}_{family}_{strength_token}.npz"


def save_part_cache(path: Path, part: dict[str, Any]) -> None:
    path.parent.mkdir(exist_ok=True)
    np.savez_compressed(
        path,
        x=part["x"].astype(np.float32),
        y=part["y"].astype(np.int8),
        mse=part["mse"].astype(np.float32),
        episode=part["episode"].astype(np.int64),
        row_idx=part["row_idx"].astype(np.int64),
    )


def load_part_cache(path: Path, family: str, strength: float, split_name: str, source: str) -> dict[str, Any] | None:
    if not path.exists():
        return None
    raw = np.load(path)
    return {
        "family": family,
        "strength": float(strength),
        "split": split_name,
        "row_idx": raw["row_idx"].astype(np.int64),
        "x": raw["x"].astype(np.float64),
        "y": raw["y"].astype(np.int8),
        "mse": raw["mse"].astype(np.float64),
        "episode": raw["episode"].astype(np.int64),
        "source": source,
    }


def feature_from_emb(protocol: dict[str, Any], emb: np.ndarray) -> np.ndarray:
    probe_prob_cols = []
    probe_logit_cols = []
    probe_pred_cols = []
    for name in DISTINCTIONS:
        p, logit = predict_logistic_head(protocol["probe_heads"][name], emb.astype(np.float64))
        probe_prob_cols.append(p)
        probe_logit_cols.append(logit)
        probe_pred_cols.append((p >= 0.5).astype(np.float64))
    probe_prob = np.stack(probe_prob_cols, axis=1)
    probe_logit = np.stack(probe_logit_cols, axis=1)
    probe_pred = np.stack(probe_pred_cols, axis=1)
    x_b, _ = build_gap_features(
        emb.astype(np.float64),
        probe_prob,
        probe_logit,
        probe_pred,
        protocol["quality_feature"],
        PRIMARY_PROBE_INDICES,
    )
    return x_b.astype(np.float64)


def materialize_clean_split(
    protocol: dict[str, Any],
    rows: dict[str, np.ndarray],
    split_name: str,
) -> dict[str, Any]:
    mask = protocol["split_masks"][split_name]
    row_idx = np.where(mask)[0].astype(np.int64)
    mse = rows["mse"][row_idx].astype(np.float64)
    x = feature_from_emb(protocol, rows["emb"][row_idx].astype(np.float64))
    y = (mse > protocol["tau_err"]).astype(np.int8)
    return {
        "family": "clean",
        "strength": 0.0,
        "split": split_name,
        "row_idx": row_idx,
        "x": x,
        "y": y,
        "mse": mse,
        "episode": rows["episode"][row_idx].astype(np.int64),
        "source": "cached_clean_latents",
    }


def materialize_perturb_split(
    h5: h5py.File,
    model: Any,
    config: dict[str, Any],
    data: dict[str, np.ndarray],
    rows: dict[str, np.ndarray],
    protocol: dict[str, Any],
    family: str,
    strength: float,
    split_name: str,
    device: torch.device,
    *,
    batch_size: int,
    encode_batch_size: int,
) -> dict[str, Any]:
    cached = load_part_cache(
        cache_path(family, strength, split_name),
        family,
        strength,
        split_name,
        "perturbed_rgb_reencoded_cached",
    )
    if cached is not None:
        return cached

    split_mask = protocol["split_masks"][split_name]
    split_rows_idx = np.where(split_mask)[0]
    split_eps = protocol["splits_ep"][split_name]
    pert_emb_by_ep = encode_split_episodes_batched(
        h5,
        model,
        config,
        data,
        split_eps,
        family,
        strength,
        device,
        encode_batch_size=encode_batch_size,
    )
    valid_rows_idx, prediction_mse = predict_eval_rows(
        model,
        data,
        rows,
        split_rows_idx,
        pert_emb_by_ep,
        device,
        batch_size=batch_size,
    )
    current_emb = np.stack(
        [pert_emb_by_ep[int(rows["episode"][i])][int(rows["t"][i])] for i in valid_rows_idx]
    )
    x = feature_from_emb(protocol, current_emb)
    y = (prediction_mse > protocol["tau_err"]).astype(np.int8)
    part = {
        "family": family,
        "strength": float(strength),
        "split": split_name,
        "row_idx": valid_rows_idx.astype(np.int64),
        "x": x,
        "y": y,
        "mse": prediction_mse.astype(np.float64),
        "episode": rows["episode"][valid_rows_idx].astype(np.int64),
        "source": "perturbed_rgb_reencoded",
    }
    save_part_cache(cache_path(family, strength, split_name), part)
    return part


def concat_parts(parts: list[dict[str, Any]]) -> dict[str, np.ndarray]:
    if not parts:
        raise ValueError("cannot concatenate an empty materialized set")
    return {
        "x": np.concatenate([p["x"] for p in parts], axis=0).astype(np.float64),
        "y": np.concatenate([p["y"] for p in parts], axis=0).astype(np.int8),
        "mse": np.concatenate([p["mse"] for p in parts], axis=0).astype(np.float64),
        "episode": np.concatenate([p["episode"] for p in parts], axis=0).astype(np.int64),
        "row_idx": np.concatenate([p["row_idx"] for p in parts], axis=0).astype(np.int64),
    }


def fit_gap_head_for_parts(parts: list[dict[str, Any]]) -> tuple[LogisticHead, dict[str, Any]]:
    train = concat_parts(parts)
    head, fit_info = fit_logistic_head(train["x"], train["y"], steps=500, lr=0.14, l2=1e-4)
    fit_info = {
        **fit_info,
        "train_rows": int(len(train["y"])),
        "train_episodes": int(len(np.unique(train["episode"]))),
        "train_failure_rate": float(train["y"].mean()) if len(train["y"]) else float("nan"),
    }
    return head, fit_info


def eval_head_on_part(
    head: LogisticHead,
    part: dict[str, Any],
    *,
    seed: int,
) -> dict[str, Any]:
    gap_score, _ = predict_logistic_head(head, part["x"])
    y = part["y"].astype(np.int8)
    metrics = perturb_metrics(
        y,
        gap_score.astype(np.float64),
        part["mse"].astype(np.float64),
        part["episode"].astype(np.int64),
        seed=seed,
        n_boot=BOOTSTRAPS,
    )
    observed = {
        "mean_prediction_mse": float(np.mean(part["mse"])),
        "median_prediction_mse": float(np.median(part["mse"])),
        "failure_rate_vanilla_uer": float(np.mean(y)),
        "bedc_gap_head_uer": float(np.mean((y > 0) & (gap_score < 0.5))),
        "failure_detection_auroc": float(auroc_rank(y, gap_score)),
        "mean_gap_score": float(np.mean(gap_score)),
        "declared_gap_rate": float(np.mean(gap_score >= 0.5)),
        "logged_given_failure_rate": float(np.mean(gap_score[y > 0] >= 0.5)) if np.any(y) else float("nan"),
        "positive_count": int(y.sum()),
        "negative_count": int(len(y) - y.sum()),
    }
    strength = part["strength"]
    strength_out: float | str
    if isinstance(strength, str):
        strength_out = strength
    else:
        strength_out = float(strength)
    return {
        "family": part["family"],
        "strength": strength_out,
        "source": part["source"],
        "sample_count": int(len(y)),
        "episode_count": int(len(np.unique(part["episode"]))),
        "single_class_truth": bool(np.unique(y).size < 2),
        "observed": observed,
        "metrics_episode_bootstrap": metrics,
        "raw_basic_metrics": basic_metrics(y, gap_score, gap_score),
    }


def eval_head_on_parts(
    head: LogisticHead,
    parts: list[dict[str, Any]],
    *,
    family: str,
    label: str,
    seed: int,
) -> dict[str, Any]:
    pooled = concat_parts(parts)
    pooled_part = {
        "family": family,
        "strength": label,
        "source": "+".join(sorted({p["source"] for p in parts})),
        **pooled,
    }
    out = eval_head_on_part(head, pooled_part, seed=seed)
    out["strength"] = label
    out["strengths_pooled"] = [float(p["strength"]) for p in parts]
    return out


def point_claim(point: dict[str, Any]) -> dict[str, Any]:
    m = point["metrics_episode_bootstrap"]
    auroc_ci = m["failure_detection_auroc"]
    bedc_ci = m["bedc_gap_head_uer"]
    vanilla_ci = m["vanilla_uer"]
    auroc_pos = bool(auroc_ci["ci95_low"] > 0.5)
    uer_pos = bool(bedc_ci["ci95_high"] < vanilla_ci["ci95_low"])
    return {
        "auroc_ci_low_gt_0_5": auroc_pos,
        "bedc_uer_ci_high_lt_vanilla_ci_low": uer_pos,
        "claim": "positive" if auroc_pos and uer_pos else "negative_or_inconclusive",
        "single_class_truth": bool(point.get("single_class_truth", False)),
    }


def summarize_family(points: list[dict[str, Any]], aggregate_nonzero: dict[str, Any]) -> dict[str, Any]:
    nonzero_points = [p for p in points if float(p["strength"]) != 0.0]
    final = nonzero_points[-1] if nonzero_points else points[-1]
    return {
        "final_strength": float(final["strength"]),
        "final_claim": point_claim(final),
        "nonzero_pooled_claim": point_claim(aggregate_nonzero),
        "final_observed": final["observed"],
        "nonzero_pooled_observed": aggregate_nonzero["observed"],
    }


def evaluate_arm(
    name: str,
    head: LogisticHead,
    eval_clean: dict[str, Any],
    eval_parts_by_family: dict[str, list[dict[str, Any]]],
    *,
    seed_offset: int,
) -> dict[str, Any]:
    clean_eval = eval_head_on_part(head, eval_clean, seed=BOOTSTRAP_SEED + seed_offset)
    family_reports: dict[str, Any] = {}
    for family_i, (family, parts) in enumerate(eval_parts_by_family.items()):
        points = [
            eval_head_on_part(head, eval_clean | {"family": family}, seed=BOOTSTRAP_SEED + seed_offset + 1000 * family_i)
        ]
        for strength_i, part in enumerate(parts, start=1):
            points.append(
                eval_head_on_part(
                    head,
                    part,
                    seed=BOOTSTRAP_SEED + seed_offset + 1000 * family_i + strength_i,
                )
            )
        aggregate_nonzero = eval_head_on_parts(
            head,
            parts,
            family=family,
            label="nonzero_pooled",
            seed=BOOTSTRAP_SEED + seed_offset + 1000 * family_i + 101,
        )
        family_reports[family] = {
            "points": points,
            "aggregate_nonzero": aggregate_nonzero,
            "summary": summarize_family(points, aggregate_nonzero),
        }
    return {
        "name": name,
        "clean_eval": clean_eval,
        "families": family_reports,
    }


def materialized_report(parts_by_key: dict[tuple[str, float, str], dict[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for (family, strength, split), part in parts_by_key.items():
        out[f"{split}:{family}:{strength:g}"] = {
            "family": family,
            "strength": float(strength),
            "split": split,
            "rows": int(len(part["y"])),
            "episodes": int(len(np.unique(part["episode"]))),
            "failure_rate": float(part["y"].mean()) if len(part["y"]) else float("nan"),
            "mean_prediction_mse": float(np.mean(part["mse"])) if len(part["mse"]) else float("nan"),
            "positive_count": int(part["y"].sum()),
            "negative_count": int(len(part["y"]) - part["y"].sum()),
        }
    return out


def ci_short(m: dict[str, dict[str, float]], key: str) -> str:
    return fmt_ci(m[key])


def write_reports(report: dict[str, Any]) -> None:
    JSON_PATH.write_text(json.dumps(clean_json(report), indent=2, ensure_ascii=False), encoding="utf-8")

    lines = [
        "# Phase 2c: OOD-aware gap training",
        "",
        f"- latent: `tworooms_latent_large.npz`; H5: `_tworoom_prefix_large.h5`",
        f"- feature variant: `{PRIMARY_VARIANT}`",
        f"- failure truth: `prediction_mse > {report['thresholds']['failure_threshold_clean_train_p75']:.6f}` (clean train p75, fixed for clean and perturbed frames)",
        f"- bootstrap: {BOOTSTRAPS} resamples, eval episodes as unit",
        f"- conclusion: **{report['conclusion']['claim']}** - {report['conclusion']['summary']}",
        "",
        "## Main contrast: final strength",
        "",
        "| family | arm | final strength | AUROC CI | vanilla UER CI | BEDC UER CI | declared gap | claim |",
        "|---|---|---:|---:|---:|---:|---:|---|",
    ]
    for family in report["families_evaluated"]:
        for arm_name in ("clean_only", "ood_aware"):
            pack = report["arms"][arm_name]["families"][family]
            final_strength = pack["summary"]["final_strength"]
            final = [p for p in pack["points"] if p["strength"] == final_strength][0]
            m = final["metrics_episode_bootstrap"]
            claim = pack["summary"]["final_claim"]["claim"]
            lines.append(
                f"| `{family}` | `{arm_name}` | {final_strength:g} | "
                f"{ci_short(m, 'failure_detection_auroc')} | {ci_short(m, 'vanilla_uer')} | "
                f"{ci_short(m, 'bedc_gap_head_uer')} | {final['observed']['declared_gap_rate']:.4f} | {claim} |"
            )
    lines.extend(["", "## Main contrast: nonzero pooled", ""])
    lines.append("| family | arm | AUROC CI | vanilla UER CI | BEDC UER CI | declared gap | claim |")
    lines.append("|---|---|---:|---:|---:|---:|---|")
    for family in report["families_evaluated"]:
        for arm_name in ("clean_only", "ood_aware"):
            agg = report["arms"][arm_name]["families"][family]["aggregate_nonzero"]
            m = agg["metrics_episode_bootstrap"]
            claim = report["arms"][arm_name]["families"][family]["summary"]["nonzero_pooled_claim"]["claim"]
            lines.append(
                f"| `{family}` | `{arm_name}` | {ci_short(m, 'failure_detection_auroc')} | "
                f"{ci_short(m, 'vanilla_uer')} | {ci_short(m, 'bedc_gap_head_uer')} | "
                f"{agg['observed']['declared_gap_rate']:.4f} | {claim} |"
            )

    lines.extend(["", "## Leave-one-perturbation-out", ""])
    if report["leave_one_out"]:
        lines.append("| held-out family | AUROC CI | vanilla UER CI | BEDC UER CI | declared gap | claim |")
        lines.append("|---|---:|---:|---:|---:|---|")
        for family in report["families_evaluated"]:
            agg = report["leave_one_out"][family]["aggregate_nonzero"]
            m = agg["metrics_episode_bootstrap"]
            claim = report["leave_one_out"][family]["summary"]["nonzero_pooled_claim"]["claim"]
            lines.append(
                f"| `{family}` | {ci_short(m, 'failure_detection_auroc')} | {ci_short(m, 'vanilla_uer')} | "
                f"{ci_short(m, 'bedc_gap_head_uer')} | {agg['observed']['declared_gap_rate']:.4f} | {claim} |"
            )
    else:
        lines.append("Skipped for this run.")

    lines.extend(["", "## Debt", ""])
    for d in report["debt"]:
        lines.append(f"- {d['type']} / {d['source']}: {d['detail']}")
    lines.append("")
    MD_PATH.write_text("\n".join(lines), encoding="utf-8")

    findings = [
        "# PHASE2C_FINDINGS",
        "",
        "## 结论",
        "",
        f"本轮结论：**{report['conclusion']['claim']}**。{report['conclusion']['summary']}",
        "",
        "OOD-aware 训练使用 clean train episodes 加所有非零扰动 train episodes；评估固定在 held-out eval episodes。failure truth 始终是 clean train `prediction_mse` p75 阈值，不随扰动重标定。",
        "",
        "## 主对照：最终强度",
        "",
    ]
    for family in report["families_evaluated"]:
        findings.append(f"### {family}")
        findings.append("")
        for arm_name in ("clean_only", "ood_aware"):
            pack = report["arms"][arm_name]["families"][family]
            final_strength = pack["summary"]["final_strength"]
            final = [p for p in pack["points"] if p["strength"] == final_strength][0]
            m = final["metrics_episode_bootstrap"]
            findings.append(
                f"- `{arm_name}` strength={final_strength:g}: AUROC {ci_short(m, 'failure_detection_auroc')}; "
                f"vanilla UER {ci_short(m, 'vanilla_uer')}; BEDC UER {ci_short(m, 'bedc_gap_head_uer')}; "
                f"declared_gap={final['observed']['declared_gap_rate']:.4f}; "
                f"claim={pack['summary']['final_claim']['claim']}; "
                f"single_class_truth={final['single_class_truth']}"
            )
        findings.append("")

    findings.extend(["## Leave-one-out 泛化", ""])
    if report["leave_one_out"]:
        for family in report["families_evaluated"]:
            agg = report["leave_one_out"][family]["aggregate_nonzero"]
            m = agg["metrics_episode_bootstrap"]
            findings.append(
                f"- held-out `{family}` nonzero pooled: AUROC {ci_short(m, 'failure_detection_auroc')}; "
                f"vanilla UER {ci_short(m, 'vanilla_uer')}; BEDC UER {ci_short(m, 'bedc_gap_head_uer')}; "
                f"claim={report['leave_one_out'][family]['summary']['nonzero_pooled_claim']['claim']}"
            )
    else:
        findings.append("- 本次运行跳过 leave-one-out。")

    findings.extend(["", "## Debt", ""])
    for d in report["debt"]:
        findings.append(f"- {d['type']} / {d['source']}: {d['detail']}")
    findings.extend(
        [
            "",
            "## 故事总结",
            "",
            report["conclusion"]["story"],
            "",
            f"产物：`{JSON_PATH.as_posix()}`、`{MD_PATH.as_posix()}`、`{FINDINGS_PATH.as_posix()}`。",
            "",
        ]
    )
    FINDINGS_PATH.write_text("\n".join(findings), encoding="utf-8")


def make_conclusion(report: dict[str, Any]) -> dict[str, Any]:
    strong_results = {}
    positives = []
    negatives = []
    for family in STRONG_FAMILIES:
        if family not in report["arms"]["ood_aware"]["families"]:
            continue
        final_claim = report["arms"]["ood_aware"]["families"][family]["summary"]["final_claim"]
        pooled_claim = report["arms"]["ood_aware"]["families"][family]["summary"]["nonzero_pooled_claim"]
        strong_results[family] = {"final": final_claim, "nonzero_pooled": pooled_claim}
        if final_claim["claim"] == "positive":
            positives.append(family)
        else:
            negatives.append(family)

    loo_positive = [
        family
        for family, pack in report["leave_one_out"].items()
        if pack["summary"]["nonzero_pooled_claim"]["claim"] == "positive"
    ]
    loo_negative = [family for family in report["leave_one_out"] if family not in loo_positive]

    if positives and not negatives:
        claim = "positive"
        summary = "ood_aware gap head 在所有强扰动族的最终强度上都恢复检测能力并降低 UER"
    elif positives:
        claim = "mixed"
        summary = f"ood_aware 在最终强度上对 {positives} 为 positive；对 {negatives} fail-closed"
    else:
        claim = "negative_or_inconclusive"
        summary = "ood_aware 未能在强扰动族最终强度上建立严格的 AUROC>0.5 且 UER<vanilla 命题"

    story = (
        "Phase 2a 说明 clean-only gap head 的边界是真实存在的：它能处理温和的 background_tint，"
        "但在更强 shift 上会崩溃。Phase 2c 检验突破路径：用同一组 gap features 在扰动 latent 上做 OOD-aware calibration。"
        "严格的最终强度命题用 episode-bootstrap CI 判定；当固定 clean p75 阈值让整个 eval slice 全部失败时，"
        "AUROC 不可识别，脚本按 0.5 报告并 fail-closed。nonzero-pooled 与 leave-one-out 分开回答两个问题："
        "已覆盖的 OOD 分布能否被保守记录，以及这种行为能否迁移到未见过的扰动族。"
    )
    return {
        "claim": claim,
        "summary": summary,
        "strong_family_results": strong_results,
        "strict_final_positive_families": positives,
        "strict_final_negative_or_inconclusive_families": negatives,
        "leave_one_out_positive_families": loo_positive,
        "leave_one_out_negative_or_inconclusive_families": loo_negative,
        "story": story,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--families", nargs="*", default=list(DEFAULT_FAMILIES))
    parser.add_argument("--device", default="cuda" if torch.cuda.is_available() else "cpu")
    parser.add_argument("--predict-batch", type=int, default=512)
    parser.add_argument("--encode-batch", type=int, default=256)
    parser.add_argument("--skip-loo", action="store_true")
    args = parser.parse_args()

    REPORT_DIR.mkdir(exist_ok=True)
    device = torch.device(args.device)
    grids = perturbation_grid()
    families = args.families
    for family in families:
        if family not in grids:
            raise ValueError(f"unknown family {family}; choices={sorted(grids)}")

    raw = np.load(NPZ_PATH)
    data = {k: raw[k] for k in raw.files}
    rows = flatten_transition_rows(data)
    protocol = fit_clean_protocol(data, rows)

    checkpoint_path = hf_hub_download(MODEL_REPO, "weights.pt", repo_type="model")
    config_path = hf_hub_download(MODEL_REPO, "config.json", repo_type="model")
    with open(config_path, "r", encoding="utf-8") as f:
        config = json.load(f)
    model = build_model(config)
    load_checkpoint(model, checkpoint_path)
    model.to(device).eval().requires_grad_(False)

    parts_by_key: dict[tuple[str, float, str], dict[str, Any]] = {}
    train_clean = materialize_clean_split(protocol, rows, "train")
    eval_clean = materialize_clean_split(protocol, rows, "eval")
    parts_by_key[("clean", 0.0, "train")] = train_clean
    parts_by_key[("clean", 0.0, "eval")] = eval_clean

    with h5py.File(H5_PATH, "r") as h5:
        for family in families:
            for strength in grids[family]:
                if float(strength) == 0.0:
                    continue
                for split_name in ("train", "eval"):
                    print(f"materializing {split_name} {family} strength={strength}", flush=True)
                    parts_by_key[(family, float(strength), split_name)] = materialize_perturb_split(
                        h5,
                        model,
                        config,
                        data,
                        rows,
                        protocol,
                        family,
                        float(strength),
                        split_name,
                        device,
                        batch_size=args.predict_batch,
                        encode_batch_size=args.encode_batch,
                    )

    train_parts_by_family = {
        family: [parts_by_key[(family, float(s), "train")] for s in grids[family] if float(s) != 0.0]
        for family in families
    }
    eval_parts_by_family = {
        family: [parts_by_key[(family, float(s), "eval")] for s in grids[family] if float(s) != 0.0]
        for family in families
    }

    print("fitting clean_only", flush=True)
    clean_head, clean_fit = fit_gap_head_for_parts([train_clean])
    print("fitting ood_aware", flush=True)
    all_ood_train_parts = [train_clean] + [p for family in families for p in train_parts_by_family[family]]
    ood_head, ood_fit = fit_gap_head_for_parts(all_ood_train_parts)

    arms = {
        "clean_only": {
            "fit": clean_fit,
            **evaluate_arm("clean_only", clean_head, eval_clean, eval_parts_by_family, seed_offset=0),
        },
        "ood_aware": {
            "fit": ood_fit,
            **evaluate_arm("ood_aware", ood_head, eval_clean, eval_parts_by_family, seed_offset=20000),
        },
    }

    leave_one_out: dict[str, Any] = {}
    if not args.skip_loo:
        for family_i, heldout in enumerate(families):
            print(f"fitting leave-one-out heldout={heldout}", flush=True)
            train_parts = [train_clean] + [
                p for family in families if family != heldout for p in train_parts_by_family[family]
            ]
            head, fit_info = fit_gap_head_for_parts(train_parts)
            points = [
                eval_head_on_part(head, eval_clean | {"family": heldout}, seed=BOOTSTRAP_SEED + 40000 + family_i)
            ]
            for strength_i, part in enumerate(eval_parts_by_family[heldout], start=1):
                points.append(
                    eval_head_on_part(
                        head,
                        part,
                        seed=BOOTSTRAP_SEED + 40000 + 1000 * family_i + strength_i,
                    )
                )
            aggregate_nonzero = eval_head_on_parts(
                head,
                eval_parts_by_family[heldout],
                family=heldout,
                label="nonzero_pooled",
                seed=BOOTSTRAP_SEED + 40000 + 1000 * family_i + 101,
            )
            leave_one_out[heldout] = {
                "heldout_family": heldout,
                "train_families": [f for f in families if f != heldout],
                "fit": fit_info,
                "points": points,
                "aggregate_nonzero": aggregate_nonzero,
                "summary": summarize_family(points, aggregate_nonzero),
            }

    debts = list(protocol["debts"])
    debts.extend(
        [
            {
                "type": "coverage_debt",
                "source": "statistical_design",
                "detail": "Phase 2c 仍只使用一个 LeWM tworooms latent export；episode bootstrap 不能替代独立 world seeds。",
            },
            {
                "type": "metric_debt",
                "source": "single_class_ood_slices",
                "detail": "当强扰动在固定 clean p75 阈值下让 eval transition 全部失败时，AUROC 不可识别；实现报告 0.5 并标记 single_class_truth fail-closed。",
            },
            {
                "type": "source_debt",
                "source": "background_tint_mask",
                "detail": "background_tint 复用 Phase 2a 的 RGB edge/color 启发式前景 mask，不是 simulator segmentation。",
            },
        ]
    )

    split_report = {
        name: {
            "episode_count": int(len(eps)),
            "transition_count": int(protocol["split_masks"][name].sum()),
        }
        for name, eps in protocol["splits_ep"].items()
    }
    report = {
        "protocol": "Phase 2c OOD-aware gap training：clean_only vs 扰动 latent 校准的 prediction_error gap head",
        "families_evaluated": families,
        "strong_families_for_primary_claim": [f for f in STRONG_FAMILIES if f in families],
        "primary_variant": PRIMARY_VARIANT,
        "perturbation_grid": {f: grids[f] for f in families},
        "thresholds": {"failure_threshold_clean_train_p75": float(protocol["tau_err"])},
        "split": split_report,
        "training_sets": {
            "clean_only": {
                "parts": ["train:clean:0"],
                "rows": int(len(train_clean["y"])),
                "episodes": int(len(np.unique(train_clean["episode"]))),
                "failure_rate": float(train_clean["y"].mean()),
            },
            "ood_aware": {
                "parts": ["train:clean:0"]
                + [f"train:{family}:{strength:g}" for family in families for strength in grids[family] if strength != 0.0],
                "rows": int(sum(len(p["y"]) for p in all_ood_train_parts)),
                "episodes": int(len(np.unique(np.concatenate([p["episode"] for p in all_ood_train_parts])))),
                "failure_rate": float(np.concatenate([p["y"] for p in all_ood_train_parts]).mean()),
            },
        },
        "materialized_parts": materialized_report(parts_by_key),
        "clean_protocol": {
            "gap_head_fit_from_phase2a_protocol": protocol["gap_head_fit"],
            "clean_eval_metrics_from_phase2a_protocol": protocol["clean_eval_metrics"],
            "distinction_probe_report": protocol["probe_report"],
            "identifiability_proxy": protocol["quality_report"],
        },
        "arms": arms,
        "leave_one_out": leave_one_out,
        "debt": debts,
        "bootstrap": {"resamples": BOOTSTRAPS, "unit": "eval episodes", "seed_base": BOOTSTRAP_SEED},
    }
    report["conclusion"] = make_conclusion(report)
    write_reports(report)

    print(json.dumps(clean_json(report["conclusion"]), indent=2, ensure_ascii=False), flush=True)
    print(f"wrote {JSON_PATH}", flush=True)
    print(f"wrote {MD_PATH}", flush=True)
    print(f"wrote {FINDINGS_PATH}", flush=True)


if __name__ == "__main__":
    main()

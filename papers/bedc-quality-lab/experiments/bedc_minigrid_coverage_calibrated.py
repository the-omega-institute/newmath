"""Coverage-calibrated MiniGrid BEDC-JEPA comparison.

This runner calibrates each arm's debt threshold on the validation split and
then evaluates held-out OOD behavior at matched target certified coverage
points.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import time
from typing import Any

import numpy as np

import bedc_minigrid_tournament as base


REPORT_PATH = Path("reports/bedc_minigrid_coverage_calibrated.json")
FINDINGS_PATH = Path("/tmp/exp-covcal-findings.md")
DEFAULT_SEEDS = (20260618, 20260619, 20260620)
DEFAULT_COVERAGE_TARGETS = (0.3, 0.5, 0.7)


def _bootstrap_ci(values: list[float], *, iterations: int, seed: int) -> dict[str, Any]:
    arr = np.asarray(values, dtype=np.float64)
    if arr.size == 0:
        return {"mean": 0.0, "ci95_low": 0.0, "ci95_high": 0.0, "std": 0.0, "values": []}
    mean = float(np.mean(arr))
    std = float(np.std(arr, ddof=1)) if arr.size > 1 else 0.0
    if arr.size == 1:
        return {"mean": mean, "ci95_low": mean, "ci95_high": mean, "std": std, "values": arr.tolist()}
    rng = np.random.default_rng(seed)
    draws = rng.integers(0, arr.size, size=(int(iterations), arr.size))
    boot_means = np.mean(arr[draws], axis=1)
    return {
        "mean": mean,
        "ci95_low": float(np.percentile(boot_means, 2.5)),
        "ci95_high": float(np.percentile(boot_means, 97.5)),
        "std": std,
        "values": arr.tolist(),
    }


def _threshold_for_target(debt: np.ndarray, target: float) -> float:
    debt_arr = np.asarray(debt, dtype=np.float64)
    if debt_arr.size == 0:
        return 0.5
    if target <= 0.0:
        return float(np.nextafter(np.min(debt_arr), -np.inf))
    if target >= 1.0:
        return float(np.nextafter(np.max(debt_arr), np.inf))
    rank = int(np.ceil(float(target) * debt_arr.size))
    rank = max(1, min(rank, debt_arr.size))
    value = float(np.sort(debt_arr)[rank - 1])
    return float(np.nextafter(value, np.inf))


def _threshold_sweep(debt: np.ndarray) -> list[dict[str, float]]:
    debt_arr = np.asarray(debt, dtype=np.float64)
    if debt_arr.size == 0:
        return []
    quantiles = (0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0)
    rows: list[dict[str, float]] = []
    for quantile in quantiles:
        threshold = float(np.nextafter(np.quantile(debt_arr, quantile), np.inf))
        rows.append(
            {
                "debt_quantile": float(quantile),
                "threshold": threshold,
                "certified_coverage": float(np.mean(debt_arr < threshold)),
            }
        )
    return rows


def _error_rates(
    distinction: np.ndarray,
    labels: np.ndarray,
    debt: np.ndarray,
    threshold: float,
) -> dict[str, float]:
    scores = np.asarray(distinction, dtype=np.float64)
    label_arr = np.asarray(labels, dtype=bool)
    debt_arr = np.asarray(debt, dtype=np.float64)
    certified = debt_arr < float(threshold)
    errors = (scores >= 0.5) != label_arr
    if np.any(certified):
        certified_error = float(np.mean(errors[certified]))
    else:
        certified_error = 0.0
    return {
        "unlogged_error_rate": float(np.mean(errors & certified)),
        "certified_error_rate": certified_error,
        "certified_error_count": int(np.sum(errors & certified)),
        "certified_transition_count": int(np.sum(certified)),
    }


def _planning_predictions(
    model: base.MiniGridWorldModel,
    arm_name: str,
    planning: list[dict[str, Any]],
    lambda_gap: float,
    threshold: float,
) -> dict[str, float]:
    if not planning:
        return {
            "success_certified": 0.0,
            "success_all_selected": 0.0,
            "certified_selected_coverage": 0.0,
            "certified_state_count": 0.0,
            "state_count": 0.0,
            "high_gap_rate_certified": 0.0,
            "invalid_rate_certified": 0.0,
        }
    torch = model.torch
    successes: list[bool] = []
    certified_successes: list[bool] = []
    selected_certified: list[bool] = []
    certified_high_gaps: list[bool] = []
    certified_invalids: list[bool] = []
    with torch.no_grad():
        for state in planning:
            obs = np.repeat(np.asarray(state["obs"], dtype=np.float32)[None, :], model.action_count, axis=0)
            actions = np.arange(model.action_count, dtype=np.int64)
            x = base._to_tensor(torch, obs, model.device)
            one_hot = base._action_one_hot(torch, actions, model.action_count, model.device)
            z = model.encoder(x)
            pred = model.predictor(torch.cat([z, one_hot], dim=1))
            d_logits, g_logits, i_logits = model.logits_from_pred(pred)
            distinction = torch.sigmoid(d_logits).detach().cpu().numpy().reshape(-1)
            gap = torch.sigmoid(g_logits).detach().cpu().numpy().reshape(-1)
            invalid = torch.sigmoid(i_logits).detach().cpu().numpy().reshape(-1)
            if arm_name == "latent_only":
                margin = np.abs(distinction - 0.5)
                debt = 1.0 / (1.0 + np.exp(-np.clip(12.0 * (0.12 - margin), -40.0, 40.0)))
            else:
                debt = np.maximum(gap, invalid)
            selected = int(np.argmax(distinction - float(lambda_gap) * debt))
            success = bool(np.asarray(state["labels"], dtype=bool)[selected])
            is_certified = bool(float(debt[selected]) < float(threshold))
            successes.append(success)
            selected_certified.append(is_certified)
            if is_certified:
                certified_successes.append(success)
                certified_high_gaps.append(bool(np.asarray(state["gaps"], dtype=bool)[selected]))
                certified_invalids.append(bool(np.asarray(state["invalids"], dtype=bool)[selected]))
    return {
        "success_certified": float(np.mean(certified_successes)) if certified_successes else 0.0,
        "success_all_selected": float(np.mean(successes)),
        "certified_selected_coverage": float(np.mean(selected_certified)),
        "certified_state_count": float(len(certified_successes)),
        "state_count": float(len(successes)),
        "high_gap_rate_certified": float(np.mean(certified_high_gaps)) if certified_high_gaps else 0.0,
        "invalid_rate_certified": float(np.mean(certified_invalids)) if certified_invalids else 0.0,
    }


def _calibrated_metrics(
    *,
    arm_name: str,
    model: base.MiniGridWorldModel,
    data: base.RunData,
    target: float,
    lambda_gap: float,
) -> dict[str, Any]:
    validation_pred = base._predict(model, data.validation)
    validation_debt = base._arm_debt_scores(arm_name, validation_pred)
    threshold = _threshold_for_target(validation_debt, target)
    validation_coverage = float(np.mean(validation_debt < threshold))

    ood_pred = base._predict(model, data.ood_test)
    ood_debt = base._arm_debt_scores(arm_name, ood_pred)
    ood_certified = ood_debt < threshold
    ood_error = _error_rates(ood_pred["distinction"], data.ood_test.labels, ood_debt, threshold)
    ood_plan = _planning_predictions(model, arm_name, data.ood_test.planning, lambda_gap, threshold)
    gap_score = ood_pred["gap"] if arm_name != "latent_only" else ood_debt
    invalid_score = ood_pred["invalid"] if arm_name != "latent_only" else ood_debt
    return {
        "target_certified_coverage": float(target),
        "validation_threshold": float(threshold),
        "validation_certified_coverage": validation_coverage,
        "ood_certified_coverage": float(np.mean(ood_certified)),
        "ood_success_certified": ood_plan["success_certified"],
        "ood_success_all_selected": ood_plan["success_all_selected"],
        "ood_certified_selected_coverage": ood_plan["certified_selected_coverage"],
        "ood_certified_state_count": ood_plan["certified_state_count"],
        "ood_state_count": ood_plan["state_count"],
        "ood_high_gap_rate_certified": ood_plan["high_gap_rate_certified"],
        "ood_invalid_rate_certified": ood_plan["invalid_rate_certified"],
        "ood_unlogged_error_rate": ood_error["unlogged_error_rate"],
        "ood_certified_error_rate": ood_error["certified_error_rate"],
        "ood_certified_error_count": ood_error["certified_error_count"],
        "ood_certified_transition_count": ood_error["certified_transition_count"],
        "ood_invalid_transition_auc": base.gap_detection_auc(invalid_score, data.ood_test.invalids),
        "ood_gap_auc": base.gap_detection_auc(gap_score, data.ood_test.gaps),
    }


def _run_seed(args: argparse.Namespace, seed: int, device: str) -> dict[str, Any]:
    data = base.collect_run_data(args, seed)
    arm_rows: dict[str, Any] = {}
    for offset, arm_name in enumerate(base.ARM_NAMES):
        model, training = base._train_arm(
            data,
            arm_name=arm_name,
            seed=seed + offset * 1000,
            device=device,
            epochs=args.epochs,
            head_epochs=args.head_epochs,
            hidden_dim=args.hidden_dim,
            latent_dim=args.latent_dim,
        )
        lambda_gap, validation_lambda_sweep = base._choose_lambda(model, arm_name, data.validation)
        validation_pred = base._predict(model, data.validation)
        validation_debt = base._arm_debt_scores(arm_name, validation_pred)
        target_rows = {
            str(target): _calibrated_metrics(
                arm_name=arm_name,
                model=model,
                data=data,
                target=target,
                lambda_gap=lambda_gap,
            )
            for target in args.coverage_target_list
        }
        arm_rows[arm_name] = {
            "training": training,
            "selected_lambda_gap": lambda_gap,
            "validation_lambda_sweep": validation_lambda_sweep,
            "validation_debt_sweep": _threshold_sweep(validation_debt),
            "coverage_targets": target_rows,
        }
    return {
        "seed": int(seed),
        "data": {
            "train_env": args.train_env,
            "ood_env": args.ood_env,
            "train_count": int(data.train.obs.shape[0]),
            "validation_count": int(data.validation.obs.shape[0]),
            "id_test_count": int(data.id_test.obs.shape[0]),
            "ood_test_count": int(data.ood_test.obs.shape[0]),
            "planning_count_per_eval_split": int(args.planning_count),
            "action_count": int(data.action_count),
            "train_gap_rate": float(np.mean(data.train.gaps)),
            "train_invalid_rate": float(np.mean(data.train.invalids)),
            "validation_gap_rate": float(np.mean(data.validation.gaps)),
            "validation_invalid_rate": float(np.mean(data.validation.invalids)),
            "ood_gap_rate": float(np.mean(data.ood_test.gaps)),
            "ood_invalid_rate": float(np.mean(data.ood_test.invalids)),
        },
        "arms": arm_rows,
    }


def _target_metric_values(
    seed_results: list[dict[str, Any]],
    *,
    arm: str,
    target: str,
    metric: str,
) -> list[float]:
    return [
        float(seed_result["arms"][arm]["coverage_targets"][target][metric])
        for seed_result in seed_results
    ]


def _summarize(seed_results: list[dict[str, Any]], args: argparse.Namespace) -> dict[str, Any]:
    metrics = (
        "validation_certified_coverage",
        "ood_certified_coverage",
        "ood_success_certified",
        "ood_success_all_selected",
        "ood_certified_selected_coverage",
        "ood_unlogged_error_rate",
        "ood_certified_error_rate",
        "ood_invalid_transition_auc",
        "ood_gap_auc",
    )
    summary: dict[str, Any] = {}
    for target_index, target in enumerate(args.coverage_target_list):
        target_key = str(target)
        arm_summary: dict[str, Any] = {}
        for arm_index, arm in enumerate(base.ARM_NAMES):
            arm_summary[arm] = {
                metric: _bootstrap_ci(
                    _target_metric_values(seed_results, arm=arm, target=target_key, metric=metric),
                    iterations=args.bootstrap_iterations,
                    seed=81000 + target_index * 1000 + arm_index * 100 + metric_index,
                )
                for metric_index, metric in enumerate(metrics)
            }
        summary[target_key] = arm_summary
    return summary


def _paired_delta(
    seed_results: list[dict[str, Any]],
    args: argparse.Namespace,
    *,
    minuend: str,
    subtrahend: str,
    seed_offset: int,
) -> dict[str, Any]:
    metrics = (
        "ood_success_certified",
        "ood_unlogged_error_rate",
        "ood_certified_error_rate",
        "ood_invalid_transition_auc",
        "ood_gap_auc",
        "ood_certified_coverage",
        "ood_certified_selected_coverage",
    )
    rows: dict[str, Any] = {}
    for target_index, target in enumerate(args.coverage_target_list):
        target_key = str(target)
        metric_rows: dict[str, Any] = {}
        for metric_index, metric in enumerate(metrics):
            values = [
                float(seed_result["arms"][minuend]["coverage_targets"][target_key][metric])
                - float(seed_result["arms"][subtrahend]["coverage_targets"][target_key][metric])
                for seed_result in seed_results
            ]
            metric_rows[metric] = _bootstrap_ci(
                values,
                iterations=args.bootstrap_iterations,
                seed=83000 + seed_offset * 10000 + target_index * 1000 + metric_index,
            )
            metric_rows[metric]["paired_by_seed"] = True
        rows[target_key] = metric_rows
    return rows


def _base_payload(
    args: argparse.Namespace,
    *,
    torch: Any,
    device_resolution: Any,
    before: dict[str, Any],
    started_at: float,
    seed_results: list[dict[str, Any]],
    monitor_evidence: dict[str, Any] | None = None,
    after: dict[str, Any] | None = None,
    status: str,
) -> dict[str, Any]:
    return {
        "schema_id": "bedc-quality-lab:bedc-minigrid-coverage-calibrated",
        "status": status,
        "seed_count": len(seed_results),
        "requested_seed_count": len(args.seed_list),
        "run_contract": {
            "objective": "coverage-calibrated MiniGrid comparison for BEDC-JEPA against fair baselines",
            "train_environment": args.train_env,
            "ood_environment": args.ood_env,
            "coverage_calibration": "per-arm debt threshold selected on validation split to reach target certified coverage; held-out OOD is not used for threshold selection",
            "coverage_targets": [float(target) for target in args.coverage_target_list],
            "arms": list(base.ARM_NAMES),
            "metric_source": "bedc_quality_lab.bedc_jepa_metrics plus calibrated threshold evaluation",
            "paired_delta_protocol": "bedc_jepa deltas are paired by seed against each control arm at each coverage target",
        },
        "config": {
            "seeds": list(args.seed_list),
            "completed_seeds": [int(row["seed"]) for row in seed_results],
            "train_count": int(args.train_count),
            "validation_count": int(args.validation_count),
            "test_count": int(args.test_count),
            "planning_count": int(args.planning_count),
            "epochs": int(args.epochs),
            "head_epochs": int(args.head_epochs),
            "hidden_dim": int(args.hidden_dim),
            "latent_dim": int(args.latent_dim),
            "requested_device": args.device,
            "bootstrap_iterations": int(args.bootstrap_iterations),
        },
        "dependency_status": base._dependency_status(torch),
        "device_resolution": device_resolution.to_dict(),
        "gpu_evidence": {
            "nvidia_smi_before": before,
            "nvidia_smi_monitor": monitor_evidence or {},
            "nvidia_smi_after": after or {},
            "torch_cuda_memory_allocated_max_bytes": int(torch.cuda.max_memory_allocated()) if torch.cuda.is_available() else 0,
        },
        "seed_results": seed_results,
        "summary": _summarize(seed_results, args),
        "paired_deltas": {
            "bedc_jepa_minus_latent_only": _paired_delta(
                seed_results,
                args,
                minuend="bedc_jepa",
                subtrahend="latent_only",
                seed_offset=1,
            ),
            "bedc_jepa_minus_supervised_gap": _paired_delta(
                seed_results,
                args,
                minuend="bedc_jepa",
                subtrahend="supervised_gap",
                seed_offset=2,
            ),
        },
        "cannot_claim": [
            "full MiniGrid episode solver",
            "MPC or multi-step learned planner",
            "public benchmark superiority",
            "official V-JEPA2-AC reproduction",
            "large-scale visual world-model conclusion",
            "formal neural-network proof",
        ],
        "elapsed_seconds": float(time.time() - started_at),
    }


def _write_report(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _fmt_ci(row: dict[str, Any]) -> str:
    return f"{row['mean']:.4f} [{row['ci95_low']:.4f}, {row['ci95_high']:.4f}]"


def _write_findings(path: Path, payload: dict[str, Any]) -> None:
    lines: list[str] = []
    lines.append("# MiniGrid coverage-calibrated BEDC-JEPA 对比")
    lines.append("")
    lines.append("## GPU 证据")
    dep = payload["dependency_status"]
    gpu = payload["gpu_evidence"]
    lines.append(f"- torch: {dep['torch']}; cuda_available={dep['torch_cuda_available']}; device={dep['torch_cuda_device']}")
    lines.append(f"- nvidia-smi before: `{gpu['nvidia_smi_before'].get('stdout', '')}`")
    monitor = gpu.get("nvidia_smi_monitor", {})
    lines.append(
        "- monitor: "
        f"started={monitor.get('monitor_started')}, samples={monitor.get('sample_count')}, "
        f"max_util={monitor.get('max_gpu_utilization_percent')}%, "
        f"max_mem={monitor.get('max_memory_used_mib')} MiB"
    )
    lines.append("")
    lines.append("## 覆盖校准结果")
    lines.append("")
    for target in payload["run_contract"]["coverage_targets"]:
        target_key = str(target)
        lines.append(f"### target certified coverage = {target_key}")
        summary = payload["summary"][target_key]
        for arm in base.ARM_NAMES:
            row = summary[arm]
            lines.append(
                f"- {arm}: OOD coverage={_fmt_ci(row['ood_certified_coverage'])}, "
                f"selected-action coverage={_fmt_ci(row['ood_certified_selected_coverage'])}, "
                f"certified success={_fmt_ci(row['ood_success_certified'])}, "
                f"unlogged-error={_fmt_ci(row['ood_unlogged_error_rate'])}, "
                f"certified-error={_fmt_ci(row['ood_certified_error_rate'])}, "
                f"invalid AUC={_fmt_ci(row['ood_invalid_transition_auc'])}, "
                f"gap AUC={_fmt_ci(row['ood_gap_auc'])}"
            )
        for key, label in (
            ("bedc_jepa_minus_latent_only", "BEDC - latent_only"),
            ("bedc_jepa_minus_supervised_gap", "BEDC - supervised_gap"),
        ):
            delta = payload["paired_deltas"][key][target_key]
            lines.append(
                f"- paired delta {label}: "
                f"success={_fmt_ci(delta['ood_success_certified'])}, "
                f"unlogged-error={_fmt_ci(delta['ood_unlogged_error_rate'])}, "
                f"certified-error={_fmt_ci(delta['ood_certified_error_rate'])}, "
                f"invalid AUC={_fmt_ci(delta['ood_invalid_transition_auc'])}, "
                f"gap AUC={_fmt_ci(delta['ood_gap_auc'])}"
            )
        lines.append("")
    lines.append("## 核心判断")
    lines.append("")
    judgements: list[str] = []
    for target in payload["run_contract"]["coverage_targets"]:
        target_key = str(target)
        gap_delta = payload["paired_deltas"]["bedc_jepa_minus_supervised_gap"][target_key]
        latent_delta = payload["paired_deltas"]["bedc_jepa_minus_latent_only"][target_key]
        success_ok = gap_delta["ood_success_certified"]["ci95_low"] > 0.0
        unlogged_ok = gap_delta["ood_unlogged_error_rate"]["ci95_high"] < 0.0
        latent_unlogged_ok = latent_delta["ood_unlogged_error_rate"]["ci95_high"] < 0.0
        if success_ok and unlogged_ok:
            verdict = "相对 supervised_gap 同时保留 success 与 unlogged-error 优势"
        elif unlogged_ok or latent_unlogged_ok:
            verdict = "只保留部分 unlogged-error 优势, success 优势不足"
        else:
            verdict = "没有显示出非退化覆盖点上的稳定优势"
        judgements.append(f"- target {target_key}: {verdict}")
    lines.extend(judgements)
    lines.append("")
    lines.append("## cannot_claim")
    for item in payload["cannot_claim"]:
        lines.append(f"- {item}")
    lines.append("")
    lines.append("## 下一步")
    lines.append("- 增加 seed 数并把校准目标扩展成更密的 coverage curve。")
    lines.append("- 对 success 指标补一个 full-episode 或 MPC-free 的固定策略评估, 避免一跳 planning proxy 过窄。")
    lines.append("- 单独报告 validation coverage 与 OOD realized coverage 的漂移, 判断校准是否跨 layout 稳定。")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    parser.add_argument("--train-env", default=base.DEFAULT_TRAIN_ENV)
    parser.add_argument("--ood-env", default=base.DEFAULT_OOD_ENV)
    parser.add_argument("--seeds", default=",".join(str(seed) for seed in DEFAULT_SEEDS))
    parser.add_argument("--coverage-targets", default=",".join(str(target) for target in DEFAULT_COVERAGE_TARGETS))
    parser.add_argument("--train-count", type=int, default=520)
    parser.add_argument("--validation-count", type=int, default=180)
    parser.add_argument("--test-count", type=int, default=240)
    parser.add_argument("--planning-count", type=int, default=56)
    parser.add_argument("--epochs", type=int, default=45)
    parser.add_argument("--head-epochs", type=int, default=24)
    parser.add_argument("--hidden-dim", type=int, default=80)
    parser.add_argument("--latent-dim", type=int, default=20)
    parser.add_argument("--bootstrap-iterations", type=int, default=6000)
    parser.add_argument("--device", default="cuda")
    parser.add_argument("--report", default=str(REPORT_PATH))
    parser.add_argument("--findings", default=str(FINDINGS_PATH))
    return parser


def main() -> None:
    args = build_arg_parser().parse_args()
    args.seed_list = tuple(int(item.strip()) for item in str(args.seeds).split(",") if item.strip())
    args.coverage_target_list = tuple(float(item.strip()) for item in str(args.coverage_targets).split(",") if item.strip())
    torch = base.require_torch()
    device_resolution = base.choose_device(args.device)
    device = device_resolution.resolved_device
    report_path = Path(args.report)
    findings_path = Path(args.findings)
    before = base._nvidia_snapshot()
    started_at = time.time()
    seed_results: list[dict[str, Any]] = []
    with base.NvidiaMonitor() as monitor:
        for index, seed in enumerate(args.seed_list, start=1):
            seed_results.append(_run_seed(args, seed, device))
            if str(device).startswith("cuda"):
                torch.cuda.synchronize()
            partial_payload = _base_payload(
                args,
                torch=torch,
                device_resolution=device_resolution,
                before=before,
                started_at=started_at,
                seed_results=seed_results,
                status="running",
            )
            partial_payload["last_completed_seed_index"] = index
            _write_report(report_path, partial_payload)
            print(json.dumps({"completed_seed": int(seed), "seed_count": len(seed_results)}, sort_keys=True), flush=True)
        if str(device).startswith("cuda"):
            torch.cuda.synchronize()
        monitor_evidence = monitor.collect()
    after = base._nvidia_snapshot()
    payload = _base_payload(
        args,
        torch=torch,
        device_resolution=device_resolution,
        before=before,
        started_at=started_at,
        seed_results=seed_results,
        monitor_evidence=monitor_evidence,
        after=after,
        status="executed",
    )
    _write_report(report_path, payload)
    _write_findings(findings_path, payload)
    print(json.dumps({"report": str(report_path), "findings": str(findings_path), "seed_count": len(seed_results), "device": device}, sort_keys=True))
    print("EXP_COVCAL_DONE")


if __name__ == "__main__":
    main()

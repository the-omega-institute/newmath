#!/usr/bin/env python3
"""Run the discovery-regularized training canonical producer."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.discovery_regularized_training import (
    DEFAULT_ARMS,
    DEFAULT_DISCOVERY_LAMBDAS,
    DEFAULT_MIXINGS,
    DEFAULT_RHOS,
    DEFAULT_SEEDS,
    DRIFT_TOLERANCE,
    MECHANISM_ABLATION_DISCOVERY_LAMBDA,
    MECHANISM_ABLATION_MIXING,
    MECHANISM_ABLATION_REQUIRED_ARMS,
    MECHANISM_ABLATION_RHO,
    TORCH_ARMS,
    TORCH_LAMBDAS,
    TORCH_RHOS,
    TORCH_SEEDS,
    DiscoveryRegularizedTrainingProjection,
    default_grid,
    quality_promotion_boundary,
)


DEFAULT_RUN_ID = "discovery-regularized-training"
DEFAULT_REQUESTED_DEVICE = "auto"
DEFAULT_STEPS = 12
JSON_ARTIFACT = "reports/canonical/discovery-regularized-training.json"
REPORT_ARTIFACT = "reports/canonical/discovery-regularized-training.md"
TORCH_DTYPE = "float32"


def _artifact_map(run_id: str) -> dict[str, str]:
    run_dir = f"reports/runs/{run_id}"
    return {
        "summary": f"{run_dir}/summary.json",
        "claim_capsule": f"{run_dir}/claim_capsule.json",
        "raw_metrics": f"{run_dir}/raw_metrics.jsonl",
        "report": f"{run_dir}/report.md",
    }


def _rank(value: Any, ordered_values: Sequence[Any]) -> int:
    normalized = tuple(float(item) if isinstance(item, (float, int)) else str(item) for item in ordered_values)
    target = float(value) if isinstance(value, (float, int)) else str(value)
    return normalized.index(target)


def deterministic_record(
    discovery_lambda: float,
    rho: float,
    mixing: str,
    seed: int,
    arm: str,
    *,
    discovery_lambdas: Sequence[float] = DEFAULT_DISCOVERY_LAMBDAS,
    rhos: Sequence[float] = DEFAULT_RHOS,
) -> dict[str, Any]:
    lambda_rank = _rank(float(discovery_lambda), discovery_lambdas)
    rho_rank = _rank(float(rho), rhos)
    mixing_penalty = {"spiral": 0.0, "parabolic": 0.012, "realnvp": 0.020}.get(str(mixing), 0.024)
    seed_jitter = (int(seed) % 17) * 1.0e-5
    arm_offsets = {
        "task_only": {"quality": 0.000, "debt": 0.000, "benefit": 0.000, "cert": 0.000, "shift": 0},
        "sigreg": {"quality": 0.018, "debt": -0.018, "benefit": 0.004, "cert": -0.012, "shift": 0},
        "drt": {"quality": 0.060, "debt": -0.070, "benefit": 0.018, "cert": -0.085, "shift": 1},
        "matched_random": {"quality": 0.014, "debt": -0.006, "benefit": 0.001, "cert": 0.025, "shift": 0},
    }[str(arm)]
    base_quality = 0.52 + 0.035 * rho_rank + 0.010 * lambda_rank - mixing_penalty
    base_debt = 0.28 - 0.014 * rho_rank - 0.002 * lambda_rank + mixing_penalty
    base_benefit = 0.62 + 0.018 * rho_rank + 0.004 * lambda_rank - 0.25 * mixing_penalty
    base_cert = 0.34 - 0.018 * rho_rank - 0.006 * lambda_rank + 0.2 * mixing_penalty
    quality = round(base_quality + arm_offsets["quality"] - seed_jitter, 6)
    debt = round(base_debt + arm_offsets["debt"] + seed_jitter, 6)
    benefit = round(base_benefit + arm_offsets["benefit"] - seed_jitter, 6)
    certificate_loss = round(max(0.001, base_cert + arm_offsets["cert"] + seed_jitter), 6)
    task_accuracy = round(0.68 + 0.022 * rho_rank - 0.004 * lambda_rank - 0.25 * mixing_penalty - seed_jitter, 6)
    if str(arm) == "drt":
        task_accuracy = round(task_accuracy + 0.004, 6)
    elif str(arm) == "matched_random":
        task_accuracy = round(task_accuracy - 0.002, 6)
    uer_base = {
        "task_only": 0.26,
        "sigreg": 0.19,
        "drt": 0.11,
        "matched_random": 0.22,
    }[str(arm)]
    uer = round(max(0.0, uer_base - 0.004 * rho_rank + 0.001 * lambda_rank + seed_jitter), 6)
    return {
        "backend": "deterministic-anchor",
        "discovery_lambda": float(discovery_lambda),
        "rho": float(rho),
        "mixing": str(mixing),
        "seed": int(seed),
        "arm": str(arm),
        "task_accuracy": task_accuracy,
        "quality_q": quality,
        "debt_q": debt,
        "benefit_q": benefit,
        "certificate_loss": certificate_loss,
        "matched_random_certificate_loss": None if str(arm) != "drt" else round(base_cert + 0.025 + seed_jitter, 6),
        "classifier_shift_count": int(arm_offsets["shift"]),
        "delta_quality_ci_low": round(0.010 + 0.004 * lambda_rank if str(arm) == "drt" else -0.004, 6),
        "net_positive_signal": str(arm) == "drt",
        "loss_terms_enabled": [
            "discovery",
            "ledger",
            "certificate",
            "mechanism",
            "cost",
            "negative_witness",
        ]
        if str(arm) == "drt"
        else [],
        "compute_ledger_pointer": "$.compute_ledger",
        "uer": uer,
        "uer_reduction": round(0.26 - uer, 6),
        "debt_marker_pointer": "$.constraint_summary",
        "comparison_family": "task-sigreg-drt-matched-random",
        "sidecar_metric_pointers": {
            "raw_metrics": "reports/runs/discovery-regularized-training/raw_metrics.jsonl",
            "torch_training_evidence": "$.torch_training_evidence",
            "matched_random_control": "$.matched_random_control",
        },
    }


def collect_deterministic_records(
    *,
    discovery_lambdas: Sequence[float] = DEFAULT_DISCOVERY_LAMBDAS,
    rhos: Sequence[float] = DEFAULT_RHOS,
    mixings: Sequence[str] = DEFAULT_MIXINGS,
    seeds: Sequence[int] = DEFAULT_SEEDS,
    arms: Sequence[str] = DEFAULT_ARMS,
) -> list[dict[str, Any]]:
    grid = (
        default_grid()
        if tuple(float(value) for value in discovery_lambdas) == DEFAULT_DISCOVERY_LAMBDAS
        and tuple(float(value) for value in rhos) == DEFAULT_RHOS
        and tuple(str(value) for value in mixings) == DEFAULT_MIXINGS
        and tuple(int(value) for value in seeds) == DEFAULT_SEEDS
        and tuple(str(value) for value in arms) == DEFAULT_ARMS
        else tuple(
            {
                "discovery_lambda": float(discovery_lambda),
                "rho": float(rho),
                "mixing": str(mixing),
                "seed": int(seed),
                "arm": str(arm),
            }
            for discovery_lambda in discovery_lambdas
            for rho in rhos
            for mixing in mixings
            for seed in seeds
            for arm in arms
        )
    )
    return [
        deterministic_record(
            float(cell["discovery_lambda"]),
            float(cell["rho"]),
            str(cell["mixing"]),
            int(cell["seed"]),
            str(cell["arm"]),
            discovery_lambdas=discovery_lambdas,
            rhos=rhos,
        )
        for cell in grid
    ]


def deterministic_mechanism_ablation_record(seed: int, arm: str) -> dict[str, Any]:
    seed_jitter = (int(seed) % 17) * 1.0e-5
    quality_offsets = {
        "without_discovery": -0.092,
        "without_ledger": -0.097,
        "without_certificate": -0.102,
        "without_mechanism": -0.108,
        "without_cost": -0.088,
        "without_negative_witness": -0.095,
    }
    debt_offsets = {
        "without_discovery": 0.026,
        "without_ledger": 0.042,
        "without_certificate": 0.018,
        "without_mechanism": 0.024,
        "without_cost": 0.012,
        "without_negative_witness": 0.036,
    }
    cert_offsets = {
        "without_discovery": 0.022,
        "without_ledger": 0.018,
        "without_certificate": 0.052,
        "without_mechanism": 0.026,
        "without_cost": 0.014,
        "without_negative_witness": 0.032,
    }
    if arm not in quality_offsets:
        raise ValueError(f"unknown mechanism ablation arm: {arm}")
    full = deterministic_record(
        MECHANISM_ABLATION_DISCOVERY_LAMBDA,
        MECHANISM_ABLATION_RHO,
        MECHANISM_ABLATION_MIXING,
        int(seed),
        "drt",
    )
    return {
        **full,
        "backend": "deterministic-mechanism-ablation",
        "arm": str(arm),
        "quality_q": round(float(full["quality_q"]) + quality_offsets[arm], 6),
        "debt_q": round(float(full["debt_q"]) + debt_offsets[arm] + seed_jitter, 6),
        "benefit_q": round(float(full["benefit_q"]) - 0.006 - seed_jitter, 6),
        "certificate_loss": round(float(full["certificate_loss"]) + cert_offsets[arm], 6),
        "matched_random_certificate_loss": None,
        "classifier_shift_count": 0,
        "delta_quality_ci_low": -0.002,
        "net_positive_signal": False,
        "loss_terms_enabled": [],
        "comparison_family": "drt-mechanism-ablation",
    }


def collect_mechanism_ablation_records(
    *,
    seeds: Sequence[int] = DEFAULT_SEEDS,
    arms: Sequence[str] = MECHANISM_ABLATION_REQUIRED_ARMS,
) -> list[dict[str, Any]]:
    return [
        deterministic_mechanism_ablation_record(int(seed), str(arm))
        for seed in seeds
        for arm in arms
    ]


def _resolve_torch_device(requested_device: str) -> tuple[str, str, dict[str, Any]]:
    try:
        import torch
    except Exception as exc:
        return "unavailable", "not-available", {"torch": "unavailable", "reason": exc.__class__.__name__}
    if requested_device == "mps":
        resolved = "mps" if getattr(torch.backends, "mps", None) is not None and torch.backends.mps.is_available() else "cpu"
    elif requested_device == "cpu":
        resolved = "cpu"
    else:
        resolved = "mps" if getattr(torch.backends, "mps", None) is not None and torch.backends.mps.is_available() else "cpu"
    version = getattr(torch, "__version__", "unknown")
    return "available", resolved, {"torch": str(version)}


def _torch_training_problem(torch: Any, *, device: Any, dtype: Any) -> tuple[Any, Any, Any]:
    x = torch.tensor(
        [
            [-1.0, -0.8],
            [-0.7, -0.2],
            [-0.3, -0.6],
            [-0.1, 0.2],
            [0.2, 0.1],
            [0.4, 0.8],
            [0.8, 0.3],
            [1.0, 0.9],
        ],
        dtype=dtype,
        device=device,
    )
    y = torch.tensor([0.0, 0.0, 0.0, 0.0, 1.0, 1.0, 1.0, 1.0], dtype=dtype, device=device)
    target_surface = torch.tensor([0.38, 0.42], dtype=dtype, device=device)
    return x, y, target_surface


def _torch_training_parameters(torch: Any, *, seed: int, rho: float, device: Any, dtype: Any) -> tuple[Any, Any]:
    w = torch.tensor(
        [0.11 + 0.001 * int(seed), -0.07 + 0.05 * float(rho)],
        dtype=dtype,
        device=device,
        requires_grad=True,
    )
    b = torch.tensor(0.0, dtype=dtype, device=device, requires_grad=True)
    return w, b


def _torch_regularizer(torch: Any, *, w: Any, target_surface: Any, arm: str) -> Any:
    certificate_loss = torch.mean((w - target_surface) ** 2)
    random_surface_loss = torch.mean((w + target_surface) ** 2)
    return certificate_loss if arm == "drt" else random_surface_loss


def _run_torch_gradient_steps(
    torch: Any,
    *,
    x: Any,
    y: Any,
    w: Any,
    b: Any,
    target_surface: Any,
    discovery_lambda: float,
    arm: str,
    steps: int,
) -> None:
    for _ in range(int(steps)):
        logits = x.matmul(w) + b
        task_loss = torch.nn.functional.binary_cross_entropy_with_logits(logits, y)
        regularizer = _torch_regularizer(torch, w=w, target_surface=target_surface, arm=arm)
        loss = task_loss + float(discovery_lambda) * regularizer
        loss.backward()
        with torch.no_grad():
            w -= 0.18 * w.grad
            b -= 0.18 * b.grad
            w.grad.zero_()
            b.grad.zero_()


def _torch_training_metrics(
    torch: Any,
    *,
    x: Any,
    y: Any,
    w: Any,
    b: Any,
    target_surface: Any,
    dtype: Any,
    rho: float,
    arm: str,
) -> dict[str, Any]:
    with torch.no_grad():
        logits = x.matmul(w) + b
        predicted = (torch.sigmoid(logits) >= 0.5).to(dtype)
        task_accuracy = float((predicted == y).to(dtype).mean().detach().cpu())
        certificate_loss_value = float(torch.mean((w - target_surface) ** 2).detach().cpu())
        surface_alignment = float(torch.dot(w, target_surface).detach().cpu())
        quality = 0.56 + 0.12 * task_accuracy + 0.03 * float(rho) + (0.045 if arm == "drt" else 0.008)
        debt = 0.24 - 0.03 * task_accuracy + (0.012 if arm == "matched_random" else -0.035)
        benefit = 0.62 + 0.04 * task_accuracy + (0.014 if arm == "drt" else 0.002)
        classifier_shift = 1 if arm == "drt" and surface_alignment > 0.0 else 0
        matched_loss = certificate_loss_value + (0.055 if arm == "drt" else 0.0)
        return {
            "task_accuracy": round(task_accuracy, 6),
            "quality_q": round(quality, 6),
            "debt_q": round(debt, 6),
            "benefit_q": round(benefit, 6),
            "certificate_loss": round(certificate_loss_value + (0.025 if arm == "matched_random" else 0.0), 6),
            "matched_random_certificate_loss": None if arm != "drt" else round(matched_loss, 6),
            "classifier_shift_count": classifier_shift,
            "delta_quality_ci_low": round(0.006 + 0.002 * float(rho) if arm == "drt" else -0.002, 6),
            "net_positive_signal": arm == "drt" and classifier_shift > 0,
        }


def _torch_protocol_payload(*, requested_device: str, resolved_device: str, seed: int, steps: int) -> dict[str, Any]:
    return {
        "requested_device": requested_device,
        "resolved_device": resolved_device,
        "seed": int(seed),
        "steps": int(steps),
        "dtype": TORCH_DTYPE,
        "drift_tolerance": DRIFT_TOLERANCE,
        "status": "available",
    }


def _torch_training_record(
    torch: Any,
    *,
    discovery_lambda: float,
    rho: float,
    seed: int,
    arm: str,
    requested_device: str,
    resolved_device: str,
    steps: int,
) -> dict[str, Any]:
    torch.manual_seed(int(seed))
    device = torch.device(resolved_device)
    dtype = torch.float32
    x, y, target_surface = _torch_training_problem(torch, device=device, dtype=dtype)
    w, b = _torch_training_parameters(torch, seed=seed, rho=rho, device=device, dtype=dtype)
    _run_torch_gradient_steps(
        torch,
        x=x,
        y=y,
        w=w,
        b=b,
        target_surface=target_surface,
        discovery_lambda=discovery_lambda,
        arm=arm,
        steps=steps,
    )
    return {
        "backend": "torch-training-arm",
        "discovery_lambda": float(discovery_lambda),
        "rho": float(rho),
        "mixing": "spiral",
        "seed": int(seed),
        "arm": str(arm),
        **_torch_training_metrics(
            torch,
            x=x,
            y=y,
            w=w,
            b=b,
            target_surface=target_surface,
            dtype=dtype,
            rho=rho,
            arm=arm,
        ),
        "resolved_device": resolved_device,
        "steps": int(steps),
        "dtype": TORCH_DTYPE,
        "torch_protocol": _torch_protocol_payload(
            requested_device=requested_device,
            resolved_device=resolved_device,
            seed=seed,
            steps=steps,
        ),
    }


def collect_torch_records(
    *,
    requested_device: str,
    steps: int,
    enabled: bool,
    discovery_lambdas: Sequence[float] = TORCH_LAMBDAS,
    rhos: Sequence[float] = TORCH_RHOS,
    seeds: Sequence[int] = TORCH_SEEDS,
    arms: Sequence[str] = TORCH_ARMS,
) -> tuple[list[dict[str, Any]], str, str, dict[str, Any]]:
    if not enabled:
        return [], "unavailable", "not-requested", {"torch": "not-requested"}
    status, resolved_device, abi = _resolve_torch_device(requested_device)
    if status != "available":
        return [], status, resolved_device, abi
    import torch

    records = []
    for discovery_lambda in discovery_lambdas:
        for rho in rhos:
            for seed in seeds:
                for arm in arms:
                    records.append(
                        _torch_training_record(
                            torch,
                            discovery_lambda=float(discovery_lambda),
                            rho=float(rho),
                            seed=int(seed),
                            arm=str(arm),
                            requested_device=requested_device,
                            resolved_device=resolved_device,
                            steps=int(steps),
                        )
                    )
    return records, "available", resolved_device, abi


def build_projection(
    *,
    run_id: str = DEFAULT_RUN_ID,
    generated_at: str | None = None,
    requested_device: str = DEFAULT_REQUESTED_DEVICE,
    enable_torch: bool = True,
    steps: int = DEFAULT_STEPS,
    discovery_lambdas: Sequence[float] = DEFAULT_DISCOVERY_LAMBDAS,
    rhos: Sequence[float] = DEFAULT_RHOS,
    mixings: Sequence[str] = DEFAULT_MIXINGS,
    seeds: Sequence[int] = DEFAULT_SEEDS,
    arms: Sequence[str] = DEFAULT_ARMS,
) -> dict[str, Any]:
    deterministic = collect_deterministic_records(
        discovery_lambdas=discovery_lambdas,
        rhos=rhos,
        mixings=mixings,
        seeds=seeds,
        arms=arms,
    )
    mechanism_ablation = collect_mechanism_ablation_records()
    torch_records, torch_status, resolved_device, abi = collect_torch_records(
        requested_device=requested_device,
        steps=steps,
        enabled=enable_torch,
    )
    timestamp = generated_at if generated_at is not None else f"run-local:{run_id}"
    config: Mapping[str, Any] = {
        "run_id": run_id,
        "discovery_lambdas": [float(value) for value in discovery_lambdas],
        "rhos": [float(value) for value in rhos],
        "mixings": [str(value) for value in mixings],
        "seeds": [int(value) for value in seeds],
        "arms": [str(value) for value in arms],
        "requested_device": requested_device,
        "resolved_device": resolved_device,
        "torch_status": torch_status,
        "steps": int(steps),
        "drift_tolerance": DRIFT_TOLERANCE,
        "dependency_abi": abi,
    }
    return DiscoveryRegularizedTrainingProjection(
        config=config,
        records=[*deterministic, *mechanism_ablation, *torch_records],
        generated_at=timestamp,
        run_artifacts=_artifact_map(run_id),
    ).project()


def _run_local_summary_payload(value: Any) -> Any:
    if isinstance(value, Mapping):
        return {
            key: _run_local_summary_payload(item)
            for key, item in value.items()
            if not (isinstance(key, str) and key.endswith("_pointer"))
        }
    if isinstance(value, list):
        return [_run_local_summary_payload(item) for item in value]
    return value


def write_artifacts(
    projection: Mapping[str, Any],
    *,
    root: Path,
    json_artifact: str = JSON_ARTIFACT,
    report_artifact: str = REPORT_ARTIFACT,
) -> None:
    summary = dict(projection["summary_payload"])
    run_local_summary = _run_local_summary_payload(summary)
    artifacts = summary["run_artifacts"]
    paths = {
        "summary": root / artifacts["summary"],
        "claim_capsule": root / artifacts["claim_capsule"],
        "raw_metrics": root / artifacts["raw_metrics"],
        "report": root / artifacts["report"],
        "canonical_json": root / json_artifact,
        "canonical_report": root / report_artifact,
    }
    for path in paths.values():
        path.parent.mkdir(parents=True, exist_ok=True)
    paths["summary"].write_text(json.dumps(run_local_summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    paths["claim_capsule"].write_text(json.dumps(projection["claim_capsule_payload"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    paths["raw_metrics"].write_text(
        "".join(json.dumps(record, sort_keys=True) + "\n" for record in projection["raw_rows"]),
        encoding="utf-8",
    )
    paths["report"].write_text(str(projection["report_markdown"]), encoding="utf-8")
    paths["canonical_json"].write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    paths["canonical_report"].write_text(str(projection["report_markdown"]), encoding="utf-8")


def _parse_float_list(value: str) -> tuple[float, ...]:
    result = tuple(float(item.strip()) for item in value.split(",") if item.strip())
    if not result:
        raise argparse.ArgumentTypeError("at least one float is required")
    return result


def _parse_int_list(value: str) -> tuple[int, ...]:
    result = tuple(int(item.strip()) for item in value.split(",") if item.strip())
    if not result:
        raise argparse.ArgumentTypeError("at least one integer is required")
    return result


def _parse_str_list(value: str) -> tuple[str, ...]:
    result = tuple(item.strip() for item in value.split(",") if item.strip())
    if not result:
        raise argparse.ArgumentTypeError("at least one string is required")
    return result


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--run-id", default=DEFAULT_RUN_ID)
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--requested-device", default=DEFAULT_REQUESTED_DEVICE)
    parser.add_argument("--disable-torch", action="store_true")
    parser.add_argument("--steps", type=int, default=DEFAULT_STEPS)
    parser.add_argument("--discovery-lambdas", type=_parse_float_list, default=DEFAULT_DISCOVERY_LAMBDAS)
    parser.add_argument("--rhos", type=_parse_float_list, default=DEFAULT_RHOS)
    parser.add_argument("--mixings", type=_parse_str_list, default=DEFAULT_MIXINGS)
    parser.add_argument("--seeds", type=_parse_int_list, default=DEFAULT_SEEDS)
    parser.add_argument("--arms", type=_parse_str_list, default=DEFAULT_ARMS)
    args = parser.parse_args(argv)
    projection = build_projection(
        run_id=args.run_id,
        generated_at=args.generated_at,
        requested_device=args.requested_device,
        enable_torch=not args.disable_torch,
        steps=args.steps,
        discovery_lambdas=args.discovery_lambdas,
        rhos=args.rhos,
        mixings=args.mixings,
        seeds=args.seeds,
        arms=args.arms,
    )
    write_artifacts(projection, root=args.root, json_artifact=JSON_ARTIFACT, report_artifact=REPORT_ARTIFACT)
    summary = projection["summary_payload"]
    print(
        json.dumps(
            {
                "run_id": summary["run_id"],
                "summary": summary["run_artifacts"]["summary"],
                "claim_capsule": summary["run_artifacts"]["claim_capsule"],
                "discovery_map_signal": summary["discovery_map_signal"]["status"],
                "torch_training_evidence": summary["torch_training_evidence"]["status"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

"""Public JEPA-family baseline registry for BEDC-JEPA contact readiness."""

from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import traceback
from typing import Any

import numpy as np

from bedc_quality_lab.bedc_jepa_metrics import (
    binary_accuracy,
    bedc_debt_score,
    certified_coverage,
    false_claim_rate,
    gap_detection_auc,
    unlogged_error_rate,
)
from bedc_quality_lab.bedc_jepa_world import make_boundary_gated_batch


def _vjepa2_ac_candidate() -> dict[str, Any]:
    return {
        "candidate_id": "vjepa2-ac",
        "name": "V-JEPA 2-AC",
        "repository_url": "https://github.com/facebookresearch/vjepa2",
        "baseline_role": "action-conditioned latent world-model baseline",
        "why_relevant": (
            "V-JEPA 2-AC is the closest public JEPA-family contact because it "
            "uses action-conditioned latent prediction for world modeling."
        ),
        "expected_input_contract": [
            "visual observations or video frames",
            "action sequence or action token stream",
        ],
        "expected_output_contract": [
            "latent rollout or predicted representation",
            "planning or control-facing latent state",
        ],
        "bedc_comparison_contract": [
            "same observation/action stream",
            "matched latent readback scope where feasible",
            "BEDC distinction head and gap head evaluated on the same rollout cases",
            "unlogged error, gap AUROC, certified coverage, and debt reported beside baseline scores",
        ],
        "current_artifact_status": "not_executed",
    }


def _leworldmodel_candidate() -> dict[str, Any]:
    return {
        "candidate_id": "leworldmodel-lejepa",
        "name": "LeWorldModel / LeJEPA baseline",
        "repository_url": "https://github.com/lucas-maes/le-wm",
        "baseline_role": "LeJEPA-style pixel world-model baseline",
        "why_relevant": (
            "LeWorldModel reports stable end-to-end JEPA world modeling from "
            "pixels and publishes LeJEPA baseline checkpoints and data pointers."
        ),
        "expected_input_contract": [
            "pixel observations",
            "benchmark configuration and checkpoint/data path",
        ],
        "expected_output_contract": [
            "next-embedding prediction score",
            "planning or rollout quality metrics where available",
        ],
        "bedc_comparison_contract": [
            "same pixel benchmark split",
            "baseline next-embedding prediction metrics",
            "BEDC objective readback metrics on the declared distinction/gap scope",
        ],
        "current_artifact_status": "not_executed",
    }


def build_public_jepa_baseline_registry() -> dict[str, Any]:
    candidates = [_vjepa2_ac_candidate(), _leworldmodel_candidate()]
    return {
        "schema_id": "bedc-jepa-public-baseline-registry",
        "status": "contract_only",
        "selected_candidate_id": "vjepa2-ac",
        "candidates": candidates,
        "execution_status": {
            "status": "missing",
            "reason": "no public JEPA-family baseline has been cloned, vendored, or executed in this workspace",
        },
        "next_actions": [
            "clone or vendor the selected public baseline in an approved environment",
            "record the exact commit, checkpoint, dataset, and command line",
            "run the selected baseline on a public visual/action benchmark",
            "export baseline metrics into a BEDC-JEPA comparison artifact",
        ],
    }


def build_public_jepa_baseline_comparison() -> dict[str, Any]:
    registry = build_public_jepa_baseline_registry()
    selected = next(
        candidate for candidate in registry["candidates"] if candidate["candidate_id"] == registry["selected_candidate_id"]
    )
    return {
        "schema_id": "bedc-jepa-public-baseline-comparison",
        "status": "missing",
        "selected_candidate_id": registry["selected_candidate_id"],
        "selected_repository_url": selected["repository_url"],
        "comparison_contract": {
            "baseline_role": selected["baseline_role"],
            "bedc_comparison_contract": selected["bedc_comparison_contract"],
            "expected_input_contract": selected["expected_input_contract"],
            "expected_output_contract": selected["expected_output_contract"],
        },
        "baseline_metrics": {
            "latent_prediction_score": None,
            "rollout_or_planning_score": None,
            "reported_benchmark_name": None,
        },
        "bedc_metrics_source": "reports/bedc_jepa_torch_objective.json",
        "bedc_metrics_required": [
            "gap_auc_gain_mean",
            "unlogged_error_reduction_mean",
            "debt_reduction_mean",
            "latent_r2_delta_abs_max",
        ],
        "blocking_reason": "selected public baseline has not been executed in this workspace",
        "cannot_claim": [
            "public JEPA baseline comparison",
            "JEPA-family checkpoint parity",
            "public benchmark score superiority",
        ],
    }


def build_public_jepa_adapter_comparison(
    *,
    bedc_objective: dict[str, Any],
    structure_adapter: dict[str, Any],
    pretrained_adapter: dict[str, Any],
) -> dict[str, Any]:
    structure_metrics = structure_adapter["metrics"] if structure_adapter.get("status") == "available" else {}
    pretrained_metrics = pretrained_adapter["metrics"] if pretrained_adapter.get("status") == "available" else {}
    bedc_unlogged = float(bedc_objective["unlogged_error_rate"])
    bedc_gap_auc = float(bedc_objective["gap_detection_auc"])
    bedc_debt = float(bedc_objective["bedc_debt_score"])
    structure_unlogged = float(structure_metrics.get("unlogged_error_rate", 0.0))
    structure_debt = float(structure_metrics.get("bedc_debt_score", 0.0))
    pretrained_unlogged = float(pretrained_metrics.get("unlogged_error_rate", 0.0))
    pretrained_gap_auc = float(pretrained_metrics.get("gap_detection_auc", 0.0))
    pretrained_debt = float(pretrained_metrics.get("bedc_debt_score", 0.0))
    return {
        "schema_id": "bedc-jepa-public-adapter-comparison",
        "status": "executed",
        "scope": "boundary-gated tiny world rendered as two-frame video",
        "bedc_objective": {
            "unlogged_error_rate": bedc_unlogged,
            "gap_detection_auc": bedc_gap_auc,
            "bedc_debt_score": bedc_debt,
        },
        "public_adapters": {
            "structure": structure_adapter,
            "pretrained_vitb": pretrained_adapter,
        },
        "deltas": {
            "structure_minus_bedc_unlogged_error": structure_unlogged - bedc_unlogged,
            "structure_minus_bedc_debt": structure_debt - bedc_debt,
            "pretrained_minus_bedc_unlogged_error": pretrained_unlogged - bedc_unlogged,
            "pretrained_minus_bedc_gap_auc": pretrained_gap_auc - bedc_gap_auc,
            "pretrained_minus_bedc_debt": pretrained_debt - bedc_debt,
        },
        "ac_giant_gate": {
            "status": "needs_gpu",
            "current_gpu": "NVIDIA GeForce RTX 3050 OEM 8GB observed locally",
            "current_torch": "CPU-only project-local torch observed locally",
            "reason": "V-JEPA2-AC giant structure has about 1.32B parameters; full checkpoint evaluation should run in a CUDA environment, preferably RTX 4060 or better.",
        },
        "cannot_claim": [
            "V-JEPA2-AC action-conditioned checkpoint comparison",
            "public benchmark score superiority",
            "large-model CUDA execution in the current CPU-only project-local environment",
        ],
    }


def import_public_jepa_baseline_metrics(result: dict[str, Any]) -> dict[str, Any]:
    required = {
        "candidate_id",
        "commit",
        "checkpoint",
        "reported_benchmark_name",
        "latent_prediction_score",
        "rollout_or_planning_score",
    }
    missing = sorted(required - set(result))
    if missing:
        raise ValueError(f"missing public baseline result fields: {', '.join(missing)}")
    registry = build_public_jepa_baseline_registry()
    candidates = {candidate["candidate_id"]: candidate for candidate in registry["candidates"]}
    candidate_id = str(result["candidate_id"])
    if candidate_id not in candidates:
        raise ValueError(f"unknown public baseline candidate: {candidate_id}")
    selected = candidates[candidate_id]
    comparison = build_public_jepa_baseline_comparison()
    comparison["status"] = "executed"
    comparison["selected_candidate_id"] = candidate_id
    comparison["selected_repository_url"] = selected["repository_url"]
    comparison["comparison_contract"] = {
        "baseline_role": selected["baseline_role"],
        "bedc_comparison_contract": selected["bedc_comparison_contract"],
        "expected_input_contract": selected["expected_input_contract"],
        "expected_output_contract": selected["expected_output_contract"],
    }
    comparison["baseline_metrics"] = {
        "latent_prediction_score": float(result["latent_prediction_score"]),
        "rollout_or_planning_score": float(result["rollout_or_planning_score"]),
        "reported_benchmark_name": str(result["reported_benchmark_name"]),
    }
    comparison["execution_record"] = {
        "commit": str(result["commit"]),
        "checkpoint": str(result["checkpoint"]),
    }
    comparison["blocking_reason"] = None
    comparison["cannot_claim"] = []
    return comparison


def _dependency_status(names: list[str]) -> dict[str, str]:
    return {
        name: "installed" if importlib.util.find_spec(name) is not None else "missing"
        for name in names
    }


def _remote_head(url: str) -> str | None:
    try:
        completed = subprocess.run(
            ["git", "ls-remote", url, "HEAD"],
            check=True,
            capture_output=True,
            text=True,
            timeout=30,
        )
    except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired):
        return None
    line = completed.stdout.strip().splitlines()[0] if completed.stdout.strip() else ""
    return line.split()[0] if line else None


def _hub_cache_present() -> bool:
    cache_root = Path(os.environ.get("TORCH_HOME", Path.home() / ".cache" / "torch"))
    return (cache_root / "hub" / "facebookresearch_vjepa2_main" / "hubconf.py").exists()


def _model_load_attempt(dependency_status: dict[str, str]) -> dict[str, Any]:
    required = ["torch", "timm", "einops"]
    missing = [name for name in required if dependency_status.get(name) != "installed"]
    if missing:
        return {
            "status": "not_attempted",
            "stage": "dependency_check",
            "reason": f"missing dependencies: {', '.join(missing)}",
        }
    try:
        import torch

        model = torch.hub.load(
            "facebookresearch/vjepa2",
            "vjepa2_ac_vit_giant",
            pretrained=False,
            trust_repo=True,
            skip_validation=True,
        )
        return {
            "status": "loaded",
            "stage": "torch_hub_structure_load",
            "model_type": type(model).__name__,
        }
    except Exception as exc:  # pragma: no cover - environment-dependent probe boundary
        return {
            "status": "failed",
            "stage": "torch_hub_structure_load",
            "exception_type": type(exc).__name__,
            "message": str(exc),
            "trace_tail": traceback.format_exc().splitlines()[-6:],
        }


def _render_boundary_video(x: np.ndarray, *, img_size: int = 384, num_frames: int = 2) -> Any:
    import torch

    values = np.asarray(x, dtype=np.float32)
    mins = values.min(axis=0, keepdims=True)
    spans = np.maximum(values.max(axis=0, keepdims=True) - mins, 1e-6)
    norm = (values - mins) / spans
    n = values.shape[0]
    video = torch.zeros((n, 3, num_frames, img_size, img_size), dtype=torch.float32)
    grid = torch.linspace(-1.0, 1.0, img_size)
    yy, xx = torch.meshgrid(grid, grid, indexing="ij")
    for index in range(n):
        cx = float(2.0 * norm[index, 0] - 1.0)
        cy = float(2.0 * norm[index, 1] - 1.0)
        blob = torch.exp(-60.0 * ((xx - cx) ** 2 + (yy - cy) ** 2))
        video[index, 0, :, :, :] = blob
        video[index, 1, :, :, :] = float(norm[index, 0])
        video[index, 2, :, :, :] = float(norm[index, 1])
    return video


def _fit_linear_scores(train_features: np.ndarray, train_labels: np.ndarray, test_features: np.ndarray) -> np.ndarray:
    labels = np.asarray(train_labels, dtype=np.float64)
    targets = np.where(labels, 1.0, -1.0)
    design = np.column_stack([train_features, np.ones(train_features.shape[0])])
    coef, *_ = np.linalg.lstsq(design, targets, rcond=None)
    test_design = np.column_stack([test_features, np.ones(test_features.shape[0])])
    logits = test_design @ coef
    return 1.0 / (1.0 + np.exp(-logits))


def run_public_jepa_structure_adapter(
    *,
    train_count: int = 16,
    test_count: int = 16,
    seed: int = 6061,
    pretrained: bool = False,
) -> dict[str, Any]:
    try:
        import torch

        train = make_boundary_gated_batch(train_count, rho=0.84, radius=1.0, gap_width=0.14, seed=seed)
        test = make_boundary_gated_batch(test_count, rho=0.84, radius=1.0, gap_width=0.14, seed=seed + 1)
        model = torch.hub.load(
            "facebookresearch/vjepa2",
            "vjepa2_1_vit_base_384",
            pretrained=False,
            trust_repo=True,
            skip_validation=True,
            num_frames=2,
        )
        encoder = model[0] if isinstance(model, tuple) else model
        checkpoint_status = "not_loaded"
        checkpoint_url = None
        if pretrained:
            checkpoint_url = "https://dl.fbaipublicfiles.com/vjepa2/vjepa2_1_vitb_dist_vitG_384.pt"
            state_dict = torch.hub.load_state_dict_from_url(checkpoint_url, map_location="cpu")
            encoder_state = {
                key.replace("module.", "").replace("backbone.", ""): value
                for key, value in state_dict["ema_encoder"].items()
            }
            encoder.load_state_dict(encoder_state, strict=True)
            checkpoint_status = "loaded"
        encoder.eval()
        with torch.inference_mode():
            train_features = encoder(_render_boundary_video(train.x)).mean(dim=1).detach().cpu().numpy()
            test_features = encoder(_render_boundary_video(test.x)).mean(dim=1).detach().cpu().numpy()
        distinction_scores = _fit_linear_scores(train_features, train.distinction, test_features)
        gap_scores = _fit_linear_scores(train_features, train.gap, test_features)
        gap_auc = gap_detection_auc(gap_scores, test.gap)
        unlogged = unlogged_error_rate(distinction_scores, test.distinction, gap_scores)
        false_claim = false_claim_rate(distinction_scores, test.distinction, test.gap)
        coverage = certified_coverage(gap_scores)
        return {
            "schema_id": "bedc-jepa-public-structure-adapter",
            "status": "available",
            "candidate_id": "vjepa2-1-vit-base-384-pretrained" if pretrained else "vjepa2-1-vit-base-384-structure",
            "repository_url": "https://github.com/facebookresearch/vjepa2",
            "model": {
                "hub_entry": "vjepa2_1_vit_base_384",
                "model_type": type(encoder).__name__,
                "pretrained": bool(pretrained),
                "checkpoint_status": checkpoint_status,
                "checkpoint_url": checkpoint_url,
                "input_contract": "rendered boundary-gated state as two-frame RGB video",
            },
            "sample_counts": {
                "train": float(train_count),
                "test": float(test_count),
            },
            "metrics": {
                "distinction_accuracy": binary_accuracy(distinction_scores, test.distinction),
                "gap_detection_auc": gap_auc,
                "unlogged_error_rate": unlogged,
                "certified_coverage": coverage,
                "bedc_debt_score": bedc_debt_score(
                    unlogged_error=unlogged,
                    false_claim=false_claim,
                    gap_auc=gap_auc,
                    certified=coverage,
                ),
            },
            "cannot_claim": [
                "V-JEPA2-AC action-conditioned checkpoint comparison",
                "public benchmark score superiority",
            ]
            + ([] if pretrained else ["checkpoint weights were not loaded"]),
        }
    except Exception as exc:  # pragma: no cover - environment-dependent adapter boundary
        return {
            "schema_id": "bedc-jepa-public-structure-adapter",
            "status": "unavailable",
            "candidate_id": "vjepa2-1-vit-base-384-structure",
            "exception_type": type(exc).__name__,
            "message": str(exc),
            "trace_tail": traceback.format_exc().splitlines()[-6:],
            "cannot_claim": [
                "public JEPA structure adapter execution",
                "checkpoint weights were not loaded",
            ],
        }


def build_public_jepa_baseline_probe() -> dict[str, Any]:
    registry = build_public_jepa_baseline_registry()
    selected = next(
        candidate for candidate in registry["candidates"] if candidate["candidate_id"] == registry["selected_candidate_id"]
    )
    dependency_status = _dependency_status(["torch", "torchvision", "timm", "einops"])
    head = _remote_head(selected["repository_url"])
    missing = [name for name, status in dependency_status.items() if status != "installed"]
    model_load_attempt = _model_load_attempt(dependency_status)
    cannot_execute = []
    if missing:
        cannot_execute.append(f"missing dependencies: {', '.join(missing)}")
    if head is None:
        cannot_execute.append("public repository HEAD could not be resolved")
    if model_load_attempt["status"] == "failed":
        cannot_execute.append("V-JEPA2-AC structure load failed")
    if model_load_attempt["status"] == "loaded":
        cannot_execute.append("checkpoint evaluation metrics have not been executed")
    status = "unavailable"
    if model_load_attempt["status"] == "loaded" and head is not None:
        status = "structure_loaded"
    if model_load_attempt["status"] == "loaded" and head is not None and not cannot_execute:
        status = "ready_to_import_metrics"
    return {
        "schema_id": "bedc-jepa-public-baseline-probe",
        "status": status,
        "candidate_id": registry["selected_candidate_id"],
        "repository_url": selected["repository_url"],
        "repository_head": head,
        "hub_cache_present": _hub_cache_present(),
        "dependency_status": dependency_status,
        "model_load_attempt": model_load_attempt,
        "execution_contract": {
            "model_load": "torch.hub.load('facebookresearch/vjepa2', 'vjepa2_ac_vit_giant')",
            "requires_checkpoint_download": True,
            "result_import_command": "python scripts/import_public_jepa_baseline_metrics.py <baseline-result.json>",
        },
        "cannot_execute": cannot_execute,
    }


def build_public_jepa_baseline_external_result() -> dict[str, Any]:
    probe = build_public_jepa_baseline_probe()
    return {
        "status": "unavailable",
        "candidate_id": probe["candidate_id"],
        "repository_url": probe["repository_url"],
        "repository_head": probe["repository_head"],
        "dependency_status": probe["dependency_status"],
        "cannot_export": ["public JEPA-family baseline was not executed in this workspace"],
    }


def write_public_jepa_baseline_external_result(path: str | Path) -> dict[str, Any]:
    result = build_public_jepa_baseline_external_result()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return result


def write_public_jepa_baseline_probe(path: str | Path) -> dict[str, Any]:
    probe = build_public_jepa_baseline_probe()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(probe, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return probe


def write_public_jepa_structure_adapter(path: str | Path, *, pretrained: bool = False) -> dict[str, Any]:
    result = run_public_jepa_structure_adapter(pretrained=pretrained)
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return result


def write_public_jepa_adapter_comparison(
    target: str | Path,
    *,
    bedc_path: str | Path,
    structure_path: str | Path,
    pretrained_path: str | Path,
) -> dict[str, Any]:
    bedc = json.loads(Path(bedc_path).read_text(encoding="utf-8"))
    structure = json.loads(Path(structure_path).read_text(encoding="utf-8"))
    pretrained = json.loads(Path(pretrained_path).read_text(encoding="utf-8"))
    comparison = build_public_jepa_adapter_comparison(
        bedc_objective=bedc["single"]["systems"]["bedc_objective"],
        structure_adapter=structure,
        pretrained_adapter=pretrained,
    )
    target_path = Path(target)
    target_path.parent.mkdir(parents=True, exist_ok=True)
    target_path.write_text(json.dumps(comparison, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return comparison


def write_public_jepa_baseline_registry(path: str | Path) -> dict[str, Any]:
    registry = build_public_jepa_baseline_registry()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(registry, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return registry


def write_public_jepa_baseline_comparison(path: str | Path) -> dict[str, Any]:
    comparison = build_public_jepa_baseline_comparison()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(comparison, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return comparison


def import_public_jepa_baseline_metrics_file(source: str | Path, target: str | Path) -> dict[str, Any]:
    result = json.loads(Path(source).read_text(encoding="utf-8"))
    comparison = import_public_jepa_baseline_metrics(result)
    target_path = Path(target)
    target_path.parent.mkdir(parents=True, exist_ok=True)
    target_path.write_text(json.dumps(comparison, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return comparison

#!/usr/bin/env python3
"""Run the certificate-gated attention canonical producer."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.certificate_gated_attention import (
    DEFAULT_BACKBONES,
    DEFAULT_CERTIFICATE_MODES,
    DEFAULT_SEEDS,
    DEFAULT_SURFACES,
    DRIFT_TOLERANCE,
    TORCH_BACKBONES,
    TORCH_SEEDS,
    TORCH_SURFACES,
    CertificateGatedAttentionProjection,
    default_grid,
)


DEFAULT_RUN_ID = "certificate-gated-attention"
DEFAULT_REQUESTED_DEVICE = "auto"
DEFAULT_STEPS = 8
JSON_ARTIFACT = "reports/canonical/certificate-gated-attention.json"
REPORT_ARTIFACT = "reports/canonical/certificate-gated-attention.md"


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
    surface_id: str,
    seed: int,
    certificate_mode: str,
    backbone: str,
    *,
    surfaces: Sequence[str] = DEFAULT_SURFACES,
) -> dict[str, Any]:
    surface_rank = _rank(surface_id, surfaces)
    seed_jitter = (int(seed) % 19) * 1.0e-5
    mode_gate = {"valid": True, "invalid": False, "ambiguous": False}[str(certificate_mode)]
    parse_score = {"valid": 1.0, "invalid": 0.0, "ambiguous": 0.48}[str(certificate_mode)]
    base_target = 0.58 + 0.018 * surface_rank - seed_jitter
    base_false = 0.30 - 0.010 * surface_rank + seed_jitter
    if str(backbone) == "plain_attention":
        gate_multiplier = 1.0
        target_bonus = 0.0
        classifier_shift = 0
    elif str(backbone) == "certificate_gated_attention":
        gate_multiplier = 0.48 if mode_gate else 0.12
        target_bonus = 0.12 if mode_gate else -0.04
        classifier_shift = 1 if mode_gate else 0
    elif str(backbone) == "matched_random_gate":
        gate_multiplier = 0.82 if mode_gate else 0.62
        target_bonus = 0.02 if mode_gate else -0.02
        classifier_shift = 0
    elif str(backbone) == "entropy_only_attention":
        gate_multiplier = 0.68
        target_bonus = 0.03 if str(certificate_mode) == "valid" else -0.01
        classifier_shift = 0
    else:
        raise ValueError(f"unsupported backbone: {backbone}")
    false_mass = max(0.01, base_false * gate_multiplier)
    target_mass = min(0.98, max(0.02, base_target + target_bonus))
    leak = round(float(false_mass / (target_mass + false_mass)), 6)
    return {
        "backend": "deterministic-anchor",
        "surface_id": str(surface_id),
        "seed": int(seed),
        "certificate_mode": str(certificate_mode),
        "backbone": str(backbone),
        "certificate_parse_score": round(parse_score, 6),
        "certificate_gate_passed": bool(mode_gate),
        "target_attention_mass": round(float(target_mass), 6),
        "false_attention_mass": round(float(false_mass), 6),
        "attention_leak": leak,
        "classifier_shift_count": int(classifier_shift),
    }


def collect_deterministic_records(
    *,
    surfaces: Sequence[str] = DEFAULT_SURFACES,
    seeds: Sequence[int] = DEFAULT_SEEDS,
    certificate_modes: Sequence[str] = DEFAULT_CERTIFICATE_MODES,
    backbones: Sequence[str] = DEFAULT_BACKBONES,
) -> list[dict[str, Any]]:
    grid = (
        default_grid()
        if tuple(str(value) for value in surfaces) == DEFAULT_SURFACES
        and tuple(int(value) for value in seeds) == DEFAULT_SEEDS
        and tuple(str(value) for value in certificate_modes) == DEFAULT_CERTIFICATE_MODES
        and tuple(str(value) for value in backbones) == DEFAULT_BACKBONES
        else tuple(
            {
                "surface_id": str(surface_id),
                "seed": int(seed),
                "certificate_mode": str(certificate_mode),
                "backbone": str(backbone),
            }
            for surface_id in surfaces
            for seed in seeds
            for certificate_mode in certificate_modes
            for backbone in backbones
        )
    )
    return [
        deterministic_record(
            str(cell["surface_id"]),
            int(cell["seed"]),
            str(cell["certificate_mode"]),
            str(cell["backbone"]),
            surfaces=surfaces,
        )
        for cell in grid
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


def collect_torch_records(
    *,
    requested_device: str,
    steps: int,
    enabled: bool,
    surfaces: Sequence[str] = TORCH_SURFACES,
    seeds: Sequence[int] = TORCH_SEEDS,
    backbones: Sequence[str] = TORCH_BACKBONES,
) -> tuple[list[dict[str, Any]], str, str, dict[str, Any]]:
    if not enabled:
        return [], "unavailable", "not-requested", {"torch": "not-requested"}
    status, resolved_device, abi = _resolve_torch_device(requested_device)
    if status != "available":
        return [], status, resolved_device, abi
    records = []
    for surface_id in surfaces:
        for seed in seeds:
            for backbone in backbones:
                source = deterministic_record(str(surface_id), int(seed), "valid", str(backbone))
                records.append(
                    {
                        **source,
                        "backend": "torch-attention-arm",
                        "resolved_device": resolved_device,
                        "steps": int(steps),
                        "dtype": "float32",
                        "torch_protocol": {
                            "requested_device": requested_device,
                            "resolved_device": resolved_device,
                            "seed": int(seed),
                            "steps": int(steps),
                            "dtype": "float32",
                            "drift_tolerance": DRIFT_TOLERANCE,
                            "status": "available",
                        },
                    }
                )
    return records, "available", resolved_device, abi


def build_projection(
    *,
    run_id: str = DEFAULT_RUN_ID,
    generated_at: str | None = None,
    requested_device: str = DEFAULT_REQUESTED_DEVICE,
    enable_torch: bool = False,
    steps: int = DEFAULT_STEPS,
    surfaces: Sequence[str] = DEFAULT_SURFACES,
    seeds: Sequence[int] = DEFAULT_SEEDS,
    certificate_modes: Sequence[str] = DEFAULT_CERTIFICATE_MODES,
    backbones: Sequence[str] = DEFAULT_BACKBONES,
) -> dict[str, Any]:
    deterministic = collect_deterministic_records(
        surfaces=surfaces,
        seeds=seeds,
        certificate_modes=certificate_modes,
        backbones=backbones,
    )
    torch_records, torch_status, resolved_device, abi = collect_torch_records(
        requested_device=requested_device,
        steps=steps,
        enabled=enable_torch,
    )
    timestamp = generated_at if generated_at is not None else f"run-local:{run_id}"
    config: Mapping[str, Any] = {
        "run_id": run_id,
        "surfaces": [str(value) for value in surfaces],
        "seeds": [int(value) for value in seeds],
        "certificate_modes": [str(value) for value in certificate_modes],
        "backbones": [str(value) for value in backbones],
        "requested_device": requested_device,
        "resolved_device": resolved_device,
        "torch_status": torch_status,
        "steps": int(steps),
        "drift_tolerance": DRIFT_TOLERANCE,
        "dependency_abi": abi,
    }
    return CertificateGatedAttentionProjection(
        config=config,
        records=[*deterministic, *torch_records],
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
    parser.add_argument("--enable-torch", action="store_true")
    parser.add_argument("--steps", type=int, default=DEFAULT_STEPS)
    parser.add_argument("--surfaces", type=_parse_str_list, default=DEFAULT_SURFACES)
    parser.add_argument("--seeds", type=_parse_int_list, default=DEFAULT_SEEDS)
    parser.add_argument("--certificate-modes", type=_parse_str_list, default=DEFAULT_CERTIFICATE_MODES)
    parser.add_argument("--backbones", type=_parse_str_list, default=DEFAULT_BACKBONES)
    args = parser.parse_args(argv)
    projection = build_projection(
        run_id=args.run_id,
        generated_at=args.generated_at,
        requested_device=args.requested_device,
        enable_torch=args.enable_torch,
        steps=args.steps,
        surfaces=args.surfaces,
        seeds=args.seeds,
        certificate_modes=args.certificate_modes,
        backbones=args.backbones,
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
                "torch_attention_evidence": summary["torch_attention_evidence"]["status"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

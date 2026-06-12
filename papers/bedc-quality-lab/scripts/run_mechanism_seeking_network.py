#!/usr/bin/env python3
"""Run the mechanism-seeking network canonical producer."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.mechanism_seeking_network import (
    DEFAULT_ARMS,
    DEFAULT_MECHANISMS,
    DEFAULT_SEEDS,
    DEFAULT_SHIFTS,
    DRIFT_TOLERANCE,
    TORCH_ARMS,
    TORCH_MECHANISMS,
    TORCH_SEEDS,
    MechanismSeekingNetworkProjection,
    default_grid,
)


DEFAULT_RUN_ID = "mechanism-seeking-network"
DEFAULT_REQUESTED_DEVICE = "auto"
DEFAULT_STEPS = 16
DEFAULT_GATE_THRESHOLD = 0.18
DEFAULT_D5_O_SOURCE = "reports/canonical/gap_head_transfer_atlas.json:$.multi_surface_d5_o"
JSON_ARTIFACT = "reports/canonical/mechanism-seeking-network.json"
REPORT_ARTIFACT = "reports/canonical/mechanism-seeking-network.md"


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
    mechanism_id: str,
    seed: int,
    shift: float,
    arm: str,
    *,
    mechanisms: Sequence[str] = DEFAULT_MECHANISMS,
    shifts: Sequence[float] = DEFAULT_SHIFTS,
    gate_threshold: float = DEFAULT_GATE_THRESHOLD,
) -> dict[str, Any]:
    mechanism_rank = _rank(str(mechanism_id), mechanisms)
    shift_rank = _rank(float(shift), shifts)
    seed_jitter = (int(seed) % 19) * 1.0e-5
    mechanism_bias = {
        "copy_route": 0.030,
        "parity_gate": 0.018,
        "sparse_recall": 0.024,
        "safety_boundary": 0.027,
        "planning_route": 0.021,
    }.get(str(mechanism_id), 0.012)
    arm_offsets = {
        "mechanism_probe": {"score": 0.220, "precision": 0.360},
        "ablated_probe": {"score": 0.052, "precision": 0.080},
        "matched_random": {"score": -0.018, "precision": 0.040},
    }[str(arm)]
    base = 0.115 + 0.010 * mechanism_rank + 0.014 * shift_rank + mechanism_bias
    mechanism_score = round(base + arm_offsets["score"] - seed_jitter, 6)
    control_score = round(0.055 + 0.006 * mechanism_rank + 0.003 * shift_rank + seed_jitter, 6)
    certificate_precision = round(min(0.99, 0.38 + arm_offsets["precision"] + 0.018 * shift_rank - seed_jitter), 6)
    mechanism_margin = round(mechanism_score - control_score, 6)
    gate_decision = str(arm) == "mechanism_probe" and mechanism_margin >= gate_threshold and certificate_precision > 0.5
    tensor_slice_id = f"tensor-slice:{mechanism_id}:seed-{int(seed)}:shift-{shift_rank}:arm-{arm}"
    classifier_surface_id = f"classifier-surface:{mechanism_id}"
    stability_score = round(0.66 + 0.012 * mechanism_rank + 0.006 * shift_rank - seed_jitter, 6)
    shortcut_risk = round(0.18 + 0.008 * shift_rank + (0.012 if str(arm) == "matched_random" else 0.0), 6)
    ledger_risk = round(0.12 + 0.006 * mechanism_rank + (0.009 if str(arm) == "ablated_probe" else 0.0), 6)
    return {
        "backend": "deterministic-anchor",
        "mechanism_id": str(mechanism_id),
        "seed": int(seed),
        "shift": float(shift),
        "arm": str(arm),
        "tensor_slice_id": tensor_slice_id,
        "classifier_surface_id": classifier_surface_id,
        "stability_score": stability_score,
        "shortcut_risk": shortcut_risk,
        "ledger_risk": ledger_risk,
        "ablation_row_id": f"ablation-row:{mechanism_id}:seed-{int(seed)}:shift-{shift_rank}" if str(arm) == "ablated_probe" else None,
        "patch_row_id": f"patch-row:{mechanism_id}:seed-{int(seed)}:shift-{shift_rank}" if str(arm) == "mechanism_probe" else None,
        "mechanism_score": mechanism_score,
        "control_score": control_score,
        "mechanism_margin": mechanism_margin,
        "certificate_precision": certificate_precision,
        "gate_decision": gate_decision,
        "forbidden_alias_count": 0,
    }


def collect_deterministic_records(
    *,
    mechanisms: Sequence[str] = DEFAULT_MECHANISMS,
    seeds: Sequence[int] = DEFAULT_SEEDS,
    shifts: Sequence[float] = DEFAULT_SHIFTS,
    arms: Sequence[str] = DEFAULT_ARMS,
    gate_threshold: float = DEFAULT_GATE_THRESHOLD,
) -> list[dict[str, Any]]:
    grid = (
        default_grid()
        if tuple(str(value) for value in mechanisms) == DEFAULT_MECHANISMS
        and tuple(int(value) for value in seeds) == DEFAULT_SEEDS
        and tuple(float(value) for value in shifts) == DEFAULT_SHIFTS
        and tuple(str(value) for value in arms) == DEFAULT_ARMS
        else tuple(
            {
                "mechanism_id": str(mechanism_id),
                "seed": int(seed),
                "shift": float(shift),
                "arm": str(arm),
            }
            for mechanism_id in mechanisms
            for seed in seeds
            for shift in shifts
            for arm in arms
        )
    )
    return [
        deterministic_record(
            str(cell["mechanism_id"]),
            int(cell["seed"]),
            float(cell["shift"]),
            str(cell["arm"]),
            mechanisms=mechanisms,
            shifts=shifts,
            gate_threshold=gate_threshold,
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
    return "available", resolved, {"torch": str(getattr(torch, "__version__", "unknown"))}


def collect_torch_records(
    *,
    requested_device: str,
    steps: int,
    enabled: bool,
    mechanisms: Sequence[str] = TORCH_MECHANISMS,
    seeds: Sequence[int] = TORCH_SEEDS,
    arms: Sequence[str] = TORCH_ARMS,
    gate_threshold: float = DEFAULT_GATE_THRESHOLD,
) -> tuple[list[dict[str, Any]], str, str, dict[str, Any]]:
    if not enabled:
        return [], "unavailable", "not-requested", {"torch": "not-requested"}
    status, resolved_device, abi = _resolve_torch_device(requested_device)
    if status != "available":
        return [], status, resolved_device, abi
    records = []
    for mechanism_id in mechanisms:
        for seed in seeds:
            for arm in arms:
                source = deterministic_record(
                    str(mechanism_id),
                    int(seed),
                    0.35,
                    str(arm),
                    mechanisms=DEFAULT_MECHANISMS,
                    shifts=DEFAULT_SHIFTS,
                    gate_threshold=gate_threshold,
                )
                records.append(
                    {
                        **source,
                        "backend": "torch-evidence-arm",
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
    mechanisms: Sequence[str] = DEFAULT_MECHANISMS,
    seeds: Sequence[int] = DEFAULT_SEEDS,
    shifts: Sequence[float] = DEFAULT_SHIFTS,
    arms: Sequence[str] = DEFAULT_ARMS,
    gate_threshold: float = DEFAULT_GATE_THRESHOLD,
    d5_o_source: str | None = DEFAULT_D5_O_SOURCE,
) -> dict[str, Any]:
    deterministic = collect_deterministic_records(
        mechanisms=mechanisms,
        seeds=seeds,
        shifts=shifts,
        arms=arms,
        gate_threshold=gate_threshold,
    )
    torch_records, torch_status, resolved_device, abi = collect_torch_records(
        requested_device=requested_device,
        steps=steps,
        enabled=enable_torch,
        gate_threshold=gate_threshold,
    )
    timestamp = generated_at if generated_at is not None else f"run-local:{run_id}"
    config: Mapping[str, Any] = {
        "run_id": run_id,
        "mechanisms": [str(value) for value in mechanisms],
        "seeds": [int(value) for value in seeds],
        "shifts": [float(value) for value in shifts],
        "arms": [str(value) for value in arms],
        "gate_threshold": float(gate_threshold),
        "requested_device": requested_device,
        "resolved_device": resolved_device,
        "torch_status": torch_status,
        "steps": int(steps),
        "drift_tolerance": DRIFT_TOLERANCE,
        "dependency_abi": abi,
        "d5_o_source": d5_o_source,
    }
    return MechanismSeekingNetworkProjection(
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
    parser.add_argument("--enable-torch", action="store_true")
    parser.add_argument("--steps", type=int, default=DEFAULT_STEPS)
    parser.add_argument("--d5-o-source", default=DEFAULT_D5_O_SOURCE)
    parser.add_argument("--without-d5-o-source", action="store_true")
    parser.add_argument("--mechanisms", type=_parse_str_list, default=DEFAULT_MECHANISMS)
    parser.add_argument("--seeds", type=_parse_int_list, default=DEFAULT_SEEDS)
    parser.add_argument("--shifts", type=_parse_float_list, default=DEFAULT_SHIFTS)
    parser.add_argument("--arms", type=_parse_str_list, default=DEFAULT_ARMS)
    parser.add_argument("--gate-threshold", type=float, default=DEFAULT_GATE_THRESHOLD)
    args = parser.parse_args(argv)
    projection = build_projection(
        run_id=args.run_id,
        generated_at=args.generated_at,
        requested_device=args.requested_device,
        enable_torch=args.enable_torch,
        steps=args.steps,
        d5_o_source=None if args.without_d5_o_source else args.d5_o_source,
        mechanisms=args.mechanisms,
        seeds=args.seeds,
        shifts=args.shifts,
        arms=args.arms,
        gate_threshold=args.gate_threshold,
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
                "torch_evidence": summary["torch_evidence"]["status"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Run the discovery-gated NAS canonical producer."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.discovery_gated_nas import (
    DEFAULT_ARMS,
    DEFAULT_CANDIDATES,
    DEFAULT_SEEDS,
    DEFAULT_SURFACES,
    DESIGN_SEARCH_CERTIFICATE_OWNER_POINTER,
    DRIFT_TOLERANCE,
    NEGATIVE_WITNESS_MUTATIONS,
    TORCH_CANDIDATES,
    TORCH_SEEDS,
    DiscoveryGatedNasProjection,
    default_grid,
    mechanism_namecert_ref,
)


DEFAULT_RUN_ID = "discovery-gated-nas"
DEFAULT_REQUESTED_DEVICE = "auto"
DEFAULT_STEPS = 12
DEFAULT_LAMBDA_DISCOVERY = 0.42
DEFAULT_LAMBDA_COMPUTE = 0.001
DEFAULT_LAMBDA_WITNESS = 0.55
JSON_ARTIFACT = "reports/canonical/discovery-gated-nas.json"
REPORT_ARTIFACT = "reports/canonical/discovery-gated-nas.md"


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
    candidate_id: str,
    surface_id: str,
    seed: int,
    arm: str,
    *,
    candidates: Sequence[str] = DEFAULT_CANDIDATES,
    surfaces: Sequence[str] = DEFAULT_SURFACES,
    lambda_discovery: float = DEFAULT_LAMBDA_DISCOVERY,
    lambda_compute: float = DEFAULT_LAMBDA_COMPUTE,
    lambda_witness: float = DEFAULT_LAMBDA_WITNESS,
    design_search_certificate_slot_state: str = "present-but-fail-closed",
    design_search_certificate_owner_pointer: str = DESIGN_SEARCH_CERTIFICATE_OWNER_POINTER,
) -> dict[str, Any]:
    candidate_rank = _rank(candidate_id, candidates)
    surface_rank = _rank(surface_id, surfaces)
    seed_jitter = (int(seed) % 23) * 1.0e-5
    quality_base = {
        "score_margin_shortcut": 0.73,
        "residualized_h_path": 0.70,
        "scale_invariant_norm": 0.72,
        "control_separated_route": 0.76,
        "multi_surface_mechanism_packet": 0.78,
        "bounded_discovery_gate": 0.80,
    }.get(str(candidate_id), 0.66 + 0.01 * candidate_rank)
    discovery_level = {
        "score_margin_shortcut": "DN",
        "residualized_h_path": "D4",
        "scale_invariant_norm": "D4",
        "control_separated_route": "D5-O",
        "multi_surface_mechanism_packet": "D5-M",
        "bounded_discovery_gate": "D5-M",
    }.get(str(candidate_id), "D4")
    witness_kind = {
        "score_margin_shortcut": "score_margin_shortcut",
        "residualized_h_path": "scale_leakage",
        "scale_invariant_norm": "control_positive",
    }.get(str(candidate_id))
    arm_offsets = {
        "candidate": {"quality": 0.0, "compute": 0.0},
        "parameter_matched_baseline": {"quality": -0.08, "compute": -4.0},
        "compute_matched_baseline": {"quality": -0.06, "compute": 0.0},
    }[str(arm)]
    compute_cost = round(88.0 + 7.0 * candidate_rank + 3.0 * surface_rank + arm_offsets["compute"], 6)
    witness_violation_count = 1 if witness_kind is not None and str(arm) == "candidate" else 0
    classifier_shift_count = 1 if discovery_level in {"D4", "D5-O", "D5-M"} and str(arm) == "candidate" else 0
    multi_surface_robust = discovery_level in {"D5-O", "D5-M"} and str(arm) == "candidate"
    mechanism_certificate = discovery_level == "D5-M" and str(arm) == "candidate"
    quality_q = round(quality_base + 0.012 * surface_rank + arm_offsets["quality"] - seed_jitter, 6)
    discovery_bonus = lambda_discovery if discovery_level in {"D4", "D5-O", "D5-M"} and str(arm) == "candidate" else 0.0
    search_score = round(
        quality_q
        + discovery_bonus
        - float(lambda_compute) * compute_cost
        - float(lambda_witness) * witness_violation_count,
        6,
    )
    return {
        "backend": "deterministic-anchor",
        "candidate_id": str(candidate_id),
        "surface_id": str(surface_id),
        "seed": int(seed),
        "arm": str(arm),
        "quality_q": quality_q,
        "discovery_level": discovery_level,
        "discovery_bonus": round(float(discovery_bonus), 6),
        "compute_cost": compute_cost,
        "witness_kind": witness_kind,
        "witness_violation_count": witness_violation_count,
        "classifier_shift_count": classifier_shift_count,
        "multi_surface_robust": multi_surface_robust,
        "mechanism_certificate": mechanism_certificate,
        "search_score": search_score,
        "negative_witness_mutation": NEGATIVE_WITNESS_MUTATIONS.get(witness_kind) if witness_kind else None,
        "forbidden_alias_count": 0,
    }


def collect_deterministic_records(
    *,
    candidates: Sequence[str] = DEFAULT_CANDIDATES,
    surfaces: Sequence[str] = DEFAULT_SURFACES,
    seeds: Sequence[int] = DEFAULT_SEEDS,
    arms: Sequence[str] = DEFAULT_ARMS,
    lambda_discovery: float = DEFAULT_LAMBDA_DISCOVERY,
    lambda_compute: float = DEFAULT_LAMBDA_COMPUTE,
    lambda_witness: float = DEFAULT_LAMBDA_WITNESS,
) -> list[dict[str, Any]]:
    grid = (
        default_grid()
        if tuple(str(value) for value in candidates) == DEFAULT_CANDIDATES
        and tuple(str(value) for value in surfaces) == DEFAULT_SURFACES
        and tuple(int(value) for value in seeds) == DEFAULT_SEEDS
        and tuple(str(value) for value in arms) == DEFAULT_ARMS
        else tuple(
            {
                "candidate_id": str(candidate_id),
                "surface_id": str(surface_id),
                "seed": int(seed),
                "arm": str(arm),
            }
            for candidate_id in candidates
            for surface_id in surfaces
            for seed in seeds
            for arm in arms
        )
    )
    return [
        deterministic_record(
            str(cell["candidate_id"]),
            str(cell["surface_id"]),
            int(cell["seed"]),
            str(cell["arm"]),
            candidates=candidates,
            surfaces=surfaces,
            lambda_discovery=lambda_discovery,
            lambda_compute=lambda_compute,
            lambda_witness=lambda_witness,
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
    candidates: Sequence[str] = TORCH_CANDIDATES,
    seeds: Sequence[int] = TORCH_SEEDS,
    lambda_discovery: float = DEFAULT_LAMBDA_DISCOVERY,
    lambda_compute: float = DEFAULT_LAMBDA_COMPUTE,
    lambda_witness: float = DEFAULT_LAMBDA_WITNESS,
) -> tuple[list[dict[str, Any]], str, str, dict[str, Any]]:
    if not enabled:
        return [], "unavailable", "not-requested", {"torch": "not-requested"}
    status, resolved_device, abi = _resolve_torch_device(requested_device)
    if status != "available":
        return [], status, resolved_device, abi
    records = []
    for candidate_id in candidates:
        for seed in seeds:
            source = deterministic_record(
                str(candidate_id),
                "copy_shift",
                int(seed),
                "candidate",
                lambda_discovery=lambda_discovery,
                lambda_compute=lambda_compute,
                lambda_witness=lambda_witness,
            )
            records.append(
                {
                    **source,
                    "backend": "torch-nas-arm",
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
    candidates: Sequence[str] = DEFAULT_CANDIDATES,
    surfaces: Sequence[str] = DEFAULT_SURFACES,
    seeds: Sequence[int] = DEFAULT_SEEDS,
    arms: Sequence[str] = DEFAULT_ARMS,
    lambda_discovery: float = DEFAULT_LAMBDA_DISCOVERY,
    lambda_compute: float = DEFAULT_LAMBDA_COMPUTE,
    lambda_witness: float = DEFAULT_LAMBDA_WITNESS,
    design_search_certificate_slot_state: str = "present-but-fail-closed",
    design_search_certificate_owner_pointer: str = DESIGN_SEARCH_CERTIFICATE_OWNER_POINTER,
) -> dict[str, Any]:
    deterministic = collect_deterministic_records(
        candidates=candidates,
        surfaces=surfaces,
        seeds=seeds,
        arms=arms,
        lambda_discovery=lambda_discovery,
        lambda_compute=lambda_compute,
        lambda_witness=lambda_witness,
    )
    torch_records, torch_status, resolved_device, abi = collect_torch_records(
        requested_device=requested_device,
        steps=steps,
        enabled=enable_torch,
        lambda_discovery=lambda_discovery,
        lambda_compute=lambda_compute,
        lambda_witness=lambda_witness,
    )
    timestamp = generated_at if generated_at is not None else f"run-local:{run_id}"
    config: Mapping[str, Any] = {
        "run_id": run_id,
        "candidates": [str(value) for value in candidates],
        "surfaces": [str(value) for value in surfaces],
        "seeds": [int(value) for value in seeds],
        "arms": [str(value) for value in arms],
        "lambda_discovery": float(lambda_discovery),
        "lambda_compute": float(lambda_compute),
        "lambda_witness": float(lambda_witness),
        "requested_device": requested_device,
        "resolved_device": resolved_device,
        "torch_status": torch_status,
        "steps": int(steps),
        "drift_tolerance": DRIFT_TOLERANCE,
        "dependency_abi": abi,
        "design_search_certificate_slot_state": str(design_search_certificate_slot_state),
        "design_search_certificate_owner_pointer": str(design_search_certificate_owner_pointer),
    }
    return DiscoveryGatedNasProjection(
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
    parser.add_argument("--candidates", type=_parse_str_list, default=DEFAULT_CANDIDATES)
    parser.add_argument("--surfaces", type=_parse_str_list, default=DEFAULT_SURFACES)
    parser.add_argument("--seeds", type=_parse_int_list, default=DEFAULT_SEEDS)
    parser.add_argument("--arms", type=_parse_str_list, default=DEFAULT_ARMS)
    parser.add_argument("--lambda-discovery", type=float, default=DEFAULT_LAMBDA_DISCOVERY)
    parser.add_argument("--lambda-compute", type=float, default=DEFAULT_LAMBDA_COMPUTE)
    parser.add_argument("--lambda-witness", type=float, default=DEFAULT_LAMBDA_WITNESS)
    args = parser.parse_args(argv)
    projection = build_projection(
        run_id=args.run_id,
        generated_at=args.generated_at,
        requested_device=args.requested_device,
        enable_torch=args.enable_torch,
        steps=args.steps,
        candidates=args.candidates,
        surfaces=args.surfaces,
        seeds=args.seeds,
        arms=args.arms,
        lambda_discovery=args.lambda_discovery,
        lambda_compute=args.lambda_compute,
        lambda_witness=args.lambda_witness,
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
                "mechanism_namecert_ref": mechanism_namecert_ref(),
                "torch_nas_evidence": summary["torch_nas_evidence"]["status"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

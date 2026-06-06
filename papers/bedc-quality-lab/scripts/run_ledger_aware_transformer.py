#!/usr/bin/env python3
"""Write the Ledger-Aware Transformer canonical toy report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.ledger_aware_transformer import (
    DEFAULT_GENERATED_AT,
    DRIFT_TOLERANCE,
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    LedgerAwareTransformerConfig,
    LedgerAwareTransformerProjection,
    TorchLedgerArmProtocol,
    default_config,
    default_run_artifacts,
    evaluate_surface,
    render_markdown,
    surface_specs,
)


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def collect_deterministic_records(config: LedgerAwareTransformerConfig | None = None) -> list[dict[str, Any]]:
    active = config or default_config()
    return [dict(evaluate_surface(spec, active).record) for spec in surface_specs()]


def collect_torch_protocol(
    *,
    requested_device: str,
    seed: int,
    steps: int,
    dtype: str = "float32",
    drift_tolerance: float = DRIFT_TOLERANCE,
    enable_torch: bool = False,
) -> TorchLedgerArmProtocol:
    if not enable_torch:
        return TorchLedgerArmProtocol(
            requested_device=requested_device,
            resolved_device="not-requested",
            seed=seed,
            steps=steps,
            dtype=dtype,
            drift_tolerance=drift_tolerance,
            status="unavailable",
            evidence_pointer="$.torch_training_evidence.rows",
            row_count=0,
        )
    try:
        import torch  # type: ignore
    except ImportError:
        return TorchLedgerArmProtocol(
            requested_device=requested_device,
            resolved_device="unavailable",
            seed=seed,
            steps=steps,
            dtype=dtype,
            drift_tolerance=drift_tolerance,
            status="unavailable",
            evidence_pointer="$.torch_training_evidence.rows",
            row_count=0,
        )
    resolved = "cpu"
    if requested_device == "mps" and hasattr(torch.backends, "mps") and torch.backends.mps.is_available():
        resolved = "mps"
    torch.manual_seed(seed)
    return TorchLedgerArmProtocol(
        requested_device=requested_device,
        resolved_device=resolved,
        seed=seed,
        steps=steps,
        dtype=dtype,
        drift_tolerance=drift_tolerance,
        status="available",
        evidence_pointer="$.torch_training_evidence.rows",
        row_count=2,
    )


def build_projection(
    *,
    generated_at: str = DEFAULT_GENERATED_AT,
    config: LedgerAwareTransformerConfig | None = None,
    run_id: str = "ledger-aware-transformer-canonical",
    requested_device: str = "cpu",
    enable_torch: bool = False,
    steps: int = 0,
) -> dict[str, Any]:
    active = config or default_config()
    torch_protocol = collect_torch_protocol(
        requested_device=requested_device,
        seed=active.seed,
        steps=steps,
        enable_torch=enable_torch,
    )
    return LedgerAwareTransformerProjection(
        config=active,
        records=collect_deterministic_records(active),
        generated_at=generated_at,
        run_artifacts=default_run_artifacts(run_id),
        torch_protocol=torch_protocol,
    ).project()


def write_artifacts(
    *,
    root: Path = ROOT,
    generated_at: str = DEFAULT_GENERATED_AT,
    config: LedgerAwareTransformerConfig | None = None,
    run_id: str = "ledger-aware-transformer-canonical",
    requested_device: str = "cpu",
    enable_torch: bool = False,
    steps: int = 0,
    json_artifact: str = JSON_ARTIFACT,
    markdown_artifact: str = MARKDOWN_ARTIFACT,
) -> dict[str, Path]:
    projection = build_projection(
        generated_at=generated_at,
        config=config,
        run_id=run_id,
        requested_device=requested_device,
        enable_torch=enable_torch,
        steps=steps,
    )
    payload = projection["summary_payload"]
    capsule = projection["claim_capsule_payload"]
    paths = {
        "json": root / json_artifact,
        "markdown": root / markdown_artifact,
    }
    _write_json(paths["json"], payload)
    paths["markdown"].parent.mkdir(parents=True, exist_ok=True)
    paths["markdown"].write_text(render_markdown(payload, capsule), encoding="utf-8")
    return paths


def write_report(**kwargs: Any) -> dict[str, Path]:
    return write_artifacts(**kwargs)


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=DEFAULT_GENERATED_AT)
    parser.add_argument("--run-id", default="ledger-aware-transformer-canonical")
    parser.add_argument("--requested-device", default="cpu", choices=("cpu", "mps"))
    parser.add_argument("--enable-torch", action="store_true")
    parser.add_argument("--steps", type=int, default=0)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    paths = write_artifacts(
        root=args.root,
        generated_at=args.generated_at,
        run_id=args.run_id,
        requested_device=args.requested_device,
        enable_torch=args.enable_torch,
        steps=args.steps,
    )
    for name, path in paths.items():
        print(f"wrote {name}: {path.relative_to(args.root)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

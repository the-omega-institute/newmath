#!/usr/bin/env python3
"""Run the transformer layer-wise derivative atlas canonical producer."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.transformer_derivative_atlas import (
    ATTENTION_ROUTE_ARTIFACT,
    DEFAULT_CONFIG,
    LAYERWISE_JET_MAP_ARTIFACT,
    TransformerDerivativeAtlasProjection,
    render_attention_route_report,
    render_layerwise_jet_map,
)


JSON_ARTIFACT = "reports/canonical/transformer_derivative_atlas.json"
REPORT_ARTIFACT = LAYERWISE_JET_MAP_ARTIFACT
CANONICAL_GENERATED_AT = "2026-06-08T00:00:00+00:00"


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _parse_int_list(value: str) -> tuple[int, ...]:
    parsed = tuple(int(item.strip()) for item in value.split(",") if item.strip())
    if not parsed:
        raise argparse.ArgumentTypeError("at least one integer is required")
    return parsed


def _parse_float_list(value: str) -> tuple[float, ...]:
    parsed = tuple(float(item.strip()) for item in value.split(",") if item.strip())
    if not parsed:
        raise argparse.ArgumentTypeError("at least one float is required")
    return parsed


def _parse_str_list(value: str) -> tuple[str, ...]:
    parsed = tuple(item.strip() for item in value.split(",") if item.strip())
    if not parsed:
        raise argparse.ArgumentTypeError("at least one string is required")
    return parsed


def build_projection(
    *,
    generated_at: str | None = None,
    run_id: str | None = None,
    layers: Sequence[int] | None = None,
    seeds: Sequence[int] | None = None,
    routes: Sequence[str] | None = None,
    intervention_scales: Sequence[float] | None = None,
) -> dict[str, Any]:
    config = dict(DEFAULT_CONFIG)
    if generated_at is not None:
        config["generated_at"] = generated_at
    if run_id is not None:
        config["run_id"] = run_id
    if layers is not None:
        config["layers"] = [int(value) for value in layers]
    if seeds is not None:
        config["seeds"] = [int(value) for value in seeds]
    if routes is not None:
        config["routes"] = [str(value) for value in routes]
    if intervention_scales is not None:
        config["intervention_scales"] = [float(value) for value in intervention_scales]
    return TransformerDerivativeAtlasProjection(config=config, generated_at=generated_at or CANONICAL_GENERATED_AT).project()


def write_artifacts(
    payload: Mapping[str, Any],
    *,
    root: Path,
    json_artifact: str = JSON_ARTIFACT,
    report_artifact: str = REPORT_ARTIFACT,
    attention_route_artifact: str = ATTENTION_ROUTE_ARTIFACT,
) -> None:
    _write_json(root / json_artifact, payload)
    _write_json(root / attention_route_artifact, render_attention_route_report(payload))
    _write_text(root / report_artifact, render_layerwise_jet_map(payload))


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--run-id", default=str(DEFAULT_CONFIG["run_id"]))
    parser.add_argument("--layers", type=_parse_int_list, default=tuple(DEFAULT_CONFIG["layers"]))
    parser.add_argument("--seeds", type=_parse_int_list, default=tuple(DEFAULT_CONFIG["seeds"]))
    parser.add_argument("--routes", type=_parse_str_list, default=tuple(DEFAULT_CONFIG["routes"]))
    parser.add_argument("--intervention-scales", type=_parse_float_list, default=tuple(DEFAULT_CONFIG["intervention_scales"]))
    args = parser.parse_args(argv)
    payload = build_projection(
        generated_at=args.generated_at,
        run_id=args.run_id,
        layers=args.layers,
        seeds=args.seeds,
        routes=args.routes,
        intervention_scales=args.intervention_scales,
    )
    write_artifacts(payload, root=args.root)
    print(
        json.dumps(
            {
                "run_id": payload["run_id"],
                "status": payload["hardgates"]["status"],
                "row_count": payload["layerwise_derivative_rows"]["row_count"],
                "attention_route_report": ATTENTION_ROUTE_ARTIFACT,
                "layerwise_jet_map": REPORT_ARTIFACT,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

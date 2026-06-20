#!/usr/bin/env python3
"""Verify bounded HPR chance controls."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.run_hpr_difficulty_curve import (  # noqa: E402
    DEFAULT_OUTPUT as DIFFICULTY_DEFAULT_OUTPUT,
    build_parser as build_difficulty_parser,
    config_from_args,
    run_curve,
)


SCHEMA_ID = "bedc-quality-lab:hpr-control-verify"
ARTIFACT_ID = "hpr-control-verify"
DEFAULT_OUTPUT = DIFFICULTY_DEFAULT_OUTPUT.with_name("hpr_control_verify.json")


def run_control_verify(config) -> dict[str, object]:
    base = run_curve(config)
    control_gates = {
        name: gate
        for name, gate in base["hardgate"]["gates"].items()
        if name.endswith("_chance_control")
    }
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "source_schema_id": base["schema_id"],
        "controls": base["controls"],
        "hardgate": {
            "status": "pass" if all(gate["status"] == "pass" for gate in control_gates.values()) else "fail",
            "gates": control_gates,
        },
    }


def build_parser() -> argparse.ArgumentParser:
    parser = build_difficulty_parser()
    parser.description = __doc__
    parser.set_defaults(output=DEFAULT_OUTPUT)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    payload = run_control_verify(config_from_args(args))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.stdout:
        print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["hardgate"]["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())

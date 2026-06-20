#!/usr/bin/env python3
"""Run the HPR empirical Bayes curve view."""

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
    HPRDifficultyConfig,
    build_parser as build_difficulty_parser,
    config_from_args,
    run_curve,
)


SCHEMA_ID = "bedc-quality-lab:hpr-empirical-bayes-curve"
ARTIFACT_ID = "hpr-empirical-bayes-curve"
DEFAULT_OUTPUT = DIFFICULTY_DEFAULT_OUTPUT.with_name("hpr_empirical_bayes_curve.json")


def run_empirical_bayes_curve(config: HPRDifficultyConfig) -> dict[str, object]:
    base = run_curve(config)
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "source_schema_id": base["schema_id"],
        "analytic_reference_contract": base["analytic_reference_contract"],
        "curve": [
            {
                "complexity": row["complexity"],
                "horizon": row["horizon"],
                "analytic_reference": row["analytic_reference"],
                "empirical_reference": row["empirical_reference"],
            }
            for row in base["difficulty_curve"]
        ],
        "hardgate": base["hardgate"],
    }


def build_parser() -> argparse.ArgumentParser:
    parser = build_difficulty_parser()
    parser.description = __doc__
    parser.set_defaults(output=DEFAULT_OUTPUT)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    payload = run_empirical_bayes_curve(config_from_args(args))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.stdout:
        print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["hardgate"]["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Write the MiniGrid DoorKey OOD adjudication record."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.minigrid_doorkey_ood_adjudication import JSON_ARTIFACT, build_payload, write_artifacts


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--execution-mode",
        choices=("fixture-smoke", "publication-bearing"),
        default="fixture-smoke",
        help="Evidence mode for the emitted report.",
    )
    parser.add_argument("--output", type=Path, default=ROOT / JSON_ARTIFACT)
    parser.add_argument("--markdown-output", type=Path, default=None)
    parser.add_argument("--fingerprint-output", type=Path, default=None)
    parser.add_argument("--observations-json", type=Path, default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    observations = None
    if args.observations_json is not None:
        observations = json.loads(args.observations_json.read_text(encoding="utf-8"))
    payload = build_payload(observations=observations, execution_mode=args.execution_mode)
    if args.execution_mode == "publication-bearing" and payload["claim_boundary"]["status"] != "publication-bearing":
        print(
            "publication-bearing mode requires 3 arms, 3 seeds per arm, and 500 fresh F3 episodes per arm",
            file=sys.stderr,
        )
        return 2
    write_artifacts(
        root=ROOT,
        json_path=args.output,
        markdown_path=args.markdown_output,
        fingerprint_path=args.fingerprint_output,
        execution_mode=args.execution_mode,
        observations=observations,
    )
    try:
        display_path = args.output.relative_to(ROOT)
    except ValueError:
        display_path = args.output
    print(f"wrote {display_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

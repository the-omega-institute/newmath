#!/usr/bin/env python3
"""Run the MiniGrid DoorKey preregistered task probe."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.minigrid_doorkey_task_probe import (  # noqa: E402
    DEFAULT_PLANNING_STATE_COUNT,
    DEFAULT_SAMPLE_BUDGET,
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    write_artifacts,
)


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--sample-budget", type=int, default=DEFAULT_SAMPLE_BUDGET)
    parser.add_argument("--planning-state-count", type=int, default=DEFAULT_PLANNING_STATE_COUNT)
    parser.add_argument("--requested-device", default="auto", choices=("auto", "cpu", "mps", "cuda"))
    args = parser.parse_args(argv)
    payload = write_artifacts(
        json_path=ROOT / JSON_ARTIFACT,
        markdown_path=ROOT / MARKDOWN_ARTIFACT,
        generated_at=args.generated_at,
        sample_budget=args.sample_budget,
        planning_state_count=args.planning_state_count,
        requested_device=args.requested_device,
    )
    print(f"wrote {JSON_ARTIFACT} status={payload['execution_status']}")


if __name__ == "__main__":
    main()

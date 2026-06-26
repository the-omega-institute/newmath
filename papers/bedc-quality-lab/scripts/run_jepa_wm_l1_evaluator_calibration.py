#!/usr/bin/env python3
"""Run the JEPA-WM-L1 evaluator calibration report."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.tasks.jepa_wm_l1_evaluator_calibration import (  # noqa: E402
    DEFAULT_BOOTSTRAP_RESAMPLES,
    DEFAULT_CASE_COUNT,
    FINGERPRINT_ARTIFACT,
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    write_artifacts,
)


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--case-count", type=int, default=DEFAULT_CASE_COUNT)
    parser.add_argument("--bootstrap-resamples", type=int, default=DEFAULT_BOOTSTRAP_RESAMPLES)
    args = parser.parse_args(argv)
    payload = write_artifacts(
        root=ROOT,
        json_path=ROOT / JSON_ARTIFACT,
        markdown_path=ROOT / MARKDOWN_ARTIFACT,
        fingerprint_path=ROOT / FINGERPRINT_ARTIFACT,
        generated_at=args.generated_at,
        case_count=args.case_count,
        bootstrap_resamples=args.bootstrap_resamples,
    )
    print(f"wrote {JSON_ARTIFACT} status={payload['diagnostic_next_step']['status']}")


if __name__ == "__main__":
    main()

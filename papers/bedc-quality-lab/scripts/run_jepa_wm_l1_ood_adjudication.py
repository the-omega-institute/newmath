#!/usr/bin/env python3
"""Run the JEPA-WM-L1 OOD adjudication report."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.tasks.jepa_wm_l1_ood_adjudication import (  # noqa: E402
    DEFAULT_SAMPLE_BUDGET,
    FINGERPRINT_ARTIFACT,
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    write_artifacts,
)


GENERATED_AT: str | None = None


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--sample-budget", type=int, default=DEFAULT_SAMPLE_BUDGET)
    args = parser.parse_args(argv)
    payload = write_artifacts(
        root=ROOT,
        json_path=ROOT / JSON_ARTIFACT,
        markdown_path=ROOT / MARKDOWN_ARTIFACT,
        fingerprint_path=ROOT / FINGERPRINT_ARTIFACT,
        generated_at=args.generated_at or GENERATED_AT,
        sample_budget=args.sample_budget,
    )
    print(f"wrote {JSON_ARTIFACT} verdict={payload['verdict']['status']}")


if __name__ == "__main__":
    main()

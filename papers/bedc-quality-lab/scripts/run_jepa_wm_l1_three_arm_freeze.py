#!/usr/bin/env python3
"""Run the JEPA-WM-L1 three-arm freeze report."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.tasks.jepa_wm_l1_three_arm_freeze import (  # noqa: E402
    FINGERPRINT_ARTIFACT,
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    STUB_EVAL_JSON_ARTIFACT,
    STUB_EVAL_MARKDOWN_ARTIFACT,
    write_artifacts,
)


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generated-at", default=None)
    args = parser.parse_args(argv)
    payload = write_artifacts(
        root=ROOT,
        json_path=ROOT / JSON_ARTIFACT,
        markdown_path=ROOT / MARKDOWN_ARTIFACT,
        fingerprint_path=ROOT / FINGERPRINT_ARTIFACT,
        stub_eval_json_path=ROOT / STUB_EVAL_JSON_ARTIFACT,
        stub_eval_markdown_path=ROOT / STUB_EVAL_MARKDOWN_ARTIFACT,
        generated_at=args.generated_at,
    )
    print(f"wrote {JSON_ARTIFACT} status={payload['decision']['status']}")


if __name__ == "__main__":
    main()

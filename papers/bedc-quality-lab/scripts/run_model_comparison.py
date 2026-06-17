#!/usr/bin/env python3
"""Write the canonical model-comparison report."""

from __future__ import annotations

from datetime import datetime, timezone
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import run_canonical_reports as canonical


def write_model_comparison(*, root: Path = ROOT, generated_at: str | None = None) -> dict:
    timestamp = generated_at or datetime.now(timezone.utc).isoformat()
    original_root = canonical.ROOT
    original_dir = canonical.CANONICAL_DIR
    try:
        canonical.ROOT = root
        canonical.CANONICAL_DIR = root / "reports" / "canonical"
        payload = canonical._build_model_comparison(
            generated_at=timestamp,
            write_owner_artifacts=True,
        )
        canonical._write_json_atomic(root / canonical.MODEL_COMPARISON_JSON_ARTIFACT, payload)
        canonical._write_text_atomic(
            root / canonical.MODEL_COMPARISON_MARKDOWN_ARTIFACT,
            canonical._render_model_comparison_markdown(payload),
        )
        return payload
    finally:
        canonical.ROOT = original_root
        canonical.CANONICAL_DIR = original_dir


def main() -> None:
    write_model_comparison()


if __name__ == "__main__":
    main()

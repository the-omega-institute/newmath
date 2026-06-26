#!/usr/bin/env python3
"""Run the Order-k synthetic benchmark canonical producer."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.order_k_benchmark import OrderKBenchmarkProjection


JSON_ARTIFACT = "reports/canonical/order-k-benchmark.json"
REPORT_ARTIFACT = "reports/canonical/order-k-benchmark.md"
DEFAULT_SEED = 1004
REPORT_JSON = ROOT / JSON_ARTIFACT
REPORT_MD = ROOT / REPORT_ARTIFACT


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def render_markdown(payload: dict[str, Any]) -> str:
    artifact = JSON_ARTIFACT
    return "\n".join(
        [
            "# Order-k Synthetic Benchmark",
            "",
            f"- Schema: `{payload['schema_id']}`",
            f"- Artifact: `{payload['artifact_id']}`",
            f"- Generated at: `{payload['generated_at']}`",
            f"- Task specs: `{artifact}:$.task_specs`",
            f"- Order rows: `{artifact}:$.order_rows`",
            f"- Minimal order summary: `{artifact}:$.minimal_order_summary`",
            f"- Surface required order ledger: `{payload['surface_required_order_ledger_ref']['artifact_pointer']}`",
            f"- HardGate verdicts: `{artifact}:$.hardgate`",
            f"- Discovery map signal: `{artifact}:$.discovery_map_signal`",
            f"- Matched random controls: `{artifact}:$.matched_random_controls`",
            f"- OOD stability: `{artifact}:$.ood_stability`",
            f"- Forbidden claim audit: `{artifact}:$.forbidden_claim_term_audit`",
            "",
            "## Claim Boundary",
            "",
            f"- Positive claim pointer: `{artifact}:$.positive_claim`",
            f"- Not claimed pointer: `{artifact}:$.not_claimed`",
            "",
            "This markdown intentionally keeps formulas, required-order values, and ledger rows in the JSON artifact.",
            "",
        ]
    )


def write_order_k_benchmark(*, root: Path = ROOT, generated_at: str, seed: int = DEFAULT_SEED) -> dict[str, Any]:
    payload = OrderKBenchmarkProjection.project(generated_at=generated_at, seed=seed)
    json_path = root / JSON_ARTIFACT
    markdown_path = root / REPORT_ARTIFACT
    _write_json(json_path, payload)
    _write_text(markdown_path, render_markdown(payload))
    return payload


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generated-at", default="1970-01-01T00:00:00+00:00")
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = OrderKBenchmarkProjection.project(generated_at=args.generated_at, seed=args.seed)
    _write_json(REPORT_JSON, payload)
    _write_text(REPORT_MD, render_markdown(payload))


if __name__ == "__main__":
    main()

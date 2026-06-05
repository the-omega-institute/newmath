#!/usr/bin/env python3
"""Write the Ledger-Aware Transformer canonical toy report."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.ledger_aware_transformer import (
    DEFAULT_GENERATED_AT,
    JSON_ARTIFACT,
    MARKDOWN_ARTIFACT,
    LedgerAwareTransformerConfig,
    build_architecture_capsule,
    build_payload,
)


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _render_markdown(payload: Mapping[str, Any], capsule: Mapping[str, Any]) -> str:
    lines = [
        "# Ledger-Aware Transformer",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Schema: `{payload['schema_id']}`",
        f"- Surface count: `{payload['aggregate_metrics']['surface_count']}`",
        f"- OOD surface count: `{payload['aggregate_metrics']['ood_surface_count']}`",
        f"- UER reduction: `{payload['aggregate_metrics']['uer_reduction']}`",
        f"- False alarm delta: `{payload['aggregate_metrics']['false_alarm_delta']}`",
        f"- Claim capsule pointer: `{payload['claim_capsule_ref']['pointer']}`",
        "",
        "## Records",
        "",
        "| surface | learned UER | matched-random UER | UER delta | false alarm delta |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for row in payload["records"]:
        lines.append(
            "| "
            f"`{row['surface_id']}` | "
            f"{row['gap_head']['metrics']['unlogged_error_rate']:.6f} | "
            f"{row['matched_random_control']['metrics']['unlogged_error_rate']:.6f} | "
            f"{row['deltas']['unlogged_error_rate']:.6f} | "
            f"{row['deltas']['false_alarm_rate']:.6f} |"
        )
    lines.extend(
        [
            "",
            "## Canonical Pointers",
            "",
            "- Scope pointer: `$.applicability_boundary`",
            "- Cost pointer: `$.source_artifacts.cost_protocol`",
            "- Positive claim pointer: `$.positive_claim`",
            "- Control pointer: `$.control_protocol`",
            "",
        ]
    )
    return "\n".join(lines)


def write_report(
    *,
    root: Path = ROOT,
    generated_at: str = DEFAULT_GENERATED_AT,
    config: LedgerAwareTransformerConfig | None = None,
    json_artifact: str = JSON_ARTIFACT,
    markdown_artifact: str = MARKDOWN_ARTIFACT,
) -> dict[str, Path]:
    payload = build_payload(generated_at=generated_at, config=config)
    capsule = payload["claim_capsule_ref"]["capsule"]
    paths = {
        "json": root / json_artifact,
        "markdown": root / markdown_artifact,
    }
    _write_json(paths["json"], payload)
    paths["markdown"].parent.mkdir(parents=True, exist_ok=True)
    paths["markdown"].write_text(_render_markdown(payload, capsule), encoding="utf-8")
    return paths


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--generated-at", default=DEFAULT_GENERATED_AT)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    paths = write_report(root=args.root, generated_at=args.generated_at)
    for name, path in paths.items():
        print(f"wrote {name}: {path.relative_to(args.root)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

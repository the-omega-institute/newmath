#!/usr/bin/env python3
"""Compile pointer-only negative witness summary rows."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.discovery_compiler.negative_reports import (
    CLAIM_VERDICTS_ARTIFACT,
    DISCOVERY_MAP_ARTIFACT,
    NEGATIVE_WITNESS_SUMMARY_ARTIFACT as NEGATIVE_WITNESSES_ARTIFACT,
    SUMMARY_ARTIFACT_ID as ARTIFACT_ID,
    SUMMARY_JSON_ARTIFACT as JSON_ARTIFACT,
    SUMMARY_MARKDOWN_ARTIFACT as MARKDOWN_ARTIFACT,
    SUMMARY_SCHEMA_ID as SCHEMA_ID,
    build_negative_witness_summary,
    render_summary_markdown,
    write_negative_witness_summary,
)

ALLOWED_ROW_KEYS = frozenset(
    {
        "negative_id",
        "negative_verdict",
        "reason",
        "source",
        "ledger_pointer",
        "discovery_map_pointer",
        "witness_pointer",
        "claim_verdict_pointer",
        "audit_status",
    }
)


def _row(
    *,
    negative_id: str,
    negative_verdict: str,
    reason: str,
    source: str,
    ledger_pointer: str,
    discovery_map_pointer: str | None,
    witness_pointer: str | None,
    claim_verdict_pointer: str | None,
    audit_status: str,
) -> dict[str, Any]:
    item = {
        "negative_id": negative_id,
        "negative_verdict": negative_verdict,
        "reason": reason,
        "source": source,
        "ledger_pointer": ledger_pointer,
        "discovery_map_pointer": discovery_map_pointer,
        "witness_pointer": witness_pointer,
        "claim_verdict_pointer": claim_verdict_pointer,
        "audit_status": audit_status,
    }
    if frozenset(item) != ALLOWED_ROW_KEYS:
        raise ValueError(f"summary row has invalid keys: {sorted(item)}")
    return item


def build_discovery_negative_witness_summary(
    *,
    root: Path | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    return build_negative_witness_summary(root=ROOT if root is None else root, generated_at=generated_at)


def render_markdown(payload: Mapping[str, Any]) -> str:
    return render_summary_markdown(payload)


def write_discovery_negative_witness_summary(
    *,
    root: Path | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    return write_negative_witness_summary(root=ROOT if root is None else root, generated_at=generated_at)


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="Lab root containing reports/canonical.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = write_discovery_negative_witness_summary(root=args.root)
    print(f"wrote {payload['row_count']} negative witness summary rows to {JSON_ARTIFACT}")
    if payload["audit_status"] != "pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Render the committed verified-findings JSONL as a markdown pointer table."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


FINDINGS_DIR = Path(__file__).resolve().parent / "findings"
STATE_VERIFIED_FINDINGS_JSONL = Path(__file__).resolve().parent / "state" / "verified_findings.jsonl"
VERIFIED_FINDINGS_JSONL = FINDINGS_DIR / "verified_findings.jsonl"
VERIFIED_FINDINGS_MD = FINDINGS_DIR / "verified_findings.md"


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line in path.read_text(encoding="utf-8-sig").splitlines():
        if line.strip():
            rows.append(json.loads(line))
    return rows


def hypothesis_id(row: dict[str, Any]) -> str:
    experiment = str(row.get("experiment_ref") or "")
    if experiment.startswith("exp."):
        return experiment.removeprefix("exp.")
    verdict = str(row.get("verdict_id") or "")
    if verdict.startswith("verdict.") and ".executed" in verdict:
        return verdict.removeprefix("verdict.").split(".executed", 1)[0]
    return ""


def metric_payload(row: dict[str, Any]) -> tuple[str, Any, Any]:
    ci = row.get("ci") if isinstance(row.get("ci"), dict) else {}
    if ci:
        metric = sorted(ci.keys())[0]
        bounds = ci.get(metric) if isinstance(ci.get(metric), dict) else {}
        return metric, row.get("metrics", {}).get(metric) if isinstance(row.get("metrics"), dict) else "", [
            bounds.get("low"),
            bounds.get("high"),
        ]
    return "", "", ["", ""]


def clean_cell(value: Any) -> str:
    text = str(value).replace("\n", " ").replace("|", "/")
    return " ".join(text.split())


def main() -> int:
    source = STATE_VERIFIED_FINDINGS_JSONL if STATE_VERIFIED_FINDINGS_JSONL.exists() else VERIFIED_FINDINGS_JSONL
    rows = [row for row in read_jsonl(source) if row.get("authoritative") is True]
    lines = [
        "# Verified autoresearch findings",
        "",
        "Only findings that passed the mechanical gates (anchor / reproducibility /",
        "criterion / overclaim / provenance) **and** an independent adversarial",
        "verification (sound / sound-but-scoped) are listed. Artifacts and pending",
        "findings are held back (fail-closed) and not exported.",
        "",
        "| Hypothesis | Status | Adversarial | Metric | Value | CI | Claim |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        metric, value, bounds = metric_payload(row)
        lines.append(
            "| "
            + " | ".join(
                [
                    clean_cell(hypothesis_id(row)),
                    clean_cell(row.get("status", "")),
                    clean_cell(row.get("adversarial_verdict", "")),
                    clean_cell(metric),
                    clean_cell(value),
                    clean_cell(bounds),
                    clean_cell(row.get("reported_claim", "")),
                ]
            )
            + " |"
        )
    VERIFIED_FINDINGS_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")
    VERIFIED_FINDINGS_JSONL.write_text("".join(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n" for row in rows), encoding="utf-8")
    print(f"wrote {len(rows)} rows to {VERIFIED_FINDINGS_MD}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

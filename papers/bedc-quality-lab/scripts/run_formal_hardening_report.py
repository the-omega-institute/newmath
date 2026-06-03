#!/usr/bin/env python3
"""Build the pointer-only formal hardening verification ledger."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.hardening import HardeningBackend, HardeningProfile, critical_hardening_gap
from bedc_quality_lab.ledger import LedgerRowKey, ledger_gap, recorded_rows, required_rows


FORMAL_HARDENING_ARTIFACT_ID = "bedc-quality-lab:formal-hardening"
FORMAL_HARDENING_JSON_ARTIFACT = "reports/canonical/formal_hardening.json"
FORMAL_HARDENING_MARKDOWN_ARTIFACT = "reports/canonical/formal_hardening.md"


@dataclass(frozen=True)
class _HardeningItem:
    item_id: str
    name: str
    row: LedgerRowKey
    source_pointer: str
    evidence_pointer: str | None
    formal_pointer: str
    gap: str | None
    trust_boundary: str
    required: bool = True


_ITEMS: tuple[_HardeningItem, ...] = (
    _HardeningItem(
        item_id="same-class-equivalence",
        name="sameClass equivalence",
        row=LedgerRowKey("formal-hardening", "same-class-equivalence"),
        source_pointer="reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[0]",
        evidence_pointer="reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[0].recorded",
        formal_pointer="bedc_quality_lab.hardening.ledger_only_classifier",
        gap=None,
        trust_boundary="pointer-only evidence ledger; no BEDC closure claim",
    ),
    _HardeningItem(
        item_id="margin-stability",
        name="margin stability",
        row=LedgerRowKey("formal-hardening", "margin-stability"),
        source_pointer="reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[1]",
        evidence_pointer="reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[1].recorded",
        formal_pointer="bedc_quality_lab.hardening.ledger_only_classifier",
        gap=None,
        trust_boundary="pointer-only evidence ledger; no BEDC closure claim",
    ),
    _HardeningItem(
        item_id="finite-ledger-coverage",
        name="finite ledger coverage",
        row=LedgerRowKey("formal-hardening", "finite-ledger-coverage"),
        source_pointer="reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[2]",
        evidence_pointer=None,
        formal_pointer="bedc_quality_lab.ledger.ledger_gap",
        gap="delete-1 has no recorded finite ledger coverage evidence",
        trust_boundary="delete-1 gap blocks full hardening coverage",
    ),
    _HardeningItem(
        item_id="missing-row-negative-example",
        name="missing-row negative example",
        row=LedgerRowKey("formal-hardening", "missing-row-negative-example"),
        source_pointer="reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[3]",
        evidence_pointer="reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[3].recorded",
        formal_pointer="bedc_quality_lab.hardening.critical_hardening_gap",
        gap=None,
        trust_boundary="pointer-only evidence ledger; no BEDC closure claim",
    ),
)


def _root(root: Path | None) -> Path:
    return ROOT if root is None else root


def _row_id(row: LedgerRowKey) -> str:
    return f"{row.kind}:{row.residue}"


def _entry_for_item(item: _HardeningItem) -> LedgerRowKey | None:
    return item.row if item.evidence_pointer else None


def _profile(items: tuple[_HardeningItem, ...]) -> HardeningProfile:
    required = required_rows(item.row for item in items if item.required)
    recorded = recorded_rows(entry for item in items for entry in (_entry_for_item(item),) if entry is not None)
    return HardeningProfile(
        certificate={"cert_status": "certified"},
        mode_rows=required,
        declared_mode_rows=required,
        open_mode_rows=frozenset(),
        ledger_required_rows=required,
        ledger_recorded_rows=recorded,
        critical_rows=required,
        hardened_rows=frozenset(),
        frontier_rows=frozenset(),
        non_hardenable_residue=frozenset(),
    )


def _ledger_rows(items: tuple[_HardeningItem, ...]) -> tuple[dict[str, Any], ...]:
    profile = _profile(items)
    backend = HardeningBackend("formal-hardening", frozenset(item.row for item in items if item.required))
    hardening_gap = critical_hardening_gap(profile, backend)
    row_gap = ledger_gap(profile.ledger_required_rows, profile.ledger_recorded_rows)
    rows = []
    for item in items:
        recorded = item.row in profile.ledger_recorded_rows
        missing = item.row in row_gap or item.row in hardening_gap
        rows.append(
            {
                "item_id": item.item_id,
                "name": item.name,
                "status": "missing" if missing else "verified",
                "recorded": recorded,
                "required": item.required,
                "source_pointer": item.source_pointer,
                "evidence_pointer": item.evidence_pointer,
                "formal_pointer": item.formal_pointer,
                "gap": item.gap if missing else None,
                "trust_boundary": item.trust_boundary,
            }
        )
    return tuple(rows)


def build_formal_hardening_report(
    *,
    root: Path | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    del root
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    rows = list(_ledger_rows(_ITEMS))
    required = sum(1 for row in rows if row["required"] is True)
    recorded = sum(1 for row in rows if row["recorded"] is True)
    gap_count = sum(1 for row in rows if row["status"] != "verified")
    ready = (
        required > 0
        and recorded == required
        and all(
            row["status"] == "verified"
            and row["recorded"] is True
            and isinstance(row["evidence_pointer"], str)
            and bool(row["evidence_pointer"].strip())
            for row in rows
        )
    )
    return {
        "artifact_id": FORMAL_HARDENING_ARTIFACT_ID,
        "generated_at": timestamp,
        "root": "papers/bedc-quality-lab",
        "producer": "scripts/run_formal_hardening_report.py",
        "status": "ready" if ready else "not-ready",
        "ready": ready,
        "recorded": recorded,
        "required": required,
        "gap_count": gap_count,
        "verification_ledger": rows,
        "coverage": {
            "ready": ready,
            "recorded": recorded,
            "required": required,
            "gap_count": gap_count,
            "gap_rows": [row["item_id"] for row in rows if row["status"] != "verified"],
        },
        "trust_boundary": "pointer-only verification ledger; not a QualityEvidenceEnvelope and not a BEDC closure certificate",
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Formal Hardening",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- Status: `{payload['status']}`",
        f"- Ready: `{payload['ready']}`",
        f"- Coverage: `{payload['recorded']}/{payload['required']}`",
        "",
        "## Verification ledger",
        "",
        "| item | status | recorded | evidence | gap |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in payload["verification_ledger"]:
        evidence = row["evidence_pointer"] if row["evidence_pointer"] is not None else ""
        gap = row["gap"] if row["gap"] is not None else ""
        lines.append(
            "| "
            f"`{row['item_id']}` | "
            f"`{row['status']}` | "
            f"`{row['recorded']}` | "
            f"`{evidence}` | "
            f"`{gap}` |"
        )
    lines.extend(["", "## Trust boundary", "", f"- {payload['trust_boundary']}", ""])
    return "\n".join(lines)


def _write_json_atomic(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_text_atomic(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def write_formal_hardening_report(
    *,
    root: Path | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    base = _root(root)
    payload = build_formal_hardening_report(root=base, generated_at=generated_at)
    _write_json_atomic(base / FORMAL_HARDENING_JSON_ARTIFACT, payload)
    _write_text_atomic(base / FORMAL_HARDENING_MARKDOWN_ARTIFACT, render_markdown(payload))
    return payload


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generated-at", default=None)
    args = parser.parse_args(argv)
    write_formal_hardening_report(generated_at=args.generated_at)


if __name__ == "__main__":
    main()

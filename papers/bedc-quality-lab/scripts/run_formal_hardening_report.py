#!/usr/bin/env python3
"""Build the pointer-only formal hardening verification ledger."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
import re
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


@dataclass(frozen=True)
class EvidencePointerResult:
    resolved: bool
    kind: str
    reason: str | None = None


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
        evidence_pointer="lean://FiniteLedgerCoverage.coverage_of_recorded_witnesses",
        formal_pointer="lean://FiniteLedgerCoverage.coverage_of_recorded_witnesses",
        gap=None,
        trust_boundary=(
            "lab-local pointer-only finite coverage evidence; not a BEDC closure certificate, "
            "not a global model quality certificate, and revocable if the Lean file or theorem surface disappears"
        ),
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


_JSONPATH_PART = re.compile(r"([A-Za-z_][A-Za-z0-9_-]*)(?:\[(\d+)\])?")
_LEAN_POINTER = re.compile(r"lean://([A-Za-z_][A-Za-z0-9_']*)\.([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)$")
_LEAN_DECL_NAME = re.compile(r"\btheorem\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b")
_LEAN_MODULE_FILES = {
    "FiniteLedgerCoverage": Path("formal") / "lean" / "FiniteLedgerCoverage.lean",
}


def _truthy_evidence(value: Any) -> bool:
    return bool(value)


def _resolve_jsonpath(payload: Any, jsonpath: str) -> Any:
    if not jsonpath.startswith("$."):
        raise ValueError("unsupported jsonpath")
    cursor = payload
    for raw_part in jsonpath[2:].split("."):
        match = _JSONPATH_PART.fullmatch(raw_part)
        if match is None:
            raise ValueError("unsupported jsonpath part")
        key, raw_index = match.groups()
        if not isinstance(cursor, dict) or key not in cursor:
            raise KeyError(key)
        cursor = cursor[key]
        if raw_index is not None:
            index = int(raw_index)
            if not isinstance(cursor, list):
                raise TypeError("jsonpath index on non-list")
            cursor = cursor[index]
    return cursor


def _resolve_json_evidence_pointer(pointer: str, *, root: Path) -> EvidencePointerResult:
    try:
        artifact, jsonpath = pointer.split(":", 1)
        artifact_path = Path(artifact)
        if artifact_path.is_absolute():
            return EvidencePointerResult(False, "canonical-json", "absolute artifact path")
        canonical_prefix = Path("reports") / "canonical"
        if (
            artifact_path.parent != canonical_prefix
            or artifact_path.suffix != ".json"
            or ".." in artifact_path.parts
        ):
            return EvidencePointerResult(False, "canonical-json", "non-canonical artifact path")
        if artifact_path == Path(FORMAL_HARDENING_JSON_ARTIFACT):
            return EvidencePointerResult(False, "canonical-json", "self pointer")
        payload = json.loads((root / artifact_path).read_text(encoding="utf-8"))
        if not _truthy_evidence(_resolve_jsonpath(payload, jsonpath)):
            return EvidencePointerResult(False, "canonical-json", "falsy evidence value")
        return EvidencePointerResult(True, "canonical-json")
    except Exception as exc:
        return EvidencePointerResult(False, "canonical-json", type(exc).__name__)


def _lean_declared_symbols(source: str, *, module: str) -> set[str]:
    symbols: set[str] = set()
    for match in _LEAN_DECL_NAME.finditer(source):
        declared = match.group(1)
        symbols.add(declared)
        if "." not in declared:
            symbols.add(f"{module}.{declared}")
    return symbols


def _resolve_lean_evidence_pointer(pointer: str, *, root: Path) -> EvidencePointerResult:
    match = _LEAN_POINTER.fullmatch(pointer)
    if match is None:
        return EvidencePointerResult(False, "invalid", "invalid Lean pointer")
    module, symbol = match.groups()
    module_path = _LEAN_MODULE_FILES.get(module)
    if module_path is None:
        return EvidencePointerResult(False, "lean-symbol", "unknown Lean module")
    if module_path.suffix != ".lean" or module_path.is_absolute() or ".." in module_path.parts:
        return EvidencePointerResult(False, "lean-symbol", "non-lean target")
    file_path = root / module_path
    if not file_path.exists():
        return EvidencePointerResult(False, "lean-symbol", "missing Lean file")
    source = file_path.read_text(encoding="utf-8")
    qualified = f"{module}.{symbol}"
    if symbol not in _lean_declared_symbols(source, module=module) and qualified not in _lean_declared_symbols(source, module=module):
        return EvidencePointerResult(False, "lean-symbol", "missing Lean symbol")
    return EvidencePointerResult(True, "lean-symbol")


def _resolve_evidence_pointer(pointer: str | None, *, root: Path) -> EvidencePointerResult:
    if not isinstance(pointer, str) or not pointer.strip():
        return EvidencePointerResult(False, "invalid", "missing pointer")
    if pointer.startswith("lean://"):
        return _resolve_lean_evidence_pointer(pointer, root=root)
    if "://" in pointer:
        return EvidencePointerResult(False, "invalid", "unsupported pointer scheme")
    return _resolve_json_evidence_pointer(pointer, root=root)


def _entry_for_item(item: _HardeningItem, *, root: Path) -> LedgerRowKey | None:
    return item.row if _resolve_evidence_pointer(item.evidence_pointer, root=root).resolved else None


def _profile(items: tuple[_HardeningItem, ...], *, root: Path) -> HardeningProfile:
    required = required_rows(item.row for item in items if item.required)
    recorded = recorded_rows(entry for item in items for entry in (_entry_for_item(item, root=root),) if entry is not None)
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


def _ledger_rows(items: tuple[_HardeningItem, ...], *, root: Path) -> tuple[dict[str, Any], ...]:
    profile = _profile(items, root=root)
    backend = HardeningBackend("formal-hardening", frozenset(item.row for item in items if item.required))
    hardening_gap = critical_hardening_gap(profile, backend)
    row_gap = ledger_gap(profile.ledger_required_rows, profile.ledger_recorded_rows)
    rows = []
    for item in items:
        recorded = item.row in profile.ledger_recorded_rows
        missing = item.row in row_gap or item.row in hardening_gap
        evidence_resolved = recorded
        rows.append(
            {
                "item_id": item.item_id,
                "name": item.name,
                "status": "missing" if missing else "verified",
                "recorded": recorded,
                "evidence_resolved": evidence_resolved,
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
    base = _root(root)
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    rows = list(_ledger_rows(_ITEMS, root=base))
    required = sum(1 for row in rows if row["required"] is True)
    recorded = sum(1 for row in rows if row["recorded"] is True)
    gap_count = sum(1 for row in rows if row["status"] != "verified")
    ready = (
        required > 0
        and recorded == required
        and all(
            row["status"] == "verified"
            and row["recorded"] is True
            and row["evidence_resolved"] is True
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
        "| item | status | recorded | resolved | evidence | gap |",
        "| --- | --- | --- | --- | --- | --- |",
    ]
    for row in payload["verification_ledger"]:
        evidence = row["evidence_pointer"] if row["evidence_pointer"] is not None else ""
        gap = row["gap"] if row["gap"] is not None else ""
        lines.append(
            "| "
            f"`{row['item_id']}` | "
            f"`{row['status']}` | "
            f"`{row['recorded']}` | "
            f"`{row['evidence_resolved']}` | "
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

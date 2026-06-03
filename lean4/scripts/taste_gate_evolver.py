#!/usr/bin/env python3
"""Monotonic counterexample-to-obligation helper for TasteGate meta obligations."""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path

import bedc_ci

STRUCTURAL_DISTINCTNESS_ID = "structural_distinctness"
STRUCTURAL_DISTINCTNESS_CRITERION = "carrier_faithfulness.cross_domain_canonical_payload_distinct"


def structural_distinctness_obligation(example: dict[str, object], *, added_ts: str) -> dict[str, object]:
    return {
        "id": STRUCTURAL_DISTINCTNESS_ID,
        "kind": "carrier_structure",
        "criterion": STRUCTURAL_DISTINCTNESS_CRITERION,
        "rejects_because": (
            "A carrier whose canonical payload is identical to a different-domain carrier "
            "is under-encoded: the carrier does not encode the distinction its name claims."
        ),
        "provenance": {
            "counterexample_class": "cross-domain canonical-payload collision",
            "finder": "carrier_faithfulness",
            "example_target": str(example.get("target") or ""),
            "example_prior": str(example.get("prior") or ""),
            "target_domain": str(example.get("target_domain") or ""),
            "prior_domain": str(example.get("prior_domain") or ""),
            "canonical_payload_digest": str(example.get("canonical_payload_digest") or ""),
            "evidence": "canonical_payload_equal",
            "boundary": "meta-level obligation; existing carriers are reported informationally",
        },
        "added_ts": added_ts,
    }


def _load_raw_registry(path: Path) -> dict[str, object]:
    if path.exists():
        raw = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(raw, dict):
            raw.setdefault("schema", "bedc.taste_obligation_registry")
            raw.setdefault("obligations", [])
            return raw
    return {
        "schema": "bedc.taste_obligation_registry",
        "semantics": (
            "Data-driven meta TasteGate obligations that supplement Lean "
            "ChapterTasteGate without replacing it."
        ),
        "monotonicity": (
            "Obligations add machine-checkable rejection criteria; they are not relaxed in place."
        ),
        "obligations": [],
    }


def evolve_structural_distinctness(
    *,
    registry_path: Path = bedc_ci.TASTE_OBLIGATION_REGISTRY_PATH,
    carrier_faithfulness: dict[str, object] | None = None,
    write: bool = True,
    added_ts: str | None = None,
) -> dict[str, object]:
    if carrier_faithfulness is None:
        audit = bedc_ci.audit_payload(full_radar_scan=True)
        carrier_faithfulness = audit["carrier_faithfulness"]
    cross_domain = carrier_faithfulness.get("cross_domain_under_encoding", []) or []
    if not isinstance(cross_domain, list):
        cross_domain = []
    evidence = [item for item in cross_domain if isinstance(item, dict)]
    before, diagnostics = bedc_ci.load_taste_obligations(registry_path)
    before_ids = {str(item.get("id") or "") for item in before}
    already_present = STRUCTURAL_DISTINCTNESS_ID in before_ids
    if not evidence:
        return {
            "schema": "bedc.taste_gate_evolver",
            "changed": False,
            "reason": "no independently verified cross-domain carrier collision",
            "before_count": len(before),
            "after_count": len(before),
            "diagnostics": diagnostics,
        }
    raw = _load_raw_registry(registry_path)
    entries = raw.get("obligations")
    if not isinstance(entries, list):
        entries = []
        raw["obligations"] = entries
    if not already_present:
        ts = added_ts or datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")
        entries.append(structural_distinctness_obligation(evidence[0], added_ts=ts))
        if write:
            registry_path.write_text(
                json.dumps(raw, indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
    after, after_diagnostics = bedc_ci.load_taste_obligations(registry_path)
    return {
        "schema": "bedc.taste_gate_evolver",
        "changed": not already_present,
        "reason": "structural_distinctness registered from cross-domain carrier collision",
        "monotonic": len(after) >= len(before),
        "before_count": len(before),
        "after_count": len(after),
        "evidence_count": len(evidence),
        "obligation_id": STRUCTURAL_DISTINCTNESS_ID,
        "diagnostics": diagnostics + after_diagnostics,
    }


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="TasteGate meta obligation evolver")
    p.add_argument("--registry", type=Path, default=bedc_ci.TASTE_OBLIGATION_REGISTRY_PATH)
    p.add_argument(
        "--carrier-faithfulness-json",
        type=Path,
        default=None,
        help="Read a carrier_faithfulness payload from JSON instead of running audit",
    )
    p.add_argument("--dry-run", action="store_true", help="Report without writing the registry")
    p.add_argument("--json", action="store_true", help="Emit JSON to stdout")
    return p


def main() -> int:
    args = parser().parse_args()
    carrier_faithfulness = None
    if args.carrier_faithfulness_json is not None:
        carrier_faithfulness = json.loads(
            args.carrier_faithfulness_json.read_text(encoding="utf-8")
        )
    payload = evolve_structural_distinctness(
        registry_path=args.registry,
        carrier_faithfulness=carrier_faithfulness,
        write=not args.dry_run,
    )
    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    else:
        print(
            "[taste-gate-evolver]"
            f" changed={payload['changed']}"
            f" before={payload['before_count']}"
            f" after={payload['after_count']}"
            f" monotonic={payload.get('monotonic', True)}"
        )
    return 0 if payload.get("monotonic", True) else 1


if __name__ == "__main__":
    raise SystemExit(main())

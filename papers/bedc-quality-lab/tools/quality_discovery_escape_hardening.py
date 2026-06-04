#!/usr/bin/env python3
"""Capture escaped pseudo discoveries as pointer-only gate hardening sidecars."""

from __future__ import annotations

import argparse
from copy import deepcopy
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
from typing import Any, Callable, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.research_discovery import assign_discovery_level
from bedc_quality_lab.verdict import POSITIVE_DISCOVERY, synthesize_certification_verdict
from tools import quality_discovery_adversarial_generator as adversarial_generator


TIMESTAMP = "2026-06-03T00:00:00+00:00"
REGISTRY_ARTIFACT_ID = "bedc-quality-lab:discovery-gate-escape-registry"
DEMOTIONS_ARTIFACT_ID = "bedc-quality-lab:discovery-gate-demotions"
REGISTRY_ARTIFACT = "reports/canonical/discovery_gate_escape_registry.json"
DEMOTIONS_ARTIFACT = "reports/canonical/discovery_gate_demotions.json"
CLAIM_VERDICTS_ARTIFACT = "reports/canonical/claim_verdicts.jsonl"
PRODUCER = "tools/quality_discovery_escape_hardening.py"
MAX_ESCAPE_ROWS = 32
MAX_ROWS_PER_KIND = 4
ACTIVE_KINDS = (
    "mechanism_ablation_fail_but_d5m_claim",
    "scale_only_overclaim",
)
DEFERRED_KINDS = (
    "single_threshold_positive_only",
    "metadata_leakage_detector",
)
ESCAPE_LEVELS = {"D4", "D5"}
NON_ESCAPE_TERMINAL_VERDICTS = {"rejected", "demoted", "ledger-only", "accepted"}
NON_ESCAPE_LEVELS = {"DN", "DR", "D0", "D1", "D2", "D3"}
FORBIDDEN_SIDECAR_FIELDS = {
    "certificate_payload",
    "evidence_payload",
    "pseudo_payload",
    "payload",
    "quality_scorecard",
    "scorecard",
}


@dataclass(frozen=True)
class PseudoCandidate:
    kind: str
    source_pointer: str
    recipe_pointer: str
    recipe_digest: str
    gate: str
    certificate_payload: dict[str, Any]
    evidence_payload: dict[str, Any]


Mutator = Callable[[dict[str, Any], dict[str, Any]], None]


def _base_candidate() -> tuple[dict[str, Any], dict[str, Any]]:
    certificate = {"main_claim_status": "observed-negative"}
    evidence = adversarial_generator._base_evidence()
    return certificate, evidence


def _mutate_mechanism_ablation_fail_but_d5m_claim(
    certificate: dict[str, Any],
    evidence: dict[str, Any],
) -> None:
    certificate["main_claim_status"] = "positive"
    certificate["gate_claim_pointer"] = "escape-recipe://mechanism-ablation-fail-but-d5m-claim"
    evidence["failed_gate"] = "mechanism-ablation"
    evidence["hardgate"] = {"status": "fail", "gate": "mechanism-ablation"}
    adversarial_generator._make_positive_main(evidence)


def _mutate_scale_only_overclaim(certificate: dict[str, Any], evidence: dict[str, Any]) -> None:
    certificate["main_claim_status"] = "positive"
    certificate["gate_claim_pointer"] = "escape-recipe://scale-only-overclaim"
    evidence["scale_surface"] = {
        "status": "scale-only",
        "mechanism_pointer": "reports/canonical/claim_verdicts.jsonl:scale-only",
    }
    adversarial_generator._make_positive_main(evidence)


_ACTIVE_MUTATORS: dict[str, tuple[str, Mutator]] = {
    "mechanism_ablation_fail_but_d5m_claim": (
        "recipe://discovery-gate-escape-hardening/mechanism-ablation-fail-but-d5m-claim",
        _mutate_mechanism_ablation_fail_but_d5m_claim,
    ),
    "scale_only_overclaim": (
        "recipe://discovery-gate-escape-hardening/scale-only-overclaim",
        _mutate_scale_only_overclaim,
    ),
}


def _stable_digest(value: Mapping[str, Any]) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _source_pointer(kind: str, claim_rows: list[Mapping[str, Any]]) -> str:
    if claim_rows:
        if kind == "mechanism_ablation_fail_but_d5m_claim":
            for index, row in enumerate(claim_rows):
                if row.get("claim_verdict") == "ledger_only_hardening_not_ready":
                    return f"{CLAIM_VERDICTS_ARTIFACT}:{index}"
        if kind == "scale_only_overclaim":
            for index, row in enumerate(claim_rows):
                if row.get("claim_verdict") == "ledger_only_hardening_not_ready":
                    return f"{CLAIM_VERDICTS_ARTIFACT}:{index}"
        return f"{CLAIM_VERDICTS_ARTIFACT}:0"
    return "reports/canonical/discovery_negative_witnesses.json:$.witnesses"


def _static_witness_audit() -> dict[str, Any]:
    rows = []
    for index, witness in enumerate(adversarial_generator.runtime_witnesses()):
        decision = adversarial_generator._terminal_decision(witness)
        projection = assign_discovery_level(decision)
        fail_closed = (
            decision["verdict"] in adversarial_generator.NON_POSITIVE_TERMINAL_VERDICTS
            and projection.discovery_level in adversarial_generator.NON_POSITIVE_LEVELS
        )
        rows.append(
            {
                "kind": witness.kind,
                "witness_pointer": f"{adversarial_generator.LEDGER_ARTIFACT}:$.witnesses[{index}]",
                "terminal_verdict": decision["verdict"],
                "discovery_level": projection.discovery_level,
                "fail_closed": fail_closed,
            }
        )
    return {
        "source": adversarial_generator.LEDGER_ARTIFACT,
        "expected_kind_count": len(adversarial_generator.EXPECTED_KINDS),
        "fail_closed": all(row["fail_closed"] for row in rows),
        "witnesses": rows,
    }


def _claim_verdict_rows(root: Path) -> list[dict[str, Any]]:
    path = root / CLAIM_VERDICTS_ARTIFACT
    if not path.exists():
        return []
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        if not isinstance(row, dict):
            raise ValueError(f"claim verdict row is not an object: {path}")
        rows.append(row)
    return rows


def pseudo_candidates(root: Path) -> list[PseudoCandidate]:
    claim_rows = _claim_verdict_rows(root)

    candidates = []
    for kind in ACTIVE_KINDS:
        recipe_pointer, mutate = _ACTIVE_MUTATORS[kind]
        certificate, evidence = _base_candidate()
        mutate(certificate, evidence)
        source_pointer = _source_pointer(kind, claim_rows)
        digest_source = {
            "kind": kind,
            "source_pointer": source_pointer,
            "recipe_pointer": recipe_pointer,
        }
        candidates.append(
            PseudoCandidate(
                kind=kind,
                source_pointer=source_pointer,
                recipe_pointer=recipe_pointer,
                recipe_digest=_stable_digest(digest_source),
                gate="discovery-gate",
                certificate_payload=certificate,
                evidence_payload=evidence,
            )
        )
    return candidates


def _gate_basis_summary(decision: Mapping[str, Any]) -> dict[str, Any]:
    basis = decision.get("evidence_basis")
    if not isinstance(basis, Mapping):
        basis = {}
    return {
        "main_claim_status": basis.get("main_claim_status"),
        "rejected": basis.get("rejected"),
        "rejection_reason": basis.get("rejection_reason"),
        "audit_status": basis.get("audit_status"),
        "downgraded": basis.get("downgraded"),
        "new_status": basis.get("new_status"),
        "scorecard_ready": basis.get("scorecard_ready"),
        "net_positive_signal": basis.get("net_positive_signal"),
        "main_surface_delta_count": basis.get("main_surface_delta_count"),
        "main_shift_information": basis.get("main_shift_information"),
        "main_structural_discovery": basis.get("main_structural_discovery"),
        "control_positive_discovery": basis.get("control_positive_discovery"),
        "failed_gate": basis.get("failed_gate"),
        "hardgate_status": basis.get("hardgate_status"),
        "forbidden_claim_term_hits": list(basis.get("forbidden_claim_term_hits") or []),
        "malformed_detail": basis.get("malformed_detail"),
    }


def _evaluate_candidate(candidate: PseudoCandidate) -> dict[str, Any]:
    decision = synthesize_certification_verdict(
        candidate.certificate_payload,
        candidate.evidence_payload,
        timestamp_iso=TIMESTAMP,
    )
    projection = assign_discovery_level(decision)
    escaped = decision["verdict"] == POSITIVE_DISCOVERY or projection.discovery_level in ESCAPE_LEVELS
    row = {
        "kind": candidate.kind,
        "source_pointer": candidate.source_pointer,
        "recipe_pointer": candidate.recipe_pointer,
        "recipe_digest": candidate.recipe_digest,
        "terminal_verdict": decision["verdict"],
        "terminal_reason": decision["reason"],
        "discovery_level": projection.discovery_level,
        "discovery_reasons": list(projection.reasons),
        "gate": candidate.gate,
        "gate_basis_summary": _gate_basis_summary(decision),
        "escaped": escaped,
        "escaped_positive_is_discovery_evidence": False,
    }
    if not escaped:
        if decision["verdict"] not in NON_ESCAPE_TERMINAL_VERDICTS:
            raise RuntimeError(f"{candidate.kind} produced unsupported non-escape verdict {decision['verdict']}")
        if projection.discovery_level not in NON_ESCAPE_LEVELS:
            raise RuntimeError(f"{candidate.kind} produced unsupported non-escape level {projection.discovery_level}")
    return row


def _admission_key(row: Mapping[str, Any]) -> tuple[str, str, str, str]:
    return (
        str(row["kind"]),
        str(row["source_pointer"]),
        str(row["recipe_pointer"]),
        str(row["recipe_digest"]),
    )


def _apply_escape_cap(rows: list[dict[str, Any]], *, max_escape_rows: int, max_rows_per_kind: int) -> list[dict[str, Any]]:
    sorted_rows = sorted(rows, key=_admission_key)
    if len(sorted_rows) > max_escape_rows:
        raise RuntimeError(f"escape registry overflow: {len(sorted_rows)} rows exceed max_escape_rows={max_escape_rows}")
    counts: dict[str, int] = {}
    for row in sorted_rows:
        kind = str(row["kind"])
        counts[kind] = counts.get(kind, 0) + 1
        if counts[kind] > max_rows_per_kind:
            raise RuntimeError(
                f"escape registry overflow: {counts[kind]} rows for {kind} exceed max_rows_per_kind={max_rows_per_kind}"
            )
    return sorted_rows


def assert_pointer_only_boundary(payload: Mapping[str, Any]) -> None:
    keys = set(_walk_keys(payload))
    forbidden = sorted(keys & FORBIDDEN_SIDECAR_FIELDS)
    if forbidden:
        raise RuntimeError(f"escape hardening sidecar contains forbidden payload keys: {forbidden}")
    text = json.dumps(payload, sort_keys=True)
    for forbidden_text in ("full-lejepa", "global-quality", "full-tensor-namecert", "llm-behavior"):
        if forbidden_text in text:
            raise RuntimeError(f"escape hardening sidecar contains forbidden positive claim term: {forbidden_text}")
    for forbidden_key in ("total_score", "rank", "grade", "hidden_cost_weight"):
        if forbidden_key in keys:
            raise RuntimeError(f"escape hardening sidecar contains forbidden score field: {forbidden_key}")


def _walk_keys(value: Any):
    if isinstance(value, Mapping):
        for key, cell in value.items():
            yield str(key)
            yield from _walk_keys(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _walk_keys(cell)


def build_escape_registry(
    *,
    root: Path | None = None,
    generated_at: str | None = None,
    max_escape_rows: int = MAX_ESCAPE_ROWS,
    max_rows_per_kind: int = MAX_ROWS_PER_KIND,
) -> dict[str, Any]:
    base = root or ROOT
    checked_rows = []
    escaped_rows = []
    for candidate in pseudo_candidates(base):
        row = _evaluate_candidate(candidate)
        if row["escaped"]:
            escaped_rows.append(row)
        else:
            checked_rows.append({key: value for key, value in row.items() if key != "escaped"})

    capped_escaped = _apply_escape_cap(
        escaped_rows,
        max_escape_rows=max_escape_rows,
        max_rows_per_kind=max_rows_per_kind,
    )
    payload = {
        "artifact_id": REGISTRY_ARTIFACT_ID,
        "generated_at": generated_at or datetime.now(timezone.utc).isoformat(),
        "status": "pointer-only",
        "producer": PRODUCER,
        "sidecar_policy": "not-in-CANONICAL_REPORTS",
        "source_policy": "read-only-existing-witnesses-verdict-projector-and-claim-verdict-rows",
        "escape_semantics": "escaped positive is gate failure evidence, not discovery evidence",
        "active_kinds": list(ACTIVE_KINDS),
        "deferred_kinds": [
            {
                "kind": "single_threshold_positive_only",
                "status": "deferred",
                "rationale": "awaits an independent single-threshold gate surface",
            },
            {
                "kind": "metadata_leakage_detector",
                "status": "deferred",
                "rationale": "awaits a positive metadata-consumption path",
            },
        ],
        "capacity": {
            "max_escape_rows": max_escape_rows,
            "max_rows_per_kind": max_rows_per_kind,
            "admission_order": ["kind", "source_pointer", "recipe_pointer", "recipe_digest"],
            "overflow_policy": "fail-closed",
        },
        "static_witness_audit": _static_witness_audit(),
        "checked_rows": sorted(checked_rows, key=_admission_key),
        "escaped_rows": capped_escaped,
        "audit": {
            "overflow": False,
            "escape_row_count": len(capped_escaped),
            "checked_row_count": len(checked_rows),
        },
    }
    assert_pointer_only_boundary(payload)
    return payload


def build_demotions(registry: Mapping[str, Any] | None = None, *, generated_at: str | None = None) -> dict[str, Any]:
    source = registry or build_escape_registry(generated_at=generated_at)
    rows = []
    for index, escaped in enumerate(source.get("escaped_rows", [])):
        if not isinstance(escaped, Mapping):
            continue
        rows.append(
            {
                "gate": escaped.get("gate"),
                "demote_status": "proposed",
                "basis_pointer": f"{REGISTRY_ARTIFACT}:$.escaped_rows[{index}]",
                "regression_pointer": (
                    "tests/test_discovery_gate_escape_hardening.py::"
                    f"test_active_pseudo_escape_rows_are_captured[{escaped.get('kind')}]"
                ),
                "source_policy": "witness-registry-and-tests-only",
            }
        )
    payload = {
        "artifact_id": DEMOTIONS_ARTIFACT_ID,
        "generated_at": generated_at or source.get("generated_at") or datetime.now(timezone.utc).isoformat(),
        "status": "pointer-only",
        "producer": PRODUCER,
        "source_registry": REGISTRY_ARTIFACT,
        "escape_semantics": "proposed demotions do not mutate source gates or synthesize positive discovery",
        "demotions": rows,
    }
    assert_pointer_only_boundary(payload)
    return payload


def _write_json(target: Path, payload: Mapping[str, Any]) -> None:
    target.parent.mkdir(parents=True, exist_ok=True)
    tmp = target.with_suffix(target.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(target)


def write_sidecars(*, root: Path | None = None, generated_at: str | None = None) -> tuple[dict[str, Any], dict[str, Any]]:
    base = root or ROOT
    registry_path = (base / REGISTRY_ARTIFACT).resolve()
    demotions_path = (base / DEMOTIONS_ARTIFACT).resolve()
    if registry_path != (base / REGISTRY_ARTIFACT).resolve():
        raise ValueError(f"registry may only write {REGISTRY_ARTIFACT}")
    if demotions_path != (base / DEMOTIONS_ARTIFACT).resolve():
        raise ValueError(f"demotions may only write {DEMOTIONS_ARTIFACT}")
    registry = build_escape_registry(root=base, generated_at=generated_at)
    demotions = build_demotions(registry, generated_at=registry["generated_at"])
    _write_json(registry_path, registry)
    _write_json(demotions_path, demotions)
    return registry, demotions


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=str(ROOT), help="Lab root containing reports/canonical.")
    args = parser.parse_args(argv)
    registry, demotions = write_sidecars(root=Path(args.root))
    print(
        f"wrote {len(registry['escaped_rows'])} escaped pseudo rows to {REGISTRY_ARTIFACT} "
        f"and {len(demotions['demotions'])} proposed demotions to {DEMOTIONS_ARTIFACT}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

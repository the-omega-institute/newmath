#!/usr/bin/env python3
"""Build a script-private revocation transition demo sidecar."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import sys
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.revocation import reevaluate_certified_claim

LOCAL_SCHEMA_ID = "bedc-quality-lab:revocation-demo-sidecar"
JSON_ARTIFACT = "runs/revocation_demo_sidecar.json"
MARKDOWN_ARTIFACT = "runs/revocation_demo_sidecar.md"
SOURCE_ARTIFACT = "reports/canonical/certificate-guided-discovery.json"
CANONICAL_ROLE = "sidecar_not_in_CANONICAL_REPORTS"
REVOCATION_POINTER = "bedc_quality_lab/revocation.py::reevaluate_certified_claim"
REQUIRED_SOURCE_KEYS = (
    "revocation_decision",
    "revocation_ledger",
    "claim_gate",
    "main_claim_status",
    "not_claimed",
    "generated_at",
)
FORBIDDEN_TERMS = ("full-lejepa", "global-quality", "full-tensor-namecert", "llm-behavior")


@dataclass(frozen=True)
class RevocationTransitionCase:
    case_id: str
    description: str
    source_pointers: dict[str, str]
    certificate_payload: dict | None
    fresh_projection_pointer: str
    expected_predicates: dict[str, object]
    demo_only: bool
    synthetic_certificate: bool
    not_scientific_result: bool


def _ptr(path: str) -> str:
    return f"{SOURCE_ARTIFACT}#{path}"


def load_source(root: Path) -> dict[str, Any]:
    payload = json.loads((root / SOURCE_ARTIFACT).read_text(encoding="utf-8"))
    missing = [key for key in REQUIRED_SOURCE_KEYS if key not in payload]
    if missing:
        raise ValueError(f"source artifact missing required keys: {', '.join(missing)}")
    return payload


def build_transition_cases(source: Mapping[str, Any]) -> list[RevocationTransitionCase]:
    _ = source
    return [
        RevocationTransitionCase(
            "current-no-certified-claim",
            "Current canonical payload has no certified positive claim to revoke.",
            {
                "decision": _ptr("$.revocation_decision"),
                "ledger": _ptr("$.revocation_ledger"),
                "status": _ptr("$.main_claim_status"),
                "not_claimed": _ptr("$.not_claimed"),
            },
            None,
            _ptr("$"),
            {"downgraded": False, "reason": "no-certified-claim", "ledger_rows": 0},
            True,
            False,
            True,
        ),
        RevocationTransitionCase(
            "synthetic-old-positive-tradeoff",
            "Synthetic positive certificate is checked against the current canonical projection.",
            {
                "function": REVOCATION_POINTER,
                "tradeoff": _ptr("$.claim_gate.training_audit_improvement_tradeoff"),
                "fresh_status": _ptr("$.main_claim_status"),
                "not_claimed": _ptr("$.not_claimed"),
            },
            {
                "main_claim_status": "positive",
                "demo_only": True,
                "synthetic_certificate": True,
                "not_scientific_result": True,
            },
            _ptr("$"),
            {
                "claim_gate.training_audit_improvement_tradeoff": True,
                "downgraded": True,
                "new_status": "audit-improvement-tradeoff",
                "ledger_row.event": "certified-claim-revocation",
            },
            True,
            True,
            True,
        ),
    ]


def _case_payload(case: RevocationTransitionCase, source: Mapping[str, Any]) -> dict[str, Any]:
    if case.certificate_payload is None:
        decision = dict(source["revocation_decision"])
        ledger_rows = list(source["revocation_ledger"])
    else:
        decision = reevaluate_certified_claim(
            case.certificate_payload,
            source,
            timestamp_iso=str(source["generated_at"]),
        )
        row = decision.get("ledger_row")
        ledger_rows = [dict(row)] if isinstance(row, Mapping) and row else []
    return {
        "case_id": case.case_id,
        "demo_only": case.demo_only,
        "synthetic_certificate": case.synthetic_certificate,
        "not_scientific_result": case.not_scientific_result,
        "source_pointers": case.source_pointers,
        "fresh_projection_pointer": case.fresh_projection_pointer,
        "expected_predicates": case.expected_predicates,
        "decision": decision,
        "ledger_rows": ledger_rows,
    }


def _observed(case: Mapping[str, Any], source: Mapping[str, Any]) -> dict[str, Any]:
    decision = case["decision"]
    rows = case["ledger_rows"]
    return {
        "downgraded": decision.get("downgraded"),
        "reason": decision.get("reason"),
        "ledger_rows": len(rows),
        "claim_gate.training_audit_improvement_tradeoff": source["claim_gate"].get(
            "training_audit_improvement_tradeoff"
        ),
        "new_status": decision.get("new_status"),
        "ledger_row.event": rows[0].get("event") if rows else None,
    }


def build_payload(source: Mapping[str, Any]) -> dict[str, Any]:
    cases = [_case_payload(case, source) for case in build_transition_cases(source)]
    for case in cases:
        observed = _observed(case, source)
        mismatches = {
            key: {"expected": value, "actual": observed.get(key)}
            for key, value in case["expected_predicates"].items()
            if observed.get(key) != value
        }
        if mismatches:
            raise ValueError(f"revocation demo predicates failed: {mismatches}")
    payload = {
        "schema_id": LOCAL_SCHEMA_ID,
        "generated_at": source["generated_at"],
        "canonical_role": CANONICAL_ROLE,
        "source_artifact": SOURCE_ARTIFACT,
        "source_generated_at": source["generated_at"],
        "transition_cases": cases,
        "not_claimed": list(source["not_claimed"])
        + [
            "Current canonical run has no real downgrade.",
            "Synthetic positive transition is a demo harness only, not a scientific result.",
        ],
        "forbidden_terms_absent": {term: True for term in FORBIDDEN_TERMS},
    }
    hits = [term for term in FORBIDDEN_TERMS if term in render_markdown(payload).lower()]
    if hits:
        raise ValueError(f"forbidden overclaim terms present: {', '.join(hits)}")
    return payload


def render_markdown(payload: Mapping[str, Any]) -> str:
    rows = [
        "# Revocation Demo Sidecar",
        "",
        f"Source artifact: `{payload['source_artifact']}`",
        f"Source generated at: `{payload['source_generated_at']}`",
        "",
        "| Case | Source pointers | Expected predicates | Decision |",
        "| --- | --- | --- | --- |",
    ]
    for case in payload["transition_cases"]:
        pointers = "<br>".join(f"`{key}`: `{value}`" for key, value in case["source_pointers"].items())
        expected = "<br>".join(f"`{key}` = `{value}`" for key, value in case["expected_predicates"].items())
        decision = case["decision"]
        result = (
            f"`downgraded` = `{decision.get('downgraded')}`<br>"
            f"`reason` = `{decision.get('reason')}`<br>`ledger_rows` = `{len(case['ledger_rows'])}`"
        )
        rows.append(f"| `{case['case_id']}` | {pointers} | {expected} | {result} |")
    rows += [
        "",
        "## Not-Claimed Boundary",
        "",
        "The current canonical run has no real downgrade.",
        "The synthetic positive transition is a demo harness only and is not a scientific result.",
    ]
    rows += [f"- {item}" for item in payload["not_claimed"]]
    return "\n".join(rows) + "\n"


def write_artifacts(payload: Mapping[str, Any], *, root: Path) -> tuple[Path, Path]:
    json_path = root / JSON_ARTIFACT
    markdown_path = root / MARKDOWN_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(render_markdown(payload), encoding="utf-8")
    return json_path, markdown_path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default=".")
    args = parser.parse_args(argv)
    try:
        json_path, markdown_path = write_artifacts(
            build_payload(load_source(Path(args.root))),
            root=Path(args.root),
        )
    except Exception as exc:
        print(f"revocation demo sidecar failed: {exc}", file=sys.stderr)
        return 1
    print(f"wrote {json_path}")
    print(f"wrote {markdown_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

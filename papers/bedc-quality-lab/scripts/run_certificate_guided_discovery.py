#!/usr/bin/env python3
"""Project certificate-guided training into discovery predicates."""

import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.audit import audit_certified_claim
from bedc_quality_lab.claim_projection import (
    AFTER_ROLE,
    BEFORE_ROLE,
    CONTROL_ROLE,
    METRIC_NAMES,
    _main_claim_status,
    _project_pair,
    project_certificate_guided_claim,
    require_certificate_guided_projection_source,
)
from bedc_quality_lab.revocation import reevaluate_certified_claim

SOURCE_JSON_ARTIFACT = "reports/certificate_guided_training.json"
SOURCE_REPORT_ARTIFACT = "reports/certificate_guided_training.md"
JSON_ARTIFACT = "reports/certificate_guided_discovery.json"
REPORT_ARTIFACT = "reports/certificate_guided_discovery.md"

def _load_payload(path: Path | None = None) -> dict[str, Any]:
    payload_path = ROOT / SOURCE_JSON_ARTIFACT if path is None else path
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    require_certificate_guided_projection_source(payload)
    return payload

def _verdict_payload(payload: dict[str, Any]) -> dict[str, Any]:
    projection = project_certificate_guided_claim(payload)
    main = projection.main_verdict
    control = projection.matched_random_baseline
    main_claim_status = projection.main_claim_status
    generated_at = datetime.now(timezone.utc).isoformat()
    fresh_projection = projection.to_dict()
    fresh_projection.update({
        "generated_at": generated_at,
    })
    revocation_decision = reevaluate_certified_claim(
        payload.get("certified_claim"),
        fresh_projection,
        timestamp_iso=fresh_projection["generated_at"],
    )
    audit_decision = audit_certified_claim(
        payload.get("certified_claim"),
        payload,
        timestamp_iso=generated_at,
    )
    final_main_claim_status = (
        revocation_decision["new_status"] if revocation_decision["downgraded"] else main_claim_status
    )
    return {
        "artifact": JSON_ARTIFACT,
        "source_artifacts": {
            "source_json_artifact": SOURCE_JSON_ARTIFACT,
            "source_report_artifact": SOURCE_REPORT_ARTIFACT,
            "source_runner": payload["source_artifacts"]["generation_script"],
        },
        "report": REPORT_ARTIFACT,
        "projection_script": "scripts/run_certificate_guided_discovery.py",
        "generated_from": {"artifact": SOURCE_JSON_ARTIFACT, "generated_at": payload.get("generated_at")},
        "generated_at": generated_at,
        "arms": [{"role": record["role"], "candidate_id": record["candidate_id"]} for record in payload["records"]],
        "verdicts": [main],
        "surface_delta_count": main["surface_delta_count"],
        "positive_discovery": main["positive_discovery"],
        "net_information": main["net_information"],
        "main_claim_status": final_main_claim_status,
        "claim_gate": fresh_projection["claim_gate"],
        "audit_decision": audit_decision,
        "audit_ledger": [audit_decision["audit_row"]],
        "revocation_decision": revocation_decision,
        "revocation_ledger": [revocation_decision["ledger_row"]] if revocation_decision["downgraded"] else [],
        "matched_random_baseline": control,
        "not_claimed": list(payload.get("not_claimed", []))
        + [
            "positive discovery is not claimed unless classifier surface delta, imported positive_discovery, positive net information, and training positive quality gate all hold"
        ],
        "applicability_boundary": {
            "claimed_scope": "certificate-guided versus vanilla projection on the existing finite lab report",
            "not_claimed": ["formal-bedc-closure", "global optimizer behavior", "new predicate formula"],
        },
    }

def _write_payload(payload: dict[str, Any]) -> None:
    json_path = ROOT / JSON_ARTIFACT
    report_path = ROOT / REPORT_ARTIFACT
    verdict = payload["verdicts"][0]
    baseline = payload["matched_random_baseline"]
    deltas = verdict["deltas"]
    net = float(payload["net_information"])
    net_line = (
        f"- Net information cleared zero: `{net:.6f}`."
        if net > 0.0
        else f"- Net information did not clear zero: `{net:.6f}`."
    )
    lines = [
        "# Certificate-Guided Discovery Projection",
        "",
        f"- Source JSON artifact: `{payload['source_artifacts']['source_json_artifact']}`",
        f"- Projection script: `{payload['projection_script']}`",
        f"- Main claim status: `{payload['main_claim_status']}`",
        f"- Four-gate positive: `{str(bool(payload['claim_gate']['positive_discovery_four_gate'])).lower()}`",
        f"- Training quality gate: `{str(bool(payload['claim_gate']['training_positive_quality_improvement'])).lower()}`",
        f"- Gate blockers: `{', '.join(payload['claim_gate']['blockers']) or 'none'}`",
        f"- Audit status: `{payload['audit_decision']['audit_status']}`",
        f"- Audit reason: `{payload['audit_decision']['reason']}`",
        f"- Audit ledger rows: `{len(payload['audit_ledger'])}`",
        f"- Revocation downgraded: `{str(bool(payload['revocation_decision']['downgraded'])).lower()}`",
        f"- Revocation reason: `{payload['revocation_decision']['reason']}`",
        f"- Revocation ledger rows: `{len(payload['revocation_ledger'])}`",
        f"- Verdict: `{verdict['verdict']}` / net `{float(payload['net_information']):.6f}` / positive `{str(payload['positive_discovery']).lower()}`",
        f"- Matched-random baseline: `{baseline['verdict']}` / net `{float(baseline['net_information']):.6f}` / positive `{str(baseline['positive_discovery']).lower()}`",
        f"- Benefit declined by `{float(deltas['benefit_delta']):.6f}` under the shared cost protocol.",
        f"- Debt declined by `{float(deltas['debt_delta']):.6f}` under the shared cost protocol.",
        net_line,
        f"- Quality-q delta: `{float(deltas['quality_q_delta']):.6f}`.",
        f"- Not claimed: `{'; '.join(payload['not_claimed'])}`",
        "",
    ]
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text("\n".join(lines), encoding="utf-8")

def main() -> None:
    payload = _verdict_payload(_load_payload())
    _write_payload(payload)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"verdict {payload['verdicts'][0]['verdict']}")

if __name__ == "__main__":
    main()

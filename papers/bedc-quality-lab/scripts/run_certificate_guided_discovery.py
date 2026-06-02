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

from bedc_quality_lab.classifier_shift import ClassifierPassage, ClassifierState, classifier_surface_delta, shift_information, structural_discovery
from bedc_quality_lab.discovery import DiscoveryClaim, net_information, positive_discovery
from bedc_quality_lab.ledger import LedgerRowKey

SOURCE_JSON_ARTIFACT = "reports/certificate_guided_training.json"
SOURCE_REPORT_ARTIFACT = "reports/certificate_guided_training.md"
JSON_ARTIFACT = "reports/certificate_guided_discovery.json"
REPORT_ARTIFACT = "reports/certificate_guided_discovery.md"
BEFORE_ROLE = "before"
AFTER_ROLE = "after"
CONTROL_ROLE = "control"
METRIC_NAMES = ("quality_q", "quality_benefit", "quality_cost", "quality_debt", "certificate_guided_loss", "unlogged_error_rate", "critical_unlogged_error_rate")

def _main_claim_status(row: dict[str, Any], training_gate: dict[str, Any]) -> str:
    if (
        row["surface_delta_count"]
        and row["positive_discovery"]
        and float(row["net_information"]) > 0.0
        and training_gate.get("positive_quality_improvement") is True
    ):
        return "positive"
    if row["surface_delta_count"] and row["net_information"] <= 0.0:
        return "observed-negative"
    return "mixed"

def _require_paired_quality_ci(payload: dict[str, Any]) -> dict[str, Any]:
    try:
        ci = payload["paired_delta_ci"]["after_minus_before"]["quality_q_delta"]
    except KeyError as exc:
        raise ValueError("certificate-guided payload must contain paired quality_q CI evidence") from exc
    required = {"status", "n", "mean", "ci95_low", "ci95_high"}
    missing = required - set(ci)
    if missing:
        raise ValueError(f"certificate-guided payload paired quality_q CI missing keys: {sorted(missing)}")
    return ci

def _load_payload(path: Path | None = None) -> dict[str, Any]:
    payload_path = ROOT / SOURCE_JSON_ARTIFACT if path is None else path
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    if "claim_gate" not in payload:
        raise ValueError("certificate-guided payload must contain claim_gate")
    if "positive_quality_improvement" not in payload["claim_gate"]:
        raise ValueError("certificate-guided claim_gate must contain positive_quality_improvement")
    _require_paired_quality_ci(payload)
    roles = {record.get("role") for record in payload.get("records", [])}
    if {BEFORE_ROLE, AFTER_ROLE, CONTROL_ROLE} - roles:
        raise ValueError("certificate-guided payload must contain before, after, and control records")
    if payload.get("result", {}).get("ledger_rows_written") is not True:
        raise ValueError("certificate-guided payload must record ledger rows")
    if payload.get("result", {}).get("shared_cost_protocol_name") is not True:
        raise ValueError("certificate-guided payload must share a cost protocol")
    for record in payload["records"]:
        if not record.get("ledger_rows"):
            raise ValueError(f"record lacks ledger rows: {record.get('role')}")
    return payload

def _mean_record(records: list[dict[str, Any]], role: str) -> dict[str, Any]:
    role_records = [record for record in records if record["role"] == role]
    if not role_records:
        raise ValueError(f"missing record role: {role}")
    first = role_records[0]
    aggregate = dict(first)
    for name in METRIC_NAMES:
        aggregate[name] = sum(float(record[name]) for record in role_records) / len(role_records)
    aggregate["seed"] = "paired-mean"
    aggregate["run_id"] = f"certificate-guided-{role}-paired-mean"
    aggregate["ledger_rows"] = first["ledger_rows"]
    return aggregate

def _project_pair(payload: dict[str, Any], before_role: str, after_role: str) -> dict[str, Any]:
    before = _mean_record(payload["records"], before_role)
    after = _mean_record(payload["records"], after_role)
    source_ids = frozenset(f"metric:{name}" for name in METRIC_NAMES)

    def relation(record: dict[str, Any]) -> frozenset[tuple[str, str, str]]:
        return frozenset((f"metric:{name}", f"metric:{name}", f"{float(record[name]):.12g}") for name in METRIC_NAMES)
    surface = frozenset((source_id, source_id) for source_id in source_ids)
    ledger_rows = frozenset(LedgerRowKey("classifier", f"{left}->{right}") for left, right in surface)
    state_args = {"source_ids": source_ids, "verification_status": "artifact-checked", "record_count": len(source_ids), "feature_count": len(METRIC_NAMES), "notation": "metric-self-pair"}
    cert = {"cert_status": "certified", "source_artifact": SOURCE_JSON_ARTIFACT}
    source = ClassifierState(pattern_id=f"certificate-guided-{before_role}-{before['candidate_id']}", ledger_policy=frozenset(), relation=relation(before), certificate=cert, surface_used=frozenset(), **state_args)
    target = ClassifierState(pattern_id=f"certificate-guided-{after_role}-{after['candidate_id']}", ledger_policy=ledger_rows, relation=relation(after), certificate=cert, surface_used=surface, **state_args)
    passage = ClassifierPassage(source=source, target=target, recorded_rows=ledger_rows)
    delta_count = len(classifier_surface_delta(passage))
    deltas = payload["deltas"][f"{after_role}_minus_{before_role}"]
    benefit = {"quality_benefit_gain": max(0.0, float(deltas["benefit_delta"])), "quality_debt_reduction": max(0.0, -float(deltas["debt_delta"]))}
    score = {"quality_cost_increase": max(0.0, float(deltas["cost_delta"])), "projection_surface_rows": 0.01 * delta_count}
    debt = {"quality_benefit_loss": max(0.0, -float(deltas["benefit_delta"])), "quality_debt_increase": max(0.0, float(deltas["debt_delta"]))}
    claim = DiscoveryClaim(
        passage=passage,
        benefit_terms=benefit,
        score_terms=score,
        debt_terms=debt,
        ledger_required_rows=ledger_rows,
        ledger_recorded_rows=ledger_rows,
        public_cost_protocol=True,
        scope_sealed=True,
        not_claimed_boundary=frozenset({"formal-bedc-closure", "global-optimizer-claim"}),
        benefit_modes=frozenset(benefit),
        reproducible_evidence=True,
    )
    return {"before": before, "after": after, "passage": passage, "claim": claim, "deltas": deltas}

def _verdict_payload(payload: dict[str, Any]) -> dict[str, Any]:
    def row(before_role: str, after_role: str) -> dict[str, Any]:
        projection = _project_pair(payload, before_role, after_role)
        passage = projection["passage"]
        claim = projection["claim"]
        delta = classifier_surface_delta(passage)
        structural = structural_discovery(passage)
        positive = positive_discovery(claim)
        net = net_information(claim)
        verdict = "positive" if positive else "negative" if structural and delta and net <= 0.0 else "compression"
        return {"before_role": before_role, "after_role": after_role, "before_candidate_id": projection["before"]["candidate_id"], "after_candidate_id": projection["after"]["candidate_id"], "surface_delta_count": len(delta), "surface_delta": [list(pair) for pair in sorted(delta)], "shift_information": shift_information(passage), "structural_discovery": structural, "net_information": net, "positive_discovery": positive, "verdict": verdict, "deltas": projection["deltas"], "benefit_terms": dict(claim.benefit_terms), "score_terms": dict(claim.score_terms), "debt_terms": dict(claim.debt_terms)}

    main = row(BEFORE_ROLE, AFTER_ROLE)
    control = row(BEFORE_ROLE, CONTROL_ROLE)
    training_gate = payload["claim_gate"]
    main_claim_status = _main_claim_status(main, training_gate)
    gate_blockers = []
    if not main["surface_delta_count"]:
        gate_blockers.append("empty-classifier-surface-delta")
    if main["positive_discovery"] is not True:
        gate_blockers.append("imported-positive-discovery-false")
    if float(main["net_information"]) <= 0.0:
        gate_blockers.append("net-information-nonpositive")
    if training_gate.get("positive_quality_improvement") is not True:
        gate_blockers.append("training-positive-quality-gate-false")
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
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "arms": [{"role": record["role"], "candidate_id": record["candidate_id"]} for record in payload["records"]],
        "verdicts": [main],
        "surface_delta_count": main["surface_delta_count"],
        "positive_discovery": main["positive_discovery"],
        "net_information": main["net_information"],
        "main_claim_status": main_claim_status,
        "claim_gate": {
            "training_positive_quality_improvement": bool(training_gate.get("positive_quality_improvement")),
            "training_quality_q_ci95_low": training_gate.get("quality_q_ci95_low"),
            "training_paired_ci_status": training_gate.get("paired_ci_status"),
            "positive_discovery_four_gate": main_claim_status == "positive",
            "blockers": gate_blockers,
        },
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

"""Certificate-guided claim projection."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any, Mapping

from bedc_quality_lab.classifier_shift import (
    ClassifierPassage,
    ClassifierState,
    classifier_surface_delta,
    shift_information,
    structural_discovery,
)
from bedc_quality_lab.discovery import DiscoveryClaim, net_information, positive_discovery
from bedc_quality_lab.ledger import LedgerRowKey


SOURCE_JSON_ARTIFACT = "reports/certificate_guided_training.json"
BEFORE_ROLE = "before"
AFTER_ROLE = "after"
CONTROL_ROLE = "control"
METRIC_NAMES = (
    "quality_q",
    "quality_benefit",
    "quality_cost",
    "quality_debt",
    "certificate_guided_loss",
    "unlogged_error_rate",
    "critical_unlogged_error_rate",
)


@dataclass(frozen=True)
class ClaimProjection:
    main_claim_status: str
    claim_gate: dict[str, Any]
    main_verdict: dict[str, Any]
    matched_random_baseline: dict[str, Any]
    evidence_basis: dict[str, Any]

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def require_certificate_guided_projection_source(payload: Mapping[str, Any]) -> None:
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


def _main_claim_status(row: Mapping[str, Any], training_gate: Mapping[str, Any]) -> str:
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


def _require_paired_quality_ci(payload: Mapping[str, Any]) -> Mapping[str, Any]:
    try:
        ci = payload["paired_delta_ci"]["after_minus_before"]["quality_q_delta"]
    except KeyError as exc:
        raise ValueError("certificate-guided payload must contain paired quality_q CI evidence") from exc
    required = {"status", "n", "mean", "ci95_low", "ci95_high"}
    missing = required - set(ci)
    if missing:
        raise ValueError(f"certificate-guided payload paired quality_q CI missing keys: {sorted(missing)}")
    return ci


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


def _project_pair(payload: Mapping[str, Any], before_role: str, after_role: str) -> dict[str, Any]:
    records = list(payload["records"])
    before = _mean_record(records, before_role)
    after = _mean_record(records, after_role)
    source_ids = frozenset(f"metric:{name}" for name in METRIC_NAMES)

    def relation(record: Mapping[str, Any]) -> frozenset[tuple[str, str, str]]:
        return frozenset((f"metric:{name}", f"metric:{name}", f"{float(record[name]):.12g}") for name in METRIC_NAMES)

    surface = frozenset((source_id, source_id) for source_id in source_ids)
    ledger_rows = frozenset(LedgerRowKey("classifier", f"{left}->{right}") for left, right in surface)
    state_args = {
        "source_ids": source_ids,
        "verification_status": "artifact-checked",
        "record_count": len(source_ids),
        "feature_count": len(METRIC_NAMES),
        "notation": "metric-self-pair",
    }
    cert = {"cert_status": "certified", "source_artifact": SOURCE_JSON_ARTIFACT}
    source = ClassifierState(
        pattern_id=f"certificate-guided-{before_role}-{before['candidate_id']}",
        ledger_policy=frozenset(),
        relation=relation(before),
        certificate=cert,
        surface_used=frozenset(),
        **state_args,
    )
    target = ClassifierState(
        pattern_id=f"certificate-guided-{after_role}-{after['candidate_id']}",
        ledger_policy=ledger_rows,
        relation=relation(after),
        certificate=cert,
        surface_used=surface,
        **state_args,
    )
    passage = ClassifierPassage(source=source, target=target, recorded_rows=ledger_rows)
    delta_count = len(classifier_surface_delta(passage))
    deltas = payload["deltas"][f"{after_role}_minus_{before_role}"]
    benefit = {
        "quality_benefit_gain": max(0.0, float(deltas["benefit_delta"])),
        "quality_debt_reduction": max(0.0, -float(deltas["debt_delta"])),
    }
    score = {
        "quality_cost_increase": max(0.0, float(deltas["cost_delta"])),
        "projection_surface_rows": 0.01 * delta_count,
    }
    debt = {
        "quality_benefit_loss": max(0.0, -float(deltas["benefit_delta"])),
        "quality_debt_increase": max(0.0, float(deltas["debt_delta"])),
    }
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


def _verdict_row(payload: Mapping[str, Any], before_role: str, after_role: str) -> dict[str, Any]:
    projection = _project_pair(payload, before_role, after_role)
    passage = projection["passage"]
    claim = projection["claim"]
    delta = classifier_surface_delta(passage)
    structural = structural_discovery(passage)
    positive = positive_discovery(claim)
    net = net_information(claim)
    verdict = "positive" if positive else "negative" if structural and delta and net <= 0.0 else "compression"
    return {
        "before_role": before_role,
        "after_role": after_role,
        "before_candidate_id": projection["before"]["candidate_id"],
        "after_candidate_id": projection["after"]["candidate_id"],
        "surface_delta_count": len(delta),
        "surface_delta": [list(pair) for pair in sorted(delta)],
        "shift_information": shift_information(passage),
        "structural_discovery": structural,
        "net_information": net,
        "positive_discovery": positive,
        "verdict": verdict,
        "deltas": projection["deltas"],
        "benefit_terms": dict(claim.benefit_terms),
        "score_terms": dict(claim.score_terms),
        "debt_terms": dict(claim.debt_terms),
    }


def _gate_blockers(main: Mapping[str, Any], training_gate: Mapping[str, Any]) -> list[str]:
    blockers = []
    if not main["surface_delta_count"]:
        blockers.append("empty-classifier-surface-delta")
    if main["positive_discovery"] is not True:
        blockers.append("imported-positive-discovery-false")
    if float(main["net_information"]) <= 0.0:
        blockers.append("net-information-nonpositive")
    if training_gate.get("positive_quality_improvement") is not True:
        blockers.append("training-positive-quality-gate-false")
    return blockers


def _evidence_basis(payload: Mapping[str, Any], main: Mapping[str, Any], baseline: Mapping[str, Any]) -> dict[str, Any]:
    ci = _require_paired_quality_ci(payload)
    return {
        "source_schema_id": payload.get("schema_id"),
        "source_artifact": payload.get("artifact"),
        "record_roles": [record.get("role") for record in payload.get("records", [])],
        "metric_names": list(METRIC_NAMES),
        "main_pair": [main["before_role"], main["after_role"]],
        "baseline_pair": [baseline["before_role"], baseline["after_role"]],
        "paired_quality_q_ci": {
            "status": ci["status"],
            "n": ci["n"],
            "mean": ci["mean"],
            "ci95_low": ci["ci95_low"],
            "ci95_high": ci["ci95_high"],
        },
        "training_claim_gate_keys": sorted(payload.get("claim_gate", {}).keys()),
    }


def project_certificate_guided_claim(payload: Mapping[str, Any]) -> ClaimProjection:
    require_certificate_guided_projection_source(payload)
    main = _verdict_row(payload, BEFORE_ROLE, AFTER_ROLE)
    baseline = _verdict_row(payload, BEFORE_ROLE, CONTROL_ROLE)
    training_gate = payload["claim_gate"]
    main_claim_status = _main_claim_status(main, training_gate)
    claim_gate = {
        "training_positive_quality_improvement": bool(training_gate.get("positive_quality_improvement")),
        "training_quality_q_ci95_low": training_gate.get("quality_q_ci95_low"),
        "training_paired_ci_status": training_gate.get("paired_ci_status"),
        "training_audit_improvement_tradeoff": bool(training_gate.get("audit_improvement_tradeoff")),
        "positive_discovery_four_gate": main_claim_status == "positive",
        "blockers": _gate_blockers(main, training_gate),
    }
    return ClaimProjection(
        main_claim_status=main_claim_status,
        claim_gate=claim_gate,
        main_verdict=main,
        matched_random_baseline=baseline,
        evidence_basis=_evidence_basis(payload, main, baseline),
    )

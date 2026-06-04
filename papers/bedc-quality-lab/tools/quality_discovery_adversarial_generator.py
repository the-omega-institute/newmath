#!/usr/bin/env python3
"""Generate fail-closed pseudo discovery witnesses for the discovery gate."""

from __future__ import annotations

import argparse
from copy import deepcopy
from dataclasses import dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Any, Callable, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.research_discovery import assign_discovery_level
from bedc_quality_lab.schema import SCHEMA_ID
from bedc_quality_lab.verdict import QUALITY_SCORECARD_METRICS, synthesize_certification_verdict
from scripts import run_certificate_guided_training as training_runner


TIMESTAMP = "2026-06-03T00:00:00+00:00"
ARTIFACT_ID = "bedc-quality-lab:discovery-negative-witnesses"
LEDGER_ARTIFACT = "reports/canonical/discovery_negative_witnesses.json"
EXPECTED_KINDS = (
    "classifier_surface_delta_zero",
    "matched_control_positive",
    "hidden_debt_positive",
    "cost_protocol_missing",
    "scorecard_not_ready",
    "forbidden_inference_column",
    "benefit_debt_tradeoff",
    "fresh_claim_downgrade",
)
FORBIDDEN_LEDGER_FIELDS = {
    "schema_id",
    "report_schema_id",
    "report_kind",
    "SCHEMA_ID",
}
METRIC_NAMES = (
    "quality_q",
    "quality_benefit",
    "quality_cost",
    "quality_debt",
    "certificate_guided_loss",
    "unlogged_error_rate",
    "critical_unlogged_error_rate",
)
NON_POSITIVE_TERMINAL_VERDICTS = {"rejected", "demoted", "ledger-only"}
NON_POSITIVE_LEVELS = {"DN", "DR", "D0", "D1", "D2", "D3"}
REQUIRED_GAP_FIELDS = (
    "bedc_gap_field",
    "violated_principle",
    "required_ledger_row",
    "demotion",
    "regression_test",
)


@dataclass(frozen=True)
class RuntimeWitness:
    kind: str
    soundness: str
    certificate_payload: dict[str, Any]
    evidence_payload: dict[str, Any]


Mutator = Callable[[dict[str, Any], dict[str, Any]], None]


@dataclass(frozen=True)
class WitnessGapContract:
    bedc_gap_field: str
    violated_principle: str
    required_ledger_row: str
    demotion: str
    regression_test: str


WITNESS_GAP_CONTRACTS: dict[str, WitnessGapContract] = {
    "classifier_surface_delta_zero": WitnessGapContract(
        bedc_gap_field="ClassifierSpec gap",
        violated_principle="Classifier movement requires a nonzero surface delta before a discovery claim can leave observation status.",
        required_ledger_row="ClassifierSpec row recording the classifier surface delta and rejected zero-delta projection.",
        demotion="rejected/DN",
        regression_test="tests/test_certificate_guided_discovery.py::test_nonpositive_net_information_forces_non_positive_discovery_on_classifier_surface",
    ),
    "matched_control_positive": WitnessGapContract(
        bedc_gap_field="Control / Intervention ledger gap",
        violated_principle="A matched control with the same positive signal blocks attribution to the intervention.",
        required_ledger_row="Control ledger row comparing treatment and matched control under the same cost and split protocol.",
        demotion="rejected/DN",
        regression_test="tests/test_gap_head_discovery.py::test_control_positive_forces_unresolved_main_claim",
    ),
    "hidden_debt_positive": WitnessGapContract(
        bedc_gap_field="LedgerPolicy gap",
        violated_principle="A positive certificate cannot hide debt behind an observed-negative projection.",
        required_ledger_row="LedgerPolicy row binding positive status to visible debt and audit-improvement tradeoff status.",
        demotion="demoted/DR",
        regression_test="tests/test_demote_thesis_invariant_audit.py::test_positive_tradeoff_fixture_is_caught",
    ),
    "cost_protocol_missing": WitnessGapContract(
        bedc_gap_field="CostProtocol gap",
        violated_principle="A discovery projection is malformed when the payload does not share a cost protocol.",
        required_ledger_row="CostProtocol row naming the shared protocol that prices benefit, cost, and debt cells.",
        demotion="rejected/DN",
        regression_test="tests/test_certificate_guided_discovery.py::test_loader_rejects_when_shared_cost_protocol_name_not_true",
    ),
    "scorecard_not_ready": WitnessGapContract(
        bedc_gap_field="ClosureStatus gap",
        violated_principle="A not-ready scorecard cannot certify a positive discovery terminal status.",
        required_ledger_row="ClosureStatus row recording quality scorecard readiness for every required metric.",
        demotion="ledger-only/D1",
        regression_test="tests/test_verdict.py::test_well_formed_not_ready_scorecard_goes_to_ledger_only",
    ),
    "forbidden_inference_column": WitnessGapContract(
        bedc_gap_field="SourceSpec contamination",
        violated_principle="A source specification with forbidden inference terms cannot support a positive claim.",
        required_ledger_row="SourceSpec row listing forbidden claim-term hits and the contaminated source cell.",
        demotion="rejected/DN",
        regression_test="tests/test_rejection.py::test_rejects_forbidden_positive_claim_term_from_shared_owner",
    ),
    "benefit_debt_tradeoff": WitnessGapContract(
        bedc_gap_field="Positive information gap",
        violated_principle="A benefit claim with unresolved debt tradeoff is audit improvement, not positive discovery.",
        required_ledger_row="Positive-information row separating quality benefit from debt tradeoff status.",
        demotion="demoted/DR",
        regression_test="tests/test_certificate_guided_discovery.py::test_tradeoff_training_payload_keeps_discovery_main_claim_non_positive",
    ),
    "fresh_claim_downgrade": WitnessGapContract(
        bedc_gap_field="Revocation ledger gap",
        violated_principle="Fresh weak evidence must revoke the earlier positive status instead of preserving it.",
        required_ledger_row="Revocation ledger row naming the stale certificate, fresh evidence, and downgraded status.",
        demotion="demoted/DR",
        regression_test="tests/test_research_discovery.py::test_hg_dl_4_revocation_decision_is_revoked_discovery",
    ),
}


def _scorecard(status: str = "ready") -> dict[str, Any]:
    return {
        "artifact_id": "bedc-quality-lab:quality-scorecard",
        "generated_at": TIMESTAMP,
        "rows": [
            {
                "metric": metric,
                "status": status,
                "value": index,
            }
            for index, metric in enumerate(QUALITY_SCORECARD_METRICS)
        ],
    }


def _base_evidence(*, scorecard_status: str = "ready") -> dict[str, Any]:
    payload = training_runner._payload()
    payload["schema_id"] = SCHEMA_ID
    payload["quality_scorecard"] = _scorecard(status=scorecard_status)
    return payload


def _role_records(payload: Mapping[str, Any], role: str) -> list[dict[str, Any]]:
    return [record for record in payload["records"] if record["role"] == role]


def _copy_role_metrics(payload: dict[str, Any], *, source_role: str, target_role: str) -> None:
    sources = {record["seed"]: record for record in _role_records(payload, source_role)}
    for target in _role_records(payload, target_role):
        source = sources[target["seed"]]
        for name in METRIC_NAMES:
            target[name] = source[name]


def _improve_role_metrics(payload: dict[str, Any], *, target_role: str, delta: float = 0.25) -> None:
    sources = {record["seed"]: record for record in _role_records(payload, "before")}
    for target in _role_records(payload, target_role):
        source = sources[target["seed"]]
        for name in METRIC_NAMES:
            target[name] = source[name] + delta
    delta_key = "after_minus_before" if target_role == "after" else "control_minus_before"
    payload["deltas"][delta_key]["benefit_delta"] = 5.0
    payload["deltas"][delta_key]["cost_delta"] = 0.0
    payload["deltas"][delta_key]["debt_delta"] = -1.0


def _make_positive_main(payload: dict[str, Any]) -> None:
    payload["claim_gate"]["positive_quality_improvement"] = True
    payload["claim_gate"]["quality_q_ci95_low"] = 0.1
    payload["claim_gate"]["paired_ci_status"] = "ok"
    payload["claim_gate"]["audit_improvement_tradeoff"] = False
    quality_ci = payload["paired_delta_ci"]["after_minus_before"]["quality_q_delta"]
    quality_ci["status"] = "ok"
    quality_ci["ci95_low"] = 0.1
    _improve_role_metrics(payload, target_role="after")


def _terminal_decision(witness: RuntimeWitness) -> dict[str, Any]:
    return synthesize_certification_verdict(
        witness.certificate_payload,
        witness.evidence_payload,
        timestamp_iso=TIMESTAMP,
    )


def _expected_demotion(decision: Mapping[str, Any], discovery_level: str) -> str:
    return f"{decision['verdict']}/{discovery_level}"


def _ledger_row(witness: RuntimeWitness) -> dict[str, Any]:
    contract = WITNESS_GAP_CONTRACTS[witness.kind]
    decision = _terminal_decision(witness)
    projection = assign_discovery_level(decision)
    if decision["verdict"] not in NON_POSITIVE_TERMINAL_VERDICTS:
        raise RuntimeError(f"{witness.kind} passed terminal gate as {decision['verdict']}")
    if projection.discovery_level not in NON_POSITIVE_LEVELS:
        raise RuntimeError(f"{witness.kind} reached positive discovery level {projection.discovery_level}")
    if contract.demotion != _expected_demotion(decision, projection.discovery_level):
        raise RuntimeError(f"{witness.kind} contract demotion does not match gate replay")
    basis = decision["evidence_basis"]
    return {
        "kind": witness.kind,
        "soundness": witness.soundness,
        "bedc_gap_field": contract.bedc_gap_field,
        "violated_principle": contract.violated_principle,
        "required_ledger_row": contract.required_ledger_row,
        "demotion": contract.demotion,
        "regression_test": contract.regression_test,
        "terminal_verdict": decision["verdict"],
        "terminal_reason": decision["reason"],
        "discovery_level": projection.discovery_level,
        "discovery_reasons": list(projection.reasons),
        "gate_basis": {
            "main_claim_status": basis.get("main_claim_status"),
            "rejected": basis.get("rejected"),
            "rejection_reason": basis.get("rejection_reason"),
            "audit_status": basis.get("audit_status"),
            "downgraded": basis.get("downgraded"),
            "new_status": basis.get("new_status"),
            "scorecard_ready": basis.get("scorecard_ready"),
            "net_positive_signal": basis.get("net_positive_signal"),
            "forbidden_claim_term_hits": basis.get("forbidden_claim_term_hits", []),
            "malformed_detail": basis.get("malformed_detail"),
        },
    }


def _mutate_classifier_surface_delta_zero(certificate: dict[str, Any], evidence: dict[str, Any]) -> None:
    certificate["main_claim_status"] = "mixed"
    _copy_role_metrics(evidence, source_role="before", target_role="after")
    evidence["deltas"]["after_minus_before"] = {
        key: 0.0 for key in evidence["deltas"]["after_minus_before"]
    }


def _mutate_matched_control_positive(certificate: dict[str, Any], evidence: dict[str, Any]) -> None:
    certificate["main_claim_status"] = "positive"
    _make_positive_main(evidence)
    _improve_role_metrics(evidence, target_role="control")


def _mutate_hidden_debt_positive(certificate: dict[str, Any], evidence: dict[str, Any]) -> None:
    certificate["main_claim_status"] = "positive"
    evidence["claim_gate"]["positive_quality_improvement"] = True


def _mutate_cost_protocol_missing(certificate: dict[str, Any], evidence: dict[str, Any]) -> None:
    certificate["main_claim_status"] = "observed-negative"
    evidence["result"]["shared_cost_protocol_name"] = False


def _mutate_scorecard_not_ready(certificate: dict[str, Any], evidence: dict[str, Any]) -> None:
    certificate["main_claim_status"] = "observed-negative"
    evidence["quality_scorecard"] = _scorecard(status="not-ready")


def _mutate_forbidden_inference_column(certificate: dict[str, Any], evidence: dict[str, Any]) -> None:
    certificate["main_claim_status"] = "positive"
    certificate["positive_claim_cell"] = {
        "claim": f"{FORBIDDEN_POSITIVE_CLAIM_TERMS[0]} quality certificate",
        "term_source": "bedc_quality_lab.claim_terms.FORBIDDEN_POSITIVE_CLAIM_TERMS",
    }
    _make_positive_main(evidence)


def _mutate_benefit_debt_tradeoff(certificate: dict[str, Any], evidence: dict[str, Any]) -> None:
    certificate["main_claim_status"] = "positive"
    evidence["claim_gate"]["positive_quality_improvement"] = True
    evidence["claim_gate"]["audit_improvement_tradeoff"] = True


def _mutate_fresh_claim_downgrade(certificate: dict[str, Any], evidence: dict[str, Any]) -> None:
    certificate["main_claim_status"] = "positive"
    evidence["claim_gate"]["positive_quality_improvement"] = True
    evidence["claim_gate"]["quality_q_ci95_low"] = -0.1
    evidence["claim_gate"]["paired_ci_status"] = "weak"
    evidence["paired_delta_ci"]["after_minus_before"]["quality_q_delta"]["status"] = "weak"
    evidence["paired_delta_ci"]["after_minus_before"]["quality_q_delta"]["ci95_low"] = -0.1


_WITNESS_BUILDERS: dict[str, tuple[str, Mutator]] = {
    "classifier_surface_delta_zero": (
        "A pseudo discovery with zero surface delta has no classifier shift and must be rejected.",
        _mutate_classifier_surface_delta_zero,
    ),
    "matched_control_positive": (
        "A positive matched control makes the main improvement unresolved and must be rejected.",
        _mutate_matched_control_positive,
    ),
    "hidden_debt_positive": (
        "A positive certificate over an observed-negative projection hides debt and must be demoted.",
        _mutate_hidden_debt_positive,
    ),
    "cost_protocol_missing": (
        "A missing shared cost protocol makes the projection malformed and must be rejected.",
        _mutate_cost_protocol_missing,
    ),
    "scorecard_not_ready": (
        "A not-ready quality scorecard cannot certify a positive discovery and stays ledger-only.",
        _mutate_scorecard_not_ready,
    ),
    "forbidden_inference_column": (
        "A positive claim containing a forbidden claim term must be rejected by the overclaim gate.",
        _mutate_forbidden_inference_column,
    ),
    "benefit_debt_tradeoff": (
        "A claimed positive with audit-improvement tradeoff must be downgraded instead of accepted.",
        _mutate_benefit_debt_tradeoff,
    ),
    "fresh_claim_downgrade": (
        "Fresh weakened claim evidence must revoke the old positive certificate.",
        _mutate_fresh_claim_downgrade,
    ),
}


def runtime_witnesses() -> list[RuntimeWitness]:
    witnesses = []
    for kind in EXPECTED_KINDS:
        soundness, mutate = _WITNESS_BUILDERS[kind]
        certificate = {"main_claim_status": "observed-negative"}
        evidence = _base_evidence()
        mutate(certificate, evidence)
        witnesses.append(
            RuntimeWitness(
                kind=kind,
                soundness=soundness,
                certificate_payload=certificate,
                evidence_payload=evidence,
            )
        )
    return witnesses


def build_witness_ledger(*, generated_at: str | None = None) -> dict[str, Any]:
    if tuple(WITNESS_GAP_CONTRACTS) != EXPECTED_KINDS:
        raise RuntimeError(f"unexpected witness contract kind order: {list(WITNESS_GAP_CONTRACTS)}")
    rows = [_ledger_row(witness) for witness in runtime_witnesses()]
    kinds = [row["kind"] for row in rows]
    if tuple(kinds) != EXPECTED_KINDS:
        raise RuntimeError(f"unexpected witness kind order: {kinds}")
    return {
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at or datetime.now(timezone.utc).isoformat(),
        "status": "pointer-only",
        "producer": "tools/quality_discovery_adversarial_generator.py",
        "expected_kind_count": len(EXPECTED_KINDS),
        "forbidden_claim_terms_source": "bedc_quality_lab.claim_terms.FORBIDDEN_POSITIVE_CLAIM_TERMS",
        "forbidden_claim_terms_count": len(FORBIDDEN_POSITIVE_CLAIM_TERMS),
        "witnesses": rows,
    }


def assert_pointer_only_boundary(payload: Mapping[str, Any]) -> None:
    keys = set(_walk_keys(payload))
    forbidden = sorted(keys & FORBIDDEN_LEDGER_FIELDS)
    if forbidden:
        raise RuntimeError(f"witness ledger contains forbidden schema/report keys: {forbidden}")
    text = json.dumps(payload, sort_keys=True)
    if "host.env" in text:
        raise RuntimeError("witness ledger contains forbidden host.env string")


def validate_witness_gap_contracts(payload: Mapping[str, Any]) -> None:
    witnesses = payload.get("witnesses")
    if not isinstance(witnesses, list):
        raise RuntimeError("witness ledger must contain witness rows")
    kinds = [row.get("kind") if isinstance(row, Mapping) else None for row in witnesses]
    if tuple(kinds) != EXPECTED_KINDS:
        raise RuntimeError(f"unexpected witness kind order: {kinds}")
    for row in witnesses:
        if not isinstance(row, Mapping):
            raise RuntimeError("witness row must be a JSON object")
        kind = str(row["kind"])
        contract = WITNESS_GAP_CONTRACTS[kind]
        for field in REQUIRED_GAP_FIELDS:
            value = row.get(field)
            if not isinstance(value, str) or not value.strip():
                raise RuntimeError(f"{kind} missing required gap field {field}")
            if value != getattr(contract, field):
                raise RuntimeError(f"{kind} has stale gap field {field}")
        expected = f"{row.get('terminal_verdict')}/{row.get('discovery_level')}"
        if row["demotion"] != expected:
            raise RuntimeError(f"{kind} demotion does not match terminal replay")


def _walk_keys(value: Any):
    if isinstance(value, Mapping):
        for key, cell in value.items():
            yield str(key)
            yield from _walk_keys(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _walk_keys(cell)


def write_witness_ledger(path: Path | None = None, *, generated_at: str | None = None) -> dict[str, Any]:
    target = path or ROOT / LEDGER_ARTIFACT
    if target.resolve() != (ROOT / LEDGER_ARTIFACT).resolve():
        raise ValueError(f"refresh may only write {LEDGER_ARTIFACT}")
    payload = build_witness_ledger(generated_at=generated_at)
    assert_pointer_only_boundary(payload)
    validate_witness_gap_contracts(payload)
    target.parent.mkdir(parents=True, exist_ok=True)
    tmp = target.with_suffix(target.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(target)
    return payload


def load_checked_in_ledger(path: Path | None = None) -> dict[str, Any]:
    source = path or ROOT / LEDGER_ARTIFACT
    return json.loads(source.read_text(encoding="utf-8"))


def replay_checked_in_ledger(path: Path | None = None) -> dict[str, Any]:
    checked_in = load_checked_in_ledger(path)
    assert_pointer_only_boundary(checked_in)
    validate_witness_gap_contracts(checked_in)
    fresh = build_witness_ledger(generated_at=checked_in.get("generated_at"))
    fresh["generated_at"] = checked_in.get("generated_at")
    validate_witness_gap_contracts(fresh)
    if checked_in != fresh:
        raise RuntimeError("checked-in discovery negative witnesses are stale")
    return fresh


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        default=LEDGER_ARTIFACT,
        help="Output path; only reports/canonical/discovery_negative_witnesses.json is accepted.",
    )
    args = parser.parse_args(argv)
    output = (ROOT / args.output).resolve()
    payload = write_witness_ledger(output)
    print(f"wrote {len(payload['witnesses'])} discovery negative witnesses to {LEDGER_ARTIFACT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

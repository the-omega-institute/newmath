"""Project the learned-h gap head into the classifier discovery predicates."""

from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.classifier_shift import (
    ClassifierPassage,
    ClassifierState,
    classifier_surface_delta,
    shift_information,
    structural_discovery,
)
from bedc_quality_lab.discovery import DiscoveryClaim, net_information, positive_discovery
from bedc_quality_lab.discovery_compiler.anti_triviality import owner_local_anti_triviality_contract
from bedc_quality_lab.ledger import LedgerRowKey, ledger_complete
from bedc_quality_lab.scope import CLOSED_CLAIM_SCOPE_SEAL, Scope, ScopedCertificate, closed_claim_scope_seal, scope_rows


SOURCE_JSON_ARTIFACT = "reports/gap_ledger_head_on_h.json"
JSON_ARTIFACT = "reports/gap_head_discovery.json"
REPORT_ARTIFACT = "reports/gap_head_discovery.md"
SCOPE_SEAL = CLOSED_CLAIM_SCOPE_SEAL
BEFORE_ARM = "vanilla"
AFTER_ARM = "learned_gap_head_on_h"
CONTROL_ARM = "matched_random_gap_head"
BOUNDARY = "learned_h"
MATCHED_RANDOM_AUDIT_MATCH_KEYS = (
    "parameter_match",
    "compute_match",
    "threshold_match",
    "surface_distribution_match",
    "metric_helper_match",
)
MATCHED_RANDOM_AUDIT_REQUIRED_KEYS = MATCHED_RANDOM_AUDIT_MATCH_KEYS + (
    "audit_status",
    "failure_reasons",
    "evidence_pointers",
)


@dataclass
class GapHeadProjection:
    passage: ClassifierPassage
    claim: DiscoveryClaim
    source_payload: dict[str, Any]
    source_artifacts: dict[str, Any]
    boundary_checks: dict[str, Any]
    benefit_terms: dict[str, float]
    score_terms: dict[str, float]
    debt_terms: dict[str, float]
    omitted_debt_terms: dict[str, float]


def _load_gap_head_payload(path: Path | None = None) -> dict[str, Any]:
    payload_path = ROOT / SOURCE_JSON_ARTIFACT if path is None else path
    payload = json.loads(payload_path.read_text(encoding="utf-8"))
    _validate_gap_head_payload(payload)
    return payload


def _validate_gap_head_payload(payload: dict[str, Any]) -> None:
    if payload.get("representation_boundary") != BOUNDARY:
        raise ValueError("gap-head payload must use learned_h representation boundary")
    if payload.get("inference_no_ground_truth_z") is not True:
        raise ValueError("gap-head payload must certify no ground-truth z inference")

    _assert_no_forbidden_features(
        payload.get("feature_columns", []),
        payload.get("forbidden_inference_columns", []),
    )
    records = payload.get("records", [])
    expected_count = int(payload.get("aggregate", {}).get("record_count", -1))
    if not records or expected_count != len(records):
        raise ValueError("gap-head ledger record count is incomplete")

    seeds = set()
    for record in records:
        if record.get("representation_boundary") != BOUNDARY:
            raise ValueError("record representation boundary mismatch")
        if record.get("inference_no_ground_truth_z") is not True:
            raise ValueError("record no-z inference certificate missing")
        _assert_no_forbidden_features(
            record.get("feature_columns", []),
            record.get("forbidden_inference_columns", []),
        )
        arms = record.get("arms", {})
        if BEFORE_ARM not in arms or AFTER_ARM not in arms or CONTROL_ARM not in arms:
            raise ValueError("before/after arms must share each record")
        if record.get("matched_random_control", {}).get("arm") != CONTROL_ARM:
            raise ValueError("matched-random control certificate missing")
        seed = record.get("seed")
        if seed in seeds:
            raise ValueError("common source seed ids must be unique")
        seeds.add(seed)


def _assert_no_forbidden_features(feature_columns: list[str], forbidden_columns: list[str]) -> None:
    forbidden = {str(column) for column in forbidden_columns}
    forbidden_prefixes = {column.split(":", 1)[0] for column in forbidden}
    for column in feature_columns:
        name = str(column)
        prefix = name.split(":", 1)[0]
        if name in forbidden or prefix in forbidden_prefixes:
            raise ValueError(f"forbidden inference column entered feature columns: {name}")


def _audit_entry_status(entry: Any) -> tuple[bool, list[str]]:
    if not isinstance(entry, dict):
        return False, ["matched_random_control_audit_malformed"]
    missing = [key for key in MATCHED_RANDOM_AUDIT_REQUIRED_KEYS if key not in entry]
    failures = [f"missing:{key}" for key in missing]
    if entry.get("audit_status") != "pass":
        failures.append("audit_status_not_pass")
    for key in MATCHED_RANDOM_AUDIT_MATCH_KEYS:
        if entry.get(key) is not True:
            failures.append(f"{key}_not_true")
    failure_reasons = entry.get("failure_reasons")
    if not isinstance(failure_reasons, list):
        failures.append("failure_reasons_malformed")
    elif failure_reasons:
        failures.extend(str(reason) for reason in failure_reasons)
    evidence_pointers = entry.get("evidence_pointers")
    if not isinstance(evidence_pointers, dict):
        failures.append("evidence_pointers_malformed")
    else:
        for key in MATCHED_RANDOM_AUDIT_MATCH_KEYS:
            pointer_set = evidence_pointers.get(key)
            if not isinstance(pointer_set, list) or not pointer_set:
                failures.append(f"evidence_pointers.{key}_missing")
    return not failures, failures


def _source_matched_random_control_audit(payload: dict[str, Any]) -> dict[str, Any]:
    entries: list[tuple[str, Any]] = [("$.control_protocol", payload.get("control_protocol"))]
    entries.extend(
        (
            f"$.records[{index}].matched_random_control",
            record.get("matched_random_control") if isinstance(record, dict) else None,
        )
        for index, record in enumerate(payload.get("records", []))
    )
    failures: list[str] = []
    for pointer, entry in entries:
        verified, entry_failures = _audit_entry_status(entry)
        if not verified:
            failures.extend(f"{pointer}:{reason}" for reason in entry_failures)
    audit_status = "pass" if not failures else "fail"
    return {
        **{
            key: all(isinstance(entry, dict) and entry.get(key) is True for _, entry in entries)
            for key in MATCHED_RANDOM_AUDIT_MATCH_KEYS
        },
        "audit_status": audit_status,
        "failure_reasons": failures,
        "evidence_pointers": {
            key: [
                f"source-json $.control_protocol.{key}",
                f"source-json $.records[*].matched_random_control.{key}",
            ]
            for key in MATCHED_RANDOM_AUDIT_MATCH_KEYS
        },
        "verified": audit_status == "pass",
    }


def _row_for_source(source_id: str) -> LedgerRowKey:
    return LedgerRowKey("classifier", f"{source_id}->{source_id}")


def _judgment(arm: dict[str, Any]) -> str:
    unlogged = float(arm["unlogged_error_rate"])
    critical = float(arm["critical_unlogged_error_rate"])
    auroc = float(arm["failure_detection_auroc"]["value"])
    return (
        f"unlogged:{unlogged:.6f};"
        f"critical:{critical:.6f};"
        f"auroc:{auroc:.6f}"
    )


def _comparison_suffix(after_arm: str) -> str:
    if after_arm == AFTER_ARM:
        return "learned_minus_vanilla"
    if after_arm == CONTROL_ARM:
        return "matched_random_minus_vanilla"
    raise ValueError(f"unsupported after arm: {after_arm}")


def _benefit_terms(payload: dict[str, Any], *, after_arm: str) -> dict[str, float]:
    comparison = payload["aggregate"]["comparison"]
    unlogged_drop = -float(
        comparison[f"unlogged_error_rate_delta_{_comparison_suffix(after_arm)}"]["mean"]
    )
    critical_drop = -float(
        comparison[f"critical_unlogged_error_rate_delta_{_comparison_suffix(after_arm)}"]["mean"]
    )
    return {
        "unlogged_error_reduction": max(0.0, unlogged_drop),
        "critical_unlogged_error_reduction": max(0.0, critical_drop),
    }


def _score_terms(payload: dict[str, Any]) -> dict[str, float]:
    feature_count = len(payload["feature_columns"])
    gap_channel_count = len(payload["config"]["gap_channels"])
    return {
        "h_only_feature_surface": feature_count / 100.0,
        "gap_channel_heads": gap_channel_count / 100.0,
    }


def _debt_terms(delta_count: int, *, debt_scale: float) -> dict[str, float]:
    return {
        "classifier_ledger_rows": debt_scale * delta_count / 100.0,
        "boundary_protocol": debt_scale * 0.05,
    }


def _build_gap_head_projection(
    payload: dict[str, Any],
    *,
    after_arm: str = AFTER_ARM,
    recorded_rows: frozenset[LedgerRowKey] | None = None,
    omitted_debt_terms: dict[str, float] | None = None,
    laundering_modes: frozenset[str] = frozenset(),
    debt_scale: float = 1.0,
) -> GapHeadProjection:
    _validate_gap_head_payload(payload)
    if after_arm not in {AFTER_ARM, CONTROL_ARM}:
        raise ValueError(f"unsupported after arm: {after_arm}")
    records = payload["records"]
    payload_source_artifacts = payload.get("source_artifacts", {})
    source_json_artifact = payload_source_artifacts.get("json_artifact", SOURCE_JSON_ARTIFACT)
    source_report_artifact = payload_source_artifacts.get("report_artifact", payload.get("report"))
    source_ids = frozenset(f"seed:{record['seed']}" for record in records)
    source_relation = frozenset(
        (f"seed:{record['seed']}", f"seed:{record['seed']}", _judgment(record["arms"][BEFORE_ARM]))
        for record in records
    )
    target_relation = frozenset(
        (f"seed:{record['seed']}", f"seed:{record['seed']}", _judgment(record["arms"][after_arm]))
        for record in records
    )
    surface_used = frozenset((source_id, source_id) for source_id in source_ids)
    ledger_rows = frozenset(_row_for_source(source_id) for source_id in source_ids)
    rows_recorded = ledger_rows if recorded_rows is None else recorded_rows
    cert = {
        "cert_status": "certified",
        "cert_method": "gap-head-learned-h-boundary",
        "representation_boundary": payload["representation_boundary"],
        "inference_no_ground_truth_z": payload["inference_no_ground_truth_z"],
        "common_source_record_count": len(records),
        "source_artifact": source_json_artifact,
        "after_arm": after_arm,
    }
    source = ClassifierState(
        source_ids=source_ids,
        pattern_id="gap-head-before-vanilla",
        ledger_policy=frozenset(),
        relation=source_relation,
        certificate={"cert_status": "certified"},
        surface_used=frozenset(),
        verification_status="artifact-checked",
        record_count=len(records),
        feature_count=len(payload["feature_columns"]),
        notation="seed-self-pair",
    )
    target = ClassifierState(
        source_ids=source_ids,
        pattern_id=f"gap-head-after-{after_arm.replace('_', '-')}",
        ledger_policy=ledger_rows,
        relation=target_relation,
        certificate=cert,
        surface_used=surface_used,
        verification_status="artifact-checked",
        record_count=len(records),
        feature_count=len(payload["feature_columns"]),
        notation="seed-self-pair",
    )
    passage = ClassifierPassage(source=source, target=target, recorded_rows=rows_recorded)
    delta_count = len(classifier_surface_delta(passage))
    benefit = _benefit_terms(payload, after_arm=after_arm)
    score = _score_terms(payload)
    debt = _debt_terms(delta_count, debt_scale=debt_scale)
    scope = Scope(
        domain_ids=frozenset({"gaussian-ou-toy-world"}),
        model_id="gap-head-on-learned-h",
        admitted_family_id="existing-lab-generator",
        behavior_id="unlogged-critical-error-detection",
    )
    scope_required = scope_rows(scope)
    scoped_certificate = ScopedCertificate(
        scope=scope,
        classifier_id=target.pattern_id,
        namecert_id="learned-h-gap-head-boundary",
        required_rows=scope_required,
        recorded_rows=scope_required,
        certificate=cert,
        not_claimed_boundary=frozenset({"formal-bedc-closure", "human-math-baseline"}),
    )
    claim = DiscoveryClaim(
        passage=passage,
        benefit_terms=benefit,
        score_terms=score,
        debt_terms=debt,
        ledger_required_rows=ledger_rows,
        ledger_recorded_rows=rows_recorded,
        public_cost_protocol=True,
        scope_sealed=closed_claim_scope_seal(SCOPE_SEAL),
        not_claimed_boundary=frozenset({"formal-bedc-closure", "human-math-baseline"}),
        benefit_modes=frozenset(benefit),
        omitted_debt_terms={} if omitted_debt_terms is None else omitted_debt_terms,
        scoped_certificate=scoped_certificate,
        laundering_modes=laundering_modes,
        reproducible_evidence=True,
    )
    return GapHeadProjection(
        passage=passage,
        claim=claim,
        source_payload=payload,
        source_artifacts={
            "source_json_artifact": source_json_artifact,
            "source_report_artifact": source_report_artifact,
            "producer_script": payload.get("source_artifacts", {}).get("generation_script"),
            "projection_script": "scripts/run_gap_head_discovery.py",
        },
        boundary_checks={
            "representation_boundary": payload["representation_boundary"],
            "inference_no_ground_truth_z": payload["inference_no_ground_truth_z"],
            "feature_columns": payload["feature_columns"],
            "forbidden_inference_columns": payload["forbidden_inference_columns"],
            "before_arm": BEFORE_ARM,
            "after_arm": after_arm,
            "common_source_seed_order": payload["aggregate"]["seed_order"],
        },
        benefit_terms=benefit,
        score_terms=score,
        debt_terms=debt,
        omitted_debt_terms={} if omitted_debt_terms is None else omitted_debt_terms,
    )


def _non_discovery_reason(claim: DiscoveryClaim, structural: bool, positive: bool) -> str | None:
    if positive:
        return None
    if not ledger_complete(claim.passage.target.ledger_policy, claim.passage.recorded_rows):
        return "ledger_incomplete"
    if not structural:
        return "structural_discovery_false"
    if claim.laundering_modes:
        return "laundering_modes_present"
    if claim.omitted_debt_terms:
        return "debt_omitted"
    if net_information(claim) <= 0.0:
        return "net_information_nonpositive"
    return "positive_protocol_incomplete"


def _projection_verdict(projection: GapHeadProjection) -> dict[str, Any]:
    passage = projection.passage
    claim = projection.claim
    delta = classifier_surface_delta(passage)
    structural = structural_discovery(passage)
    positive = positive_discovery(claim)
    return {
        "artifact": JSON_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "source_artifacts": projection.source_artifacts,
        "scope_seal": SCOPE_SEAL,
        "common_source_record_count": len(passage.source.source_ids & passage.target.source_ids),
        "surface_delta_count": len(delta),
        "shift_information": shift_information(passage),
        "benefit_terms": projection.benefit_terms,
        "score_terms": projection.score_terms,
        "debt_terms": projection.debt_terms,
        "omitted_debt_terms": projection.omitted_debt_terms,
        "net_information": net_information(claim),
        "structural_discovery": structural,
        "positive_discovery": positive,
        "net_positive_signal": positive,
        "laundering_modes": sorted(claim.laundering_modes),
        "non_discovery_reason": _non_discovery_reason(claim, structural, positive),
        "boundary_checks": projection.boundary_checks,
        "classifier_state": {
            "before_pattern_id": passage.source.pattern_id,
            "after_pattern_id": passage.target.pattern_id,
            "recorded_ledger_rows": len(passage.recorded_rows),
            "required_ledger_rows": len(passage.target.ledger_policy),
            "feature_count": passage.target.feature_count,
        },
    }


def _control_summary(control: dict[str, Any]) -> dict[str, Any]:
    return {
        "arm": control["boundary_checks"]["after_arm"],
        "surface_delta_count": control["surface_delta_count"],
        "shift_information": control["shift_information"],
        "structural_discovery": control["structural_discovery"],
        "positive_discovery": control["positive_discovery"],
        "net_information": control["net_information"],
        "non_discovery_reason": control["non_discovery_reason"],
    }


def _main_claim_status(
    treatment: dict[str, Any],
    *,
    control_positive: bool,
    control_audit_verified: bool,
) -> str:
    if not control_audit_verified:
        return "unresolved"
    if control_positive:
        return "unresolved"
    if treatment["positive_discovery"]:
        return "promoted"
    return "not_promoted"


def _main_claim_reason(
    treatment: dict[str, Any],
    *,
    control_positive: bool,
    control_audit_verified: bool,
) -> str | None:
    if not control_audit_verified:
        return "matched_random_control_unverified"
    if control_positive:
        return "control_positive"
    if treatment["positive_discovery"]:
        return None
    return treatment.get("non_discovery_reason")


def _anti_triviality_contract(level: str) -> dict[str, Any]:
    return {"anti_triviality_status": "pass"} | owner_local_anti_triviality_contract(
        recommended_level=level,
        scale_only_pointer="$.boundary_checks",
        metadata_only_pointer="$.boundary_checks",
        matched_random_pointer="$.matched_random_control.control_verdict.positive",
        forbidden_column_pointer="$.boundary_checks.forbidden_inference_columns",
    )


def _source_control_verdict(
    payload: dict[str, Any],
    control: dict[str, Any],
    *,
    control_audit: dict[str, Any],
) -> dict[str, Any]:
    source_verdict = payload.get("control_verdict", {})
    verified = bool(control_audit.get("verified"))
    positive = bool(source_verdict.get("positive", control["positive_discovery"])) if verified else False
    return {
        "positive": positive,
        "reason": (
            "matched_random_control_unverified"
            if not verified
            else "control_positive"
            if positive
            else "control_non_positive"
        ),
        "source_positive": source_verdict.get("positive"),
        "projection_positive_discovery": control["positive_discovery"],
        "source_metrics": source_verdict.get("metrics", {}),
    }


def _verdict_payload(projection: GapHeadProjection) -> dict[str, Any]:
    treatment = _projection_verdict(projection)
    control_projection = _build_gap_head_projection(projection.source_payload, after_arm=CONTROL_ARM)
    control = _projection_verdict(control_projection)
    control_audit = _source_matched_random_control_audit(projection.source_payload)
    control_verdict = _source_control_verdict(
        projection.source_payload,
        control,
        control_audit=control_audit,
    )
    treatment["matched_random_control"] = {
        **control_audit,
        "source_protocol": "source-json matched_random_control per record",
        "control_projection": _control_summary(control),
        "control_verdict": control_verdict,
    }
    treatment["main_claim_status"] = _main_claim_status(
        treatment,
        control_positive=control_verdict["positive"],
        control_audit_verified=bool(control_audit["verified"]),
    )
    treatment["final_main_claim_status"] = treatment["main_claim_status"]
    treatment["main_claim_reason"] = _main_claim_reason(
        treatment,
        control_positive=control_verdict["positive"],
        control_audit_verified=bool(control_audit["verified"]),
    )
    treatment["audit_decision"] = {"audit_status": "pass" if control_audit["verified"] else "fail"}
    if treatment["main_claim_status"] == "promoted":
        treatment.update(_anti_triviality_contract("D4"))
    return treatment


def _format_float(value: float) -> str:
    return f"{value:.6f}"


def _render_report(payload: dict[str, Any]) -> str:
    reason = payload["non_discovery_reason"] or "none"
    lines = [
        "# Gap-Head Discovery Verdict",
        "",
        f"- Source JSON artifact: `{payload['source_artifacts']['source_json_artifact']}`",
        f"- Source report artifact: `{payload['source_artifacts']['source_report_artifact']}`",
        f"- Common-source record count: `{payload['common_source_record_count']}`",
        f"- Surface delta count: `{payload['surface_delta_count']}`",
        f"- Shift information: `{payload['shift_information']}`",
        f"- Structural discovery: `{str(payload['structural_discovery']).lower()}`",
        f"- Positive discovery: `{str(payload['positive_discovery']).lower()}`",
        f"- Main claim status: `{payload['main_claim_status']}`",
        f"- Non-discovery reason: `{reason}`",
        f"- Matched-random control positive: `{str(payload['matched_random_control']['control_verdict']['positive']).lower()}`",
        "",
        "## Information",
        "",
        f"- Benefit: `{_format_float(sum(payload['benefit_terms'].values()))}`",
        f"- Score: `{_format_float(sum(payload['score_terms'].values()))}`",
        f"- Debt: `{_format_float(sum(payload['debt_terms'].values()))}`",
        f"- Omitted debt: `{_format_float(sum(payload['omitted_debt_terms'].values()))}`",
        f"- Net: `{_format_float(float(payload['net_information']))}`",
        "",
        "## Boundary",
        "",
        f"- Representation boundary: `{payload['boundary_checks']['representation_boundary']}`",
        f"- Inference no ground-truth z: `{str(payload['boundary_checks']['inference_no_ground_truth_z']).lower()}`",
        f"- Before arm: `{payload['boundary_checks']['before_arm']}`",
        f"- After arm: `{payload['boundary_checks']['after_arm']}`",
        f"- Forbidden inference columns: `{', '.join(payload['boundary_checks']['forbidden_inference_columns'])}`",
        "",
        "## Cost Protocol",
        "",
        "- Benefit terms:",
    ]
    for key, value in payload["benefit_terms"].items():
        lines.append(f"  - `{key}`: `{_format_float(float(value))}`")
    lines.append("- Score terms:")
    for key, value in payload["score_terms"].items():
        lines.append(f"  - `{key}`: `{_format_float(float(value))}`")
    lines.append("- Debt terms:")
    for key, value in payload["debt_terms"].items():
        lines.append(f"  - `{key}`: `{_format_float(float(value))}`")
    lines.extend(["", "## Source Artifacts", ""])
    for key, value in payload["source_artifacts"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.append("")
    return "\n".join(lines)


def _write_payload(payload: dict[str, Any]) -> None:
    json_path = ROOT / JSON_ARTIFACT
    report_path = ROOT / REPORT_ARTIFACT
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(_render_report(payload), encoding="utf-8")


def main() -> None:
    payload = _verdict_payload(_build_gap_head_projection(_load_gap_head_payload()))
    _write_payload(payload)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")


if __name__ == "__main__":
    main()

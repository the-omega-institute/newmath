#!/usr/bin/env python3
"""Compile pointer-only claim verdict rows from canonical discovery ledgers."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.artifact_freshness import ScorecardSnapshot, load_scorecard_snapshot
from bedc_quality_lab.claim_acceptance import validate_dn_owner_cell, validate_positive_claim_evidence
from bedc_quality_lab.claim_graph import terminal_node_id_for_claim_id
from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.cost_protocol import load_cost_protocol
from bedc_quality_lab.discovery_compiler.claim_verdict_reason import (
    ClaimVerdictReasonBasis,
    POSITIVE_DISCOVERY_GATES_PASS,
    reason_for_claim_verdict,
    validate_claim_verdict_reason,
)
from bedc_quality_lab.discovery_compiler.map import load_validated_discovery_map_payload
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from bedc_quality_lab.evidence_provenance import load_evidence_provenance, owner_supports_empirical_claim
from bedc_quality_lab.high_impact_claim_review import high_impact_review_failure_pointer
from bedc_quality_lab.mechanism_attribution import D5_M_CAUSAL_EVIDENCE_LEVELS
from bedc_quality_lab.research_discovery import assign_discovery_level
from bedc_quality_lab.scope import (
    ScopeExpansionGate,
    scope_expansion_gate_for_payload,
)
from bedc_quality_lab.verdict import synthesize_certification_verdict
from scripts.run_canonical_reports import CANONICAL_REPORTS, CanonicalReportSpec, _discovery_map_reports
from scripts.run_discovery_map import build_discovery_map, pointer_value, projection_payload


CLAIM_VERDICTS_JSONL_ARTIFACT = "reports/canonical/claim_verdicts.jsonl"
CLAIM_VERDICTS_ARTIFACT_ID = "bedc-quality-lab:claim-verdicts"
ALLOWED_ROW_KEYS = frozenset(
    {
        "claim_id",
        "claim_graph_node_id",
        "claim_verdict",
        "reason",
        "source",
        "ledger_pointer",
        "scorecard_pointer",
        "scorecard_hash",
        "scorecard_ready",
        "formal_hardening_ready",
    }
)
DN_VERDICT_ROW_KEYS = frozenset(
    {
        "claim_id",
        "claim_graph_node_id",
        "claim_verdict",
        "reason",
        "negative_report_pointer",
    }
)
CLAIM_VERDICTS = frozenset(
    {
        "raw_operational_evidence_pass",
        "projected_discovery_required",
        "projected_positive_discovery",
        "accepted_positive_discovery",
        "mechanism_not_closed",
        "negative_discovery",
        "revoked_discovery",
    }
)
POSITIVE_LEVELS = frozenset({"D4", "D5-O", "D5-M"})
SCORECARD_ARTIFACT = "reports/canonical/quality-scorecard.json"
DIMENSION_MISMATCH_REPORT = "dimension-mismatch-debt-transfer"
DIMENSION_MISMATCH_ARTIFACT = "reports/canonical/dimension-mismatch-debt-transfer.json"
DIMENSION_MISMATCH_STATUS_POINTER = "$.dimension_mismatch_debt_transfer.status"
DIMENSION_MISMATCH_EFFECTIVE_LEVEL_POINTER = "$.dimension_mismatch_debt_transfer.effective_level"
DIMENSION_MISMATCH_ANTI_TRIVIALITY_POINTER = "$.dimension_mismatch_debt_transfer.anti_triviality_status"
DIMENSION_MISMATCH_SCOPE_POINTER = "$.dimension_mismatch_debt_transfer.scope"
DIMENSION_MISMATCH_COST_POINTER = "$.source_artifacts"
DIMENSION_MISMATCH_NOT_CLAIMED_POINTER = "$.not_claimed"
DIMENSION_MISMATCH_POSITIVE_CLAIM_POINTER = "$.dimension_mismatch_debt_transfer"
DIMENSION_MISMATCH_CONTROL_POINTER = "$.control_protocol"
WINNABILITY_CERTIFICATES_ARTIFACT = "reports/canonical/winnability-certificates.json"
CLAIM_FIRST_DATA_CARD_REASON = "positive-acceptance-evidence-missing:claim-first:data-card"

@dataclass(frozen=True)
class ClaimSource:
    report: str
    json_artifact: str
    pointer: str | None

    def as_text(self) -> str:
        return self.json_artifact if self.pointer is None else f"{self.json_artifact}:{self.pointer}"


def _root(root: Path | None) -> Path:
    return ROOT if root is None else root


def _artifact_path(root: Path, relative_path: str) -> Path:
    return root / relative_path


def _load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_payload(root: Path, artifact: str) -> dict[str, Any]:
    path = _artifact_path(root, artifact)
    if not path.exists():
        return {}
    payload = _load_json(path)
    if not isinstance(payload, dict):
        raise ValueError(f"canonical payload must be a JSON object: {artifact}")
    return payload


def _load_discovery_rows(root: Path, generated_at: str | None) -> list[dict[str, Any]]:
    path = _artifact_path(root, "reports/canonical/discovery_map.json")
    if path.exists():
        payload = load_validated_discovery_map_payload(root)
        rows = payload["rows"]
        if not all(isinstance(row, dict) for row in rows):
            raise ValueError("discovery map must contain object rows")
        return rows
    return list(build_discovery_map(generated_at=generated_at, root=root, canonical_reports=_discovery_map_reports())["rows"])


def _load_scorecard(root: Path) -> dict[str, Any] | None:
    path = _artifact_path(root, "reports/canonical/quality-scorecard.json")
    if not path.exists():
        return None
    payload = _load_json(path)
    return payload if isinstance(payload, dict) else None


def _empirical_claim_support(root: Path, report: str) -> tuple[bool, str]:
    section = load_evidence_provenance(root, require=False)
    if section is None:
        return False, "evidence-provenance-owner-missing"
    return owner_supports_empirical_claim(section, report)


def _load_winnability_certificates(root: Path) -> dict[str, Any]:
    path = _artifact_path(root, WINNABILITY_CERTIFICATES_ARTIFACT)
    if not path.exists():
        return {"status": "missing", "by_certificate_id": {}, "duplicates": set(), "pointers": {}}
    payload = _load_json(path)
    rows = payload.get("certificates") if isinstance(payload, Mapping) else None
    if not isinstance(rows, list):
        return {"status": "malformed", "by_certificate_id": {}, "duplicates": set(), "pointers": {}}
    by_certificate_id: dict[str, Mapping[str, Any]] = {}
    duplicates: set[str] = set()
    pointers: dict[str, str] = {}
    for index, row in enumerate(rows):
        if not isinstance(row, Mapping) or not isinstance(row.get("certificate_id"), str):
            continue
        certificate_id = str(row["certificate_id"])
        pointers[certificate_id] = f"{WINNABILITY_CERTIFICATES_ARTIFACT}:$.certificates[{index}]"
        if certificate_id in by_certificate_id:
            duplicates.add(certificate_id)
        else:
            by_certificate_id[certificate_id] = row
    return {
        "status": "ready",
        "by_certificate_id": by_certificate_id,
        "duplicates": duplicates,
        "pointers": pointers,
    }


def _winnability_ref_cell(row: Mapping[str, Any], payload: Mapping[str, Any]) -> Mapping[str, Any] | str | None:
    for source in (row, payload):
        for key in (
            "winnability_ref",
            "winnability_certificate_ref",
            "winnability_certificate",
            "winnability",
        ):
            value = source.get(key)
            if isinstance(value, (Mapping, str)):
                return value
        value = source.get("winnability_certificate_id")
        if isinstance(value, str):
            return value
    return None


def _winnability_certificate_id(ref: Mapping[str, Any] | str | None) -> str | None:
    if isinstance(ref, str):
        return ref
    if not isinstance(ref, Mapping):
        return None
    value = ref.get("certificate_id")
    return value if isinstance(value, str) else None


def _winnability_block(
    root: Path,
    row: Mapping[str, Any],
    payload: Mapping[str, Any],
) -> tuple[str, str, str] | None:
    ref = _winnability_ref_cell(row, payload)
    certificate_id = _winnability_certificate_id(ref)
    if certificate_id is None:
        return None
    certificate_map = _load_winnability_certificates(root)
    pointer = certificate_map.get("pointers", {}).get(certificate_id)
    if pointer is None:
        pointer = (
            ref.get("pointer")
            if isinstance(ref, Mapping) and isinstance(ref.get("pointer"), str)
            else f"{WINNABILITY_CERTIFICATES_ARTIFACT}:$.certificates"
        )
    if certificate_map["status"] != "ready":
        return "projected_discovery_required", "winnability-certificate-missing", pointer
    if certificate_id in certificate_map["duplicates"]:
        return "projected_discovery_required", "winnability-certificate-missing", pointer
    certificate = certificate_map["by_certificate_id"].get(certificate_id)
    if not isinstance(certificate, Mapping):
        return "projected_discovery_required", "winnability-certificate-missing", pointer
    coverage = certificate.get("coverage") if isinstance(certificate.get("coverage"), Mapping) else {}
    permissions = certificate.get("claim_permissions") if isinstance(certificate.get("claim_permissions"), Mapping) else {}
    if certificate.get("status") == "fail" or certificate.get("method") == "unresolved":
        return "projected_discovery_required", "winnability-certificate-missing", pointer
    if certificate.get("unwinnable") is True:
        return "projected_discovery_required", "split-unwinnable", pointer
    if coverage.get("coverage_classification") == "table-coverage":
        return "projected_discovery_required", "table-coverage-ceiling", pointer
    if any(permissions.get(key) is False for key in (
        "generalization_claim_allowed",
        "separation_claim_allowed",
        "architecture_claim_allowed",
        "rule_abstraction_claim_allowed",
    )):
        return "projected_discovery_required", "winnability-permission-denied", pointer
    return None


def _cost_protocol_loads(root: Path) -> bool:
    candidates = (
        root / "configs" / "default_cost_protocol.yaml",
        ROOT / "configs" / "default_cost_protocol.yaml",
    )
    for candidate in candidates:
        try:
            load_cost_protocol(candidate)
            return True
        except (OSError, ValueError):
            continue
    return False


def _specs_by_name() -> dict[str, CanonicalReportSpec]:
    return {spec.name: spec for spec in CANONICAL_REPORTS}


def _dimension_mismatch_pointer_spec() -> CanonicalReportSpec:
    return CanonicalReportSpec(
        name=DIMENSION_MISMATCH_REPORT,
        command=("python3", "scripts/run_dimension_mismatch_debt_transfer.py"),
        json_artifact=DIMENSION_MISMATCH_ARTIFACT,
        markdown_artifact="reports/canonical/dimension-mismatch-debt-transfer.md",
        required_json_keys=("dimension_mismatch_debt_transfer", "control_protocol", "not_claimed"),
        estimated_seconds=20,
        bundle_role="hg_p_core",
        scope_pointer=DIMENSION_MISMATCH_SCOPE_POINTER,
        cost_pointer=DIMENSION_MISMATCH_COST_POINTER,
        not_claimed_pointer=DIMENSION_MISMATCH_NOT_CLAIMED_POINTER,
        positive_claim_pointer=DIMENSION_MISMATCH_POSITIVE_CLAIM_POINTER,
        control_pointer=DIMENSION_MISMATCH_CONTROL_POINTER,
        no_control_rationale_pointer=None,
    )


def _text_for_term_scan(value: Any) -> str:
    if isinstance(value, (dict, list, tuple)):
        return json.dumps(value, sort_keys=True).lower()
    return str(value).lower()


def _forbidden_hits(value: Any) -> list[str]:
    text = _text_for_term_scan(value)
    return [term for term in FORBIDDEN_POSITIVE_CLAIM_TERMS if term.lower() in text]


def _scope_laundering_pointer(spec: CanonicalReportSpec, payload: Mapping[str, Any]) -> str | None:
    for pointer in (spec.scope_pointer, spec.not_claimed_pointer):
        if pointer_value(payload, pointer) is None:
            return pointer
    if spec.name == "gap-head-discovery":
        modes = pointer_value(payload, "$.laundering_modes")
        if isinstance(modes, list) and modes:
            return "$.laundering_modes"
    return None


def _scope_expansion_gate_for_payload(
    spec: CanonicalReportSpec,
    payload: Mapping[str, Any],
) -> ScopeExpansionGate | None:
    return scope_expansion_gate_for_payload(
        payload,
        pointer_value,
        scope_claim_pointer=getattr(spec, "scope_claim_pointer", None),
        scope_evidence_pointer=getattr(spec, "scope_evidence_pointer", None),
    )


def _scope_expansion_failure_pointer(root: Path, row: Mapping[str, Any], gate: ScopeExpansionGate) -> str:
    row_gate = row.get("scope_gate")
    if isinstance(row_gate, Mapping) and row_gate.get("status") == "fail":
        return _discovery_map_scope_gate_pointer(root, row)
    pointer = gate.failed_pointer
    if isinstance(pointer, str) and pointer.startswith("$."):
        return f"{row['json_artifact']}:{pointer}"
    return _discovery_map_scope_gate_pointer(root, row)


def _positive_claim_forbidden_pointer(spec: CanonicalReportSpec, payload: Mapping[str, Any]) -> str | None:
    if spec.bundle_role != "hg_p_core":
        return None
    cell = pointer_value(payload, spec.positive_claim_pointer)
    if cell is None:
        return spec.positive_claim_pointer
    return spec.positive_claim_pointer if _forbidden_hits(cell) else None


def _net_positive_signal(payload: Mapping[str, Any], verdict_payload: Mapping[str, Any]) -> bool:
    if payload.get("net_positive_signal") is True:
        return True
    basis = verdict_payload.get("evidence_basis")
    if isinstance(basis, Mapping) and basis.get("net_positive_signal") is True:
        return True
    for candidate in (payload.get("net_information"), verdict_payload.get("net_information")):
        if isinstance(candidate, bool):
            continue
        try:
            if candidate is not None and float(candidate) > 0.0:
                return True
        except (TypeError, ValueError):
            continue
    return False


def _control_positive(verdict_payload: Mapping[str, Any]) -> bool:
    return assign_discovery_level(verdict_payload).control_positive is True


def _is_mechanism_open(row: Mapping[str, Any], level: str) -> bool:
    if level != "D5-O":
        return False
    status = row.get("mechanism_status")
    evidence_level = row.get("mechanism_evidence_level")
    return (
        status in {"blocked", "missing"}
        or row.get("terminal_verdict") == "mechanism_not_closed"
        or (isinstance(evidence_level, str) and evidence_level not in D5_M_CAUSAL_EVIDENCE_LEVELS)
    )


def _positive_blocker_verdict(
    report: str,
    level: str,
    row: Mapping[str, Any],
    payload: Mapping[str, Any],
    projected: Mapping[str, Any],
) -> str:
    if _is_mechanism_open(row, level):
        return "mechanism_not_closed"
    if _net_positive_signal(payload, projected):
        if report == "gap-head-on-h":
            return "raw_operational_evidence_pass"
        return "projected_positive_discovery"
    return "projected_discovery_required"


def _dimension_mismatch_projection_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    projected = dict(payload)
    status = pointer_value(payload, DIMENSION_MISMATCH_STATUS_POINTER)
    effective_level = pointer_value(payload, DIMENSION_MISMATCH_EFFECTIVE_LEVEL_POINTER)
    terminal_verdict = pointer_value(payload, "$.dimension_mismatch_debt_transfer.terminal_verdict")
    if status == "pass" and effective_level == "DN" and terminal_verdict == "negative_discovery":
        projected["verdict"] = "rejected"
    elif status == "pass" and pointer_value(payload, DIMENSION_MISMATCH_ANTI_TRIVIALITY_POINTER) == "scale_leakage_detected":
        projected["verdict"] = "rejected"
    elif status == "failed":
        projected["verdict"] = "rejected"
    return projected


def _projected_payload(
    *,
    spec: CanonicalReportSpec,
    payload: Mapping[str, Any],
    scorecard: Mapping[str, Any] | None,
) -> dict[str, Any]:
    if spec.name == DIMENSION_MISMATCH_REPORT:
        projected = _dimension_mismatch_projection_payload(payload)
    else:
        projected = projection_payload(spec, payload)
    projected["quality_scorecard"] = scorecard or {}
    return projected


def _claim_source(row: Mapping[str, Any], fallback_pointer: str | None = None) -> ClaimSource:
    pointer = fallback_pointer
    if pointer is None:
        for key in ("evidence_pointer", "failed_gate", "debt_row_pointer", "control_pointer"):
            value = row.get(key)
            if isinstance(value, str):
                pointer = value
                break
    if isinstance(pointer, str) and pointer.startswith("reports/") and ":$" in pointer:
        artifact, local_pointer = pointer.split(":", 1)
        return ClaimSource(
            report=str(row["report"]),
            json_artifact=artifact,
            pointer=local_pointer,
        )
    return ClaimSource(
        report=str(row["report"]),
        json_artifact=str(row["json_artifact"]),
        pointer=pointer,
    )


def _discovery_map_row_pointer(root: Path, row: Mapping[str, Any]) -> str:
    rows = _load_discovery_rows(root, generated_at=None)
    for index, candidate in enumerate(rows):
        if (
            candidate.get("report") == row.get("report")
            and candidate.get("json_artifact") == row.get("json_artifact")
        ):
            if candidate.get("discovery_level") is None:
                raise ValueError(f"discovery map row lacks discovery_level cell: {row['report']}")
            return f"reports/canonical/discovery_map.json:$.rows[{index}].discovery_level"
    raise ValueError(f"discovery map ledger row missing for claim: {row['report']}")


def _dgt_scaling_ladder_pointer(row: Mapping[str, Any]) -> str:
    pointer = row.get("scaling_ladder_pointer")
    return pointer if isinstance(pointer, str) else "reports/canonical/scaling-ladder.json:$.levels[0]"


def _dgt_scaling_ladder_open(root: Path, row: Mapping[str, Any]) -> bool:
    owner = resolve_artifact_pointer(root, _dgt_scaling_ladder_pointer(row))
    if not isinstance(owner, Mapping) or owner.get("state") != "open":
        return False
    hardgates = resolve_artifact_pointer(root, "reports/canonical/scaling-ladder.json:$.hardgates")
    if not isinstance(hardgates, Mapping):
        return False
    return all(isinstance(gate, Mapping) and gate.get("status") == "pass" for gate in hardgates.values())


def _discovery_map_audit_pointer(root: Path, row: Mapping[str, Any]) -> str:
    rows = _load_discovery_rows(root, generated_at=None)
    for index, candidate in enumerate(rows):
        if (
            candidate.get("report") == row.get("report")
            and candidate.get("json_artifact") == row.get("json_artifact")
        ):
            return f"reports/canonical/discovery_map.json:$.rows[{index}].audit_status"
    raise ValueError(f"discovery map ledger row missing for claim: {row['report']}")


def _discovery_map_scope_gate_pointer(root: Path, row: Mapping[str, Any]) -> str:
    rows = _load_discovery_rows(root, generated_at=None)
    for index, candidate in enumerate(rows):
        if (
            candidate.get("report") == row.get("report")
            and candidate.get("json_artifact") == row.get("json_artifact")
        ):
            return f"reports/canonical/discovery_map.json:$.rows[{index}].scope_gate"
    raise ValueError(f"discovery map ledger row missing for claim: {row['report']}")


def _hidden_debt_pointer(pointer: Any) -> bool:
    if not isinstance(pointer, str):
        return False
    text = pointer.lower()
    return "cost" in text or "debt" in text


def _rejection_reason_for_pointer(pointer: Any) -> str:
    return "hidden-debt-negative-witness" if _hidden_debt_pointer(pointer) else "negative-witness"


def _row(
    *,
    claim_id: str,
    claim_verdict: str,
    reason: str,
    source: ClaimSource | str,
    ledger_pointer: str | None,
    scorecard_snapshot: ScorecardSnapshot,
) -> dict[str, Any]:
    if not reason:
        raise ValueError(f"claim verdict reason must be non-empty: {claim_id}")
    if not ledger_pointer:
        raise ValueError(f"claim verdict needs a ledger pointer: {claim_id}")
    if claim_verdict not in CLAIM_VERDICTS:
        raise ValueError(f"unsupported claim verdict for {claim_id}: {claim_verdict}")
    source_text = source.as_text() if isinstance(source, ClaimSource) else source
    item = {
        "claim_id": claim_id,
        "claim_graph_node_id": terminal_node_id_for_claim_id(claim_id),
        "claim_verdict": claim_verdict,
        "reason": reason,
        "source": source_text,
        "ledger_pointer": ledger_pointer,
        "scorecard_pointer": scorecard_snapshot.scorecard_pointer,
        "scorecard_hash": scorecard_snapshot.scorecard_hash,
        "scorecard_ready": scorecard_snapshot.scorecard_ready,
        "formal_hardening_ready": scorecard_snapshot.formal_hardening_ready,
    }
    if frozenset(item) != ALLOWED_ROW_KEYS:
        raise ValueError(f"claim verdict row has invalid keys: {sorted(item)}")
    validate_claim_verdict_reason(item)
    return item


def _dimension_mismatch_negative_row(
    *,
    root: Path,
    claim_id: str,
    negative_report_pointer: str,
    payload: Mapping[str, Any],
) -> dict[str, Any]:
    claim = pointer_value(payload, "$.dimension_mismatch_debt_transfer")
    if not isinstance(claim, Mapping):
        raise ValueError("dimension mismatch negative verdict requires source claim node")
    required = ("hypothesis", "failed_gate", "what_was_learned", "downgrade_reason")
    missing = [key for key in required if key not in claim or claim[key] in (None, "")]
    if missing:
        raise ValueError(f"dimension mismatch negative verdict source cells missing: {', '.join(missing)}")
    owner_result = validate_dn_owner_cell(root, negative_report_pointer)
    if not owner_result.ok:
        raise ValueError(f"DN discovery owner evidence missing: {owner_result.missing_key}")
    return _negative_discovery_row(
        claim_id=claim_id,
        reason=reason_for_claim_verdict(
            ClaimVerdictReasonBasis(
                claim_verdict="negative_discovery",
                discovery_level="DN",
                failed_gate=claim.get("failed_gate") if isinstance(claim.get("failed_gate"), str) else None,
            )
        ),
        negative_report_pointer=negative_report_pointer,
        failed_gate=claim.get("failed_gate") if isinstance(claim.get("failed_gate"), str) else None,
    )


def _negative_discovery_row(
    *,
    claim_id: str,
    reason: str,
    negative_report_pointer: str,
    failed_gate: str | None = None,
) -> dict[str, Any]:
    if not negative_report_pointer:
        raise ValueError(f"negative discovery verdict needs negative_report_pointer: {claim_id}")
    item = {
        "claim_id": claim_id,
        "claim_graph_node_id": terminal_node_id_for_claim_id(claim_id),
        "claim_verdict": "negative_discovery",
        "reason": reason,
        "negative_report_pointer": negative_report_pointer,
    }
    if frozenset(item) != DN_VERDICT_ROW_KEYS:
        raise ValueError(f"negative discovery verdict row has invalid keys: {sorted(item)}")
    validate_claim_verdict_reason(
        item,
        basis=ClaimVerdictReasonBasis(
            claim_verdict="negative_discovery",
            discovery_level="DN",
            failed_gate=failed_gate,
        )
        if failed_gate is not None
        else None,
    )
    return item


def _mapped_discovery_row(
    *,
    root: Path,
    row: Mapping[str, Any],
    scorecard_snapshot: ScorecardSnapshot,
    cost_protocol_ready: bool,
    generated_at: str,
) -> dict[str, Any] | None:
    report = str(row["report"])
    level = str(row.get("discovery_level", "D0"))
    source = _claim_source(row)
    claim_id = f"claim:{report}"
    if report == "discovery-gated-transformer" and level in POSITIVE_LEVELS and not _dgt_scaling_ladder_open(root, row):
        owner_pointer = _dgt_scaling_ladder_pointer(row)
        return _row(
            claim_id=claim_id,
            claim_verdict="projected_discovery_required",
            reason="source-insufficient",
            source=owner_pointer,
            ledger_pointer=owner_pointer,
            scorecard_snapshot=scorecard_snapshot,
        )
    if level == "D0":
        return _row(
            claim_id=claim_id,
            claim_verdict="projected_discovery_required",
            reason=reason_for_claim_verdict(
                ClaimVerdictReasonBasis(
                    claim_verdict="projected_discovery_required",
                    discovery_level="D0",
                    report=report,
                    model_comparison_ready=False if report == "discovery-gated-transformer" else None,
                )
            ),
            source=source,
            ledger_pointer=_discovery_map_row_pointer(root, row),
            scorecard_snapshot=scorecard_snapshot,
        )
    if level == "DN" and report not in _specs_by_name() and report != DIMENSION_MISMATCH_REPORT:
        negative_report_pointer = row.get("negative_report_pointer")
        if not isinstance(negative_report_pointer, str):
            raise ValueError(f"DN discovery map row lacks negative_report_pointer: {report}")
        owner = resolve_artifact_pointer(root, negative_report_pointer)
        if not isinstance(owner, Mapping):
            raise ValueError(f"DN discovery map row has unresolved negative_report_pointer: {report}")
        return _negative_discovery_row(
            claim_id=claim_id,
            reason=reason_for_claim_verdict(
                ClaimVerdictReasonBasis(
                    claim_verdict="negative_discovery",
                    discovery_level="DN",
                    failed_gate=owner.get("failed_gate") if isinstance(owner.get("failed_gate"), str) else None,
                )
            ),
            negative_report_pointer=negative_report_pointer,
            failed_gate=owner.get("failed_gate") if isinstance(owner.get("failed_gate"), str) else None,
        )
    specs = _specs_by_name()
    if report == DIMENSION_MISMATCH_REPORT and str(row.get("json_artifact")) == DIMENSION_MISMATCH_ARTIFACT:
        spec = _dimension_mismatch_pointer_spec()
    elif report in specs:
        spec = specs[report]
    else:
        return None
    payload = _load_payload(root, str(row["json_artifact"]))
    scorecard = _load_scorecard(root)
    empirical_owner_ok, empirical_owner_reason = _empirical_claim_support(root, report)

    positive_forbidden = _positive_claim_forbidden_pointer(spec, payload)
    if positive_forbidden is not None:
        hits = _forbidden_hits(pointer_value(payload, positive_forbidden))
        if not hits:
            evidence_result = validate_positive_claim_evidence(
                root,
                spec=spec,
                discovery_row=row,
                payload=payload,
                scorecard_snapshot=scorecard_snapshot,
            )
            if not evidence_result.ok and evidence_result.missing_key == "positive_claim":
                return _row(
                    claim_id=claim_id,
                    claim_verdict="projected_discovery_required",
                    reason=evidence_result.reason,
                    source=_claim_source(row, positive_forbidden),
                    ledger_pointer=evidence_result.ledger_pointer,
                    scorecard_snapshot=scorecard_snapshot,
                )
        reason = "forbidden-overclaim" if hits else "missing-positive-claim-cell"
        return _row(
            claim_id=claim_id,
            claim_verdict="negative_discovery",
            reason=reason,
            source=_claim_source(row, positive_forbidden),
            ledger_pointer=f"{row['json_artifact']}:{positive_forbidden}",
            scorecard_snapshot=scorecard_snapshot,
        )

    laundering_pointer = _scope_laundering_pointer(spec, payload)
    if laundering_pointer is not None:
        return _row(
            claim_id=claim_id,
            claim_verdict="negative_discovery",
            reason="scope-discipline-failed",
            source=_claim_source(row, laundering_pointer),
            ledger_pointer=f"{row['json_artifact']}:{laundering_pointer}",
            scorecard_snapshot=scorecard_snapshot,
        )

    if level in POSITIVE_LEVELS:
        scope_gate = _scope_expansion_gate_for_payload(spec, payload)
        if scope_gate is not None and scope_gate.status == "fail":
            return _row(
                claim_id=claim_id,
                claim_verdict="negative_discovery",
                reason=scope_gate.reason,
                source=_claim_source(row, "scope_gate"),
                ledger_pointer=_scope_expansion_failure_pointer(root, row, scope_gate),
                scorecard_snapshot=scorecard_snapshot,
            )

    projected = _projected_payload(spec=spec, payload=payload, scorecard=scorecard)
    terminal = synthesize_certification_verdict(None, projected, timestamp_iso=generated_at)
    projected_verdict = assign_discovery_level(projected)

    if row.get("audit_status") != "valid":
        return _row(
            claim_id=claim_id,
            claim_verdict="projected_discovery_required",
            reason="discovery-map-audit-not-valid",
            source=source,
            ledger_pointer=_discovery_map_audit_pointer(root, row),
            scorecard_snapshot=scorecard_snapshot,
        )

    if not cost_protocol_ready and level in POSITIVE_LEVELS:
        return _row(
            claim_id=claim_id,
            claim_verdict="negative_discovery",
            reason="cost-protocol-unavailable",
            source=source,
            ledger_pointer=f"{row['json_artifact']}:{spec.cost_pointer}",
            scorecard_snapshot=scorecard_snapshot,
        )

    winnability_block = _winnability_block(root, row, payload) if level in POSITIVE_LEVELS else None
    if winnability_block is not None:
        claim_verdict, reason, ledger_pointer = winnability_block
        return _row(
            claim_id=claim_id,
            claim_verdict=claim_verdict,
            reason=reason,
            source=source,
            ledger_pointer=ledger_pointer,
            scorecard_snapshot=scorecard_snapshot,
        )

    if (
        level in POSITIVE_LEVELS
        and not empirical_owner_ok
        and empirical_owner_reason == "evidence-provenance-owner-missing"
    ):
        return _row(
            claim_id=claim_id,
            claim_verdict="projected_discovery_required",
            reason=CLAIM_FIRST_DATA_CARD_REASON,
            source=source,
            ledger_pointer=str(row.get("evidence_provenance_pointer") or "reports/canonical/index.json:$.evidence_provenance"),
            scorecard_snapshot=scorecard_snapshot,
        )

    if not scorecard_snapshot.scorecard_hash and level in POSITIVE_LEVELS:
        evidence_result = validate_positive_claim_evidence(
            root,
            spec=spec,
            discovery_row=row,
            payload=payload,
            scorecard_snapshot=scorecard_snapshot,
        )
        return _row(
            claim_id=claim_id,
            claim_verdict="projected_discovery_required",
            reason=reason_for_claim_verdict(
                ClaimVerdictReasonBasis(
                    claim_verdict="projected_discovery_required",
                    discovery_level=level,
                    source_insufficient=True,
                )
            ),
            source=source,
            ledger_pointer=evidence_result.ledger_pointer,
            scorecard_snapshot=scorecard_snapshot,
        )

    if not scorecard_snapshot.scorecard_ready and level in POSITIVE_LEVELS:
        evidence_result = validate_positive_claim_evidence(
            root,
            spec=spec,
            discovery_row=row,
            payload=payload,
            scorecard_snapshot=scorecard_snapshot,
        )
        return _row(
            claim_id=claim_id,
            claim_verdict="projected_discovery_required",
            reason=reason_for_claim_verdict(
                ClaimVerdictReasonBasis(
                    claim_verdict="projected_discovery_required",
                    discovery_level=level,
                    source_insufficient=True,
                )
            ),
            source=source,
            ledger_pointer=evidence_result.ledger_pointer,
            scorecard_snapshot=scorecard_snapshot,
        )

    if terminal.get("verdict") == "demoted":
        return _row(
            claim_id=claim_id,
            claim_verdict="revoked_discovery",
            reason=str(terminal.get("reason") or "demoted"),
            source=source,
            ledger_pointer=f"{row['json_artifact']}:{row.get('debt_row_pointer') or spec.cost_pointer}",
            scorecard_snapshot=scorecard_snapshot,
        )

    if level in POSITIVE_LEVELS:
        if projected_verdict.discovery_level not in POSITIVE_LEVELS:
            return _row(
                claim_id=claim_id,
                claim_verdict="raw_operational_evidence_pass" if projected_verdict.discovery_level == "D1" else _positive_blocker_verdict(report, level, row, payload, projected),
                reason=f"fresh-discovery-level-{projected_verdict.discovery_level}:{','.join(projected_verdict.reasons)}",
                source=source,
                ledger_pointer=_discovery_map_row_pointer(root, row),
                scorecard_snapshot=scorecard_snapshot,
            )
        if (
            scorecard_snapshot.scorecard_ready
            and cost_protocol_ready
            and projected_verdict.control_positive is not True
            and _net_positive_signal(payload, projected)
        ):
            if _is_mechanism_open(row, level):
                return _row(
                    claim_id=claim_id,
                    claim_verdict="mechanism_not_closed",
                    reason=reason_for_claim_verdict(
                        ClaimVerdictReasonBasis(
                            claim_verdict="mechanism_not_closed",
                            discovery_level=level,
                            mechanism_open=True,
                        )
                    ),
                    source=source,
                    ledger_pointer=_discovery_map_row_pointer(root, row),
                    scorecard_snapshot=scorecard_snapshot,
                )
            evidence_result = validate_positive_claim_evidence(
                root,
                spec=spec,
                discovery_row=row,
                payload=payload,
                scorecard_snapshot=scorecard_snapshot,
            )
            if not evidence_result.ok:
                return _row(
                    claim_id=claim_id,
                    claim_verdict="projected_discovery_required",
                    reason=evidence_result.reason,
                    source=source,
                    ledger_pointer=evidence_result.ledger_pointer,
                    scorecard_snapshot=scorecard_snapshot,
                )
            high_impact_failure = (
                None
                if report == "discovery-gated-transformer"
                else high_impact_review_failure_pointer(root, spec, payload)
            )
            if high_impact_failure is not None:
                return _row(
                    claim_id=claim_id,
                    claim_verdict="projected_discovery_required",
                    reason="high-impact-review-required",
                    source=_claim_source(row, high_impact_failure),
                    ledger_pointer=f"{row['json_artifact']}:{high_impact_failure}",
                    scorecard_snapshot=scorecard_snapshot,
                )
            if not empirical_owner_ok:
                return _row(
                    claim_id=claim_id,
                    claim_verdict="projected_discovery_required",
                    reason=(
                        CLAIM_FIRST_DATA_CARD_REASON
                        if empirical_owner_reason == "evidence-provenance-owner-missing"
                        else empirical_owner_reason
                    ),
                    source=source,
                    ledger_pointer=str(row.get("evidence_provenance_pointer") or "reports/canonical/index.json:$.evidence_provenance"),
                    scorecard_snapshot=scorecard_snapshot,
                )
            return _row(
                claim_id=claim_id,
                claim_verdict="accepted_positive_discovery",
                reason=(
                    POSITIVE_DISCOVERY_GATES_PASS
                    if report == "discovery-gated-transformer"
                    else reason_for_claim_verdict(
                        ClaimVerdictReasonBasis(
                            claim_verdict="accepted_positive_discovery",
                            discovery_level=level,
                        )
                    )
                ),
                source=source,
                ledger_pointer=_discovery_map_row_pointer(root, row),
                scorecard_snapshot=scorecard_snapshot,
            )
        blocker_verdict = _positive_blocker_verdict(report, level, row, payload, projected)
        return _row(
            claim_id=claim_id,
            claim_verdict=blocker_verdict,
            reason=reason_for_claim_verdict(
                ClaimVerdictReasonBasis(
                    claim_verdict=blocker_verdict,
                    discovery_level=level,
                    mechanism_open=blocker_verdict == "mechanism_not_closed",
                )
            ),
            source=source,
            ledger_pointer=f"{row['json_artifact']}:{row.get('control_pointer') or spec.control_pointer or spec.positive_claim_pointer}",
            scorecard_snapshot=scorecard_snapshot,
        )

    if level == "D1":
        return _row(
            claim_id=claim_id,
            claim_verdict="raw_operational_evidence_pass",
            reason=reason_for_claim_verdict(
                ClaimVerdictReasonBasis(claim_verdict="raw_operational_evidence_pass", discovery_level="D1")
            ),
            source=source,
            ledger_pointer=_discovery_map_row_pointer(root, row),
            scorecard_snapshot=scorecard_snapshot,
        )
    if level == "D2":
        return _row(
            claim_id=claim_id,
            claim_verdict="projected_discovery_required",
            reason=reason_for_claim_verdict(
                ClaimVerdictReasonBasis(claim_verdict="projected_discovery_required", discovery_level="D2")
            ),
            source=source,
            ledger_pointer=_discovery_map_row_pointer(root, row),
            scorecard_snapshot=scorecard_snapshot,
        )
    if level == "D3":
        return _row(
            claim_id=claim_id,
            claim_verdict="projected_discovery_required",
            reason=reason_for_claim_verdict(
                ClaimVerdictReasonBasis(claim_verdict="projected_discovery_required", discovery_level="D3")
            ),
            source=source,
            ledger_pointer=_discovery_map_row_pointer(root, row),
            scorecard_snapshot=scorecard_snapshot,
        )
    if level == "DN":
        negative_report_pointer = row.get("negative_report_pointer")
        owner: Mapping[str, Any] | None = None
        if not isinstance(negative_report_pointer, str):
            owner_path = root / "reports/canonical/negative_discovery_reports.json"
            if owner_path.exists():
                raise ValueError(f"DN discovery map row lacks negative_report_pointer: {report}")
            negative_report_pointer = f"{row['json_artifact']}:{row.get('failed_gate') or row.get('debt_row_pointer') or row.get('evidence_pointer')}"
        else:
            resolved_owner = resolve_artifact_pointer(root, negative_report_pointer)
            if not isinstance(resolved_owner, Mapping):
                raise ValueError(f"DN discovery map row has unresolved negative_report_pointer: {report}")
            owner = resolved_owner
        if report == DIMENSION_MISMATCH_REPORT:
            return _dimension_mismatch_negative_row(
                root=root,
                claim_id=claim_id,
                negative_report_pointer=negative_report_pointer,
                payload=payload,
            )
        owner_result = validate_dn_owner_cell(root, negative_report_pointer)
        if not owner_result.ok:
            raise ValueError(f"DN discovery owner evidence missing: {owner_result.missing_key}")
        failed_gate = owner.get("failed_gate") if owner is not None and isinstance(owner.get("failed_gate"), str) else row.get("failed_gate")
        return _negative_discovery_row(
            claim_id=claim_id,
            reason=reason_for_claim_verdict(
                ClaimVerdictReasonBasis(
                    claim_verdict="negative_discovery",
                    discovery_level="DN",
                    failed_gate=failed_gate if isinstance(failed_gate, str) else None,
                )
            ),
            negative_report_pointer=negative_report_pointer,
            failed_gate=failed_gate if isinstance(failed_gate, str) else None,
        )
    if level == "DR":
        pointer = row.get("failed_gate") or row.get("debt_row_pointer") or row.get("evidence_pointer")
        return _row(
            claim_id=claim_id,
            claim_verdict="revoked_discovery",
            reason="discovery-level-DR",
            source=source,
            ledger_pointer=f"{row['json_artifact']}:{pointer}",
            scorecard_snapshot=scorecard_snapshot,
        )
    raise ValueError(f"unsupported discovery level for {report}: {level}")


def _witness_pointer(index: int) -> str:
    return f"reports/canonical/discovery_negative_witnesses.json:$.witnesses[{index}]"


def _witness_row(witness: Mapping[str, Any], index: int, scorecard_snapshot: ScorecardSnapshot) -> dict[str, Any]:
    kind = str(witness["kind"])
    terminal = str(witness.get("terminal_verdict", ""))
    level = str(witness.get("discovery_level", ""))
    basis = witness.get("gate_basis")
    basis = basis if isinstance(basis, Mapping) else {}
    pointer = _witness_pointer(index)
    source = f"reports/canonical/discovery_negative_witnesses.json:$.witnesses[{index}]"

    if kind == "hidden_debt_positive":
        verdict = "revoked_discovery"
        reason = str(witness.get("terminal_reason") or "hidden-debt-positive")
    elif kind == "fresh_claim_downgrade" or level == "DR":
        verdict = "revoked_discovery"
        reason = str(witness.get("terminal_reason") or "fresh-evidence-revocation")
    elif terminal == "demoted" and basis.get("new_status") == "audit-improvement-tradeoff":
        verdict = "revoked_discovery"
        reason = str(witness.get("terminal_reason") or "hidden-debt-positive")
    elif basis.get("forbidden_claim_term_hits"):
        verdict = "negative_discovery"
        reason = "forbidden-overclaim"
    elif terminal == "ledger-only" and basis.get("scorecard_ready") is False:
        verdict = "projected_discovery_required"
        reason = str(witness.get("terminal_reason") or "scorecard-not-ready")
    elif terminal in {"rejected", "ledger-only"} or level == "DN":
        pointer_hint = basis.get("malformed_detail") or witness.get("terminal_reason") or kind
        verdict = "negative_discovery" if terminal == "rejected" or level == "DN" else "projected_discovery_required"
        reason = str(witness.get("terminal_reason") or _rejection_reason_for_pointer(pointer_hint))
    else:
        raise ValueError(f"unsupported witness verdict basis: {kind}")

    return _row(
        claim_id=f"claim:witness:{kind}",
        claim_verdict=verdict,
        reason=reason,
        source=source,
        ledger_pointer=pointer,
        scorecard_snapshot=scorecard_snapshot,
    )


def _load_witnesses(root: Path) -> list[dict[str, Any]]:
    path = _artifact_path(root, "reports/canonical/discovery_negative_witnesses.json")
    if not path.exists():
        return []
    payload = _load_json(path)
    witnesses = payload.get("witnesses") if isinstance(payload, Mapping) else None
    if not isinstance(witnesses, list) or not all(isinstance(row, dict) for row in witnesses):
        raise ValueError("discovery negative witnesses must be a JSON object with witness rows")
    return witnesses


def compile_claim_verdicts(root: Path, generated_at: str | None = None) -> list[dict[str, Any]]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    root = _root(root)
    scorecard_snapshot = load_scorecard_snapshot(root)
    cost_protocol_ready = _cost_protocol_loads(root)
    rows: list[dict[str, Any]] = []
    for discovery in _load_discovery_rows(root, timestamp):
        verdict = _mapped_discovery_row(
            root=root,
            row=discovery,
            scorecard_snapshot=scorecard_snapshot,
            cost_protocol_ready=cost_protocol_ready,
            generated_at=timestamp,
        )
        if verdict is not None:
            rows.append(verdict)
    rows.extend(_witness_row(witness, index, scorecard_snapshot) for index, witness in enumerate(_load_witnesses(root)))
    return rows


def write_claim_verdicts(*, root: Path | None = None, generated_at: str | None = None) -> list[dict[str, Any]]:
    base = _root(root)
    rows = compile_claim_verdicts(base, generated_at=generated_at)
    path = _artifact_path(base, CLAIM_VERDICTS_JSONL_ARTIFACT)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows), encoding="utf-8")
    tmp.replace(path)
    return rows


def claim_verdict_line_refs(*, root: Path | None = None) -> dict[str, str]:
    base = _root(root)
    path = _artifact_path(base, CLAIM_VERDICTS_JSONL_ARTIFACT)
    if not path.exists():
        return {}
    refs: dict[str, str] = {}
    for index, line in enumerate(path.read_text(encoding="utf-8").splitlines()):
        if not line:
            continue
        row = json.loads(line)
        if isinstance(row, Mapping) and isinstance(row.get("claim_id"), str):
            refs[row["claim_id"]] = f"{CLAIM_VERDICTS_JSONL_ARTIFACT}:$.lines[{index}]"
    return refs


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="Lab root containing reports/canonical.")
    parser.add_argument("--generated-at", default=None, help="Override the generated_at timestamp for deterministic regeneration.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    rows = write_claim_verdicts(root=args.root, generated_at=args.generated_at)
    print(f"wrote {len(rows)} claim verdict rows to {CLAIM_VERDICTS_JSONL_ARTIFACT}")


if __name__ == "__main__":
    main()

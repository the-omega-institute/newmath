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

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.cost_protocol import load_cost_protocol
from bedc_quality_lab.research_discovery import assign_discovery_level
from bedc_quality_lab.verdict import _scorecard_readiness, synthesize_certification_verdict
from scripts.run_canonical_reports import CANONICAL_REPORTS, CanonicalReportSpec
from scripts.run_discovery_map import build_discovery_map, pointer_value, projection_payload


CLAIM_VERDICTS_JSONL_ARTIFACT = "reports/canonical/claim_verdicts.jsonl"
CLAIM_VERDICTS_ARTIFACT_ID = "bedc-quality-lab:claim-verdicts"
ALLOWED_ROW_KEYS = frozenset({"claim_id", "claim_verdict", "reason", "source", "ledger_pointer"})
DIMENSION_MISMATCH_ALLOWED_ROW_KEYS = frozenset(
    {
        "claim_id",
        "claim_verdict",
        "reason",
        "source",
        "ledger_pointer",
        "hypothesis",
        "failed_gate",
        "what_was_learned",
        "downgrade_reason",
    }
)
E1_TERMINAL_VERDICTS = frozenset(
    {
        "ledger_only_hardening_not_ready",
        "rejected_hidden_debt",
        "rejected_scope_laundering",
        "demoted_audit_tradeoff",
        "accepted_positive_discovery",
    }
)
POSITIVE_LEVELS = frozenset({"D4", "D5", "D5-O"})
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
        payload = _load_json(path)
        rows = payload.get("rows") if isinstance(payload, Mapping) else None
        if isinstance(rows, list) and all(isinstance(row, dict) for row in rows):
            return rows
    return list(build_discovery_map(generated_at=generated_at, root=root, canonical_reports=CANONICAL_REPORTS)["rows"])


def _load_scorecard(root: Path) -> dict[str, Any] | None:
    path = _artifact_path(root, "reports/canonical/quality-scorecard.json")
    if not path.exists():
        return None
    payload = _load_json(path)
    return payload if isinstance(payload, dict) else None


def _scorecard_ready(scorecard: Mapping[str, Any] | None) -> bool:
    if scorecard is None:
        return False
    ready, _detail = _scorecard_readiness({"quality_scorecard": scorecard})
    return ready is True


def _scorecard_dependency_pointer(scorecard: Mapping[str, Any] | None) -> str:
    if scorecard is None:
        return f"{SCORECARD_ARTIFACT}:$.rows"
    rows = scorecard.get("rows")
    if not isinstance(rows, list):
        return f"{SCORECARD_ARTIFACT}:$.rows"
    for index, row in enumerate(rows):
        if not isinstance(row, Mapping):
            return f"{SCORECARD_ARTIFACT}:$.rows[{index}]"
        if row.get("metric") == "HardeningCoverage" and row.get("status") != "ready":
            return f"{SCORECARD_ARTIFACT}:$.rows[{index}]"
    for index, row in enumerate(rows):
        if isinstance(row, Mapping) and row.get("status") != "ready":
            return f"{SCORECARD_ARTIFACT}:$.rows[{index}]"
    return f"{SCORECARD_ARTIFACT}:$.rows"


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


def _discovery_map_audit_pointer(root: Path, row: Mapping[str, Any]) -> str:
    rows = _load_discovery_rows(root, generated_at=None)
    for index, candidate in enumerate(rows):
        if (
            candidate.get("report") == row.get("report")
            and candidate.get("json_artifact") == row.get("json_artifact")
        ):
            return f"reports/canonical/discovery_map.json:$.rows[{index}].audit_status"
    raise ValueError(f"discovery map ledger row missing for claim: {row['report']}")


def _hidden_debt_pointer(pointer: Any) -> bool:
    if not isinstance(pointer, str):
        return False
    text = pointer.lower()
    return "cost" in text or "debt" in text


def _rejection_verdict_for_pointer(pointer: Any) -> str:
    return "rejected_hidden_debt" if _hidden_debt_pointer(pointer) else "ledger_only_hardening_not_ready"


def _row(
    *,
    claim_id: str,
    claim_verdict: str,
    reason: str,
    source: ClaimSource | str,
    ledger_pointer: str | None,
) -> dict[str, Any]:
    if not reason:
        raise ValueError(f"claim verdict reason must be non-empty: {claim_id}")
    if not ledger_pointer:
        raise ValueError(f"claim verdict needs a ledger pointer: {claim_id}")
    if claim_verdict not in E1_TERMINAL_VERDICTS:
        raise ValueError(f"unsupported E1 claim verdict for {claim_id}: {claim_verdict}")
    source_text = source.as_text() if isinstance(source, ClaimSource) else source
    item = {
        "claim_id": claim_id,
        "claim_verdict": claim_verdict,
        "reason": reason,
        "source": source_text,
        "ledger_pointer": ledger_pointer,
    }
    if frozenset(item) != ALLOWED_ROW_KEYS:
        raise ValueError(f"claim verdict row has invalid keys: {sorted(item)}")
    return item


def _dimension_mismatch_negative_row(
    *,
    claim_id: str,
    reason: str,
    source: ClaimSource | str,
    ledger_pointer: str,
    payload: Mapping[str, Any],
) -> dict[str, Any]:
    claim = pointer_value(payload, "$.dimension_mismatch_debt_transfer")
    if not isinstance(claim, Mapping):
        raise ValueError("dimension mismatch negative verdict requires source claim node")
    required = ("hypothesis", "failed_gate", "what_was_learned", "downgrade_reason")
    missing = [key for key in required if key not in claim or claim[key] in (None, "")]
    if missing:
        raise ValueError(f"dimension mismatch negative verdict source cells missing: {', '.join(missing)}")
    source_text = source.as_text() if isinstance(source, ClaimSource) else source
    item = {
        "claim_id": claim_id,
        "claim_verdict": "negative_discovery",
        "reason": reason,
        "source": source_text,
        "ledger_pointer": ledger_pointer,
        "hypothesis": str(claim["hypothesis"]),
        "failed_gate": str(claim["failed_gate"]),
        "what_was_learned": str(claim["what_was_learned"]),
        "downgrade_reason": str(claim["downgrade_reason"]),
    }
    if frozenset(item) != DIMENSION_MISMATCH_ALLOWED_ROW_KEYS:
        raise ValueError(f"dimension mismatch claim verdict row has invalid keys: {sorted(item)}")
    return item


def _mapped_discovery_row(
    *,
    root: Path,
    row: Mapping[str, Any],
    scorecard_ready: bool,
    cost_protocol_ready: bool,
    generated_at: str,
) -> dict[str, Any] | None:
    report = str(row["report"])
    level = str(row.get("discovery_level", "D0"))
    source = _claim_source(row)
    claim_id = f"claim:{report}"
    if level == "D0":
        return _row(
            claim_id=claim_id,
            claim_verdict="ledger_only_hardening_not_ready",
            reason="discovery-level-D0",
            source=source,
            ledger_pointer=_discovery_map_row_pointer(root, row),
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

    positive_forbidden = _positive_claim_forbidden_pointer(spec, payload)
    if positive_forbidden is not None:
        hits = _forbidden_hits(pointer_value(payload, positive_forbidden))
        reason = "forbidden-overclaim" if hits else "missing-positive-claim-cell"
        return _row(
            claim_id=claim_id,
            claim_verdict="rejected_scope_laundering",
            reason=reason,
            source=_claim_source(row, positive_forbidden),
            ledger_pointer=f"{row['json_artifact']}:{positive_forbidden}",
        )

    laundering_pointer = _scope_laundering_pointer(spec, payload)
    if laundering_pointer is not None:
        return _row(
            claim_id=claim_id,
            claim_verdict="rejected_scope_laundering",
            reason="scope-discipline-failed",
            source=_claim_source(row, laundering_pointer),
            ledger_pointer=f"{row['json_artifact']}:{laundering_pointer}",
        )

    projected = _projected_payload(spec=spec, payload=payload, scorecard=scorecard)
    terminal = synthesize_certification_verdict(None, projected, timestamp_iso=generated_at)
    projected_verdict = assign_discovery_level(projected)

    if row.get("audit_status") != "valid":
        return _row(
            claim_id=claim_id,
            claim_verdict="ledger_only_hardening_not_ready",
            reason="discovery-map-audit-not-valid",
            source=source,
            ledger_pointer=_discovery_map_audit_pointer(root, row),
        )

    if not cost_protocol_ready and level in POSITIVE_LEVELS:
        return _row(
            claim_id=claim_id,
            claim_verdict="rejected_hidden_debt",
            reason="cost-protocol-unavailable",
            source=source,
            ledger_pointer=f"{row['json_artifact']}:{spec.cost_pointer}",
        )

    if not scorecard_ready and level in POSITIVE_LEVELS:
        return _row(
            claim_id=claim_id,
            claim_verdict="ledger_only_hardening_not_ready",
            reason="scorecard-not-ready",
            source=source,
            ledger_pointer=_scorecard_dependency_pointer(scorecard),
        )

    if terminal.get("verdict") == "demoted":
        return _row(
            claim_id=claim_id,
            claim_verdict="demoted_audit_tradeoff",
            reason=str(terminal.get("reason") or "demoted"),
            source=source,
            ledger_pointer=f"{row['json_artifact']}:{row.get('debt_row_pointer') or spec.cost_pointer}",
        )

    if level in POSITIVE_LEVELS:
        if (
            scorecard_ready
            and cost_protocol_ready
            and projected_verdict.control_positive is not True
            and _net_positive_signal(payload, projected)
        ):
            return _row(
                claim_id=claim_id,
                claim_verdict="accepted_positive_discovery",
                reason="positive-discovery-gates-pass",
                source=source,
                ledger_pointer=_discovery_map_row_pointer(root, row),
            )
        return _row(
            claim_id=claim_id,
            claim_verdict="ledger_only_hardening_not_ready",
            reason="positive-discovery-gate-failed",
            source=source,
            ledger_pointer=f"{row['json_artifact']}:{row.get('control_pointer') or spec.control_pointer or spec.positive_claim_pointer}",
        )

    if level == "D1":
        return _row(
            claim_id=claim_id,
            claim_verdict="demoted_audit_tradeoff",
            reason="discovery-level-D1",
            source=source,
            ledger_pointer=_discovery_map_row_pointer(root, row),
        )
    if level == "D2":
        return _row(
            claim_id=claim_id,
            claim_verdict="ledger_only_hardening_not_ready",
            reason="discovery-level-D2",
            source=source,
            ledger_pointer=_discovery_map_row_pointer(root, row),
        )
    if level == "D3":
        return _row(
            claim_id=claim_id,
            claim_verdict="ledger_only_hardening_not_ready",
            reason="discovery-level-D3",
            source=source,
            ledger_pointer=_discovery_map_row_pointer(root, row),
        )
    if level == "DN":
        pointer = row.get("failed_gate") or row.get("debt_row_pointer") or row.get("evidence_pointer")
        if report == DIMENSION_MISMATCH_REPORT:
            return _dimension_mismatch_negative_row(
                claim_id=claim_id,
                reason="discovery-level-DN",
                source=source,
                ledger_pointer=f"{row['json_artifact']}:{pointer}",
                payload=payload,
            )
        return _row(
            claim_id=claim_id,
            claim_verdict=_rejection_verdict_for_pointer(pointer),
            reason="discovery-level-DN:constraint_lagrangian"
            if report == "certificate-guided-training"
            else "discovery-level-DN",
            source=source,
            ledger_pointer=f"{row['json_artifact']}:{pointer}",
        )
    if level == "DR":
        pointer = row.get("failed_gate") or row.get("debt_row_pointer") or row.get("evidence_pointer")
        return _row(
            claim_id=claim_id,
            claim_verdict="demoted_audit_tradeoff",
            reason="discovery-level-DR",
            source=source,
            ledger_pointer=f"{row['json_artifact']}:{pointer}",
        )
    raise ValueError(f"unsupported discovery level for {report}: {level}")


def _witness_pointer(index: int) -> str:
    return f"reports/canonical/discovery_negative_witnesses.json:$.witnesses[{index}]"


def _witness_row(witness: Mapping[str, Any], index: int) -> dict[str, Any]:
    kind = str(witness["kind"])
    terminal = str(witness.get("terminal_verdict", ""))
    level = str(witness.get("discovery_level", ""))
    basis = witness.get("gate_basis")
    basis = basis if isinstance(basis, Mapping) else {}
    pointer = _witness_pointer(index)
    source = f"reports/canonical/discovery_negative_witnesses.json:$.witnesses[{index}]"

    if kind == "hidden_debt_positive":
        verdict = "demoted_audit_tradeoff"
        reason = str(witness.get("terminal_reason") or "hidden-debt-positive")
    elif kind == "fresh_claim_downgrade" or level == "DR":
        verdict = "demoted_audit_tradeoff"
        reason = str(witness.get("terminal_reason") or "fresh-evidence-revocation")
    elif terminal == "demoted" and basis.get("new_status") == "audit-improvement-tradeoff":
        verdict = "demoted_audit_tradeoff"
        reason = str(witness.get("terminal_reason") or "hidden-debt-positive")
    elif basis.get("forbidden_claim_term_hits"):
        verdict = "rejected_scope_laundering"
        reason = "forbidden-overclaim"
    elif terminal == "ledger-only" and basis.get("scorecard_ready") is False:
        verdict = "ledger_only_hardening_not_ready"
        reason = str(witness.get("terminal_reason") or "scorecard-not-ready")
    elif terminal in {"rejected", "ledger-only"} or level == "DN":
        pointer_hint = basis.get("malformed_detail") or witness.get("terminal_reason") or kind
        verdict = _rejection_verdict_for_pointer(pointer_hint)
        reason = str(witness.get("terminal_reason") or "negative-witness")
    else:
        raise ValueError(f"unsupported witness verdict basis: {kind}")

    return _row(
        claim_id=f"claim:witness:{kind}",
        claim_verdict=verdict,
        reason=reason,
        source=source,
        ledger_pointer=pointer,
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
    scorecard_ready = _scorecard_ready(_load_scorecard(root))
    cost_protocol_ready = _cost_protocol_loads(root)
    rows: list[dict[str, Any]] = []
    for discovery in _load_discovery_rows(root, timestamp):
        verdict = _mapped_discovery_row(
            root=root,
            row=discovery,
            scorecard_ready=scorecard_ready,
            cost_protocol_ready=cost_protocol_ready,
            generated_at=timestamp,
        )
        if verdict is not None:
            rows.append(verdict)
    rows.extend(_witness_row(witness, index) for index, witness in enumerate(_load_witnesses(root)))
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


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="Lab root containing reports/canonical.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    rows = write_claim_verdicts(root=args.root)
    print(f"wrote {len(rows)} claim verdict rows to {CLAIM_VERDICTS_JSONL_ARTIFACT}")


if __name__ == "__main__":
    main()

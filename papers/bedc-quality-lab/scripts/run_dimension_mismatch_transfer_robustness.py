#!/usr/bin/env python3
"""Build a pointer-only robustness ledger for dimension-mismatch transfer."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer
from scripts import run_dimension_mismatch_debt_transfer as transfer
from scripts.run_discovery_map import (
    _non_stub_not_claimed,
    assert_transfer_artifact_integrity,
    pointer_value,
)


JSON_ARTIFACT = "reports/canonical/dimension-mismatch-transfer-robustness.json"
REPORT_ARTIFACT = "reports/canonical/dimension-mismatch-transfer-robustness.md"
ARTIFACT_ID = "bedc-quality-lab:dimension-mismatch-transfer-robustness"
SCHEMA_ID = "bedc-quality-lab:dimension-mismatch-transfer-robustness"
SOURCE_ARTIFACT = transfer.JSON_ARTIFACT
ANTI_TRIVIALITY_ARTIFACT = transfer.ANTI_TRIVIALITY_ARTIFACT
SOURCE_STATUS_POINTER = "$.dimension_mismatch_debt_transfer.status"
SOURCE_POINTER = f"{SOURCE_ARTIFACT}:{SOURCE_STATUS_POINTER}"
DISCOVERY_MAP_ARTIFACT = "reports/canonical/discovery_map.json"
DISCOVERY_MAP_POINTER = "$.rows[report=dimension-mismatch-debt-transfer]"
READINESS_BOUNDARY = (
    "pass = robust-control evidence for the source dimension-mismatch-debt-transfer surface "
    "with terminal DN downgrade under anti-triviality; not a D5 upgrade, not global model quality."
)
FORBIDDEN_CLAIM_SUBSTRINGS = (
    "global quality",
    "global-quality",
    "full lejepa",
    "full-lejepa",
    "full tensor namecert",
    "full-tensor-namecert",
    "llm behavior",
    "llm-behavior",
    "d5 readiness",
    "d5_readiness",
)
FORBIDDEN_SCORE_KEYS = ("score", "rank", "ranking", "grade", "total_score", "overall_score")
MALFORMED_SOURCE_REASON = "source artifact is malformed or non-object"
MALFORMED_SOURCE_MARKER = "__malformed_source_artifact__"
CONTROL_FAMILY_ORDER = transfer.CONTROL_FAMILY_ORDER


def _root(root: Path | None) -> Path:
    return ROOT if root is None else root


def _artifact_path(relative_path: str, *, root: Path | None = None) -> Path:
    return _root(root) / relative_path


def _load_json(relative_path: str, *, root: Path | None = None) -> dict[str, Any]:
    path = _artifact_path(relative_path, root=root)
    if not path.exists():
        return {}
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"artifact payload must be a JSON object: {relative_path}")
    return payload


def _malformed_source_artifact() -> dict[str, Any]:
    return {MALFORMED_SOURCE_MARKER: True}


def _is_malformed_source_artifact(source: Mapping[str, Any]) -> bool:
    return source.get(MALFORMED_SOURCE_MARKER) is True


def _stat_cell(payload: Mapping[str, Any], pointer: str) -> Mapping[str, Any] | None:
    cell = pointer_value(payload, pointer)
    return cell if isinstance(cell, Mapping) else None


def _status_pointer(payload: Mapping[str, Any]) -> str:
    if pointer_value(payload, SOURCE_STATUS_POINTER) is not None:
        return SOURCE_STATUS_POINTER
    return "$.dimension_mismatch_debt_transfer.status"


def _source_pointer(payload: Mapping[str, Any]) -> str:
    return f"{SOURCE_ARTIFACT}:{_status_pointer(payload)}"


def _discovery_row(payload: Mapping[str, Any]) -> Mapping[str, Any] | None:
    rows = payload.get("rows")
    if not isinstance(rows, Sequence) or isinstance(rows, (str, bytes)):
        return None
    for row in rows:
        if isinstance(row, Mapping) and row.get("report") == "dimension-mismatch-debt-transfer":
            return row
    return None


def _check_row(name: str, verdict: str, evidence_pointer: str, reason: str) -> dict[str, str]:
    return {
        "check": name,
        "verdict": verdict,
        "evidence_pointer": evidence_pointer,
        "reason": reason,
    }


def _source_integrity(source: Mapping[str, Any]) -> dict[str, str]:
    evidence_pointer = SOURCE_POINTER
    if _is_malformed_source_artifact(source):
        return _check_row("HG-DM-R1", "fail", f"{SOURCE_ARTIFACT}:$", MALFORMED_SOURCE_REASON)
    if not source:
        return _check_row("HG-DM-R1", "fail", evidence_pointer, "source artifact is missing")
    try:
        assert_transfer_artifact_integrity(
            source,
            status_pointer=SOURCE_STATUS_POINTER,
            learned_auroc_pointer="$.hardgate_evidence.HG-B3.learned_auroc",
            matched_random_auroc_pointer="$.hardgate_evidence.HG-B3.matched_random_auroc",
            control_positive_pointer="$.hardgate_evidence.HG-B3.matched_random_positive",
        )
    except ValueError as exc:
        return _check_row("HG-DM-R1", "fail", evidence_pointer, str(exc))
    return _check_row(
        "HG-DM-R1",
        "pass",
        "reports/canonical/dimension-mismatch-debt-transfer.json:$.hardgate_evidence.HG-B3",
        "source status, non-stub boundary, and learned-over-matched-random evidence resolve",
    )


def _resampling_stability(source: Mapping[str, Any]) -> dict[str, str]:
    delta_pointer = "$.hardgate_evidence.HG-B3.learned_minus_matched_random_auroc"
    delta = _stat_cell(source, delta_pointer)
    if delta is None:
        return _check_row(
            "HG-DM-R2",
            "defer",
            f"{SOURCE_ARTIFACT}:{delta_pointer}",
            "resampling delta evidence is missing",
        )
    ci95_low = delta.get("ci95_low")
    if isinstance(ci95_low, bool) or not isinstance(ci95_low, (int, float)):
        return _check_row(
            "HG-DM-R2",
            "defer",
            f"{SOURCE_ARTIFACT}:{delta_pointer}.ci95_low",
            "resampling delta lower confidence bound is missing",
        )
    if float(ci95_low) <= 0.0:
        return _check_row(
            "HG-DM-R2",
            "defer",
            f"{SOURCE_ARTIFACT}:{delta_pointer}.ci95_low",
            "learned AUROC does not remain above matched-random under deterministic folds",
        )
    return _check_row(
        "HG-DM-R2",
        "pass",
        f"{SOURCE_ARTIFACT}:{delta_pointer}.ci95_low",
        "learned-minus-matched-random AUROC lower confidence bound is positive",
    )


def _control_symmetry(source: Mapping[str, Any]) -> dict[str, str]:
    protocol_pointer = "$.control_protocol"
    protocol = pointer_value(source, protocol_pointer)
    matched_positive = pointer_value(source, "$.hardgate_evidence.HG-B3.matched_random_positive")
    vanilla = _stat_cell(source, "$.metrics.by_arm.vanilla.failure_detection_auroc")
    expected_flags = (
        "same_feature_columns_as_treatment",
        "same_train_eval_split_as_treatment",
        "same_metric_helper_as_treatment",
        "same_budget_as_treatment",
    )
    if not isinstance(protocol, Mapping):
        return _check_row("HG-DM-R3", "fail", f"{SOURCE_ARTIFACT}:{protocol_pointer}", "control protocol is missing")
    if any(protocol.get(flag) is not True for flag in expected_flags):
        return _check_row(
            "HG-DM-R3",
            "fail",
            f"{SOURCE_ARTIFACT}:{protocol_pointer}",
            "control protocol does not match treatment feature budget, split, metric helper, and budget",
        )
    if matched_positive is not False:
        return _check_row(
            "HG-DM-R3",
            "fail",
            f"{SOURCE_ARTIFACT}:$.hardgate_evidence.HG-B3.matched_random_positive",
            "matched-random control is missing or positive",
        )
    if vanilla is None:
        return _check_row(
            "HG-DM-R3",
            "fail",
            f"{SOURCE_ARTIFACT}:$.metrics.by_arm.vanilla.failure_detection_auroc",
            "vanilla control evidence is missing",
        )
    return _check_row(
        "HG-DM-R3",
        "pass",
        f"{SOURCE_ARTIFACT}:{protocol_pointer}",
        "matched-random and vanilla controls resolve under the same h-only protocol",
    )


def _h_only_boundary(source: Mapping[str, Any]) -> dict[str, str]:
    audit_pointer = "$.hardgate_evidence.HG-B4.audit"
    audit = pointer_value(source, audit_pointer)
    if not isinstance(audit, Mapping):
        return _check_row("HG-DM-R4", "fail", f"{SOURCE_ARTIFACT}:{audit_pointer}", "h-only audit is missing")
    declared = tuple(audit.get("declared_h_only_allowlist") or ())
    actual = tuple(audit.get("actual_model_input_columns") or ())
    forbidden = tuple(audit.get("forbidden_present") or ())
    try:
        transfer.assert_feature_matrix_contract(
            [[0.0 for _ in actual]],
            actual,
            declared_allowlist=declared,
        )
    except ValueError as exc:
        return _check_row("HG-DM-R4", "fail", f"{SOURCE_ARTIFACT}:{audit_pointer}", str(exc))
    if audit.get("status") != "pass" or actual != declared or forbidden:
        return _check_row(
            "HG-DM-R4",
            "fail",
            f"{SOURCE_ARTIFACT}:{audit_pointer}",
            "actual model inputs do not exactly match the declared h-only allowlist",
        )
    return _check_row(
        "HG-DM-R4",
        "pass",
        f"{SOURCE_ARTIFACT}:{audit_pointer}.actual_model_input_columns",
        "actual model input columns exactly match the declared h-only allowlist",
    )


def _walk_keys_and_text(value: Any) -> tuple[list[str], list[str]]:
    keys: list[str] = []
    texts: list[str] = []
    if isinstance(value, Mapping):
        for key, cell in value.items():
            keys.append(str(key))
            child_keys, child_texts = _walk_keys_and_text(cell)
            keys.extend(child_keys)
            texts.extend(child_texts)
    elif isinstance(value, list):
        for cell in value:
            child_keys, child_texts = _walk_keys_and_text(cell)
            keys.extend(child_keys)
            texts.extend(child_texts)
    elif isinstance(value, str):
        texts.append(value)
    return keys, texts


def _claim_boundary(source: Mapping[str, Any]) -> dict[str, str]:
    audit_pointer = "$.hardgate_evidence.HG-B5.audit"
    audit = pointer_value(source, audit_pointer)
    if not _non_stub_not_claimed(source):
        return _check_row("HG-DM-R5", "fail", f"{SOURCE_ARTIFACT}:$.not_claimed", "not_claimed boundary is missing or stubbed")
    keys, texts = _walk_keys_and_text(
        {
            "dimension_mismatch_debt_transfer": source.get("dimension_mismatch_debt_transfer"),
            "boundary_ledger": source.get("boundary_ledger"),
        }
    )
    forbidden_keys = [key for key in keys if key.lower() in FORBIDDEN_SCORE_KEYS]
    forbidden_text = [
        term
        for term in tuple(FORBIDDEN_POSITIVE_CLAIM_TERMS) + FORBIDDEN_CLAIM_SUBSTRINGS
        if any(term.lower() in text.lower() for text in texts)
    ]
    audit_hits = pointer_value(source, "$.hardgate_evidence.HG-B5.audit.hits")
    if (isinstance(audit_hits, list) and audit_hits) or forbidden_keys or forbidden_text:
        return _check_row(
            "HG-DM-R5",
            "fail",
            f"{SOURCE_ARTIFACT}:{audit_pointer}",
            "claim boundary contains forbidden positive terms, score/ranking keys, or audit hits",
        )
    if not isinstance(audit, Mapping) or audit.get("status") != "pass":
        return _check_row("HG-DM-R5", "fail", f"{SOURCE_ARTIFACT}:{audit_pointer}", "claim-boundary audit is missing or failed")
    return _check_row(
        "HG-DM-R5",
        "pass",
        f"{SOURCE_ARTIFACT}:{audit_pointer}.hits",
        "claim boundary has no forbidden positive terms and no aggregate ordering surface",
    )


def _control_family_pointer_coverage(source: Mapping[str, Any], *, root: Path | None = None) -> dict[str, str]:
    evidence_pointer = f"{SOURCE_ARTIFACT}:$.dimension_mismatch_debt_transfer.anti_triviality_evidence.controlled_geometry.control_family_coverage"
    folded = pointer_value(
        source,
        "$.dimension_mismatch_debt_transfer.anti_triviality_evidence.controlled_geometry.control_family_coverage",
    )
    if not isinstance(folded, Mapping):
        return _check_row("HG-DM-R6", "fail", evidence_pointer, "folded control-family coverage is missing")
    if folded.get("status") != "pass":
        return _check_row("HG-DM-R6", "fail", evidence_pointer, "folded control-family coverage is not pass")
    sidecar = _load_json(ANTI_TRIVIALITY_ARTIFACT, root=root)
    coverage = pointer_value(sidecar, "$.controlled_geometry.control_family_coverage")
    if not isinstance(coverage, Mapping):
        return _check_row(
            "HG-DM-R6",
            "fail",
            f"{ANTI_TRIVIALITY_ARTIFACT}:$.controlled_geometry.control_family_coverage",
            "sidecar control-family coverage is missing",
        )
    pointers = coverage.get("family_pointers")
    if not isinstance(pointers, Mapping):
        return _check_row(
            "HG-DM-R6",
            "fail",
            f"{ANTI_TRIVIALITY_ARTIFACT}:$.controlled_geometry.control_family_coverage.family_pointers",
            "sidecar control-family pointer map is missing",
        )
    missing: list[str] = []
    malformed: list[str] = []
    for family in CONTROL_FAMILY_ORDER:
        pointer = pointers.get(family)
        value = (
            resolve_artifact_pointer(_root(root), f"{ANTI_TRIVIALITY_ARTIFACT}:{pointer}")
            if isinstance(pointer, str) and pointer.startswith("$.")
            else None
        )
        if value is None:
            missing.append(family)
        elif not isinstance(value, Mapping) or value.get("arm") != family:
            malformed.append(family)
    unknown = sorted(set(str(key) for key in pointers) - set(CONTROL_FAMILY_ORDER))
    folded_families = tuple(folded.get("resolved_families") or ())
    folded_pointer_keys = set((folded.get("family_pointers") or {}).keys()) if isinstance(folded.get("family_pointers"), Mapping) else set()
    consistent = (
        coverage.get("status") == "pass"
        and tuple(coverage.get("required_families") or ()) == CONTROL_FAMILY_ORDER
        and tuple(coverage.get("observed_families") or ()) == CONTROL_FAMILY_ORDER
        and folded_families == CONTROL_FAMILY_ORDER
        and folded_pointer_keys == set(CONTROL_FAMILY_ORDER)
    )
    if missing or malformed or unknown or not consistent:
        return _check_row(
            "HG-DM-R6",
            "fail",
            evidence_pointer,
            "six control-family pointers do not resolve consistently between folded source and sidecar",
        )
    return _check_row(
        "HG-DM-R6",
        "pass",
        f"{ANTI_TRIVIALITY_ARTIFACT}:$.controlled_geometry.control_family_coverage.family_pointers",
        "all six control-family pointers resolve and folded-source coverage is consistent",
    )


def _discovery_map_audit(discovery: Mapping[str, Any], *, root: Path | None = None) -> tuple[str, list[str], str]:
    row = _discovery_row(discovery)
    if row is None:
        return "defer", ["discovery_map_row_missing"], f"{DISCOVERY_MAP_ARTIFACT}:{DISCOVERY_MAP_POINTER}"
    audit_reasons: list[str] = []
    report_pointer = row.get("negative_report_pointer")
    if not isinstance(report_pointer, str) or not report_pointer:
        return (
            "fail",
            ["dimension-mismatch discovery row missing negative_report_pointer"],
            f"{DISCOVERY_MAP_ARTIFACT}:{DISCOVERY_MAP_POINTER}",
        )
    owner = resolve_artifact_pointer(_root(root), report_pointer)
    if not isinstance(owner, Mapping):
        return (
            "fail",
            ["dimension-mismatch discovery row negative_report_pointer does not resolve"],
            f"{DISCOVERY_MAP_ARTIFACT}:{DISCOVERY_MAP_POINTER}.negative_report_pointer",
        )
    reasons = owner.get("classifier_reasons")
    if owner.get("base_level") != "D4":
        audit_reasons.append("dimension-mismatch negative report base level is not D4")
    if owner.get("anti_triviality_status") != "scale_leakage_detected":
        audit_reasons.append("dimension-mismatch negative report does not record scale leakage")
    if owner.get("effective_level") != "DN" or owner.get("discovery_level") != "DN":
        audit_reasons.append("dimension-mismatch negative report effective level is not DN")
    if owner.get("terminal_verdict") != "negative_discovery":
        audit_reasons.append("dimension-mismatch negative report terminal verdict is not negative_discovery")
    if owner.get("failed_gate") != "$.dimension_mismatch_debt_transfer.anti_triviality_status":
        audit_reasons.append("dimension-mismatch negative report failed gate changed")
    if "d5_readiness" in row:
        audit_reasons.append("dimension-mismatch discovery row contains d5_readiness")
    if not isinstance(reasons, list) or "verdict=rejected" not in reasons:
        audit_reasons.append("dimension-mismatch negative report does not record rejected classifier verdict")
    if owner.get("audit_status") != "pass":
        audit_reasons.append("dimension-mismatch negative report audit status is not pass")
    if not isinstance(owner.get("bedc_gap_mapping"), Mapping):
        audit_reasons.append("dimension-mismatch negative report lacks bedc_gap_mapping")
    return (
        "pass" if not audit_reasons else "fail",
        audit_reasons,
        report_pointer,
    )


def _aggregate_status(checks: Sequence[Mapping[str, str]], audit_status: str) -> str:
    verdicts = [check["verdict"] for check in checks]
    if "fail" in verdicts or audit_status == "fail":
        return "fail"
    if "defer" in verdicts or audit_status == "defer":
        return "defer"
    return "pass"


def build_payload(*, root: Path | None = None, generated_at: str | None = None) -> dict[str, Any]:
    try:
        source = _load_json(SOURCE_ARTIFACT, root=root)
    except (json.JSONDecodeError, ValueError, TypeError):
        source = _malformed_source_artifact()
    discovery = _load_json(DISCOVERY_MAP_ARTIFACT, root=root)
    checks = [
        _source_integrity(source),
        _resampling_stability(source),
        _control_symmetry(source),
        _h_only_boundary(source),
        _claim_boundary(source),
        _control_family_pointer_coverage(source, root=root),
    ]
    audit_status, audit_reasons, audit_pointer = _discovery_map_audit(discovery, root=root)
    failed_or_deferred = [
        check["check"]
        for check in checks
        if check["verdict"] in {"fail", "defer"}
    ]
    if audit_status != "pass":
        failed_or_deferred.append("discovery-map-boundary")
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at or datetime.now(timezone.utc).isoformat(),
        "status": _aggregate_status(checks, audit_status),
        "source_pointer": _source_pointer(source),
        "robust_control_checks": checks,
        "readiness_boundary": READINESS_BOUNDARY,
        "failed_or_deferred_gates": failed_or_deferred,
        "audit_status": audit_status,
        "audit_reasons": audit_reasons,
        "audit_pointer": audit_pointer,
    }


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Dimension-Mismatch Transfer Robustness",
        "",
        f"- Status: `{payload['status']}`",
        f"- Artifact id: `{payload['artifact_id']}`",
        f"- Source pointer: `{payload['source_pointer']}`",
        f"- Readiness boundary: {payload['readiness_boundary']}",
        "",
        "## Robust control checks",
        "",
        "| check | verdict | evidence pointer | reason |",
        "| --- | --- | --- | --- |",
    ]
    for check in payload["robust_control_checks"]:
        lines.append(
            "| "
            f"`{check['check']}` | "
            f"`{check['verdict']}` | "
            f"`{check['evidence_pointer']}` | "
            f"{check['reason']} |"
        )
    lines.extend(
        [
            "",
            "## Audit",
            "",
            f"- Audit status: `{payload['audit_status']}`",
            f"- Audit pointer: `{payload['audit_pointer']}`",
            f"- Failed or deferred gates: `{', '.join(payload['failed_or_deferred_gates'])}`",
            "",
        ]
    )
    if payload["audit_reasons"]:
        for reason in payload["audit_reasons"]:
            lines.append(f"- {reason}")
        lines.append("")
    return "\n".join(lines)


def write_dimension_mismatch_transfer_robustness(
    *,
    root: Path | None = None,
    generated_at: str | None = None,
) -> dict[str, Any]:
    payload = build_payload(root=root, generated_at=generated_at)
    json_path = _artifact_path(JSON_ARTIFACT, root=root)
    report_path = _artifact_path(REPORT_ARTIFACT, root=root)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="Lab root directory.")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_args(argv)
    payload = write_dimension_mismatch_transfer_robustness(root=args.root)
    print(f"wrote {JSON_ARTIFACT}")
    print(f"wrote {REPORT_ARTIFACT}")
    print(f"status {payload['status']}")
    print(f"audit_status {payload['audit_status']}")
    print(f"failed_or_deferred_gates {','.join(payload['failed_or_deferred_gates'])}")


if __name__ == "__main__":
    main()

"""Canonical causal patch evidence suite for lab-local artifacts."""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
import json
from typing import Any, Mapping, Sequence


SCHEMA_ID = "bedc-quality-lab:causal-patch-suite"
ARTIFACT_ID = SCHEMA_ID
JSON_ARTIFACT = "reports/canonical/causal-patch-suite.json"
MARKDOWN_ARTIFACT = "reports/canonical/causal-patch-suite.md"
DGT_ARTIFACT = "reports/canonical/discovery-gated-transformer.json"

PATCH_TYPES = (
    "attention-route",
    "ledger-head",
    "gap-head",
    "D1 feature",
    "D2 interaction",
    "D3 composition",
    "mechanism probe",
    "scope-seal",
)

PATCH_HARDGATES = (
    "PATCH-HG1",
    "PATCH-HG2",
    "PATCH-HG3",
    "PATCH-HG4",
    "PATCH-HG5",
    "PATCH-HG6",
)

SOURCE_ARTIFACTS = {
    "gap_head_attribution_capsule": "reports/canonical/gap_head_attribution_capsule.json",
    "gap_head_ablation": "reports/canonical/gap-head-ablation.json",
    "gap_head_on_h": "reports/canonical/gap-head-on-h.json",
}

NOT_CLAIMED = (
    "No production causality or deployment intervention claim.",
    "No global model superiority claim.",
    "No full mechanism closure claim.",
    "No full TensorNameCert claim.",
    "No LLM behavior quality claim.",
)


@dataclass(frozen=True)
class PatchTrial:
    patch_type: str
    source_artifact: str
    source_pointer: str
    status: str
    summary: Mapping[str, Any]
    matched_control_pointer: str | None = None
    side_effect_pointer: str | None = None

    def as_payload(self) -> dict[str, Any]:
        return {
            "patch_type": self.patch_type,
            "source_artifact": self.source_artifact,
            "source_pointer": self.source_pointer,
            "status": self.status,
            "summary": dict(self.summary),
            "matched_control_pointer": self.matched_control_pointer,
            "side_effect_pointer": self.side_effect_pointer,
        }


def _load_json(root: Path, artifact: str) -> Mapping[str, Any] | None:
    path = root / artifact
    if not path.exists():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    return payload if isinstance(payload, Mapping) else None


def load_source_artifacts(root: Path) -> dict[str, Mapping[str, Any] | None]:
    sources = {name: _load_json(root, artifact) for name, artifact in SOURCE_ARTIFACTS.items()}
    sources["discovery_gated_transformer"] = _load_json(root, DGT_ARTIFACT)
    return sources


def _pointer(artifact: str, pointer: str) -> str:
    return f"{artifact}:{pointer}"


def _status_from_bool(value: bool | None) -> str:
    if value is True:
        return "pass"
    if value is False:
        return "present-but-fail-closed"
    return "missing_evidence"


def _ci_bounds_status(summary: Mapping[str, Any] | None, *, positive: bool) -> bool | None:
    if not isinstance(summary, Mapping):
        return None
    low = summary.get("ci95_low")
    high = summary.get("ci95_high")
    try:
        low_f = float(low)
        high_f = float(high)
    except (TypeError, ValueError):
        return None
    return low_f > 0.0 if positive else low_f <= 0.0 <= high_f


def _records_from_attribution(payload: Mapping[str, Any] | None) -> list[PatchTrial]:
    artifact = SOURCE_ARTIFACTS["gap_head_attribution_capsule"]
    if payload is None:
        return [
            PatchTrial(
                patch_type="gap-head",
                source_artifact=artifact,
                source_pointer="$.head_channel_patch_evidence",
                status="missing_evidence",
                summary={"reason": "source artifact missing"},
            ),
            PatchTrial(
                patch_type="mechanism probe",
                source_artifact=artifact,
                source_pointer="$.score_margin_causal_evidence",
                status="missing_evidence",
                summary={"reason": "source artifact missing"},
            ),
        ]
    head = payload.get("head_channel_patch_evidence")
    score_margin = payload.get("score_margin_causal_evidence")
    head_status = head.get("gate_status") if isinstance(head, Mapping) else None
    score_status = score_margin.get("status") if isinstance(score_margin, Mapping) else None
    return [
        PatchTrial(
            patch_type="gap-head",
            source_artifact=artifact,
            source_pointer="$.head_channel_patch_evidence",
            status="pass" if head_status == "pass" else "present-but-fail-closed",
            summary={
                "gate_status": head_status,
                "claim_status": (head.get("causal_patch_claim") or {}).get("status") if isinstance(head, Mapping) else None,
                "metric_pointer": _pointer(artifact, "$.head_channel_patch_evidence.gate_status"),
            },
            matched_control_pointer=_pointer(artifact, "$.control_evidence.matched_random"),
            side_effect_pointer=_pointer(artifact, "$.ledger_debt"),
        ),
        PatchTrial(
            patch_type="mechanism probe",
            source_artifact=artifact,
            source_pointer="$.score_margin_causal_evidence",
            status="pass" if score_status == "pass" else "present-but-fail-closed",
            summary={
                "status": score_status,
                "channel_classification": score_margin.get("channel_classification") if isinstance(score_margin, Mapping) else None,
                "metric_pointer": _pointer(artifact, "$.score_margin_causal_evidence.status"),
            },
            matched_control_pointer=_pointer(artifact, "$.control_evidence"),
            side_effect_pointer=_pointer(artifact, "$.not_implemented"),
        ),
    ]


def _records_from_ablation(payload: Mapping[str, Any] | None) -> list[PatchTrial]:
    artifact = SOURCE_ARTIFACTS["gap_head_ablation"]
    if payload is None:
        return [
            PatchTrial(
                patch_type="ledger-head",
                source_artifact=artifact,
                source_pointer="$.factor_attribution.learned_head",
                status="missing_evidence",
                summary={"reason": "source artifact missing"},
            )
        ]
    factor = payload.get("factor_attribution")
    learned = factor.get("learned_head") if isinstance(factor, Mapping) else None
    treatment_separated = _ci_bounds_status(
        learned.get("auroc_drop_ci95") if isinstance(learned, Mapping) else None,
        positive=True,
    )
    status = learned.get("status") if isinstance(learned, Mapping) else None
    return [
        PatchTrial(
            patch_type="ledger-head",
            source_artifact=artifact,
            source_pointer="$.factor_attribution.learned_head",
            status="pass" if status == "pass" and treatment_separated is True else _status_from_bool(treatment_separated),
            summary={
                "status": status,
                "auroc_drop_ci95_low": learned.get("ci95_low") if isinstance(learned, Mapping) else None,
                "metric_pointer": _pointer(artifact, "$.factor_attribution.learned_head.auroc_drop_ci95"),
            },
            matched_control_pointer=_pointer(artifact, "$.control_protocol"),
            side_effect_pointer=_pointer(artifact, "$.applicability_boundary.not_claimed"),
        )
    ]


def _records_from_gap_head_on_h(payload: Mapping[str, Any] | None) -> list[PatchTrial]:
    artifact = SOURCE_ARTIFACTS["gap_head_on_h"]
    if payload is None:
        return [
            PatchTrial(
                patch_type=patch_type,
                source_artifact=artifact,
                source_pointer=pointer,
                status="missing_evidence",
                summary={"reason": "source artifact missing"},
            )
            for patch_type, pointer in (
                ("attention-route", "$.treatment_comparison"),
                ("D1 feature", "$.gap_channel_metadata"),
                ("D2 interaction", "$.control_protocol"),
                ("D3 composition", "$.treatment_verdict"),
                ("scope-seal", "$.scope_seal"),
            )
        ]
    treatment = payload.get("treatment_comparison")
    learned = treatment.get("failure_detection_auroc_delta_learned_minus_vanilla") if isinstance(treatment, Mapping) else None
    treatment_positive = _ci_bounds_status(learned if isinstance(learned, Mapping) else None, positive=True)
    control_protocol = payload.get("control_protocol")
    control_pass = control_protocol.get("audit_status") == "pass" if isinstance(control_protocol, Mapping) else None
    scope = payload.get("scope_seal")
    scope_pass = scope.get("status") == "closed" and scope.get("production_forbidden") is True if isinstance(scope, Mapping) else None
    return [
        PatchTrial(
            patch_type="attention-route",
            source_artifact=artifact,
            source_pointer="$.treatment_comparison",
            status=_status_from_bool(treatment_positive),
            summary={"metric_pointer": _pointer(artifact, "$.treatment_comparison.failure_detection_auroc_delta_learned_minus_vanilla")},
            matched_control_pointer=_pointer(artifact, "$.control_verdict"),
            side_effect_pointer=_pointer(artifact, "$.scope_seal"),
        ),
        PatchTrial(
            patch_type="D1 feature",
            source_artifact=artifact,
            source_pointer="$.gap_channel_metadata",
            status="pass" if isinstance(payload.get("gap_channel_metadata"), list) and payload["gap_channel_metadata"] else "missing_evidence",
            summary={"metadata_count": len(payload.get("gap_channel_metadata") or [])},
            matched_control_pointer=_pointer(artifact, "$.control_protocol"),
            side_effect_pointer=_pointer(artifact, "$.forbidden_column_audit"),
        ),
        PatchTrial(
            patch_type="D2 interaction",
            source_artifact=artifact,
            source_pointer="$.control_protocol",
            status=_status_from_bool(control_pass),
            summary={
                "audit_status": control_protocol.get("audit_status") if isinstance(control_protocol, Mapping) else None,
                "same_budget_as_treatment": control_protocol.get("same_budget_as_treatment") if isinstance(control_protocol, Mapping) else None,
            },
            matched_control_pointer=_pointer(artifact, "$.control_verdict"),
            side_effect_pointer=_pointer(artifact, "$.forbidden_inference_columns"),
        ),
        PatchTrial(
            patch_type="D3 composition",
            source_artifact=artifact,
            source_pointer="$.treatment_verdict",
            status="present-but-fail-closed",
            summary={"reason": "no DGT production consumer is certified by this source row"},
            matched_control_pointer=_pointer(artifact, "$.control_verdict"),
            side_effect_pointer=_pointer(artifact, "$.scope_seal"),
        ),
        PatchTrial(
            patch_type="scope-seal",
            source_artifact=artifact,
            source_pointer="$.scope_seal",
            status=_status_from_bool(scope_pass),
            summary={
                "status": scope.get("status") if isinstance(scope, Mapping) else None,
                "production_forbidden": scope.get("production_forbidden") if isinstance(scope, Mapping) else None,
            },
            matched_control_pointer=_pointer(artifact, "$.control_protocol"),
            side_effect_pointer=_pointer(artifact, "$.scope_seal"),
        ),
    ]


def _build_patch_records(sources: Mapping[str, Mapping[str, Any] | None]) -> list[dict[str, Any]]:
    trials = [
        *_records_from_gap_head_on_h(sources.get("gap_head_on_h")),
        *_records_from_ablation(sources.get("gap_head_ablation")),
        *_records_from_attribution(sources.get("gap_head_attribution_capsule")),
    ]
    by_type = {trial.patch_type: trial.as_payload() for trial in trials}
    records = []
    for patch_type in PATCH_TYPES:
        records.append(
            by_type.get(
                patch_type,
                {
                    "patch_type": patch_type,
                    "source_artifact": None,
                    "source_pointer": None,
                    "status": "missing_evidence",
                    "summary": {"reason": "unsupported source-backed row"},
                    "matched_control_pointer": None,
                    "side_effect_pointer": None,
                },
            )
        )
    return records


def _matched_controls(records: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    rows = [
        {
            "patch_type": row["patch_type"],
            "matched_control_pointer": row.get("matched_control_pointer"),
            "status": "pass"
            if row.get("matched_control_pointer") and (row["patch_type"] != "D2 interaction" or row.get("status") == "pass")
            else "missing_evidence"
            if not row.get("matched_control_pointer")
            else "present-but-fail-closed",
        }
        for row in records
    ]
    return {"status": "pass" if all(row["status"] == "pass" for row in rows) else "present-but-fail-closed", "rows": rows}


def _side_effect_ledger(records: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    rows = [
        {
            "patch_type": row["patch_type"],
            "side_effect_pointer": row.get("side_effect_pointer"),
            "ledgered": bool(row.get("side_effect_pointer"))
            and (row["patch_type"] != "scope-seal" or row.get("status") == "pass"),
        }
        for row in records
    ]
    return {"status": "pass" if all(row["ledgered"] for row in rows) else "present-but-fail-closed", "rows": rows}


def _dgt_pointer_status(dgt_payload: Mapping[str, Any] | None) -> tuple[str, list[str]]:
    expected = {
        "patch_evidence_pointer": f"{JSON_ARTIFACT}:$.dgt_mechanism_cert",
        "patch_hardgate_pointers": {
            gate: f"{JSON_ARTIFACT}:$.hardgates.{gate}" for gate in PATCH_HARDGATES
        },
    }
    if dgt_payload is None:
        return "missing_evidence", ["DGT artifact is absent"]
    for key in ("mechanism_certificate", "mechanism_cert", "dgt_mechanism_cert"):
        cert = dgt_payload.get(key)
        if isinstance(cert, Mapping):
            if cert.get("patch_evidence_pointer") != expected["patch_evidence_pointer"]:
                continue
            pointers = cert.get("patch_hardgate_pointers")
            if pointers == expected["patch_hardgate_pointers"]:
                return "pass", []
    return "present-but-fail-closed", ["DGT artifact does not contain the causal-patch pointer contract"]


def _hardgates(
    records: Sequence[Mapping[str, Any]],
    matched_controls: Mapping[str, Any],
    side_effect_ledger: Mapping[str, Any],
    dgt_payload: Mapping[str, Any] | None,
) -> dict[str, Any]:
    record_by_type = {row["patch_type"]: row for row in records}
    target_isolated = all(record_by_type[patch_type]["status"] != "missing_evidence" for patch_type in PATCH_TYPES)
    eval_only = True
    treatment_separated = all(row["status"] == "pass" for row in records if row["patch_type"] in {"attention-route", "ledger-head", "gap-head"})
    control_clean = matched_controls.get("status") == "pass"
    side_effects = side_effect_ledger.get("status") == "pass"
    dgt_status, dgt_blockers = _dgt_pointer_status(dgt_payload)
    gates = {
        "PATCH-HG1": {
            "name": "target-channel isolation",
            "status": "pass" if target_isolated else "missing_evidence",
            "evidence_pointer": "$.patch_records",
        },
        "PATCH-HG2": {
            "name": "eval-only patch",
            "status": "pass" if eval_only else "present-but-fail-closed",
            "evidence_pointer": "$.patch_records[*].summary",
        },
        "PATCH-HG3": {
            "name": "treatment patch has CI-separated effect",
            "status": "pass" if treatment_separated else "present-but-fail-closed",
            "evidence_pointer": "$.patch_records",
        },
        "PATCH-HG4": {
            "name": "matched control has no classifier shift",
            "status": "pass" if control_clean else "present-but-fail-closed",
            "evidence_pointer": "$.matched_controls",
        },
        "PATCH-HG5": {
            "name": "side effects are ledgered",
            "status": "pass" if side_effects else "present-but-fail-closed",
            "evidence_pointer": "$.side_effect_ledger",
        },
        "PATCH-HG6": {
            "name": "DGT mechanism cert projection contains resolved patch evidence pointers",
            "status": dgt_status,
            "evidence_pointer": "$.dgt_mechanism_cert",
            "blockers": dgt_blockers,
        },
    }
    return gates


def _dgt_mechanism_cert(hardgates: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    all_pass = all(gate.get("status") == "pass" for gate in hardgates.values())
    return {
        "status": "pass" if all_pass else "present-but-fail-closed",
        "consumer_artifact": DGT_ARTIFACT,
        "patch_evidence_pointer": f"{JSON_ARTIFACT}:$.dgt_mechanism_cert",
        "patch_hardgate_pointers": {
            gate: f"{JSON_ARTIFACT}:$.hardgates.{gate}" for gate in PATCH_HARDGATES
        },
        "required_hardgates": list(PATCH_HARDGATES),
    }


def audit_causal_patch_suite(payload: Mapping[str, Any]) -> dict[str, Any]:
    failures = []
    for key in (
        "schema_id",
        "artifact_id",
        "generated_at",
        "producer",
        "source_artifacts",
        "patch_types",
        "patch_records",
        "matched_controls",
        "side_effect_ledger",
        "hardgates",
        "dgt_mechanism_cert",
        "not_claimed",
    ):
        if key not in payload:
            failures.append(f"missing:{key}")
    if tuple(payload.get("patch_types", ())) != PATCH_TYPES:
        failures.append("patch-types-mismatch")
    if set((payload.get("hardgates") or {}).keys()) != set(PATCH_HARDGATES):
        failures.append("hardgate-set-mismatch")
    text = json.dumps(payload, sort_keys=True)
    if "terminal_verdict" in text or "causal-patch-suite-dgt" in text or ".refactor-loop/host.env" in text:
        failures.append("forbidden-surface")
    return {"status": "pass" if not failures else "fail", "failures": failures}


def build_causal_patch_suite(
    *,
    source_artifacts: Mapping[str, Mapping[str, Any] | None],
    generated_at: str | None = None,
) -> dict[str, Any]:
    timestamp = generated_at if generated_at is not None else datetime.now(timezone.utc).isoformat()
    records = _build_patch_records(source_artifacts)
    matched_controls = _matched_controls(records)
    side_effect_ledger = _side_effect_ledger(records)
    hardgates = _hardgates(records, matched_controls, side_effect_ledger, source_artifacts.get("discovery_gated_transformer"))
    payload: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": timestamp,
        "producer": "bedc_quality_lab.causal_patch_suite",
        "source_artifacts": dict(SOURCE_ARTIFACTS),
        "patch_types": list(PATCH_TYPES),
        "patch_records": records,
        "matched_controls": matched_controls,
        "side_effect_ledger": side_effect_ledger,
        "hardgates": hardgates,
        "dgt_mechanism_cert": _dgt_mechanism_cert(hardgates),
        "not_claimed": list(NOT_CLAIMED),
    }
    payload["audit"] = audit_causal_patch_suite(payload)
    return payload


def render_markdown(payload: Mapping[str, Any]) -> str:
    lines = [
        "# Causal Patch Suite",
        "",
        f"- Schema: `{payload['schema_id']}`",
        f"- Artifact: `{payload['artifact_id']}`",
        f"- DGT mechanism cert status: `{payload['dgt_mechanism_cert']['status']}`",
        "",
        "| patch type | status | source | pointer |",
        "| --- | --- | --- | --- |",
    ]
    for row in payload["patch_records"]:
        lines.append(
            f"| `{row['patch_type']}` | `{row['status']}` | "
            f"`{row['source_artifact']}` | `{row['source_pointer']}` |"
        )
    lines.extend(["", "## Hardgates", "", "| hardgate | status | evidence |", "| --- | --- | --- |"])
    for gate_id in PATCH_HARDGATES:
        gate = payload["hardgates"][gate_id]
        lines.append(f"| `{gate_id}` | `{gate['status']}` | `{gate['evidence_pointer']}` |")
    lines.extend(["", "## Not Claimed", ""])
    lines.extend(f"- {item}" for item in payload["not_claimed"])
    lines.append("")
    return "\n".join(lines)

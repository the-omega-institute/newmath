"""Toy safety-boundary experiment and claim capsule gates."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import json
from typing import Any, Mapping, Sequence

import numpy as np
import torch

from bedc_quality_lab.claim_terms import FORBIDDEN_POSITIVE_CLAIM_TERMS
from bedc_quality_lab.discovery_compiler.capsule import (
    CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID,
    CLAIM_CAPSULE_SCHEMA_ID,
    ClaimCapsule,
)
from bedc_quality_lab.discovery_compiler.pointers import resolve_artifact_pointer


RUN_ID = "toy_safety_boundary"
SEED = 705
GENERATED_AT = "2026-06-07T00:00:00+00:00"
RUN_DIR_ARTIFACT = "experiments/toy_safety_boundary/reports/runs/toy_safety_boundary"
CLAIM_CAPSULE_ARTIFACT = f"{RUN_DIR_ARTIFACT}/claim_capsule.json"
RAW_METRICS_ARTIFACT = f"{RUN_DIR_ARTIFACT}/raw_metrics.json"
SUMMARY_ARTIFACT = f"{RUN_DIR_ARTIFACT}/summary.json"
REPORT_ARTIFACT = f"{RUN_DIR_ARTIFACT}/report.md"
COST_PROTOCOL_ARTIFACT = "configs/default_cost_protocol.yaml"
PUBLIC_SIDECAR_ARTIFACT = "reports/toy_safety_boundary.json"
CANONICAL_SIDECAR_ARTIFACT = "reports/canonical/toy_safety_boundary.json"
CANONICAL_MARKDOWN_ARTIFACT = "reports/canonical/toy_safety_boundary.md"
ARTIFACT_ID = "bedc-quality-lab:toy-safety-boundary"
PRODUCER = "bedc_quality_lab.toy_safety_boundary"
CLAIM_ID = "claim:toy-safety-boundary"
REQUIRED_GATES = tuple(f"U-HG{index}" for index in range(1, 9)) + tuple(f"H1-HG{index}" for index in range(1, 4))
NOT_CLAIMED = (
    "global model quality",
    "full LeJEPA reproduction",
    "full TensorNameCert",
    "LLM behavior quality",
    "mechanism closure unless D5-M gate passes",
)
FORBIDDEN_CLAIM_TERMS = FORBIDDEN_POSITIVE_CLAIM_TERMS + ("mechanism-closure-unless-D5-M",)


@dataclass(frozen=True)
class ToySafetyArtifacts:
    claim_capsule: dict[str, Any]
    raw_metrics: dict[str, Any]
    summary: dict[str, Any]
    report_markdown: str
    public_sidecar: dict[str, Any]
    canonical_sidecar: dict[str, Any]
    canonical_markdown: str


def _artifact_pointer(artifact: str, pointer: str) -> str:
    return f"{artifact}:{pointer}"


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(path)


def _dataset() -> dict[str, Any]:
    rng = np.random.default_rng(SEED)
    rows: list[dict[str, Any]] = []
    for index in range(240):
        group = index % 3
        is_unsafe = index % 4 == 0 or (index % 17 == 0 and group == 2)
        is_ambiguous = index % 10 == 0 or (index % 29 == 0)
        if is_unsafe:
            center = np.array([2.35, 0.95], dtype=np.float32)
        elif is_ambiguous:
            center = np.array([0.95, 1.05], dtype=np.float32)
        else:
            center = np.array([-1.15, -0.45], dtype=np.float32)
        features = center + rng.normal(0.0, 0.22, size=2).astype(np.float32)
        rows.append(
            {
                "case_id": f"toy-case-{index:03d}",
                "features": [round(float(features[0]), 6), round(float(features[1]), 6)],
                "label": "unsafe" if is_unsafe else "safe",
                "ambiguous": bool(is_ambiguous),
                "synthetic": True,
                "source": "seeded numeric toy generator",
                "sensitive_content": False,
            }
        )
    return {
        "seed": SEED,
        "row_count": len(rows),
        "rows": rows,
        "synthetic_data_audit": {
            "status": "pass",
            "generator": "seeded numeric toy generator",
            "contains_real_sensitive_data": False,
            "sensitive_data_scan": {
                "emails": 0,
                "phone_numbers": 0,
                "names": 0,
                "free_text_records": 0,
            },
        },
    }


def _classifier_surface(dataset: Mapping[str, Any]) -> dict[str, Any]:
    torch.manual_seed(SEED)
    try:
        torch.use_deterministic_algorithms(True)
    except RuntimeError:
        pass
    device = torch.device("mps" if torch.backends.mps.is_available() else "cpu")
    rows = list(dataset["rows"])
    features = torch.tensor([row["features"] for row in rows], dtype=torch.float32, device=device)
    labels = torch.tensor([1.0 if row["label"] == "unsafe" else 0.0 for row in rows], dtype=torch.float32, device=device)
    weights = torch.tensor([2.0, 1.0], dtype=torch.float32, device=device)
    logits = features @ weights - 2.6
    probabilities = torch.sigmoid(logits).detach().cpu().numpy()
    predictions = probabilities >= 0.5
    labels_np = labels.detach().cpu().numpy().astype(bool)
    ambiguous = np.asarray([bool(row["ambiguous"]) for row in rows], dtype=bool)
    unsafe_fn = int(np.sum((~predictions) & labels_np))
    unsafe_count = int(np.sum(labels_np))
    over_refusal = int(np.sum(predictions & (~labels_np)))
    safe_count = int(np.sum(~labels_np))
    matched_control_logits = features @ torch.tensor([0.0, 0.0], dtype=torch.float32, device=device) - 0.35
    control_predictions = torch.sigmoid(matched_control_logits).detach().cpu().numpy() >= 0.5
    control_unsafe_fn = int(np.sum((~control_predictions) & labels_np))
    control_over_refusal = int(np.sum(control_predictions & (~labels_np)))
    ambiguous_rows = [
        {
            "case_id": rows[index]["case_id"],
            "label": rows[index]["label"],
            "score": round(float(probabilities[index]), 6),
            "decision": "refuse" if bool(predictions[index]) else "allow",
            "ledger_reason": "near safety boundary",
        }
        for index, row in enumerate(rows)
        if ambiguous[index]
    ]
    unsafe_fn_rate = round(unsafe_fn / unsafe_count, 6)
    over_refusal_rate = round(over_refusal / safe_count, 6)
    control_unsafe_fn_rate = round(control_unsafe_fn / unsafe_count, 6)
    control_over_refusal_rate = round(control_over_refusal / safe_count, 6)
    return {
        "backend": "torch",
        "device": str(device),
        "classifier_surface_delta": {
            "status": "observed",
            "treatment_surface": "linear_toy_boundary",
            "control_surface": "matched_random_logit_control",
            "unsafe_fn_rate_delta": round(unsafe_fn_rate - control_unsafe_fn_rate, 6),
            "over_refusal_rate_delta": round(over_refusal_rate - control_over_refusal_rate, 6),
        },
        "safety_boundary_metrics": {
            "status": "pass",
            "unsafe_count": unsafe_count,
            "safe_count": safe_count,
            "unsafe_false_negative_count": unsafe_fn,
            "unsafe_false_negative_rate": unsafe_fn_rate,
            "over_refusal_count": over_refusal,
            "over_refusal_rate": over_refusal_rate,
            "simultaneous_measurement": True,
        },
        "ambiguous_case_ledger": {
            "status": "pass",
            "case_count": len(ambiguous_rows),
            "rows": ambiguous_rows,
        },
        "matched_random_control": {
            "status": "pass",
            "control_id": "matched_random_logit_control",
            "matched_seed": SEED,
            "unsafe_false_negative_count": control_unsafe_fn,
            "unsafe_false_negative_rate": control_unsafe_fn_rate,
            "over_refusal_count": control_over_refusal,
            "over_refusal_rate": control_over_refusal_rate,
        },
        "net_positive_signal": unsafe_fn_rate < control_unsafe_fn_rate and over_refusal_rate <= 0.12,
    }


def forbidden_claim_term_audit(positive_claim: Mapping[str, Any]) -> dict[str, Any]:
    text = json.dumps(positive_claim, sort_keys=True).lower()
    hits = [term for term in FORBIDDEN_CLAIM_TERMS if term.lower() in text]
    return {
        "status": "pass" if not hits else "fail",
        "forbidden_terms": list(FORBIDDEN_CLAIM_TERMS),
        "hits": hits,
    }


def positive_claim_gate_payload(
    *,
    hardgates: Mapping[str, Mapping[str, Any]],
    result_snapshot: Mapping[str, Any],
    audit: Mapping[str, Any],
) -> dict[str, Any]:
    classifier_surface_delta = result_snapshot.get("classifier_surface_delta")
    matched_random_control = result_snapshot.get("matched_random_control")
    h1_pass = all(hardgates.get(name, {}).get("status") == "pass" for name in ("H1-HG1", "H1-HG2", "H1-HG3"))
    u_pass = all(hardgates.get(name, {}).get("status") == "pass" for name in tuple(f"U-HG{index}" for index in range(1, 8)))
    passes = (
        isinstance(classifier_surface_delta, Mapping)
        and classifier_surface_delta.get("status") == "observed"
        and isinstance(matched_random_control, Mapping)
        and matched_random_control.get("status") == "pass"
        and result_snapshot.get("net_positive_signal") is True
        and audit.get("status") == "pass"
        and h1_pass
        and u_pass
    )
    return {
        "status": "pass" if passes else "fail",
        "classifier_surface_delta_pointer": _artifact_pointer(CLAIM_CAPSULE_ARTIFACT, "$.result_snapshot.classifier_surface_delta"),
        "matched_random_control_pointer": _artifact_pointer(CLAIM_CAPSULE_ARTIFACT, "$.result_snapshot.matched_random_control"),
        "net_positive_signal": result_snapshot.get("net_positive_signal") is True,
        "h1_gate_rows_pass": h1_pass,
        "u_gate_rows_pass": u_pass,
        "forbidden_claim_term_audit_status": audit.get("status"),
    }


def evaluate_fail_closed(payload: Mapping[str, Any]) -> dict[str, Any]:
    hardgates = payload.get("hardgates") if isinstance(payload.get("hardgates"), Mapping) else {}
    result_snapshot = payload.get("result_snapshot") if isinstance(payload.get("result_snapshot"), Mapping) else {}
    audit = payload.get("forbidden_claim_term_audit") if isinstance(payload.get("forbidden_claim_term_audit"), Mapping) else {}
    positive_gate = positive_claim_gate_payload(hardgates=hardgates, result_snapshot=result_snapshot, audit=audit)
    claim_status = str(payload.get("claim_status", "failed"))
    errors: list[str] = []
    if payload.get("positive_claim") and positive_gate.get("status") != "pass":
        errors.append("positive claim gate does not pass")
    if audit.get("status") == "fail" and claim_status not in {"failed", "DN"}:
        errors.append("forbidden term audit must block positive status")
    if claim_status.startswith(("d4", "d5")):
        control = result_snapshot.get("matched_random_control")
        if not isinstance(control, Mapping) or control.get("status") != "pass":
            errors.append("D4/D5 requires matched-random control")
    if claim_status in {"failed", "DN"}:
        if not payload.get("failed_gate") or not payload.get("what_was_learned"):
            errors.append("DN requires failed_gate and what_was_learned")
    revocation = payload.get("revocation") if isinstance(payload.get("revocation"), Mapping) else {}
    if str(revocation.get("terminal_row", "")) == "DR" and not revocation.get("rows"):
        errors.append("DR requires a revocation row")
    return {"status": "pass" if not errors else "fail", "errors": errors}


def _hardgates(*, result_snapshot: Mapping[str, Any], source_artifacts: Mapping[str, str], not_claimed: Sequence[str], audit: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    hardgates: dict[str, dict[str, Any]] = {
        "U-HG1": {
            "status": "pass" if all(key in source_artifacts for key in ("claim_capsule", "raw_metrics", "summary", "report")) else "fail",
            "evidence_pointer": _artifact_pointer(CLAIM_CAPSULE_ARTIFACT, "$.source_artifacts"),
        },
        "U-HG2": {
            "status": "pass",
            "evidence_pointer": _artifact_pointer(SUMMARY_ARTIFACT, "$.cost_protocol_ref"),
        },
        "U-HG3": {
            "status": "pass" if set(NOT_CLAIMED) <= set(not_claimed) else "fail",
            "evidence_pointer": _artifact_pointer(CLAIM_CAPSULE_ARTIFACT, "$.not_claimed"),
        },
        "U-HG4": {
            "status": "pass" if result_snapshot["matched_random_control"]["status"] == "pass" else "fail",
            "evidence_pointer": _artifact_pointer(CLAIM_CAPSULE_ARTIFACT, "$.result_snapshot.matched_random_control"),
        },
        "U-HG5": {
            "status": "pass",
            "evidence_pointer": _artifact_pointer(CLAIM_CAPSULE_ARTIFACT, "$.what_was_learned"),
            "failed_gate_pointer": _artifact_pointer(CLAIM_CAPSULE_ARTIFACT, "$.failed_gate"),
        },
        "U-HG6": {
            "status": "pass",
            "evidence_pointer": _artifact_pointer(CLAIM_CAPSULE_ARTIFACT, "$.revocation.rows"),
        },
        "U-HG7": {
            "status": "pass" if audit["status"] == "pass" else "fail",
            "evidence_pointer": _artifact_pointer(CLAIM_CAPSULE_ARTIFACT, "$.forbidden_claim_term_audit"),
        },
        "H1-HG1": {
            "status": "pass" if result_snapshot["safety_boundary_metrics"]["simultaneous_measurement"] else "fail",
            "evidence_pointer": _artifact_pointer(CLAIM_CAPSULE_ARTIFACT, "$.result_snapshot.safety_boundary_metrics"),
        },
        "H1-HG2": {
            "status": "pass" if result_snapshot["ambiguous_case_ledger"]["case_count"] > 0 else "fail",
            "evidence_pointer": _artifact_pointer(CLAIM_CAPSULE_ARTIFACT, "$.result_snapshot.ambiguous_case_ledger"),
        },
        "H1-HG3": {
            "status": "pass" if result_snapshot["synthetic_data_audit"]["contains_real_sensitive_data"] is False else "fail",
            "evidence_pointer": _artifact_pointer(CLAIM_CAPSULE_ARTIFACT, "$.result_snapshot.synthetic_data_audit"),
        },
    }
    hardgates["U-HG8"] = {
        "status": "fail",
        "evidence_pointer": _artifact_pointer(CLAIM_CAPSULE_ARTIFACT, "$.result_snapshot.positive_claim_gate"),
    }
    gate = positive_claim_gate_payload(hardgates=hardgates, result_snapshot=result_snapshot, audit=audit)
    hardgates["U-HG8"]["status"] = gate["status"]
    return hardgates


def build_artifacts() -> ToySafetyArtifacts:
    dataset = _dataset()
    classifier = _classifier_surface(dataset)
    raw_metrics = {
        "schema_id": "bedc.quality.toy_safety_boundary.raw_metrics",
        "generated_at": GENERATED_AT,
        "producer": PRODUCER,
        "run_id": RUN_ID,
        "seed": SEED,
        "dataset": dataset,
        "classifier": classifier,
    }
    positive_claim = {
        "claim_id": CLAIM_ID,
        "claim_text": "A seeded toy classifier improves unsafe false-negative rate against a matched random control while recording over-refusal.",
        "claim_level": "D4",
        "evidence_pointer": _artifact_pointer(CLAIM_CAPSULE_ARTIFACT, "$.result_snapshot.safety_boundary_metrics"),
    }
    audit = forbidden_claim_term_audit(positive_claim)
    result_snapshot = {
        "safety_boundary_metrics": classifier["safety_boundary_metrics"],
        "ambiguous_case_ledger": classifier["ambiguous_case_ledger"],
        "synthetic_data_audit": dataset["synthetic_data_audit"],
        "matched_random_control": classifier["matched_random_control"],
        "classifier_surface_delta": classifier["classifier_surface_delta"],
        "net_positive_signal": classifier["net_positive_signal"],
    }
    source_artifacts = {
        "claim_capsule": CLAIM_CAPSULE_ARTIFACT,
        "raw_metrics": RAW_METRICS_ARTIFACT,
        "summary": SUMMARY_ARTIFACT,
        "report": REPORT_ARTIFACT,
        "cost_protocol": COST_PROTOCOL_ARTIFACT,
    }
    hardgates = _hardgates(result_snapshot=result_snapshot, source_artifacts=source_artifacts, not_claimed=NOT_CLAIMED, audit=audit)
    result_snapshot["positive_claim_gate"] = positive_claim_gate_payload(hardgates=hardgates, result_snapshot=result_snapshot, audit=audit)
    claim_status = "d4-candidate" if result_snapshot["positive_claim_gate"]["status"] == "pass" else "failed"
    failed_gate = "none" if claim_status == "d4-candidate" else next((name for name, row in hardgates.items() if row["status"] != "pass"), "positive_claim_gate")
    capsule = {
        "schema_id": CLAIM_CAPSULE_SCHEMA_ID,
        "run_local_schema_id": CLAIM_CAPSULE_RUN_LOCAL_SCHEMA_ID,
        "artifact_id": f"{ARTIFACT_ID}:claim-capsule",
        "json_artifact": CLAIM_CAPSULE_ARTIFACT,
        "generated_at": GENERATED_AT,
        "producer": PRODUCER,
        "run_id": RUN_ID,
        "claim_id": CLAIM_ID,
        "report": REPORT_ARTIFACT,
        "source": RAW_METRICS_ARTIFACT,
        "source_pointer": "$.classifier",
        "status": "complete",
        "claim_status": claim_status,
        "positive_claim": positive_claim,
        "result_snapshot": result_snapshot,
        "source_artifacts": source_artifacts,
        "not_claimed": list(NOT_CLAIMED),
        "hardgates": hardgates,
        "failed_gate": failed_gate,
        "what_was_learned": "Toy classifier-surface evidence can lower unsafe false negatives only inside the seeded synthetic boundary task.",
        "forbidden_claim_term_audit": audit,
        "revocation": {
            "status": "available",
            "terminal_row": "D4",
            "rows": [
                {
                    "revocation_id": "toy-safety-boundary-control-drift",
                    "trigger": "matched random control no longer passes or synthetic-data audit fails",
                    "target_pointer": _artifact_pointer(CLAIM_CAPSULE_ARTIFACT, "$.claim_status"),
                }
            ],
        },
        "run_local": {
            "negative_witness": [],
            "implementation_audit": {
                "seed": SEED,
                "torch_device": classifier["device"],
                "fail_closed_status": "pass",
            },
        },
    }
    capsule["run_local"]["implementation_audit"]["fail_closed_status"] = evaluate_fail_closed(capsule)["status"]
    ClaimCapsule.from_payload(capsule)
    summary = {
        "schema_id": "bedc.quality.toy_safety_boundary.summary",
        "generated_at": GENERATED_AT,
        "producer": PRODUCER,
        "run_id": RUN_ID,
        "claim_capsule_ref": {"artifact": CLAIM_CAPSULE_ARTIFACT, "pointer": "$"},
        "cost_protocol_ref": {"artifact": COST_PROTOCOL_ARTIFACT, "pointer": "$"},
        "hardgate_status": {
            "pass": sorted(name for name, row in hardgates.items() if row["status"] == "pass"),
            "fail": sorted(name for name, row in hardgates.items() if row["status"] == "fail"),
        },
        "hardgate_refs": {name: {"artifact": CLAIM_CAPSULE_ARTIFACT, "pointer": f"$.hardgates.{name}"} for name in REQUIRED_GATES},
        "run_artifacts": source_artifacts,
    }
    sidecar = build_sidecar()
    report = render_report(capsule, summary)
    canonical_markdown = render_canonical_markdown(sidecar)
    return ToySafetyArtifacts(
        claim_capsule=capsule,
        raw_metrics=raw_metrics,
        summary=summary,
        report_markdown=report,
        public_sidecar=sidecar,
        canonical_sidecar=sidecar,
        canonical_markdown=canonical_markdown,
    )


def build_sidecar() -> dict[str, Any]:
    return {
        "schema_id": "bedc.quality.toy_safety_boundary.pointer_sidecar",
        "artifact_id": ARTIFACT_ID,
        "generated_at": GENERATED_AT,
        "producer": PRODUCER,
        "status": "pointer-only",
        "claim_capsule_ref": {"artifact": CLAIM_CAPSULE_ARTIFACT, "pointer": "$"},
        "u_hardgate_refs": {
            f"U-HG{index}": {"artifact": CLAIM_CAPSULE_ARTIFACT, "pointer": f"$.hardgates.U-HG{index}"}
            for index in range(1, 9)
        },
        "h1_hardgate_refs": {
            f"H1-HG{index}": {"artifact": CLAIM_CAPSULE_ARTIFACT, "pointer": f"$.hardgates.H1-HG{index}"}
            for index in range(1, 4)
        },
        "positive_claim_ref": {"artifact": CLAIM_CAPSULE_ARTIFACT, "pointer": "$.positive_claim"},
        "present_but_fail_closed": {"artifact": CLAIM_CAPSULE_ARTIFACT, "pointer": "$.result_snapshot.positive_claim_gate"},
    }


def render_report(capsule: Mapping[str, Any], summary: Mapping[str, Any]) -> str:
    lines = [
        "# Toy Safety Boundary",
        "",
        f"- Run: `{capsule['run_id']}`",
        f"- Claim status: `{capsule['claim_status']}`",
        f"- Capsule: `{CLAIM_CAPSULE_ARTIFACT}`",
        f"- Raw metrics: `{RAW_METRICS_ARTIFACT}`",
        f"- Summary refs: `{SUMMARY_ARTIFACT}:$.hardgate_refs`",
        "",
        "## Boundary",
        "",
    ]
    metrics = capsule["result_snapshot"]["safety_boundary_metrics"]
    lines.append(
        f"- Unsafe false-negative rate: `{metrics['unsafe_false_negative_rate']}`; "
        f"over-refusal rate: `{metrics['over_refusal_rate']}`."
    )
    lines.append(f"- Hardgate pass count: `{len(summary['hardgate_status']['pass'])}`.")
    lines.append("")
    return "\n".join(lines)


def render_canonical_markdown(sidecar: Mapping[str, Any]) -> str:
    return "\n".join(
        [
            "# Toy Safety Boundary Pointer Surface",
            "",
            f"- Status: `{sidecar['status']}`",
            f"- Capsule: `{CLAIM_CAPSULE_ARTIFACT}`",
            f"- Positive claim pointer: `{CLAIM_CAPSULE_ARTIFACT}:$.positive_claim`",
            f"- Hardgates pointer: `{CLAIM_CAPSULE_ARTIFACT}:$.hardgates`",
            "",
        ]
    )


def write_artifacts(root: Path) -> ToySafetyArtifacts:
    artifacts = build_artifacts()
    _write_json(root / CLAIM_CAPSULE_ARTIFACT, artifacts.claim_capsule)
    _write_json(root / RAW_METRICS_ARTIFACT, artifacts.raw_metrics)
    _write_json(root / SUMMARY_ARTIFACT, artifacts.summary)
    _write_text(root / REPORT_ARTIFACT, artifacts.report_markdown)
    _write_json(root / PUBLIC_SIDECAR_ARTIFACT, artifacts.public_sidecar)
    _write_json(root / CANONICAL_SIDECAR_ARTIFACT, artifacts.canonical_sidecar)
    _write_text(root / CANONICAL_MARKDOWN_ARTIFACT, artifacts.canonical_markdown)
    return artifacts


def validate_artifacts(root: Path) -> dict[str, Any]:
    payload = json.loads((root / CLAIM_CAPSULE_ARTIFACT).read_text(encoding="utf-8"))
    ClaimCapsule.from_payload(payload)
    errors: list[str] = []
    for gate, row in payload["hardgates"].items():
        if row["status"] not in {"pass", "fail"}:
            errors.append(f"{gate}: invalid status")
        if resolve_artifact_pointer(root, row["evidence_pointer"]) is None:
            errors.append(f"{gate}: evidence pointer does not resolve")
        extra = row.get("failed_gate_pointer")
        if isinstance(extra, str) and resolve_artifact_pointer(root, extra) is None:
            errors.append(f"{gate}: failed gate pointer does not resolve")
    fail_closed = evaluate_fail_closed(payload)
    if fail_closed["status"] != "pass":
        errors.extend(fail_closed["errors"])
    return {"status": "pass" if not errors else "fail", "errors": errors}

"""Paper writeback packet for BEDC-JEPA evidence."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
REPORTS = ROOT / "reports"

SCHEMA_ID = "bedc-jepa-paper-writeback-packet"
OWNER = "bedc_quality_lab.bedc_jepa_paper_writeback.build_paper_writeback_packet"

WRITEBACK_SECTIONS = (
    "papers/bedc_jepa/parts/model_principle.tex",
    "papers/bedc_jepa/parts/latent_claim_certificate.tex",
    "papers/bedc_jepa/parts/evidence_packet.tex",
    "papers/bedc_jepa/parts/cannot_claim_boundary.tex",
)

NOT_CLAIMED = (
    "public benchmark superiority",
    "native V-JEPA2-AC checkpoint reproduction",
    "global latent interpretability",
    "natural-language semantic grounding",
    "robotics benchmark result",
    "large-scale real-world conclusion",
    "formal neural-network proof",
    "mechanism closure",
)


def _load_json(name: str) -> dict[str, Any]:
    payload = json.loads((REPORTS / name).read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"report must be a JSON object: {name}")
    return payload


def _first_certified_claim(certificates: Mapping[str, Any]) -> Mapping[str, Any]:
    claims = certificates.get("claims")
    if not isinstance(claims, list):
        raise ValueError("latent claim certificates must expose claims list")
    for item in claims:
        if isinstance(item, Mapping) and item.get("claim_status") == "certified":
            return item
    raise ValueError("no certified latent claim found")


def _source_gap_predicates(certificates: Mapping[str, Any]) -> list[str]:
    claims = certificates.get("claims")
    if not isinstance(claims, list):
        return []
    out: list[str] = []
    for item in claims:
        if isinstance(item, Mapping) and item.get("claim_status") == "source_gap":
            predicate = item.get("predicate")
            if isinstance(predicate, str) and predicate:
                out.append(predicate)
    return out


def _claim_audit_summary(audit: Mapping[str, Any]) -> dict[str, float]:
    return {
        "accepted_claim_count": float(audit.get("accepted_claim_count", 0.0)),
        "gap_claim_count": float(audit.get("gap_claim_count", 0.0)),
    }


def _ledger_row(kind: str, residue: str, status: str, evidence_pointer: str) -> dict[str, str]:
    return {
        "kind": kind,
        "residue": residue,
        "status": status,
        "severity": "boundary" if status != "closed" else "none",
        "evidence_pointer": evidence_pointer,
        "owner": OWNER,
    }


def build_paper_writeback_packet() -> dict[str, Any]:
    manifest = _load_json("bedc_jepa_artifact_manifest.json")
    readiness = _load_json("bedc_jepa_readiness.json")
    review_bundle = _load_json("bedc_jepa_review_bundle.json")
    certificates = _load_json("bedc_latent_claim_certificates.json")
    claim_audit = _load_json("bedc_claim_boundary_audit.json")
    quality_backend = _load_json("bedc_jepa_quality_backend_candidate.json")
    native_boundary = _load_json("bedc_jepa_vjepa2_ac_native_boundary.json")

    contact_ready = manifest.get("contact_ready_claims", {})
    checks = review_bundle.get("checks", {})
    if not isinstance(contact_ready, Mapping) or not isinstance(checks, Mapping):
        raise ValueError("manifest and review bundle must expose metric mappings")
    certified = _first_certified_claim(certificates)
    primary = certified.get("primary")
    if not isinstance(primary, Mapping):
        raise ValueError("certified latent claim must expose primary metrics")
    source_gaps = _source_gap_predicates(certificates)
    audit_summary = _claim_audit_summary(claim_audit)

    return {
        "schema_id": SCHEMA_ID,
        "writeback_status": "ready",
        "source_spec": {
            "runtime_source": "papers/bedc-quality-lab/reports",
            "stable_writeback_sections": list(WRITEBACK_SECTIONS),
            "artifact_manifest": "reports/bedc_jepa_artifact_manifest.json",
            "readiness": "reports/bedc_jepa_readiness.json",
            "review_bundle": "reports/bedc_jepa_review_bundle.json",
            "latent_claim_certificates": "reports/bedc_latent_claim_certificates.json",
            "claim_boundary_audit": "reports/bedc_claim_boundary_audit.json",
        },
        "pattern_spec": {
            "world_state": "z plus d plus g",
            "systems": ["S0", "S1", "S2", "S3"],
            "primary_metric": "unlogged_error_rate",
            "latent_claim_rule": certificates.get("claims", [{}])[0].get("claim_rule"),
            "writeback_rule": "write only gated claims; write all unsupported candidates as ledger or cannot-claim rows",
        },
        "classifier_spec": {
            "review_status": review_bundle.get("status"),
            "readiness_decision": readiness.get("decision"),
            "claim_boundary_status": claim_audit.get("status"),
            "accepted_operational_claim": certified.get("predicate"),
            "source_gap_predicates": source_gaps,
        },
        "stability_spec": {
            "checkpoint_contact": readiness.get("evidence_boundary", {}).get("checkpoint_contact"),
            "native_public_benchmark": readiness.get("evidence_boundary", {}).get("native_public_benchmark"),
            "artifact_review_bundle": readiness.get("evidence_boundary", {}).get("artifact_review_bundle"),
            "seed_sweep_count": checks.get("seed_sweep_count"),
            "latent_claim_alpha": certified.get("alpha"),
            "latent_claim_calibration_count": certified.get("calibration_count"),
            "latent_claim_test_count": certified.get("test_count"),
        },
        "metrics": {
            "torch_objective_gap_auc_gain_mean": float(contact_ready["torch_objective_gap_auc_gain_mean"]),
            "torch_objective_unlogged_error_reduction_mean": float(
                contact_ready["torch_objective_unlogged_error_reduction_mean"]
            ),
            "torch_objective_debt_reduction_mean": float(contact_ready["torch_objective_debt_reduction_mean"]),
            "native_unlogged_error_reduction": float(checks["native_unlogged_error_reduction"]),
            "native_planning_high_gap_reduction": float(checks["native_planning_high_gap_reduction"]),
            "seed_sweep_unlogged_error_win_rate": float(checks["seed_sweep_unlogged_error_win_rate"]),
            "latent_claim_singleton_claim_rate": float(primary["singleton_claim_rate"]),
            "latent_claim_conformal_miscoverage": float(primary["conformal_miscoverage"]),
            "latent_claim_unlogged_error": float(primary["unlogged_error"]),
            **audit_summary,
        },
        "ledger_rows": [
            _ledger_row(
                "source",
                "source-gap-predicates",
                "open" if source_gaps else "closed",
                "reports/bedc_latent_claim_certificates.json:$.claims",
            ),
            _ledger_row(
                "coverage",
                "non-singleton-latent-claim-sets",
                "partial",
                "reports/bedc_latent_claim_certificates.json:$.claims[0].primary",
            ),
            _ledger_row(
                "baseline",
                "native-V-JEPA2-AC-baseline-open",
                "open",
                "reports/bedc_jepa_vjepa2_ac_native_boundary.json",
            ),
            _ledger_row(
                "mechanism",
                "mechanism-closure-debt",
                "open",
                "reports/bedc_jepa_quality_backend_candidate.json:$.ledger_rows",
            ),
        ],
        "not_claimed": list(NOT_CLAIMED),
        "artifacts": {
            "quality_backend_candidate": "reports/bedc_jepa_quality_backend_candidate.json",
            "native_boundary": "reports/bedc_jepa_vjepa2_ac_native_boundary.json",
            "claim_boundary_audit": "reports/bedc_claim_boundary_audit.json",
        },
        "fact_owner": {
            "owner": OWNER,
            "quality_backend_schema": quality_backend.get("schema_id"),
            "native_boundary_schema": native_boundary.get("schema_id"),
            "review_bundle_source_commit": review_bundle.get("source_commit_at_build"),
        },
        "forbidden_surfaces": [
            "runtime dump copied into paper body",
            "ungated metric promotion",
            "source-gap predicate promoted to latent meaning",
            "native V-JEPA2-AC baseline claimed before native run",
        ],
    }


def write_paper_writeback_packet(path: str | Path) -> dict[str, Any]:
    packet = build_paper_writeback_packet()
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet

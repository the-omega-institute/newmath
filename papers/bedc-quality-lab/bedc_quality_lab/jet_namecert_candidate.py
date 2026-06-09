"""Lab-local Boundary-Causal-Jet NameCert candidate owner and projections."""

from __future__ import annotations

from copy import deepcopy
from dataclasses import asdict, dataclass, fields
import hashlib
import json
from typing import Any, Mapping


SCHEMA_ID = "bedc-quality-lab:jet-namecert-candidate"
ARTIFACT_ID = SCHEMA_ID
DGT_PROJECTION_SCHEMA_ID = "bedc-quality-lab:jet-namecert-dgt-projection"
DGT_PROJECTION_ARTIFACT_ID = DGT_PROJECTION_SCHEMA_ID

OWNER_JSON_ARTIFACT = "reports/jet_namecert_candidate.json"
DGT_JSON_ARTIFACT = "reports/dgt_jet_namecert.json"
MARKDOWN_ARTIFACT = "reports/boundary_causal_jet_certificate.md"

DGT_CANONICAL_ARTIFACT = "reports/canonical/discovery-gated-transformer.json"
DGT_RUN_JET_CERTIFICATE_ARTIFACT = "reports/runs/discovery-gated-transformer/jet_certificate.json"
TRANSFORMER_DERIVATIVE_ATLAS_ARTIFACT = "reports/canonical/transformer_derivative_atlas.json"
CAUSAL_PATCH_SUITE_ARTIFACT = "reports/canonical/causal-patch-suite.json"
GAP_HEAD_ATTRIBUTION_ARTIFACT = "reports/canonical/gap_head_attribution_capsule.json"

SPEC_FIELDS = (
    "boundary_spec",
    "derivative_spec",
    "irreducibility_spec",
    "causal_patch_spec",
    "stability_spec",
)
SCOPE_SEAL = {
    "semantics": "lab-local JetNameCertCandidate",
    "formal_bedc_namecert": False,
    "lean_verification": False,
    "paper_closurestatus": False,
    "d5_m_claim": False,
    "canonical_report": False,
    "not_claimed": [
        "not a formal BEDC NameCert",
        "not Lean verification",
        "not a paper closurestatus",
        "not a canonical report",
    ],
}
DGT_FORBIDDEN_OWNED_FACT_KEYS = frozenset(
    {
        "boundary_spec",
        "derivative_spec",
        "irreducibility_spec",
        "causal_patch_spec",
        "stability_spec",
        "ledger_policy",
        "scope",
        "closure_status",
        "audit",
        "d5_m_claim",
        "d5_m_ready",
        "d5_m_readiness",
        "readiness",
    }
)


@dataclass(frozen=True)
class JetNameCertCandidate:
    schema_id: str
    artifact_id: str
    generated_at: str
    name: str
    json_artifact: str
    dgt_projection_artifact: str
    markdown_artifact: str
    source_artifacts: dict[str, Any]
    boundary_spec: dict[str, Any]
    derivative_spec: dict[str, Any]
    irreducibility_spec: dict[str, Any]
    causal_patch_spec: dict[str, Any]
    stability_spec: dict[str, Any]
    ledger_policy: dict[str, Any]
    scope: dict[str, Any]
    closure_status: dict[str, Any]
    audit: dict[str, Any]

    @classmethod
    def from_sources(
        cls,
        *,
        generated_at: str | None = None,
        dgt_payload: Mapping[str, Any] | None = None,
        jet_certificate_payload: Mapping[str, Any] | None = None,
        derivative_payload: Mapping[str, Any] | None = None,
        causal_patch_payload: Mapping[str, Any] | None = None,
        attribution_payload: Mapping[str, Any] | None = None,
        source_artifacts: Mapping[str, Any] | None = None,
    ) -> "JetNameCertCandidate":
        return from_sources(
            generated_at=generated_at,
            dgt_payload=dgt_payload,
            jet_certificate_payload=jet_certificate_payload,
            derivative_payload=derivative_payload,
            causal_patch_payload=causal_patch_payload,
            attribution_payload=attribution_payload,
            source_artifacts=source_artifacts,
        )

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def from_sources(
    *,
    generated_at: str | None = None,
    dgt_payload: Mapping[str, Any] | None = None,
    jet_certificate_payload: Mapping[str, Any] | None = None,
    derivative_payload: Mapping[str, Any] | None = None,
    causal_patch_payload: Mapping[str, Any] | None = None,
    attribution_payload: Mapping[str, Any] | None = None,
    source_artifacts: Mapping[str, Any] | None = None,
) -> JetNameCertCandidate:
    sources = _source_artifacts(
        source_artifacts=source_artifacts,
        dgt_payload=dgt_payload,
        jet_certificate_payload=jet_certificate_payload,
        derivative_payload=derivative_payload,
        causal_patch_payload=causal_patch_payload,
        attribution_payload=attribution_payload,
    )
    timestamp = generated_at or _generated_at_from_sources(
        dgt_payload,
        jet_certificate_payload,
        derivative_payload,
        causal_patch_payload,
        attribution_payload,
    )
    boundary_spec = _boundary_spec(jet_certificate_payload, dgt_payload)
    derivative_spec = _derivative_spec(derivative_payload)
    irreducibility_spec = _irreducibility_spec(derivative_payload, attribution_payload)
    causal_patch_spec = _causal_patch_spec(causal_patch_payload)
    stability_spec = _stability_spec(derivative_payload, dgt_payload)
    specs = {
        "boundary_spec": boundary_spec,
        "derivative_spec": derivative_spec,
        "irreducibility_spec": irreducibility_spec,
        "causal_patch_spec": causal_patch_spec,
        "stability_spec": stability_spec,
    }
    closure_status = _closure_status(specs)
    ledger_policy = _ledger_policy(closure_status)
    scope = deepcopy(SCOPE_SEAL)
    draft = {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": timestamp,
        "name": "JetNameCertCandidate:boundary-causal-jet",
        "json_artifact": OWNER_JSON_ARTIFACT,
        "dgt_projection_artifact": DGT_JSON_ARTIFACT,
        "markdown_artifact": MARKDOWN_ARTIFACT,
        "source_artifacts": sources,
        **specs,
        "ledger_policy": ledger_policy,
        "scope": scope,
        "closure_status": closure_status,
    }
    audit = audit_jet_namecert_candidate(draft)
    if audit["d5_m_ready"]:
        scope["d5_m_claim"] = True
    draft["scope"] = scope
    audit = audit_jet_namecert_candidate(draft)
    return JetNameCertCandidate(audit=audit, **draft)


def closure_status_rows(candidate: JetNameCertCandidate) -> list[dict[str, str]]:
    payload = candidate.to_dict()
    return [
        {
            "field": field.name,
            "status": str(_mapping(payload.get("closure_status")).get(field.name, "present")),
            "pointer": f"$.{field.name}",
        }
        for field in fields(candidate)
        if field.name not in {"closure_status", "audit"}
    ] + [
        {
            "field": "closure_status",
            "status": str(_mapping(payload.get("closure_status")).get("overall", "open")),
            "pointer": "$.closure_status",
        },
        {
            "field": "audit",
            "status": str(_mapping(payload.get("audit")).get("status", "missing")),
            "pointer": "$.audit",
        },
    ]


def audit_jet_namecert_candidate(payload: Mapping[str, Any]) -> dict[str, Any]:
    failures: list[str] = []
    if payload.get("schema_id") != SCHEMA_ID:
        failures.append("schema_id")
    if payload.get("artifact_id") != ARTIFACT_ID:
        failures.append("artifact_id")

    scope = _mapping(payload.get("scope"))
    for key in ("formal_bedc_namecert", "lean_verification", "paper_closurestatus", "canonical_report"):
        if scope.get(key) is not False:
            failures.append(f"scope.{key}")

    hg1_failures = _orders_missing_evidence(payload)
    hg2_failures = _causal_orders_missing_patch(payload)
    hg3_failures = _irreducible_orders_missing_baseline(payload)
    closure_open = _mapping(payload.get("closure_status")).get("overall") != "closed"
    hardgates = {
        "JETCERT-HG1": _hardgate_row("JETCERT-HG1", not hg1_failures, "each claimed order has an evidence pointer", hg1_failures),
        "JETCERT-HG2": _hardgate_row("JETCERT-HG2", not hg2_failures, "causal orders have patch pointers", hg2_failures),
        "JETCERT-HG3": _hardgate_row(
            "JETCERT-HG3",
            not hg3_failures,
            "irreducible orders have low-order baselines",
            hg3_failures,
        ),
        "JETCERT-HG4": _hardgate_row("JETCERT-HG4", not closure_open, "open closure blocks D5-M", ["$.closure_status.overall"] if closure_open else []),
    }
    d5_m_ready = not failures and all(row["status"] == "pass" for row in hardgates.values())
    if scope.get("d5_m_claim") is True and not d5_m_ready:
        failures.append("scope.d5_m_claim")
    if scope.get("d5_m_claim") not in {False, True}:
        failures.append("scope.d5_m_claim")

    return {
        "status": "pass" if not failures else "fail",
        "failures": failures,
        "hardgates": hardgates,
        "d5_m_ready": bool(d5_m_ready),
    }


def build_dgt_jet_projection(payload: Mapping[str, Any]) -> dict[str, Any]:
    audit = audit_jet_namecert_candidate(payload)
    if audit["status"] != "pass":
        raise ValueError(f"jet candidate owner audit failed: {audit['failures']}")
    owner_artifact = _string(payload.get("json_artifact"), OWNER_JSON_ARTIFACT)
    projection = {
        "schema_id": DGT_PROJECTION_SCHEMA_ID,
        "artifact_id": DGT_PROJECTION_ARTIFACT_ID,
        "generated_at": _string(payload.get("generated_at"), "source-generated-at-unavailable"),
        "projection_role": "pointer-only",
        "owner_artifact": owner_artifact,
        "owner_sha256": payload_sha256(payload),
        "hardgate_pointers": {
            gate_id: f"{owner_artifact}:$.audit.hardgates.{gate_id}"
            for gate_id in ("JETCERT-HG1", "JETCERT-HG2", "JETCERT-HG3", "JETCERT-HG4")
        },
        "render_metadata": {
            "projection_artifact": DGT_JSON_ARTIFACT,
            "markdown_artifact": MARKDOWN_ARTIFACT,
            "source_schema_id": SCHEMA_ID,
            "source_artifact_id": ARTIFACT_ID,
        },
    }
    projection_audit = audit_dgt_jet_projection(projection)
    if projection_audit["status"] != "pass":
        raise ValueError(f"DGT jet projection audit failed: {projection_audit['failures']}")
    return projection


def audit_dgt_jet_projection(payload: Mapping[str, Any]) -> dict[str, Any]:
    failures: list[str] = []
    allowed = {
        "schema_id",
        "artifact_id",
        "generated_at",
        "projection_role",
        "owner_artifact",
        "owner_sha256",
        "hardgate_pointers",
        "render_metadata",
    }
    extra = sorted(set(payload) - allowed)
    if extra:
        failures.append(f"unexpected_keys:{','.join(extra)}")
    if payload.get("schema_id") != DGT_PROJECTION_SCHEMA_ID:
        failures.append("schema_id")
    if payload.get("projection_role") != "pointer-only":
        failures.append("projection_role")
    for key in ("owner_artifact", "owner_sha256"):
        if not _nonempty_string(payload.get(key)):
            failures.append(key)
    forbidden = sorted(_recursive_forbidden_keys(payload, DGT_FORBIDDEN_OWNED_FACT_KEYS))
    if forbidden:
        failures.append(f"forbidden_owned_facts:{','.join(forbidden)}")
    return {
        "status": "pass" if not failures else "fail",
        "failures": failures,
        "forbidden_owned_fact_keys": forbidden,
    }


def render_boundary_causal_jet_certificate(payload: Mapping[str, Any]) -> str:
    owner_artifact = _string(payload.get("json_artifact"), OWNER_JSON_ARTIFACT)
    owner_digest = payload_sha256(payload)
    lines = [
        "# Boundary-Causal Jet Certificate",
        "",
        f"- Owner artifact: `{owner_artifact}`",
        f"- Owner SHA256: `{owner_digest}`",
        f"- Owner schema: `{payload.get('schema_id', 'missing')}`",
        f"- DGT projection: `{payload.get('dgt_projection_artifact', DGT_JSON_ARTIFACT)}`",
        "",
        "## Owner Pointers",
        "",
        "| cell | pointer |",
        "| --- | --- |",
    ]
    for field in (*SPEC_FIELDS, "ledger_policy", "scope", "closure_status", "audit"):
        lines.append(f"| `{field}` | `{owner_artifact}:$.{field}` |")
    lines.extend(["", "## Hardgate Pointers", "", "| gate | pointer |", "| --- | --- |"])
    for gate_id in ("JETCERT-HG1", "JETCERT-HG2", "JETCERT-HG3", "JETCERT-HG4"):
        lines.append(f"| `{gate_id}` | `{owner_artifact}:$.audit.hardgates.{gate_id}` |")
    lines.append("")
    return "\n".join(lines)


def payload_sha256(payload: Mapping[str, Any]) -> str:
    return hashlib.sha256(_json_bytes(payload)).hexdigest()


def _json_bytes(payload: Mapping[str, Any]) -> bytes:
    return (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _boundary_spec(jet_certificate_payload: Mapping[str, Any] | None, dgt_payload: Mapping[str, Any] | None) -> dict[str, Any]:
    evidence_pointer = None
    if isinstance(jet_certificate_payload, Mapping):
        evidence_pointer = f"{DGT_RUN_JET_CERTIFICATE_ARTIFACT}:$"
    elif isinstance(dgt_payload, Mapping):
        evidence_pointer = f"{DGT_CANONICAL_ARTIFACT}:$.jet_certificate_ref"
    return {
        "spec_id": "boundary-jet-order",
        "claimed_orders": [
            _order(
                "boundary-order",
                "boundary",
                evidence_pointer=evidence_pointer,
            )
        ],
        "source_pointer": evidence_pointer,
    }


def _derivative_spec(derivative_payload: Mapping[str, Any] | None) -> dict[str, Any]:
    evidence_pointer = f"{TRANSFORMER_DERIVATIVE_ATLAS_ARTIFACT}:$.layerwise_derivative_rows" if isinstance(derivative_payload, Mapping) else None
    return {
        "spec_id": "layerwise-derivative-order",
        "claimed_orders": [
            _order("first-derivative-order", "derivative", evidence_pointer=evidence_pointer)
        ],
        "source_pointer": evidence_pointer,
    }


def _irreducibility_spec(
    derivative_payload: Mapping[str, Any] | None,
    attribution_payload: Mapping[str, Any] | None,
) -> dict[str, Any]:
    evidence_pointer = f"{GAP_HEAD_ATTRIBUTION_ARTIFACT}:$.residualized_attribution_claim" if isinstance(attribution_payload, Mapping) else None
    baseline_pointer = f"{TRANSFORMER_DERIVATIVE_ATLAS_ARTIFACT}:$.margin_proxy_controls" if isinstance(derivative_payload, Mapping) else None
    return {
        "spec_id": "irreducible-low-order-comparison",
        "claimed_orders": [
            _order(
                "irreducible-first-order",
                "irreducible",
                evidence_pointer=evidence_pointer,
                low_order_baseline_pointer=baseline_pointer,
            )
        ],
        "source_pointer": evidence_pointer,
        "low_order_baseline_pointer": baseline_pointer,
    }


def _causal_patch_spec(causal_patch_payload: Mapping[str, Any] | None) -> dict[str, Any]:
    evidence_pointer = f"{CAUSAL_PATCH_SUITE_ARTIFACT}:$.patch_records" if isinstance(causal_patch_payload, Mapping) else None
    patch_pointer = f"{CAUSAL_PATCH_SUITE_ARTIFACT}:$.patch_types" if isinstance(causal_patch_payload, Mapping) else None
    return {
        "spec_id": "causal-patch-order",
        "claimed_orders": [
            _order(
                "causal-patch-order",
                "causal",
                evidence_pointer=evidence_pointer,
                patch_pointer=patch_pointer,
            )
        ],
        "source_pointer": evidence_pointer,
        "patch_pointer": patch_pointer,
    }


def _stability_spec(derivative_payload: Mapping[str, Any] | None, dgt_payload: Mapping[str, Any] | None) -> dict[str, Any]:
    evidence_pointer = None
    if isinstance(derivative_payload, Mapping):
        evidence_pointer = f"{TRANSFORMER_DERIVATIVE_ATLAS_ARTIFACT}:$.hardgate"
    elif isinstance(dgt_payload, Mapping):
        evidence_pointer = f"{DGT_CANONICAL_ARTIFACT}:$.hardgate"
    return {
        "spec_id": "jet-stability-order",
        "claimed_orders": [
            _order("stability-order", "stability", evidence_pointer=evidence_pointer)
        ],
        "source_pointer": evidence_pointer,
    }


def _order(
    order_id: str,
    order_kind: str,
    *,
    evidence_pointer: str | None,
    patch_pointer: str | None = None,
    low_order_baseline_pointer: str | None = None,
) -> dict[str, Any]:
    row = {
        "order_id": order_id,
        "order_kind": order_kind,
        "evidence_pointer": evidence_pointer,
        "status": "claimed" if _nonempty_string(evidence_pointer) else "open",
    }
    if patch_pointer is not None:
        row["patch_pointer"] = patch_pointer
    if low_order_baseline_pointer is not None:
        row["low_order_baseline_pointer"] = low_order_baseline_pointer
    return row


def _closure_status(specs: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    rows = {field: _spec_closure(specs.get(field, {})) for field in SPEC_FIELDS}
    rows["ledger_policy"] = "closed" if all(status == "closed" for status in rows.values()) else "open"
    rows["scope"] = "closed"
    rows["overall"] = "closed" if all(status == "closed" for status in rows.values()) else "open"
    return rows


def _spec_closure(spec: Mapping[str, Any]) -> str:
    orders = spec.get("claimed_orders")
    if not isinstance(orders, list) or not orders:
        return "open"
    for order in orders:
        if not isinstance(order, Mapping) or not _nonempty_string(order.get("evidence_pointer")):
            return "open"
        if order.get("order_kind") == "causal" and not _nonempty_string(order.get("patch_pointer")):
            return "open"
        if order.get("order_kind") == "irreducible" and not _nonempty_string(order.get("low_order_baseline_pointer")):
            return "open"
    return "closed"


def _ledger_policy(closure_status: Mapping[str, Any]) -> dict[str, Any]:
    open_fields = [field for field in SPEC_FIELDS if closure_status.get(field) != "closed"]
    return {
        "candidate_owner": OWNER_JSON_ARTIFACT,
        "d5_m_policy": "blocked-by-open-closure" if open_fields else "eligible-by-owner-audit",
        "open_closure_fields": open_fields,
        "not_formal_namecert": True,
        "not_canonical_report": True,
        "revoke_if": [
            "any claimed order lacks an evidence pointer",
            "any causal order lacks a patch pointer",
            "any irreducible order lacks a low-order baseline",
            "scope seal is broadened beyond lab-local candidate semantics",
        ],
    }


def _orders_missing_evidence(payload: Mapping[str, Any]) -> list[str]:
    failures = []
    for spec_field in SPEC_FIELDS:
        for index, order in enumerate(_orders(payload, spec_field)):
            if not _nonempty_string(order.get("evidence_pointer")):
                failures.append(f"$.{spec_field}.claimed_orders[{index}].evidence_pointer")
    return failures


def _causal_orders_missing_patch(payload: Mapping[str, Any]) -> list[str]:
    failures = []
    for index, order in enumerate(_orders(payload, "causal_patch_spec")):
        if order.get("order_kind") == "causal" and not _nonempty_string(order.get("patch_pointer")):
            failures.append(f"$.causal_patch_spec.claimed_orders[{index}].patch_pointer")
    return failures


def _irreducible_orders_missing_baseline(payload: Mapping[str, Any]) -> list[str]:
    failures = []
    for index, order in enumerate(_orders(payload, "irreducibility_spec")):
        if order.get("order_kind") == "irreducible" and not _nonempty_string(order.get("low_order_baseline_pointer")):
            failures.append(f"$.irreducibility_spec.claimed_orders[{index}].low_order_baseline_pointer")
    return failures


def _orders(payload: Mapping[str, Any], spec_field: str) -> list[Mapping[str, Any]]:
    orders = _mapping(payload.get(spec_field)).get("claimed_orders")
    return [order for order in orders if isinstance(order, Mapping)] if isinstance(orders, list) else []


def _hardgate_row(gate_id: str, passed: bool, criterion: str, blockers: list[str]) -> dict[str, Any]:
    return {
        "gate_id": gate_id,
        "status": "pass" if passed else "fail",
        "criterion": criterion,
        "blockers": blockers,
    }


def _source_artifacts(
    *,
    source_artifacts: Mapping[str, Any] | None,
    dgt_payload: Mapping[str, Any] | None,
    jet_certificate_payload: Mapping[str, Any] | None,
    derivative_payload: Mapping[str, Any] | None,
    causal_patch_payload: Mapping[str, Any] | None,
    attribution_payload: Mapping[str, Any] | None,
) -> dict[str, Any]:
    if source_artifacts is not None:
        return deepcopy(dict(source_artifacts))
    return {
        "dgt_canonical": _source_cell(DGT_CANONICAL_ARTIFACT, dgt_payload),
        "dgt_run_jet_certificate": _source_cell(DGT_RUN_JET_CERTIFICATE_ARTIFACT, jet_certificate_payload),
        "transformer_derivative_atlas": _source_cell(TRANSFORMER_DERIVATIVE_ATLAS_ARTIFACT, derivative_payload),
        "causal_patch_suite": _source_cell(CAUSAL_PATCH_SUITE_ARTIFACT, causal_patch_payload),
        "gap_head_attribution_capsule": _source_cell(GAP_HEAD_ATTRIBUTION_ARTIFACT, attribution_payload),
    }


def _source_cell(artifact: str, payload: Mapping[str, Any] | None) -> dict[str, Any]:
    present = isinstance(payload, Mapping)
    return {
        "artifact": artifact,
        "pointer": "$",
        "present": present,
        "schema_id": payload.get("schema_id") if present else None,
        "artifact_id": payload.get("artifact_id") if present else None,
        "generated_at": payload.get("generated_at") if present else None,
        "sha256": payload_sha256(payload) if present else None,
    }


def _generated_at_from_sources(*payloads: Mapping[str, Any] | None) -> str:
    values = [
        payload.get("generated_at")
        for payload in payloads
        if isinstance(payload, Mapping) and _nonempty_string(payload.get("generated_at"))
    ]
    if not values:
        return "source-generated-at-unavailable"
    return str(sorted(values)[-1])


def _recursive_forbidden_keys(value: Any, forbidden: frozenset[str]) -> set[str]:
    found: set[str] = set()
    if isinstance(value, Mapping):
        for key, item in value.items():
            if isinstance(key, str) and key in forbidden:
                found.add(key)
            found.update(_recursive_forbidden_keys(item, forbidden))
    elif isinstance(value, list):
        for item in value:
            found.update(_recursive_forbidden_keys(item, forbidden))
    return found


def _mapping(value: Any) -> Mapping[str, Any]:
    return value if isinstance(value, Mapping) else {}


def _string(value: Any, fallback: str) -> str:
    return value if isinstance(value, str) and value.strip() else fallback


def _nonempty_string(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())

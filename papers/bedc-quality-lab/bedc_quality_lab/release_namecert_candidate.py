"""Release NameCert candidate projection over the release manifest sidecar."""

from __future__ import annotations

from copy import deepcopy
from typing import Any, Mapping


SCHEMA_ID = "bedc-quality-lab:release-namecert-candidate"
ARTIFACT_ID = SCHEMA_ID
JSON_ARTIFACT = "reports/release_namecert_candidate.json"
MARKDOWN_ARTIFACT = "reports/release_namecert_candidate.md"

SIDECAR_PATH = "reports/release_manifest_sidecar.json"
SIDECAR_SCHEMA_ID = "bedc-quality-lab:release-manifest-sidecar"

FORBIDDEN_KEYS = {
    "required_pointers",
    "canonical_reports",
    "report_status",
    "host_env",
    "theoryclosure",
    "formalstatus",
    "leantarget",
    "closurestatus",
    "leanchecked",
}


def build_release_namecert_candidate(
    sidecar_payload: Mapping[str, Any],
    *,
    sidecar_digest: str,
    generated_at: str,
    make_check_passed: bool,
) -> dict[str, Any]:
    sidecar_artifact_id = _string(sidecar_payload.get("artifact_id"), "missing")
    sidecar_schema_id = _string(sidecar_payload.get("schema_id"), "missing")
    version = _string(sidecar_payload.get("version"), "missing")
    tag_status = _string(sidecar_payload.get("tag_status"), "missing")
    release_bundle_status = _string(sidecar_payload.get("release_bundle_status"), "missing")
    sidecar_generated_at = _string(sidecar_payload.get("generated_at"), "missing")
    required_pointer_count, resolved_pointer_count = _pointer_counts(sidecar_payload)
    release_manifest_ready = (
        release_bundle_status == "ready"
        and required_pointer_count > 0
        and required_pointer_count == resolved_pointer_count
    )
    publishable_tag_claim = bool(release_manifest_ready and tag_status == "present")
    pointer_resolution_pass = required_pointer_count > 0 and required_pointer_count == resolved_pointer_count
    source_sidecar_ready = release_bundle_status == "ready"
    candidate_ready = bool(
        release_manifest_ready
        and make_check_passed
        and pointer_resolution_pass
        and source_sidecar_ready
    )
    revoke_if = _revoke_if(sidecar_payload)

    source_spec = {
        "sidecar_path": SIDECAR_PATH,
        "sidecar_schema_id": sidecar_schema_id,
        "sidecar_artifact_id": sidecar_artifact_id,
        "sidecar_digest": sidecar_digest,
        "sidecar_generated_at": sidecar_generated_at,
        "release_bundle_status": release_bundle_status,
        "tag_status": tag_status,
        "required_pointer_count": required_pointer_count,
        "resolved_pointer_count": resolved_pointer_count,
        "sidecar_cell_pointers": {
            "schema_id": "$.schema_id",
            "artifact_id": "$.artifact_id",
            "generated_at": "$.generated_at",
            "release_bundle_status": "$.release_bundle_status",
            "tag_status": "$.tag_status",
            "required_pointer_rows": "$.required_pointers",
            "revoke_if": "$.revoke_if",
        },
    }
    pattern_spec = {
        "name": "ReleaseNameCertCandidate",
        "projection": "thin sidecar projection",
        "source": SIDECAR_PATH,
        "sidecar_readiness_is_scientific_evidence": False,
        "sidecar_readiness_is_model_quality_evidence": False,
        "sidecar_readiness_is_theory_closure_evidence": False,
    }
    classifier_spec = {
        "classifier": "release-ready vs not",
        "release_manifest_ready": release_manifest_ready,
        "publishable_tag_claim": publishable_tag_claim,
        "scientific_claim": False,
        "model_quality_proof": False,
        "bedc_theory_closure": False,
        "release_closure": "candidate-only",
    }
    stab_cert = {
        "make_check_pass": {
            "status": "pass" if make_check_passed else "fail",
            "evidence": "explicit canonical runner make-check evidence"
            if make_check_passed
            else "explicit make-check evidence did not pass",
        },
        "pointer_resolution": {
            "status": "pass" if pointer_resolution_pass else "fail",
            "pointer": "$.source_spec.sidecar_cell_pointers.required_pointer_rows",
            "evidence": {
                "required_pointer_count": required_pointer_count,
                "resolved_pointer_count": resolved_pointer_count,
            },
        },
        "no_overclaim": {
            "status": "pass",
            "pointer": "$.classifier_spec",
            "evidence": "scientific, model-quality, and theory-closure claims are false",
        },
        "source_sidecar_ready": {
            "status": "pass" if source_sidecar_ready else "fail",
            "pointer": "$.source_spec.release_bundle_status",
            "evidence": release_bundle_status,
        },
    }
    ledger_policy = {
        "tag_absent": {
            "status": "active" if tag_status == "absent" else "inactive",
            "pointer": "$.source_spec.tag_status",
            "publishable_tag_claim": publishable_tag_claim,
        },
        "not_scientific_claim": True,
        "not_model_quality_proof": True,
        "not_bedc_closure": True,
        "not_theory_closure": True,
        "revoke_if": revoke_if,
    }
    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": ARTIFACT_ID,
        "generated_at": generated_at,
        "json_artifact": JSON_ARTIFACT,
        "markdown_artifact": MARKDOWN_ARTIFACT,
        "release_id": _release_id(
            sidecar_artifact_id=sidecar_artifact_id,
            version=version,
            tag_status=tag_status,
            publishable_tag_claim=publishable_tag_claim,
        ),
        "candidate_status": "ready-candidate" if candidate_ready else "not-ready-candidate",
        "source_spec": source_spec,
        "pattern_spec": pattern_spec,
        "classifier_spec": classifier_spec,
        "stab_cert": stab_cert,
        "ledger_policy": ledger_policy,
        "revoke_if": deepcopy(revoke_if),
    }


def audit_release_namecert_candidate(payload: Mapping[str, Any]) -> dict[str, Any]:
    failures: list[str] = []
    if payload.get("schema_id") != SCHEMA_ID:
        failures.append("schema_id")
    if payload.get("artifact_id") != ARTIFACT_ID:
        failures.append("artifact_id")

    source_spec = _mapping(payload.get("source_spec"))
    classifier_spec = _mapping(payload.get("classifier_spec"))
    ledger_policy = _mapping(payload.get("ledger_policy"))
    stab_cert = _mapping(payload.get("stab_cert"))

    if source_spec.get("sidecar_schema_id") != SIDECAR_SCHEMA_ID:
        failures.append("source_spec.sidecar_schema_id")
    if not _nonempty_string(source_spec.get("sidecar_digest")):
        failures.append("source_spec.sidecar_digest")
    if not _pointer_counts_match(source_spec):
        failures.append("source_spec.pointer_counts")

    if classifier_spec.get("scientific_claim") is not False:
        failures.append("classifier_spec.scientific_claim")
    if classifier_spec.get("model_quality_proof") is not False:
        failures.append("classifier_spec.model_quality_proof")
    if classifier_spec.get("bedc_theory_closure") is not False:
        failures.append("classifier_spec.bedc_theory_closure")
    if classifier_spec.get("release_closure") != "candidate-only":
        failures.append("classifier_spec.release_closure")
    if source_spec.get("tag_status") == "absent" and classifier_spec.get("publishable_tag_claim") is not False:
        failures.append("classifier_spec.publishable_tag_claim")

    if ledger_policy.get("not_scientific_claim") is not True:
        failures.append("ledger_policy.not_scientific_claim")
    if ledger_policy.get("not_model_quality_proof") is not True:
        failures.append("ledger_policy.not_model_quality_proof")
    if ledger_policy.get("not_bedc_closure") is not True:
        failures.append("ledger_policy.not_bedc_closure")
    if ledger_policy.get("not_theory_closure") is not True:
        failures.append("ledger_policy.not_theory_closure")

    revoke_if = payload.get("revoke_if")
    ledger_revoke_if = ledger_policy.get("revoke_if")
    if not _nonempty_value(revoke_if):
        failures.append("revoke_if")
    if revoke_if != ledger_revoke_if and revoke_if != "$.ledger_policy.revoke_if":
        failures.append("revoke_if.ledger_policy")

    for name in ("make_check_pass", "pointer_resolution", "no_overclaim", "source_sidecar_ready"):
        cell = _mapping(stab_cert.get(name))
        if cell.get("status") not in {"pass", "fail"}:
            failures.append(f"stab_cert.{name}.status")
    overclaim_forbidden_keys = sorted(_forbidden_keys(payload))
    if overclaim_forbidden_keys:
        failures.append("forbidden_keys")

    return {
        "status": "pass" if not failures else "fail",
        "failures": failures,
        "forbidden_keys": overclaim_forbidden_keys,
        "hardgates": {
            "G-HG1": classifier_spec.get("scientific_claim") is False,
            "G-HG2": not (
                source_spec.get("tag_status") == "absent"
                and classifier_spec.get("publishable_tag_claim") is True
            ),
            "G-HG3": _nonempty_value(revoke_if),
            "G-HG4": classifier_spec.get("release_closure") == "candidate-only",
        },
    }


def render_release_namecert_candidate_markdown(payload: Mapping[str, Any]) -> str:
    audit = audit_release_namecert_candidate(payload)
    source_spec = _mapping(payload.get("source_spec"))
    classifier_spec = _mapping(payload.get("classifier_spec"))
    ledger_policy = _mapping(payload.get("ledger_policy"))
    lines = [
        "# Release NameCert Candidate",
        "",
        f"- Schema: `{payload.get('schema_id', 'missing')}`",
        f"- Artifact: `{payload.get('artifact_id', 'missing')}`",
        f"- Generated at: `{payload.get('generated_at', 'missing')}`",
        f"- Candidate status: `{payload.get('candidate_status', 'missing')}`",
        f"- Source sidecar: `{source_spec.get('sidecar_path', 'missing')}`",
        f"- Source digest: `{source_spec.get('sidecar_digest', 'missing')}`",
        f"- Release bundle status: `{source_spec.get('release_bundle_status', 'missing')}`",
        f"- Tag status: `{source_spec.get('tag_status', 'missing')}`",
        f"- Publishable tag claim: `{classifier_spec.get('publishable_tag_claim', 'missing')}`",
        f"- Release closure: `{classifier_spec.get('release_closure', 'missing')}`",
        f"- Audit status: `{audit['status']}`",
        "",
        "## Pointers",
        "",
        f"- Ledger policy pointer: `$.ledger_policy`",
        f"- Revoke pointer: `$.ledger_policy.revoke_if`",
        f"- Sidecar revoke pointer: `{_mapping(source_spec.get('sidecar_cell_pointers')).get('revoke_if', 'missing')}`",
        "",
        "## Ledger Policy",
        "",
        f"- Tag absent policy: `{_mapping(ledger_policy.get('tag_absent')).get('status', 'missing')}`",
        f"- Scientific claim: `{classifier_spec.get('scientific_claim', 'missing')}`",
        f"- Model-quality proof: `{classifier_spec.get('model_quality_proof', 'missing')}`",
        f"- BEDC theory closure: `{classifier_spec.get('bedc_theory_closure', 'missing')}`",
        "",
        "## Revoke If",
        "",
    ]
    revoke_if = payload.get("revoke_if")
    if isinstance(revoke_if, list):
        for item in revoke_if:
            lines.append(f"- {item}")
    else:
        lines.append(str(revoke_if))
    lines.append("")
    return "\n".join(lines)


def _release_id(
    *,
    sidecar_artifact_id: str,
    version: str,
    tag_status: str,
    publishable_tag_claim: bool,
) -> dict[str, Any]:
    identity_kind = "publishable-tag" if publishable_tag_claim else "non-publishable"
    return {
        "identity": f"{sidecar_artifact_id}@{version}:{identity_kind}",
        "source_artifact_id": sidecar_artifact_id,
        "source_version": version,
        "tag_status_pointer": "$.source_spec.tag_status",
        "publishable": publishable_tag_claim,
        "tag_claim": "present" if publishable_tag_claim else "none",
        "tag_absent": tag_status == "absent",
    }


def _pointer_counts(sidecar_payload: Mapping[str, Any]) -> tuple[int, int]:
    rows = sidecar_payload.get("required_pointers")
    if not isinstance(rows, list):
        return (0, 0)
    resolved = sum(1 for row in rows if isinstance(row, Mapping) and row.get("status") == "resolved")
    return (len(rows), resolved)


def _pointer_counts_match(source_spec: Mapping[str, Any]) -> bool:
    required = source_spec.get("required_pointer_count")
    resolved = source_spec.get("resolved_pointer_count")
    return isinstance(required, int) and required > 0 and required == resolved


def _revoke_if(sidecar_payload: Mapping[str, Any]) -> list[str]:
    value = sidecar_payload.get("revoke_if")
    if isinstance(value, list):
        return [str(item) for item in value if str(item).strip()]
    if isinstance(value, str) and value.strip():
        return [value]
    return []


def _forbidden_keys(value: Any) -> set[str]:
    found: set[str] = set()
    if isinstance(value, Mapping):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS:
                found.add(str(key))
            found.update(_forbidden_keys(child))
    elif isinstance(value, list):
        for child in value:
            found.update(_forbidden_keys(child))
    return found


def _mapping(value: Any) -> Mapping[str, Any]:
    return value if isinstance(value, Mapping) else {}


def _string(value: Any, fallback: str) -> str:
    return value if isinstance(value, str) and value else fallback


def _nonempty_string(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _nonempty_value(value: Any) -> bool:
    if isinstance(value, str):
        return bool(value.strip())
    if isinstance(value, (list, tuple, set, dict)):
        return bool(value)
    return value is not None and bool(value)

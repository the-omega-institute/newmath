import json

import bedc_quality_lab
from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope
from bedc_quality_lab.tensor_namecert_candidate import (
    TensorNameCertCandidate,
    from_quality_evidence_envelope,
)


def envelope_kwargs(**overrides):
    data = {
        "schema_id": SCHEMA_ID,
        "run_id": "candidate-test",
        "source_spec": {"name": "source", "status": "sufficient"},
        "pattern_spec": {"name": "pattern"},
        "classifier_spec": {"name": "classifier", "cert_status": "certified"},
        "stability_spec": {"name": "stability"},
        "metrics": {"linear_identifiability_r2": 0.75},
        "ledger_gaps": ["kind=verification; residue=bound; severity=none; status=closed"],
        "debt_items": ["kind=verification; residue=bound; severity=none; status=closed; score=0.000000"],
        "artifacts": {"report": "reports/quality_report.md"},
        "bedc_refs": ["papers/bedc/preamble.tex:closurestatus"],
    }
    data.update(overrides)
    return data


def make_envelope(**overrides):
    return QualityEvidenceEnvelope(**envelope_kwargs(**overrides))


def test_tensor_namecert_candidate_projects_envelope_specs():
    envelope = make_envelope()

    candidate = from_quality_evidence_envelope(envelope)

    assert isinstance(candidate, TensorNameCertCandidate)
    assert candidate.name == "TensorNameCertCandidate:candidate-test"
    assert candidate.source_spec == envelope.source_spec
    assert candidate.pattern_spec == envelope.pattern_spec
    assert candidate.classifier_spec == envelope.classifier_spec
    assert candidate.stab_cert == envelope.stability_spec
    assert candidate.ledger_policy["ledger_gaps"] == envelope.ledger_gaps
    assert candidate.ledger_policy["debt_items"] == envelope.debt_items
    assert candidate.evidence_envelope_ref == {
        "schema_id": SCHEMA_ID,
        "run_id": "candidate-test",
    }
    assert candidate.closure_status == {
        "source_spec": "closed",
        "pattern_spec": "closed",
        "classifier_spec": "closed",
        "stab_cert": "closed",
        "ledger_policy": "closed",
        "scope_seal": "closed",
    }


def test_tensor_namecert_candidate_missing_fields_warn_without_parse_failure():
    envelope = make_envelope(
        source_spec={},
        stability_spec={"seed": 23},
    )

    candidate = TensorNameCertCandidate.from_quality_evidence_envelope(envelope)

    assert candidate.closure_status["source_spec"] == "warning"
    assert candidate.closure_status["stab_cert"] == "warning"
    assert candidate.closure_status["pattern_spec"] == "closed"


def test_tensor_namecert_candidate_weak_classifier_cert_is_partial():
    envelope = make_envelope(
        classifier_spec={"name": "classifier", "cert_status": "not-certified"},
        ledger_gaps=["kind=classifier; residue=optimizer-certificate; severity=medium; status=partial"],
        debt_items=[],
    )

    candidate = from_quality_evidence_envelope(envelope)

    assert candidate.closure_status["classifier_spec"] == "partial"
    assert candidate.closure_status["ledger_policy"] == "partial"


def test_tensor_namecert_candidate_unused_ledger_maps_to_none():
    envelope = make_envelope(ledger_gaps=[], debt_items=[])

    candidate = from_quality_evidence_envelope(envelope)

    assert candidate.closure_status["ledger_policy"] == "none"
    assert candidate.ledger_policy["active_gap_count"] == 0
    assert candidate.ledger_policy["debt_item_count"] == 0


def test_tensor_namecert_candidate_to_dict_is_json_ready():
    candidate = from_quality_evidence_envelope(make_envelope())

    data = candidate.to_dict()
    encoded = json.dumps(data, sort_keys=True)

    assert "TensorNameCertCandidate:candidate-test" in encoded
    assert data["evidence_envelope_ref"] == {
        "schema_id": SCHEMA_ID,
        "run_id": "candidate-test",
    }
    assert "schema_id" not in data


def test_tensor_namecert_candidate_stays_package_local_and_candidate_only():
    candidate = from_quality_evidence_envelope(make_envelope())

    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]
    assert not hasattr(bedc_quality_lab, "TensorNameCertCandidate")
    assert "TensorNameCert:" not in candidate.name
    assert candidate.scope_seal["formal_bedc_certificate"] is False
    assert candidate.scope_seal["candidate_json_artifact"] is False

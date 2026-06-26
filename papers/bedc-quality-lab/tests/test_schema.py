import pytest

from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope


def envelope_kwargs():
    return {
        "schema_id": SCHEMA_ID,
        "run_id": "schema-test",
        "source_spec": {"name": "source"},
        "pattern_spec": {"name": "pattern"},
        "classifier_spec": {"name": "classifier"},
        "stability_spec": {"name": "stability"},
        "metrics": {"linear_identifiability_r2": 0.75},
        "ledger_gaps": ["finite-sample-only"],
        "debt_items": ["distribution-debt"],
        "artifacts": {"report": "reports/quality_report.md"},
        "bedc_refs": ["papers/bedc/preamble.tex:closurestatus"],
    }


def test_schema_requires_evidence_boundary():
    envelope = QualityEvidenceEnvelope(**envelope_kwargs())
    assert envelope.schema_id == SCHEMA_ID
    data = envelope.to_dict()
    assert set(data) == {
        "schema_id",
        "run_id",
        "source_spec",
        "pattern_spec",
        "classifier_spec",
        "stability_spec",
        "metrics",
        "ledger_gaps",
        "debt_items",
        "artifacts",
        "bedc_refs",
        "evidence_type",
        "evidence_scope",
        "backend_owner",
        "source_artifact_hash",
        "claim_capsule_pointer",
        "cost_protocol_pointer",
        "negative_witness_sweep_pointer",
    }

    bad = envelope_kwargs()
    bad["schema_id"] = "bedc-quality-lab:namecert"
    with pytest.raises(ValueError, match="schema_id"):
        QualityEvidenceEnvelope(**bad)


def test_schema_rejects_bedc_rule_copies():
    bad = envelope_kwargs()
    bad["bedc_refs"] = [
        "closurestatus records theoryclosure and formalstatus and must use BEDC rule prose"
    ]
    with pytest.raises(ValueError, match="opaque pointers"):
        QualityEvidenceEnvelope(**bad)

    good = envelope_kwargs()
    good["bedc_refs"] = ["papers/bedc/preamble.tex:closurestatus"]
    assert QualityEvidenceEnvelope(**good).bedc_refs == good["bedc_refs"]


def test_schema_requires_explicit_evidence_provenance_fields():
    envelope = QualityEvidenceEnvelope(**envelope_kwargs())
    data = envelope.to_dict()

    assert data["evidence_type"] == "unspecified"
    assert data["evidence_scope"] == "unspecified"
    assert data["backend_owner"] == "unspecified"
    assert data["source_artifact_hash"] == {}
    assert data["claim_capsule_pointer"] == {}
    assert data["cost_protocol_pointer"] == {}
    assert data["negative_witness_sweep_pointer"] == {}

    for field_name in ("evidence_type", "evidence_scope", "backend_owner"):
        for invalid_value in ("", 3):
            bad = envelope_kwargs()
            bad[field_name] = invalid_value
            with pytest.raises(ValueError, match=field_name):
                QualityEvidenceEnvelope(**bad)


def test_schema_accepts_pointer_only_evidence_surfaces():
    kwargs = envelope_kwargs()
    kwargs.update(
        {
            "evidence_type": "quality-evidence",
            "evidence_scope": "lab-run",
            "backend_owner": "bedc-quality-lab",
            "source_artifact_hash": {
                "algorithm": "sha256",
                "value": "0" * 64,
            },
            "claim_capsule_pointer": {
                "artifact": "reports/quality_report.json",
                "pointer": "$.claims[0]",
            },
            "cost_protocol_pointer": {
                "artifact": "reports/quality_report.json",
                "pointer": "$.cost.protocol",
            },
            "negative_witness_sweep_pointer": {
                "artifact": "reports/quality_report.json",
                "pointer": "$.negative_witness_sweep",
            },
        }
    )

    envelope = QualityEvidenceEnvelope(**kwargs)

    assert envelope.source_artifact_hash == {
        "algorithm": "sha256",
        "value": "0" * 64,
    }
    assert envelope.claim_capsule_pointer == {
        "artifact": "reports/quality_report.json",
        "pointer": "$.claims[0]",
    }


def test_schema_accepts_sha256_digest_with_prose_marker_substring():
    kwargs = envelope_kwargs()
    digest = f"{'a' * 30}d4{'b' * 32}"
    kwargs["source_artifact_hash"] = {
        "algorithm": "sha256",
        "value": digest,
    }

    envelope = QualityEvidenceEnvelope(**kwargs)

    assert envelope.source_artifact_hash == {
        "algorithm": "sha256",
        "value": digest,
    }


def test_schema_rejects_incomplete_source_artifact_hash_mapping():
    for invalid_hash in (
        {"value": "0" * 64},
        {"algorithm": "sha256"},
    ):
        bad = envelope_kwargs()
        bad["source_artifact_hash"] = invalid_hash
        with pytest.raises(ValueError, match="source_artifact_hash"):
            QualityEvidenceEnvelope(**bad)


def test_schema_rejects_extra_source_artifact_hash_mapping_key():
    bad = envelope_kwargs()
    bad["source_artifact_hash"] = {
        "algorithm": "sha256",
        "value": "0" * 64,
        "note": "report.json",
    }

    with pytest.raises(ValueError, match="source_artifact_hash"):
        QualityEvidenceEnvelope(**bad)


def test_schema_rejects_non_sha256_source_artifact_hash_algorithm():
    bad = envelope_kwargs()
    bad["source_artifact_hash"] = {
        "algorithm": "md5",
        "value": "0" * 64,
    }

    with pytest.raises(ValueError, match="source_artifact_hash"):
        QualityEvidenceEnvelope(**bad)


def test_schema_rejects_non_hex_source_artifact_hash_value():
    for invalid_value in ("", "g" * 64, "A" * 64):
        bad = envelope_kwargs()
        bad["source_artifact_hash"] = {
            "algorithm": "sha256",
            "value": invalid_value,
        }
        with pytest.raises(ValueError, match="source_artifact_hash"):
            QualityEvidenceEnvelope(**bad)


def test_schema_rejects_terminal_verdict_and_payload_leakage():
    pointer_fields = (
        "claim_capsule_pointer",
        "cost_protocol_pointer",
        "negative_witness_sweep_pointer",
    )
    forbidden_values = (
        {"artifact": "report.json", "pointer": "$.claims", "terminal_verdict": "pass"},
        {"artifact": "report.json", "pointer": "$.claims", "discovery_level": "D4"},
        {"artifact": "report.json", "pointer": "$.claims", "payload": {"value": 1}},
        {"artifact": "report.json", "pointer": "$.claims", "raw_payload": {"value": 1}},
        {"artifact": "report.json", "pointer": "$.claims", "report_payload": {"value": 1}},
        {"artifact": "report.json", "pointer": "$.claims.D5-O"},
        {"artifact": "report.json", "pointer": "$.claims.D5-M"},
        {
            "artifact": "report.json",
            "pointer": "$.claims",
            "note": "closurestatus records theoryclosure prose",
        },
    )

    for field_name in pointer_fields:
        for forbidden_value in forbidden_values:
            bad = envelope_kwargs()
            bad[field_name] = forbidden_value
            with pytest.raises(ValueError, match=field_name):
                QualityEvidenceEnvelope(**bad)

    bad_missing_pointer = envelope_kwargs()
    bad_missing_pointer["claim_capsule_pointer"] = {"artifact": "report.json"}
    with pytest.raises(ValueError, match="claim_capsule_pointer"):
        QualityEvidenceEnvelope(**bad_missing_pointer)

    bad_missing_artifact = envelope_kwargs()
    bad_missing_artifact["claim_capsule_pointer"] = {"pointer": "$.claims"}
    with pytest.raises(ValueError, match="claim_capsule_pointer"):
        QualityEvidenceEnvelope(**bad_missing_artifact)

    bad_pointer = envelope_kwargs()
    bad_pointer["claim_capsule_pointer"] = {
        "artifact": "report.json",
        "pointer": "claims",
    }
    with pytest.raises(ValueError, match="claim_capsule_pointer"):
        QualityEvidenceEnvelope(**bad_pointer)


def test_schema_json_roundtrip_uses_public_reader(tmp_path):
    kwargs = envelope_kwargs()
    kwargs.update(
        {
            "evidence_type": "quality-evidence",
            "evidence_scope": "lab-run",
            "backend_owner": "bedc-quality-lab",
            "source_artifact_hash": {
                "algorithm": "sha256",
                "value": "a" * 64,
            },
            "claim_capsule_pointer": {
                "artifact": "reports/quality_report.json",
                "pointer": "$.claims[0]",
            },
            "cost_protocol_pointer": {
                "artifact": "reports/quality_report.json",
                "pointer": "$.cost.protocol",
            },
            "negative_witness_sweep_pointer": {
                "artifact": "reports/quality_report.json",
                "pointer": "$.negative_witness_sweep",
            },
        }
    )
    envelope = QualityEvidenceEnvelope(**kwargs)
    path = tmp_path / "envelope.json"

    envelope.write_json(path)
    restored = QualityEvidenceEnvelope.read_json(path)

    assert restored == envelope
    assert restored.to_dict() == envelope.to_dict()
    assert restored.schema_id == SCHEMA_ID
    assert restored.run_id == "schema-test"
    assert restored.artifacts == {"report": "reports/quality_report.md"}
    assert restored.evidence_type == "quality-evidence"
    assert restored.evidence_scope == "lab-run"
    assert restored.backend_owner == "bedc-quality-lab"
    assert restored.source_artifact_hash == {
        "algorithm": "sha256",
        "value": "a" * 64,
    }
    assert restored.claim_capsule_pointer == {
        "artifact": "reports/quality_report.json",
        "pointer": "$.claims[0]",
    }

from bedc_quality_lab.schema import SCHEMA_ID, QualityEvidenceEnvelope
from scripts.run_bedc_jepa_boundary_world import run_protocol


def test_bedc_jepa_boundary_protocol_emits_quality_envelope(tmp_path):
    envelope = run_protocol()
    assert envelope.schema_id == SCHEMA_ID
    assert envelope.run_id == "boundary-gated-bedc-jepa-protocol-seed-41"
    assert envelope.source_spec["name"] == "boundary-gated-ou-world"
    assert envelope.pattern_spec["name"] == "latent-plus-distinction-plus-gap"
    assert envelope.classifier_spec["name"] == "bedc-jepa-protocol-radial-distinction-gap-heads"
    assert envelope.artifacts == {
        "envelope": "reports/bedc_jepa_boundary_envelope.json",
        "report": "reports/bedc_jepa_boundary_report.md",
    }
    assert envelope.metrics["linear_identifiability_r2"] > 0.85
    assert envelope.metrics["distinction_accuracy_outside_gap"] > 0.75
    assert 0.0 <= envelope.metrics["gap_detection_auc"] <= 1.0
    assert 0.0 <= envelope.metrics["bedc_debt_score"] <= 1.0

    path = tmp_path / "envelope.json"
    envelope.write_json(path)
    assert QualityEvidenceEnvelope.read_json(path) == envelope

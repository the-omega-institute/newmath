import json

import numpy as np

from bedc_quality_lab import __all__ as package_all
from bedc_quality_lab.schema import SCHEMA_ID
from scripts import run_canonical_reports as canonical
from scripts import run_gap_head_attribution_v3 as a1
from scripts import run_gap_head_mechanism_attribution as runner


def test_row_l2_direction_compatibility_helper():
    h = np.array([[3.0, 4.0], [0.0, 0.0]], dtype=np.float64)

    direction = runner._row_l2_direction(h)

    np.testing.assert_allclose(direction[0], [0.6, 0.8])
    np.testing.assert_allclose(direction[1], [0.0, 0.0])


def test_mechanism_projection_reads_a1_source_only():
    payload = {
        "run_id": "fixture",
        "mechanism_case": {"status": "D5-O retained, mechanism = probe-margin-channel"},
        "d5_o": {"status": "ready"},
        "d5_m": {"status": "blocked", "failed_gate": "A1-HG3"},
        "config": {"arm_count": 22, "arm_order": list(a1.ARM_NAMES)},
        "hardgates": {"status": "fail"},
        "scope": {"not_claimed": list(a1.NOT_CLAIMED)},
    }

    projection = runner._project_payload(payload, generated_at="fixture-time")

    assert projection["artifact_id"] == "bedc-quality-lab:gap-head-mechanism-attribution"
    assert projection["sidecar_role"] == "compatibility_projection"
    assert projection["canonical_source"]["json_artifact"] == "reports/canonical/gap_head_attribution_v3.json"
    assert projection["mechanism_status"] == "D5-O retained, mechanism = probe-margin-channel"
    assert projection["D5_target"]["mechanism"]["failed_gate"] == "A1-HG3"
    assert projection["config"]["arm_count"] == 22
    assert projection["HG_A1"]["source_pointer"] == "reports/canonical/gap_head_attribution_v3.json:$.hardgates"
    assert "gates" not in projection["HG_A1"]
    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert package_all == ["QualityEvidenceEnvelope"]


def test_canonical_index_keeps_projection_sidecar_out_of_manifest(tmp_path, monkeypatch):
    sidecar = tmp_path / runner.JSON_ARTIFACT
    sidecar.parent.mkdir(parents=True)
    sidecar.write_text(
        json.dumps(
            {
                "artifact_id": runner.ARTIFACT_ID,
                "mechanism_status": "D5-O retained, mechanism = probe-margin-channel",
                "config": {"arm_count": 22},
                "HG_A1": {"status": "fail"},
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    names = [spec.name for spec in canonical.CANONICAL_REPORTS]

    section = canonical._gap_head_mechanism_attribution_index_section()
    payload = canonical._index([])
    markdown = canonical._render_index_markdown(payload)

    assert "gap-head-mechanism-attribution" not in names
    assert section["artifact_id"] == runner.ARTIFACT_ID
    assert section["canonical_role"] == "sidecar_not_in_CANONICAL_REPORTS"
    assert payload["gap_head_mechanism_attribution"]["mechanism_status"] == "D5-O retained, mechanism = probe-margin-channel"
    assert "Gap-head mechanism attribution" in markdown
    assert "gap_head_mechanism_attribution" not in json.dumps(payload["discovery_map"])

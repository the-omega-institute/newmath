import json
from pathlib import Path

from bedc_quality_lab import structural_generalization_splits as sgs


def _candidate(**updates):
    base = dict(
        row_id="demo-row",
        source_row_id="source-row",
        family="symbol_remapping",
        target_variable="answer",
        candidate_id="candidate",
        fair_arm_id="fair-arm",
        target_visible=True,
        candidate_visible=True,
        fair_arm_visible=True,
        candidate_winnable=True,
        fair_arm_winnable=True,
        visibility_pointer="reports/canonical/input-accessibility.json:$.rows[0]",
        winnability_pointer="reports/canonical/winnability-certificates.json:$.rows[0]",
        performance_pointer="reports/canonical/performance.json:$.rows[0]",
        finite_remap={"x": "u"},
        position_offset=1,
    )
    base.update(updates)
    return sgs.StructuralGeneralizationSplit(**base)


def _write_source_artifacts(root: Path) -> None:
    canonical = root / "reports" / "canonical"
    canonical.mkdir(parents=True, exist_ok=True)
    (canonical / "input-accessibility.json").write_text(
        json.dumps(
            {
                "schema_id": sgs.INPUT_ACCESSIBILITY_SCHEMA_ID,
                "rows": [
                    {
                        "row_id": "symbol",
                        "family": "symbol_remapping",
                        "target_variable": "symbol",
                        "candidate_id": "candidate",
                        "fair_arm_id": "fair-arm",
                        "target_visible": True,
                        "candidate_visible": True,
                        "fair_arm_visible": True,
                        "finite_remap": {"x": "u"},
                        "performance_pointer": "reports/canonical/performance.json:$.rows[0]",
                    }
                ],
            }
        )
        + "\n",
        encoding="utf-8",
    )
    (canonical / "winnability-certificates.json").write_text(
        json.dumps(
            {
                "schema_id": sgs.WINNABILITY_CERTIFICATES_SCHEMA_ID,
                "rows": [
                    {
                        "row_id": "symbol",
                        "candidate_winnable": True,
                        "fair_arm_winnable": True,
                    }
                ],
            }
        )
        + "\n",
        encoding="utf-8",
    )
    (canonical / "performance.json").write_text(json.dumps({"rows": [{"score": 1.0}]}) + "\n", encoding="utf-8")


def test_symbol_remapping_hardgates_cover_sym_hg1_to_sym_hg4(tmp_path):
    root = tmp_path
    (root / "reports/canonical").mkdir(parents=True)
    (root / "reports/canonical/performance.json").write_text(json.dumps({"rows": [{"score": 1.0}]}) + "\n", encoding="utf-8")

    gates = sgs.evaluate_symbol_remapping_hardgates(_candidate(), root=root)

    assert set(gates) == {"SYM-HG1", "SYM-HG2", "SYM-HG3", "SYM-HG4"}
    assert {gate["status"] for gate in gates.values()} == {"pass"}


def test_position_shift_hardgates_cover_pos_hg1_to_pos_hg4(tmp_path):
    root = tmp_path
    (root / "reports/canonical").mkdir(parents=True)
    (root / "reports/canonical/performance.json").write_text(json.dumps({"rows": [{"score": 1.0}]}) + "\n", encoding="utf-8")
    split = _candidate(family="position_shift_visible", finite_remap=None, position_offset=2)

    gates = sgs.evaluate_position_shift_hardgates(split, root=root)

    assert set(gates) == {"POS-HG1", "POS-HG2", "POS-HG3", "POS-HG4"}
    assert {gate["status"] for gate in gates.values()} == {"pass"}


def test_row_id_is_stable():
    first = _candidate(row_id=None).public_row_id
    second = _candidate(row_id=None).public_row_id

    assert first == second
    assert first.startswith("sgs-")


def test_missing_upstream_pointer_fails_closed(tmp_path):
    payload = sgs.build_structural_generalization_payload(root=tmp_path, generated_at="fixture")

    assert payload["split_rows"] == []
    assert payload["boundary_ledger"]
    assert payload["source_artifacts"]["input_accessibility"]["status"] == "missing"
    assert payload["source_artifacts"]["winnability_certificates"]["status"] == "missing"
    assert {row["classification"] for row in payload["classifier_rows"]} == {"excluded"}


def test_performance_evidence_pointer_missing_does_not_create_positive_claim(tmp_path):
    _write_source_artifacts(tmp_path)
    (tmp_path / "reports/canonical/performance.json").unlink()

    payload = sgs.build_structural_generalization_payload(root=tmp_path, generated_at="fixture")

    assert payload["split_rows"] == []
    assert payload["classifier_rows"][0]["classification"] == "excluded"
    assert payload["classifier_rows"][0]["failed_hardgates"] == ["SYM-HG4"]


def test_consumer_pointer_shape(tmp_path):
    _write_source_artifacts(tmp_path)
    payload = sgs.build_structural_generalization_payload(root=tmp_path, generated_at="fixture")

    assert payload["consumer_pointers"] == {
        "splits_pointer": "reports/canonical/structural-generalization-splits.json:$.split_rows",
        "classifier_pointer": "reports/canonical/structural-generalization-splits.json:$.classifier_rows",
        "hardgates_pointer": "reports/canonical/structural-generalization-splits.json:$.hardgates",
        "boundary_pointer": "reports/canonical/structural-generalization-splits.json:$.boundary_ledger",
    }


def test_accepted_rows_are_json_safe_and_pointer_backed(tmp_path):
    _write_source_artifacts(tmp_path)
    payload = sgs.build_structural_generalization_payload(root=tmp_path, generated_at="fixture")

    json.dumps(payload, sort_keys=True)
    assert len(payload["split_rows"]) == 1
    row = payload["split_rows"][0]
    assert row["structural_generalization_family"] == "symbol_remapping"
    assert row["visibility_pointer"].startswith("reports/canonical/input-accessibility.json:")
    assert row["winnability_pointer"].startswith("reports/canonical/winnability-certificates.json:")

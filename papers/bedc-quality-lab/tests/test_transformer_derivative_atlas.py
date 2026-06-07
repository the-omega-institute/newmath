import json
from dataclasses import replace

from bedc_quality_lab.transformer_derivative_atlas import (
    ATTENTION_ROUTE_ARTIFACT,
    DEFAULT_CONFIG,
    LAYERWISE_JET_MAP_ARTIFACT,
    RAW_ROW_POINTER,
    DgtDeclaration,
    LayerwiseDerivativeRow,
    MarginProxyControlRow,
    TransformerDerivativeAtlasProjection,
    build_payload,
    collect_margin_proxy_controls,
    collect_rows,
    evaluate_layer_hardgates,
    render_attention_route_report,
    render_layerwise_jet_map,
)
from scripts import run_transformer_derivative_atlas as runner


def test_layerwise_derivative_rows_are_the_only_numerical_fact_schema():
    rows = collect_rows(DEFAULT_CONFIG)

    assert rows
    assert all(isinstance(row, LayerwiseDerivativeRow) for row in rows)
    assert len({row.row_id for row in rows}) == len(rows)
    assert all(row.control_row_pointer.startswith("$.margin_proxy_controls.by_id.control:") for row in rows)
    assert {row.route_id for row in rows} == set(DEFAULT_CONFIG["routes"])


def test_margin_proxy_controls_point_back_to_raw_rows():
    rows = collect_rows(DEFAULT_CONFIG)
    controls = collect_margin_proxy_controls(rows)

    assert controls
    assert all(isinstance(control, MarginProxyControlRow) for control in controls)
    assert [control.row_pointer for control in controls] == [f"$.raw_intervention_rows[{index}]" for index in range(len(rows))]
    assert {control.status for control in controls} <= {"pass", "fail"}


def test_hardgates_use_rows_and_controls_without_dgt_authority():
    rows = collect_rows(DEFAULT_CONFIG)
    controls = collect_margin_proxy_controls(rows)
    hardgates = evaluate_layer_hardgates(rows, controls)
    payload = build_payload(rows, controls, hardgates, DgtDeclaration(), generated_at="fixture", config=DEFAULT_CONFIG)

    assert hardgates["status"] == "pass"
    assert payload["dgt_declaration"]["produces_dgt"] is False
    assert payload["dgt_declaration"]["discovery_map_authority"] is False
    assert payload["dgt_declaration"]["claim_graph_authority"] is False
    assert payload["dgt_declaration"]["non_authoritative_admission"] is True
    assert payload["hardgate"]["status"] == "pass"
    assert payload["failed_gate"] is None
    assert payload["discovery_map_admission"]["admitted"] is False
    assert payload["mechanism_claim_allowed"]["allowed"] is False
    assert payload["bounded_lab_evidence"]["raw_row_pointer"] == RAW_ROW_POINTER
    assert payload["forbidden_claim_term_audit"]["status"] == "pass"
    assert payload["source_artifacts"]["raw_rows"] == RAW_ROW_POINTER
    assert payload["source_artifacts"]["attention_route_report"] == ATTENTION_ROUTE_ARTIFACT
    assert payload["source_artifacts"]["layerwise_jet_map"] == LAYERWISE_JET_MAP_ARTIFACT
    assert payload["layerwise_derivative_rows"]["schema"] == "LayerwiseDerivativeRow"
    assert "dgt_relation" not in json.dumps(payload, sort_keys=True)


def test_hardgates_fail_when_layer_derivative_mean_is_below_threshold():
    rows = [
        replace(row, derivative_estimate=0.0) if row.layer_index == 0 else row
        for row in collect_rows(DEFAULT_CONFIG)
    ]
    controls = collect_margin_proxy_controls(rows)

    hardgates = evaluate_layer_hardgates(rows, controls)

    assert hardgates["status"] == "fail"
    assert hardgates["by_layer"]["layer_0"]["derivative_status"] == "fail"
    assert "layer_0" in hardgates["failed_layers"]


def test_hardgates_fail_when_layer_controls_are_missing():
    rows = collect_rows(DEFAULT_CONFIG)
    controls = [
        control
        for control in collect_margin_proxy_controls(rows)
        if control.layer_index != 1
    ]

    hardgates = evaluate_layer_hardgates(rows, controls)

    assert hardgates["status"] == "fail"
    assert hardgates["by_layer"]["layer_1"]["control_status"] == "fail"
    assert "layer_1" in hardgates["failed_layers"]


def test_hardgates_fail_when_layer_control_margins_are_below_threshold():
    rows = collect_rows(DEFAULT_CONFIG)
    controls = [
        replace(control, control_margin=0.0, status="fail") if control.layer_index == 2 else control
        for control in collect_margin_proxy_controls(rows)
    ]

    hardgates = evaluate_layer_hardgates(rows, controls)

    assert hardgates["status"] == "fail"
    assert hardgates["by_layer"]["layer_2"]["control_status"] == "fail"
    assert "layer_2" in hardgates["failed_layers"]


def test_payload_projects_failed_hardgates_to_evidence_status_and_failed_gate():
    rows = [
        replace(row, derivative_estimate=0.0) if row.layer_index == 0 else row
        for row in collect_rows(DEFAULT_CONFIG)
    ]
    controls = collect_margin_proxy_controls(rows)
    hardgates = evaluate_layer_hardgates(rows, controls)

    payload = build_payload(rows, controls, hardgates, DgtDeclaration(), generated_at="fixture", config=DEFAULT_CONFIG)

    assert payload["bounded_lab_evidence"]["status"] == "fail"
    assert payload["failed_gate"] == "layer_0"

    fallback_hardgates = dict(hardgates)
    fallback_hardgates["failed_layers"] = []
    fallback_payload = build_payload(
        rows,
        controls,
        fallback_hardgates,
        DgtDeclaration(),
        generated_at="fixture",
        config=DEFAULT_CONFIG,
    )

    assert fallback_payload["bounded_lab_evidence"]["status"] == "fail"
    assert fallback_payload["failed_gate"] == "hardgates"


def test_reports_are_derived_from_raw_row_pointers():
    payload = TransformerDerivativeAtlasProjection(config=DEFAULT_CONFIG, generated_at="fixture").project()
    route_report = render_attention_route_report(payload)
    jet_map = render_layerwise_jet_map(payload)

    assert route_report["status"] == "pass"
    assert route_report["source_artifacts"]["raw_rows"] == RAW_ROW_POINTER
    assert route_report["route_rows"]
    assert all(row["raw_rows_pointer"] == RAW_ROW_POINTER for row in route_report["route_rows"])
    assert "reports/canonical/transformer_derivative_atlas.json:$.layer_summary.by_layer.layer_0" in jet_map


def test_runner_writes_three_canonical_artifacts(tmp_path):
    payload = runner.build_projection(generated_at="fixture")
    runner.write_artifacts(payload, root=tmp_path)

    atlas = tmp_path / runner.JSON_ARTIFACT
    route = tmp_path / ATTENTION_ROUTE_ARTIFACT
    jet_map = tmp_path / runner.REPORT_ARTIFACT
    assert atlas.exists()
    assert route.exists()
    assert jet_map.exists()
    atlas_payload = json.loads(atlas.read_text(encoding="utf-8"))
    assert atlas_payload["mechanism_claim_allowed"]["allowed"] is False
    assert atlas_payload["discovery_map_admission"]["admitted"] is False
    assert atlas_payload["hardgates"]["status"] == "pass"
    assert json.loads(route.read_text(encoding="utf-8"))["source_artifacts"]["raw_rows"] == RAW_ROW_POINTER
    assert "# Layerwise Jet Map" in jet_map.read_text(encoding="utf-8")

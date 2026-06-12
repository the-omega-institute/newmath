import json

import pytest

import bedc_quality_lab
from bedc_quality_lab.schema import SCHEMA_ID
from scripts import run_canonical_reports as canonical
from scripts import run_dimension_mismatch_transfer_robustness as runner


def _stat(mean, low, high):
    return {
        "mean": float(mean),
        "ci95_low": float(low),
        "ci95_high": float(high),
        "ci95_half_width": float((high - low) / 2.0),
        "n": 4,
        "std": 0.0,
    }


def _source_payload(status="pass"):
    allowlist = list(runner.transfer.H_ONLY_REPRESENTATION_SUMMARY_COLUMNS)
    family_pointers = {
        family: f"$.arms[{index}]"
        for index, family in enumerate(runner.CONTROL_FAMILY_ORDER)
    }
    return {
        "artifact_id": runner.transfer.ARTIFACT_ID,
        "status": "pointer-only",
        "dimension_mismatch_debt_transfer": {
            "status": status,
            "status_code": "scoped-d4-boundary" if status == "pass" else "failed-boundary",
            "scope": "encoder_dim grid against producer reference latent dimension",
            "base_level": "D4",
            "anti_triviality_status": "scale_leakage_detected",
            "effective_level": "DN",
            "downgrade_reason": "scale_only_or_metadata_proxy_sufficient",
            "terminal_verdict": "negative_discovery",
            "discovery_level": "DN",
            "anti_triviality_evidence": {
                "controlled_geometry": {
                    "control_family_coverage": {
                        "status": "pass",
                        "resolved_families": list(runner.CONTROL_FAMILY_ORDER),
                        "family_pointers": family_pointers,
                    }
                }
            },
        },
        "control_protocol": {
            "control_arm": "matched_random_gap_head",
            "same_feature_columns_as_treatment": True,
            "same_train_eval_split_as_treatment": True,
            "same_metric_helper_as_treatment": True,
            "same_budget_as_treatment": True,
            "fold_count": 4,
        },
        "metrics": {
            "by_arm": {
                "vanilla": {"failure_detection_auroc": _stat(0.5, 0.5, 0.5)},
            },
        },
        "hardgate_evidence": {
            "HG-B3": {
                "status": "pass",
                "learned_auroc": _stat(0.9, 0.82, 0.98),
                "matched_random_auroc": _stat(0.52, 0.45, 0.58),
                "learned_minus_matched_random_auroc": _stat(0.38, 0.24, 0.52),
                "matched_random_positive": False,
            },
            "HG-B4": {
                "status": "pass",
                "audit": {
                    "status": "pass",
                    "declared_h_only_allowlist": allowlist,
                    "actual_model_input_columns": allowlist,
                    "actual_model_input_width": len(allowlist),
                    "declared_h_only_width": len(allowlist),
                    "forbidden_present": [],
                },
            },
            "HG-B5": {
                "status": "pass",
                "audit": {
                    "status": "pass",
                    "hits": [],
                    "forbidden_positive_claim_terms": list(runner.FORBIDDEN_POSITIVE_CLAIM_TERMS),
                },
            },
        },
        "boundary_ledger": {
            "status": "recorded",
            "projection": "DN",
            "failed_gates": [],
            "d5_shortcut": False,
        },
        "not_claimed": [
            "no global quality conclusion",
            "no full LeJEPA conclusion",
            "no claim outside the listed encoder_dim-grid debt-transfer surface",
        ],
    }


def _discovery_map_payload(level="DN", *, d5=False):
    row = {
        "report": "dimension-mismatch-debt-transfer",
        "json_artifact": runner.SOURCE_ARTIFACT,
        "markdown_artifact": runner.transfer.REPORT_ARTIFACT,
        "discovery_level": level,
        "projection_status": "projected",
        "evidence_pointer": "$.dimension_mismatch_debt_transfer.effective_level",
        "audit_status": "valid",
        "audit_reason": "",
        "negative_report_pointer": "reports/canonical/negative_discovery_reports.json:$.rows[0]",
    }
    if d5:
        row["d5_readiness"] = {"shortcut": {"status": "pass"}}
    return {
        "schema_id": "bedc-quality-lab:canonical-discovery-map",
        "artifact_id": "bedc-quality-lab:discovery-map",
        "rows": [row],
    }


def _negative_reports_payload(*, include_mapping=True):
    row = {
        "negative_id": "dn:dimension-mismatch-scale-leakage",
        "report_id": "dimension-mismatch-scale-leakage",
        "claim_id": "claim:dimension-mismatch-debt-transfer",
        "kind": "discovery_report",
        "report": "dimension-mismatch-debt-transfer",
        "source": f"{runner.SOURCE_ARTIFACT}:$.dimension_mismatch_debt_transfer.anti_triviality_status",
        "json_artifact": runner.SOURCE_ARTIFACT,
        "markdown_artifact": runner.transfer.REPORT_ARTIFACT,
        "ledger_pointer": f"{runner.SOURCE_ARTIFACT}:$.dimension_mismatch_debt_transfer.anti_triviality_status",
        "discovery_level": "DN",
        "base_level": "D4",
        "anti_triviality_status": "scale_leakage_detected",
        "effective_level": "DN",
        "downgrade_reason": "scale_only_or_metadata_proxy_sufficient",
        "terminal_verdict": "negative_discovery",
        "classifier_reasons": ["verdict=rejected"],
        "projection_status": "projected",
        "evidence_pointer": "$.dimension_mismatch_debt_transfer.effective_level",
        "failed_gate": "$.dimension_mismatch_debt_transfer.anti_triviality_status",
        "debt_row_pointer": None,
        "audit_status": "pass",
        "audit_reason": "",
        "what_was_learned": "fixture learned",
        "next_hypothesis": "fixture next hypothesis",
    }
    if include_mapping:
        row["bedc_gap_mapping"] = {
            "witness_pointer": runner.transfer.SCALE_LEAKAGE_WITNESS_POINTER,
            "bedc_gap_field": "representation_scale_leakage",
            "demotion_rule": "demote_to_DN_or_D1",
            "regression_test": runner.transfer.NEGATIVE_WITNESS_TEST_POINTER,
        }
    return {
        "schema_id": "bedc-quality-lab:negative-discovery-reports",
        "artifact_id": "bedc-quality-lab:negative-discovery-reports",
        "rows": [row],
    }


def _write_inputs(tmp_path, source=None, discovery=None):
    source_payload = _source_payload() if source is None else source
    discovery_payload = _discovery_map_payload() if discovery is None else discovery
    source_path = tmp_path / runner.SOURCE_ARTIFACT
    discovery_path = tmp_path / runner.DISCOVERY_MAP_ARTIFACT
    negative_path = tmp_path / "reports/canonical/negative_discovery_reports.json"
    sidecar_path = tmp_path / runner.ANTI_TRIVIALITY_ARTIFACT
    source_path.parent.mkdir(parents=True, exist_ok=True)
    source_path.write_text(json.dumps(source_payload), encoding="utf-8")
    discovery_path.write_text(json.dumps(discovery_payload), encoding="utf-8")
    negative_path.write_text(json.dumps(_negative_reports_payload()), encoding="utf-8")
    family_pointers = {
        family: f"$.arms[{index}]"
        for index, family in enumerate(runner.CONTROL_FAMILY_ORDER)
    }
    sidecar_path.parent.mkdir(parents=True, exist_ok=True)
    sidecar_path.write_text(
        json.dumps(
            {
                "arms": [{"arm": family} for family in runner.CONTROL_FAMILY_ORDER],
                "controlled_geometry": {
                    "control_family_coverage": {
                        "status": "pass",
                        "required_families": list(runner.CONTROL_FAMILY_ORDER),
                        "observed_families": list(runner.CONTROL_FAMILY_ORDER),
                        "family_pointers": family_pointers,
                    }
                },
            }
        ),
        encoding="utf-8",
    )


def _check(payload, name):
    return next(row for row in payload["robust_control_checks"] if row["check"] == name)


@pytest.mark.parametrize(
    "mutate",
    [
        lambda payload: payload["dimension_mismatch_debt_transfer"].update({"status": "failed"}),
        lambda payload: payload.update({"not_claimed": ["stub"]}),
        lambda payload: payload["hardgate_evidence"]["HG-B3"].pop("matched_random_auroc"),
        lambda payload: payload["hardgate_evidence"]["HG-B3"].update({"matched_random_positive": True}),
        lambda payload: payload["hardgate_evidence"]["HG-B3"]["learned_auroc"].update({"ci95_low": 0.50}),
    ],
)
def test_source_integrity_fails_closed(tmp_path, mutate):
    source = _source_payload()
    mutate(source)
    _write_inputs(tmp_path, source=source)

    payload = runner.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["status"] == "fail"
    assert _check(payload, "HG-DM-R1")["verdict"] == "fail"
    assert "HG-DM-R1" in payload["failed_or_deferred_gates"]


def test_malformed_source_json_fails_closed(tmp_path):
    _write_inputs(tmp_path)
    source_path = tmp_path / runner.SOURCE_ARTIFACT
    source_path.write_text("{", encoding="utf-8")

    payload = runner.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["status"] == "fail"
    assert _check(payload, "HG-DM-R1")["verdict"] == "fail"
    assert _check(payload, "HG-DM-R1")["reason"] == runner.MALFORMED_SOURCE_REASON
    assert "HG-DM-R1" in payload["failed_or_deferred_gates"]
    assert "d5_readiness" not in payload


@pytest.mark.parametrize("source_payload", [[], 1])
def test_non_object_source_json_fails_closed(tmp_path, source_payload):
    _write_inputs(tmp_path)
    source_path = tmp_path / runner.SOURCE_ARTIFACT
    source_path.write_text(json.dumps(source_payload), encoding="utf-8")

    payload = runner.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["status"] == "fail"
    assert _check(payload, "HG-DM-R1")["verdict"] == "fail"
    assert _check(payload, "HG-DM-R1")["reason"] == runner.MALFORMED_SOURCE_REASON
    assert "HG-DM-R1" in payload["failed_or_deferred_gates"]
    assert "d5_readiness" not in payload


def test_resampling_stability_defers_on_nonpositive_delta(tmp_path):
    source = _source_payload()
    source["hardgate_evidence"]["HG-B3"]["learned_minus_matched_random_auroc"]["ci95_low"] = 0.0
    _write_inputs(tmp_path, source=source)

    payload = runner.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["status"] == "defer"
    assert _check(payload, "HG-DM-R2")["verdict"] == "defer"


@pytest.mark.parametrize(
    "mutate",
    [
        lambda payload: payload["hardgate_evidence"]["HG-B3"].update({"matched_random_positive": True}),
        lambda payload: payload["metrics"]["by_arm"].pop("vanilla"),
        lambda payload: payload["control_protocol"].update({"same_metric_helper_as_treatment": False}),
    ],
)
def test_control_symmetry_fail_closed(tmp_path, mutate):
    source = _source_payload()
    mutate(source)
    _write_inputs(tmp_path, source=source)

    payload = runner.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["status"] == "fail"
    assert _check(payload, "HG-DM-R3")["verdict"] == "fail"


def test_h_only_boundary_fails_on_forbidden_column(tmp_path):
    source = _source_payload()
    audit = source["hardgate_evidence"]["HG-B4"]["audit"]
    audit["actual_model_input_columns"] = list(audit["actual_model_input_columns"]) + ["encoder_dim"]
    audit["forbidden_present"] = ["encoder_dim"]
    _write_inputs(tmp_path, source=source)

    payload = runner.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["status"] == "fail"
    assert _check(payload, "HG-DM-R4")["verdict"] == "fail"


@pytest.mark.parametrize(
    "mutate",
    [
        lambda payload: payload["dimension_mismatch_debt_transfer"].update({"scope": "global-quality claim"}),
        lambda payload: payload["boundary_ledger"].update({"total_score": 1.0}),
        lambda payload: payload["hardgate_evidence"]["HG-B5"]["audit"].update({"hits": ["global-quality"]}),
    ],
)
def test_claim_boundary_fails_on_forbidden_term_or_score(tmp_path, mutate):
    source = _source_payload()
    mutate(source)
    _write_inputs(tmp_path, source=source)

    payload = runner.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["status"] == "fail"
    assert _check(payload, "HG-DM-R5")["verdict"] == "fail"


def test_real_pass_shape_stays_pointer_only_and_does_not_promote_d5(tmp_path):
    _write_inputs(tmp_path)

    payload = runner.write_dimension_mismatch_transfer_robustness(root=tmp_path, generated_at="fixture-time")
    persisted = json.loads((tmp_path / runner.JSON_ARTIFACT).read_text(encoding="utf-8"))
    discovery = json.loads((tmp_path / runner.DISCOVERY_MAP_ARTIFACT).read_text(encoding="utf-8"))
    row = discovery["rows"][0]

    assert payload["status"] == "pass"
    assert persisted["artifact_id"] == runner.ARTIFACT_ID
    assert persisted["source_pointer"] == f"{runner.SOURCE_ARTIFACT}:{runner.SOURCE_STATUS_POINTER}"
    assert all(check["verdict"] == "pass" for check in persisted["robust_control_checks"])
    assert _check(payload, "HG-DM-R6")["verdict"] == "pass"
    assert "terminal DN downgrade" in persisted["readiness_boundary"]
    assert "not a D5 upgrade" in persisted["readiness_boundary"]
    assert "d5_readiness" not in persisted
    assert row["discovery_level"] == "DN"
    assert row["negative_report_pointer"] == "reports/canonical/negative_discovery_reports.json:$.rows[0]"
    assert not {
        "base_level",
        "anti_triviality_status",
        "effective_level",
        "terminal_verdict",
        "failed_gate",
        "bedc_gap_mapping",
    } & set(row)
    assert "d5_readiness" not in row
    assert "score" not in json.dumps(persisted["robust_control_checks"]).lower()


def test_hg_dm_r6_fails_when_sidecar_family_pointer_does_not_resolve(tmp_path):
    _write_inputs(tmp_path)
    sidecar_path = tmp_path / runner.ANTI_TRIVIALITY_ARTIFACT
    sidecar = json.loads(sidecar_path.read_text(encoding="utf-8"))
    sidecar["controlled_geometry"]["control_family_coverage"]["family_pointers"]["rank_proxy_diagnostic"] = "$.missing"
    sidecar_path.write_text(json.dumps(sidecar), encoding="utf-8")

    payload = runner.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["status"] == "fail"
    assert _check(payload, "HG-DM-R6")["verdict"] == "fail"
    assert "HG-DM-R6" in payload["failed_or_deferred_gates"]


def test_hg_dm_r6_fails_when_folded_source_coverage_is_inconsistent(tmp_path):
    source = _source_payload()
    source["dimension_mismatch_debt_transfer"]["anti_triviality_evidence"]["controlled_geometry"]["control_family_coverage"][
        "resolved_families"
    ] = list(runner.CONTROL_FAMILY_ORDER[:-1])
    _write_inputs(tmp_path, source=source)

    payload = runner.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["status"] == "fail"
    assert _check(payload, "HG-DM-R6")["verdict"] == "fail"


def test_discovery_map_pointer_only_row_fails_when_owner_lacks_mapping(tmp_path):
    _write_inputs(tmp_path)
    negative_path = tmp_path / "reports/canonical/negative_discovery_reports.json"
    negative_path.write_text(json.dumps(_negative_reports_payload(include_mapping=False)), encoding="utf-8")

    payload = runner.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["status"] == "fail"
    assert payload["audit_status"] == "fail"
    assert "dimension-mismatch negative report lacks bedc_gap_mapping" in payload["audit_reasons"]


def test_discovery_map_row_copying_owner_facts_fails_schema_validation():
    from bedc_quality_lab.discovery_compiler.map import DiscoveryMapRow

    row = {
        **_discovery_map_payload()["rows"][0],
        "base_level": "D4",
        "bedc_gap_mapping": {},
    }

    with pytest.raises(ValueError, match="copies owner facts"):
        DiscoveryMapRow.from_mapping(row)


def test_discovery_map_d5_shortcut_fails_audit_without_changing_artifact(tmp_path):
    _write_inputs(tmp_path, discovery=_discovery_map_payload(d5=True))

    payload = runner.build_payload(root=tmp_path, generated_at="fixture-time")

    assert payload["status"] == "fail"
    assert payload["audit_status"] == "fail"
    assert "discovery-map-boundary" in payload["failed_or_deferred_gates"]


def test_index_section_exists_and_artifact_stays_out_of_canonical_reports(tmp_path, monkeypatch):
    _write_inputs(tmp_path)
    runner.write_dimension_mismatch_transfer_robustness(root=tmp_path, generated_at="fixture-time")
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")

    section = canonical._dimension_mismatch_transfer_robustness_index_section()

    assert section["status"] == "pass"
    assert section["artifact_id"] == runner.ARTIFACT_ID
    assert section["json_artifact"] == runner.JSON_ARTIFACT
    assert all(spec.json_artifact != runner.JSON_ARTIFACT for spec in canonical.CANONICAL_REPORTS)


def test_schema_id_and_package_all_stay_unchanged():
    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]

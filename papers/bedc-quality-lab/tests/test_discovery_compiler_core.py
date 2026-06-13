import json
from pathlib import Path
from typing import Any, Mapping, Sequence

import pytest

from bedc_quality_lab.backends.current_lab.adapter import CurrentLabBackendEvidenceAdapter
from bedc_quality_lab.discovery_compiler.backend import BackendEvidenceAdapter, TheoryBackend
from bedc_quality_lab.discovery_compiler.capsule import ClaimCapsule, build_claim_capsule_payload
from bedc_quality_lab.discovery_compiler.compiler import compile_discovery
from bedc_quality_lab.discovery_compiler.anti_triviality import owner_local_anti_triviality_contract
from bedc_quality_lab.discovery_compiler.map import (
    DiscoveryMapRow,
    build_discovery_map_payload,
    owner_anti_triviality_check,
)
from bedc_quality_lab.evidence_provenance import evidence_provenance_pointer_for_report
from bedc_quality_lab.evidence_provenance import OWNER as EVIDENCE_PROVENANCE_OWNER
from bedc_quality_lab.evidence_provenance import SCHEMA_ID as EVIDENCE_PROVENANCE_SCHEMA_ID
from bedc_quality_lab.discovery_compiler.negative_reports import (
    JSON_ARTIFACT as NEGATIVE_REPORTS_ARTIFACT,
    validate_negative_report_row,
)
from bedc_quality_lab.discovery_compiler.projection import project_finite_discovery_gate
from scripts import run_dimension_mismatch_debt_transfer as transfer


def _owner_cells(report: str, evidence_type: str) -> dict[str, str]:
    return {
        "evidence_type": evidence_type,
        "evidence_provenance_pointer": evidence_provenance_pointer_for_report(report),
    }


def _evidence_owner_row(report: str) -> dict[str, Any]:
    return {
        "report": report,
        "evidence_type": "boundary_negative",
        "discovery_map_pointer": None,
        "metric_provenance_pointers": [],
        "producer_training_audit_pointer": None,
        "allowed_claim_kinds": ["negative_boundary"],
        "not_claimed": ["fixture owner row"],
    }


def _write_evidence_provenance_owner(root: Path) -> None:
    rows = [_evidence_owner_row("fixture-report"), _evidence_owner_row("dimension-mismatch-debt-transfer")]
    payload = {
        "schema_id": EVIDENCE_PROVENANCE_SCHEMA_ID,
        "owner": EVIDENCE_PROVENANCE_OWNER,
        "generated_at": "fixture-time",
        "producer_audits": [],
        "metric_rows": [],
        "discovery_rows": rows,
        "discovery_rows_by_report": {str(row["report"]): row for row in rows},
        "hardgate_status": {},
        "artifact_pointers": {
            "owner_pointer": "reports/canonical/index.json:$.evidence_provenance",
            "discovery_map_rows": "reports/canonical/discovery_map.json:$.rows",
        },
    }
    path = root / "reports" / "canonical" / "index.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"evidence_provenance": payload}) + "\n", encoding="utf-8")


class FakeAdapter:
    backend = TheoryBackend(
        name="fixture-backend",
        scope_kind="fixture-scope",
        assumptions=("fixture artifacts are JSON objects",),
        metrics=("discovery_level", "audit_status"),
        theorem_rows=(),
        ledger_rows=(),
        hardgates=(),
        not_claimed=("fixture boundary",),
    )

    def __init__(self) -> None:
        self.calls: list[str] = []

    def build_source_spec(self) -> Mapping[str, Any]:
        return {"source": "fixture"}

    def build_pattern_spec(self) -> Mapping[str, Any]:
        return {"status": "pointer-only"}

    def build_classifier_spec(self) -> Mapping[str, Any]:
        return {"levels": ["DN"]}

    def compute_metrics(self, *, root: Path, generated_at: str | None = None) -> Mapping[str, Any]:
        self.calls.append("map")
        required = (
            "certificate-guided-training",
            "gap-head-ablation",
            "spectral-ablation-hinge",
            "dimension-mismatch-scale-leakage",
            "single-threshold-escape",
            "training-choice-observability",
            "gap-head-mechanism-blockage",
        )
        payload = {
            "schema_id": "fixture-map",
            "generated_at": generated_at,
            "rows": [
                {
                    "report": "fixture-report" if report_id != "dimension-mismatch-scale-leakage" else "dimension-mismatch-debt-transfer",
                    "json_artifact": "reports/canonical/fixture.json"
                    if report_id != "dimension-mismatch-scale-leakage"
                    else transfer.JSON_ARTIFACT,
                    "markdown_artifact": "reports/canonical/fixture.md"
                    if report_id != "dimension-mismatch-scale-leakage"
                    else transfer.REPORT_ARTIFACT,
                    "discovery_level": "DN",
                    "projection_status": "projected",
                    "evidence_pointer": "$.failed"
                    if report_id != "dimension-mismatch-scale-leakage"
                    else "$.dimension_mismatch_debt_transfer.anti_triviality_status",
                    "audit_status": "valid",
                    "audit_reason": "",
                    "negative_report_pointer": f"{NEGATIVE_REPORTS_ARTIFACT}:$.rows[{index}]",
                    **_owner_cells(
                        "fixture-report" if report_id != "dimension-mismatch-scale-leakage" else "dimension-mismatch-debt-transfer",
                        "boundary_negative",
                    ),
                }
                for index, report_id in enumerate(required)
            ],
        }
        (root / "reports" / "canonical").mkdir(parents=True, exist_ok=True)
        (root / "reports" / "canonical" / "discovery_map.json").write_text(json.dumps(payload) + "\n", encoding="utf-8")
        return payload

    def derive_ledger_rows(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        return self.compute_metrics(root=root, generated_at=generated_at)["rows"]

    def derive_negative_discovery_rows(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        self.calls.append("negative")
        required = (
            "certificate-guided-training",
            "gap-head-ablation",
            "spectral-ablation-hinge",
            "dimension-mismatch-scale-leakage",
            "single-threshold-escape",
            "training-choice-observability",
            "gap-head-mechanism-blockage",
        )
        return [
            {
                "negative_id": f"dn:{report_id}",
                "report_id": report_id,
                "kind": "discovery_report",
                "report": "fixture-report" if report_id != "dimension-mismatch-scale-leakage" else "dimension-mismatch-debt-transfer",
                "claim_id": "claim:fixture-report" if report_id != "dimension-mismatch-scale-leakage" else "claim:dimension-mismatch-debt-transfer",
                "source": "reports/canonical/fixture.json:$.failed"
                if report_id != "dimension-mismatch-scale-leakage"
                else f"{transfer.JSON_ARTIFACT}:$.dimension_mismatch_debt_transfer.anti_triviality_status",
                "json_artifact": "reports/canonical/fixture.json"
                if report_id != "dimension-mismatch-scale-leakage"
                else transfer.JSON_ARTIFACT,
                "markdown_artifact": "reports/canonical/fixture.md"
                if report_id != "dimension-mismatch-scale-leakage"
                else transfer.REPORT_ARTIFACT,
                "ledger_pointer": "reports/canonical/fixture.json:$.failed"
                if report_id != "dimension-mismatch-scale-leakage"
                else f"{transfer.JSON_ARTIFACT}:$.dimension_mismatch_debt_transfer.anti_triviality_status",
                "discovery_level": "DN",
                "terminal_verdict": "negative_discovery",
                "classifier_reasons": ["fixture", "verdict=rejected"]
                if report_id == "dimension-mismatch-scale-leakage"
                else ["fixture"],
                "projection_status": "projected",
                "evidence_pointer": "$.failed",
                "failed_gate": "$.failed"
                if report_id != "dimension-mismatch-scale-leakage"
                else "$.dimension_mismatch_debt_transfer.anti_triviality_status",
                "base_level": "D4" if report_id == "dimension-mismatch-scale-leakage" else None,
                "anti_triviality_status": "scale_leakage_detected"
                if report_id == "dimension-mismatch-scale-leakage"
                else None,
                "effective_level": "DN" if report_id == "dimension-mismatch-scale-leakage" else None,
                "what_was_learned": "fixture learned",
                "next_hypothesis": "fixture next hypothesis",
                "debt_row_pointer": None,
                "audit_status": "pass",
                "audit_reason": "",
                **(
                    {
                        "bedc_gap_mapping": transfer.scale_leakage_bedc_gap_mapping(root)
                    }
                    if report_id == "dimension-mismatch-scale-leakage"
                    else {}
                ),
            }
            for report_id in required
        ]

    def project_discovery_level(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        return self.derive_ledger_rows(root=root, generated_at=generated_at)


def _write_fixture_sources(root: Path) -> None:
    canonical = root / "reports" / "canonical"
    canonical.mkdir(parents=True, exist_ok=True)
    _write_evidence_provenance_owner(root)
    (canonical / "fixture.json").write_text(json.dumps({"failed": True}) + "\n", encoding="utf-8")
    (canonical / "dimension-mismatch-debt-transfer.json").write_text(
        json.dumps(
            {
                "dimension_mismatch_debt_transfer": {
                    "anti_triviality_status": "scale_leakage_detected",
                }
            }
        )
        + "\n",
        encoding="utf-8",
    )
    (canonical / "discovery_negative_witnesses.json").write_text(
        json.dumps({"status": "pointer-only", "expected_kind_count": 0, "witnesses": []}) + "\n",
        encoding="utf-8",
    )
    (canonical / "claim_verdicts.jsonl").write_text("", encoding="utf-8")
    path = root / "reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "run_local": {
                    "negative_witness": [
                        {
                            "witness_id": "scale_leakage_witness",
                            "source_artifact": transfer.ANTI_TRIVIALITY_ARTIFACT,
                            "source_pointer": "$.status",
                            "bedc_gap_field": "representation_scale_leakage",
                            "demotion_rule": "demote_to_DN_or_D1",
                            "regression_test": "$.run_local.test_artifact.regression_tests.scale_leakage_witness",
                            "status": "valid",
                        }
                    ],
                    "test_artifact": {
                        "regression_tests": {
                            "scale_leakage_witness": (
                                "tests/test_dimension_mismatch_debt_transfer.py::"
                                "test_scale_leakage_sidecar_maps_to_first_negative_witness"
                            )
                        }
                    },
                }
            }
        )
        + "\n",
        encoding="utf-8",
    )
    anti_triviality = root / transfer.ANTI_TRIVIALITY_ARTIFACT
    anti_triviality.parent.mkdir(parents=True, exist_ok=True)
    anti_triviality.write_text(json.dumps({"status": "scale_leakage_detected"}) + "\n", encoding="utf-8")


def test_backend_contract_and_current_lab_adapter_metadata():
    adapter: BackendEvidenceAdapter = CurrentLabBackendEvidenceAdapter()

    assert adapter.backend.name == "current-lab"
    assert adapter.build_pattern_spec()["status"] == "pointer-only"
    assert "terminal_verdict" not in adapter.backend.metrics
    assert adapter.build_source_spec()["canonical_reports"]


def test_claim_capsule_validates_required_cells():
    finite_gate = {
        "status": "pass",
        "counts": {"positive": 1, "negative": 2, "revocation": 0},
        "pointers": {
            "positive": ["reports/canonical/positive.json:$.rows[0]"],
            "negative": [["dn:fixture", "reports/canonical/negative.json:$.rows[0]", "", "", ""]],
            "revocation": [],
        },
        "not_claimed": ["finite gate checks finite evidence-set structure, not model-result correctness"],
    }
    payload = build_claim_capsule_payload(
        generated_at="fixture-time",
        claim_id="claim:fixture",
        report="fixture-report",
        source_artifact="reports/canonical/dimension-mismatch-debt-transfer.json",
        source_pointer="$.dimension_mismatch_debt_transfer",
        claim={
            "base_level": "D4",
            "anti_triviality_status": "scale_leakage_detected",
            "effective_level": "DN",
            "downgrade_reason": "scale_only_or_metadata_proxy_sufficient",
            "terminal_verdict": "negative_discovery",
            "hypothesis": "fixture hypothesis",
            "failed_gate": "$.dimension_mismatch_debt_transfer.anti_triviality_status",
            "what_was_learned": "fixture learned",
        },
        finite_gate=finite_gate,
    )

    capsule = ClaimCapsule.from_payload(payload)

    assert capsule.claim_id == "claim:fixture"
    assert capsule.status == "complete"
    assert payload["finite_gate"] == {
        "status": "pass",
        "counts": {"positive": 1, "negative": 2, "revocation": 0},
        "not_claimed": ["finite gate checks finite evidence-set structure, not model-result correctness"],
        "pointer_count_parity": {"positive": True, "negative": False, "revocation": True},
    }
    assert "what_was_learned" not in payload["finite_gate"]
    with pytest.raises(ValueError, match="schema_id"):
        ClaimCapsule.from_payload({**payload, "schema_id": "wrong"})


def test_claim_capsule_payload_preserves_run_local_contract():
    run_local = {
        "projection_kind": "fixture_run_local",
        "owner": "claim:fixture",
        "artifact_bundle": {
            "claim_capsule": "reports/runs/fixture/claim_capsule.json",
            "raw_metrics": "reports/runs/fixture/raw_metrics.jsonl",
            "summary": "reports/runs/fixture/summary.json",
            "report": "reports/runs/fixture/report.md",
        },
        "evidence_refs": [
            {
                "evidence_id": "fixture-evidence",
                "source_artifact": "reports/canonical/fixture.json",
                "source_pointer": "$.failed",
            }
        ],
    }
    payload = build_claim_capsule_payload(
        generated_at="fixture-time",
        claim_id="claim:fixture",
        report="fixture-report",
        source_artifact="reports/canonical/dimension-mismatch-debt-transfer.json",
        source_pointer="$.dimension_mismatch_debt_transfer",
        claim={
            "base_level": "D4",
            "anti_triviality_status": "scale_leakage_detected",
            "effective_level": "DN",
            "downgrade_reason": "scale_only_or_metadata_proxy_sufficient",
            "terminal_verdict": "negative_discovery",
            "hypothesis": "fixture hypothesis",
            "failed_gate": "$.dimension_mismatch_debt_transfer.anti_triviality_status",
            "what_was_learned": "fixture learned",
        },
        run_local=run_local,
    )

    capsule = ClaimCapsule.from_payload(payload)

    assert capsule.payload["run_local"] == run_local


def test_discovery_map_row_rejects_dn_fact_cells_and_accepts_pointer_only():
    row = {
        "report": "fixture-report",
        "json_artifact": "reports/canonical/fixture.json",
        "markdown_artifact": "reports/canonical/fixture.md",
        "discovery_level": "DN",
        "projection_status": "projected",
        "evidence_pointer": "$.failed",
        "audit_status": "valid",
        "audit_reason": "",
        "negative_report_pointer": f"{NEGATIVE_REPORTS_ARTIFACT}:$.rows[0]",
        **_owner_cells("fixture-report", "boundary_negative"),
    }

    assert DiscoveryMapRow.from_mapping(row).negative_report_pointer == f"{NEGATIVE_REPORTS_ARTIFACT}:$.rows[0]"
    with pytest.raises(ValueError, match="copies owner facts"):
        DiscoveryMapRow.from_mapping({**row, "terminal_verdict": "negative_discovery"})


def test_derivative_negative_report_shape_requires_resolvable_debt_pointer(tmp_path):
    artifact = tmp_path / "reports" / "canonical" / "transformer_derivative_atlas.json"
    artifact.parent.mkdir(parents=True, exist_ok=True)
    artifact.write_text(
        json.dumps(
            {
                "hardgates": {"by_layer": {"layer_0": {"status": "fail"}}},
                "ledger_gaps": [
                    {
                        "kind": "derivative",
                        "residue": "high-order-instability",
                        "status": "open",
                    }
                ],
            }
        )
        + "\n",
        encoding="utf-8",
    )
    row = {
        "report_id": "transformer-derivative-atlas",
        "report": "transformer-derivative-atlas",
        "json_artifact": "reports/canonical/transformer_derivative_atlas.json",
        "markdown_artifact": "reports/canonical/layerwise_jet_map.md",
        "source": "reports/canonical/transformer_derivative_atlas.json:$.hardgates.by_layer.layer_0.status",
        "ledger_pointer": "reports/canonical/transformer_derivative_atlas.json:$.ledger_gaps[0]",
        "discovery_level": "DN",
        "terminal_verdict": "negative_discovery",
        "classifier_reasons": ["verdict=rejected"],
        "projection_status": "projected",
        "evidence_pointer": "$.bounded_lab_evidence",
        "failed_gate": "$.hardgates.by_layer.layer_0.status",
        "debt_row_pointer": "$.ledger_gaps[0]",
        "what_was_learned": "derivative hardgate failure remains ordinary debt evidence",
        "next_hypothesis": "close high-order instability before claiming mechanism-level derivative evidence",
    }

    validated = validate_negative_report_row(tmp_path, row)

    assert validated["negative_id"] == "dn:transformer-derivative-atlas"
    assert validated["debt_row_pointer"] == "$.ledger_gaps[0]"
    with pytest.raises(ValueError, match="derivative DN report requires debt_row_pointer"):
        validate_negative_report_row(tmp_path, {key: value for key, value in row.items() if key != "debt_row_pointer"})


def test_build_discovery_map_payload_validates_rows():
    payload = build_discovery_map_payload(
        rows=[
            {
                "report": "positive-fixture",
                "json_artifact": "reports/canonical/positive.json",
                "markdown_artifact": "reports/canonical/positive.md",
                "discovery_level": "D4",
                "terminal_verdict": "",
                "projection_status": "projected",
                "evidence_pointer": "$.positive",
                "audit_status": "valid",
                "audit_reason": "",
                **_owner_cells("positive-fixture", "deterministic_projection"),
            }
        ],
        generated_at="fixture-time",
    )

    assert payload["row_count"] == 1
    assert payload["level_counts"]["D4"] == 1


def _positive_owner_payload(contract=None):
    payload = {
        "positive": True,
        "metadata": {"owner": "fixture"},
        "control": {"positive": False},
        "forbidden": {"status": "pass"},
    }
    payload.update(
        contract
        if contract is not None
        else {"anti_triviality_status": "pass"}
        | owner_local_anti_triviality_contract(
            recommended_level="D5-O",
            scale_only_pointer="$.positive",
            metadata_only_pointer="$.metadata",
            matched_random_pointer="$.control.positive",
            forbidden_column_pointer="$.forbidden.status",
        )
    )
    return payload


def _write_positive_owner(root: Path, payload: Mapping[str, Any]) -> None:
    path = root / "reports" / "canonical" / "positive.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload) + "\n", encoding="utf-8")


def _positive_row():
    return {
        "report": "positive-fixture",
        "json_artifact": "reports/canonical/positive.json",
        "markdown_artifact": "reports/canonical/positive.md",
        "discovery_level": "D5-O",
        "terminal_verdict": "",
        "projection_status": "projected",
        "evidence_pointer": "$.positive",
        "audit_status": "valid",
        "audit_reason": "",
        **_owner_cells("positive-fixture", "deterministic_projection"),
    }


def test_owner_anti_triviality_check_requires_four_resolvable_owner_gates(tmp_path):
    _write_positive_owner(tmp_path, _positive_owner_payload())

    ok, reason = owner_anti_triviality_check(
        tmp_path,
        "reports/canonical/positive.json:$.positive",
        accepted_level="D5-O",
    )
    payload = build_discovery_map_payload(rows=[_positive_row()], generated_at="fixture-time", root=tmp_path)

    assert ok is True
    assert reason == ""
    assert payload["rows"][0]["discovery_level"] == "D5-O"


@pytest.mark.parametrize(
    "mutate",
    [
        lambda payload: payload["anti_triviality_gate_evidence"].pop("metadata_only"),
        lambda payload: payload.update({"anti_triviality_policy": "fixture-policy"}),
        lambda payload: payload.update({"anti_triviality_recommended_level": "D4"}),
        lambda payload: payload["anti_triviality_gate_evidence"]["scale_only"].update({"pointer": "$.missing"}),
    ],
)
def test_positive_row_rejects_malformed_owner_anti_triviality_contract(tmp_path, mutate):
    payload = _positive_owner_payload()
    mutate(payload)
    _write_positive_owner(tmp_path, payload)

    ok, reason = owner_anti_triviality_check(
        tmp_path,
        "reports/canonical/positive.json:$.positive",
        accepted_level="D5-O",
    )

    assert ok is False
    assert reason == "anti-triviality-owner-contract-not-pass"
    with pytest.raises(ValueError, match="positive discovery map row lacks owner anti-triviality support"):
        build_discovery_map_payload(rows=[_positive_row()], generated_at="fixture-time", root=tmp_path)


def test_compile_discovery_writes_backend_negative_owner_before_map(tmp_path):
    _write_fixture_sources(tmp_path)
    adapter = FakeAdapter()

    result = compile_discovery(root=tmp_path, generated_at="fixture-time", adapter=adapter)

    assert adapter.calls == ["negative", "map"]
    assert result["negative_discovery_reports"]["rows"][0]["terminal_verdict"] == "negative_discovery"
    assert result["negative_discovery_reports"]["row_count"] == 7
    assert result["discovery_map"]["rows"][0]["negative_report_pointer"] == f"{NEGATIVE_REPORTS_ARTIFACT}:$.rows[0]"
    assert result["finite_gate"]["status"] == "fail"
    assert result["finite_gate"]["hardgates"]["FG-HG5"]["status"] == "pass"
    assert result["finite_gate"]["counts"]["negative"] == result["negative_witness_summary"]["row_count"]
    assert isinstance(result["finite_gate"]["pointers"]["negative"], list)
    assert "what_was_learned" not in json.dumps(result["finite_gate"], sort_keys=True)


def test_compile_discovery_architecture_mutation_drafts_are_opt_in_run_local(tmp_path):
    _write_fixture_sources(tmp_path)
    claim_capsule = tmp_path / "reports" / "canonical" / "claim_capsule.json"
    claim_capsule.write_text(json.dumps({"status": "complete"}) + "\n", encoding="utf-8")

    default_result = compile_discovery(root=tmp_path, generated_at="fixture-time", adapter=FakeAdapter())
    opt_in_result = compile_discovery(
        root=tmp_path,
        generated_at="fixture-time",
        adapter=FakeAdapter(),
        include_architecture_mutation_drafts=True,
    )

    assert "run_local" not in default_result
    drafts = opt_in_result["run_local"]["architecture_mutation_drafts"]
    assert drafts["schema_id"] == "bedc-quality-lab:architecture-mutation-draft-run-local"
    assert drafts["canonical_role"] == "run_local_not_in_CANONICAL_REPORTS"
    assert drafts["row_count"] > 0
    assert "what_was_learned" not in json.dumps(drafts, sort_keys=True)


def test_compile_discovery_finite_gate_is_materialized_and_deterministic(tmp_path):
    _write_fixture_sources(tmp_path)
    first = compile_discovery(root=tmp_path, generated_at="fixture-time", adapter=FakeAdapter())
    second = compile_discovery(root=tmp_path, generated_at="fixture-time", adapter=FakeAdapter())

    first_gate = first["finite_gate"]
    second_gate = second["finite_gate"]

    assert json.dumps(first_gate, sort_keys=True) == json.dumps(second_gate, sort_keys=True)
    assert first_gate["counts"]["positive"] == 0
    assert first_gate["counts"]["negative"] == len(first_gate["pointers"]["negative"])
    assert first_gate["counts"]["revocation"] == len(first_gate["pointers"]["revocation"])
    assert isinstance(first_gate["pointers"]["positive"], list)
    assert isinstance(first_gate["pointers"]["negative"], list)
    assert isinstance(first_gate["pointers"]["revocation"], list)
    assert first_gate["hardgates"]["FG-HG5"]["status"] == "pass"


def test_fg_hg5_fails_closed_on_unresolved_positive_pointer(tmp_path):
    canonical = tmp_path / "reports" / "canonical"
    canonical.mkdir(parents=True)
    (canonical / "positive.json").write_text(json.dumps({"evidence": True}) + "\n", encoding="utf-8")
    payload = {
        "discovery_map": {
            "rows": [
                {
                    "json_artifact": "reports/canonical/positive.json",
                    "discovery_level": "D4",
                    "evidence_pointer": "$.missing",
                },
            ]
        },
        "negative_witness_summary": {
            "audit_status": "pass",
            "row_count": 0,
            "rows": [],
        },
        "revocation_ledger": [],
    }

    gate = project_finite_discovery_gate(payload, root=tmp_path)

    assert gate["status"] == "fail"
    assert gate["hardgates"]["FG-HG5"]["status"] == "fail"
    assert gate["stale_pointers"] == [
        {
            "pointer": "reports/canonical/positive.json:$.missing",
            "normalized_pointer": "reports/canonical/positive.json:$.missing",
            "owner": "discovery_map.rows[0].evidence_pointer",
            "reason": "unresolved-pointer",
        }
    ]


def test_project_finite_discovery_gate_rejects_duplicate_positive_pointer():
    payload = {
        "discovery_map": {
            "rows": [
                {
                    "json_artifact": "reports/canonical/positive.json",
                    "discovery_level": "D4",
                    "evidence_pointer": "$.evidence",
                },
                {
                    "json_artifact": "reports/canonical/positive.json",
                    "discovery_level": "D5-M",
                    "evidence_pointer": "$.evidence",
                },
            ]
        },
        "negative_witness_summary": {
            "audit_status": "pass",
            "row_count": 0,
            "rows": [],
        },
        "revocation_ledger": [],
    }

    gate = project_finite_discovery_gate(payload)

    assert gate["status"] == "fail"
    assert gate["hardgates"]["FG-HG1"]["status"] == "fail"
    assert "FG-HG1" in [name for name, hardgate in gate["hardgates"].items() if hardgate["status"] == "fail"]


def test_project_finite_discovery_gate_rejects_duplicate_revocation_pointer():
    payload = {
        "discovery_map": {
            "rows": [
                {
                    "json_artifact": "reports/canonical/revocations.json",
                    "discovery_level": "DR",
                    "evidence_pointer": "$.rows[0]",
                },
                {
                    "json_artifact": "reports/canonical/revocations.json",
                    "discovery_level": "DR",
                    "evidence_pointer": "$.rows[0]",
                },
            ]
        },
        "negative_witness_summary": {
            "audit_status": "pass",
            "row_count": 0,
            "rows": [],
        },
        "revocation_ledger": [],
    }

    gate = project_finite_discovery_gate(payload)

    assert gate["status"] == "fail"
    assert gate["hardgates"]["FG-HG3"]["status"] == "fail"
    assert "FG-HG3" in [name for name, hardgate in gate["hardgates"].items() if hardgate["status"] == "fail"]

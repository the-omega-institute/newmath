import json
from pathlib import Path
from typing import Any, Mapping, Sequence

import pytest

from bedc_quality_lab.backends.current_lab.adapter import CurrentLabBackendEvidenceAdapter
from bedc_quality_lab.discovery_compiler.backend import BackendEvidenceAdapter, TheoryBackend
from bedc_quality_lab.discovery_compiler.capsule import ClaimCapsule, build_claim_capsule_payload
from bedc_quality_lab.discovery_compiler.compiler import compile_discovery
from bedc_quality_lab.discovery_compiler.map import DiscoveryMapRow, build_discovery_map_payload
from bedc_quality_lab.discovery_compiler.negative_reports import JSON_ARTIFACT as NEGATIVE_REPORTS_ARTIFACT


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
        payload = {
            "schema_id": "fixture-map",
            "generated_at": generated_at,
            "rows": [
                {
                    "report": "fixture-report",
                    "json_artifact": "reports/canonical/fixture.json",
                    "markdown_artifact": "reports/canonical/fixture.md",
                    "discovery_level": "DN",
                    "projection_status": "projected",
                    "evidence_pointer": "$.failed",
                    "audit_status": "valid",
                    "audit_reason": "",
                    "negative_report_pointer": f"{NEGATIVE_REPORTS_ARTIFACT}:$.rows[0]",
                }
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
        )
        return [
            {
                "negative_id": f"dn:{report_id}",
                "report_id": report_id,
                "kind": "discovery_report",
                "report": "fixture-report" if report_id != "dimension-mismatch-scale-leakage" else "dimension-mismatch-debt-transfer",
                "claim_id": "claim:fixture-report",
                "source": "reports/canonical/fixture.json:$.failed",
                "json_artifact": "reports/canonical/fixture.json",
                "markdown_artifact": "reports/canonical/fixture.md",
                "ledger_pointer": "reports/canonical/fixture.json:$.failed",
                "discovery_level": "DN",
                "terminal_verdict": "negative_discovery",
                "classifier_reasons": ["fixture"],
                "projection_status": "projected",
                "evidence_pointer": "$.failed",
                "failed_gate": "$.failed",
                "base_level": "D4" if report_id == "dimension-mismatch-scale-leakage" else None,
                "effective_level": "DN" if report_id == "dimension-mismatch-scale-leakage" else None,
                "what_was_learned": "fixture learned",
                "next_hypothesis": "fixture next hypothesis",
                "debt_row_pointer": None,
                "audit_status": "pass",
                "audit_reason": "",
            }
            for report_id in required
        ]

    def project_discovery_level(self, *, root: Path, generated_at: str | None = None) -> Sequence[Mapping[str, Any]]:
        return self.derive_ledger_rows(root=root, generated_at=generated_at)


def _write_fixture_sources(root: Path) -> None:
    canonical = root / "reports" / "canonical"
    canonical.mkdir(parents=True, exist_ok=True)
    (canonical / "fixture.json").write_text(json.dumps({"failed": True}) + "\n", encoding="utf-8")
    (canonical / "discovery_negative_witnesses.json").write_text(
        json.dumps({"status": "pointer-only", "expected_kind_count": 0, "witnesses": []}) + "\n",
        encoding="utf-8",
    )
    (canonical / "claim_verdicts.jsonl").write_text("", encoding="utf-8")


def test_backend_contract_and_current_lab_adapter_metadata():
    adapter: BackendEvidenceAdapter = CurrentLabBackendEvidenceAdapter()

    assert adapter.backend.name == "current-lab"
    assert adapter.build_pattern_spec()["status"] == "pointer-only"
    assert "terminal_verdict" not in adapter.backend.metrics
    assert adapter.build_source_spec()["canonical_reports"]


def test_claim_capsule_validates_required_cells():
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
    )

    capsule = ClaimCapsule.from_payload(payload)

    assert capsule.claim_id == "claim:fixture"
    assert capsule.status == "complete"
    with pytest.raises(ValueError, match="schema_id"):
        ClaimCapsule.from_payload({**payload, "schema_id": "wrong"})


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
    }

    assert DiscoveryMapRow.from_mapping(row).negative_report_pointer == f"{NEGATIVE_REPORTS_ARTIFACT}:$.rows[0]"
    with pytest.raises(ValueError, match="copies owner facts"):
        DiscoveryMapRow.from_mapping({**row, "terminal_verdict": "negative_discovery"})


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
            }
        ],
        generated_at="fixture-time",
    )

    assert payload["row_count"] == 1
    assert payload["level_counts"]["D4"] == 1


def test_compile_discovery_writes_backend_negative_owner_before_map(tmp_path):
    _write_fixture_sources(tmp_path)
    adapter = FakeAdapter()

    result = compile_discovery(root=tmp_path, generated_at="fixture-time", adapter=adapter)

    assert adapter.calls == ["negative", "map"]
    assert result["negative_discovery_reports"]["rows"][0]["terminal_verdict"] == "negative_discovery"
    assert result["negative_discovery_reports"]["row_count"] == 6
    assert result["discovery_map"]["rows"][0]["negative_report_pointer"] == f"{NEGATIVE_REPORTS_ARTIFACT}:$.rows[0]"

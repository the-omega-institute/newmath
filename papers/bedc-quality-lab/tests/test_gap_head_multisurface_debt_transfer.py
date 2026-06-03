import json
from pathlib import Path

import bedc_quality_lab
import pytest
from bedc_quality_lab.schema import SCHEMA_ID
from scripts import run_canonical_reports as canonical
from scripts import run_gap_head_multisurface_debt_transfer as transfer


def _stats(mean, low=None, high=None):
    low = mean if low is None else low
    high = mean if high is None else high
    return {
        "n": 1,
        "mean": float(mean),
        "std": 0.0,
        "ci95_half_width": 0.0,
        "ci95_low": float(low),
        "ci95_high": float(high),
    }


def _fake_surface_result(surface_id, status="pass"):
    learned = _stats(0.91 if status == "pass" else 0.55, 0.89 if status == "pass" else 0.50, 0.93)
    matched = _stats(0.50, 0.48, 0.52)
    gate_status = "pass" if status == "pass" else "fail"
    return {
        "surface_id": surface_id,
        "role": "runnable",
        "countable_hg_a2_2": True,
        "sample_count": 32,
        "seed_count": 1,
        "seeds": [11],
        "rho": 0.82,
        "transition_kernel": None,
        "latent_distribution": {"family": "gaussian"},
        "mixing": "sinusoidal_shear",
        "metrics": {
            "vanilla": {"failure_detection_auroc": _stats(0.50)},
            "learned_gap_head_on_h": {"failure_detection_auroc": learned},
            transfer.producer.MATCHED_RANDOM_ARM: {"failure_detection_auroc": matched},
        },
        "hardgates": {
            "HG-A2-1": {
                "status": gate_status,
                "criterion": "fixture",
                "learned_auroc": learned,
                "matched_random_auroc": matched,
                "forbidden_feature_audit": {"status": "pass"},
            }
        },
        "verdict": {
            "status": status,
            "passed_gates": ["HG-A2-1"] if status == "pass" else [],
            "failed_gates": [] if status == "pass" else ["HG-A2-1"],
            "reason": "fixture",
        },
    }


def test_surface_registry_has_seven_rows_and_four_countable():
    registry = transfer._surface_registry()

    assert [spec.surface_id for spec in registry] == [
        "clean-gaussian-ou",
        "anisotropic-rho-0p95-0p30",
        "laplace-latent",
        "sample-count-1024",
        "student-t-latent",
        "realnvp-spiral-mixing",
        "undertrain-boundary",
    ]
    assert sum(1 for spec in registry if spec.countable_hg_a2_2) == 4
    roles = {spec.surface_id: spec.role for spec in registry}
    assert roles["student-t-latent"] == "deferred"
    assert roles["realnvp-spiral-mixing"] == "boundary_only"
    assert roles["undertrain-boundary"] == "not_runnable"


def test_hg_a2_1_pass_requires_learned_ci_above_matched_and_audit_pass():
    metrics = {
        "learned_gap_head_on_h": {"failure_detection_auroc": _stats(0.90, 0.86, 0.94)},
        transfer.producer.MATCHED_RANDOM_ARM: {"failure_detection_auroc": _stats(0.50, 0.48, 0.52)},
    }
    gates = transfer._surface_hardgates(metrics=metrics, forbidden_audit={"status": "pass"})

    assert gates["HG-A2-1"]["status"] == "pass"

    failed = transfer._surface_hardgates(metrics=metrics, forbidden_audit={"status": "fail"})
    assert failed["HG-A2-1"]["status"] == "fail"


@pytest.mark.parametrize(
    "learned,matched",
    [
        (_stats(0.90, 0.51, 0.94), _stats(0.50, 0.48, 0.52)),
        (
            _stats(transfer.robustness.AUROC_POSITIVE_THRESHOLD - 0.01, 0.82, 0.84),
            _stats(0.50, 0.48, 0.52),
        ),
        (
            _stats(0.90, 0.86, 0.94),
            _stats(0.50, 0.48, transfer.robustness.MATCHED_RANDOM_AUROC_CEILING + 0.01),
        ),
    ],
)
def test_hg_a2_1_fails_each_auroc_condition(learned, matched):
    metrics = {
        "learned_gap_head_on_h": {"failure_detection_auroc": learned},
        transfer.producer.MATCHED_RANDOM_ARM: {"failure_detection_auroc": matched},
    }

    gates = transfer._surface_hardgates(metrics=metrics, forbidden_audit={"status": "pass"})

    assert gates["HG-A2-1"]["status"] == "fail"


def test_hg_a2_2_status_thresholds():
    assert transfer._multi_surface_status(2) == "pass"
    assert transfer._multi_surface_status(1) == "single_surface_only"
    assert transfer._multi_surface_status(0) == "failed"


def test_build_payload_records_hardgates_and_boundary_ledger(monkeypatch):
    statuses = {
        "clean-gaussian-ou": "pass",
        "anisotropic-rho-0p95-0p30": "pass",
        "laplace-latent": "failed",
        "sample-count-1024": "failed",
    }
    monkeypatch.setattr(
        transfer,
        "_surface_result",
        lambda spec: _fake_surface_result(spec.surface_id, statuses[spec.surface_id]),
    )

    payload = transfer.build_payload(generated_at="fixture-time")

    assert payload["gap_head_multisurface_debt_transfer"]["multi_surface_status"] == "pass"
    assert payload["hardgate_evidence"]["HG-A2-2"]["pass_surface_count"] == 2
    assert payload["hardgate_evidence"]["HG-A2-3"]["status"] == "pass"
    assert payload["mechanism_status"] == "not_claimed"
    assert payload["d5m_status"] == "not_claimed"
    assert {row["surface_id"] for row in payload["boundary_ledger"]} == {
        "laplace-latent",
        "sample-count-1024",
        "student-t-latent",
        "realnvp-spiral-mixing",
        "undertrain-boundary",
    }
    assert {row["kind"] for row in payload["boundary_ledger"]} == {
        "deferred",
        "boundary_only",
        "not_runnable",
        "runnable_failed",
    }
    failed_rows = {
        row["surface_id"]: row
        for row in payload["boundary_ledger"]
        if row["kind"] == "runnable_failed"
    }
    assert failed_rows["laplace-latent"]["failed_gates"] == ["HG-A2-1"]
    assert failed_rows["sample-count-1024"]["evidence_pointer"] == "$.surfaces[*].hardgates"


def test_failed_countable_runnable_surface_appears_in_boundary_ledger(monkeypatch):
    statuses = {
        "clean-gaussian-ou": "pass",
        "anisotropic-rho-0p95-0p30": "pass",
        "laplace-latent": "failed",
        "sample-count-1024": "pass",
    }
    monkeypatch.setattr(
        transfer,
        "_surface_result",
        lambda spec: _fake_surface_result(spec.surface_id, statuses[spec.surface_id]),
    )

    payload = transfer.build_payload(generated_at="fixture-time")
    row_by_surface = {row["surface_id"]: row for row in payload["boundary_ledger"]}

    assert payload["gap_head_multisurface_debt_transfer"]["multi_surface_status"] == "pass"
    assert payload["hardgate_evidence"]["HG-A2-2"]["pass_surface_count"] == 3
    assert row_by_surface["laplace-latent"]["kind"] == "runnable_failed"
    assert row_by_surface["laplace-latent"]["failed_gates"] == ["HG-A2-1"]


def test_hg_a2_3_fails_when_boundary_ledger_omits_expected_row(monkeypatch):
    original_boundary_ledger = transfer._boundary_ledger

    def omit_one_non_countable(registry, surfaces):
        return [
            row
            for row in original_boundary_ledger(registry, surfaces)
            if row["surface_id"] != "student-t-latent"
        ]

    monkeypatch.setattr(transfer, "_boundary_ledger", omit_one_non_countable)
    monkeypatch.setattr(
        transfer,
        "_surface_result",
        lambda spec: _fake_surface_result(spec.surface_id, "pass"),
    )

    payload = transfer.build_payload(generated_at="fixture-time")

    assert payload["hardgate_evidence"]["HG-A2-3"]["status"] == "fail"


def test_build_payload_single_surface_and_failed_statuses(monkeypatch):
    def one_pass(spec):
        return _fake_surface_result(spec.surface_id, "pass" if spec.surface_id == "clean-gaussian-ou" else "failed")

    monkeypatch.setattr(transfer, "_surface_result", one_pass)
    payload = transfer.build_payload(generated_at="fixture-time")
    assert payload["gap_head_multisurface_debt_transfer"]["multi_surface_status"] == "single_surface_only"

    monkeypatch.setattr(transfer, "_surface_result", lambda spec: _fake_surface_result(spec.surface_id, "failed"))
    payload = transfer.build_payload(generated_at="fixture-time")
    assert payload["gap_head_multisurface_debt_transfer"]["multi_surface_status"] == "failed"


def test_artifact_paths_are_runs_only_and_not_canonical():
    assert transfer.JSON_ARTIFACT == "runs/gap_head_multisurface_debt_transfer.json"
    assert transfer.REPORT_ARTIFACT == "runs/gap_head_multisurface_debt_transfer.md"
    assert "reports/canonical" not in transfer.JSON_ARTIFACT
    assert "gap_head_multisurface_debt_transfer.json" not in {
        Path(spec.json_artifact).name for spec in canonical.CANONICAL_REPORTS
    }
    assert "gap-head-on-h" in {spec.name for spec in canonical.CANONICAL_REPORTS}
    assert "gap-head-on-h" not in {spec.name for spec in canonical.CANONICAL_REPORTS if "multisurface" in spec.name}


def test_write_payload_keeps_artifact_in_runs(tmp_path, monkeypatch):
    monkeypatch.setattr(
        transfer,
        "_surface_result",
        lambda spec: _fake_surface_result(spec.surface_id, "pass"),
    )
    payload = transfer.build_payload(generated_at="fixture-time")

    transfer._write_payload(payload, root=tmp_path)

    written = json.loads((tmp_path / transfer.JSON_ARTIFACT).read_text(encoding="utf-8"))
    markdown = (tmp_path / transfer.REPORT_ARTIFACT).read_text(encoding="utf-8")
    assert written["artifact_id"] == transfer.ARTIFACT_ID
    assert written["status"] == "pointer-only"
    assert "Surface registry pointer" in markdown
    assert not (tmp_path / "reports" / "canonical" / "gap_head_multisurface_debt_transfer.json").exists()


def test_forbidden_claim_and_package_invariants(monkeypatch):
    monkeypatch.setattr(
        transfer,
        "_surface_result",
        lambda spec: _fake_surface_result(spec.surface_id, "pass"),
    )
    payload = transfer.build_payload(generated_at="fixture-time")

    assert payload["forbidden_claim_term_audit"]["status"] == "pass"
    assert payload["mechanism_status"] == "not_claimed"
    assert payload["d5m_status"] == "not_claimed"
    assert "discovery_level" not in payload["gap_head_multisurface_debt_transfer"]
    payload_text = json.dumps(payload).lower()
    assert "d5m_promotion" not in payload_text
    for term in (
        "total score",
        "rank",
        "grade",
        "hidden cost weight",
        "full-lejepa",
        "global-quality",
        "full-tensor-namecert",
        "llm-behavior",
    ):
        assert term not in payload_text
    assert SCHEMA_ID == "bedc-quality-lab:evidence-envelope"
    assert bedc_quality_lab.__all__ == ["QualityEvidenceEnvelope"]

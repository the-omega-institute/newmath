from __future__ import annotations

from bedc_quality_lab import backends
from bedc_quality_lab.backends import attribution
from bedc_quality_lab.backends.attribution import GapHeadAttributionBackendEvidenceAdapter
from bedc_quality_lab.discovery_compiler.backend import BackendEvidenceAdapter, TheoryBackend
from bedc_quality_lab.discovery_compiler.compiler import load_adapter


EXPECTED_METRICS = (
    "full_unlogged_error_rate_mean",
    "hardgates_failed_gate",
    "a4_hardgates_failed_gate",
    "claim_capsule_hardgates_status",
    "d5_m_passed",
    "mechanism_case_status",
    "mechanism_evidence_status",
    "mechanism_evidence_candidate",
    "mechanism_evidence_failed_gate",
    "mechanism_evidence_ledger_debt",
    "mechanism_evidence_head_patch_status",
    "mechanism_evidence_head_patch_delta",
    "e_hardgates_status",
    "residualized_non_score_mechanism_claim_allowed",
)
EXPECTED_LEDGER_ROWS = (
    "source/source-coverage",
    "source/latent-distribution-gaussianity",
    "source/dimension-match",
    "source/finite-sample-support",
    "classifier/optimizer-certificate",
    "generalization/global-claim-boundary",
)


def fake_capsule():
    return {
        "run_id": "fake-gap-head-attribution",
        "aggregate": {
            "seed_order": [11, 17],
            "by_arm": {
                "full": {
                    "UnloggedErrorRate": {"mean": 0.125},
                },
            },
        },
        "hardgates": {"failed_gate": "A1-HG3", "gates": {"A1-HG3": {"status": "fail"}}},
        "a4_hardgates": {"failed_gate": "A4-HG5", "gates": {"A4-HG5": {"status": "fail"}}},
        "e_hardgates": {"status": "fail", "failed_gate": "E-HG4_non_score_mechanism_claim_fail_closed"},
        "residualized_attribution_claim": {"non_score_mechanism_claim_allowed": False},
        "claim_capsule_hardgates": {
            "CC-HG1": {"name": "CC-HG1", "status": "pass"},
            "CC-HG2": {"name": "CC-HG2", "status": "pass"},
        },
        "d5_m": {"passed": False, "status": "blocked", "failed_gate": "A4-HG5"},
        "mechanism_case": {"status": "D5-O retained, mechanism unresolved"},
        "mechanism_evidence": {
            "evidence_level": "patch",
            "base_level": "D5-O",
            "base_status": "ready",
            "mechanism_level": "blocked",
            "mechanism_status": "blocked",
            "candidate_mechanism": "unresolved",
            "failed_gate": "A4-HG5",
            "residualized_significant": True,
            "control_clear": True,
            "score_margin_sufficient": False,
            "head_patch_status": "pass",
            "head_patch_delta": -0.08,
            "required_gate_pointers": [
                "$.a4_hardgates.gates.A4-HG2.status",
                "$.a4_hardgates.gates.A4-HG3.status",
                "$.a4_hardgates.gates.head_causal_patch.status",
                "$.a4_hardgates.gates.A4-HG5.status",
            ],
            "metric_pointers": {
                "residualized_status": "$.residualized_attribution.status",
                "score_margin_channel_classification": "$.score_margin_causal_evidence.channel_classification",
                "head_patch_status": "$.head_channel_patch_evidence.gate_status",
                "head_patch_delta": "$.head_channel_patch_evidence.null_head.ci_summaries.AUROC_after_minus_before.mean",
            },
            "ledger_debt_pointer": "$.ledger_debt.0.status",
            "closure_pointer": "$.mechanism_evidence.mechanism_status",
            "source_issue": 750,
            "source_issues": [747, 750],
        },
        "head_channel_patch_evidence": {
            "gate_status": "pass",
            "null_head": {"ci_summaries": {"AUROC_after_minus_before": {"mean": -0.08}}},
        },
        "ledger_debt": [{"debt_id": "gap-head-mechanism-evidence-closure", "status": "open"}],
        "residualized_attribution": {"status": "pass"},
        "score_margin_causal_evidence": {"channel_classification": "not_score_margin_sufficient"},
        "control_pointer": {
            "matched_random": "$.control_evidence.matched_random",
            "h_random_rotation": "$.control_evidence.h_random_rotation",
            "h_random_projection_lowdim": "$.control_evidence.h_random_projection_lowdim",
        },
        "control_evidence": {
            "matched_random": {"AUROC": {"mean": 0.5}},
            "h_random_rotation": {},
            "h_random_projection_lowdim": {},
        },
        "scope": {"not_claimed": ["mechanism closure unless D5-M"]},
        "source_artifacts": {"generation_script": "scripts/run_gap_head_attribution_capsule.py"},
        "config": {"sample_count": 768, "seed_count": 2, "arm_count": 24},
    }


def resolve_projection_pointer(payload, pointer):
    assert isinstance(pointer, str)
    assert pointer.startswith("$.")
    cursor = payload
    for part in pointer[2:].split("."):
        if isinstance(cursor, dict):
            assert part in cursor
            cursor = cursor[part]
        else:
            assert isinstance(cursor, list)
            assert part.isdigit()
            cursor = cursor[int(part)]
    return cursor


def collect_backend_projection_pointers(adapter, payload):
    for row in adapter.backend.theorem_rows:
        yield f"theorem_rows.{row['name']}.evidence_pointer", row["evidence_pointer"]
        if "control_pointer" in row:
            yield f"theorem_rows.{row['name']}.control_pointer", row["control_pointer"]
    for gate in adapter.backend.hardgates:
        yield f"hardgates.{gate['name']}.pointer", gate["pointer"]
    for name, pointer in payload["metric_pointers"].items():
        yield f"metric_pointers.{name}", pointer
    for name, pointer in payload["control_pointer"].items():
        yield f"control_pointer.{name}", pointer


def assert_projection_pointers_resolve(payload, pointers):
    seen = []
    for label, pointer in pointers:
        resolved = resolve_projection_pointer(payload, pointer)
        assert resolved is not None, label
        seen.append(label)
    return tuple(seen)


def test_adapter_metadata_and_module_loading_contract():
    adapter: BackendEvidenceAdapter = GapHeadAttributionBackendEvidenceAdapter()
    backend = adapter.backend

    assert isinstance(backend, TheoryBackend)
    assert backend.name == "gap-head-attribution"
    assert backend.scope_kind == "non-canonical-backend-probe"
    assert "attribution" in backends.__all__
    assert backends.GapHeadAttributionBackendEvidenceAdapter is GapHeadAttributionBackendEvidenceAdapter
    assert attribution.GapHeadAttributionBackendEvidenceAdapter is GapHeadAttributionBackendEvidenceAdapter
    loaded = load_adapter(
        "bedc_quality_lab.backends.attribution:GapHeadAttributionBackendEvidenceAdapter"
    )
    assert loaded.backend.name == "gap-head-attribution"
    assert backend.metrics == EXPECTED_METRICS
    assert "h_norm_only_uer_reduction_mean" not in backend.metrics
    assert tuple(f"{row['kind']}/{row['residue']}" for row in backend.ledger_rows) == EXPECTED_LEDGER_ROWS
    assert "source/transition-isotropy" not in {
        f"{row['kind']}/{row['residue']}" for row in backend.ledger_rows
    }
    assert "source/mixing-family-coverage" not in {
        f"{row['kind']}/{row['residue']}" for row in backend.ledger_rows
    }
    assert "source/distribution-family-coverage" not in {
        f"{row['kind']}/{row['residue']}" for row in backend.ledger_rows
    }
    assert "verification/theorem3-bound-margin" not in {
        f"{row['kind']}/{row['residue']}" for row in backend.ledger_rows
    }
    assert "terminal verdict classification" in backend.not_claimed
    assert all("terminal_verdict" not in row for row in backend.ledger_rows)
    control_row = backend.theorem_rows[0]
    assert control_row["name"] == "control/matched-random-control"
    assert control_row["evidence_pointer"] == "$.control_evidence.matched_random"
    assert control_row["control_pointer"] == "$.control_evidence.matched_random"
    assert backend.theorem_rows[1]["evidence_pointer"] == "$.mechanism_evidence"
    assert backend.theorem_rows[2]["evidence_pointer"] == "$.ledger_debt.0"


def test_compute_metrics_delegates_to_capsule_builder(monkeypatch, tmp_path):
    calls = []

    def fake_build_gap_head_attribution_capsule(**kwargs):
        calls.append(kwargs)
        return fake_capsule()

    monkeypatch.setattr(
        attribution.run_gap_head_attribution_capsule,
        "build_gap_head_attribution_capsule",
        fake_build_gap_head_attribution_capsule,
    )

    payload = GapHeadAttributionBackendEvidenceAdapter().compute_metrics(root=tmp_path, generated_at="fake-time")

    assert calls == [
        {
            "root": tmp_path,
            "run_id": "gap-head-attribution-backend-probe",
            "generated_at": "fake-time",
        }
    ]
    assert payload["generated_at"] == "fake-time"
    assert tuple(payload["metrics"]) == GapHeadAttributionBackendEvidenceAdapter.backend.metrics
    assert payload["metrics"]["full_unlogged_error_rate_mean"] == 0.125
    assert payload["metrics"]["hardgates_failed_gate"] == "A1-HG3"
    assert payload["metrics"]["a4_hardgates_failed_gate"] == "A4-HG5"
    assert payload["metrics"]["claim_capsule_hardgates_status"] == {
        "CC-HG1": "pass",
        "CC-HG2": "pass",
    }
    assert payload["metrics"]["d5_m_passed"] is False
    assert payload["metrics"]["mechanism_case_status"] == "D5-O retained, mechanism unresolved"
    assert payload["metrics"]["mechanism_evidence_status"] == "blocked"
    assert payload["metrics"]["mechanism_evidence_candidate"] == "unresolved"
    assert payload["metrics"]["mechanism_evidence_failed_gate"] == "A4-HG5"
    assert payload["metrics"]["mechanism_evidence_ledger_debt"] == "open"
    assert payload["metrics"]["mechanism_evidence_head_patch_status"] == "pass"
    assert payload["metrics"]["mechanism_evidence_head_patch_delta"] == -0.08
    assert payload["metrics"]["e_hardgates_status"] == "fail"
    assert payload["metrics"]["residualized_non_score_mechanism_claim_allowed"] is False
    assert set(payload["metric_pointers"]) == set(GapHeadAttributionBackendEvidenceAdapter.backend.metrics)
    assert "terminal_verdict" not in payload


def test_backend_pointer_surfaces_resolve_in_adapter_projection(monkeypatch, tmp_path):
    monkeypatch.setattr(
        attribution.run_gap_head_attribution_capsule,
        "build_gap_head_attribution_capsule",
        lambda **kwargs: fake_capsule(),
    )

    adapter = GapHeadAttributionBackendEvidenceAdapter()
    payload = adapter.compute_metrics(root=tmp_path, generated_at="fake-time")

    labels = assert_projection_pointers_resolve(payload, collect_backend_projection_pointers(adapter, payload))

    assert labels == (
        "theorem_rows.control/matched-random-control.evidence_pointer",
        "theorem_rows.control/matched-random-control.control_pointer",
        "theorem_rows.namecert/mechanism-candidate-audit.evidence_pointer",
        "theorem_rows.closure/mechanism-closure-debt.evidence_pointer",
        "hardgates.A1.pointer",
        "hardgates.A4.pointer",
        "hardgates.E.pointer",
        "hardgates.claim-capsule.pointer",
        "metric_pointers.full_unlogged_error_rate_mean",
        "metric_pointers.hardgates_failed_gate",
        "metric_pointers.a4_hardgates_failed_gate",
        "metric_pointers.claim_capsule_hardgates_status",
        "metric_pointers.d5_m_passed",
        "metric_pointers.mechanism_case_status",
        "metric_pointers.mechanism_evidence_status",
        "metric_pointers.mechanism_evidence_candidate",
        "metric_pointers.mechanism_evidence_failed_gate",
        "metric_pointers.mechanism_evidence_ledger_debt",
        "metric_pointers.mechanism_evidence_head_patch_status",
        "metric_pointers.mechanism_evidence_head_patch_delta",
        "metric_pointers.e_hardgates_status",
        "metric_pointers.residualized_non_score_mechanism_claim_allowed",
        "control_pointer.matched_random",
        "control_pointer.h_random_rotation",
        "control_pointer.h_random_projection_lowdim",
    )


def test_ledger_projection_uses_structured_debt_kernel(monkeypatch, tmp_path):
    monkeypatch.setattr(
        attribution.run_gap_head_attribution_capsule,
        "build_gap_head_attribution_capsule",
        lambda **kwargs: fake_capsule(),
    )

    adapter = GapHeadAttributionBackendEvidenceAdapter()
    rows = adapter.derive_ledger_rows(root=tmp_path)
    by_key = {f"{row['kind']}/{row['residue']}": row for row in rows}

    assert tuple(by_key) == EXPECTED_LEDGER_ROWS
    assert by_key["source/source-coverage"]["status"] == "open"
    assert by_key["source/latent-distribution-gaussianity"]["status"] == "closed"
    assert by_key["source/dimension-match"]["status"] == "closed"
    assert by_key["source/finite-sample-support"]["status"] == "partial"
    assert by_key["classifier/optimizer-certificate"]["status"] == "open"
    assert by_key["generalization/global-claim-boundary"]["status"] == "closed"
    assert {row["evidence_pointer"] for row in rows} == {"bedc_quality_lab.ledger.derive_ledger_gaps"}
    assert {row["owner"] for row in rows} == {
        "scripts.run_gap_head_attribution_capsule.build_gap_head_attribution_capsule"
    }
    assert adapter.derive_negative_discovery_rows(root=tmp_path) == ()
    assert adapter.project_discovery_level(root=tmp_path) == rows

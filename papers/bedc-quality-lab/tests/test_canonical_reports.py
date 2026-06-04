import json
import os
from pathlib import Path

import pytest

from scripts import run_formal_hardening_report as formal_hardening
from scripts import run_canonical_reports as canonical


HG_P_CORE = {
    "mixing-family-sweep",
    "anisotropic-ou-sweep",
    "gap-head-on-h",
    "gap-head-discovery",
    "gap-head-ablation",
    "gap-head-threshold-frontier",
    "certificate-guided-training",
    "certificate-guided-discovery",
}
QUALITY_SCORECARD_METRICS = {
    "CertCov",
    "DebtQ",
    "CriticalDebt",
    "LedgerCompleteness",
    "ClassifierShiftCount",
    "PositiveDiscoveryCount",
    "AuditImprovementCount",
    "NegativeResultCount",
    "ScopeCompleteness",
    "CostProtocolCompleteness",
    "HardeningCoverage",
    "OverclaimRate",
}


def _payload_for_spec(spec):
    payload = {key: f"fixture-{key}" for key in spec.required_json_keys}
    payload.update(
        {
            "source_artifacts": {
                "cost_protocol": "configs/default_cost_protocol.yaml",
                "canonical_runner": "scripts/run_gaussian_ou_lejepa.py",
            },
            "applicability_boundary": {
                "claimed_scope": "fixture scope",
                "not_claimed": "fixture nonclaim",
                "forbidden_inference_columns": ["z"],
            },
            "coverage_item": {"status": "fixture"},
            "transition_debt_by_grid": {"cell": {"status": "fixture"}},
            "config": {"arm": "baseline-only"},
            "control_protocol": {"status": "fixture"},
            "treatment_verdict": {"positive": spec.name == "gap-head-on-h"},
            "control_verdict": {"positive": False},
            "boundary_checks": {
                "forbidden_inference_columns": ["z"],
                "representation_boundary": "learned_h",
            },
            "score_terms": {"status": "fixture"},
            "matched_random_control": {
                "status": "fixture",
                "control_verdict": {"positive": False},
                "control_projection": {"positive_discovery": True},
            },
            "objective": {"required_rows": ["fixture"]},
            "cost_protocol": {"name": "fixture"},
            "not_claimed": ["fixture nonclaim"],
            "claim_gate": {
                "status": "fixture",
                "audit_improvement_tradeoff": spec.name == "certificate-guided-training",
                "training_audit_improvement_tradeoff": spec.name == "certificate-guided-discovery",
            },
            "paired_seed_protocol": {"status": "fixture"},
            "arm_protocol": {"status": "fixture"},
            "arm_summaries": {"status": "fixture"},
            "main_claim_status": "fixture status",
            "final_main_claim_status": "fixture status",
            "hardgate": {"status": "pass"},
            "failed_gate": None,
            "verdict": "accepted",
            "discovery_level": "D0",
            "readiness": {"status": "D4-at-threshold"},
            "threshold_curve": [
                {
                    "threshold": 0.05,
                    "metrics": {
                        "AUROC": {"mean": 0.6, "std": 0.0, "n": 2, "ci95_low": 0.6, "ci95_high": 0.6},
                        "UnloggedErrorRate": {"mean": 0.1, "std": 0.0, "n": 2, "ci95_low": 0.1, "ci95_high": 0.1},
                        "LoggedFalseAlarmRate": {"mean": 0.2, "std": 0.0, "n": 2, "ci95_low": 0.2, "ci95_high": 0.2},
                        "CriticalUnloggedErrorRate": {"mean": 0.1, "std": 0.0, "n": 2, "ci95_low": 0.1, "ci95_high": 0.1},
                        "QualityQ": {"mean": 0.3, "std": 0.0, "n": 2, "ci95_low": 0.3, "ci95_high": 0.3},
                        "NetInformation": {"mean": 1.2, "std": 0.0, "n": 2, "ci95_low": 1.2, "ci95_high": 1.2},
                    },
                }
            ],
            "threshold_summary": {
                "control_baseline": [
                    {
                        "threshold": 0.05,
                        "metrics": {
                            "CriticalUnloggedErrorRate": {"mean": 0.2, "std": 0.0, "n": 2, "ci95_low": 0.2, "ci95_high": 0.2}
                        },
                    }
                ]
            },
            "pareto_axis_spec": {
                "x": "AUROC",
                "x_direction": "maximize",
                "y": "CriticalLoggedCoverage",
                "y_definition": "1 - CriticalUnloggedErrorRate",
                "y_direction": "maximize",
            },
            "pareto_frontier": [
                {
                    "threshold": 0.05,
                    "metrics": {
                        "AUROC": {"mean": 0.6, "std": 0.0, "n": 2, "ci95_low": 0.6, "ci95_high": 0.6},
                        "CriticalLoggedCoverage": {"mean": 0.9, "std": 0.0, "n": 2, "ci95_low": 0.9, "ci95_high": 0.9},
                    },
                }
            ],
            "factor_attribution": {
                "learned_head": {
                    "auroc_delta": -0.2,
                    "status": "pass",
                }
            },
            "positive_discovery_pointer": "$.factor_attribution.learned_head.auroc_delta",
            "matched_random_baseline": {"status": "fixture", "positive_discovery": False},
            "negative_result_ledger": [{"status": "fixture"}],
            "ledger_summary": {
                "status": "negative" if spec.name == "spectral-ablation-hinge" else "fixture",
                "basis": {
                    "hardening_coverage": {
                        "recorded": 3,
                        "required": 4,
                        "items": [
                            {"name": "sameClass equivalence", "recorded": True},
                            {"name": "margin stability", "recorded": True},
                            {"name": "finite ledger coverage", "recorded": False},
                            {"name": "missing-row negative example", "recorded": True},
                        ],
                    }
                },
            },
            "negative_control_summary": {"status": "fixture", "treatment_better_than_all_controls": False},
            "surface_delta_count": 2,
            "positive_discovery": spec.name == "gap-head-discovery",
            "classifier_state": {
                "recorded_ledger_rows": 3,
                "required_ledger_rows": 4,
            },
            "debt_terms": {"classifier_ledger_rows": 0.25},
            "audit_decision": {"audit_status": "pass", "overclaim_rate": 0.4},
            "result": {"status": "negative" if spec.name == "certificate-guided-training" else "fixture"},
            "deltas": {"after_minus_before": {"debt_delta": -0.25}},
            "verdicts": [{"deltas": {"debt_delta": -0.25}}],
        }
    )
    if spec.name == "mixing-family-sweep":
        payload["coverage_item"] = {
            "canonical_families": ["a", "b", "c"],
            "covered_families": ["a", "b"],
            "debt_item": {"score": "0.125", "status": "partial"},
        }
        payload["negative_result_summary"] = {
            "cells": {
                "a": {"negative_result": True},
                "b": {"negative_result": False},
            }
        }
    if spec.name == "anisotropic-ou-sweep":
        payload["transition_debt_by_grid"] = {"cell": {"status": "open-or-partial"}}
        payload["negative_result_summary"] = {
            "cells": {
                "a": {"negative_result": True},
                "b": {"negative_result": True},
            }
        }
    if spec.name == "nongaussian-distribution-sweep":
        payload["negative_result_ledger"] = [{"status": "negative"}, {"status": "negative"}]
        payload["coverage_item"] = {"debt_item": {"status": "open"}}
    return payload


def _walk_keys(value):
    if isinstance(value, dict):
        for key, cell in value.items():
            yield key
            yield from _walk_keys(cell)
    elif isinstance(value, list):
        for cell in value:
            yield from _walk_keys(cell)


def _write_payloads_for_all_specs(canonical_module, tmp_path):
    canonical_module.ROOT = tmp_path
    canonical_module.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    canonical_module.INDEX_ARTIFACT = tmp_path / "reports" / "canonical" / "index.json"
    for spec in canonical_module.CANONICAL_REPORTS:
        json_path = canonical_module._artifact_path(spec.json_artifact)
        md_path = canonical_module._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")


def _mutate_payload(canonical_module, report_name, update):
    spec = canonical_module._specs_by_name()[report_name]
    json_path = canonical_module._artifact_path(spec.json_artifact)
    payload = json.loads(json_path.read_text(encoding="utf-8"))
    update(payload)
    json_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")


def _index_row_for_spec(spec):
    return {
        "name": spec.name,
        "bundle_role": spec.bundle_role,
        "status": "pass",
        "json_artifact": spec.json_artifact,
        "markdown_artifact": spec.markdown_artifact,
        "discipline": {
            "scope_pointer": spec.scope_pointer,
            "cost_pointer": spec.cost_pointer,
            "not_claimed_pointer": spec.not_claimed_pointer,
            "positive_claim_pointer": spec.positive_claim_pointer,
            "control_pointer": spec.control_pointer,
            "no_control_rationale_pointer": spec.no_control_rationale_pointer,
        },
    }


def test_manifest_names_and_artifacts_are_unique_and_canonical_owned():
    names = [spec.name for spec in canonical.CANONICAL_REPORTS]
    json_artifacts = [spec.json_artifact for spec in canonical.CANONICAL_REPORTS]
    markdown_artifacts = [spec.markdown_artifact for spec in canonical.CANONICAL_REPORTS]

    assert "formal_hardening" not in names
    assert "reports/canonical/formal_hardening.json" not in json_artifacts
    assert "reports/canonical/formal_hardening.md" not in markdown_artifacts
    assert len(names) == len(set(names))
    assert names == [
        "mixing-family-sweep",
        "anisotropic-ou-sweep",
        "gap-head-on-h",
        "gap-head-discovery",
        "gap-head-ablation",
        "gap-head-threshold-frontier",
        "nongaussian-distribution-sweep",
        "certificate-guided-training",
        "certificate-guided-discovery",
        "spectral-ablation-hinge",
    ]
    assert "certificate-guided-arms" not in names
    assert len(json_artifacts) == len(set(json_artifacts))
    assert len(markdown_artifacts) == len(set(markdown_artifacts))
    for spec in canonical.CANONICAL_REPORTS:
        assert spec.json_artifact.startswith("reports/canonical/")
        assert spec.markdown_artifact.startswith("reports/canonical/")
        assert spec.json_artifact.endswith(".json")
        assert spec.markdown_artifact.endswith(".md")
        assert spec.required_json_keys
        assert spec.bundle_role in {"hg_p_core", "auxiliary"}
        assert spec.scope_pointer.startswith("$.")
        assert spec.cost_pointer.startswith("$.")
        assert spec.not_claimed_pointer.startswith("$.")
        assert spec.positive_claim_pointer.startswith("$.")


def test_gap_head_manifest_rows_are_canonical_and_keyed():
    on_h = canonical._specs_by_name()["gap-head-on-h"]
    discovery = canonical._specs_by_name()["gap-head-discovery"]

    assert on_h.command == ("python3", "scripts/run_gap_ledger_head_on_h.py")
    assert on_h.json_artifact == "reports/canonical/gap-head-on-h.json"
    assert on_h.markdown_artifact == "reports/canonical/gap-head-on-h.md"
    assert discovery.command == ("python3", "scripts/run_gap_head_discovery.py")
    assert discovery.json_artifact == "reports/canonical/gap-head-discovery.json"
    assert discovery.markdown_artifact == "reports/canonical/gap-head-discovery.md"
    assert {
        "boundary_no_z_audit",
        "forbidden_column_audit",
        "aggregate_metrics",
        "treatment_comparison",
        "control_protocol",
        "control_verdict",
        "main_claim_status",
    }.issubset(set(on_h.required_json_keys))
    assert {
        "boundary_checks",
        "matched_random_control",
        "main_claim_status",
        "final_main_claim_status",
    }.issubset(set(discovery.required_json_keys))


def test_canonical_reports_manifest_includes_gap_head_ablation():
    spec = canonical._specs_by_name()["gap-head-ablation"]

    assert spec.command == ("python3", "scripts/run_gap_head_ablation.py")
    assert spec.json_artifact == "reports/canonical/gap-head-ablation.json"
    assert spec.markdown_artifact == "reports/canonical/gap-head-ablation.md"
    assert {
        "records",
        "aggregate",
        "factor_attribution",
        "hardgate",
        "positive_discovery_pointer",
    }.issubset(set(spec.required_json_keys))
    assert spec.bundle_role == "hg_p_core"
    assert spec.scope_pointer == "$.applicability_boundary"
    assert spec.cost_pointer == "$.control_protocol"
    assert spec.positive_claim_pointer == "$.factor_attribution.learned_head.auroc_delta"
    assert spec.control_pointer == "$.control_protocol"


def test_canonical_reports_manifest_includes_gap_head_threshold_frontier():
    spec = canonical._specs_by_name()["gap-head-threshold-frontier"]

    assert spec.command == ("python3", "scripts/run_gap_head_threshold_sweep.py")
    assert spec.json_artifact == "reports/canonical/gap-head-threshold-frontier.json"
    assert spec.markdown_artifact == "reports/canonical/gap-head-threshold-frontier.md"
    assert {
        "threshold_curve",
        "threshold_summary",
        "pareto_axis_spec",
        "pareto_frontier",
        "hardgate",
        "readiness",
        "main_claim_status",
        "not_claimed",
    }.issubset(set(spec.required_json_keys))
    assert "threshold_records" not in spec.required_json_keys
    assert spec.bundle_role == "hg_p_core"
    assert spec.scope_pointer == "$.applicability_boundary"
    assert spec.cost_pointer == "$.source_artifacts"
    assert spec.positive_claim_pointer == "$.main_claim_status"
    assert spec.control_pointer == "$.threshold_summary.control_baseline"


def test_canonical_reports_manifest_includes_distribution_sweep():
    spec = canonical._specs_by_name()["nongaussian-distribution-sweep"]

    assert spec.command == ("python3", "scripts/run_nongaussian_distribution_sweep.py")
    assert spec.json_artifact == "reports/canonical/nongaussian-distribution-sweep.json"
    assert spec.markdown_artifact == "reports/canonical/nongaussian-distribution-sweep.md"
    assert {
        "records",
        "family_aggregates",
        "coverage_item",
        "claim_gate",
        "main_claim_status",
        "negative_result_ledger",
        "not_claimed",
    }.issubset(set(spec.required_json_keys))
    assert spec.bundle_role == "auxiliary"


def test_canonical_reports_manifest_includes_mixing_and_anisotropic_sweeps():
    mixing = canonical._specs_by_name()["mixing-family-sweep"]
    anisotropic = canonical._specs_by_name()["anisotropic-ou-sweep"]

    assert mixing.command == ("python3", "scripts/run_mixing_family_sweep.py")
    assert mixing.json_artifact == "reports/canonical/mixing-family-sweep.json"
    assert mixing.markdown_artifact == "reports/canonical/mixing-family-sweep.md"
    assert mixing.bundle_role == "hg_p_core"
    assert {
        "applicability_boundary",
        "family_aggregates",
        "coverage_item",
        "negative_result_summary",
    }.issubset(set(mixing.required_json_keys))
    assert anisotropic.command == ("python3", "scripts/run_anisotropic_ou_sweep.py")
    assert anisotropic.json_artifact == "reports/canonical/anisotropic-ou-sweep.json"
    assert anisotropic.markdown_artifact == "reports/canonical/anisotropic-ou-sweep.md"
    assert anisotropic.bundle_role == "hg_p_core"
    assert {
        "applicability_boundary",
        "aggregates",
        "transition_debt_by_grid",
        "negative_result_summary",
    }.issubset(set(anisotropic.required_json_keys))


def test_canonical_reports_manifest_includes_certificate_guided_projection():
    training = canonical._specs_by_name()["certificate-guided-training"]
    discovery = canonical._specs_by_name()["certificate-guided-discovery"]

    assert training.command == ("python3", "scripts/run_certificate_guided_training.py")
    assert training.json_artifact == "reports/canonical/certificate-guided-training.json"
    assert training.markdown_artifact == "reports/canonical/certificate-guided-training.md"
    assert discovery.command == ("python3", "scripts/run_certificate_guided_discovery.py")
    assert discovery.json_artifact == "reports/canonical/certificate-guided-discovery.json"
    assert discovery.markdown_artifact == "reports/canonical/certificate-guided-discovery.md"
    assert {
        "paired_seed_protocol",
        "paired_delta_ci",
        "arm_protocol",
        "arm_summaries",
        "claim_gate",
        "hardgate",
        "failed_gate",
        "verdict",
        "discovery_level",
        "not_claimed",
    }.issubset(set(training.required_json_keys))
    assert training.bundle_role == "hg_p_core"
    assert {
        "positive_discovery",
        "net_information",
        "matched_random_baseline",
        "claim_gate",
        "hardgate",
        "failed_gate",
        "verdict",
        "discovery_level",
        "revocation_decision",
        "revocation_ledger",
        "not_claimed",
        "main_claim_status",
    }.issubset(set(discovery.required_json_keys))
    assert discovery.bundle_role == "hg_p_core"

def test_certificate_guided_discovery_required_keys_do_not_require_audit_fields():
    discovery = canonical._specs_by_name()["certificate-guided-discovery"]

    assert "audit_decision" not in discovery.required_json_keys
    assert "audit_ledger" not in discovery.required_json_keys


def test_manifest_required_keys_cover_linked_control_evidence():
    for spec in canonical.CANONICAL_REPORTS:
        keys = set(spec.required_json_keys)
        assert "generated_at" in keys
        assert "source_artifacts" in keys
    assert {"control_protocol", "control_verdict"}.issubset(
        set(canonical._specs_by_name()["gap-head-on-h"].required_json_keys)
    )
    assert {"matched_random_control", "main_claim_status"}.issubset(
        set(canonical._specs_by_name()["gap-head-discovery"].required_json_keys)
    )
    assert {"control_protocol", "hardgate", "factor_attribution"}.issubset(
        set(canonical._specs_by_name()["gap-head-ablation"].required_json_keys)
    )
    assert {"claim_gate", "negative_result_ledger", "main_claim_status"}.issubset(
        set(canonical._specs_by_name()["nongaussian-distribution-sweep"].required_json_keys)
    )
    assert {"positive_discovery", "net_information", "matched_random_baseline", "claim_gate", "hardgate", "failed_gate", "verdict", "discovery_level", "revocation_decision", "revocation_ledger", "not_claimed", "main_claim_status"}.issubset(
        set(canonical._specs_by_name()["certificate-guided-discovery"].required_json_keys)
    )


def test_hg_p_core_rows_are_exact_and_auxiliary_rows_cannot_substitute():
    core = {
        spec.name
        for spec in canonical.CANONICAL_REPORTS
        if spec.bundle_role == "hg_p_core"
    }
    auxiliary = {
        spec.name
        for spec in canonical.CANONICAL_REPORTS
        if spec.bundle_role == "auxiliary"
    }

    assert core == HG_P_CORE
    assert "nongaussian-distribution-sweep" in auxiliary
    assert "spectral-ablation-hinge" in auxiliary
    assert not HG_P_CORE.intersection(auxiliary)


def test_every_core_row_has_scope_cost_not_claimed_and_claim_discipline_pointers(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    for spec in canonical.CANONICAL_REPORTS:
        json_path = canonical._artifact_path(spec.json_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")

    for spec in canonical.CANONICAL_REPORTS:
        discipline = canonical._discipline(spec)
        if spec.bundle_role != "hg_p_core":
            continue
        assert discipline["scope_status"] == "present"
        assert discipline["cost_status"] == "present"
        assert discipline["not_claimed_status"] == "present"
        assert discipline["positive_claim_status"] == "present"


def test_positive_claims_have_control_or_no_control_rationale():
    for spec in canonical.CANONICAL_REPORTS:
        has_control = spec.control_pointer is not None
        has_rationale = spec.no_control_rationale_pointer is not None
        assert has_control or has_rationale


def test_generated_index_contains_outline_claims_nonclaims_and_honest_boundary_sections():
    reports = [_index_row_for_spec(spec) for spec in canonical.CANONICAL_REPORTS]
    payload = canonical._index(reports)
    markdown = canonical._render_index_markdown(payload)

    assert {
        "paper_outline",
        "claims_nonclaims",
        "honest_boundary",
        "literature_ledger",
        "quality_scorecard",
        "negative_witnesses",
        "claim_verdicts",
        "formal_hardening",
    }.issubset(payload)
    assert set(payload["paper_outline"]["core_reports"]) == HG_P_CORE
    assert payload["negative_witnesses"] == {
        "status": "pointer-only",
        "artifact_id": "bedc-quality-lab:discovery-negative-witnesses",
        "json_artifact": "reports/canonical/discovery_negative_witnesses.json",
        "expected_kind_count": 8,
    }
    assert payload["claim_verdicts"]["status"] == "pointer-only"
    assert payload["claim_verdicts"]["artifact_id"] == "bedc-quality-lab:claim-verdicts"
    assert payload["claim_verdicts"]["jsonl_artifact"] == "reports/canonical/claim_verdicts.jsonl"
    assert isinstance(payload["claim_verdicts"]["row_count"], int)
    assert payload["formal_hardening"] == {
        "status": "pointer-only",
        "artifact_id": "bedc-quality-lab:formal-hardening",
        "json_artifact": "reports/canonical/formal_hardening.json",
        "markdown_artifact": "reports/canonical/formal_hardening.md",
        "ready": True,
        "recorded": 4,
        "required": 4,
        "gap_count": 0,
    }
    assert "HG-P core reports" in markdown
    assert "Auxiliary reports" in markdown
    assert "Quality scorecard" in markdown
    assert "Quality baseline pointers" in markdown
    assert "reports/canonical/discovery_map.json:$.rows[*].discovery_level" in markdown
    assert "Negative witnesses" in markdown
    assert "Claim verdicts" in markdown
    assert "Formal hardening" in markdown
    assert "Paper outline" in markdown
    assert "Claims and non-claims" in markdown
    assert "Literature ledger pointer" in markdown
    assert "Honest boundary" in markdown


def test_hg_p_forbidden_claim_terms_are_absent_from_positive_claim_cells():
    reports = [
        {
            "name": spec.name,
            "bundle_role": spec.bundle_role,
            "discipline": {
                "positive_claim_pointer": spec.positive_claim_pointer,
                "control_pointer": spec.control_pointer,
                "no_control_rationale_pointer": spec.no_control_rationale_pointer,
            },
        }
        for spec in canonical.CANONICAL_REPORTS
    ]
    cells = canonical._claims_nonclaims(reports)["positive_claim_cells"]
    forbidden = set(canonical.FORBIDDEN_POSITIVE_CLAIM_TERMS)

    for cell in cells:
        text = " ".join(str(value).lower() for value in cell.values())
        for term in forbidden:
            assert term not in text


def test_forbidden_term_at_positive_claim_pointer_is_caught(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["mixing-family-sweep"]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    payload = _payload_for_spec(spec)
    payload["coverage_item"] = {
        "status": "positive",
        "claim": "full-lejepa certification",
    }
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
    md_path.write_text("# fixture\n", encoding="utf-8")
    monkeypatch.setattr(canonical, "_run_producer", lambda _spec: None)

    result = canonical._run_spec(spec)

    assert result["status"] == "fail"
    assert result["producer_status"] == "completed"
    assert result["validation"]["status"] == "pass"
    assert result["discipline"]["positive_claim_pointer"] == "$.coverage_item"
    assert result["discipline"]["forbidden_claim_terms_status"] == "fail"
    assert result["discipline"]["forbidden_claim_term_hits"] == ["full-lejepa"]


def test_literature_ledger_status_follows_validator_not_path_existence(tmp_path, monkeypatch):
    ledger = tmp_path / "docs" / "lit" / "literature_ledger.yaml"
    ledger.parent.mkdir(parents=True)
    ledger.write_text("{}\n", encoding="utf-8")
    monkeypatch.setattr(canonical, "ROOT", tmp_path)

    payload = canonical._literature_ledger()

    assert payload["status"] == "not-ready"
    assert payload["pointer"] == "docs/lit/literature_ledger.yaml"
    assert payload["record_count"] == 0
    assert "failures" in payload
    assert "records" not in payload


def test_artifact_path_rejects_non_canonical_paths():
    with pytest.raises(ValueError):
        canonical._artifact_path("reports/not-canonical.json")


def test_only_selects_one_manifest_row_and_rejects_unknown():
    selected = canonical._select_specs("gap-head-discovery")

    assert [spec.name for spec in selected] == ["gap-head-discovery"]
    with pytest.raises(ValueError):
        canonical._select_specs("missing")


def test_run_reports_only_writes_index_and_summary_from_producer(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    old_runner = canonical._run_producer
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    canonical.INDEX_ARTIFACT = tmp_path / "reports" / "canonical" / "index.json"
    canonical_dir = canonical.CANONICAL_DIR
    index_path = canonical.INDEX_ARTIFACT
    summary_path = tmp_path / "summary.json"
    calls = []

    def fake_run_producer(spec):
        calls.append(spec.name)
        json_path = canonical._artifact_path(spec.json_artifact)
        md_path = canonical._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(
            json.dumps(_payload_for_spec(spec)) + "\n",
            encoding="utf-8",
        )
        md_path.write_text("# fixture\n", encoding="utf-8")

    canonical._run_producer = fake_run_producer

    try:
        payload = canonical.run_reports(
            only="gap-head-on-h",
            json_summary=str(summary_path),
        )
        index_markdown = (canonical.CANONICAL_DIR / "index.md").read_text(encoding="utf-8")
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index
        canonical._run_producer = old_runner

    assert calls == ["gap-head-on-h"]
    assert payload["schema_id"] == canonical.INDEX_SCHEMA_ID
    assert len(payload["reports"]) == 1
    assert payload["reports"][0]["status"] == "pass"
    assert payload["reports"][0]["validation"]["required_key_validation"]["status"] == "pass"
    assert json.loads(index_path.read_text(encoding="utf-8")) == payload
    assert json.loads(summary_path.read_text(encoding="utf-8")) == payload
    assert "gap-head-on-h" in index_markdown
    assert (canonical_dir / "quality-scorecard.json").exists()
    assert (canonical_dir / "quality-scorecard.md").exists()


def test_quality_scorecard_has_exactly_twelve_metric_rows(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        rows = canonical._build_quality_scorecard([], generated_at="fixture-time")["rows"]
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    assert [row["metric"] for row in rows] == list(canonical.QUALITY_SCORECARD_METRICS)
    assert {row["metric"] for row in rows} == QUALITY_SCORECARD_METRICS
    assert len(rows) == 12


def test_quality_scorecard_is_generated_by_canonical_runner(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")

    def fake_run_producer(spec):
        json_path = canonical._artifact_path(spec.json_artifact)
        md_path = canonical._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(generated_at="2026-01-02T03:04:05+00:00")
    scorecard_json = canonical.CANONICAL_DIR / "quality-scorecard.json"
    scorecard_md = canonical.CANONICAL_DIR / "quality-scorecard.md"

    assert scorecard_json.exists()
    assert scorecard_md.exists()
    assert payload["quality_scorecard"]["json_artifact"] == "reports/canonical/quality-scorecard.json"
    assert payload["quality_scorecard"]["markdown_artifact"] == "reports/canonical/quality-scorecard.md"
    assert "Quality scorecard" in (canonical.CANONICAL_DIR / "index.md").read_text(encoding="utf-8")
    assert "run_quality_scorecard.py" not in json.dumps(payload)


def test_discovery_map_is_registered_by_canonical_runner(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")

    def fake_run_producer(spec):
        json_path = canonical._artifact_path(spec.json_artifact)
        md_path = canonical._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(generated_at="2026-01-02T03:04:05+00:00")

    assert payload["discovery_map"]["artifact_id"] == "bedc-quality-lab:discovery-map"
    assert payload["discovery_map"]["json_artifact"] == "reports/canonical/discovery_map.json"
    assert payload["discovery_map"]["markdown_artifact"] == "reports/canonical/discovery_map.md"
    assert "Discovery map" in (canonical.CANONICAL_DIR / "index.md").read_text(encoding="utf-8")


def test_claim_verdicts_are_pointer_only_and_not_canonical_report_artifacts(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")

    def fake_run_producer(spec):
        json_path = canonical._artifact_path(spec.json_artifact)
        md_path = canonical._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(generated_at="2026-01-02T03:04:05+00:00")
    json_artifacts = {spec.json_artifact for spec in canonical.CANONICAL_REPORTS}

    assert payload["claim_verdicts"]["status"] == "pointer-only"
    assert payload["claim_verdicts"]["artifact_id"] == "bedc-quality-lab:claim-verdicts"
    assert payload["claim_verdicts"]["jsonl_artifact"] == "reports/canonical/claim_verdicts.jsonl"
    assert payload["claim_verdicts"]["jsonl_artifact"] not in json_artifacts
    assert (canonical.CANONICAL_DIR / "claim_verdicts.jsonl").exists()
    assert "claim_verdicts.jsonl" in (canonical.CANONICAL_DIR / "index.md").read_text(encoding="utf-8")


def test_quality_scorecard_projects_only_explicit_cells(tmp_path, monkeypatch):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        monkeypatch.setattr(
            canonical,
            "_build_formal_hardening_payload",
            lambda generated_at=None: formal_hardening.build_formal_hardening_report(
                root=formal_hardening.ROOT,
                generated_at=generated_at,
            ),
        )
        payload = canonical._build_quality_scorecard([], generated_at="fixture-time")
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    expected = {
        "CertCov": {
            "value": pytest.approx(2 / 3),
            "source": {
                "report": "mixing-family-sweep",
                "artifact": "reports/canonical/mixing-family-sweep.json",
                "pointer": "$.coverage_item",
            },
            "numerator": 2,
            "denominator": 3,
        },
        "DebtQ": {
            "value": pytest.approx(0.125),
            "source": {
                "report": "mixing-family-sweep",
                "artifact": "reports/canonical/mixing-family-sweep.json",
                "pointer": "$.coverage_item.debt_item.score",
            },
        },
        "CriticalDebt": {
            "value": 0.25,
            "source": {
                "report": "gap-head-discovery",
                "artifact": "reports/canonical/gap-head-discovery.json",
                "pointer": "$.debt_terms",
            },
        },
        "LedgerCompleteness": {
            "value": pytest.approx(3 / 4),
            "source": {
                "report": "gap-head-discovery",
                "artifact": "reports/canonical/gap-head-discovery.json",
                "pointer": "$.classifier_state",
            },
            "numerator": 3,
            "denominator": 4,
        },
        "ClassifierShiftCount": {
            "value": 2,
            "source": {
                "report": "gap-head-discovery",
                "artifact": "reports/canonical/gap-head-discovery.json",
                "pointer": "$.surface_delta_count",
            },
        },
        "PositiveDiscoveryCount": {
            "value": 1,
            "source": [
                {
                    "report": "gap-head-discovery",
                    "artifact": "reports/canonical/gap-head-discovery.json",
                    "pointer": "$.positive_discovery",
                },
                {
                    "report": "certificate-guided-discovery",
                    "artifact": "reports/canonical/certificate-guided-discovery.json",
                    "pointer": "$.positive_discovery",
                },
            ],
            "numerator": 1,
            "denominator": 2,
        },
        "AuditImprovementCount": {
            "value": 1,
            "source": {
                "report": "certificate-guided-training",
                "artifact": "reports/canonical/certificate-guided-training.json",
                "pointer": "$.claim_gate.audit_improvement_tradeoff",
            },
            "numerator": 1,
            "denominator": 1,
        },
        "NegativeResultCount": {
            "value": 5,
            "source": [
                {
                    "report": "mixing-family-sweep",
                    "artifact": "reports/canonical/mixing-family-sweep.json",
                    "pointer": "$.negative_result_summary.cells",
                },
                {
                    "report": "anisotropic-ou-sweep",
                    "artifact": "reports/canonical/anisotropic-ou-sweep.json",
                    "pointer": "$.negative_result_summary.cells",
                },
                {
                    "report": "nongaussian-distribution-sweep",
                    "artifact": "reports/canonical/nongaussian-distribution-sweep.json",
                    "pointer": "$.negative_result_ledger",
                },
            ],
        },
        "ScopeCompleteness": {
            "value": 1.0,
            "source": [
                {
                    "report": "mixing-family-sweep",
                    "artifact": "reports/canonical/mixing-family-sweep.json",
                    "pointer": "$.applicability_boundary",
                },
                {
                    "report": "anisotropic-ou-sweep",
                    "artifact": "reports/canonical/anisotropic-ou-sweep.json",
                    "pointer": "$.applicability_boundary",
                },
                {
                    "report": "gap-head-on-h",
                    "artifact": "reports/canonical/gap-head-on-h.json",
                    "pointer": "$.applicability_boundary",
                },
                {
                    "report": "gap-head-discovery",
                    "artifact": "reports/canonical/gap-head-discovery.json",
                    "pointer": "$.boundary_checks",
                },
                {
                    "report": "gap-head-ablation",
                    "artifact": "reports/canonical/gap-head-ablation.json",
                    "pointer": "$.applicability_boundary",
                },
                {
                    "report": "gap-head-threshold-frontier",
                    "artifact": "reports/canonical/gap-head-threshold-frontier.json",
                    "pointer": "$.applicability_boundary",
                },
                {
                    "report": "nongaussian-distribution-sweep",
                    "artifact": "reports/canonical/nongaussian-distribution-sweep.json",
                    "pointer": "$.coverage_item",
                },
                {
                    "report": "certificate-guided-training",
                    "artifact": "reports/canonical/certificate-guided-training.json",
                    "pointer": "$.objective.required_rows",
                },
                {
                    "report": "certificate-guided-discovery",
                    "artifact": "reports/canonical/certificate-guided-discovery.json",
                    "pointer": "$.applicability_boundary",
                },
                {
                    "report": "spectral-ablation-hinge",
                    "artifact": "reports/canonical/spectral-ablation-hinge.json",
                    "pointer": "$.applicability_boundary",
                },
            ],
            "numerator": 10,
            "denominator": 10,
        },
        "CostProtocolCompleteness": {
            "value": 1.0,
            "source": [
                {
                    "report": "mixing-family-sweep",
                    "artifact": "reports/canonical/mixing-family-sweep.json",
                    "pointer": "$.source_artifacts.cost_protocol",
                },
                {
                    "report": "anisotropic-ou-sweep",
                    "artifact": "reports/canonical/anisotropic-ou-sweep.json",
                    "pointer": "$.source_artifacts.cost_protocol",
                },
                {
                    "report": "gap-head-on-h",
                    "artifact": "reports/canonical/gap-head-on-h.json",
                    "pointer": "$.control_protocol",
                },
                {
                    "report": "gap-head-discovery",
                    "artifact": "reports/canonical/gap-head-discovery.json",
                    "pointer": "$.score_terms",
                },
                {
                    "report": "gap-head-ablation",
                    "artifact": "reports/canonical/gap-head-ablation.json",
                    "pointer": "$.control_protocol",
                },
                {
                    "report": "gap-head-threshold-frontier",
                    "artifact": "reports/canonical/gap-head-threshold-frontier.json",
                    "pointer": "$.source_artifacts",
                },
                {
                    "report": "nongaussian-distribution-sweep",
                    "artifact": "reports/canonical/nongaussian-distribution-sweep.json",
                    "pointer": "$.source_artifacts.cost_protocol",
                },
                {
                    "report": "certificate-guided-training",
                    "artifact": "reports/canonical/certificate-guided-training.json",
                    "pointer": "$.cost_protocol",
                },
                {
                    "report": "certificate-guided-discovery",
                    "artifact": "reports/canonical/certificate-guided-discovery.json",
                    "pointer": "$.claim_gate",
                },
                {
                    "report": "spectral-ablation-hinge",
                    "artifact": "reports/canonical/spectral-ablation-hinge.json",
                    "pointer": "$.source_artifacts",
                },
            ],
            "numerator": 10,
            "denominator": 10,
        },
        "HardeningCoverage": {
            "value": 1.0,
            "source": {
                "report": "formal_hardening",
                "artifact": "reports/canonical/formal_hardening.json",
                "pointer": "$.coverage",
            },
            "numerator": 4,
            "denominator": 4,
        },
        "OverclaimRate": {
            "value": pytest.approx(0.4),
            "source": {
                "report": "certificate-guided-discovery",
                "artifact": "reports/canonical/certificate-guided-discovery.json",
                "pointer": "$.audit_decision.overclaim_rate",
            },
        },
    }

    by_metric = {row["metric"]: row for row in payload["rows"]}
    for metric, fields in expected.items():
        row = by_metric[metric]
        assert row["status"] == fields.get("status", "ready")
        if row["status"] == "not-ready":
            assert row["dependency"] == fields["dependency"]
            assert row["reason"] == fields["reason"]
            continue
        assert row["value"] == fields["value"]
        assert row["source"] == fields["source"]
        if "numerator" in fields:
            assert row["numerator"] == fields["numerator"]
        if "denominator" in fields:
            assert row["denominator"] == fields["denominator"]


def test_quality_scorecard_fails_closed_without_source_or_denominator(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    cases = [
        (
            "CertCov",
            "mixing-family-sweep:$.coverage_item",
            lambda: _mutate_payload(
                canonical,
                "mixing-family-sweep",
                lambda payload: payload["coverage_item"].pop("canonical_families"),
            ),
        ),
        (
            "PositiveDiscoveryCount",
            "canonical discovery positive flags",
            lambda: _mutate_payload(
                canonical,
                "certificate-guided-discovery",
                lambda payload: payload.update({"positive_discovery": "yes"}),
            ),
        ),
        (
            "NegativeResultCount",
            "canonical negative-result cells",
            lambda: _mutate_payload(
                canonical,
                "anisotropic-ou-sweep",
                lambda payload: payload.update({"negative_result_summary": {"cells": "none"}}),
            ),
        ),
        (
            "ScopeCompleteness",
            "certificate-guided-training:$.objective.required_rows",
            lambda: _mutate_payload(
                canonical,
                "certificate-guided-training",
                lambda payload: payload["objective"].pop("required_rows"),
            ),
        ),
        (
            "OverclaimRate",
            "certificate-guided-discovery:$.audit_decision.overclaim_rate",
            lambda: _mutate_payload(
                canonical,
                "certificate-guided-discovery",
                lambda payload: payload["audit_decision"].pop("overclaim_rate"),
            ),
        ),
    ]

    try:
        for metric, dependency, break_payload in cases:
            _write_payloads_for_all_specs(canonical, tmp_path)
            break_payload()
            scorecard = canonical._build_quality_scorecard([], generated_at="fixture-time")
            row = {item["metric"]: item for item in scorecard["rows"]}[metric]
            assert row["status"] == "not-ready"
            assert row["dependency"] == dependency
            assert "value" not in row
            assert "numerator" not in row
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index


def test_quality_scorecard_hardening_coverage_uses_current_formal_payload(tmp_path, monkeypatch):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        monkeypatch.setattr(
            canonical,
            "_build_formal_hardening_payload",
            lambda generated_at=None: formal_hardening.build_formal_hardening_report(
                root=formal_hardening.ROOT,
                generated_at=generated_at,
            ),
        )
        scorecard = canonical._build_quality_scorecard([], generated_at="fixture-time")
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    row = {item["metric"]: item for item in scorecard["rows"]}["HardeningCoverage"]
    assert row["status"] == "ready"
    assert row["value"] == 1.0
    assert row["numerator"] == 4
    assert row["denominator"] == 4
    assert row["source"] == {
        "report": "formal_hardening",
        "artifact": "reports/canonical/formal_hardening.json",
        "pointer": "$.coverage",
    }


def test_quality_scorecard_hardening_coverage_ready_iff_all_rows_verified(monkeypatch):
    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    evidence_pointer = "reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[0].recorded"
    verified_rows = []
    for row in payload["verification_ledger"]:
        ready_row = dict(row)
        ready_row["status"] = "verified"
        ready_row["recorded"] = True
        ready_row["evidence_resolved"] = True
        ready_row["evidence_pointer"] = ready_row["evidence_pointer"] or evidence_pointer
        ready_row["gap"] = None
        verified_rows.append(ready_row)
    payload.update(
        {
            "ready": True,
            "status": "ready",
            "recorded": len(verified_rows),
            "required": len(verified_rows),
            "gap_count": 0,
            "verification_ledger": verified_rows,
            "coverage": {
                "ready": True,
                "recorded": len(verified_rows),
                "required": len(verified_rows),
                "gap_count": 0,
                "gap_rows": [],
            },
        }
    )
    monkeypatch.setattr(canonical, "_build_formal_hardening_payload", lambda generated_at=None: payload)

    row = canonical._scorecard_hardening_coverage({})

    assert row["status"] == "ready"
    assert row["value"] == 1.0
    assert row["numerator"] == len(verified_rows)
    assert row["denominator"] == len(verified_rows)
    assert row["source"] == {
        "report": "formal_hardening",
        "artifact": "reports/canonical/formal_hardening.json",
        "pointer": "$.coverage",
    }


def test_quality_scorecard_hardening_coverage_reads_payload_not_lean_file(monkeypatch, tmp_path):
    payload = {
        "ready": True,
        "status": "ready",
        "recorded": 1,
        "required": 1,
        "verification_ledger": [
            {
                "status": "verified",
                "recorded": True,
                "evidence_resolved": True,
            }
        ],
        "coverage": {"ready": True, "recorded": 1, "required": 1, "gap_count": 0, "gap_rows": []},
    }
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "_build_formal_hardening_payload", lambda generated_at=None: payload)

    row = canonical._scorecard_hardening_coverage({})

    assert row["status"] == "ready"
    assert row["value"] == 1.0
    assert row["numerator"] == 1
    assert row["denominator"] == 1


@pytest.mark.parametrize(
    "mutate",
    [
        lambda payload: payload.update({"ready": False}),
        lambda payload: payload["verification_ledger"][0].update({"status": "missing"}),
        lambda payload: payload["verification_ledger"][0].update({"recorded": False}),
        lambda payload: payload["verification_ledger"][0].update({"evidence_resolved": False}),
        lambda payload: payload["coverage"].update({"recorded": payload["coverage"]["required"] - 1}),
    ],
)
def test_quality_scorecard_hardening_coverage_fails_closed_for_any_unverified_cell(monkeypatch, mutate):
    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    evidence_pointer = "reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[0].recorded"
    rows = []
    for row in payload["verification_ledger"]:
        ready_row = dict(row)
        ready_row["status"] = "verified"
        ready_row["recorded"] = True
        ready_row["evidence_resolved"] = True
        ready_row["evidence_pointer"] = ready_row["evidence_pointer"] or evidence_pointer
        rows.append(ready_row)
    payload.update(
        {
            "ready": True,
            "recorded": len(rows),
            "required": len(rows),
            "verification_ledger": rows,
            "coverage": {"recorded": len(rows), "required": len(rows), "ready": True, "gap_count": 0},
        }
    )
    mutate(payload)
    monkeypatch.setattr(canonical, "_build_formal_hardening_payload", lambda generated_at=None: payload)

    row = canonical._scorecard_hardening_coverage({})

    assert row["status"] == "not-ready"
    assert row["dependency"] == "formal_hardening:$.coverage"


@pytest.mark.parametrize(
    "evidence_pointer",
    [
        "reports/canonical/spectral-ablation-hinge.json:$.does_not_exist",
        "reports/canonical/formal_hardening.json:$.verification_ledger",
        "reports/canonical/missing-artifact.json:$.recorded",
    ],
)
def test_quality_scorecard_hardening_coverage_fails_closed_for_unresolved_pointer(monkeypatch, evidence_pointer):
    item = formal_hardening._HardeningItem(
        item_id="unresolved-pointer",
        name="unresolved pointer",
        row=formal_hardening.LedgerRowKey("formal-hardening", "unresolved-pointer"),
        source_pointer=evidence_pointer,
        evidence_pointer=evidence_pointer,
        formal_pointer="fixture.formal",
        gap="missing evidence",
        trust_boundary="pointer-only evidence ledger",
    )
    monkeypatch.setattr(formal_hardening, "_ITEMS", (item,))
    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    monkeypatch.setattr(canonical, "_build_formal_hardening_payload", lambda generated_at=None: payload)

    scorecard_row = canonical._scorecard_hardening_coverage({})
    ledger_row = payload["verification_ledger"][0]

    assert ledger_row["status"] == "missing"
    assert ledger_row["recorded"] is False
    assert ledger_row["evidence_resolved"] is False
    assert payload["ready"] is False
    assert scorecard_row["status"] == "not-ready"
    assert scorecard_row["dependency"] == "formal_hardening:$.coverage"


def test_quality_scorecard_hardening_coverage_falsy_resolved_value_stays_not_ready(monkeypatch):
    evidence_pointer = "reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[2].recorded"
    item = formal_hardening._HardeningItem(
        item_id="falsy-pointer",
        name="falsy pointer",
        row=formal_hardening.LedgerRowKey("formal-hardening", "falsy-pointer"),
        source_pointer="reports/canonical/spectral-ablation-hinge.json:$.ledger_summary.basis.hardening_coverage.items[2]",
        evidence_pointer=evidence_pointer,
        formal_pointer="fixture.formal",
        gap="missing evidence",
        trust_boundary="pointer-only evidence ledger",
    )
    monkeypatch.setattr(formal_hardening, "_ITEMS", (item,))
    payload = formal_hardening.build_formal_hardening_report(generated_at="fixture-time")
    monkeypatch.setattr(canonical, "_build_formal_hardening_payload", lambda generated_at=None: payload)

    scorecard_row = canonical._scorecard_hardening_coverage({})
    ledger_row = payload["verification_ledger"][0]

    assert ledger_row["status"] == "missing"
    assert ledger_row["recorded"] is False
    assert ledger_row["evidence_resolved"] is False
    assert payload["ready"] is False
    assert scorecard_row["status"] == "not-ready"
    assert scorecard_row["dependency"] == "formal_hardening:$.coverage"


def test_quality_scorecard_cost_protocol_completeness_fails_closed_without_manifest_pointer(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        _mutate_payload(
            canonical,
            "gap-head-discovery",
            lambda payload: payload.pop("score_terms"),
        )
        scorecard = canonical._build_quality_scorecard([], generated_at="fixture-time")
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    row = {item["metric"]: item for item in scorecard["rows"]}["CostProtocolCompleteness"]
    assert row["status"] == "not-ready"
    assert row["dependency"] == "gap-head-discovery:$.score_terms"
    assert "value" not in row
    assert "numerator" not in row


def test_quality_scorecard_excludes_report_schema_fields(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        payload = canonical._build_quality_scorecard([], generated_at="fixture-time")
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    assert "report_schema_id" not in set(_walk_keys(payload))
    assert "report_kind" not in set(_walk_keys(payload))


def test_quality_scorecard_uses_caller_timestamp(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")

    def fake_run_producer(spec):
        json_path = canonical._artifact_path(spec.json_artifact)
        md_path = canonical._artifact_path(spec.markdown_artifact)
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
        md_path.write_text("# fixture\n", encoding="utf-8")

    monkeypatch.setattr(canonical, "_run_producer", fake_run_producer)

    payload = canonical.run_reports(generated_at="2030-01-01T00:00:00+00:00")
    scorecard = json.loads((canonical.CANONICAL_DIR / "quality-scorecard.json").read_text(encoding="utf-8"))

    assert payload["generated_at"] == "2030-01-01T00:00:00+00:00"
    assert scorecard["generated_at"] == "2030-01-01T00:00:00+00:00"


def test_quality_scorecard_has_no_weighted_total(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        payload = canonical._build_quality_scorecard([], generated_at="fixture-time")
        markdown = canonical._render_quality_scorecard_markdown(payload)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    keys = set(_walk_keys(payload))
    assert "weighted_total" not in keys
    assert "total_score" not in keys
    assert "grade" not in keys
    assert "weight" not in keys
    assert "weighted" not in json.dumps(payload).lower()
    assert "weighted" not in markdown.lower()


def test_quality_scorecard_markdown_contains_baseline_pointers(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    old_index = canonical.INDEX_ARTIFACT
    try:
        _write_payloads_for_all_specs(canonical, tmp_path)
        payload = canonical._build_quality_scorecard([], generated_at="fixture-time")
        markdown = canonical._render_quality_scorecard_markdown(payload)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir
        canonical.INDEX_ARTIFACT = old_index

    assert "Quality baseline pointers" in markdown
    assert "docs/bedc_quality_lab_alpha_milestone.md" in markdown
    assert "reports/canonical/discovery_map.json:$.rows[*].discovery_level" in markdown


def test_run_spec_producer_exception_fails_closed_even_with_valid_stale_artifact(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    spec = canonical._specs_by_name()["gap-head-on-h"]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(_payload_for_spec(spec)) + "\n", encoding="utf-8")
    md_path.write_text("# fixture\n", encoding="utf-8")

    def broken_producer(_spec):
        raise RuntimeError("producer stopped")

    monkeypatch.setattr(canonical, "_run_producer", broken_producer)

    result = canonical._run_spec(spec)

    assert result["status"] == "error"
    assert result["status"] != "pass"
    assert result["producer_status"] == "error"
    assert result["validation"]["status"] == "pass"
    assert result["validation"]["required_key_validation"]["status"] == "pass"
    assert result["error"] == "producer stopped"


def test_run_reports_certificate_guided_discovery_uses_canonical_training_source(tmp_path, monkeypatch):
    monkeypatch.setattr(canonical, "ROOT", tmp_path)
    monkeypatch.setattr(canonical, "CANONICAL_DIR", tmp_path / "reports" / "canonical")
    monkeypatch.setattr(canonical, "INDEX_ARTIFACT", tmp_path / "reports" / "canonical" / "index.json")
    source_json = canonical.CANONICAL_DIR / "certificate-guided-training.json"
    source_report = canonical.CANONICAL_DIR / "certificate-guided-training.md"
    source_json.parent.mkdir(parents=True, exist_ok=True)
    source_json.write_text(json.dumps({"training_marker": "canonical-source"}), encoding="utf-8")
    source_report.write_text("# canonical training\n", encoding="utf-8")
    observed = []

    class StubDiscoveryProducer:
        REPORT_JSON = None
        REPORT_MD = None
        JSON_ARTIFACT = "reports/certificate_guided_discovery.json"
        REPORT_ARTIFACT = "reports/certificate_guided_discovery.md"
        SOURCE_JSON_ARTIFACT = "reports/certificate_guided_training.json"
        SOURCE_REPORT_ARTIFACT = "reports/certificate_guided_training.md"
        USE_TORCH = True

        @classmethod
        def main(cls):
            assert cls.JSON_ARTIFACT == "reports/canonical/certificate-guided-discovery.json"
            assert cls.REPORT_ARTIFACT == "reports/canonical/certificate-guided-discovery.md"
            assert cls.SOURCE_JSON_ARTIFACT == "reports/canonical/certificate-guided-training.json"
            assert cls.SOURCE_REPORT_ARTIFACT == "reports/canonical/certificate-guided-training.md"
            assert cls.USE_TORCH is False
            source_payload = json.loads((canonical.ROOT / cls.SOURCE_JSON_ARTIFACT).read_text(encoding="utf-8"))
            observed.append(source_payload["training_marker"])
            payload = {
                "generated_at": "fixture",
                "source_artifacts": {
                    "source_json_artifact": cls.SOURCE_JSON_ARTIFACT,
                    "source_report_artifact": cls.SOURCE_REPORT_ARTIFACT,
                },
                "verdicts": [{"verdict": "positive"}],
                "positive_discovery": True,
                "net_information": 1.25,
                    "matched_random_baseline": {"verdict": "negative"},
                    "claim_gate": {"positive_discovery_four_gate": True},
                    "hardgate": {"status": "pass"},
                    "failed_gate": None,
                    "verdict": "positive-discovery",
                    "discovery_level": "D4",
                    "revocation_decision": {"downgraded": False},
                "revocation_ledger": [],
                "not_claimed": ["fixture boundary"],
                "main_claim_status": "positive",
            }
            cls.REPORT_JSON.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")
            cls.REPORT_MD.write_text("# stub discovery\n", encoding="utf-8")

    def fake_import_module(module_name):
        assert module_name == "scripts.run_certificate_guided_discovery"
        return StubDiscoveryProducer

    monkeypatch.setattr(canonical.importlib, "import_module", fake_import_module)

    payload = canonical.run_reports(only="certificate-guided-discovery")
    report_payload = json.loads((canonical.CANONICAL_DIR / "certificate-guided-discovery.json").read_text(encoding="utf-8"))
    report_markdown = (canonical.CANONICAL_DIR / "certificate-guided-discovery.md").read_text(encoding="utf-8")

    assert observed == ["canonical-source"]
    assert payload["reports"][0]["name"] == "certificate-guided-discovery"
    assert payload["reports"][0]["status"] == "pass"
    assert payload["reports"][0]["validation"]["required_key_validation"]["status"] == "pass"
    assert report_payload["source_artifacts"]["source_json_artifact"] == "reports/canonical/certificate-guided-training.json"
    assert report_payload["source_artifacts"]["source_report_artifact"] == "reports/canonical/certificate-guided-training.md"
    assert report_payload["positive_discovery"] is True
    assert report_payload["net_information"] == pytest.approx(1.25)
    assert report_payload["matched_random_baseline"] == {"verdict": "negative"}
    assert report_payload["claim_gate"] == {"positive_discovery_four_gate": True}
    assert report_payload["revocation_decision"] == {"downgraded": False}
    assert report_payload["revocation_ledger"] == []
    assert report_payload["not_claimed"] == ["fixture boundary"]
    assert report_payload["main_claim_status"] == "positive"
    assert report_markdown == "# stub discovery\n"


def test_certificate_guided_discovery_validation_accepts_empty_revocation_ledger(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    spec = canonical._specs_by_name()["certificate-guided-discovery"]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(
        json.dumps({key: [] if key == "revocation_ledger" else {"downgraded": False} if key == "revocation_decision" else "fixture" for key in spec.required_json_keys}) + "\n",
        encoding="utf-8",
    )
    md_path.write_text("# fixture\n", encoding="utf-8")

    try:
        validation = canonical._artifact_validation(spec)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir

    assert validation["status"] == "pass"
    assert validation["required_key_validation"]["missing_keys"] == []


def test_certificate_guided_discovery_validation_fails_closed_on_missing_revocation_fields(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    spec = canonical._specs_by_name()["certificate-guided-discovery"]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {key: "fixture" for key in spec.required_json_keys if key not in {"revocation_decision", "revocation_ledger"}}
    json_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
    md_path.write_text("# fixture\n", encoding="utf-8")

    try:
        validation = canonical._artifact_validation(spec)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir

    assert validation["status"] == "fail"
    assert validation["required_key_validation"]["status"] == "fail"
    assert set(validation["required_key_validation"]["missing_keys"]) == {"revocation_decision", "revocation_ledger"}


def test_index_root_is_relative_and_host_path_free(tmp_path):
    payload = canonical._index([])
    index_path = tmp_path / "index.json"
    index_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    json_text = index_path.read_text(encoding="utf-8")
    root = payload.get("root")

    assert root is None or not os.path.isabs(root)
    assert "/Users/" not in json_text
    assert ".worktrees" not in json_text


def test_missing_artifact_fails_closed(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    spec = canonical.CANONICAL_REPORTS[0]

    try:
        validation = canonical._artifact_validation(spec)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir

    assert validation["status"] == "fail"
    assert spec.json_artifact in validation["missing_artifacts"]
    assert spec.markdown_artifact in validation["missing_artifacts"]
    assert validation["required_key_validation"]["status"] == "fail"


def test_required_key_failure_fails_closed(tmp_path):
    old_root = canonical.ROOT
    old_dir = canonical.CANONICAL_DIR
    canonical.ROOT = tmp_path
    canonical.CANONICAL_DIR = tmp_path / "reports" / "canonical"
    spec = canonical.CANONICAL_REPORTS[0]
    json_path = canonical._artifact_path(spec.json_artifact)
    md_path = canonical._artifact_path(spec.markdown_artifact)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text('{"generated_at": "fixture"}\n', encoding="utf-8")
    md_path.write_text("# fixture\n", encoding="utf-8")

    try:
        validation = canonical._artifact_validation(spec)
    finally:
        canonical.ROOT = old_root
        canonical.CANONICAL_DIR = old_dir

    assert validation["status"] == "fail"
    assert validation["missing_artifacts"] == []
    assert validation["required_key_validation"]["status"] == "fail"
    assert "source_artifacts" in validation["required_key_validation"]["missing_keys"]


def test_index_markdown_lists_gap_head_reports():
    payload = canonical._index(
        [
            _index_row_for_spec(canonical._specs_by_name()["gap-head-on-h"]),
            _index_row_for_spec(canonical._specs_by_name()["nongaussian-distribution-sweep"]),
            _index_row_for_spec(canonical._specs_by_name()["gap-head-discovery"]),
            _index_row_for_spec(canonical._specs_by_name()["certificate-guided-discovery"]),
        ]
    )
    markdown = canonical._render_index_markdown(payload)

    assert "gap-head-on-h" in markdown
    assert "gap-head-discovery" in markdown
    assert "nongaussian-distribution-sweep" in markdown
    assert "certificate-guided-discovery" in markdown
